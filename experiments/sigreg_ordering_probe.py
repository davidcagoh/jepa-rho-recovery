"""
SIGReg-ordering empirical probe — paper 3 spinoff scoping question.

The question: does the rho*-ordering of feature learning (paper 1 + paper 2's
positive branch) survive when JEPA training adds the SIGReg anti-collapse
regulariser used by LeWorldModel (Maes et al. 2026)?

Setup
-----
* Synthetic linear-Gaussian data with KNOWN generalised regression coefficients
  rho_r* = lambda_r* / mu_r. Spectrum is constructed by hand so the ordering
  is unambiguous.
* Tiny linear JEPA (depth L=2 or 3, no hidden non-linearity for the linear
  case; optional shallow tanh for the warm-up non-linear probe).
* Two training variants:
    (A) BASELINE: MSE-only (the classical analysis target).
    (B) LeWM-STYLE: MSE + lambda * SIGReg(latents), where SIGReg projects
        latents to M random unit-norm directions and runs an Epps-Pulley-like
        normality penalty on each 1D projection (squared distance from
        standard normal moments, simplified).
* For each variant: track the per-feature diagonal amplitude
  sigma_r(t) = sqrt(eigenvalue_r(W_bar^T W_bar)) (proxy: top-d sing. vals.
  of the encoder-predictor composition) and measure the critical times
  t_crit_r at which sigma_r first reaches half of its eventual plateau.

Question we want answered
-------------------------
Does (B)'s critical-time ranking still respect the rho* ordering observed in
(A), or does SIGReg homogenise the spectrum?

  If YES (ordering survives): paper 3 is well-defined -- the trajectory still
    encodes rho* ordering even under anti-collapse regularisation, so the
    signed-decomposition story extends.
  If NO (ordering destroyed): paper 3 needs a fundamentally different
    framing -- SIGReg's isotropisation overrides the spectrum, and the
    learning dynamics no longer encode rho*.

This is a one-day scoping experiment; the formal theory is a separate
multi-month project regardless of outcome.

Run
---
    python sigreg_ordering_probe.py [--n 4000] [--d 10] [--depth 2]
                                    [--steps 8000] [--lambd 0.1] [--seed 0]

Outputs go to experiments/results_sigreg_probe/.
"""

from __future__ import annotations

import argparse
import json
import math
import pathlib
import sys
from dataclasses import dataclass

import numpy as np
import torch
from torch import nn


# --------------------------------------------------------------------------- #
# Synthetic data with known rho*                                              #
# --------------------------------------------------------------------------- #

@dataclass
class SyntheticGenEigenSetup:
    """Linear-Gaussian (x, y) with hand-set generalised eigenstructure.

    Construction:
      * Pick an orthonormal basis U in R^d.
      * Pick mu_r > 0 (eigenvalues of Sigma^xx) and rho_r* (signed).
      * Set Sigma^xx = U diag(mu) U^T, Sigma^yx = U diag(rho * mu) U^T.
      * Then the generalised eigenvalues of (Sigma^yx, Sigma^xx) are exactly
        rho* in the U basis, by construction.
      * Sample x ~ N(0, Sigma^xx); set y = Sigma^yx Sigma^xx^{-1} x + noise.
    """
    d: int
    mu: np.ndarray            # (d,) positive
    rho_star: np.ndarray      # (d,) signed
    U: np.ndarray             # (d, d) orthonormal
    sigma_xx: np.ndarray      # (d, d)
    sigma_yx: np.ndarray      # (d, d)
    regression: np.ndarray    # Sigma^yx Sigma^xx^{-1}
    noise_std: float

    @classmethod
    def make(cls, d: int, rho_pos_count: int, rho_neg_count: int,
             rng: np.random.Generator, noise_std: float = 0.05,
             unit_mu: bool = True) -> "SyntheticGenEigenSetup":
        assert rho_pos_count + rho_neg_count <= d
        # mu_r: default to 1 for all r, so lambda_r* = rho_r* * mu_r = rho_r*.
        # This eliminates the mu-confounder in ordering analysis (paper-1
        # theory predicts ordering by lambda*, which equals rho* iff mu is
        # constant). Pass unit_mu=False for a "realistic" run with random mu.
        if unit_mu:
            mu = np.ones(d)
        else:
            mu = 1.0 + rng.uniform(size=d)
        # rho_r* LINEARLY spaced so all features stay above the noise floor.
        # (Geometric spacing pushes high-index features below the floor at
        # large d, where they never finish learning in the step budget.)
        rho = np.zeros(d)
        if rho_pos_count > 0:
            rho[:rho_pos_count] = np.linspace(1.0, 0.3, rho_pos_count)
        if rho_neg_count > 0:
            rho[rho_pos_count:rho_pos_count + rho_neg_count] = \
                np.linspace(-0.8, -0.3, rho_neg_count)
        # rest stay at 0.
        # Random orthonormal U.
        A = rng.standard_normal((d, d))
        U, _ = np.linalg.qr(A)
        sigma_xx = U @ np.diag(mu) @ U.T
        sigma_yx = U @ np.diag(rho * mu) @ U.T
        regression = sigma_yx @ np.linalg.inv(sigma_xx)
        return cls(d=d, mu=mu, rho_star=rho, U=U, sigma_xx=sigma_xx,
                   sigma_yx=sigma_yx, regression=regression, noise_std=noise_std)

    def sample(self, n: int, rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray]:
        x = rng.multivariate_normal(np.zeros(self.d), self.sigma_xx, size=n)
        y_clean = x @ self.regression.T
        y = y_clean + self.noise_std * rng.standard_normal((n, self.d))
        return x, y


# --------------------------------------------------------------------------- #
# Linear JEPA (depth-L encoder x predictor)                                   #
# --------------------------------------------------------------------------- #

class LinearJEPA(nn.Module):
    """Depth-L linear JEPA: encoder W_1...W_{L-1} maps x -> z, predictor V maps z -> y_hat."""

    def __init__(self, d: int, depth: int, init_scale: float, rng_seed: int = 0):
        super().__init__()
        assert depth >= 2
        torch.manual_seed(rng_seed)
        # Balanced orthogonal init at scale eps: each layer's singular values ~ eps^{1/L}.
        eps_per_layer = init_scale ** (1.0 / depth)
        layers = []
        for _ in range(depth - 1):
            W = torch.empty(d, d)
            nn.init.orthogonal_(W)
            W = eps_per_layer * W
            layers.append(nn.Parameter(W))
        # Predictor V: maps latent z to y_hat. Same dim for simplicity.
        V = torch.empty(d, d)
        nn.init.orthogonal_(V)
        V = eps_per_layer * V
        layers.append(nn.Parameter(V))
        self.weights = nn.ParameterList(layers)
        self.d = d
        self.depth = depth
        self.init_scale = init_scale

    def encode(self, x: torch.Tensor) -> torch.Tensor:
        z = x
        for W in self.weights[:-1]:
            z = z @ W.T
        return z

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        z = self.encode(x)
        y_hat = z @ self.weights[-1].T
        return y_hat

    def composition(self) -> torch.Tensor:
        """Returns the full composition W = V W_{L-1} ... W_1 (so y_hat = x W^T)."""
        W = self.weights[0]
        for layer in self.weights[1:]:
            W = layer @ W
        return W


# --------------------------------------------------------------------------- #
# SIGReg (simplified)                                                          #
# --------------------------------------------------------------------------- #

def sigreg_penalty(z: torch.Tensor, num_projections: int = 64) -> torch.Tensor:
    """SIGReg-style anti-collapse: projects latents onto random unit directions,
    penalises deviation from standard normal moments (mean=0, var=1, simplified
    Epps-Pulley proxy via moment matching up to fourth order)."""
    batch, d = z.shape
    u = torch.randn(num_projections, d, device=z.device)
    u = u / u.norm(dim=1, keepdim=True)
    proj = z @ u.T  # (batch, num_projections)
    # Standardise each projection's distribution to N(0,1) target.
    m1 = proj.mean(dim=0)
    m2 = (proj ** 2).mean(dim=0)
    m3 = (proj ** 3).mean(dim=0)
    m4 = (proj ** 4).mean(dim=0)
    # Target moments of N(0,1): 0, 1, 0, 3.
    penalty = (m1 ** 2).mean() + ((m2 - 1.0) ** 2).mean() \
            + (m3 ** 2).mean() + ((m4 - 3.0) ** 2).mean()
    return penalty


# --------------------------------------------------------------------------- #
# Training + trajectory logging                                                #
# --------------------------------------------------------------------------- #

def diagonal_amplitudes(model: LinearJEPA, setup: SyntheticGenEigenSetup) -> np.ndarray:
    """Project the model's composition into the generalised eigenbasis U of
    (Sigma^xx, Sigma^yx) and return the diagonal amplitudes sigma_r(t).

    The 'diagonal amplitude' in our paper notation: project W = V W_{L-1}...W_1
    into the (U, U) basis, take the diagonal."""
    with torch.no_grad():
        W = model.composition().cpu().numpy()           # (d, d)
        U = setup.U                                     # (d, d) orthonormal
        W_in_U = U.T @ W @ U                            # change of basis
        diag = np.diag(W_in_U)
    return diag


def train_and_log(
    model: LinearJEPA,
    setup: SyntheticGenEigenSetup,
    x: torch.Tensor, y: torch.Tensor,
    *,
    steps: int, lr: float, batch: int,
    sigreg_weight: float,
    log_every: int = 50,
    device: str = "cpu",
) -> dict:
    """Train MSE + sigreg_weight * SIGReg. Log diagonal amplitudes every
    `log_every` steps."""
    model.to(device).train()
    opt = torch.optim.SGD(model.parameters(), lr=lr)
    n = x.shape[0]
    losses = []
    sigreg_losses = []
    trajectories = []      # list of (step, sigma diag)
    for step in range(steps):
        idx = torch.randint(0, n, (batch,))
        xb = x[idx].to(device)
        yb = y[idx].to(device)
        y_hat = model(xb)
        mse = ((y_hat - yb) ** 2).mean()
        if sigreg_weight > 0.0:
            z = model.encode(xb)
            sg = sigreg_penalty(z, num_projections=32)
            loss = mse + sigreg_weight * sg
        else:
            sg = torch.tensor(0.0)
            loss = mse
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % log_every == 0 or step == steps - 1:
            losses.append(float(mse.item()))
            sigreg_losses.append(float(sg.item()))
            diag = diagonal_amplitudes(model, setup)
            trajectories.append((step, diag))
    return dict(losses=losses, sigreg_losses=sigreg_losses,
                trajectories=trajectories)


# --------------------------------------------------------------------------- #
# Analysis                                                                     #
# --------------------------------------------------------------------------- #

def critical_times(trajectories: list[tuple[int, np.ndarray]],
                   plateau_frac: float = 0.5) -> np.ndarray:
    """For each feature r, return the first step at which |sigma_r(t)| >=
    plateau_frac * |sigma_r(t_final)|. NaN if never reached."""
    steps = np.array([s for s, _ in trajectories])
    diags = np.stack([d for _, d in trajectories])     # (T, d)
    final = diags[-1]
    threshold = plateau_frac * np.abs(final)
    d = diags.shape[1]
    out = np.full(d, np.nan)
    for r in range(d):
        if np.abs(final[r]) < 1e-6:
            continue
        hits = np.where(np.abs(diags[:, r]) >= threshold[r])[0]
        if len(hits) > 0:
            out[r] = steps[hits[0]]
    return out


def rank_correlation(a: np.ndarray, b: np.ndarray) -> float:
    """Spearman rank correlation, ignoring NaN."""
    mask = ~(np.isnan(a) | np.isnan(b))
    if mask.sum() < 3:
        return float("nan")
    ra = np.argsort(np.argsort(a[mask]))
    rb = np.argsort(np.argsort(b[mask]))
    return float(np.corrcoef(ra, rb)[0, 1])


# --------------------------------------------------------------------------- #
# Main                                                                         #
# --------------------------------------------------------------------------- #

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=4000)
    ap.add_argument("--d", type=int, default=10)
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--eps", type=float, default=0.05)
    ap.add_argument("--steps", type=int, default=8000)
    ap.add_argument("--lr", type=float, default=0.05)
    ap.add_argument("--batch", type=int, default=128)
    ap.add_argument("--lambd", type=float, default=0.1,
                    help="SIGReg weight for the LeWM-style run.")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", type=str, default="experiments/results_sigreg_probe")
    args = ap.parse_args()

    rng = np.random.default_rng(args.seed)
    setup = SyntheticGenEigenSetup.make(args.d, rho_pos_count=5, rho_neg_count=3,
                                        rng=rng)
    print(f"Synthetic setup: d={args.d}, rho* = {setup.rho_star}")

    x_np, y_np = setup.sample(args.n, rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)

    print("\n=== Variant A: MSE only ===")
    torch.manual_seed(args.seed)
    model_a = LinearJEPA(args.d, args.depth, args.eps, rng_seed=args.seed)
    out_a = train_and_log(model_a, setup, x, y,
                           steps=args.steps, lr=args.lr, batch=args.batch,
                           sigreg_weight=0.0)
    print(f"final MSE = {out_a['losses'][-1]:.4f}")

    print(f"\n=== Variant B: MSE + {args.lambd} * SIGReg ===")
    torch.manual_seed(args.seed)
    model_b = LinearJEPA(args.d, args.depth, args.eps, rng_seed=args.seed)
    out_b = train_and_log(model_b, setup, x, y,
                           steps=args.steps, lr=args.lr, batch=args.batch,
                           sigreg_weight=args.lambd)
    print(f"final MSE = {out_b['losses'][-1]:.4f}  "
          f"final SIGReg = {out_b['sigreg_losses'][-1]:.4f}")

    ct_a = critical_times(out_a["trajectories"])
    ct_b = critical_times(out_b["trajectories"])
    abs_rho = np.abs(setup.rho_star)

    print("\n=== Analysis ===")
    print(f"feature   |rho*|        ct(A)     ct(B)")
    for r in range(args.d):
        ca = ("---" if math.isnan(ct_a[r]) else f"{int(ct_a[r]):>6}")
        cb = ("---" if math.isnan(ct_b[r]) else f"{int(ct_b[r]):>6}")
        print(f"  {r:>2}      {abs_rho[r]:.4f}     {ca}    {cb}")

    # Focus on POSITIVE-rho features only: the cleanest theoretical regime.
    pos_mask = setup.rho_star > 1e-6
    rho_pos = setup.rho_star[pos_mask]
    ct_a_pos = ct_a[pos_mask]
    ct_b_pos = ct_b[pos_mask]
    rho_vs_ct_a = rank_correlation(rho_pos, ct_a_pos)
    rho_vs_ct_b = rank_correlation(rho_pos, ct_b_pos)
    print(f"\nSpearman rank correlation rho* vs critical-time (positive-rho features only):")
    print(f"  Variant A (MSE only):       rho_s = {rho_vs_ct_a:+.3f}")
    print(f"  Variant B (MSE + SIGReg):   rho_s = {rho_vs_ct_b:+.3f}")
    # Expected sign: NEGATIVE (larger rho* -> smaller critical time -> faster).
    print(f"\n(Larger rho* should give smaller critical time; expect rho_s < 0.)")
    if rho_vs_ct_b < -0.6 and rho_vs_ct_a < -0.6:
        verdict = "ordering survives SIGReg"
    elif rho_vs_ct_a < -0.6 and rho_vs_ct_b > -0.3:
        verdict = "ordering destroyed by SIGReg"
    else:
        verdict = "ambiguous; tune hyperparameters or re-run"
    print(f"\nVerdict: {verdict}")

    # Persist.
    out_dir = pathlib.Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    np.savez(
        out_dir / f"probe_seed{args.seed}.npz",
        rho_star=setup.rho_star,
        mu=setup.mu,
        ct_a=ct_a,
        ct_b=ct_b,
        losses_a=np.array(out_a["losses"]),
        losses_b=np.array(out_b["losses"]),
        traj_a=np.stack([d for _, d in out_a["trajectories"]]),
        traj_b=np.stack([d for _, d in out_b["trajectories"]]),
        steps_logged=np.array([s for s, _ in out_a["trajectories"]]),
    )
    with open(out_dir / f"probe_seed{args.seed}.json", "w") as f:
        json.dump({
            "rho_star": setup.rho_star.tolist(),
            "mu": setup.mu.tolist(),
            "spearman_a": rho_vs_ct_a,
            "spearman_b": rho_vs_ct_b,
            "verdict": verdict,
            "args": vars(args),
        }, f, indent=2)
    print(f"\nWrote {out_dir}/probe_seed{args.seed}.{{npz,json}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
