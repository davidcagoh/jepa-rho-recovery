"""Smoke test for plateau_recover() — paper-2 §6 algorithm validation.

Reuses the synthetic gen-eigen setup + linear JEPA from
sigreg_ordering_probe.py, but specialised to the positive-branch
plateau-path recovery formula:

    rho_hat[r] = sign(sigma_r(T)) * |sigma_r(T)|^(1/L)

evaluated at a plateau-detected stopping time T.

Goals of this script
--------------------
1. Empirical validation of the headline rate. Sweep epsilon over
   several decades; check that ||rho_hat - rho*||_inf scales like
   epsilon^(1/L) * |log epsilon| (theory) within an order of
   magnitude.
2. Quasi-static smoke test. Record the residual

       r(t) := dot(sigma) - (lambda*_r * sigma^(3 - 1/L) - mu_r * sigma^3)

   along the trajectory at standard JEPA learning rates. If the
   normalised residual stays small the quasi-static hypothesis
   transports to practice. If it doesn't, paper-2's algorithm
   framing has to be narrowed to a small-lr regime.

Run
---
    python plateau_recover_smoke.py [--seeds 3] [--steps 12000] [--lr 1e-2]

Outputs go to experiments/results_plateau_smoke/.
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import numpy as np
import torch
from torch import nn

logger = logging.getLogger("plateau_recover_smoke")

OUT_DIR = Path(__file__).resolve().parent / "results_plateau_smoke"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# --------------------------------------------------------------------------- #
# Synthetic setup (positive-only spectrum for paper-2 headline)               #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class SyntheticSetup:
    d: int
    rho_star: np.ndarray  # (d,) signed ground-truth ρ_r*
    mu: np.ndarray        # (d,) generalised denominators
    U: np.ndarray         # (d, d) generalised eigenbasis (orthonormal in this build)
    sigma_xx: np.ndarray
    sigma_yx: np.ndarray
    regression: np.ndarray
    noise_std: float

    @classmethod
    def positive_branch(
        cls,
        d: int,
        rng: np.random.Generator,
        noise_std: float = 0.02,
    ) -> "SyntheticSetup":
        """All-positive linearly-spaced ρ_r*, unit μ. Matches paper-2 §7.1 setup."""
        mu = np.ones(d)
        rho = np.linspace(1.0, 0.2, d)
        A = rng.standard_normal((d, d))
        U, _ = np.linalg.qr(A)
        sigma_xx = U @ np.diag(mu) @ U.T
        sigma_yx = U @ np.diag(rho * mu) @ U.T
        regression = sigma_yx @ np.linalg.inv(sigma_xx)
        return cls(
            d=d,
            rho_star=rho,
            mu=mu,
            U=U,
            sigma_xx=sigma_xx,
            sigma_yx=sigma_yx,
            regression=regression,
            noise_std=noise_std,
        )

    def sample(
        self, n: int, rng: np.random.Generator
    ) -> tuple[np.ndarray, np.ndarray]:
        x = rng.multivariate_normal(np.zeros(self.d), self.sigma_xx, size=n)
        y_clean = x @ self.regression.T
        y = y_clean + self.noise_std * rng.standard_normal((n, self.d))
        return x, y


# --------------------------------------------------------------------------- #
# Linear JEPA (depth-L)                                                       #
# --------------------------------------------------------------------------- #


class LinearJEPA(nn.Module):
    """Depth-L linear network. Balanced orthogonal init at scale eps^(1/L)."""

    def __init__(self, d: int, depth: int, init_scale: float, rng_seed: int = 0):
        super().__init__()
        assert depth >= 2
        torch.manual_seed(rng_seed)
        eps_per_layer = init_scale ** (1.0 / depth)
        layers = []
        for _ in range(depth):
            W = torch.empty(d, d)
            nn.init.orthogonal_(W)
            layers.append(nn.Parameter(eps_per_layer * W))
        self.weights = nn.ParameterList(layers)
        self.d = d
        self.depth = depth
        self.init_scale = init_scale

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        z = x
        for W in self.weights:
            z = z @ W.T
        return z

    def composition(self) -> torch.Tensor:
        """Full composition W = W_L @ ... @ W_1, so y_hat = x W^T."""
        W = self.weights[0]
        for layer in self.weights[1:]:
            W = layer @ W
        return W


# --------------------------------------------------------------------------- #
# Trajectory logging in the generalised eigenbasis                            #
# --------------------------------------------------------------------------- #


def diagonal_amplitudes(model: LinearJEPA, U: np.ndarray) -> np.ndarray:
    with torch.no_grad():
        W = model.composition().cpu().numpy()
    return np.diag(U.T @ W @ U)


def train_and_collect(
    setup: SyntheticSetup,
    *,
    eps: float,
    depth: int,
    n: int,
    steps: int,
    lr: float,
    batch: int,
    seed: int,
    log_every: int,
) -> dict:
    rng = np.random.default_rng(seed)
    x_np, y_np = setup.sample(n, rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)
    model = LinearJEPA(setup.d, depth, init_scale=eps, rng_seed=seed)
    opt = torch.optim.SGD(model.parameters(), lr=lr)

    traj_steps: list[int] = []
    traj_sigma: list[np.ndarray] = []

    # initial snapshot
    traj_steps.append(0)
    traj_sigma.append(diagonal_amplitudes(model, setup.U))

    full_batch = batch <= 0 or batch >= n

    for step in range(1, steps + 1):
        if full_batch:
            xb, yb = x, y
        else:
            idx = torch.randint(0, n, (batch,))
            xb = x[idx]
            yb = y[idx]
        y_hat = model(xb)
        loss = ((y_hat - yb) ** 2).mean()
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % log_every == 0 or step == steps:
            traj_steps.append(step)
            traj_sigma.append(diagonal_amplitudes(model, setup.U))

    return {
        "steps": np.array(traj_steps),
        "sigma": np.stack(traj_sigma, axis=0),  # (T_logged, d)
    }


# --------------------------------------------------------------------------- #
# Plateau detector + ρ̂                                                       #
# --------------------------------------------------------------------------- #


def detect_plateau_step(
    sigma_traj: np.ndarray,
    *,
    window: int = 8,
    tol: float = 1e-3,
) -> int:
    """Return the logged-trajectory index at which all features have settled.

    Plateau condition: max over r of |Δσ_r| across the trailing window
    falls below tol relative to the current |σ_r|.
    """
    T, d = sigma_traj.shape
    if T <= window + 1:
        return T - 1
    for t in range(window, T):
        slab = sigma_traj[t - window : t + 1]   # (window+1, d)
        max_local = np.abs(np.diff(slab, axis=0)).max(axis=0)
        scale = np.maximum(np.abs(sigma_traj[t]), 1e-8)
        if np.all(max_local / scale < tol):
            return t
    return T - 1


def plateau_recover(
    sigma_final: np.ndarray, depth: int
) -> np.ndarray:
    """ρ̂ under paper-2 convention: ρ̂[r] = sign(σ_r) · |σ_r|^(1/L).

    NOTE (session 90): empirical σ-convention probe (`sigma_convention_probe.py`)
    found that the natural diagonal amplitude σ_A = u^T W̄ v plateaus at ρ_r, not
    ρ_r^L. Use `plateau_recover_native` for the empirically validated formula.
    """
    return np.sign(sigma_final) * np.abs(sigma_final) ** (1.0 / depth)


def plateau_recover_native(sigma_final: np.ndarray, depth: int) -> np.ndarray:
    """Empirical recovery: σ_A^∞ ≈ ρ_r directly, so ρ̂ = σ_A."""
    del depth  # unused in this convention
    return sigma_final.copy()


# --------------------------------------------------------------------------- #
# Quasi-static residual diagnostic                                            #
# --------------------------------------------------------------------------- #


def quasi_static_residual(
    setup: SyntheticSetup,
    sigma_traj: np.ndarray,
    step_idx: np.ndarray,
    lr: float,
    depth: int,
) -> dict:
    """Compute the normalised residual

        r_r(t) := dot_sigma_r(t) - (lambda_r * sigma_r^(3 - 1/L) - mu_r * sigma_r^3)

    where lambda_r = mu_r * rho_r*.

    Returns per-step max and mean residuals, normalised by the
    instantaneous RHS magnitude. Small values (≪ 1) indicate the
    trajectory is well-described by the Bernoulli quasi-static ODE.
    """
    sig = sigma_traj
    rho = setup.rho_star
    mu = setup.mu
    lam = mu * rho

    # Numerical derivative across logged samples. The *physical* time
    # between two logged samples is lr * (number of grad steps between
    # them). For SGD that's lr * delta_step.
    dt = np.diff(step_idx).astype(float) * lr  # (T-1,)
    dsig = np.diff(sig, axis=0) / dt[:, None]  # (T-1, d)
    sig_mid = 0.5 * (sig[:-1] + sig[1:])       # (T-1, d)

    exponent = 3.0 - 1.0 / depth
    rhs = lam[None, :] * np.sign(sig_mid) * np.abs(sig_mid) ** exponent \
        - mu[None, :] * sig_mid ** 3            # (T-1, d)

    rhs_scale = np.maximum(np.abs(rhs), 1e-8)
    rel_residual = np.abs(dsig - rhs) / rhs_scale

    return {
        "rel_residual_mean_per_step": rel_residual.mean(axis=1),
        "rel_residual_max_per_step": rel_residual.max(axis=1),
        "rel_residual_global_mean": float(rel_residual.mean()),
        "rel_residual_global_max": float(rel_residual.max()),
    }


# --------------------------------------------------------------------------- #
# ε-sweep driver                                                              #
# --------------------------------------------------------------------------- #


def run_eps_sweep(
    *,
    d: int,
    depth: int,
    epsilons: Iterable[float],
    n: int,
    lr: float,
    batch: int,
    steps: int,
    seeds: Iterable[int],
    log_every: int,
) -> dict:
    rows = []
    quasi = []
    for eps in epsilons:
        per_seed = []
        for seed in seeds:
            setup = SyntheticSetup.positive_branch(d, np.random.default_rng(1000 + seed))
            traj = train_and_collect(
                setup,
                eps=eps,
                depth=depth,
                n=n,
                steps=steps,
                lr=lr,
                batch=batch,
                seed=seed,
                log_every=log_every,
            )
            plateau_idx = detect_plateau_step(traj["sigma"])
            sigma_T = traj["sigma"][plateau_idx]
            rho_hat_paper = plateau_recover(sigma_T, depth)
            rho_hat_native = plateau_recover_native(sigma_T, depth)
            rho_hat = rho_hat_native       # use native as headline
            err_inf = float(np.max(np.abs(rho_hat - setup.rho_star)))
            err_l2 = float(np.linalg.norm(rho_hat - setup.rho_star) / np.sqrt(d))
            err_inf_paper = float(np.max(np.abs(rho_hat_paper - setup.rho_star)))
            qs = quasi_static_residual(
                setup, traj["sigma"], traj["steps"], lr, depth
            )
            per_seed.append({
                "seed": seed,
                "plateau_step": int(traj["steps"][plateau_idx]),
                "plateau_logged_idx": int(plateau_idx),
                "rho_hat_native": rho_hat.tolist(),
                "rho_hat_paper": rho_hat_paper.tolist(),
                "rho_star": setup.rho_star.tolist(),
                "err_inf": err_inf,
                "err_inf_paper": err_inf_paper,
                "err_l2": err_l2,
                "qs_residual_global_mean": qs["rel_residual_global_mean"],
                "qs_residual_global_max": qs["rel_residual_global_max"],
                "final_sigma": sigma_T.tolist(),
            })
            quasi.append({
                "eps": eps,
                "seed": seed,
                **{k: v for k, v in qs.items() if k.startswith("rel_residual_global")},
            })

        err_inf_vals = [s["err_inf"] for s in per_seed]
        err_l2_vals = [s["err_l2"] for s in per_seed]
        qs_mean_vals = [s["qs_residual_global_mean"] for s in per_seed]
        rows.append({
            "eps": eps,
            "err_inf_mean": float(np.mean(err_inf_vals)),
            "err_inf_std": float(np.std(err_inf_vals)),
            "err_l2_mean": float(np.mean(err_l2_vals)),
            "qs_residual_global_mean_mean": float(np.mean(qs_mean_vals)),
            "per_seed": per_seed,
        })

    # log-log slope of err vs eps
    eps_arr = np.array([r["eps"] for r in rows])
    err_arr = np.array([r["err_inf_mean"] for r in rows])
    # theory: err ≈ C · eps^(1/L) · |log eps|. Fit log(err / |log eps|) ~ log(eps).
    valid = err_arr > 0
    log_eps = np.log(eps_arr[valid])
    log_err = np.log(err_arr[valid])
    log_corrected = log_err - np.log(np.abs(np.log(eps_arr[valid])))
    slope, intercept = np.polyfit(log_eps, log_corrected, 1)
    theory_slope = 1.0 / depth

    return {
        "config": {
            "d": d, "depth": depth, "n": n, "lr": lr, "batch": batch,
            "steps": steps, "log_every": log_every,
            "seeds": list(seeds), "epsilons": list(epsilons),
        },
        "rows": rows,
        "quasi": quasi,
        "fit": {
            "slope_corrected": float(slope),
            "intercept_corrected": float(intercept),
            "theory_slope": theory_slope,
            "abs_deviation_from_theory": float(abs(slope - theory_slope)),
        },
    }


# --------------------------------------------------------------------------- #
# CLI                                                                         #
# --------------------------------------------------------------------------- #


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--d", type=int, default=10)
    p.add_argument("--depth", type=int, default=2)
    p.add_argument("--n", type=int, default=4096)
    p.add_argument("--batch", type=int, default=256)
    p.add_argument("--lr", type=float, default=1e-2)
    p.add_argument("--steps", type=int, default=12000)
    p.add_argument("--log-every", type=int, default=100)
    p.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    p.add_argument(
        "--epsilons",
        type=float,
        nargs="+",
        default=[1e-1, 3e-2, 1e-2, 3e-3, 1e-3],
    )
    p.add_argument("--out", type=str, default=str(OUT_DIR / "smoke_results.json"))
    return p.parse_args()


def main() -> int:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(name)s %(levelname)s %(message)s",
    )
    args = parse_args()
    logger.info("Running plateau_recover smoke test: %s", vars(args))
    result = run_eps_sweep(
        d=args.d,
        depth=args.depth,
        epsilons=args.epsilons,
        n=args.n,
        lr=args.lr,
        batch=args.batch,
        steps=args.steps,
        seeds=args.seeds,
        log_every=args.log_every,
    )
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        json.dump(result, f, indent=2)
    logger.info("Wrote results to %s", out_path)

    # Console summary.
    fit = result["fit"]
    logger.info(
        "Fit (theory slope %.3f): measured corrected slope %.3f (|Δ|=%.3f)",
        fit["theory_slope"],
        fit["slope_corrected"],
        fit["abs_deviation_from_theory"],
    )
    for row in result["rows"]:
        logger.info(
            "eps=%.0e  err_inf=%.4f±%.4f  err_l2=%.4f  qs_residual_mean=%.3f",
            row["eps"],
            row["err_inf_mean"],
            row["err_inf_std"],
            row["err_l2_mean"],
            row["qs_residual_global_mean_mean"],
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
