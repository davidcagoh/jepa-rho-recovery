"""Definitive test: which Bernoulli ODE form matches the JEPA gradient flow?

Two candidates for σ̇_r as a function of σ_r:

  Paper-1 form (JEPA.lean:687-697; PlateauEstimator.lean):
      σ̇ = L · λ · σ^(3-1/L) · (1 − σ^(1/L)/ρ)
    Plateau: σ = ρ^L

  Saxe (2014) deep-linear form:
      σ̇ = L · μ · σ^(2-1/L) · (ρ − σ^L)
    Plateau: σ = ρ^(1/L)
    [Equivalently: σ̇ = L · λ · σ^(2-1/L) · (1 − σ^L/ρ)]

We've already shown the empirical plateau is ρ^(1/L). Now fit σ̇/σ vs σ
across the trajectory to verify the FORM of the ODE.

Methodology
-----------
- Aligned init Wbar(0) = ε·I, V(0) = ε·I (paper-1 hypothesis regime).
- Record (σ_r(t), σ_r(t+dt)) pairs along trajectory.
- For each pair compute numerical σ̇ ≈ (σ(t+dt) − σ(t)) / dt
  where dt = lr (full-batch GD time step in continuous-time units).
- For each candidate ODE: evaluate residual `σ̇ − f(σ; λ, μ, ρ)` and
  the *relative* residual. The form with consistently small residual wins.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path

import numpy as np
import torch
from torch import nn

from plateau_recover_smoke import SyntheticSetup
from aligned_init_probe import AlignedJEPA

logger = logging.getLogger("ode_form_fit")
OUT = Path(__file__).resolve().parent / "results_plateau_smoke" / "ode_form_fit.json"


def run(d: int = 6, eps: float = 0.05, steps: int = 40000,
        lr: float = 0.02, n: int = 4096, seed: int = 0,
        log_every: int = 50) -> dict:
    rng = np.random.default_rng(seed)
    setup = SyntheticSetup.positive_branch(d, rng)
    x_np, y_np = setup.sample(n, rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)
    model = AlignedJEPA(d, setup.U, eps, seed)
    opt = torch.optim.SGD(model.parameters(), lr=lr)

    times = []
    sigmas = []  # list of (d,) encoder diag

    def snap(step: int):
        with torch.no_grad():
            W = model.Wbar.detach().cpu().numpy()
        sig = np.diag(setup.U.T @ W @ setup.U)
        times.append(step * lr)
        sigmas.append(sig)

    snap(0)
    for step in range(1, steps + 1):
        loss = ((model(x) - y) ** 2).mean()
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % log_every == 0:
            snap(step)

    times = np.array(times)
    sigmas = np.stack(sigmas)  # (T, d)
    rho = setup.rho_star
    mu = setup.mu
    lam = rho * mu
    L = 2

    # Numerical derivative on logged samples.
    dt = np.diff(times)               # (T-1,)
    dsig = np.diff(sigmas, axis=0) / dt[:, None]   # (T-1, d)
    sig_mid = 0.5 * (sigmas[:-1] + sigmas[1:])     # (T-1, d)

    # Candidate ODE evaluations (positive σ regime).
    sig_pos = np.clip(sig_mid, 1e-8, None)

    paper_rhs = (
        L * lam[None, :] * sig_pos ** (3 - 1.0 / L)
        * (1.0 - sig_pos ** (1.0 / L) / rho[None, :])
    )
    saxe_rhs = (
        L * mu[None, :] * sig_pos ** (2 - 1.0 / L)
        * (rho[None, :] - sig_pos ** L)
    )

    # Filter to "in motion" region: |dsig| > some floor (avoid noise around plateau).
    motion_mask = np.abs(dsig) > 0.001

    def stats(rhs):
        residual = dsig - rhs
        abs_res = np.abs(residual)
        rel = abs_res / (np.abs(rhs) + 1e-8)
        return {
            "mean_abs_residual_all": float(abs_res.mean()),
            "mean_abs_residual_motion": float(abs_res[motion_mask].mean()),
            "mean_rel_residual_motion": float(rel[motion_mask].mean()),
            "max_rel_residual_motion": float(rel[motion_mask].max()),
            "median_rel_residual_motion": float(np.median(rel[motion_mask])),
            "n_motion_samples": int(motion_mask.sum()),
        }

    paper_stats = stats(paper_rhs)
    saxe_stats = stats(saxe_rhs)

    # Per-feature: at peak velocity, which form is closer?
    # Find the time of max |dsig| per feature; report dsig and both RHS predictions.
    peak_idx = np.argmax(np.abs(dsig), axis=0)
    per_feature = []
    for r in range(d):
        i = peak_idx[r]
        per_feature.append({
            "r": r, "rho": float(rho[r]),
            "sigma": float(sig_mid[i, r]),
            "dsig_measured": float(dsig[i, r]),
            "paper_rhs": float(paper_rhs[i, r]),
            "saxe_rhs": float(saxe_rhs[i, r]),
            "paper_ratio": float(paper_rhs[i, r] / dsig[i, r]) if dsig[i, r] != 0 else None,
            "saxe_ratio": float(saxe_rhs[i, r] / dsig[i, r]) if dsig[i, r] != 0 else None,
        })

    return {
        "config": dict(d=d, eps=eps, steps=steps, lr=lr, n=n, seed=seed),
        "paper_form": paper_stats,
        "saxe_form": saxe_stats,
        "per_feature_at_peak_dsig": per_feature,
    }


def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    result = run()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w") as f:
        json.dump(result, f, indent=2)

    p = result["paper_form"]
    s = result["saxe_form"]
    logger.info("ODE-form fit (n_motion=%d samples each)", p["n_motion_samples"])
    logger.info("                       Paper-1 form     Saxe form")
    logger.info("  median rel residual : %12.4f   %12.4f", p["median_rel_residual_motion"], s["median_rel_residual_motion"])
    logger.info("  mean   rel residual : %12.4f   %12.4f", p["mean_rel_residual_motion"], s["mean_rel_residual_motion"])
    logger.info("  max    rel residual : %12.4f   %12.4f", p["max_rel_residual_motion"], s["max_rel_residual_motion"])
    logger.info("Per-feature peak-velocity comparison:")
    logger.info("  r   rho      sigma     dsig_meas     paper_rhs    saxe_rhs   paper/meas  saxe/meas")
    for f in result["per_feature_at_peak_dsig"]:
        logger.info(
            "  %d   %.3f    %+8.4f   %+10.4f   %+10.4f  %+10.4f   %8.3f   %8.3f",
            f["r"], f["rho"], f["sigma"], f["dsig_measured"],
            f["paper_rhs"], f["saxe_rhs"],
            f["paper_ratio"] if f["paper_ratio"] is not None else float("nan"),
            f["saxe_ratio"] if f["saxe_ratio"] is not None else float("nan"),
        )


if __name__ == "__main__":
    main()
