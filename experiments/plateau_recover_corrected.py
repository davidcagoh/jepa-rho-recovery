"""Corrected plateau_recover() — empirical validation.

Two corrections relative to session-90's initial ALGORITHM_AND_EXPERIMENT_PLAN.md:
  1. Aligned init: Wbar(0) = ε·I, V(0) = ε·I (paper-1's hypothesis regime).
     Generic orthogonal init does not satisfy σ_r(0) = ε.
  2. Recovery formula: ρ̂_r = sign(σ_r) · |σ_r|^L
     (paper had σ^(1/L); empirically wrong by ~0.5 across the spectrum).

Empirical plateau under these corrections: σ_r → ρ_r^(1/L) (= √ρ_r for L=2).
So σ_r^L → ρ_r and ρ̂_r = σ^L recovers ρ.

ε-sweep test: error should scale like ε^(1/L)·|log ε| (Saxe-style rate).
"""

from __future__ import annotations

import argparse
import json
import logging
from pathlib import Path

import numpy as np
import torch
from torch import nn

from plateau_recover_smoke import SyntheticSetup

logger = logging.getLogger("plateau_recover_corrected")
OUT_DIR = Path(__file__).resolve().parent / "results_plateau_smoke"


class AlignedJEPA(nn.Module):
    """Encoder Wbar + predictor V, aligned init: each = ε·I."""

    def __init__(self, d: int, eps: float, depth: int = 2):
        super().__init__()
        assert depth == 2, "Aligned-init prototype is for depth-2; depth-L extension TBD"
        self.Wbar = nn.Parameter(eps * torch.eye(d, dtype=torch.float32))
        self.V    = nn.Parameter(eps * torch.eye(d, dtype=torch.float32))
        self.d = d
        self.depth = depth

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return x @ self.Wbar.T @ self.V.T


def plateau_recover_corrected(sigma_T: np.ndarray, depth: int) -> np.ndarray:
    """ρ̂_r = sign(σ_r) · |σ_r|^L  (corrected formula)."""
    return np.sign(sigma_T) * np.abs(sigma_T) ** depth


def detect_plateau_step(sigma_traj: np.ndarray, window: int = 8, tol: float = 5e-4) -> int:
    T, d = sigma_traj.shape
    if T <= window + 1:
        return T - 1
    for t in range(window, T):
        slab = sigma_traj[t - window : t + 1]
        max_local = np.abs(np.diff(slab, axis=0)).max(axis=0)
        scale = np.maximum(np.abs(sigma_traj[t]), 1e-8)
        if np.all(max_local / scale < tol):
            return t
    return T - 1


def train_one(setup: SyntheticSetup, eps: float, *, depth: int, steps: int,
              lr: float, n: int, seed: int, log_every: int) -> dict:
    rng = np.random.default_rng(seed)
    x_np, y_np = setup.sample(n, rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)
    torch.manual_seed(seed)
    model = AlignedJEPA(setup.d, eps, depth=depth)
    opt = torch.optim.SGD(model.parameters(), lr=lr)

    log_steps, traj = [0], [np.diag(setup.U.T @ model.Wbar.detach().cpu().numpy() @ setup.U)]
    for step in range(1, steps + 1):
        loss = ((model(x) - y) ** 2).mean()
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % log_every == 0 or step == steps:
            with torch.no_grad():
                W = model.Wbar.detach().cpu().numpy()
            log_steps.append(step)
            traj.append(np.diag(setup.U.T @ W @ setup.U))
    sigma_traj = np.stack(traj)
    plateau_idx = detect_plateau_step(sigma_traj)
    sigma_T = sigma_traj[plateau_idx]
    rho_hat = plateau_recover_corrected(sigma_T, depth)
    err_inf = float(np.max(np.abs(rho_hat - setup.rho_star)))
    err_l2 = float(np.linalg.norm(rho_hat - setup.rho_star) / np.sqrt(setup.d))
    return {
        "eps": eps, "seed": seed, "plateau_step": int(log_steps[plateau_idx]),
        "sigma_T": sigma_T.tolist(), "rho_hat": rho_hat.tolist(),
        "rho_star": setup.rho_star.tolist(),
        "err_inf": err_inf, "err_l2": err_l2,
    }


def run_sweep(d: int, depth: int, epsilons: list[float], n: int, lr: float,
              steps: int, seeds: list[int], log_every: int) -> dict:
    rows = []
    for eps in epsilons:
        per_seed = []
        for seed in seeds:
            setup = SyntheticSetup.positive_branch(d, np.random.default_rng(2000 + seed))
            per_seed.append(train_one(setup, eps, depth=depth, steps=steps,
                                       lr=lr, n=n, seed=seed, log_every=log_every))
        err_inf_vals = [s["err_inf"] for s in per_seed]
        rows.append({
            "eps": eps,
            "err_inf_mean": float(np.mean(err_inf_vals)),
            "err_inf_std": float(np.std(err_inf_vals)),
            "err_l2_mean": float(np.mean([s["err_l2"] for s in per_seed])),
            "per_seed": per_seed,
        })

    eps_arr = np.array([r["eps"] for r in rows])
    err_arr = np.array([r["err_inf_mean"] for r in rows])
    valid = err_arr > 0
    log_eps = np.log(eps_arr[valid])
    log_err = np.log(err_arr[valid])
    log_corrected = log_err - np.log(np.abs(log_eps))
    slope, intercept = np.polyfit(log_eps, log_corrected, 1)

    # Raw slope (without |log ε| correction) for diagnostic.
    raw_slope, _ = np.polyfit(log_eps, log_err, 1)

    return {
        "config": dict(d=d, depth=depth, n=n, lr=lr, steps=steps, seeds=seeds,
                       epsilons=list(epsilons), log_every=log_every),
        "rows": rows,
        "fit": {
            "slope_corrected": float(slope),
            "theory_slope": 1.0 / depth,
            "raw_slope": float(raw_slope),
        },
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--d", type=int, default=10)
    p.add_argument("--depth", type=int, default=2)
    p.add_argument("--n", type=int, default=4096)
    p.add_argument("--lr", type=float, default=0.05)
    p.add_argument("--steps", type=int, default=80000)
    p.add_argument("--log-every", type=int, default=200)
    p.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    p.add_argument("--epsilons", type=float, nargs="+",
                   default=[3e-1, 1e-1, 3e-2, 1e-2, 3e-3])
    p.add_argument("--out", type=str, default=str(OUT_DIR / "corrected_sweep.json"))
    return p.parse_args()


def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    args = parse_args()
    result = run_sweep(args.d, args.depth, args.epsilons, args.n, args.lr,
                       args.steps, args.seeds, args.log_every)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(result, f, indent=2)

    fit = result["fit"]
    logger.info("Corrected algorithm: ρ̂ = σ^L, aligned init")
    logger.info("Fit: theory slope (1/L) = %.3f, measured corrected slope = %.3f, raw slope = %.3f",
                fit["theory_slope"], fit["slope_corrected"], fit["raw_slope"])
    for row in result["rows"]:
        logger.info("  eps=%.0e  err_inf = %.5f ± %.5f   err_l2 = %.5f",
                    row["eps"], row["err_inf_mean"], row["err_inf_std"], row["err_l2_mean"])


if __name__ == "__main__":
    main()
