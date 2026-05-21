"""Diagnostic: which σ-convention matches paper-2's Bernoulli ODE?

Question
--------
Paper-2 §4–§5 claims the diagonal-amplitude trajectory follows
    σ̇_r = λ_r * σ_r^(3 - 1/L) - μ_r * σ_r^3
with plateau σ_r^∞ = ρ_r^L, and reads off ρ̂_r = σ_r(T)^(1/L).

Empirically, three plausible σ-conventions sit on the surface:

  A. Composition diagonal:    σ_A := u_r^T W̄ v_r,      W̄ = W_L · W_{L-1} ... W_1
  B. Composition r-th SV:     σ_B := s_r(W̄)
  C. Per-layer r-th SV:       σ_C := s_r(W_1)           (same for all layers under balanced init)

Plateau predictions (when W̄ → regression matrix R = U diag(ρ) U^T):
  A.  σ_A^∞  = ρ_r              (since u_r = U[:,r], v_r = U[:,r] in this setup)
  B.  σ_B^∞  = |ρ_r|            (singular value of R)
  C.  σ_C^∞  = |ρ_r|^(1/L)      (per-layer SV; composition SV is the L-th power)

None of these directly match ρ_r^L unless we redefine σ as e.g.
    σ' := (composition SV)^L  =  |ρ_r|^L  (trivially equals ρ_r^L)

This script measures all three conventions on a small synthetic problem and
reports which matches the paper's plateau prediction.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path

import numpy as np
import torch
from torch import nn

from plateau_recover_smoke import (
    LinearJEPA,
    SyntheticSetup,
    diagonal_amplitudes,
)

logger = logging.getLogger("sigma_convention_probe")

OUT = Path(__file__).resolve().parent / "results_plateau_smoke" / "sigma_conventions.json"


def composition_sv_in_basis(model: LinearJEPA, U: np.ndarray) -> np.ndarray:
    """Diagonal of |U^T W̄ U|, treating off-diagonal as zero (good if balanced init holds)."""
    with torch.no_grad():
        W = model.composition().cpu().numpy()
    return np.abs(np.diag(U.T @ W @ U))


def layer_sv_in_basis(model: LinearJEPA, U: np.ndarray) -> np.ndarray:
    """Geometric-mean per-layer singular value along eigenbasis directions."""
    with torch.no_grad():
        layer_diags = []
        for W in model.weights:
            Wn = W.detach().cpu().numpy()
            layer_diags.append(np.diag(U.T @ Wn @ U))
        layer_diags = np.stack(layer_diags, axis=0)   # (L, d)
    return np.abs(layer_diags).prod(axis=0) ** (1.0 / layer_diags.shape[0])


def run_probe(d: int = 10, depth: int = 2, eps: float = 1e-2,
              steps: int = 30000, lr: float = 0.05) -> dict:
    rng = np.random.default_rng(2026)
    setup = SyntheticSetup.positive_branch(d, rng)
    n = 4096
    x_np, y_np = setup.sample(n, rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)
    model = LinearJEPA(d, depth, init_scale=eps, rng_seed=0)
    opt = torch.optim.SGD(model.parameters(), lr=lr)

    log_every = max(steps // 80, 1)
    log_steps, log_A, log_B, log_C = [], [], [], []
    log_steps.append(0)
    log_A.append(diagonal_amplitudes(model, setup.U))
    log_B.append(composition_sv_in_basis(model, setup.U))
    log_C.append(layer_sv_in_basis(model, setup.U))

    for step in range(1, steps + 1):
        y_hat = model(x)
        loss = ((y_hat - y) ** 2).mean()
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % log_every == 0 or step == steps:
            log_steps.append(step)
            log_A.append(diagonal_amplitudes(model, setup.U))
            log_B.append(composition_sv_in_basis(model, setup.U))
            log_C.append(layer_sv_in_basis(model, setup.U))

    A = np.stack(log_A)
    B = np.stack(log_B)
    C = np.stack(log_C)
    rho = setup.rho_star

    return {
        "rho_star": rho.tolist(),
        "steps": log_steps,
        "sigma_A_final": A[-1].tolist(),
        "sigma_B_final": B[-1].tolist(),
        "sigma_C_final": C[-1].tolist(),
        "predictions": {
            "A_predicts_plateau":          rho.tolist(),                 # σ_A → ρ_r
            "B_predicts_plateau":          np.abs(rho).tolist(),         # σ_B → |ρ_r|
            "C_predicts_plateau":          (np.abs(rho) ** (1.0/depth)).tolist(),
            "paper_predicts_plateau":      (rho ** depth).tolist(),      # σ → ρ^L
        },
        "depth": depth, "eps": eps, "steps_run": steps, "lr": lr,
    }


def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    result = run_probe()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w") as f:
        json.dump(result, f, indent=2)

    rho = np.array(result["rho_star"])
    L = result["depth"]
    def fmt(arr):
        return "  ".join(f"{x:+.3f}" for x in arr)
    logger.info("rho_star         : %s", fmt(rho))
    logger.info("σ_A (W̄ diagonal)    : %s", fmt(result["sigma_A_final"]))
    logger.info("σ_B (W̄ |diag|)      : %s", fmt(result["sigma_B_final"]))
    logger.info("σ_C (layer geomean): %s", fmt(result["sigma_C_final"]))
    logger.info("Paper prediction ρ^L: %s", fmt(rho ** L))

    sa = np.array(result["sigma_A_final"])
    err_A_paper   = np.max(np.abs(sa - rho ** L))
    err_A_native  = np.max(np.abs(sa - rho))
    logger.info("‖σ_A - ρ^L‖∞ = %.4f   ‖σ_A - ρ‖∞ = %.4f", err_A_paper, err_A_native)


if __name__ == "__main__":
    main()
