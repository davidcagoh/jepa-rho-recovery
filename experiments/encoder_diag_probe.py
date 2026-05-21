"""Test whether σ_r := u^T Wbar v (ENCODER ONLY) plateaus at ρ^L.

Paper-1 Lean (jepa-learning-order/JepaLearningOrder/JEPA.lean:858) states the
ODE for `diagAmplitude := u^T Wbar v`, where `Wbar` is the encoder matrix in
a JEPA model with separate predictor V. The hitting-time target in the same
file (`p * rho_r ^ L`) confirms σ_r^∞ = ρ_r^L.

Session-90 smoke test measured `u^T (V·Wbar) v` (full composition) and saw
plateau ρ_r, not ρ_r^L. This script disambiguates by measuring just the
encoder diagonal.

Setup: simulate the paper-1 model exactly — separate Wbar (encoder, one
linear layer) and V (predictor, one linear layer), gradient flow on the
JEPA loss with separate optimisers, balanced ε^(1/L) init.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path

import numpy as np
import torch
from torch import nn

from plateau_recover_smoke import SyntheticSetup

logger = logging.getLogger("encoder_diag_probe")
OUT = Path(__file__).resolve().parent / "results_plateau_smoke" / "encoder_diag.json"


class PaperOneJEPA(nn.Module):
    """Encoder Wbar + predictor V, both d×d. Matches `JepaLearningOrder.JEPA.JEPALoss`."""

    def __init__(self, d: int, eps: float, depth: int, seed: int = 0):
        super().__init__()
        torch.manual_seed(seed)
        eps_per_layer = eps ** (1.0 / depth)
        Wbar = torch.empty(d, d); nn.init.orthogonal_(Wbar)
        V = torch.empty(d, d); nn.init.orthogonal_(V)
        self.Wbar = nn.Parameter(eps_per_layer * Wbar)
        self.V = nn.Parameter(eps_per_layer * V)
        self.d = d

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        # y_hat = V Wbar x.
        return x @ self.Wbar.T @ self.V.T


def jepa_loss(model: PaperOneJEPA, x: torch.Tensor, y: torch.Tensor) -> torch.Tensor:
    return ((model(x) - y) ** 2).mean()


def encoder_diag(model: PaperOneJEPA, U: np.ndarray) -> np.ndarray:
    with torch.no_grad():
        W = model.Wbar.detach().cpu().numpy()
    return np.diag(U.T @ W @ U)


def composition_diag(model: PaperOneJEPA, U: np.ndarray) -> np.ndarray:
    with torch.no_grad():
        W = (model.V @ model.Wbar).detach().cpu().numpy()
    return np.diag(U.T @ W @ U)


def predictor_diag(model: PaperOneJEPA, U: np.ndarray) -> np.ndarray:
    with torch.no_grad():
        W = model.V.detach().cpu().numpy()
    return np.diag(U.T @ W @ U)


def run(d: int = 10, depth: int = 2, eps: float = 1e-2,
        steps: int = 60000, lr: float = 0.05, n: int = 4096,
        seed: int = 0) -> dict:
    rng = np.random.default_rng(seed)
    setup = SyntheticSetup.positive_branch(d, rng)
    x_np, y_np = setup.sample(n, rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)
    model = PaperOneJEPA(d, eps, depth, seed)
    opt = torch.optim.SGD(model.parameters(), lr=lr)

    log_every = max(steps // 60, 1)
    log_steps, log_enc, log_comp, log_pred = [], [], [], []

    def snap(s: int):
        log_steps.append(s)
        log_enc.append(encoder_diag(model, setup.U))
        log_comp.append(composition_diag(model, setup.U))
        log_pred.append(predictor_diag(model, setup.U))

    snap(0)
    for step in range(1, steps + 1):
        loss = jepa_loss(model, x, y)
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % log_every == 0 or step == steps:
            snap(step)

    enc = np.stack(log_enc)
    comp = np.stack(log_comp)
    pred = np.stack(log_pred)
    rho = setup.rho_star

    return {
        "rho_star": rho.tolist(),
        "rho_pow_L": (rho ** depth).tolist(),
        "encoder_final": enc[-1].tolist(),
        "composition_final": comp[-1].tolist(),
        "predictor_final": pred[-1].tolist(),
        "encoder_init": enc[0].tolist(),
        "ratios_enc_to_pred_final": (enc[-1] / np.where(np.abs(pred[-1]) > 1e-10, pred[-1], 1e-10)).tolist(),
        "config": dict(d=d, depth=depth, eps=eps, steps=steps, lr=lr, n=n, seed=seed),
    }


def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    result = run()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w") as f:
        json.dump(result, f, indent=2)

    rho = np.array(result["rho_star"])
    L = result["config"]["depth"]
    enc = np.array(result["encoder_final"])
    comp = np.array(result["composition_final"])
    pred = np.array(result["predictor_final"])

    def fmt(a): return "  ".join(f"{x:+.3f}" for x in a)
    logger.info("rho_star            : %s", fmt(rho))
    logger.info("rho^L (paper plateau): %s", fmt(rho ** L))
    logger.info("encoder diag (final): %s", fmt(enc))
    logger.info("predictor diag      : %s", fmt(pred))
    logger.info("composition diag    : %s", fmt(comp))
    logger.info("ratio enc/pred      : %s", fmt(enc / np.where(np.abs(pred)>1e-10, pred, 1e-10)))

    e_paper = np.max(np.abs(enc - rho ** L))
    e_sqrt  = np.max(np.abs(np.abs(enc) - np.sqrt(np.abs(rho))))
    e_rho   = np.max(np.abs(enc - rho))
    c_rho   = np.max(np.abs(comp - rho))
    logger.info("‖enc - ρ^L‖∞    = %.4f", e_paper)
    logger.info("‖|enc| - √|ρ|‖∞ = %.4f", e_sqrt)
    logger.info("‖enc - ρ‖∞      = %.4f", e_rho)
    logger.info("‖comp - ρ‖∞     = %.4f", c_rho)


if __name__ == "__main__":
    main()
