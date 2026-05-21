"""Test paper-1 σ_r^∞ = ρ^L claim under the aligned init it actually requires.

Paper-1's `JEPA_dynamics_ordering` (jepa-learning-order/JepaLearningOrder/
MainTheorem.lean:246) takes σ_r(0) = ε and the Bernoulli ODE as *hypotheses*.
These require an initialisation where Wbar is approximately diagonal in the
generalised eigenbasis U with diagonal entries ε:

    Wbar(0) ≈ ε · U U^T = ε · I  (in U basis)

Standard `nn.init.orthogonal_(Wbar)` gives a random orthogonal matrix at
scale ε^(1/L) — its U-basis diagonal is `ε^(1/L) · (U^T Q U)_rr ≈ ε^(1/L)/√d`,
which is *not* ε. That's why session-90's smoke test saw σ_r → ρ rather than ρ^L.

Setup
-----
- Aligned init:   Wbar(0) = ε · I  (so σ_r(0) = ε exactly)
- Aligned init:   V(0)    = ε · I  (matching scale for balanced flow)
- Train both via SGD on JEPA loss tr(½ V Wbar Σ Wbar^T V^T - V Wbar Σ^yx).
- Log diagAmplitude σ_r := u_r^T Wbar v_r at each snapshot.
- Compare final σ_r to ρ_r^L (paper claim) vs ρ_r (composition convention).

Expect under aligned init: σ_r should track the Bernoulli ODE and plateau
near ρ_r^L. If it does, paper-1 is empirically consistent and the paper-2
pseudocode just needs to flag the init requirement.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path

import numpy as np
import torch
from torch import nn

from plateau_recover_smoke import SyntheticSetup

logger = logging.getLogger("aligned_init_probe")
OUT = Path(__file__).resolve().parent / "results_plateau_smoke" / "aligned_init.json"


class AlignedJEPA(nn.Module):
    """Two-matrix JEPA with diagonal-in-U-basis init."""

    def __init__(self, d: int, U: np.ndarray, eps: float, seed: int = 0):
        super().__init__()
        torch.manual_seed(seed)
        # Wbar(0) = ε · I (which is ε · U U^T = ε · I since U orthogonal).
        # V(0)    = ε · I  (same scale, balanced).
        self.Wbar = nn.Parameter(eps * torch.eye(d, dtype=torch.float32))
        self.V    = nn.Parameter(eps * torch.eye(d, dtype=torch.float32))
        self.d = d

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return x @ self.Wbar.T @ self.V.T


def encoder_diag(model: AlignedJEPA, U: np.ndarray) -> np.ndarray:
    with torch.no_grad():
        W = model.Wbar.detach().cpu().numpy()
    return np.diag(U.T @ W @ U)


def composition_diag(model: AlignedJEPA, U: np.ndarray) -> np.ndarray:
    with torch.no_grad():
        W = (model.V @ model.Wbar).detach().cpu().numpy()
    return np.diag(U.T @ W @ U)


def run(d: int = 10, eps: float = 0.05, steps: int = 80000,
        lr: float = 0.05, n: int = 4096, seed: int = 0) -> dict:
    rng = np.random.default_rng(seed)
    setup = SyntheticSetup.positive_branch(d, rng)
    x_np, y_np = setup.sample(n, rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)
    model = AlignedJEPA(d, setup.U, eps, seed)
    opt = torch.optim.SGD(model.parameters(), lr=lr)

    log_every = max(steps // 80, 1)
    log_steps, log_enc, log_comp = [], [], []

    def snap(s):
        log_steps.append(s)
        log_enc.append(encoder_diag(model, setup.U))
        log_comp.append(composition_diag(model, setup.U))

    snap(0)
    for step in range(1, steps + 1):
        loss = ((model(x) - y) ** 2).mean()
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % log_every == 0 or step == steps:
            snap(step)

    enc = np.stack(log_enc)
    comp = np.stack(log_comp)
    rho = setup.rho_star
    L = 2

    return {
        "rho_star": rho.tolist(),
        "rho_pow_L": (rho ** L).tolist(),
        "encoder_init": enc[0].tolist(),
        "encoder_final": enc[-1].tolist(),
        "composition_final": comp[-1].tolist(),
        "config": dict(d=d, eps=eps, steps=steps, lr=lr, n=n, seed=seed, L=L),
        "encoder_traj_first6": [enc[i].tolist() for i in range(min(6, len(enc)))],
        "encoder_traj_last6": [enc[i].tolist() for i in range(max(0, len(enc)-6), len(enc))],
    }


def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    result = run()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w") as f:
        json.dump(result, f, indent=2)

    rho = np.array(result["rho_star"])
    L = result["config"]["L"]
    enc = np.array(result["encoder_final"])
    enc0 = np.array(result["encoder_init"])
    comp = np.array(result["composition_final"])

    def fmt(a): return "  ".join(f"{x:+.4f}" for x in a)
    logger.info("rho_star          : %s", fmt(rho))
    logger.info("rho^L (paper)     : %s", fmt(rho ** L))
    logger.info("encoder σ(0)=ε    : %s   ← should be all ε=%g", fmt(enc0), result["config"]["eps"])
    logger.info("encoder σ(final)  : %s", fmt(enc))
    logger.info("composition final : %s", fmt(comp))
    logger.info("‖encoder - ρ^L‖∞  = %.4f", float(np.max(np.abs(enc - rho ** L))))
    logger.info("‖encoder - √ρ‖∞   = %.4f", float(np.max(np.abs(enc - np.sqrt(np.abs(rho)) * np.sign(rho)))))
    logger.info("‖encoder - ρ‖∞    = %.4f", float(np.max(np.abs(enc - rho))))
    logger.info("‖comp - ρ‖∞       = %.4f", float(np.max(np.abs(comp - rho))))


if __name__ == "__main__":
    main()
