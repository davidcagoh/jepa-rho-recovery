"""
Metric-sensitivity check for the d=300 inversion finding.

The d300_budget_probe showed that at λ=0, d=300, Spearman(rho*, t_crit) = +1.0
under the relative-threshold critical-time definition (first step where
|sigma_r(t)| >= 0.5 * |sigma_r(t_final)|).

This may be entirely a metric artifact. Test by computing Spearman under
multiple alternative critical-time definitions:

  (a) RELATIVE (50% of final): the current default.
  (b) ABSOLUTE (fixed tau): first step where |sigma_r(t)| >= tau, for
      several tau in [0.005, 0.1].
  (c) PLATEAU-PROXIMITY (delta below plateau): first step where
      ||sigma_r(t)| - |sigma_r(t_final)|| / |sigma_r(t_final)| <= delta.

If absolute-threshold gives the theoretically-expected negative Spearman
while relative-threshold gives positive, the "inversion" is a measurement
artifact, not a physical phenomenon.

Run: ~5 min total.
"""

from __future__ import annotations

import json
import pathlib
import sys
import time

import numpy as np
import torch

sys.path.insert(0, str(pathlib.Path(__file__).parent))
from sigreg_ordering_probe import (
    LinearJEPA,
    SyntheticGenEigenSetup,
    diagonal_amplitudes,
    rank_correlation,
    sigreg_penalty,
)


def train_full_trajectory(d: int, lambd: float, seed: int, *,
                           steps: int, lr_init: float = 0.005,
                           batch: int = 128) -> dict:
    """Train and return the FULL trajectory (one snapshot every 250 steps)."""
    rng = np.random.default_rng(seed)
    rho_pos = min(8, max(3, d // 4))
    rho_neg = min(4, max(2, d // 8))
    setup = SyntheticGenEigenSetup.make(d, rho_pos_count=rho_pos,
                                          rho_neg_count=rho_neg, rng=rng,
                                          unit_mu=True)
    x_np, y_np = setup.sample(max(2 * d * 50, 1000), rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)
    torch.manual_seed(seed)
    model = LinearJEPA(d, depth=2, init_scale=0.01, rng_seed=seed)
    opt = torch.optim.SGD(model.parameters(), lr=lr_init)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=steps,
                                                       eta_min=lr_init * 0.01)
    n = x.shape[0]
    log_every = 250
    steps_logged = []
    diags = []
    for step in range(steps):
        idx = torch.randint(0, n, (batch,))
        xb = x[idx]; yb = y[idx]
        y_hat = model(xb)
        mse = ((y_hat - yb) ** 2).mean()
        if lambd > 0:
            z = model.encode(xb)
            loss = mse + lambd * sigreg_penalty(z, num_projections=32)
        else:
            loss = mse
        opt.zero_grad(); loss.backward(); opt.step(); sched.step()
        if step % log_every == 0 or step == steps - 1:
            steps_logged.append(step)
            diags.append(diagonal_amplitudes(model, setup))
    return dict(setup=setup, steps=np.array(steps_logged),
                diags=np.stack(diags))


def ct_relative(diags: np.ndarray, steps: np.ndarray,
                frac: float = 0.5) -> np.ndarray:
    final = diags[-1]
    d = diags.shape[1]
    out = np.full(d, np.nan)
    threshold = frac * np.abs(final)
    for r in range(d):
        if np.abs(final[r]) < 1e-6:
            continue
        hits = np.where(np.abs(diags[:, r]) >= threshold[r])[0]
        if len(hits) > 0:
            out[r] = steps[hits[0]]
    return out


def ct_absolute(diags: np.ndarray, steps: np.ndarray,
                tau: float) -> np.ndarray:
    d = diags.shape[1]
    out = np.full(d, np.nan)
    for r in range(d):
        hits = np.where(np.abs(diags[:, r]) >= tau)[0]
        if len(hits) > 0:
            out[r] = steps[hits[0]]
    return out


def ct_proximity(diags: np.ndarray, steps: np.ndarray,
                  delta: float = 0.1) -> np.ndarray:
    """First step where the relative *gap from plateau* drops below delta."""
    final = diags[-1]
    d = diags.shape[1]
    out = np.full(d, np.nan)
    for r in range(d):
        if np.abs(final[r]) < 1e-6:
            continue
        rel_gap = np.abs(np.abs(diags[:, r]) - np.abs(final[r])) / np.abs(final[r])
        hits = np.where(rel_gap <= delta)[0]
        if len(hits) > 0:
            out[r] = steps[hits[0]]
    return out


def analyse(label: str, traj: dict) -> dict:
    setup = traj["setup"]
    diags = traj["diags"]
    steps = traj["steps"]
    pos_mask = setup.rho_star > 1e-6
    rho_pos = setup.rho_star[pos_mask]
    print(f"\n=== {label} ===")
    print(f"Positive rho*: {rho_pos}")
    print(f"Final |diag| at pos features: {np.abs(diags[-1][pos_mask])}")
    print()
    print(f"{'Metric':<30} | {'Spearman(rho*, t_crit)':>22}")
    print("-" * 56)

    results = {}

    # Relative critical times
    for frac in [0.3, 0.5, 0.7, 0.9]:
        ct = ct_relative(diags, steps, frac=frac)
        sp = rank_correlation(rho_pos, ct[pos_mask])
        print(f"{'relative ' + str(frac) + ' of final':<30} | {sp:>+22.3f}")
        results[f"relative_{frac}"] = sp

    # Absolute thresholds
    for tau in [0.005, 0.01, 0.02, 0.05, 0.1, 0.2]:
        ct = ct_absolute(diags, steps, tau=tau)
        sp = rank_correlation(rho_pos, ct[pos_mask])
        print(f"{'absolute tau=' + str(tau):<30} | {sp:>+22.3f}")
        results[f"absolute_{tau}"] = sp

    # Proximity to plateau
    for delta in [0.05, 0.1, 0.2]:
        ct = ct_proximity(diags, steps, delta=delta)
        sp = rank_correlation(rho_pos, ct[pos_mask])
        print(f"{'proximity delta=' + str(delta):<30} | {sp:>+22.3f}")
        results[f"proximity_{delta}"] = sp

    return results


def main() -> int:
    cases = [
        ("d=300, λ=0.0, seed=0, 100k steps", dict(d=300, lambd=0.0, seed=0, steps=100_000)),
        ("d=300, λ=0.3, seed=0, 100k steps", dict(d=300, lambd=0.3, seed=0, steps=100_000)),
    ]
    all_results = {}
    t0 = time.time()
    for label, kwargs in cases:
        ts = time.time()
        print(f"\nRunning {label}...")
        traj = train_full_trajectory(**kwargs)
        print(f"  ({time.time() - ts:.0f}s)")
        all_results[label] = analyse(label, traj)
    print(f"\nTotal: {time.time() - t0:.0f}s")

    # Cross-comparison
    print("\n\n=== Metric stability: same data, multiple metrics ===")
    print("(If absolute-tau gives opposite Spearman from relative-frac, the")
    print(" 'inversion' phenomenon is a metric artifact, not a physical one.)\n")
    for label in all_results:
        rels = [v for k, v in all_results[label].items()
                if k.startswith("relative") and not np.isnan(v)]
        abss = [v for k, v in all_results[label].items()
                if k.startswith("absolute") and not np.isnan(v)]
        print(f"  {label}")
        print(f"    relative metrics:  range [{min(rels):+.3f}, {max(rels):+.3f}]")
        print(f"    absolute metrics:  range [{min(abss):+.3f}, {max(abss):+.3f}]")

    out_path = pathlib.Path("experiments/results_d300_metric_check.json")
    with open(out_path, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nWrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
