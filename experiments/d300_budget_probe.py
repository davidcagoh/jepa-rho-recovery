"""
d=300 training-budget vs info-floor probe.

The refined sweep (results_sweep_refined.json) showed that at d=300:
  * λ=0 (no SIGReg) gives Spearman +0.94 (inverted!) after 30k steps.
  * λ=1.0 (Pareto) gives Spearman -0.10 after 30k steps.

Open question: is the d=300 Pareto Spearman = -0.10 due to
  (A) TRAINING-BUDGET artifact — we just need more steps, and given
      enough time training converges to ordered spectrum, OR
  (B) FUNDAMENTAL INFO-FLOOR — even optimal SIGReg cannot recover the
      spectrum at d=300, and Spearman plateaus at ~-0.1?

Method
------
Train for 100k steps with cosine LR decay (helps escape saddle/oscillation
that constant LR can get stuck on). Log Spearman at multiple checkpoints
(every 10k steps). Also log per-feature σ_r(t) curves for diagnostic
plotting. Compare:

  * λ = 0.0  (baseline — does long training fix the +0.94 inversion?)
  * λ = 0.3  (intermediate, between Pareto and uncovered region)
  * λ = 1.0  (Pareto from refined sweep)
  * λ = 3.0  (over-regularised; sanity check)

Three seeds each = 12 runs × ~3-5 min each ≈ 40 min total.

If Spearman is still improving at 100k for any λ, the budget hypothesis
(A) is supported. If Spearman has plateaued, the info-floor (B) is.
"""

from __future__ import annotations

import argparse
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
    critical_times,
    diagonal_amplitudes,
    rank_correlation,
    sigreg_penalty,
)


def train_with_checkpoints(
    model: LinearJEPA,
    setup: SyntheticGenEigenSetup,
    x: torch.Tensor, y: torch.Tensor,
    *,
    steps: int, lr_init: float, batch: int,
    sigreg_weight: float,
    checkpoint_every: int,
) -> dict:
    """Train with cosine LR decay; checkpoint every `checkpoint_every` steps.

    Logs full diagonal-amplitude trajectory (one entry per `log_every` step)
    and a Spearman snapshot at each checkpoint."""
    opt = torch.optim.SGD(model.parameters(), lr=lr_init)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=steps,
                                                            eta_min=lr_init * 0.01)
    n = x.shape[0]
    log_every = max(steps // 400, 50)
    trajectories = []
    losses = []
    checkpoints = []     # list of (step, spearman_pos, mse)
    pos_mask = setup.rho_star > 1e-6
    rho_pos_vals = setup.rho_star[pos_mask]

    for step in range(steps):
        idx = torch.randint(0, n, (batch,))
        xb = x[idx]; yb = y[idx]
        y_hat = model(xb)
        mse = ((y_hat - yb) ** 2).mean()
        if sigreg_weight > 0:
            z = model.encode(xb)
            loss = mse + sigreg_weight * sigreg_penalty(z, num_projections=32)
        else:
            loss = mse
        opt.zero_grad()
        loss.backward()
        opt.step()
        scheduler.step()

        if step % log_every == 0 or step == steps - 1:
            losses.append(float(mse.item()))
            trajectories.append((step, diagonal_amplitudes(model, setup)))

        if step % checkpoint_every == 0 or step == steps - 1:
            ct = critical_times(trajectories)
            ct_pos = ct[pos_mask]
            sp = rank_correlation(rho_pos_vals, ct_pos)
            checkpoints.append(dict(step=step, spearman=sp, mse=float(mse.item())))

    return dict(trajectories=trajectories, losses=losses,
                checkpoints=checkpoints)


def run_cell(d: int, lambd: float, seed: int, *, steps: int) -> dict:
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

    out = train_with_checkpoints(model, setup, x, y,
                                  steps=steps, lr_init=0.005, batch=128,
                                  sigreg_weight=lambd,
                                  checkpoint_every=steps // 10)
    pos_mask = setup.rho_star > 1e-6
    ct_final = critical_times(out["trajectories"])
    return dict(
        d=d, lambd=lambd, seed=seed, steps=steps,
        checkpoints=out["checkpoints"],
        final_spearman=out["checkpoints"][-1]["spearman"],
        final_mse=out["checkpoints"][-1]["mse"],
        ct_final_pos=ct_final[pos_mask].tolist(),
        rho_star_pos=setup.rho_star[pos_mask].tolist(),
        rho_star_full=setup.rho_star.tolist(),
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=100_000)
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--out", type=str, default="experiments/results_d300_budget.json")
    args = ap.parse_args()

    d = 300
    lambdas = [0.0, 0.3, 1.0, 3.0]
    seeds = list(range(args.seeds))
    print(f"d={d}, steps={args.steps}, lambdas={lambdas}, seeds={seeds}")
    print(f"{len(lambdas) * len(seeds)} runs total\n")

    results = []
    t0 = time.time()
    for lambd in lambdas:
        for seed in seeds:
            ts = time.time()
            print(f"--- λ={lambd:.2f}, seed={seed} ---")
            r = run_cell(d, lambd, seed, steps=args.steps)
            dt = time.time() - ts
            results.append(r)
            print(f"  final Spearman = {r['final_spearman']:+.3f}  "
                  f"final MSE = {r['final_mse']:.4f}  "
                  f"({dt:.0f}s, total {time.time() - t0:.0f}s)")
            print(f"  Spearman trajectory:")
            for cp in r["checkpoints"]:
                print(f"    step={cp['step']:>7}  sp={cp['spearman']:+.3f}  mse={cp['mse']:.4f}")
            print()

    # Aggregate per λ.
    print(f"\n=== Final Spearman by λ (mean ± std across {args.seeds} seeds) ===\n")
    for lambd in lambdas:
        cells = [r["final_spearman"] for r in results if r["lambd"] == lambd
                 and not np.isnan(r["final_spearman"])]
        mses = [r["final_mse"] for r in results if r["lambd"] == lambd]
        if cells:
            print(f"  λ={lambd:.2f}: Spearman = {np.mean(cells):+.3f} ± {np.std(cells):.3f}  "
                  f"MSE = {np.mean(mses):.4f}")

    # Did Spearman plateau? Compare last checkpoint to one before it.
    print(f"\n=== Spearman trend in last 30% of training ===\n")
    print(f"(If still improving toward -1, training-budget artifact.)")
    print(f"(If plateaued, info-floor.)")
    for r in results:
        cps = r["checkpoints"]
        if len(cps) >= 3:
            late_changes = [cps[i+1]["spearman"] - cps[i]["spearman"]
                            for i in range(len(cps) // 2, len(cps) - 1)
                            if not (np.isnan(cps[i]["spearman"]) or np.isnan(cps[i+1]["spearman"]))]
            if late_changes:
                avg_delta = np.mean(late_changes)
                print(f"  λ={r['lambd']:.2f} seed={r['seed']}: "
                      f"avg ΔSpearman per checkpoint in last 50% = {avg_delta:+.3f}")

    out_path = pathlib.Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    # Strip ndarrays for JSON.
    for r in results:
        for cp in r["checkpoints"]:
            if isinstance(cp["spearman"], float) and np.isnan(cp["spearman"]):
                cp["spearman"] = None
    with open(out_path, "w") as f:
        json.dump({"d": d, "lambdas": lambdas, "seeds": seeds,
                   "steps": args.steps, "results": results}, f, indent=2,
                  default=lambda x: None if isinstance(x, float) and np.isnan(x) else x)
    print(f"\nWrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
