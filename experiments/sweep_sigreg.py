"""
SIGReg ordering sweep — d × lambda × seed.

For each (d, lambda, seed), train MSE+lambda*SIGReg and record the Spearman
rank correlation of rho* vs critical-time on positive-rho features.

Goal: find a monotonic Spearman-vs-lambda relationship that would be the
paper-3 conjecture ("SIGReg compresses rho* ordering by a characterisable
function of lambda").

Run
---
    python sweep_sigreg.py [--seeds 3] [--quick]

`--quick` halves step counts and uses 2 seeds (fast triage; ~5 min).
Default (3 seeds, full steps): ~30 min on CPU.
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
    rank_correlation,
    train_and_log,
)


def run_one(d: int, lambd: float, seed: int, *, steps: int, lr: float,
            eps: float, batch: int) -> dict:
    """Run a single (d, lambda, seed) cell. Returns Spearman + per-feature
    critical times."""
    rng = np.random.default_rng(seed)
    # Spectrum sizing: hold absolute counts fixed across d so the
    # number-of-features-to-learn doesn't scale with d. This isolates the
    # SIGReg pressure from the "more features to learn at higher d" confound.
    rho_pos = min(8, max(3, d // 4))
    rho_neg = min(4, max(2, d // 8))
    setup = SyntheticGenEigenSetup.make(d, rho_pos_count=rho_pos,
                                          rho_neg_count=rho_neg, rng=rng,
                                          unit_mu=True)
    x_np, y_np = setup.sample(max(2 * d * 50, 1000), rng)
    x = torch.tensor(x_np, dtype=torch.float32)
    y = torch.tensor(y_np, dtype=torch.float32)

    torch.manual_seed(seed)
    model = LinearJEPA(d, depth=2, init_scale=eps, rng_seed=seed)
    out = train_and_log(model, setup, x, y,
                        steps=steps, lr=lr, batch=batch,
                        sigreg_weight=lambd,
                        log_every=max(steps // 200, 25))
    ct = critical_times(out["trajectories"])
    pos_mask = setup.rho_star > 1e-6
    rho_pos_vals = setup.rho_star[pos_mask]
    ct_pos = ct[pos_mask]
    spearman = rank_correlation(rho_pos_vals, ct_pos)
    return dict(
        d=d, lambd=lambd, seed=seed,
        spearman=spearman,
        final_mse=out["losses"][-1],
        final_sigreg=out["sigreg_losses"][-1] if lambd > 0 else 0.0,
        ct_pos=ct_pos.tolist(),
        rho_pos=rho_pos_vals.tolist(),
        num_pos_features=int(pos_mask.sum()),
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--quick", action="store_true",
                    help="Halve step counts for fast triage.")
    ap.add_argument("--out", type=str,
                    default="experiments/results_sigreg_sweep.json")
    args = ap.parse_args()

    d_values = [10, 30, 100, 300]
    lambda_values = [0.0, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0]   # finer λ grid + λ=0 baseline
    # Step counts scaled with d: larger d needs more steps to reach plateau.
    steps_by_d = {10: 8000, 30: 12000, 100: 20000, 300: 30000}
    if args.quick:
        steps_by_d = {k: v // 2 for k, v in steps_by_d.items()}
        seeds = list(range(2))
    else:
        seeds = list(range(args.seeds))

    print(f"Sweep: d × lambda × seed = "
          f"{len(d_values)} × {len(lambda_values)} × {len(seeds)} "
          f"= {len(d_values) * len(lambda_values) * len(seeds)} cells")
    print(f"Steps by d: {steps_by_d}")
    print()

    results = []
    t0 = time.time()
    cell_idx = 0
    total_cells = len(d_values) * len(lambda_values) * len(seeds)
    for d in d_values:
        for lambd in lambda_values:
            for seed in seeds:
                cell_idx += 1
                ts = time.time()
                r = run_one(d, lambd, seed,
                            steps=steps_by_d[d],
                            lr=(0.02 if d <= 30 else 0.01 if d <= 100 else 0.005),
                            eps=0.01,
                            batch=128)
                results.append(r)
                dt = time.time() - ts
                elapsed = time.time() - t0
                print(f"  [{cell_idx:>2}/{total_cells}] "
                      f"d={d:>3} λ={lambd:>4.2f} seed={seed} | "
                      f"spearman={r['spearman']:+.3f} | "
                      f"mse={r['final_mse']:.4f} | "
                      f"sigreg={r['final_sigreg']:.4f} | "
                      f"{dt:>5.1f}s (elapsed {elapsed:>5.0f}s)")

    print(f"\nTotal time: {time.time() - t0:.0f}s")

    # Aggregate.
    print("\n=== Mean Spearman by (d, λ) ===\n")
    header = f"{'d':>4} |" + "".join(f" λ={l:<5}" for l in lambda_values)
    print(header)
    print("-" * len(header))
    for d in d_values:
        row = f"{d:>4} |"
        for lambd in lambda_values:
            cells = [r["spearman"] for r in results
                     if r["d"] == d and r["lambd"] == lambd
                     and not np.isnan(r["spearman"])]
            if cells:
                row += f" {np.mean(cells):>+5.2f} "
            else:
                row += "   --   "
        print(row)

    # Monotonicity diagnostic.
    print("\n=== Spearman trend in λ (per d) ===\n")
    for d in d_values:
        means = []
        for lambd in lambda_values:
            cells = [r["spearman"] for r in results
                     if r["d"] == d and r["lambd"] == lambd
                     and not np.isnan(r["spearman"])]
            means.append(np.mean(cells) if cells else float("nan"))
        # Trend: does Spearman get LESS negative as λ grows?
        diffs = np.diff(means)
        print(f"  d={d:>3}: means = {[f'{m:+.2f}' for m in means]}, "
              f"Δ = {[f'{d:+.2f}' for d in diffs]}")
        non_nan_diffs = diffs[~np.isnan(diffs)]
        if len(non_nan_diffs) > 0 and np.all(non_nan_diffs >= -0.05):
            print(f"      monotonic-non-decreasing (ordering progressively destroyed)")
        elif len(non_nan_diffs) > 0 and np.all(non_nan_diffs <= 0.05):
            print(f"      monotonic-non-increasing (ordering enhanced — unexpected)")
        else:
            print(f"      non-monotonic")

    # Pareto λ*(d): the λ minimising mean Spearman (most-negative).
    print("\n=== Pareto λ*(d) ===\n")
    print(f"{'d':>4} | {'argmin_λ Spearman':>20} | {'min Spearman':>14} | {'final MSE @ λ*':>16}")
    print("-" * 70)
    pareto = {}
    for d in d_values:
        means = []
        mses = []
        for lambd in lambda_values:
            cells = [r["spearman"] for r in results
                     if r["d"] == d and r["lambd"] == lambd
                     and not np.isnan(r["spearman"])]
            mse_cells = [r["final_mse"] for r in results
                         if r["d"] == d and r["lambd"] == lambd]
            means.append(np.mean(cells) if cells else float("nan"))
            mses.append(np.mean(mse_cells) if mse_cells else float("nan"))
        means_arr = np.array(means)
        if np.all(np.isnan(means_arr)):
            continue
        idx = int(np.nanargmin(means_arr))
        pareto[d] = (lambda_values[idx], means_arr[idx], mses[idx])
        print(f"{d:>4} | {lambda_values[idx]:>20.3f} | "
              f"{means_arr[idx]:>+14.3f} | {mses[idx]:>16.4f}")

    if len(pareto) >= 2:
        print("\nλ*(d) scaling — log-log fit:")
        dd = np.log(np.array(list(pareto.keys()), dtype=float))
        # Replace λ*=0 with the smallest non-zero λ (0.01) to keep log finite.
        ll = np.log(np.array([max(p[0], 0.005) for p in pareto.values()]))
        if len(dd) >= 2:
            slope, intercept = np.polyfit(dd, ll, 1)
            print(f"   log(λ*) ≈ {slope:+.3f} * log(d) + {intercept:+.3f}")
            print(f"   ⇒ λ*(d) ≈ {np.exp(intercept):.4f} * d^{slope:+.3f}")

    out_path = pathlib.Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump({"results": results,
                   "d_values": d_values,
                   "lambda_values": lambda_values,
                   "seeds": seeds,
                   "steps_by_d": steps_by_d}, f, indent=2)
    print(f"\nWrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
