"""Rate-isolation probe for the corrected plateau estimator.

Existing corrected_sweep.json (n=4096, d=10) shows err_inf roughly flat or
slightly growing as ε → 0 (raw_slope ≈ -0.11), inconsistent with the
theoretical ε^(1/L)|log ε| rate (theory_slope = 1/L = 0.5 for L=2).

Hypothesis: at fixed n, the err_inf is dominated by the O(n^(-1/2)) sample-noise
floor, not the O(ε^(1/L)|log ε|) dynamics-error term. The theoretical rate
should emerge once n is large enough that the dynamics term exceeds the
noise floor.

This probe sweeps ε at multiple n values and reports the per-n slope. A
shrinking err_inf with the correct ε-slope at larger n would confirm the
theory; flat behaviour across all n would falsify it.

Reuses train_one / SyntheticSetup from existing scripts to keep the
recovery pipeline identical to corrected_sweep.json.
"""

from __future__ import annotations

import argparse
import json
import logging
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from plateau_recover_corrected import OUT_DIR, train_one
from plateau_recover_smoke import SyntheticSetup

logger = logging.getLogger("rate_isolation_probe")


@dataclass(frozen=True)
class ProbeConfig:
    d: int
    depth: int
    lr: float
    steps: int
    log_every: int
    seeds: tuple[int, ...]
    ns: tuple[int, ...]
    epsilons: tuple[float, ...]


def run_one_n(cfg: ProbeConfig, n: int) -> dict:
    rows = []
    for eps in cfg.epsilons:
        per_seed = []
        for seed in cfg.seeds:
            setup = SyntheticSetup.positive_branch(
                cfg.d, np.random.default_rng(2000 + seed)
            )
            per_seed.append(
                train_one(
                    setup,
                    eps,
                    depth=cfg.depth,
                    steps=cfg.steps,
                    lr=cfg.lr,
                    n=n,
                    seed=seed,
                    log_every=cfg.log_every,
                )
            )
        err_inf_vals = [s["err_inf"] for s in per_seed]
        rows.append(
            {
                "eps": eps,
                "err_inf_mean": float(np.mean(err_inf_vals)),
                "err_inf_std": float(np.std(err_inf_vals)),
            }
        )

    eps_arr = np.array([r["eps"] for r in rows])
    err_arr = np.array([r["err_inf_mean"] for r in rows])
    log_eps = np.log(eps_arr)
    log_err = np.log(err_arr)
    log_corrected = log_err - np.log(np.abs(log_eps))
    slope_corrected, _ = np.polyfit(log_eps, log_corrected, 1)
    raw_slope, _ = np.polyfit(log_eps, log_err, 1)
    return {
        "n": n,
        "rows": rows,
        "slope_corrected": float(slope_corrected),
        "raw_slope": float(raw_slope),
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--d", type=int, default=10)
    p.add_argument("--depth", type=int, default=2)
    p.add_argument("--lr", type=float, default=0.05)
    p.add_argument("--steps", type=int, default=80000)
    p.add_argument("--log-every", type=int, default=200)
    p.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    p.add_argument(
        "--ns",
        type=int,
        nargs="+",
        default=[4096, 16384, 65536],
        help="Sample sizes to sweep (each ε row repeated per n).",
    )
    p.add_argument(
        "--epsilons",
        type=float,
        nargs="+",
        default=[3e-1, 1e-1, 3e-2, 1e-2, 3e-3, 1e-3],
    )
    p.add_argument(
        "--out", type=str, default=str(OUT_DIR / "rate_isolation.json")
    )
    return p.parse_args()


def main() -> None:
    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s"
    )
    args = parse_args()
    cfg = ProbeConfig(
        d=args.d,
        depth=args.depth,
        lr=args.lr,
        steps=args.steps,
        log_every=args.log_every,
        seeds=tuple(args.seeds),
        ns=tuple(args.ns),
        epsilons=tuple(args.epsilons),
    )

    blocks = []
    for n in cfg.ns:
        logger.info("=== n = %d ===", n)
        block = run_one_n(cfg, n)
        blocks.append(block)
        logger.info(
            "  slope_corrected=%.3f raw_slope=%.3f (theory=%.3f)",
            block["slope_corrected"],
            block["raw_slope"],
            1.0 / cfg.depth,
        )
        for row in block["rows"]:
            logger.info(
                "  eps=%.0e err_inf=%.5f ± %.5f",
                row["eps"],
                row["err_inf_mean"],
                row["err_inf_std"],
            )

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(
            {
                "config": {
                    "d": cfg.d,
                    "depth": cfg.depth,
                    "lr": cfg.lr,
                    "steps": cfg.steps,
                    "log_every": cfg.log_every,
                    "seeds": list(cfg.seeds),
                    "ns": list(cfg.ns),
                    "epsilons": list(cfg.epsilons),
                    "theory_slope": 1.0 / cfg.depth,
                },
                "blocks": blocks,
            },
            f,
            indent=2,
        )


if __name__ == "__main__":
    main()
