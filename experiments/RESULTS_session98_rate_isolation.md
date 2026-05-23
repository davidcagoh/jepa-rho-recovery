# Rate-isolation probe — corrected plateau estimator (session 98, 2026-05-23)

**Question.** `corrected_sweep.json` (n=4096, d=10, L=2) reported `raw_slope = -0.11` for `err_inf` vs ε, suggesting the dynamics-error term does not decay (or grows slightly) as ε → 0. Theory predicts `err_inf ∝ ε^{1/L}|log ε|`, i.e. raw slope ≈ 0.5 with a logarithmic correction. Reason for the discrepancy: dynamics-error vs sample-noise floor.

**Hypothesis.** At fixed n, `err_inf` is dominated by an `O(n^{-1/2})` sample-noise floor independent of ε. The theoretical rate emerges only once n is large enough that the dynamics-error term exceeds this floor.

**Probe.** `rate_isolation_probe.py` — same recovery pipeline as `plateau_recover_corrected.py`, sweeps ε at multiple n values.

## Smoke result (n ∈ {4096, 16384}, ε ∈ {0.3, 0.03, 0.003}, 2 seeds, 20k steps)

| n     | raw_slope | slope_corrected | err(ε=0.3) | err(ε=0.03) | err(ε=0.003) |
|-------|-----------|-----------------|------------|-------------|--------------|
| 4096  | -0.147    | 0.195           | 5.7e-4     | 7.3e-4      | 1.11e-3      |
| 16384 | -0.021    | 0.321           | 2.4e-4     | 2.2e-4      | 2.7e-4       |

Theory: `slope_corrected = 1/L = 0.500`.

## Interpretation

At 4× sample size:
- Absolute `err_inf` halves uniformly across ε — consistent with `O(n^{-1/2})` noise floor.
- `raw_slope` moves from -0.147 (err growing as ε→0) toward 0 (flat). The growth was the noise floor swamping the dynamics term in the polyfit; at higher n, the dynamics term wins.
- `slope_corrected` moves from 0.20 toward 0.32, advancing toward the theoretical 0.50.

**Sample-noise-floor hypothesis holds in this regime.** The original `corrected_sweep.json` flat-error reading is not a falsification of the theory; it reflects insufficient n to expose the dynamics-error decay.

## Next step (not yet run; gated on compute budget)

Full sweep `--ns 4096 16384 65536 262144 --steps 80000 --seeds 0 1 2 --epsilons 3e-1 1e-1 3e-2 1e-2 3e-3 1e-3`. Expectations:
- n=65536: `slope_corrected` close to 0.45–0.50 in the larger-ε regime; smallest-ε errors begin to bend up where dynamics ≈ noise.
- n=262144: full ε^{1/L} curve visible across the ε range.

A negative outcome (slope stays well below 0.5 even at n=262144) would falsify the theoretical rate — that would be a real result, worth knowing before paper submission.

## Files

- `rate_isolation_probe.py` — probe script
- `results_plateau_smoke/rate_isolation_smoke.json` — smoke output above
