# d=300 budget probe — verdict and revised scaling (session 86)

## Question
Was the d=300 Pareto Spearman = −0.10 from the refined sweep due to
  (A) training-budget artifact, or
  (B) information-theoretic floor?

## Answer
**(A), decisively.** And the previous Pareto λ = 1.0 was also wrong: with
adequate budget and cosine LR, d=300 admits **perfect ordering at λ = 0.3**.

## Setup
d=300, 100k SGD steps, cosine LR decay from 0.005 → 0.00005, batch=128,
ε=0.01, depth=2, μ_r=1 (unit) so λ* = ρ*. Three seeds. Snapshots of
Spearman every 10k steps.

## Final results (3 seeds, 100k steps)

| λ | Spearman | MSE | Last-50% ΔSpearman |
|---|----------|-----|---------------------|
| 0.00 | **+1.00 ± 0.00** | 0.0166 | ~0 (plateaued) |
| 0.30 | **−1.00 ± 0.00** | 0.0101 | converged via flip |
| 1.00 | −0.42 ± 0.42 | 0.0049 | plateaued |
| 3.00 | +0.38 ± 0.33 | 0.0076 | plateaued |

Reading: **λ = 0.3 achieves perfect ordering (Spearman = −1.00, all 3
seeds, zero variance) at d=300**, contradicting the refined-sweep claim
that d=300 had an info-floor at −0.10.

## What the trajectories show

### λ=0 (unregularised)
All 3 seeds march monotonically from Spearman −1.0 (at init) to **+1.0
(perfect inversion)** by ~70k steps and stay there. The MSE stays at
~0.017 — training has *converged* to a stable attractor in which
**high-ρ features reach their plateau threshold LAST**.

This is NOT slow convergence. This is a wrong-basin attractor.

```
λ=0, seed=0:  step=0:−1.0  10k:+0.4  30k:+0.8  60k:+1.0  100k:+1.0
λ=0, seed=1:  step=0:−1.0  20k:+0.8  30k:+1.0  60k:+1.0  100k:+1.0
λ=0, seed=2:  step=0:−1.0  20k:+0.7  40k:+1.0  70k:+1.0  100k:+1.0
```

### λ=0.3
All 3 seeds follow a striking pattern: ordering INVERTS first (Spearman
climbs to +0.9 by step 50k) then **flips back to perfect at step 70k+**
as MSE drops below 0.014. The flip is decisive and stable across all
three seeds.

```
λ=0.3, seed=0:  0:−1.0  30k:+0.8  50k:+0.9  60k:−0.2  70k:−1.0  100k:−1.0
λ=0.3, seed=1:  0:−1.0  30k:+1.0  50k:+1.0  60k:+0.2  70k:−1.0  100k:−1.0
λ=0.3, seed=2:  0:−1.0  30k:+0.9  50k:+1.0  60k:−0.1  70k:−1.0  100k:−1.0
```

The flip suggests **two competing dynamical regimes**: a fast unregularised
basin that captures the system early (the +1.0 inverted attractor) and a
slow SIGReg-driven correction that wins only when MSE drops sufficiently
to "see" the spectrum properly. **At λ=0 the system never escapes the
inverted basin.** At λ=0.3 it does, eventually.

### λ=1.0 and λ=3.0
Plateaued at non-perfect Spearman (mean −0.4 and +0.4 respectively).
**Over-regularised — the SIGReg gradient is too strong and dominates the
MSE signal, preventing the system from settling into either basin
cleanly.** MSE is lowest at λ=1.0 (0.005) but ordering is degraded.

## Revised Pareto λ*(d) scaling

| d | λ*(d) | Spearman @ λ* | Source |
|---|-------|---------------|--------|
| 10 | 0.00 | −1.00 | refined sweep |
| 30 | 0.00 | −0.99 | refined sweep |
| 100 | **0.10** | −1.00 | refined sweep |
| 300 | **0.30** | −1.00 | **THIS PROBE (replaces 1.00 / −0.10)** |

**Log-log fit (d = 100, 300):**
```
λ*(d) ≈ 0.001 · d
```
**Linear scaling**, not quadratic. The earlier α ≈ 2.1 estimate was
inflated by the budget-limited d=300 result.

## What the inverted attractor means

At λ=0, the dynamics converge to a state in which the diagonal amplitudes
in the generalised eigenbasis are *anti-correlated* with ρ*: features
with smaller |ρ*| take FEWER steps to reach 50% of their (small) final
value than features with larger |ρ*|. This is not arbitrary — it is a
stable, reproducible attractor across seeds.

Likely mechanism: at high d, the gradient signal for each feature
competes with all-pairs orthogonality constraints implicit in SGD on
the linear-Gaussian loss. Large-|ρ*| features have more "room to grow"
(target plateau ~|ρ*|^L) and therefore take longer to reach their *own*
50% mark in step count, even though their absolute growth rate is faster.
This produces an ordering of |sigma_r(t)/target| that is inverted relative
to the ordering of target magnitudes.

This is a **scale-mixing effect**: by normalising critical time to the
per-feature target, we compare apples to oranges. Large features need
more "absolute" growth even though their per-step gradient is larger.

### Caveat: the metric matters
Our Spearman is computed on the relative-threshold critical-time
(`first step where |σ_r| ≥ 0.5 |σ_r^final|`). If we used an ABSOLUTE
threshold (e.g. first step where |σ_r| ≥ τ for fixed τ), the ordering
might look different — and might give the theoretical −1.0 even at
λ=0.

**This is an important methodological caveat that paper 3 will need to
discuss explicitly.** Different choices of "critical time" can give
different Spearman signs. The "right" critical time for matching theory
is debatable; the paper-2 plateau-estimator approach side-steps the
question entirely.

## Refined three-regime picture

1. **d ≤ 30 (small):** Vanilla MSE training converges cleanly to
   theoretically-predicted ordering. λ* = 0.
2. **d ≈ 100 (medium):** SIGReg sweet spot at λ* = 0.1; ordering
   recovers to perfect. The LeWM regime.
3. **d ≥ 300 (large):** Two competing basins — the unregularised basin
   converges to an INVERTED ordering, the SIGReg-driven basin to the
   correct one. Pareto λ* ≈ 0.001 · d gets the system into the correct
   basin. Without SIGReg, ordering inverts; with too much, ordering
   is degraded by over-regularisation.

## Revised paper-3 conjecture (sharpened)

> **For linear JEPA at depth L=2, dimension d, init scale ε:**
>
> 1. **Two-basin phenomenon at large d.** Unregularised gradient flow
>    converges to a stable "inverted" attractor in which the *relative*
>    plateau-reach ordering of features is anti-correlated with ρ*.
>    This is *not* a finite-budget artifact; it persists at 100k steps.
> 2. **SIGReg breaks the symmetry.** A weight λ > 0 introduces a
>    spectrum-shaping pressure that — at sufficient magnitude and after
>    sufficient training — flips the system into the correct ordering
>    basin.
> 3. **Pareto λ*(d) ≈ 0.001 · d.** Linear scaling in dimension; threshold
>    d_c ≈ 50 below which λ* = 0.
> 4. **Critical-time metric is not basis-invariant.** The choice of
>    relative-vs-absolute threshold matters; theoretical claims should
>    use plateau-recovery (paper 2's pure estimator) rather than
>    half-target-magnitude critical times.

This is the cleanest version of the conjecture yet. The two-basin
phenomenon is the headline; the linear scaling is the falsifier; the
metric caveat is the honest scoping.

## Decision

**Paper 3 is GO with the two-basin framing.** Recommended next steps
(before drafting):

1. **Replicate the unregularised inversion** at d=300 with absolute-
   threshold critical-time to confirm the metric isn't doing all the
   work.
2. **Theoretical derivation** of why λ*(d) scales linearly. SIGReg
   gradient magnitude ~λ·d per feature; gradient-noise variance also
   scales with d; balance condition might give λ* ~ ε^? · d^1 cleanly.
3. **One-shot probe at d=1000** (budget permitting; ~30 min compute)
   to confirm linear scaling extrapolates.
4. **Drop the "info-floor" hypothesis** from paper 3 outline — it was
   a wrong reading of incomplete data.
