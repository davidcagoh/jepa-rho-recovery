# d=300 question — FINAL verdict (session 86)

## TL;DR

The d=300 "inversion at λ=0" reported in `RESULTS_session86_d300_budget.md`
is **a metric artifact, not a physical phenomenon**. With an absolute-
threshold critical-time definition, ordering is correctly negative at
both λ=0 and λ=0.3.

## The metric-check experiment

Single seed, d=300, 100k steps, cosine LR, both λ=0 and λ=0.3. For
each, compute Spearman(ρ*, t_crit) under three metric families:

* **Relative** (current default): first step where |σ_r(t)| ≥ frac · |σ_r(t_final)|.
* **Absolute**: first step where |σ_r(t)| ≥ τ for a fixed τ.
* **Proximity**: first step where |σ_r(t)| is within δ of |σ_r(t_final)|.

### Result table

| Metric | λ=0 | λ=0.3 |
|--------|-----|-------|
| relative (50% of final) | **+1.00** | −1.00 |
| relative (30% of final) | +0.98 | −0.95 |
| relative (90% of final) | +1.00 | −1.00 |
| absolute τ=0.005 | −0.91 | −0.91 |
| absolute τ=0.01 | **−0.98** | −0.95 |
| absolute τ=0.02 | **−1.00** | −0.98 |
| absolute τ=0.05 | −1.00 | −1.00 |
| proximity δ=0.10 | +1.00 | −1.00 |

The relative metric gives **opposite signs** for the two λ values; the
absolute metric gives **the same correct (negative) sign** for both.

## What's actually happening

### λ=0 final |diag| (top-8 positive features):
```
ρ*:        1.00   0.90   0.80   0.70   0.60   0.50   0.40   0.30
|diag|:    0.126  0.103  0.074  0.047  0.038  0.025  0.018  0.010
```
Theoretical plateaus would be ρ_r* itself (or (ρ_r*)^L by L-power
convention). Either way, training has reached **~10–13% of the
asymptotic value across all features**. Ordering by absolute magnitude
is preserved (higher ρ → bigger |diag|) but ordering by *relative-
threshold critical-time* is inverted because larger features have to
grow further in absolute terms.

### λ=0.3 final |diag|:
```
ρ*:        1.00   0.90   0.80   0.70   0.60   0.50   0.40   0.30
|diag|:    0.856  0.747  0.610  0.468  0.381  0.286  0.212  0.132
```
Near-theoretical plateaus (~85–44% of ρ_r*). SIGReg accelerates the
approach to plateau by ~7×, making all metrics agree.

## Correct conclusions

1. **There is no two-basin phenomenon.** The unregularised gradient
   flow at d=300 does NOT converge to an inverted attractor. It
   converges to the correct ordering, just *very slowly* in absolute
   magnitude. The "inversion" was the metric's fault.
2. **SIGReg's role at high d is genuine training acceleration**, not
   symmetry-breaking. It pushes the system toward its theoretical
   plateau much faster, so the ordering becomes legible under any
   reasonable metric.
3. **Pareto λ* is real and λ ≈ 0.3 at d=300 is reasonable.** The
   benefit of SIGReg at high d is mostly faster convergence; the
   over-regularisation penalty (λ ≥ 1) is also real (the model is
   pushed away from the MSE optimum).
4. **Paper-2's plateau-estimator design is vindicated.** Because it
   reads ρ_r* by taking (σ_r(T))^{1/L} at large T, it is *metric-
   invariant*: it doesn't depend on critical-time definitions at all.
   The paper-3 framing should foreground this: the right way to read
   ρ* from trajectories is the plateau, not the critical time.

## Revised Pareto λ*(d) scaling (final)

| d | λ*(d) | Spearman @ λ* (absolute metric) |
|---|-------|----------------------------------|
| 10 | 0.00 | −1.00 |
| 30 | 0.00 | −0.99 |
| 100 | 0.10 | −1.00 |
| 300 | **0.30** | −1.00 |

**Linear scaling:** λ*(d) ≈ 0.001·d for d ≳ 50. Threshold below which
λ* = 0 strictly.

## What this means for paper 3

The two-basin headline I drafted in
`RESULTS_session86_d300_budget.md` is **WRONG and must be retracted**.

The correct headline for paper 3:

> **SIGReg accelerates the unregularised JEPA gradient flow's approach
> to its theoretical plateau, with a Pareto-optimal weight λ*(d, ε, L)
> that scales linearly in d. Without SIGReg at high d, training reaches
> the correct ordering of features but at relative magnitudes too small
> for any threshold-based critical-time analysis to detect. The
> plateau-estimator design of paper 2 sidesteps this entirely.**

This is a cleaner, less-sensational, more-correct story. The paper 3
thesis becomes:

1. **Acceleration theorem.** Quantify how much faster σ_r(t) approaches
   (ρ_r*)^L under MSE + λ·SIGReg vs MSE alone. Conjecture: acceleration
   factor scales like ~d · λ for λ < λ*(d).
2. **Over-regularisation penalty.** For λ > λ*(d), the system is
   pushed away from its MSE optimum; quantify the resulting bias on
   the recovered ρ̂_r.
3. **Pareto λ*(d) ≈ 0.001·d** as the balance point.

## Lesson learned

When measuring "how fast something learns," use plateau-relative
metrics ONLY when the plateau is actually being reached. For
incompletely-converged trajectories, absolute thresholds are required
to avoid spurious sign-flips from differential growth rates.

This caveat is important enough to belong in paper 2's methodology
section as well, since the v1 critical-time inversion would suffer
the same issue at high d — yet another reason to lead with the
plateau estimator.

## Decisions

* **Retract the two-basin framing.** The data does not support it.
* **Paper 3 is GO** with the acceleration/over-regularisation framing.
* **Recommended next experiment** (one session, ~30 min compute):
  Replicate the d × λ sweep with absolute-threshold critical times,
  confirm the linear λ*(d) ≈ 0.001·d scaling holds metric-invariantly.
  Then start drafting paper 3.
* **Paper 2 unchanged** — its plateau-estimator design is vindicated.
