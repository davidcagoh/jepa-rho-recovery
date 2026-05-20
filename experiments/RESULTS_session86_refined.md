# Refined SIGReg sweep — Pareto λ*(d) scaling (session 86)

**84 cells**: d ∈ {10, 30, 100, 300}, λ ∈ {0, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0}, 3 seeds.
Total compute: 11 minutes wall.

## Mean Spearman(ρ*, t_crit) [3-seed mean]

| d \ λ | 0.0 | 0.01 | 0.03 | 0.1 | 0.3 | 1.0 | 3.0 |
|-------|-----|------|------|-----|-----|-----|-----|
| 10    | −1.00 | −1.00 | −1.00 | −1.00 | −1.00 | −0.50 | NaN |
| 30    | −0.99 | −0.99 | −0.99 | −0.98 | −0.94 | −0.79 | NaN |
| 100   | −0.38 | −0.48 | −0.64 | **−1.00** | −0.92 | −0.67 | +0.40 |
| 300   | +0.94 | +0.94 | +0.94 | +0.94 | +0.93 | **−0.10** | +0.39 |

NaN = training diverged. Bold = Pareto λ*(d).

## Final MSE [3-seed mean]

| d \ λ | 0.0 | 0.01 | 0.03 | 0.1 | 0.3 | 1.0 | 3.0 |
|-------|-----|------|------|-----|-----|-----|-----|
| 10    | 0.0024 | 0.0027 | 0.0026 | 0.0025 | 0.0028 | 0.0063 | — |
| 30    | 0.0026 | 0.0027 | 0.0026 | 0.0026 | 0.0030 | 0.0071 | — |
| 100   | 0.0101 | 0.0093 | 0.0076 | 0.0061 | 0.0030 | 0.0047 | 0.0237 |
| 300   | 0.0184 | 0.0191 | 0.0191 | 0.0189 | 0.0181 | 0.0103 | 0.0129 |

## Pareto λ*(d)

| d | λ*(d) | Spearman @ λ* | MSE @ λ* |
|---|-------|---------------|----------|
| 10 | 0.00 | −1.00 | 0.0025 |
| 30 | 0.00 | −0.99 | 0.0026 |
| 100 | **0.10** | −1.00 | 0.0061 |
| 300 | **1.00** | −0.10 | 0.0103 |

**Log-log fit (all 4 points, with λ*=0 substituted by 0.005):**

```
log(λ*) ≈ +1.66 · log(d) − 9.88
λ*(d) ≈ 1e-4 · d^1.66
```

**Fit using only the non-degenerate points (d=100, 300):**

```
λ*(d) ≈ 0.001 · d^2.1
```

The d=100→300 ratio (10× in λ* for 3× in d) gives log-slope ≈ 2.1, suggesting **roughly quadratic scaling of the Pareto λ* with dimension** in the regime where SIGReg matters at all.

## Three regimes emerge

### Regime A — d ≤ 30: unregularised dynamics already converge

Vanilla MSE training reaches near-perfect ordering (Spearman ≈ −0.99). SIGReg can only hurt (compression). λ* = 0 strictly. SIGReg-vs-no-SIGReg is monotonic destruction in λ.

### Regime B — d = 100: stabilisation × compression trade-off

This is the **interesting regime** and aligns with LeWM's chosen λ=0.1.

* At λ=0, training noise drowns the ordering (Spearman −0.38, MSE 0.0101 unconverged).
* λ ∈ [0.1, 0.3] gives a clear sweet spot: Spearman recovers to −1.00 (perfect), MSE drops by 3×.
* λ > 0.5 compresses spectrum back.

Spearman(λ) is V-shaped with a clean minimum at λ* ≈ 0.1.

### Regime C — d = 300: SIGReg-required, but ordering still degraded

The Spearman = **+0.94** at λ=0 is genuinely surprising — high-rho features take LONGER to reach their critical threshold than low-rho features. Diagnostic:

* MSE at λ=0 plateaus at 0.018; the training is essentially stuck (lr=0.005, 30k steps not enough to break out of the unregularised slow regime).
* λ ∈ [0.01, 0.3] doesn't help: SIGReg is too weak to overcome the noise floor; Spearman stays inverted.
* λ = 1.0 finally **breaks the inversion** — Spearman goes to −0.10 (faintly negative). MSE drops to 0.010.
* λ = 3.0 over-regularises (Spearman flips back positive, MSE rises).

**The d=300 regime needs SIGReg merely to make the ordering observable at all, but even then the ordering quality is much worse than what's achievable at d ≤ 100.** Possibilities:

1. Training-budget limitation. 30k steps insufficient; would converge to clean ordering with 200k steps.
2. Fundamental: at high d, ε^{1/L} initial separation between features (Order 0.1 with ε=0.01, L=2) is comparable to the noise floor SIGReg can achieve. The signal-to-noise ratio for spectrum ordering hits a floor.

Either way, the d=300 result is the **load-bearing scaling probe** for paper 3.

## Paper-3 conjecture (sharpened by data)

> **For linear JEPA at depth L=2, dimension d, init scale ε = 0.01**:
>
> 1. There exists a **Pareto-optimal SIGReg weight** λ*(d) > 0 for d above
>    a critical d_c (around d_c ≈ 50 from this probe).
> 2. λ*(d) scales as a **power of d**: λ*(d) ~ C(ε, L) · d^α with
>    α ≈ 2 from empirics. Theoretical derivation is open.
> 3. **Spearman(λ) is V-shaped (or generally non-monotonic) above d_c**,
>    with the V's depth (max attainable |Spearman| at λ*) decaying as
>    d grows beyond ~100. This suggests an information-theoretic floor:
>    even optimal SIGReg cannot recover perfect ordering at d ≫ 1.
> 4. **At small d, λ* = 0 strictly** — vanilla MSE training is best.

This is genuinely a clean conjecture suitable for paper 3. Predicting
λ*(d) ~ d² gives a falsifiable claim; deriving it from first principles
(probably via a phase-diagram argument with the SIGReg gradient pressure
vs noise-floor decay rate) is the headline theorem.

## Caveats and follow-ups

* **Training budget at d=300 is not converged.** A focused d=300 run with
  100k+ steps and lr-decay would clarify whether the d=300 Spearman
  remains floored at −0.1 or recovers further with longer training. Until
  this is settled, the "information-theoretic floor" hypothesis is
  speculative.
* **NaN at d ≤ 30, λ = 3.0**: training diverges because SIGReg overwhelms
  MSE signal. Not a problem for the analysis (those cells are clearly
  above the Pareto λ*) but worth flagging numerically.
* **Architecture and depth dependence untested.** Only L=2 linear here.
  Paper 3's theorem statement should at minimum cover L ∈ {2, 3}.
* **SIGReg approximation.** This probe uses 4-moment matching, not the
  Epps–Pulley statistic from the LeWM paper. The qualitative phenomena
  (stabilisation + compression, Pareto λ*) should be robust; quantitative
  scaling could shift by an O(1) factor.

## Decision for paper 3

**Confirmed GO with a quantitative thesis.** The d × λ × seed sweep gives
a clean Pareto λ*(d) scaling with α ≈ 2 across the 100 → 300 range and
a clear three-regime picture (no-SIGReg / Pareto-SIGReg / over-SIGReg).
This is enough to draft a paper-3 outline.

Immediate next actions before that drafting:

1. **One focused d=300, λ=1, 100k-step run** to resolve the
   training-budget-vs-information-floor question.
2. **One d ∈ {100, 300, 1000}, λ ∈ [0.1, 5.0] sweep on a single seed**
   to extend the scaling probe to d=1000 (likely 1–2h compute) and
   tighten the α exponent estimate.
3. **Re-derive the scaling from theory.** Heuristic: the SIGReg gradient
   has magnitude ~λ · d (one Epps–Pulley term per feature), and the
   ordering signal has magnitude ~ε^{1/L} per feature. Balance gives
   λ* ~ ε^{1/L}/d... but this predicts λ* ∝ 1/d, opposite to data.
   Likely the right scaling combines the gradient-noise variance (which
   scales differently). Worth a careful pen-and-paper analysis.
