# SIGReg-ordering probe — results (session 86)

**Question.** Does the rho*-ordering of feature learning (paper 1 + paper 2)
survive when JEPA is trained with the SIGReg anti-collapse regulariser used
by LeWorldModel (Maes et al. 2026)?

**Setup.** Synthetic linear-Gaussian data, `d=10`, hand-set generalised
eigenvalues with 5 positive and 3 negative rho* spaced geometrically, 2 zero;
depth-2 linear JEPA at init scale eps=0.01, lr=0.02, 12000 SGD steps,
batch=128. Two variants:
* A: MSE only.
* B: MSE + 0.1 * SIGReg (simplified moment-matching to N(0,1) on 32 random
  1D projections).

Critical time = first step at which |sigma_r(t)| reaches half of |sigma_r(t_final)|.
Analysis restricted to positive-rho features (cleanest theoretical regime).

## Results across 4 seeds (0, 1, 2, 3)

Spearman rank correlation rho* vs critical-time (expect strongly NEGATIVE if
ordering holds — larger rho* learns faster):

| Seed | Variant A | Variant B | Notes |
|------|-----------|-----------|-------|
| 0    | -0.900    | -0.400    | SIGReg compresses spectrum |
| 1    | -0.900    | -0.800    | Ordering nearly preserved |
| 2    | -0.800    | -0.300    | Strongest SIGReg effect |
| 3    | -0.900    | -0.500    | Moderate compression |
| **Mean** | **-0.875** | **-0.500** | |

## Interpretation

* **Variant A confirms paper-1's ordering theorem.** Spearman -0.875 mean is
  strongly negative; the linear-JEPA trajectory respects rho*-ordering.
* **Variant B shows SIGReg WEAKENS but does NOT DESTROY ordering.** Mean
  Spearman -0.500 is still negative across all seeds, but with substantial
  variance and notably reduced magnitude (mean drops by ~0.375).
* **Mechanism (qualitative observation from per-feature critical times):**
  SIGReg accelerates the learning of low-importance features (small rho*),
  presumably because pushing latents toward isotropic Gaussian requires
  injecting variance into all directions, including ones JEPA would
  otherwise learn last. The high-rho features still learn first; the
  low-rho features just close the gap.

## Implications for paper 3 (LeWM/SIGReg spinoff)

* **The signed-decomposition story plausibly extends.** Ordering survives,
  so a paper-3 program that conjectures (and tries to prove) a sharper
  trichotomy under SIGReg has empirical support.
* **The right theoretical claim is NOT "rho*-ordering is preserved exactly"
  but rather "rho*-ordering is preserved up to a SIGReg-induced compression."**
  The compression should be characterisable as a function of lambda (the
  SIGReg weight) and the target distribution's moments.
* **An open question worth dispatching to theory:** can we derive an
  effective rho_r*(lambda) that accounts for the SIGReg pressure, such
  that ordering by the EFFECTIVE rho is exact even with SIGReg active?
  This would be a clean paper-3 headline.
* **Negative-rho features:** under-explored in this probe (the suppression
  dynamics + plateau-at-zero make critical-time poorly defined). A second
  probe with a different timescale observable (e.g. suppression rate)
  should test whether SIGReg interferes with the negative branch.

## Caveats / known limitations

* d=10 is small; behaviour may differ at d=100 or in transformer-scale
  models. Run a sweep over d in {10, 30, 100} before any external claim.
* eps=0.01 is a regime where paper 1 / paper 2 theory is cleanest; at
  realistic init scales the effect may be different.
* SIGReg implementation here is simplified (4 moments matching, not the
  Epps-Pulley statistic from the LeWM paper). The qualitative direction
  should be similar (anti-isotropic-collapse), but quantitative magnitudes
  may differ.
* Single linear-JEPA architecture; non-linear extension untested.

## Decision for paper-3 scoping

**GO.** The empirical signal supports a paper-3 conjecture: SIGReg
preserves rho*-ordering up to a compression that should be characterisable.
This is a tractable theoretical question and the empirical foundation is
in place.

Next probe (one session): sweep d in {10, 30, 100}, sweep lambda in
{0.01, 0.1, 0.5, 1.0}, plot Spearman vs lambda, look for a clean scaling
relationship. If the curve is monotonic in lambda, that's the conjecture
to prove.
