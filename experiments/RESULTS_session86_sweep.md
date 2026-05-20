# SIGReg ordering sweep — full results (session 86)

**Question.** Does the rho*-ordering of feature learning survive SIGReg
regularisation across spectrum sizes? Does the relationship Spearman(λ) admit
a clean paper-3 conjecture?

**Setup.** Linear JEPA depth-2, init scale ε=0.01, batch=128, lr=0.02 (d≤30)
or 0.01 (d=100). Synthetic Gaussian data with hand-set generalised eigenvalues:
unit μ_r = 1 for all r (so λ_r* = ρ_r*), positive ρ_r* linearly spaced in
[0.3, 1.0], negative ρ_r* linearly spaced in [-0.8, -0.3], rest zero.
Three seeds per cell, step budgets {d=10: 8k, d=30: 12k, d=100: 20k}.

Critical time = first step at which |σ_r(t)| reaches half of |σ_r(t_final)|.
Spearman computed on positive-ρ features only.

## Mean Spearman across 3 seeds

| d \ λ | 0.00 | 0.01 | 0.10 | 0.50 | 1.00 |
|-------|------|------|------|------|------|
| 10    | −1.00 | −1.00 | −1.00 | −0.83 | −0.50 |
| 30    | −0.99 | −0.99 | −0.98 | −0.75 | −0.79 |
| 100   | **−0.38** | **−0.48** | **−1.00** | **−0.67** | **−0.67** |

Final MSE at λ=0: 0.0024 (d=10) → 0.0026 (d=30) → **0.0101** (d=100).

## The headline finding

**At d=100, SIGReg is not just a regulariser — it is a stabiliser that
makes the rho*-ordering OBSERVABLE that would otherwise be masked by
training noise.** In particular:

* λ=0 (no SIGReg) at d=100 produces Spearman ≈ −0.4 — ordering nearly
  destroyed. MSE remains high at ~0.01 even after 20k steps, signalling
  the linear-JEPA dynamics haven't reached their plateau in the
  high-dimensional regime.
* λ=0.10 at d=100 produces **Spearman = −1.00** (perfect ordering across
  all three seeds), with MSE dropping to 0.006. SIGReg accelerates
  convergence and unmasks the spectrum.
* λ=0.50–1.00 at d=100 partly compresses ordering back, but to a lesser
  degree than the unregularised noise (Spearman ≈ −0.67).

This is a **non-monotonic** Spearman(λ) profile at d=100. The structure
is U-shaped (or in this case, "deepest at λ ≈ 0.1"). At smaller d
(d=10, d=30), the unregularised dynamics already converge cleanly, so the
stabilisation effect is invisible and only the compression effect at
large λ appears — yielding the monotonic-destruction profile.

## Implications for paper 3

The naïve conjecture from session 86 ("SIGReg progressively destroys
rho*-ordering as λ grows, monotonically") is **wrong** as stated. The
corrected conjecture is:

> **SIGReg has two competing effects on the spectrum:**
>   (i) a **stabilising** effect that suppresses training noise and
>   reveals the rho*-ordering more cleanly, dominant at small λ
>   (≈0.01–0.1) and at high d;
>   (ii) a **compressing** effect that homogenises the spectrum toward
>   isotropic Gaussian, dominant at large λ (≳0.5).
>
> Spearman(ρ*, t_crit; λ) is therefore generally NON-MONOTONIC in λ,
> with a regime-dependent optimum λ* > 0 (the "Pareto λ") that maximises
> ordering fidelity. At small d this optimum collapses to λ* = 0; at
> larger d the optimum is strictly positive.

This is a richer and more LeWM-compatible story than the monotonic version:

* It explains *why* LeWM works empirically with λ=0.1 — that's near the
  Pareto optimum for the regimes they study.
* It predicts that scaling JEPA to very large d makes anti-collapse
  regularisation **necessary** for the rho*-ordering to be observable
  at all.
* It suggests a theoretical question with crisp empirical falsifiers:
  *"For depth-L linear JEPA at dimension d and init scale ε, the Pareto
  λ scales as λ*(d, ε, L) ~ ???."* Solving this scaling is the kind of
  thing a clean paper-3 theorem could nail.

## Outstanding caveats

* d=100 with λ=0 may converge more cleanly given more steps; the current
  budget (20k) is what we have, but the true asymptotic Spearman at λ=0
  could be more negative than the observed −0.38. A separate run with
  100k steps at λ=0 would clarify.
* The simplified SIGReg (4 moments matching) may behave differently from
  the Epps–Pulley statistic used in the actual LeWM paper. The qualitative
  direction (anti-isotropic-collapse, two competing effects) should be
  robust; quantitative magnitudes and the Pareto λ may shift.
* Single linear-architecture probe; non-linear behaviour untested.
* μ_r = 1 setup eliminates a confounder but is unrealistic. With random
  μ_r, the ordering is by λ_r* = ρ_r* μ_r, not by ρ_r* directly — the
  per-feature critical time still respects λ_r* but the rho*-vs-λ*
  decoupling adds noise.

## Decision

**Paper-3 spinoff is GO with a sharpened thesis.** The non-monotonic
Spearman(λ) story is more interesting and more aligned with LeWM's
empirical claims than the original monotonic conjecture. The next
empirical step (probably one more session) is a focused d-vs-Pareto-λ
sweep to characterise λ*(d) before drafting any formal claim.

Recommended next probe:
* Fix ε=0.01, depth=2, m_r=1.
* For d ∈ {10, 30, 100, 300}, sweep λ ∈ {0, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0}.
* 3 seeds. Locate λ* := argmax(|Spearman|) and plot λ*(d) on log-log.
* If λ*(d) shows clean scaling, that's the paper-3 headline conjecture.
* Then: dispatch a theoretical version to Aristotle (or hand-prove) for
  the small-d analytical regime where we can do this rigorously.

## Numbers summary

```
                 SPEARMAN(rho*, t_crit) [mean over 3 seeds]
       λ=0      λ=0.01    λ=0.10    λ=0.50    λ=1.00
d=10  -1.00     -1.00     -1.00     -0.83     -0.50
d=30  -0.99     -0.99     -0.98     -0.75     -0.79
d=100 -0.38     -0.48     -1.00*    -0.67     -0.67
                          (*** Pareto-optimal λ at d=100 ***)

                 FINAL MSE [mean over 3 seeds]
       λ=0      λ=0.01    λ=0.10    λ=0.50    λ=1.00
d=10   0.0024   0.0027    0.0025    0.0031    0.0063
d=30   0.0026   0.0027    0.0026    0.0037    0.0071
d=100  0.0101   0.0093    0.0061    0.0033    0.0047
```
