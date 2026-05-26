# Empirical Validation Plan — jepa-rho-recovery

> Written session 102, 2026-05-25. Committed as the multi-session roadmap.
> Status column updated each session as experiments run.

---

## Already done

| ID | Session | What | Result | Status |
|---|---|---|---|---|
| E0a | 90 | σ-convention verification — ODE form fit (paper-1 vs Saxe), 6 features | Saxe correct; paper-1 sign wrong for 4/6 features near plateau | ✅ |
| E0b | 90 | Positive-branch smoke: n=4096, d=10, L=2, sup-error across spectrum | ~10⁻³ across all features | ✅ |
| E0c | 98 | n-scaling: n∈{4096,16384,65536}, Bernstein n^{-1/2} check | 4.3:1 ratio across 16× n (theory 4:1) | ✅ |
| E0d | 98 | Rate-isolation smoke: n∈{4096,16384}, ε-sweep, slope_corrected | 0.20→0.32 as n↑ (theory 0.50); sample-noise-floor hypothesis confirmed | ✅ |

---

## Priority 1 — Close the rate claim (Thm 5.1′)

### E1a: ε-sweep at large n

**Paper claim:** `|ρ̂ − ρ*| ≤ C·ε^{1/L}|log ε|`

**Setup:**
- `n ∈ {65536, 262144}`, `ε ∈ {3e-1, 1e-1, 3e-2, 1e-2, 3e-3, 1e-3}`
- 3 seeds, 80k steps, d=10, L=2
- Script: `rate_isolation_probe.py` (already exists, just extend `--ns` and `--steps`)

**Pass criterion:** `slope_corrected ≥ 0.45` at n=262144 in the middle ε range (1e-2 to 3e-2).

**What failure means:** slope stays well below 0.5 at n=262144 → real empirical finding, must caveat rate claim.

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

### E1b: L-sweep (rate exponent 1/L)

**Paper claim:** rate exponent is exactly `1/L` — directly tests the depth dependence.

**Setup:**
- `L ∈ {2, 3, 4}`, `n=65536`, same ε grid as E1a, 3 seeds
- New sweep param in `rate_isolation_probe.py`

**Pass criterion:** slope_corrected tracks 1/L within ±0.1 for each L.

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

---

## Priority 2 — Validate the signed decomposition (Thms 7.1, 7.3)

### E2a: Negative-branch sign identification (Thm 7.1 trichotomy)

**Paper claim:** σ_r → (ρ*)^{1/L} for ρ* > 0, constant for ρ* = 0, decay to 0 for ρ* < 0.

**Setup:**
- Mixed-sign spectrum: `ρ* = {+0.6, +0.4, +0.2, −0.3, −0.1, 0.0}`, n=16384, d=6, L=2
- `ε ∈ {1e-2, 1e-3, 1e-4}`, 3 seeds
- Plot σ_r(t) trajectories; record sign of each asymptote; compare to sign(ρ*)

**Pass criterion:** sign recovery accuracy = 100% across all ε values and seeds.

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

### E2b: Negative-branch λ-rate (Thm 7.3 part 1)

**Paper claim:** decay-curve estimator recovers |λ*| at rate O(ε^{1/L}).

**Estimator:** `v(t) = σ(t)^{-(2L-1)/L}`, estimate `λ̂ = (L/(2L-1)) · v(T)/T`, compare to |λ*|.

**Setup:**
- Negative features from E2a; range of T values (need T large enough for power-law to dominate)
- Sweep ε, plot |λ̂ − |λ*|| vs ε; expect slope ≈ 1/L
- Note: needs longer training horizon than positive branch (suppression is slower)

**Pass criterion:** log-log slope ≈ 1/L within ±0.15.

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

---

## Priority 3 — Validate joint identifiability (Thm 5.2)

### E3: Early-slope λ̂ estimator

**Paper claim:** trajectory is a sufficient statistic for (λ*, μ); early-slope estimator recovers λ* at rate ε^{(L+1)/L}|log ε|.

**Estimator:** at `t_0 = c·λ^{-1}·ε^{-(2L-1)/L}`, use `λ̂ = (L/(2L-1))·(ε^{-(2L-1)/L} − σ(t_0)^{-(2L-1)/L}) / t_0`. Then `μ̂ = λ̂/ρ̂`.

**Setup:**
- Positive features (ρ* > 0), known (λ*, μ*), L=2
- Sweep ε; record |λ̂ − λ*| and |μ̂ − μ*|; plot log-log

**Expected complication:** `t_0` depends on λ*, which is unknown in practice — need a practical recipe (e.g., use ρ̂_pop × μ̂_pop as an initial λ* estimate).

**Pass criterion:** |λ̂ − λ*| decays with ε; combined |μ̂ − μ*| also decays.

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

---

## Priority 4 — Quasi-static regime probe (critical-path risk)

### E4: Learning-rate sweep

**Risk:** if standard JEPA learning rates violate the quasi-static assumption, the paper's §6.1 algorithm framing needs a caveat.

**Setup:**
- `lr ∈ {1e-4, 1e-3, 1e-2, 5e-2, 1e-1}`, n=4096, d=10, L=2
- For each lr: train, fit Saxe ODE form residual using `ode_form_fit.py` infrastructure
- Report median relative residual at each lr

**Pass criterion (strong):** median relative residual < 0.5 at lr=1e-2 (standard JEPA regime).

**Outcome A (residual < 0.5 at standard lr):** claim holds without caveat.
**Outcome B (residual ≥ 0.5 at standard lr):** add "for lr below [threshold]" to §6.1.

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

---

## Priority 5 — Mixed-sign ordering (Thm 9.1)

### E5: Ordering visualization

**Paper claim:** all positive-ρ features finish learning before any negative-ρ feature reaches its suppression threshold.

**Setup:**
- Mixed-sign spectrum, plot critical times per feature: time to enter δ-neighbourhood of plateau (positive) vs time to drop below δ (negative)
- Verify the gap condition `ρ_1* > max_{r∈N} |ρ_r*|` and check ordering

**Pass criterion:** visible temporal separation in the plot for a range of gap conditions.

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

---

## Stretch — Real data

### E6: CIFAR-10 or paired RNA-seq demo

**Goal:** interpretable ρ̂ on actual data; figure for §7.

**Setup (CIFAR-10 option):**
- Pretrained encoder; two random crops as X and Y
- Run PlateauRecover; interpret the signed ρ̂ spectrum

**Risk:** linear JEPA on frozen features may not exhibit the same Saxe dynamics. Report as "demonstration under linearised dynamics assumption."

| Status | | Result |
|---|---|---|
| ⏳ not run | | — |

---

## Session roadmap

| Session | Experiments | Output |
|---|---|---|
| S+1 | E1a (ε-sweep n=65536), E2a (sign ID), E4 (quasi-static probe) | Key risk items cleared or caveated |
| S+2 | E1a n=262144, E1b (L-sweep), E2b (neg-branch λ-rate) | Rate claim fully supported |
| S+3 | E3 (joint identifiability), E5 (ordering visualization) | Thm 5.2 + Thm 9.1 validated |
| S+4 | E6 (real data demo) + paper §7 draft | Submission-ready experiments section |

> **Critical-path:** run E4 (quasi-static probe) in S+1 before investing in library infrastructure. A bad result there changes the paper framing.
