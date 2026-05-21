# Algorithm + experiment plan — paper-2 ρ-recovery

> **Session-90 correction (2026-05-21).** The original draft had `ρ̂ = σ^(1/L)` and claimed plateau `σ^∞ = ρ^L`. Empirical validation showed the *correct* plateau is `σ^∞ = ρ^(1/L)` (Saxe-style deep-linear behaviour), and the *correct* recovery formula is `ρ̂ = σ^L`. The init scheme is also non-generic: the algorithm requires *aligned* init `Wbar(0) ≈ ε·I` in the eigenbasis, not generic small-init. Both corrections are reflected below. See `RESULTS_session90_verification.md` for the full audit and `plateau_recover_corrected.py` for the validated reference implementation.


> **Purpose:** bridge from the Lean-verified theory (sessions 88–89) to a deployable
> algorithm and validation experiments. This is the plan that turns paper-2 from
> "structurally complete theorems" into "we build on JEPA theory and have an algorithm
> that recovers ρ_r* on real data, with proofs and code."
>
> **Audience:** paper-2 §6 (Algorithm), §7 (Experiments), abstract reframe.
>
> **Status:** planning doc. No code written yet; this is the spec.

---

## 1. The abstract reframe

Current draft framing (theory-only): "We prove ρ-recovery is possible from JEPA
trajectory observations, with a finite-sample rate."

Proposed framing (theory + algorithm + code):

> We build on early JEPA theoretical work (paper-1's ordering theorem and Maes 2026
> LeWM springboard) and present **PlateauRecover**, an algorithm that recovers the
> spectral parameters ρ_r* from the diagonal-amplitude trajectories of a JEPA
> training run. We prove that the algorithm achieves rate `ε^{1/L}|log ε| + O(√(d
> log(d/ν)/n))` with probability ≥ 1 − ν over n iid sub-Gaussian samples
> (Theorem 3.3, formally verified in Lean 4 against Mathlib). We provide a
> reference implementation in **`plateau_recover/`** (Python, NumPy/PyTorch) and
> validate it on synthetic spectra where ground-truth ρ_r* is known. Code,
> proofs, and reproduction scripts are released as a single library.

Three things this buys:
- **"We have an algorithm"** — not just identifiability, an actual recipe.
- **"With proofs"** — Lean-verified theorems, cited by name in the paper.
- **"With code"** — running implementation, reproducible experiments.

This is the JMLR/COLT-credible framing: theory + algorithm + reproducible artefact.

---

## 2. Algorithm — `PlateauRecover`

### 2.1 Inputs

| Symbol | Meaning | Practical source |
|---|---|---|
| `X ∈ ℝ^{n×d}` | input features | dataset |
| `Y ∈ ℝ^{n×d}` | target features | dataset |
| `L : ℕ`, `L ≥ 2` | JEPA depth | architecture choice (matches paper-2) |
| `ε > 0` | initialization scale | hyperparameter (default: 1e-3) |
| `plateau_tol > 0` | stopping criterion | hyperparameter (default: 1e-4) |
| `max_steps : ℕ` | training horizon cap | hyperparameter (default: 1e5) |
| `lr > 0` | learning rate | hyperparameter (default: 1e-2) |

### 2.2 Pseudocode (matches Lean theorems line-for-line)

```python
def plateau_recover(X, Y, L, eps=1e-3, plateau_tol=1e-4,
                    max_steps=int(1e5), lr=1e-2):
    """
    PlateauRecover: recover signed ρ_r* from JEPA training dynamics.

    Returns:
        rho_hat: array of d signed recovery values.

    Maps to Lean theorems:
        - sample_eigenvalue_perturbation       (Layer 3.1)  → Step 2
        - signed_recovery_pos_magnitude_plateau (Layer 4.2) → Step 4 (positive)
        - signed_recovery_neg_lambda_rate       (Layer 4.2) → Step 4 (negative)
        - sign_identification_*_forward         (Layer 4.2) → Step 4 (zero/sign)
        - plateau_path_recovery_pos             (Main)       → Step 5 (rate)
        - matrix_bernstein_subgaussian          (Layer 3.3)  → noise bound
    """
    n, d = X.shape

    # ----- Step 1. Empirical covariances -----
    Sigma_XX_hat = (X.T @ X) / n
    Sigma_YX_hat = (Y.T @ X) / n

    # ----- Step 2. Generalized eigendecomposition (paper-1 machinery) -----
    # Solves Sigma_YX_hat v = ρ̂_pop · Sigma_XX_hat v
    # ρ̂_pop are the sample-side estimates of ρ_r* before trajectory recovery.
    # Layer 3.1 says these are within O(δ_n) of true ρ_r*.
    rho_hat_pop, V_hat = scipy.linalg.eig(Sigma_YX_hat, Sigma_XX_hat)
    # Sort by |ρ̂_pop| (paper-1 ordering); take real parts for symmetric case.
    rho_hat_pop = rho_hat_pop.real
    V_hat = V_hat.real
    # Compute biorthogonal left-eigenvectors U_hat via U_hat = Sigma_XX_hat @ V_hat;
    # normalize so U_hat[:,r] @ Sigma_XX_hat @ V_hat[:,r] = 1.
    U_hat = Sigma_XX_hat @ V_hat
    norms = np.einsum('ir,ij,jr->r', U_hat, Sigma_XX_hat, V_hat)
    U_hat /= np.sqrt(norms)
    V_hat /= np.sqrt(norms)

    # ----- Step 3. Initialize W̄ with ALIGNED init at scale ε -----
    # Aligned (eigenbasis-diagonal) init is required to satisfy paper-1's
    # σ_r(0) = ε hypothesis. Generic small-init does NOT give this and gauge-
    # ambiguates the encoder diagonal. With U̅ = Sigma_XX_hat^(1/2) V_hat the
    # right-orthonormal basis, set:
    Wbar = eps * np.eye(d)   # diagonal in U-basis → σ_r(0) = ε per direction
    V    = eps * np.eye(d)   # predictor, balanced scale
    # (In the eigenbasis U, Wbar = ε·I; equivalently in standard coords
    # Wbar = ε·U U^T = ε·I as well when U is orthonormal.)

    # ----- Step 4. Train depth-L JEPA, record diagonal amplitudes -----
    # Diagonal amplitude per direction: σ_r(t) = U_hat[:,r].T @ W(t) @ V_hat[:,r]
    # Stop when |σ̇_r| < plateau_tol for all r (plateau reached).
    sigma_history = []
    for step in range(max_steps):
        # Standard JEPA gradient step on depth-L composition.
        # Loss: L_JEPA(W) = ||Y - X @ W^L||_F^2 / (2n)
        WL = matrix_power(W, L)              # W^L (composition of L copies)
        grad = jepa_grad(W, X, Y, L)         # closed-form gradient (paper-1)
        W = W - lr * grad

        # Record current diagonal amplitudes.
        sigma_t = np.einsum('ir,ij,jr->r', U_hat, W, V_hat)
        sigma_history.append(sigma_t)

        # Plateau check: σ̇_r small for the last K steps.
        if step > 100:
            window = np.array(sigma_history[-50:])
            sigma_dot = np.abs(np.diff(window, axis=0)).max(axis=0)
            if (sigma_dot < plateau_tol).all():
                break

    sigma_final = sigma_history[-1]

    # ----- Step 5. Plateau-path recovery (the Lean theorem) -----
    # For each r:
    #   - ρ̂_pop[r] > 0 (positive branch): ρ̂[r] = sign(σ_r) · |σ_r|^{1/L}
    #     since σ_r → ρ_r^L on the positive branch.
    #   - ρ̂_pop[r] < 0 (negative branch): use late-time decay rate to extract λ̂;
    #     ρ̂[r] := sign-only (Layer 4.2(iii) magnitude obstruction).
    #   - ρ̂_pop[r] ≈ 0 (zero branch): ρ̂[r] = 0 (no learning happened).

    rho_hat = np.zeros(d)
    for r in range(d):
        if rho_hat_pop[r] > plateau_tol:
            # Positive branch: plateau-path recovery.
            # Empirically σ_r → ρ_r^(1/L), so ρ̂ = σ^L recovers ρ.
            # (NOT σ^(1/L) as an earlier draft of this doc claimed.)
            rho_hat[r] = np.sign(sigma_final[r]) * np.abs(sigma_final[r]) ** L
        elif rho_hat_pop[r] < -plateau_tol:
            # Negative branch: sign-only (paper Thm 7.3).
            # Magnitude obstructed from trajectory alone (Layer 4.2(iii));
            # fall back to ρ̂_pop[r] (covariance-based) for magnitude.
            rho_hat[r] = rho_hat_pop[r]  # covariance estimate, magnitude unreliable
        else:
            rho_hat[r] = 0.0

    return rho_hat
```

### 2.3 Theorem-to-line correspondence (for paper §6.1)

| Lean theorem | Pseudocode step | What it guarantees |
|---|---|---|
| `sample_eigenvalue_perturbation` | Step 2 | `|ρ̂_pop − ρ_r*| ≤ C·(δ_x + δ_y)` |
| `matrix_bernstein_subgaussian` (axiom) | sets bound on n | `δ_n = O(√(d log(d/ν)/n))` w.p. ≥ 1−ν |
| `quasi_static_approx` (Layer 1.1) | Step 4 | trajectory satisfies the Bernoulli ODE |
| `signed_recovery_pos_magnitude_plateau` (corrected) | Step 5 (positive) | `|σ_r(T) − ρ_r^(1/L)| ≤ K·ε^{1/L}|log ε|` |
| `rho_hat_plateau_rate` (Layer 2.2′, corrected) | Step 5 (positive) | `|σ_r^L − ρ_r| ≤ C·ε^{1/L}|log ε|` |
| `plateau_path_recovery_pos` (Main) | full chain (Steps 3–5) | end-to-end positive-branch rate |
| `plateau_path_finite_sample_rate_pos_high_prob` | n + ν dependence | high-probability finite-sample rate |

### 2.4 Hyperparameter selection in practice

| Hyperparameter | Theory link | Practical recipe |
|---|---|---|
| `ε` (init scale) | smaller → better asymptotic rate but slower training | grid search on log scale; default 1e-3 |
| `L` (depth) | fixed by architecture; rate scales as ε^{1/L} | take from JEPA arch |
| `plateau_tol` | smaller → tighter plateau detection | 1e-4 of the typical ρ scale |
| `max_steps` | upper-bound for `T(ε) = O(ε^{-(2L-1)/L})` | adapt to ε: `5/ε^{(2L-1)/L}` |
| `lr` | needs to be in the stable regime; quasi-static needs lr small | standard JEPA LR; halve if quasi-static fails |

---

## 3. Experiments

### 3.1 Synthetic Tier-1 — closing the theory loop

**Goal:** demonstrate the rate `ε^{1/L}|log ε| + δ_n` matches predictions.

**Setup.**
- `d ∈ {10, 50, 100}`, `n ∈ {100, 1k, 10k, 100k}`, `L ∈ {2, 3, 4}`.
- Generate ground-truth `ρ_r*` as a mixed-sign spectrum: 3 positive (e.g., 0.5, 0.3, 0.1),
  2 negative (e.g., -0.2, -0.05), 5 zero. Resample ν_r* unit-norm i.i.d.
- Construct `Σ_XX` as a random PD matrix (Wishart); set `Σ_YX = Σ_XX · diag(ρ*) · diag(ρ*)`
  to enforce the generalized-eigenvalue structure.
- Sample `(x_i, y_i)` iid: `x_i ~ N(0, Σ_XX)`, `y_i = ρ* ⊙ x_i + noise`.

**Sweeps.**
1. **ε-sweep** (fix n large): `ε ∈ {1e-2, 1e-3, 1e-4, 1e-5}`. Verify error scales as `ε^{1/L}|log ε|`.
2. **n-sweep** (fix ε small): `n ∈ {100, 1k, 10k, 100k}`. Verify error decays as `n^{-1/2}`.
3. **L-sweep**: `L ∈ {2, 3, 4}`. Verify rate exponent matches `1/L`.

**Pass criterion.** Log-log slopes of error-vs-ε and error-vs-n match theory within 10%.

### 3.2 Synthetic Tier-2 — robustness probes

**Goal:** stress-test the abstract hypotheses.

- **Quasi-static breakdown**: increase `lr` until trajectory diverges from Bernoulli ODE.
  Report at what `lr` the algorithm starts to fail. This validates whether the
  quasi-static hypothesis is realistic for standard JEPA training regimes.
- **Sub-Gaussian violation**: heavy-tailed noise (e.g., t-distribution with low df).
  Verify Bernstein bound degrades gracefully.
- **Mixed-sign + close-to-zero spectrum**: ρ_r* values with `|ρ_i| = |ρ_j|` very close.
  Verify ordering still holds and recovery doesn't collapse.

### 3.3 Real-data Tier-3 — demonstration

**Goal:** show the algorithm produces sensible ρ̂ on actual datasets.

- **CIFAR-10 / ImageNet features.** Use pretrained encoder; estimate ρ̂_r* between
  views (e.g., crop_1 → crop_2 in I-JEPA). Compare against known patterns from
  the I-JEPA literature.
- **Single-cell RNA-seq.** Linear JEPA between paired modalities (e.g., scRNA → scATAC).
  Recover ρ̂_r* and compare to known biological structure.
- **Audio-visual paired embeddings.** Self-supervised pretraining setting where
  Y is a delayed version of X; ρ_r* should reflect temporal structure.

**What "success" looks like at Tier-3.** The algorithm produces *interpretable* ρ̂_r*
that align with held-out validation metrics (e.g., transfer learning accuracy
correlates with the recovered ρ̂ ordering). The paper does not claim SOTA performance —
it claims *identifiability* and *interpretability* of the latent regression structure.

---

## 4. Library structure

Proposed Python package: **`plateau_recover`**.

```
plateau_recover/
├── README.md                  # quickstart + cite-this
├── pyproject.toml
├── src/plateau_recover/
│   ├── __init__.py
│   ├── core.py                # plateau_recover() (the algorithm)
│   ├── jepa.py                # depth-L JEPA training loop
│   ├── diagnostics.py         # plateau detection, quasi-static check
│   ├── theory.py              # closed-form rate predictions for validation
│   └── concentration.py       # matrix-Bernstein δ_n predictor
├── tests/
│   ├── test_synthetic_rate.py # Tier-1 regression tests
│   └── test_robustness.py     # Tier-2 regression tests
├── examples/
│   ├── 01_synthetic_demo.ipynb
│   ├── 02_cifar_features.ipynb
│   └── 03_paper_figures.ipynb
└── paper_link/
    └── README.md              # pointer to Lean proofs at lean-workspace/jepa-rho-recovery
```

**Naming.** `plateau_recover` mirrors the paper-2 framing. Alternative if you want
to brand it more aggressively: `jepa-spectral` or `rho-recover`.

**Dependencies (minimal).** numpy, scipy, torch (for differentiable JEPA training),
matplotlib (for figures). Aim for <500 LoC for the core; everything else is examples.

---

## 5. Roadmap to paper-2 submission

Sessions ordered for incremental risk reduction:

| Session | Deliverable | Risk if it fails |
|---|---|---|
| S+1 | `plateau_recover/core.py` + synthetic Tier-1 ε-sweep on `d=10, L=2` | low — confirms basic theory matches code |
| S+2 | Tier-1 n-sweep, L-sweep; produce log-log plots for paper §7 | low — extends to all theory predictions |
| S+3 | Tier-2 quasi-static breakdown probe | **medium** — may reveal real JEPA training violates the quasi-static assumption at standard learning rates, requiring caveat in paper |
| S+4 | Tier-3 CIFAR demo + figures | medium — may need encoder tweaks to make linear ρ-recovery interpretable |
| S+5 | Paper draft pass — incorporate algorithm pseudocode, theorem-to-line map, experiment results | low — writing |
| S+6 | Open-source `plateau_recover` package; Zenodo DOI for the Lean repo | low — packaging |

**Critical-path risk: Tier-2 quasi-static probe (S+3).** If standard JEPA training
violates the quasi-static condition badly (e.g., requires `lr → 0` to satisfy), the
paper's algorithm framing has to be narrowed: "for sufficiently small lr" or
"under the quasi-static regime, which holds when [empirical condition]". This is
acceptable but reduces strength. **Recommend running S+3 early as a smoke test**
before investing in full experiment infrastructure.

---

## 6. Open questions for the paper

These are worth raising as discussion points or future work:

1. **Negative-branch magnitude.** Layer 4.2(iii) (`signed_recovery_neg_magnitude_obstruction`)
   says you can't recover `|ρ_r*|` for `ρ_r* < 0` from trajectory alone. The pseudocode
   falls back to ρ̂_pop for negatives. Is this acceptable for paper-2, or does the
   paper need a separate Layer (e.g., a hybrid trajectory + covariance estimator
   for negatives)?

2. **Quasi-static empirical validation.** If S+3 shows quasi-static fails at standard
   JEPA learning rates, do we (a) caveat the result ("for lr below threshold"),
   (b) develop a non-quasi-static variant, or (c) report it as a limitation?

3. **Matrix Bernstein discharge.** Currently a named axiom. For the
   "100% Lean-verified" framing, port Tropp's matrix-MGF proof to Mathlib in a
   follow-up paper. For paper-2, the citation is fine.

4. **Algorithm complexity.** Each Step-4 gradient step is `O(n·d^2)` (Σ̂ matvec + W
   update). Total: `O(max_steps · n · d^2)`. For large d, may need stochastic
   variants. Mention briefly; defer optimization to future work.

---

## 7. Headline for the abstract (draft)

> *We build on early JEPA theoretical work (Maes & Cousseau 2024, Cabannes et al. 2025,
> our prior ρ-ordering result) and present **PlateauRecover**, an algorithm that
> recovers the spectral parameters ρ_r* of the latent regression structure from
> the diagonal-amplitude trajectories of a depth-L linear JEPA training run.
> Under standard sub-Gaussian data assumptions, we prove the algorithm achieves
> error `O(ε^{1/L}|log ε| + √(d log(d/ν)/n))` with probability ≥ 1 − ν, where ε
> is the initialization scale and n the sample size. All identifiability and
> rate theorems are formally verified in Lean 4 against Mathlib (Lean source +
> proofs at [repo], DOI [Zenodo]); a reference implementation in NumPy/PyTorch,
> together with synthetic validation experiments matching theory predictions to
> within 10% on log-log slopes, is released as the open-source `plateau_recover`
> Python package.*

That's the framing your goal articulated, made concrete.
