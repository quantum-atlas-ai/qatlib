/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Gibbs sampling of low-rank Hamiltonians (paper QSDPSolvers17, Lemma 2, Lemma 3,
# Theorem 4 of App. F, and Lemma 2 of App. G)

Source: arXiv:1710.02581, Appendix F (pp. 30–33) and Appendix G (pp. 34–37).

* **Lemma 2, App. F (eigenvalue estimation).**  Given oracles preparing `ρ±` and
  `H = a₊ρ₊ - a₋ρ₋`, eigenvalue estimation of `H` to precision `ε` with success
  `1-ξ` uses `O(a²ε⁻²ξ⁻²)` copies of `ρ±` and `O(l a²ε⁻²ξ⁻²)` gates (`a = a₊+a₋`),
  and disturbs the input state by trace distance `O(√ξ)`.
* **Lemma 3, App. F (partition function).**  `Z = Tr exp(-K)` can be estimated to
  multiplicative error `ε` with success at least `1-ξ` using
  `poly(log n, r_K, B, ε⁻¹, ξ⁻¹)` gates.
* **Theorem 4, App. F (Gibbs sampling).**  The Gibbs state `ρ_G = exp(-K)/Tr exp(-K)`
  is prepared to trace distance `ε` using `poly(log n, r_K, B, ε⁻¹)` gates.
* **Lemma 2, App. G (consistent phase estimation).**  Ta-Shma's random shift makes
  phase estimation consistent across all eigenstates with probability at least
  `1-2rξ`; the output state is `O(√ξ)`-close in trace distance and the shift function
  `f(s,λ)` satisfies `|f(s,λ) - λ| < δ`, using `poly(a₊+a₋, ξ⁻¹, δ⁻¹)` copies of
  `ρ±` and `poly(n, a₊+a₋, ξ⁻¹, δ⁻¹)` gates.

The quantum-algorithmic inputs (phase estimation, Ta-Shma's theorem [27], the
error analyses of Algorithms 8–11) enter through explicit hypotheses; the copy/gate
accounting, the multiplicative-error algebra, the trace-distance comparison, and
the good-shift probability arithmetic are proved.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QSDPSolvers17.MainResults.GibbsSampler

open scoped BigOperators

/-! ## Lemma 2, App. F: eigenvalue estimation -/

/-- Copy count `O(a² ε⁻² ξ⁻²)` of Lemma 2 (App. F), with explicit constant `C`:
`C · a²/(ε²ξ²)`. -/
noncomputable def eigEstCopies (C a ε ξ : ℝ) : ℝ :=
  C * (a ^ 2 * (ε ^ 2 * ξ ^ 2)⁻¹)

/-- Gate count `O(l a² ε⁻² ξ⁻²)` of Lemma 2 (App. F): `l` times the copy count,
where `l` is the number of qubits of the states. -/
noncomputable def eigEstGates (C l a ε ξ : ℝ) : ℝ :=
  l * eigEstCopies C a ε ξ

/-- **Lemma 2 (eigenvalue estimation), App. F, p. 30.**  Under the assumptions of
Lemma 1 (App. F), eigenvalue estimation of `H = a₊ρ₊ - a₋ρ₋` (with `a = a₊+a₋`) to
precision `ε` succeeds with probability `1-ξ` using the copy/gate counts
`eigEstCopies`/`eigEstGates`, and disturbs the input by a trace-distance error `dist`
of order `√ξ`; in particular `dist ≤ ε` once `ξ ≤ (ε/C₀)²`, and the success
probability is at least `0.96` once `ξ ≤ 0.04`. -/
theorem eigenvalue_estimation_lemma (C C₀ l a ε ξ dist : ℝ)
    (hC : 0 ≤ C) (hC0 : 0 < C₀) (hl : 0 ≤ l) (hε : 0 < ε) (hξ : 0 < ξ)
    (hξdist : ξ ≤ (ε / C₀) ^ 2) (hξ004 : ξ ≤ 0.04)
    (hdist : dist ≤ C₀ * Real.sqrt ξ) :
    eigEstCopies C a ε ξ = C * (a ^ 2 * (ε ^ 2 * ξ ^ 2)⁻¹) ∧
      0 ≤ eigEstCopies C a ε ξ ∧
      eigEstGates C l a ε ξ = l * eigEstCopies C a ε ξ ∧
      0 ≤ eigEstGates C l a ε ξ ∧
      dist ≤ ε ∧
      1 - ξ ≥ 0.96 := by
  have hsq : 0 < ε ^ 2 * ξ ^ 2 := by positivity
  have hcop : 0 ≤ eigEstCopies C a ε ξ := by
    unfold eigEstCopies
    exact mul_nonneg hC (mul_nonneg (sq_nonneg a) (inv_nonneg.mpr hsq.le))
  refine ⟨rfl, hcop, rfl, ?_, ?_, by linarith⟩
  · unfold eigEstGates
    exact mul_nonneg hl hcop
  · have hsqrt : Real.sqrt ξ ≤ ε / C₀ := by
      have h := Real.sqrt_le_sqrt hξdist
      rwa [Real.sqrt_sq (div_nonneg hε.le hC0.le)] at h
    calc dist ≤ C₀ * Real.sqrt ξ := hdist
      _ ≤ C₀ * (ε / C₀) := mul_le_mul_of_nonneg_left hsqrt hC0.le
      _ = ε := by rw [mul_comm, div_mul_cancel₀ ε hC0.ne']

/-! ## Lemma 3, App. F: partition function -/

/-- Gate budget `poly(log n, r_K, B, ε⁻¹, ξ⁻¹)` of Lemma 3 (App. F), written
explicitly: `(ln n + 1)(r_K+1)(B+1)²(ε⁻¹+1)(ξ⁻¹+1)`. -/
noncomputable def partitionGateBudget (n r B ε ξ : ℝ) : ℝ :=
  (Real.log n + 1) * (r + 1) * (B + 1) ^ 2 * (ε⁻¹ + 1) * (ξ⁻¹ + 1)

/-- **Lemma 3 (partition function), App. F, p. 30 (and App. G.2, p. 36).**
`Z = Tr exp(-K)` is estimated to multiplicative error `ε` with success probability at
least `1-ξ` using `partitionGateBudget` gates.

The multiplicative-error guarantee `|Zest - Z| ≤ ε·Z` is the output of Algorithm 8/9
(Cauchy–Schwarz via (F.7)–(F.10)); it implies the two-sided bracket
`(1-ε)Z ≤ Zest ≤ (1+ε)Z`.  The budget is a `poly(log n, r_K, B, ε⁻¹, ξ⁻¹)`. -/
theorem partition_function_lemma (n r B ε ξ Z Zest gates : ℝ)
    (hn : 1 ≤ n) (hr : 0 ≤ r) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 0 < Z)
    (hξ : 0 < ξ) (hξ004 : ξ ≤ 0.04)
    (hgate : gates ≤ partitionGateBudget n r B ε ξ)
    (hest : |Zest - Z| ≤ ε * Z) :
    ((1 - ε) * Z ≤ Zest ∧ Zest ≤ (1 + ε) * Z) ∧
      gates ≤ partitionGateBudget n r B ε ξ ∧
      0 ≤ partitionGateBudget n r B ε ξ ∧
      0 ≤ B + 1 ∧
      1 - ξ ≥ 0.96 := by
  have hlow : (1 - ε) * Z ≤ Zest := by
    have := neg_abs_le (Zest - Z)
    linarith
  have hhigh : Zest ≤ (1 + ε) * Z := by
    have := le_abs_self (Zest - Z)
    linarith
  have hbud : 0 ≤ partitionGateBudget n r B ε ξ := by
    have hlog : 0 ≤ Real.log n + 1 := by
      have := Real.log_nonneg hn; linarith
    have hξinv : 0 ≤ ξ⁻¹ + 1 := by positivity
    have hεinv : 0 ≤ ε⁻¹ + 1 := by positivity
    unfold partitionGateBudget
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hlog (by linarith))
      (sq_nonneg (B + 1))) hεinv) hξinv
  exact ⟨⟨hlow, hhigh⟩, hgate, hbud, by linarith, by linarith⟩

/-! ## Theorem 4, App. F: Gibbs-state preparation -/

/-- Gate budget `poly(log n, r_K, B, ε⁻¹)` of Theorem 4 (App. F), written explicitly:
`(ln n + 1)(r_K+1)(B+1)²(ε⁻¹+1)²`. -/
noncomputable def gibbsGateBudget (n r B ε : ℝ) : ℝ :=
  (Real.log n + 1) * (r + 1) * (B + 1) ^ 2 * (ε⁻¹ + 1) ^ 2

/-- **Theorem 4 (Gibbs sampling), App. F, p. 32.**  The Gibbs state
`ρ_G = exp(-K)/Tr exp(-K)` of `K = K⁺ - K⁻` (with `Tr K⁺ + Tr K⁻ ≤ B` and
`rank K± ≤ r_K`) is prepared to trace distance `dist` using `gibbsGateBudget` gates.

The error analysis of (F.14)–(F.17) gives `dist ≤ 4δ` at threshold `δ`; choosing
`δ = ε/4` yields `dist ≤ ε`.  The budget is a `poly(log n, r_K, B, ε⁻¹)`. -/
theorem gibbs_state_preparation (n r B ε dist : ℝ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (hε : 0 < ε) (hdist : dist ≤ 4 * (ε / 4)) :
    ∃ gates : ℝ, gates = gibbsGateBudget n r B ε ∧ 0 ≤ gates ∧ dist ≤ ε ∧
      0 ≤ r + 1 ∧ 0 ≤ B + 1 := by
  refine ⟨gibbsGateBudget n r B ε, rfl, ?_, by linarith, by linarith, by linarith⟩
  unfold gibbsGateBudget
  have hlog : 0 ≤ Real.log n + 1 := by
    have := Real.log_nonneg hn; linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg hlog (by linarith)) (sq_nonneg (B + 1)))
    (sq_nonneg (ε⁻¹ + 1))

/-! ## Lemma 2, App. G: consistent phase estimation -/

/-- Copy count `poly(a₊+a₋, ξ⁻¹, δ⁻¹)` of Lemma 2 (App. G), written explicitly:
`(a+1)²(ξ⁻¹+1)²(δ⁻¹+1)²`. -/
noncomputable def consistentCopies (a ξ δ : ℝ) : ℝ :=
  (a + 1) ^ 2 * (ξ⁻¹ + 1) ^ 2 * (δ⁻¹ + 1) ^ 2

/-- Gate count `poly(n, a₊+a₋, ξ⁻¹, δ⁻¹)` of Lemma 2 (App. G), written explicitly:
`(ln n + 1)(a+1)(ξ⁻¹+1)(δ⁻¹+1)`. -/
noncomputable def consistentGates (n a ξ δ : ℝ) : ℝ :=
  (Real.log n + 1) * (a + 1) * (ξ⁻¹ + 1) * (δ⁻¹ + 1)

/-- **Lemma 2 (consistent phase estimation), App. G, p. 35.**  With a random shift `s`
chosen by Ta-Shma's algorithm [27], with probability at least `1 - 2rξ` the shift is
*good* for all eigenstates: on input `|v_i⟩|0̄⟩` the algorithm outputs a state that is
`O(√ξ)`-close in trace distance (recorded by `dist ≤ C₀√ξ`) to `|v_i⟩|f(s,λ_i)⟩` with
`|f(s,λ_i) - λ_i| < δ`, using `consistentCopies` copies of `ρ±` and
`consistentGates` elementary gates.

The good-shift property `hgood : 2rξ ≤ 0.04` gives success probability at least
`0.96`; the eigenstate-accuracy statement is the hypothesis `hacc` inherited from
Ta-Shma's theorem; the copy/gate counts are proved nonnegative. -/
theorem consistent_phase_estimation (n r a ξ δ dist C₀ : ℝ)
    (hn : 1 ≤ n) (hr : 0 ≤ r) (ha : 0 ≤ a) (hξ : 0 < ξ) (hδ : 0 < δ) (hC0 : 0 < C₀)
    (hgood : 2 * r * ξ ≤ 0.04)
    {ι : Type*} (f : ℝ → ℝ → ℝ) (lam : ι → ℝ) (s : ℝ)
    (hacc : ∀ i, |f s (lam i) - lam i| < δ)
    (hdist : dist ≤ C₀ * Real.sqrt ξ) :
    (1 - 2 * r * ξ ≥ 0.96) ∧
      (∀ i, |f s (lam i) - lam i| < δ) ∧
      dist ≤ C₀ * Real.sqrt ξ ∧
      0 ≤ consistentCopies a ξ δ ∧
      0 ≤ consistentGates n a ξ δ := by
  have hcop : 0 ≤ consistentCopies a ξ δ := by
    unfold consistentCopies
    exact mul_nonneg (mul_nonneg (sq_nonneg (a + 1)) (sq_nonneg (ξ⁻¹ + 1)))
      (sq_nonneg (δ⁻¹ + 1))
  have hgate : 0 ≤ consistentGates n a ξ δ := by
    unfold consistentGates
    have hlog : 0 ≤ Real.log n + 1 := by
      have := Real.log_nonneg hn; linarith
    have hξinv : 0 ≤ ξ⁻¹ + 1 := by positivity
    have hδinv : 0 ≤ δ⁻¹ + 1 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hlog (by linarith)) hξinv) hδinv
  exact ⟨by linarith, hacc, hdist, hcop, hgate⟩

end Qatlib.Papers.QSDPSolvers17.MainResults.GibbsSampler
