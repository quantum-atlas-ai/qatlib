/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Forward Euler global error and the condition number of `L`

Fixed source: arXiv:2011.03185v4 (7 July 2026), Liu--Kolden--Krovi--Loureiro--Trivisa--Childs,
*Efficient quantum algorithm for dissipative nonlinear differential equations*.

This file formalises the analytic skeleton of

* **Lemma 3** (printed pp. 12--16, Eqs. (4.46)--(4.83)): the global error of forward Euler on
  the Carleman system is at most `3 N^{2.5} T h [(‖F₂‖+‖F₁‖+‖F₀‖)² + ‖F₀'‖]`;
* **Lemma 4** (printed pp. 16--17, Eqs. (4.84)--(4.101)): the condition number satisfies
  `κ ≤ 3(m+p+1)`.

Modelling boundary.  Lemma 3's proof has three independent ingredients: the local truncation
estimate (4.55) `e_k ≤ M h²/2`, the contraction/accumulation argument (4.70)--(4.73), and the
bound (4.81) on `M = max ‖ŷ''‖`.  The accumulation argument and the final coefficient
assembly are proved here in full.  The local truncation estimate and the `M` bound are taken as
hypotheses: they require the Carleman block matrices (3.3)--(3.5), Taylor's theorem for the
block ODE, and the spectral-norm estimates (4.76)--(4.80), none of which exist in the current
Lean library.

For Lemma 4 the paper proves `‖L‖ ≤ 3` in (4.89) and `‖L⁻¹‖ ≤ m+p+1` in (4.100), and
multiplies them in (4.101).  The multiplication is proved here (`condition_number_bound`), as
is the noncommutative geometric-series identity `(1-N) ∑_{i<K} N^i = 1` underlying
`L⁻¹ = ∑ L₂^i` for nilpotent `L₂` (`nilpotent_inverse_eq_geom_sum`).  The two operator-norm
bounds are taken as hypotheses of the paper-layer statement.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DissipNonlin20.MainResults.EulerCondition

open scoped BigOperators

/-- **Lemma 3, Eq. (4.70)--(4.71): accumulation of local truncation errors.**

If the global error sequence `g` starts at `g 0 = 0` and each step satisfies
`g k ≤ g (k-1) + e k`, then `g m ≤ ∑_{k=1}^{m} e k`.  This is the iteration displayed in
(4.71), with `e k` the local truncation error (4.51). -/
theorem euler_global_error_accumulation (g e : ℕ → ℝ)
    (hg0 : g 0 = 0) (hrec : ∀ k, g (k + 1) ≤ g k + e (k + 1)) :
    ∀ m : ℕ, g m ≤ (Finset.range m).sum (fun k => e (k + 1)) := by
  intro m
  induction m with
  | zero => simp [hg0]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := hrec n
      linarith

/-- **Lemma 3, Eq. (4.72): global error from the local truncation bound.**

If every local truncation error obeys (4.55), `e k ≤ M h²/2`, then the global error after `m`
steps is at most `m M h²/2`. -/
theorem euler_global_bound_of_local (g e : ℕ → ℝ) (M h : ℝ)
    (hg0 : g 0 = 0) (hrec : ∀ k, g (k + 1) ≤ g k + e (k + 1))
    (he : ∀ k, e (k + 1) ≤ M * h ^ 2 / 2) :
    ∀ m : ℕ, g m ≤ (m : ℝ) * (M * h ^ 2 / 2) := by
  intro m
  have h1 := euler_global_error_accumulation g e hg0 hrec m
  have h2 : ((Finset.range m).sum (fun k => e (k + 1))) ≤
      (Finset.range m).sum (fun _k => M * h ^ 2 / 2) :=
    Finset.sum_le_sum (fun k _ => he k)
  have h3 : ((Finset.range m).sum (fun _k => M * h ^ 2 / 2)) = (m : ℝ) * (M * h ^ 2 / 2) := by
    simp
  linarith

/-- **Lemma 3, Eq. (4.73): the `m h = T` form.**

Substituting `m h = T`, the bound of (4.72) becomes `g m ≤ M T h / 2`. -/
theorem euler_global_bound_T (g e : ℕ → ℝ) (M h T : ℝ) (m : ℕ)
    (hg0 : g 0 = 0) (hrec : ∀ k, g (k + 1) ≤ g k + e (k + 1))
    (he : ∀ k, e (k + 1) ≤ M * h ^ 2 / 2)
    (hm : (m : ℝ) * h = T) :
    g m ≤ M * T * h / 2 := by
  have h1 := euler_global_bound_of_local g e M h hg0 hrec he m
  have hmul : (m : ℝ) * (M * h ^ 2 / 2) = M * T * h / 2 := by
    rw [← hm]
    ring
  linarith

/-- **Lemma 3, Eq. (4.81)--(4.83): coefficient assembly.**

If the second-derivative bound obeys `M ≤ 2 K B` (the paper's (4.81) with
`K = 3 N^{2.5}` and `B = (‖F₂‖+‖F₁‖+‖F₀‖)² + ‖F₀'‖`), then `M T h / 2 ≤ K T h B`.
This is the arithmetic step turning (4.73) into the constant of (4.49). -/
theorem euler_coefficient_assembly (M T h B K : ℝ) (hT : 0 ≤ T) (hh : 0 ≤ h)
    (hMB : M ≤ 2 * K * B) :
    M * T * h / 2 ≤ K * T * h * B := by
  have hmul : M * (T * h / 2) ≤ (2 * K * B) * (T * h / 2) :=
    mul_le_mul_of_nonneg_right hMB (by positivity)
  have heq : (2 * K * B) * (T * h / 2) = K * T * h * B := by ring
  linarith

/-- **Lemma 3, Eq. (4.49)/(4.82)--(4.83): global Euler error bound.**

Combining the accumulation bound with the local truncation hypothesis and the `M` estimate
`M ≤ 2 K B`, where `K = 3 N^{2.5}` and `B = (‖F₂‖+‖F₁‖+‖F₀‖)² + ‖F₀'‖`, gives

`g m ≤ 3 N^{2.5} T h B`.

The hypotheses `he` (local truncation, (4.55)) and `hM` (the `M` estimate, (4.81)) are the
two Carleman-specific inputs; their derivation needs the block matrices (3.3)--(3.5) and the
spectral estimates (4.76)--(4.80), which are not in the current library. -/
theorem lemma3_global_error (g e : ℕ → ℝ) (m : ℕ) (h T N : ℝ)
    (F2 F1 F0 F0' : ℝ) (hN : 0 ≤ N) (hT : 0 ≤ T) (hh : 0 ≤ h) (hF0' : 0 ≤ F0')
    (hg0 : g 0 = 0) (hrec : ∀ k, g (k + 1) ≤ g k + e (k + 1))
    (he : ∀ k, e (k + 1) ≤ (2 * (3 * Real.rpow N (5 / 2)) *
      ((F2 + F1 + F0) ^ 2 + F0')) * h ^ 2 / 2)
    (hm : (m : ℝ) * h = T) :
    g m ≤ 3 * Real.rpow N (5 / 2) * T * h * ((F2 + F1 + F0) ^ 2 + F0') := by
  have h1 := euler_global_bound_T g e (2 * (3 * Real.rpow N (5 / 2)) *
    ((F2 + F1 + F0) ^ 2 + F0')) h T m hg0 hrec he hm
  have hMB : 2 * (3 * Real.rpow N (5 / 2) * ((F2 + F1 + F0) ^ 2 + F0')) ≤
      2 * (3 * Real.rpow N (5 / 2)) * ((F2 + F1 + F0) ^ 2 + F0') :=
    le_of_eq (by ring)
  have h2 := euler_coefficient_assembly (2 * (3 * Real.rpow N (5 / 2) *
    ((F2 + F1 + F0) ^ 2 + F0'))) T h ((F2 + F1 + F0) ^ 2 + F0')
    (3 * Real.rpow N (5 / 2)) hT hh hMB
  linarith

/-- **Lemma 4, geometric-series identity (4.100).**  In any ring, if `N^K = 0` then the finite
geometric sum `∑_{i<K} N^i` is a right inverse of `1 - N`.  This is the algebraic content of
`L⁻¹ = (1 + L₂)^{-1} = ∑_i (-L₂)^i` truncated at the nilpotency index `K = m+p+1`. -/
theorem nilpotent_inverse_eq_geom_sum {R : Type*} [Ring R] (N : R) (K : ℕ)
    (hN : N ^ K = 0) :
    (1 - N) * ((Finset.range K).sum (fun i => N ^ i)) = 1 := by
  rw [mul_neg_geom_sum, hN, sub_zero]

/-- **Lemma 4, Eq. (4.89)+(4.100)--(4.101): condition-number composition.**

If `‖L‖ ≤ 3`, `‖L⁻¹‖ ≤ m+p+1` and `κ = ‖L‖ ‖L⁻¹‖`, then `κ ≤ 3(m+p+1)`.  This is the final
multiplication (4.101). -/
theorem condition_number_bound (m p : ℕ) (κ Lnorm Linv : ℝ)
    (_hL : 0 ≤ Lnorm) (hI : 0 ≤ Linv) (hκ : κ = Lnorm * Linv)
    (hL3 : Lnorm ≤ 3) (hI1 : Linv ≤ (m : ℝ) + p + 1) :
    κ ≤ 3 * ((m : ℝ) + p + 1) := by
  rw [hκ]
  exact mul_le_mul hL3 hI1 hI (by norm_num)

/-- **Lemma 4, Eq. (4.84): the condition number of the linear system is `≤ 3(m+p+1)`.**

Paper-layer statement.  `Lnorm` and `Linv` stand for `‖L‖` and `‖L⁻¹‖` of the block matrix
(3.9); (4.89) and (4.100) provide `Lnorm ≤ 3` and `Linv ≤ m+p+1`, and `κ L Linv` is the
condition-number product.  The displayed multiplication is proved in `condition_number_bound`;
what remains outside Lean is the construction of `L` from the Carleman blocks and the two
operator-norm bounds. -/
theorem lemma4_condition_number_statement (m p : ℕ) (κ Lnorm Linv : ℝ)
    (hL : 0 ≤ Lnorm) (hI : 0 ≤ Linv) (hκ : κ = Lnorm * Linv)
    (hL3 : Lnorm ≤ 3) (hI1 : Linv ≤ (m : ℝ) + p + 1) :
    κ ≤ 3 * ((m : ℝ) + p + 1) :=
  condition_number_bound m p κ Lnorm Linv hL hI hκ hL3 hI1

end Qatlib.Papers.DissipNonlin20.MainResults.EulerCondition
