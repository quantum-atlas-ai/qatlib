/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodySim96.MainResults.Basic

/-!
# First-order segment selection and error bounds

The source uses positive-sign evolution `exp(iTH)`, represented here as `HamiltonianEvolution H
(-T)`. `sourceFirstSegments` chooses a positive first-order segment count from a uniform summand
norm bound. The resulting product formula satisfies explicit operator, observable, and
factor-count estimates.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `source_first_order_selected`: For Hermitian summands bounded by nonnegative `b` and `ε > 0`,
  the selected first-order formula has positive segment count, length `M * r`, unitary
  interpretation, operator error at most `ε` for `exp(iT∑H)`, and observable error at most `2 *
  ‖O‖ * ε`.
* `sourceFirstSegments_le`: If `0 ≤ b ≤ B` and `ε > 0`, the selected segment count is at most `1
  + ceil(T ^ 2 / ε) * (M * B) ^ 2`.
* `source_first_order_polynomial_macro_count`: Polynomial bounds on the term count and uniform
  norm give the displayed polynomial bound on the total number of first-order factors.

## References

* [Wiesner, 1996][Wiesner1996]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.FiniteStrang
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ManyBodySim96.MainResults

/-- The positive-sign exponential `exp(i * t * H)` equals Hamiltonian evolution at time `-t`. -/
theorem source_positive_evolution {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • H) = HamiltonianEvolution H (-t) := by
  unfold HamiltonianEvolution
  simp

/-- If all `M` summands have norm at most a nonnegative `b`, their tail-commutator norm sum is
at most `2 * M ^ 2 * b ^ 2`. -/
theorem bounded_tail_commutator_sum {D M : ℕ} (H : Fin M → Operator D)
    (b : ℝ) (hb : 0 ≤ b) (hH : ∀ j, ‖H j‖ ≤ b) :
    (∑ j : Fin M, ‖pfComm (finiteStrangTail H j) (H j)‖) ≤
      2 * (M : ℝ) ^ 2 * b ^ 2 := by
  have ht : ∀ j, ‖finiteStrangTail H j‖ ≤ (M : ℝ) * b := by
    intro j
    calc
      _ ≤ ∑ k : Fin M, ‖if j < k then H k else 0‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin M, b := by
        apply Finset.sum_le_sum
        intro k _
        split_ifs
        · exact hH k
        · simpa using! hb
      _ = (M : ℝ) * b := by simp
  have hc : ∀ j, ‖pfComm (finiteStrangTail H j) (H j)‖ ≤ 2 * M * b ^ 2 := by
    intro j
    have h1 : ‖finiteStrangTail H j‖ * ‖H j‖ ≤ (M : ℝ) * b * b :=
      mul_le_mul (ht j) (hH j) (norm_nonneg _) (by positivity)
    calc
      _ ≤ ‖finiteStrangTail H j * H j‖ + ‖H j * finiteStrangTail H j‖ :=
        norm_sub_le _ _
      _ ≤ ‖finiteStrangTail H j‖ * ‖H j‖ + ‖H j‖ * ‖finiteStrangTail H j‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2 * M * b ^ 2 := by nlinarith
  calc
    _ ≤ ∑ _j : Fin M, 2 * (M : ℝ) * b ^ 2 := Finset.sum_le_sum fun j _ => hc j
    _ = _ := by simp; ring

/-- Selects `max 1 (ceil(T ^ 2 * M ^ 2 * b ^ 2 / ε))` first-order segments. -/
def sourceFirstSegments (M : ℕ) (b T ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (T ^ 2 * (M : ℝ) ^ 2 * b ^ 2 / ε))

/-- For Hermitian summands bounded by nonnegative `b` and `ε > 0`, the selected first-order
formula has positive segment count, length `M * r`, unitary interpretation, operator error
at most `ε` for `exp(iT∑H)`, and observable error at most `2 * ‖O‖ * ε`. [Wiesner1996] -/
theorem source_first_order_selected {D M : ℕ} (H : Fin M → Operator D)
    (b T ε : ℝ) (O : Operator D) (hb : 0 ≤ b) (hε : 0 < ε)
    (hH : ∀ j, (H j).IsHermitian) (hbound : ∀ j, ‖H j‖ ≤ b) :
    let r := sourceFirstSegments M b T ε
    0 < r ∧ (pfFamilyWord H (-T) r).length = M * r ∧
      pfFamily H (-T) r ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ‖pfFamily H (-T) r - NormedSpace.exp ((Complex.I * (T : ℂ)) • ∑ j, H j)‖ ≤ ε ∧
      ‖(pfFamily H (-T) r)ᴴ * O * pfFamily H (-T) r -
        (HamiltonianEvolution (∑ j, H j) (-T))ᴴ * O *
          HamiltonianEvolution (∑ j, H j) (-T)‖ ≤ 2 * ‖O‖ * ε := by
  let r := sourceFirstSegments M b T ε
  have hr : 0 < r := by dsimp [r, sourceFirstSegments]; omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmax : Nat.ceil (T ^ 2 * (M : ℝ) ^ 2 * b ^ 2 / ε) ≤ r :=
    le_max_right _ _
  have hceil : T ^ 2 * (M : ℝ) ^ 2 * b ^ 2 / ε ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hmax)
  have he := trotterFirstOrderTailSum D M r H (-T) hr hH
  have herr : ‖pfFamily H (-T) r - HamiltonianEvolution (∑ j, H j) (-T)‖ ≤ ε := by
    calc
      _ ≤ |(-T)| ^ 2 / (2 * (r : ℝ)) *
          ∑ j : Fin M, ‖pfComm (finiteStrangTail H j) (H j)‖ := he
      _ ≤ |(-T)| ^ 2 / (2 * (r : ℝ)) * (2 * M ^ 2 * b ^ 2) :=
        mul_le_mul_of_nonneg_left (bounded_tail_commutator_sum H b hb hbound) (by positivity)
      _ = T ^ 2 * (M : ℝ) ^ 2 * b ^ 2 / (r : ℝ) := by
        rw [sq_abs, neg_sq]
        field_simp
      _ ≤ ε := (div_le_iff₀ hrR).mpr (by
        have hnum := (div_le_iff₀ hε).mp hceil
        nlinarith [hnum])
  obtain ⟨hu, hlen, _, _⟩ := product_formula_actual_word_and_tariffs D M r H (-T)
    (fun _ => 0) hH
  have hsum : (∑ j, H j).IsHermitian := by
    change (∑ j : Fin M, H j)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => (hH j).eq
  refine ⟨hr, hlen, hu, ?_, ?_⟩
  · simpa only [source_positive_evolution] using! herr
  · exact (Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki_unitary_observable_error
      _ _ O (hamiltonianEvolution_unitary hsum (-T)) hu).trans
      (mul_le_mul_of_nonneg_left herr (by positivity))

/-- If `0 ≤ b ≤ B` and `ε > 0`, the selected segment count is at most `1 + ceil(T ^ 2 / ε) * (M
* B) ^ 2`. -/
theorem sourceFirstSegments_le (M B : ℕ) (b T ε : ℝ) (hb : 0 ≤ b)
    (hB : b ≤ (B : ℝ)) (hε : 0 < ε) :
    sourceFirstSegments M b T ε ≤ 1 + Nat.ceil (T ^ 2 / ε) * (M * B) ^ 2 := by
  have hTnonneg : 0 ≤ T ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  have hc : T ^ 2 / ε ≤ (Nat.ceil (T ^ 2 / ε) : ℝ) := Nat.le_ceil _
  have hb2 : b ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith
  have hx : T ^ 2 * (M : ℝ) ^ 2 * b ^ 2 / ε ≤
      ((1 + Nat.ceil (T ^ 2 / ε) * (M * B) ^ 2 : ℕ) : ℝ) := by
    calc
      _ = (T ^ 2 / ε) * (M : ℝ) ^ 2 * b ^ 2 := by ring
      _ ≤ (Nat.ceil (T ^ 2 / ε) : ℝ) * (M : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) hb2
          (by positivity) (by positivity)
      _ ≤ _ := by push_cast; nlinarith
  exact max_le (by omega) (Nat.ceil_le.mpr hx)

/-- Polynomial bounds on the term count and uniform norm give the displayed polynomial bound on
the total number of first-order factors. [Wiesner1996] -/
theorem source_first_order_polynomial_macro_count (N M d : ℕ) (b T ε : ℝ)
    (hb : 0 ≤ b) (hB : b ≤ ((N + 1 : ℕ) : ℝ) ^ d) (hε : 0 < ε)
    (hM : M ≤ (N + 1) ^ 2) :
    M * sourceFirstSegments M b T ε ≤
      (N + 1) ^ 2 * (1 + Nat.ceil (T ^ 2 / ε) * ((N + 1) ^ 2 * (N + 1) ^ d) ^ 2) := by
  have h := sourceFirstSegments_le M ((N + 1) ^ d) b T ε hb (by simpa using! hB) hε
  calc
    _ ≤ M * (1 + Nat.ceil (T ^ 2 / ε) * (M * (N + 1) ^ d) ^ 2) :=
      Nat.mul_le_mul_left M h
    _ ≤ _ := by gcongr

end Qatlib.Papers.ManyBodySim96.MainResults
