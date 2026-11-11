/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.Basic

/-!
# Vacuum-compressed coefficient bound (Lemma 3.2)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 3.2, page 14.

For a finite set `F` of active occurrence labels, the Möbius coefficient
`s_F` of the activation comparison is a product of one local factor per label,
`Δ_F M = ∏_{b∈F} A_b`, where `A_b` is the compressed local transition at label
`b`.  Under the weight bound `hλ_b ≤ 1` each factor satisfies `‖A_b‖ ≤ ω_b` with
`ω_b = 64 h λ_b`.  The operator norm is submultiplicative, so

`‖Δ_F M‖ ≤ ∏_{b∈F} ω_b`.

Because operator composition is not commutative, we record the product in the
chronological order of the active occurrences (a list), which is exactly how the
circuit multiplies its factors.  The statement is uniform in the reference: the
operator norm is the reference-extended norm and the factors act trivially on
the reference.
-/

namespace Qatlib.Papers.ShallowLind26.ShallowSim.CompressedCoefficient

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The operator norm of an ordered product is at most the product of the
norms. -/
theorem norm_list_prod_le (l : List (E →L[ℂ] E)) :
    ‖l.prod‖ ≤ (l.map (fun A => ‖A‖)).prod := by
  induction l with
  | nil =>
      change ‖ContinuousLinearMap.id ℂ E‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | cons A l ih =>
      simp only [List.prod_cons, List.map_cons]
      calc ‖A * l.prod‖ ≤ ‖A‖ * ‖l.prod‖ := norm_mul_le _ _
        _ ≤ ‖A‖ * (l.map (fun A => ‖A‖)).prod :=
            mul_le_mul_of_nonneg_left ih (norm_nonneg _)

/-- **Lemma 3.2, vacuum-compressed coefficient bound.**  If every local factor
on the chronological list is bounded by its weight, the compressed coefficient
is bounded by the product of the weights. -/
theorem vacuum_coefficient_bound_list {l : List (E →L[ℂ] E)} {w : List ℝ}
    (h : List.Forall₂ (fun A x => ‖A‖ ≤ x) l w) :
    ‖l.prod‖ ≤ w.prod := by
  induction h with
  | nil =>
      change ‖ContinuousLinearMap.id ℂ E‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | cons hA htail ih =>
      rename_i A x l w
      simp only [List.prod_cons]
      have hx0 : 0 ≤ x := le_trans (norm_nonneg A) hA
      calc ‖A * l.prod‖ ≤ ‖A‖ * ‖l.prod‖ := norm_mul_le A l.prod
        _ ≤ x * w.prod := mul_le_mul hA ih (norm_nonneg l.prod) hx0


/-- A real list with all entries between `0` and `w` has product at most
`w` raised to the list length. -/
theorem list_prod_le_pow {l : List ℝ} {w : ℝ}
    (h : ∀ x ∈ l, x ≤ w) (h0 : ∀ x ∈ l, 0 ≤ x) :
    l.prod ≤ w ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.prod_cons, List.length_cons, pow_succ]
      have hx : x ≤ w := h x (by simp)
      have hx0 : 0 ≤ x := h0 x (by simp)
      have hw0 : 0 ≤ w := le_trans hx0 hx
      have hprod0 : 0 ≤ l.prod := List.prod_nonneg (fun y hy => h0 y (by simp [hy]))
      calc x * l.prod ≤ w * w ^ l.length :=
            mul_le_mul hx (ih (fun y hy => h y (by simp [hy]))
              (fun y hy => h0 y (by simp [hy]))) hprod0 hw0
        _ = w ^ l.length * w := by ring

/-- The coefficient bound with a constant weight: a list of `n` factors each of
norm at most `w` has product norm at most `w ^ n`. -/
theorem vacuum_coefficient_bound_const (l : List (E →L[ℂ] E)) (w : ℝ) (_hw : 0 ≤ w)
    (h : ∀ A ∈ l, ‖A‖ ≤ w) :
    ‖l.prod‖ ≤ w ^ l.length := by
  have hmap : ∀ x ∈ l.map (fun A => ‖A‖), x ≤ w := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hx
    exact h A hA
  have h0 : ∀ x ∈ l.map (fun A => ‖A‖), 0 ≤ x := by
    intro x hx
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  calc ‖l.prod‖ ≤ (l.map (fun A => ‖A‖)).prod := norm_list_prod_le l
    _ ≤ w ^ l.length := by
        rw [← List.length_map]
        exact list_prod_le_pow hmap h0

end Qatlib.Papers.ShallowLind26.ShallowSim.CompressedCoefficient
