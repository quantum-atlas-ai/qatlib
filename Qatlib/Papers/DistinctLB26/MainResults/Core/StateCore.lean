/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# StateCore — finite ℓ² state space and coordinate masks

Fixed source: arXiv:2604.05133v1 (Belovs, *Tight Quantum Lower Bound for
k-Distinctness*), Section 3.2–3.3, pp. 8–11.

This file provides the elementary finite-dimensional state model used by the
paper-layer development: a state over a finite index type `ι` is an element of
`EuclideanSpace ℂ ι`, i.e. a finite complex vector with the ℓ² norm.  Masks
(`projMask`) are the coordinate projectors used for `Mρ`, `Πρ` and the
knowledge operators `Υ△`; they are orthogonal projections, and their squared
norms add over disjoint masks.  All statements are stated with the genuine
Hilbert-space norm `‖·‖` and squared norm `‖·‖ ^ 2`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Core

/-- A finite complex state space over the index type `ι`. -/
abbrev State (ι : Type*) : Type _ := EuclideanSpace ℂ ι

namespace State

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Extensionality for finite states, by coordinates. -/
theorem ext {x y : State ι} (h : ∀ i, x i = y i) : x = y := by
  apply WithLp.ofLp_injective
  funext i
  exact h i

omit [Fintype ι] in
/-- The `ofLp_apply` result for the DistinctLB26 paper model. -/
@[simp] theorem ofLp_apply (x : State ι) (i : ι) : x i = WithLp.ofLp x i := rfl

/-- Coordinate mask (orthogonal projector onto the coordinates satisfying `P`). -/
def projMask (P : ι → Prop) [DecidablePred P] (x : State ι) : State ι :=
  WithLp.toLp 2 (fun i => if P i then x i else 0)

omit [Fintype ι] in
/-- The `projMask_apply` result for the DistinctLB26 paper model. -/
@[simp] theorem projMask_apply (P : ι → Prop) [DecidablePred P] (x : State ι) (i : ι) :
    projMask P x i = if P i then x i else 0 := rfl

/-- Squared norm of a masked state as a sum over the selected coordinates. -/
theorem normSq_projMask (P : ι → Prop) [DecidablePred P] (x : State ι) :
    ‖projMask P x‖ ^ 2 = ∑ i, if P i then ‖x i‖ ^ 2 else 0 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P i <;> simp [projMask_apply, h]

/-- A coordinate mask never increases the norm. -/
theorem norm_projMask_le (P : ι → Prop) [DecidablePred P] (x : State ι) :
    ‖projMask P x‖ ≤ ‖x‖ := by
  have hsq : ‖projMask P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [normSq_projMask, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : P i <;> simp [h]
  calc ‖projMask P x‖ = Real.sqrt (‖projMask P x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- The `projMask_true` result for the DistinctLB26 paper model. -/
@[simp] theorem projMask_true (x : State ι) :
    projMask (fun _ => True) x = x := by
  apply State.ext
  intro i
  simp [projMask_apply]

/-- The `projMask_false` result for the DistinctLB26 paper model. -/
@[simp] theorem projMask_false (x : State ι) :
    projMask (fun _ => False) x = 0 := by
  apply State.ext
  intro i
  simp [projMask_apply]

/-- The `projMask_zero` result for the DistinctLB26 paper model. -/
@[simp] theorem projMask_zero (P : ι → Prop) [DecidablePred P] :
    projMask P (0 : State ι) = 0 := by
  apply State.ext
  intro i
  simp [projMask_apply]

/-- The `projMask_idem` result for the DistinctLB26 paper model. -/
@[simp] theorem projMask_idem (P : ι → Prop) [DecidablePred P] (x : State ι) :
    projMask P (projMask P x) = projMask P x := by
  apply State.ext
  intro i
  by_cases h : P i <;> simp [projMask_apply, h]

/-- Masks commute. -/
theorem projMask_comm (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (x : State ι) :
    projMask P (projMask Q x) = projMask Q (projMask P x) := by
  apply State.ext
  intro i
  by_cases hp : P i <;> by_cases hq : Q i <;> simp [projMask_apply, hp, hq]

/-- Squared norms add over disjoint masks: the two orthogonal parts of a state. -/
theorem normSq_projMask_add_of_disjoint (P Q : ι → Prop) [DecidablePred P]
    [DecidablePred Q] (hdisj : ∀ i, ¬ (P i ∧ Q i)) (x : State ι) :
    ‖projMask P x‖ ^ 2 + ‖projMask Q x‖ ^ 2 =
      ‖projMask (fun i => P i ∨ Q i) x‖ ^ 2 := by
  rw [normSq_projMask, normSq_projMask, normSq_projMask, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := hdisj i
  by_cases hp : P i <;> by_cases hq : Q i <;> simp [hp, hq] at h ⊢

/-- Masked states indexed by a partition of the mask predicate: their squared
norms add up to the squared norm of the total mask. -/
theorem sum_normSq_projMask_of_partition {κ : Type*} [Fintype κ]
    (P : κ → ι → Prop) [∀ k, DecidablePred (P k)]
    (hdisj : ∀ i k l, k ≠ l → ¬ (P k i ∧ P l i))
    (x : State ι) :
    ∑ k, ‖projMask (P k) x‖ ^ 2 = ‖projMask (fun i => ∃ k, P k i) x‖ ^ 2 := by
  have key : ∀ i, (∑ k, if P k i then ‖x i‖ ^ 2 else 0)
      = if (∃ k, P k i) then ‖x i‖ ^ 2 else 0 := by
    intro i
    by_cases hne : (∃ k, P k i)
    · obtain ⟨k, hk⟩ := hne
      have hsingle : (∑ l, (if P l i then ‖x i‖ ^ 2 else 0)) =
          (if P k i then ‖x i‖ ^ 2 else 0) :=
        Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun b _ hb => by
          have hPb : ¬ P b i := fun h => hdisj i b k hb ⟨h, hk⟩
          simp [hPb])
      rw [hsingle, if_pos hk, if_pos ⟨k, hk⟩]
    · have h0 : ∀ k, ¬ P k i := fun k hk => hne ⟨k, hk⟩
      simp [h0]
  simp_rw [normSq_projMask]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact key i

end State

end Qatlib.Papers.DistinctLB26.MainResults.Core
