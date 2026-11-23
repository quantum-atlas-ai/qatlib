/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.FixedCorrect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A nonzero anti-concentrated hidden-input subspace

The constant-vector subspace is anti-concentrated with respect to guessing a
uniformly hidden label, with the sharp squared factor `1 / card Y`.
This gives a nonzero instance of the corrected Definitions 3.8--3.9, and the
measurement bound holds for every work-register unitary and response map.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.FixedCorrect

variable {Y A : Type*} [Fintype Y] [Fintype A] [DecidableEq Y]

/-- The constant hidden-label vector. -/
def flat : Vec Y := WithLp.toLp 2 (fun _ => 1)

/-- The constant-vector subspace of the hidden register. -/
def flatSpace : Submodule ℂ (Vec Y) := Submodule.span ℂ ({flat} : Set (Vec Y))

omit [DecidableEq Y] in
/-- The squared norm of a constant hidden-label vector counts the actual labels. -/
theorem flat_squares (c : ℂ) : ‖c • (flat : Vec Y)‖ ^ 2 = Fintype.card Y * ‖c‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [flat, PiLp.smul_apply]

/-- A singleton correctness projector selects exactly one constant coordinate. -/
theorem project_flat (r : Y) (c : ℂ) :
    ‖project (fun r y : Y => y = r) r (c • flat)‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ y : Y, ‖(if y = r then c * 1 else 0 : ℂ)‖ ^ 2) = ‖c‖ ^ 2
  calc
    (∑ y : Y, ‖(if y = r then c * 1 else 0 : ℂ)‖ ^ 2) =
        ∑ y : Y, if y = r then ‖c‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = ‖c‖ ^ 2 := by simp

/-- The corrected subspace definition admits a sharp, nonzero uniform-label example. -/
theorem flat_anti [Nonempty Y] :
    AntiConc (fun r y : Y => y = r) (Real.sqrt (1 / (Fintype.card Y : ℝ)))
      (flatSpace : Submodule ℂ (Vec Y)) := by
  intro r v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hd : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [project_flat, flat_squares, Real.sq_sqrt (by positivity)]
  field_simp
  exact le_rfl

omit [Fintype Y] [DecidableEq Y] in
/-- The example subspace contains an explicitly nonzero vector. -/
theorem flat_nonzero [Nonempty Y] : (flat : Vec Y) ≠ 0 := by
  intro h
  let y : Y := Classical.choice inferInstance
  have hy := congrArg (fun v : Vec Y => v y) h
  change (1 : ℂ) = 0 at hy
  exact one_ne_zero hy

/-- No actual local measurement can guess a uniform hidden label with probability above `1/card`. -/
theorem uninformed_bound [Nonempty Y] (ψ : Vec (Y × A))
    (hψ : Strong (flatSpace : Submodule ℂ (Vec Y)) ψ) (hnorm : ‖ψ‖ = 1)
    (answer : A → Y) (U : Vec A ≃ₗᵢ[ℂ] Vec A) :
    successProb (fun r y : Y => y = r) answer U ψ ≤ 1 / (Fintype.card Y : ℝ) := by
  have h := success_bound (fun r y : Y => y = r)
    (Real.sqrt (1 / (Fintype.card Y : ℝ))) flatSpace flat_anti ψ hψ answer U
  simpa only [hnorm, one_pow, mul_one, Real.sq_sqrt (show (0 : ℝ) ≤
    1 / (Fintype.card Y : ℝ) by positivity)] using h

end Qatlib.Papers.DistinctLB26.MainResults.FixedCorrect
