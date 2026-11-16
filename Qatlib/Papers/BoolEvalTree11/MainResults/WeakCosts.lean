/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.Models

@[expose] public section


/-! # Claim 2.2: weak-input costs vanish on actual witnesses

Both literal row/column witness sets impose zero coordinates at weak labels.
Changing just their costs therefore preserves each cost image and its infimum.
This algebraic claim does not require the missing tree-to-query bridge.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.WeakCosts
open Models
open DirectSpanProgram

/-- The witness set selected by the Boolean output, without changing its constraints. -/
def witnesses {c : ℕ} (sp : DirectSpanProgram c) (x : Fin c → Bool) (r : Bool) :
    Set (Fin c → ℂ) := if r then sp.trueWitnessSet x else sp.falseWitnessSet x

/-- Every actual witness has zero coordinate at a weak input. -/
theorem weakZero {c : ℕ} (sp : DirectSpanProgram c) (x : Fin c → Bool) (r : Bool)
    (w : Fin c → ℂ) (hw : w ∈ witnesses sp x r) (j : Fin c)
    (hj : sp.chi x j ≠ r) : w j = 0 := by
  cases r with
  | false =>
    obtain ⟨α,_,_,hz⟩ := hw
    exact hz j (by cases h : sp.chi x j <;> simp_all)
  | true =>
    exact hw.2.2 j (by cases h : sp.chi x j <;> simp_all)

/-- Costs agreeing on strong labels give the same cost for each admissible witness. -/
theorem costEqual {c : ℕ} (sp : DirectSpanProgram c) (x : Fin c → Bool) (r : Bool)
    (s t : Fin c → ℝ) (h : ∀ j, sp.chi x j = r → s j = t j)
    (w : Fin c → ℂ) (hw : w ∈ witnesses sp x r) :
    witnessCost s w = witnessCost t w := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : sp.chi x j = r
  · rw [h j hj]
  · rw [weakZero sp x r w hw j hj]
    simp

/-- The complete weighted witness-size infimum is independent of weak-input costs. -/
theorem sizeEqual {c : ℕ} (sp : DirectSpanProgram c) (x : Fin c → Bool) (r : Bool)
    (s t : Fin c → ℝ) (h : ∀ j, sp.chi x j = r → s j = t j) :
    sInf (witnessCost s '' witnesses sp x r) =
      sInf (witnessCost t '' witnesses sp x r) := by
  congr 1
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,(costEqual sp x r s t h w hw).symm⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,costEqual sp x r s t h w hw⟩

end Qatlib.Papers.BoolEvalTree11.MainResults.WeakCosts
