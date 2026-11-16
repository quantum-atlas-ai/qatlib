/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervSpeedup20.MainResults.Definitions

@[expose] public section


set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SupervSpeedup20.MainResults
open Finset
open scoped BigOperators

namespace FinLaw

variable {Ω : Type} [Fintype Ω]

/-- **Union bound (used in eq. (D39)).**  For a finite probability law,
`Pr[P ∨ Q] ≤ Pr[P] + Pr[Q]`. -/
theorem probOf_union_le (L : FinLaw Ω) (P Q : Ω → Prop) [DecidablePred P]
    [DecidablePred Q] :
    L.probOf (fun ω => P ω ∨ Q ω) ≤ L.probOf P + L.probOf Q := by
  have hnn : ∀ (R : Ω → Prop) [DecidablePred R] (ω : Ω),
      (0 : ℝ) ≤ (if R ω then 1 else 0) := by
    intro R _ ω
    split <;> norm_num
  have key : ∀ ω, (if (P ω ∨ Q ω) then (1 : ℝ) else 0) ≤
      (if P ω then 1 else 0) + (if Q ω then 1 else 0) := by
    intro ω
    by_cases hp : P ω
    · have h := hnn Q ω
      simp [hp]
      linarith
    · by_cases hq : Q ω
      · simp [hp, hq]
      · simp [hp, hq]
  calc L.probOf (fun ω => P ω ∨ Q ω)
      = L.expect (fun ω => if (P ω ∨ Q ω) then (1 : ℝ) else 0) :=
        (L.expect_indicator (fun ω => P ω ∨ Q ω)).symm
    _ ≤ L.expect (fun ω => (if P ω then (1 : ℝ) else 0) +
          (if Q ω then (1 : ℝ) else 0)) := L.expect_mono key
    _ = L.probOf P + L.probOf Q := by
        rw [L.expect_add, L.expect_indicator, L.expect_indicator]

end FinLaw

/-- **Union-bound arithmetic of eq. (D39).**  Two events of probability `0.99`
leave at least `2/3` for their intersection. -/
theorem two_thirds_le_union_bound :
    (2 / 3 : ℝ) ≤ 1 - 1 / 100 - 1 / 100 := by
  norm_num

end Qatlib.Papers.SupervSpeedup20.MainResults
