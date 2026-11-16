/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolMatMult11.MainResults.ThresholdReduction

@[expose] public section


/-! # Scope of the legacy lower-bound contract

The legacy cost fields do not denote executions. These diagnostics concern
that interface, not the quantum query lower bound in the source paper.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolMatMult11.MainResults.CostContract
open Qatlib.Papers.BoolMatMult11.MainResults.ThresholdReduction

/-- The complete legacy external premise admits only a zero lower bound. -/
theorem premiseZero {n ℓ L : ℕ}
    (hThr : ∀ (thr : (Fin n → Fin n → Bool) → Bool)
      (q : (Fin n → Fin n → Bool) → ℕ),
      (∀ f, thr f = thresholdAnswer ℓ f) → ∃ f, L ≤ q f) : L = 0 := by
  obtain ⟨f, hf⟩ := hThr (thresholdAnswer ℓ) (fun _ => 0) (fun _ => rfl)
  exact Nat.eq_zero_of_le_zero hf

/-- The vacuous zero case is sufficient for the entire legacy premise. -/
theorem premiseIff {n ℓ L : ℕ} :
    (∀ (thr : (Fin n → Fin n → Bool) → Bool)
      (q : (Fin n → Fin n → Bool) → ℕ),
      (∀ f, thr f = thresholdAnswer ℓ f) → ∃ f, L ≤ q f) ↔ L = 0 := by
  constructor
  · exact premiseZero
  · intro h thr q _
    subst L
    exact ⟨fun _ _ => false, Nat.zero_le _⟩

/-- Direct specification evaluation with independent zero cost fields. -/
def freeSolver (n : ℕ) : BMMSolver n where
  solve := bmmEntry
  queriesA := fun _ _ => 0
  queriesB := fun _ _ => 0

/-- The old correctness predicate cannot exclude specification evaluation. -/
theorem freeCorrect (n : ℕ) : (freeSolver n).Correct := by
  intro A B i j
  rfl

/-- Every input has zero cost in this correct legacy record. -/
theorem freeCost {n : ℕ} (A B : Fin n → Fin n → Bool) :
    (freeSolver n).queriesA A B + (freeSolver n).queriesB A B = 0 := rfl

/-- The defect persists on a nonempty instance whose product is actually true. -/
theorem positiveExample :
    (freeSolver 1).solve (identity 1) (fun _ _ => true) 0 0 = true ∧
    (freeSolver 1).queriesB (identity 1) (fun _ _ => true) = 0 := by
  constructor
  · change bmmEntry (identity 1) (fun _ _ => true) 0 0 = true
    exact identity_bmmEntry (fun _ _ => true) 0 0
  · rfl

end Qatlib.Papers.BoolMatMult11.MainResults.CostContract
