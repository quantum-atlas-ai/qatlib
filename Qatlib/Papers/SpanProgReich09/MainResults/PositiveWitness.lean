/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel

@[expose] public section


/-! # The actual positive-witness characterization

This preserves the closed positive direction of the old Lemma2.2 wrapper.
It is not the separate unproved normalized projection-range formula.
-/

set_option autoImplicit false

noncomputable section
open scoped Classical
open Qatlib.Papers.SpanProgReich09.MainResults

namespace Qatlib.Papers.SpanProgReich09.MainResults

/-- A program accepts exactly when an available combination is its real target. -/
theorem positiveWitness {n : ℕ} (P : SpanProgram n) (x : BitString n) :
    P.fP x = true ↔ ∃ w : Fin P.idx → ℂ, P.combo x w = P.target := by
  unfold SpanProgram.fP
  by_cases h : ∃ w : Fin P.idx → ℂ, P.combo x w = P.target
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]
    exact ⟨fun hbad => False.elim (Bool.false_eq_true.mp hbad), fun hw => absurd hw h⟩

end Qatlib.Papers.SpanProgReich09.MainResults
