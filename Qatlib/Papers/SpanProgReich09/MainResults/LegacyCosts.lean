/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel

@[expose] public section


/-! # The unlinked cost parameter in the legacy Theorem 10.2 target

The legacy target universally quantifies `Qf : ENNReal` without connecting it
to any evaluated algorithm. Its upper-bound conjunct is false at `Qf = top`:
every `ENNReal.ofReal` is finite. This refutes that legacy formal contract,
not the source paper's theorem about actual quantum query complexity.

Source: arXiv:0904.2759v1, Theorem 10.2; legacy source commit
474229502c7e142ea6e8f01955e16e7e6f0e6648, Section10/QueryAdversary.lean.
The full original header and the missing source bridge remain in the task registry.
-/

set_option autoImplicit false

noncomputable section
open scoped ENNReal
open Qatlib.Papers.SpanProgReich09.MainResults

namespace Qatlib.Papers.SpanProgReich09.MainResults

variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

/-- The unchanged upper-bound conjunct of the legacy target, kept as an
explicitly unproved predicate rather than exported as a theorem. -/
def oldUpper (input : X → BitString n) (f : X → Fin m) (Qf : ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Qf ≤ ENNReal.ofReal
      (C * (advGeneral input f (SpanProgram.uniformCost n)).toReal *
        (Real.log (advGeneral input f (SpanProgram.uniformCost n)).toReal /
          Real.log (Real.log (advGeneral input f (SpanProgram.uniformCost n)).toReal)))

/-- The arbitrary top cost is a rigorous counterexample to the legacy upper
bound for every source instance, independently of the adversary value. -/
theorem topCostFalse (input : X → BitString n) (f : X → Fin m) :
    ¬ oldUpper input f ⊤ := by
  rintro ⟨C, _, h⟩
  have heq := top_le_iff.mp h
  exact ENNReal.ofReal_ne_top heq

end Qatlib.Papers.SpanProgReich09.MainResults
