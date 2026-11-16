/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdversaryBounds.AdversarySets.Coarsening
public import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel

@[expose] public section


/-! # Actual adversary monotonicity and general-coordinate models

This preserves the useful closed Lemma10.3 proof and the general-coordinate
model declarations from the legacy Sections7/10. The realized supremum model
is explicit; no query algorithm, optimum attainment or composition equality is claimed.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped Classical ENNReal Matrix.Norms.L2Operator
open Qatlib.Papers.SpanProgReich09.MainResults

namespace Qatlib.Papers.SpanProgReich09.MainResults

/-- Lemma10.3 on the pinned paper model follows from genuine feasible-set inclusion. -/
theorem adversaryMono {X E F : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → BitString n) (f : X → E) (g : E → F) (s : Fin n → ℝ) :
    advNonneg input (fun x => g (f x)) s ≤ advNonneg input f s ∧
      advGeneral input (fun x => g (f x)) s ≤ advGeneral input f s := by
  exact Qatlib.Concepts.AdversaryBounds.AdversarySets.boundsCoarsen input f g s

end Qatlib.Papers.SpanProgReich09.MainResults
