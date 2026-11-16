/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TriangleFind14.MainResults.SourceTheorem11

@[expose] public section


/-! # Inhabitation check for the inherited triangle-finder record

The record requires every outcome to contain exactly three vertices even at
`n = 2`. A normalized finite outcome distribution is inhabited, making that
record impossible. This refutes its literal interface, not the source theorem,
whose small instances may return no triangle.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TriangleFind14.MainResults.TinyContract

open Qatlib.Papers.TriangleFind14.MainResults

/-- A normalized record cannot always output three distinct vertices on two vertices. -/
theorem noTwoFinder (A : TriangleFindingQuantumAlgorithm 2) : False := by
  obtain ⟨r⟩ := A.seedNonempty
  have hle := Finset.card_le_univ (A.output (⊥ : SimpleGraph (Fin 2)) r)
  rw [A.output_card] at hle
  norm_num at hle

end Qatlib.Papers.TriangleFind14.MainResults.TinyContract
