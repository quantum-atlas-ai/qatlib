/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanProgSt12.MainResults.SourceModel

@[expose] public section


/-! Structural fragment of Belovs and Reichardt, arXiv:1203.2603v1, Corollary 6.
This implication alone does not establish the quantum detection algorithm. -/

set_option autoImplicit false

namespace Qatlib.Papers.SpanProgSt12.MainResults

open Qatlib.Papers.SpanProgSt12.MainResults.SourceModel

/-- A subdivision of a claw is a subdivided star: its unique degree-`3` vertex is a
valid root, and every other vertex has degree at most `2`. -/
theorem isSubdividedClaw_isSubdividedStar {k : ℕ} {T : SimpleGraph (Fin k)}
    (hT : IsSubdividedClaw T) : IsSubdividedStar T := by
  obtain ⟨htree, r, -, hr⟩ := hT
  exact ⟨htree, r, hr⟩

end Qatlib.Papers.SpanProgSt12.MainResults
