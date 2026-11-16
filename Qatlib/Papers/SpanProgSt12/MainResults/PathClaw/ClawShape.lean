/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanProgSt12.MainResults.SourceModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Subdivided-claw shape

Extracted proved structural lemma from the incomplete SourceCorollary6 candidate.
Source: arXiv:1203.2603v1, Section 4.1, p. 5. A subdivided claw is a tree
whose root has degree three and whose other vertices have degree at most two.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgSt12.MainResults.PathClaw

open Qatlib.Papers.SpanProgSt12.MainResults.SourceModel

/-- A subdivision of a claw is a subdivided star: its unique degree-`3` vertex is a
valid root, and every other vertex has degree at most `2`. -/
theorem isSubdividedClaw_isSubdividedStar {k : ℕ} {T : SimpleGraph (Fin k)}
    (hT : IsSubdividedClaw T) : IsSubdividedStar T := by
  obtain ⟨htree, r, -, hr⟩ := hT
  exact ⟨htree, r, hr⟩

end Qatlib.Papers.SpanProgSt12.MainResults.PathClaw
