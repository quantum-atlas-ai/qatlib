/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgForm09.MainResults.Model.Formula

set_option backward.isDefEq.respectTransparency false

/-!
# Basic proven facts about the formula / adversary model of
Reichardt, *Span-program-based quantum algorithm for evaluating unbalanced formulas*
(arXiv:0907.1622v1)

This module collects elementary theorems about the definitions in
`Model/Formula.lean` that hold for *every* formula, independent of the paper's
still-unformalised span-program construction. They are the proven part of the
paper's model: size/leaf-count bookkeeping and nonnegativity of the general
adversary bound `Adv±` of Eq. (2.1) (inherited from the library's
`sourceAdversary`).

Nothing here reproves a paper result; the paper statements that consume these
facts are documented in the PR description because their proofs are not yet
mechanised (the `Source*` scaffolding of the earlier pass was removed because it
contained only `sorry` and therefore violated the repository's no-`sorry` rule).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgForm09.MainResults

open Matrix
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open scoped Classical BigOperators ENNReal

namespace Formula

variable {I : Type} {G : GateSet}

/-- Every formula has positive `size` (`at least one` node). -/
theorem size_pos : ∀ φ : Formula I G, 0 < φ.size
  | .leaf _ => by simp
  | .node k g ch => by
      rw [size_node]
      omega

/-- `leafCount` at a leaf is one, by the defining equation. -/
theorem leafCount_leaf (i : I) : leafCount (leaf (G := G) i) = 1 := rfl

/-- `leafCount` at an internal node is the sum over its children, by the defining
equation. -/
theorem leafCount_node (k : ℕ) (g : G.gate k) (ch : Fin k → Formula I G) :
    leafCount (node k g ch) = ∑ j : Fin k, leafCount (ch j) := rfl

end Formula

variable {I : Type} [Fintype I] [DecidableEq I] {G : GateSet}

/-- `Adv±(φ)` is nonnegative: it is the real projection of the library's
extended-nonnegative-real adversary value `sourceAdversary` (Eq. (2.1)). -/
theorem advPlus_nonneg (φ : Formula I G) : 0 ≤ advPlus φ := by
  unfold advPlus
  exact ENNReal.toReal_nonneg

end Qatlib.Papers.SpanProgForm09.MainResults
