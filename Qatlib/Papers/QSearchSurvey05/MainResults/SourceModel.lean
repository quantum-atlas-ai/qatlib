/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchSurvey05.MainResults.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for Ambainis, *Quantum search algorithms*

Fixed source: A. Ambainis, *Quantum search algorithms*, arXiv:quant-ph/0504012v1
(3 April 2005), 9 pages.  All page numbers below refer to that PDF.

This module fixes the problem statements used by the paper-layer claims:

* global minimum of a function `Fin N → ℤ` (p. 5);
* local minimum of a Boolean function `(Fin n → Bool) → ℤ` (p. 5), where flipping any
  single coordinate does not decrease the value;
* the `d`-dimensional grid `Fin d → Fin n` with `N = n ^ d` cells (p. 7);
* existence of a marked cell in the unordered search problem (p. 1);
* triangle finding in a Boolean adjacency matrix (p. 8);
* Boolean matrix product `AB = C` modulo `2` (p. 9), encoded over `ZMod 2`.

These are the source's mathematical objects only.  The paper's algorithms are discussed
in the individual claim modules; this file adds no assumptions about them.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.QSearchSurvey05.MainResults

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- Paper p. 1, *Search*: an input is a Boolean string indexed by `Fin N`; a cell is
marked when its bit is `1`. -/
def HasMarked {N : ℕ} (x : Fin N → Bool) : Prop :=
  ∃ i : Fin N, x i = true

/-- Paper p. 5, *Global Minimum*: `i` is a global minimum of `f` when `f i ≤ f j` for
every `j`. -/
def IsGlobalMinimum {N : ℕ} (f : Fin N → ℤ) (i : Fin N) : Prop :=
  ∀ j : Fin N, f i ≤ f j

/-- Paper p. 8, *Triangle finding*: the graph with adjacency matrix `adj` contains a
triangle. -/
def HasTriangle {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop :=
  ∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    adj a b = true ∧ adj a c = true ∧ adj b c = true

end Qatlib.Papers.QSearchSurvey05.MainResults
