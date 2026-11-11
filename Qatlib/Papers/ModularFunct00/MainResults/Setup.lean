/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Basic data for modular-functor matrix calculations

This module introduces the matrix type `CM`, complex phases, bounded signed generator words,
braid relations, and a numerical notion of polylogarithmic overhead. These definitions provide
the common language for the modular-functor calculations associated with
[FreedmanLarsenWang2000].

`JonesSector` records dimensions, strand count, generator matrices, and a complex parameter for
a sector.

## Main statements

* `BraidWord`: Express a group element using a bounded list of signed generators.
* `BraidRelations`: Record distant commutation and adjacent braid relations.
* `PolyLogOverhead`: Bound an overhead by a power of a shifted binary logarithm.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Square complex matrices indexed by `Fin d`. -/
abbrev CM (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℂ

/-- The condition `z * star z = 1` for a complex scalar `z`. -/
def IsPhase (z : ℂ) : Prop := z * star z = 1

/-- The element `b` is the product of a list of generators or their inverses of length at most
`l`. -/
def BraidWord {G : Type*} [Group G] {m : ℕ} (σ : Fin m → G) (l : ℕ) (b : G) : Prop :=
  ∃ w : List (Fin m × Bool), w.length ≤ l ∧
    (w.map (fun p => if p.2 then σ p.1 else (σ p.1)⁻¹)).prod = b

/-- The chosen generators commute at index distance at least two and satisfy the three-factor
braid relation at adjacent indices. -/
def BraidRelations {G : Type*} [Group G] {m : ℕ} (σ : Fin m → G) : Prop :=
  (∀ i j : Fin m, (i : ℕ) + 2 ≤ (j : ℕ) ∨ (j : ℕ) + 2 ≤ (i : ℕ) → Commute (σ i) (σ j)) ∧
  (∀ i k : Fin m, (i : ℕ) + 1 = (k : ℕ) → σ i * σ k * σ i = σ k * σ i * σ k)

/-- The function is bounded at every `L` by some natural power of `Nat.log 2 (L + 1) + 1`. -/
def PolyLogOverhead (overhead : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, ∀ L : ℕ, overhead L ≤ (Nat.log 2 (L + 1) + 1) ^ d

/-- Data consisting of a dimension, a strand count, generator matrices indexed by `Fin (n - 1)`,
and a complex parameter. -/
structure JonesSector where

  d : ℕ

  n : ℕ

  M : Fin (n - 1) → CM d

  q : ℂ

end Qatlib.Papers.ModularFunct00.MainResults
