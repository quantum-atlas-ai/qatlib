/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs

/-!
# Parent support and column norms for tree simulation

The definitions `columnTwoNorm` and `IsRootedTreeSupport` record column Euclidean norms and a
parent-based support condition for the tree-simulation setting of [Childs2010]. The structure
`TreeHamiltonian` adds Hermiticity and an attained uniform column-norm bound; the support
predicate requires a root and edge compatibility.

## Main statements

* `columnTwoNorm_le_hParam`: the recorded parameter bounds every column norm.
* `hParam_nonneg`: the attained bound is nonnegative.
* `tree_has_root`: a vertex with no parent exists.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

/-- Defines the Euclidean norm of a matrix column as the square root of the sum of squared entry
norms. -/
def columnTwoNorm {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) : ℝ :=
  Real.sqrt (∑ k : Fin N, ‖H k j‖ ^ 2)

/-- Requires a vertex with no parent, every nonzero matrix entry to join a parent and child, and
each parent relation to give a nonzero entry. -/
def IsRootedTreeSupport {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (parent : Fin N → Option (Fin N)) : Prop :=
  (∃ r : Fin N, parent r = none) ∧
  (∀ j k : Fin N, H j k ≠ 0 → parent j = some k ∨ parent k = some j) ∧
  (∀ j k : Fin N, parent j = some k → H j k ≠ 0)

/-- Packages a Hermitian matrix, a parent map satisfying `IsRootedTreeSupport`, and an attained
uniform upper bound on column Euclidean norms. -/
structure TreeHamiltonian (N : ℕ) where

  H : Matrix (Fin N) (Fin N) ℂ

  isHermitian : H.IsHermitian

  parent : Fin N → Option (Fin N)

  support_tree : IsRootedTreeSupport H parent

  hParam : ℝ

  column_bound : ∀ j : Fin N, columnTwoNorm H j ≤ hParam

  column_attained : ∃ j : Fin N, columnTwoNorm H j = hParam

/-- The Euclidean norm of every matrix column is nonnegative. -/
theorem columnTwoNorm_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    0 ≤ columnTwoNorm H j :=
  Real.sqrt_nonneg _

/-- Each column Euclidean norm of `T.H` is at most the recorded parameter `T.hParam`. -/
theorem columnTwoNorm_le_hParam {N : ℕ} (T : TreeHamiltonian N) (j : Fin N) :
    columnTwoNorm T.H j ≤ T.hParam :=
  T.column_bound j

/-- The attained column-norm bound `T.hParam` is nonnegative. -/
theorem hParam_nonneg {N : ℕ} (T : TreeHamiltonian N) : 0 ≤ T.hParam := by
  obtain ⟨j, hj⟩ := T.column_attained
  rw [← hj]
  exact columnTwoNorm_nonneg T.H j

/-- A `TreeHamiltonian` has a vertex whose parent is `none`. -/
theorem tree_has_root {N : ℕ} (T : TreeHamiltonian N) :
    ∃ r : Fin N, T.parent r = none :=
  T.support_tree.1

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
