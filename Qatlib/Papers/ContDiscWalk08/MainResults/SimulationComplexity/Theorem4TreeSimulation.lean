/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

def columnTwoNorm {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) : ℝ :=
  Real.sqrt (∑ k : Fin N, ‖H k j‖ ^ 2)

def IsRootedTreeSupport {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (parent : Fin N → Option (Fin N)) : Prop :=
  (∃ r : Fin N, parent r = none) ∧
  (∀ j k : Fin N, H j k ≠ 0 → parent j = some k ∨ parent k = some j) ∧
  (∀ j k : Fin N, parent j = some k → H j k ≠ 0)

structure TreeHamiltonian (N : ℕ) where

  H : Matrix (Fin N) (Fin N) ℂ

  isHermitian : H.IsHermitian

  parent : Fin N → Option (Fin N)

  support_tree : IsRootedTreeSupport H parent

  hParam : ℝ

  column_bound : ∀ j : Fin N, columnTwoNorm H j ≤ hParam

  column_attained : ∃ j : Fin N, columnTwoNorm H j = hParam

theorem columnTwoNorm_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    0 ≤ columnTwoNorm H j :=
  Real.sqrt_nonneg _

theorem columnTwoNorm_le_hParam {N : ℕ} (T : TreeHamiltonian N) (j : Fin N) :
    columnTwoNorm T.H j ≤ T.hParam :=
  T.column_bound j

theorem hParam_nonneg {N : ℕ} (T : TreeHamiltonian N) : 0 ≤ T.hParam := by
  obtain ⟨j, hj⟩ := T.column_attained
  rw [← hj]
  exact columnTwoNorm_nonneg T.H j

theorem tree_has_root {N : ℕ} (T : TreeHamiltonian N) :
    ∃ r : Fin N, T.parent r = none :=
  T.support_tree.1

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
