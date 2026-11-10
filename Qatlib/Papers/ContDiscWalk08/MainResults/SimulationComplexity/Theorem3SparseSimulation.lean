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

structure SparseHamiltonian (N : ℕ) where

  H : Matrix (Fin N) (Fin N) ℂ

  isHermitian : H.IsHermitian

  degree : ℕ

  degree_pos : 1 ≤ degree

  entryBound : ℝ

  entryBound_nonneg : 0 ≤ entryBound

  row_sparse : ∀ j : Fin N, (Finset.univ.filter (fun k : Fin N => H j k ≠ 0)).card ≤ degree

  entry_bound : ∀ j k : Fin N, ‖H j k‖ ≤ entryBound

theorem row_support_card_le_min (N : ℕ) (S : SparseHamiltonian N) (j : Fin N) :
    (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0)).card ≤ min N S.degree :=
  le_min (by
    have h := Finset.card_le_univ (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0))
    simpa using h) (S.row_sparse j)

theorem entryBound_nonneg' (N : ℕ) (S : SparseHamiltonian N) : 0 ≤ S.entryBound :=
  S.entryBound_nonneg

theorem row_support_finite (N : ℕ) (S : SparseHamiltonian N) (j : Fin N) :
    (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0)).card ≤ N := by
  have h := Finset.card_le_univ (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0))
  simpa using h

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
