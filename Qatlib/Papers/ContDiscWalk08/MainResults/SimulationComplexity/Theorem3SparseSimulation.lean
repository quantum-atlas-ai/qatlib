/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs

/-!
# Sparse Hamiltonian data

The structure `SparseHamiltonian` packages a finite Hermitian matrix with a positive
row-sparsity bound and a nonnegative bound on entry norms. These data support the
sparse-simulation setting of Theorem 3 in [Childs2010]; the results here concern finite row
supports and the recorded bounds.

## Main statements

* `row_support_card_le_min`: each row support is bounded by both dimension and degree.
* `entryBound_nonneg'`: the entry bound is nonnegative.

## References

* [Childs, 2010][Childs2010]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

/-- Packages a Hermitian matrix with a positive degree bound, a nonnegative entry-norm bound,
and proofs of the corresponding sparsity and entry estimates. -/
structure SparseHamiltonian (N : ℕ) where

  H : Matrix (Fin N) (Fin N) ℂ

  isHermitian : H.IsHermitian

  degree : ℕ

  degree_pos : 1 ≤ degree

  entryBound : ℝ

  entryBound_nonneg : 0 ≤ entryBound

  row_sparse : ∀ j : Fin N, (Finset.univ.filter (fun k : Fin N => H j k ≠ 0)).card ≤ degree

  entry_bound : ∀ j k : Fin N, ‖H j k‖ ≤ entryBound

/-- The support of each row has cardinality at most the minimum of the dimension and the
recorded degree bound. -/
theorem row_support_card_le_min (N : ℕ) (S : SparseHamiltonian N) (j : Fin N) :
    (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0)).card ≤ min N S.degree :=
  le_min (by
    have h := Finset.card_le_univ (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0))
    simpa using h) (S.row_sparse j)

/-- The entry-norm bound recorded in `SparseHamiltonian` is nonnegative. -/
theorem entryBound_nonneg' (N : ℕ) (S : SparseHamiltonian N) : 0 ≤ S.entryBound :=
  S.entryBound_nonneg

/-- The support of each row has cardinality at most the matrix dimension. -/
theorem row_support_finite (N : ℕ) (S : SparseHamiltonian N) (j : Fin N) :
    (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0)).card ≤ N := by
  have h := Finset.card_le_univ (Finset.univ.filter (fun k : Fin N => S.H j k ≠ 0))
  simpa using h

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
