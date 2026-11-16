/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.MainResults.FullPauliPhysicalSource
public import Qatlib.Concepts.GibbsSource.SpectralGeom.CompressedObservableTransport
public import Qatlib.Concepts.GibbsSource.SpectralGeom.SchurBlockCertification

@[expose] public section


/-! The complete physical Pauli source consumes the finite spectral geometry.
This connects the original Hermitian Hamiltonian and its actual source Gram
to the full source supermatrix, with every complex operator coordinate retained.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.GibbsSource.SourceForms
open Qatlib.Concepts.GibbsSource.SpectralGeom
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GibbsSampl26.MainResults

/-- The actual physical plain Pauli parent is self-adjoint in Hilbert--Schmidt geometry. -/
theorem fullPauliPhysical_plain_selfAdjoint {n : ℕ} {H : Operator (fullPauliDim n)}
    (hH : H.IsHermitian) (β : ℝ) :
    SourceSelfAdjoint (fullPauliPhysicalParentOp hH β (fun _ => 1)) := by
  intro X Y
  simp only [fullPauliPhysicalParentOp_eq, LinearMap.sum_apply,
    hsInner_sum_left, hsInner_sum_right]
  apply Finset.sum_congr rfl
  intro P _
  apply sourceSelfAdjoint_parentGramFamOp (fourthRoot_isHermitian _) _ _ _ X Y
  intro a b
  simp only [fullWeight, mul_one]
  exact ckgSourceWeight_symm β _ _

/-- Every eigenvector in the complete source spectrum is an eigenoperator of the physical source. -/
theorem fullPauliPhysical_sourceEigenoperator {n : ℕ} {H : Operator (fullPauliDim n)}
    (hH : H.IsHermitian) (β : ℝ) (i : Fin (fullPauliDim n) × Fin (fullPauliDim n)) :
    let L := fullPauliPhysicalParentOp hH β (fun _ => 1)
    let hL := fullPauliPhysical_plain_selfAdjoint hH β
    L (sourceEigenoperator L hL i) =
      (sourceEigenvalues L hL i : ℂ) • sourceEigenoperator L hL i :=
  sourceEigenoperator_apply _ _ i

end Qatlib.Papers.GibbsSampl26.MainResults
