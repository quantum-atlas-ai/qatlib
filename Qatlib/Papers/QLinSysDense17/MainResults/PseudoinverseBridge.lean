/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PseudoInverse

set_option backward.isDefEq.respectTransparency false

/-!
# QLinSysDense17 — bridging `|A⁻¹b⟩` to the library pseudoinverse

Fixed source: Wossnig–Zhao–Prakash, *A quantum linear system algorithm for
dense matrices*, arXiv:1704.06174v2 (3 May 2017).

Theorem 3 (p. 3) takes a Hermitian `A ∈ ℝ^{n×n}` with spectral decomposition
`A = ∑ᵢ λᵢ uᵢuᵢ†` and promises a state within `ε` of `|A⁻¹b⟩`.  The library
represents exactly such a Hermitian matrix as `continuousHHLMatrix eig V =
V·diag(eig)·Vᴴ` with `V` unitary, and provides the pseudoinverse semantics of
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse`, reused here with FQN
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse.singular_hermitian_pseudoinverse_and_least_squares`.

This module states the two bridges the paper's output assertion needs:

* for a nonsingular Hermitian `A` (all eigenvalues nonzero), the paper's `A⁻¹`
  is the library pseudoinverse and `A·A⁺ = 1`;
* for a singular Hermitian `A` the same pseudoinverse returns the Euclidean
  least-squares solution, which is what the paper's filter map converges to
  when part of `b` lies in the ill-conditioned subspace.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLinSysDense17.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

/-- Bridge for **claim c001**, output-state semantics.  A nonsingular Hermitian
`A = V·diag(eig)·Vᴴ` (all `eig i ≠ 0`, `V` unitary) stored in the data
structure of Lemma 1: the paper's inverse `A⁻¹` coincides with the library
pseudoinverse, in the sense `A · A⁺ = 1`.  The proof reuses the frozen result
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse.singular_hermitian_pseudoinverse_and_least_squares`:
it gives `A·A⁺ = spectralSupport eig V`, and with no zero eigenvalue the
spectral support is the identity. -/
theorem continuousHHLMatrix_mul_pseudoinverse_eq_one
    {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hne : ∀ i, eig i ≠ 0) :
    continuousHHLMatrix eig V * matrixPseudoinverse (continuousHHLMatrix eig V) = 1 := by
  have hprod :=
    (singular_hermitian_pseudoinverse_and_least_squares D eig V hV).2.1
  rw [hprod]
  have hdiag : (fun i : Fin D => if eig i = 0 then (0 : ℂ) else 1) = fun _ => 1 := by
    funext i
    simp [hne i]
  unfold spectralSupport
  rw [hdiag]
  simp only [Matrix.diagonal_one, Matrix.mul_one]
  have hv : V * Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hV)
  exact hv

/-- Bridge for **claim c001**, least-squares semantics on the singular
spectrum.  For any Hermitian `A = V·diag(eig)·Vᴴ` and any right-hand side `b`,
the library pseudoinverse applied to `b` is the Euclidean least-squares
solution — the vector the paper's filter map approximates when `b` has
components in the ill-conditioned subspace.  Proof: the frozen
`singular_hermitian_pseudoinverse_and_least_squares`, third conjunct. -/
theorem pseudoinverse_apply_is_leastSquares
    {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (b : QState (Fin D)) :
    IsEuclideanLeastSquares (continuousHHLMatrix eig V) b
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b) :=
  (singular_hermitian_pseudoinverse_and_least_squares D eig V hV).2.2 b

end Qatlib.Papers.QLinSysDense17.MainResults
