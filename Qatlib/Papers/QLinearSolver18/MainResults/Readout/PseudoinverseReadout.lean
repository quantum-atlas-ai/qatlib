/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PseudoInverse

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver18.MainResults.Readout.PseudoinverseReadout

Readout-target bridge for QLinearSolver18, fixed arXiv:1805.10549v2
(29 Nov 2018), Subasi--Somma--Orsucci.

Both algorithms of the paper output the normalized solution
`|x> = A^{-1} |b> / ||A^{-1} |b>||` (Eq. (1), p. 2) of the quantum linear
system `A |x> = |b>`, under the standing assumption that `A` is Hermitian and
invertible (and `|b>` has unit norm).  Claims `c001`/`c002` bind the concept
`QlsReadoutSpec.PseudoInverse`, whose Frozen formalisation is
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse.singular_hermitian_pseudoinverse_and_least_squares`
(spectral decomposition of the pseudoinverse, `A A^+ = spectralSupport A`,
and the minimum-norm Euclidean least-squares property).

The theorems below only restate, at the paper layer and for a spectrally
represented Hermitian `A = V diag(eig) V^H` with all eigenvalues nonzero, that
this canonical object is exactly the paper's readout target:

* `pseudoinverse_eq_inv_of_ne_zero`: `A^+ = A^{-1}` (so `A^+ b = A^{-1} b`);
* `pseudoinverse_mulVec_solves`: `A (A^+ b) = b` (Eq. (1) target solves the QLSP);
* `pseudoinverse_solution_ne_zero`: `b != 0 -> A^+ b != 0` (the target is a
  well-defined non-null state, so Eq. (1)'s normalization is legitimate);
* `pseudoinverse_mulVec_leastSquares`: the usual least-squares specification,
  inherited from the Frozen result.

No new quantum-mechanical content is introduced here; the proofs are direct
consequences of the Frozen theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver18.MainResults.Readout.PseudoinverseReadout

open Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Foundations.PureStateMath
open Matrix

/-- With all eigenvalues nonzero the spectral support of the singular Hermitian
form `A = V diag(eig) V^H` is the identity, i.e. `A` is invertible. -/
theorem spectralSupport_eq_one_of_ne_zero {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hne : ∀ i, eig i ≠ 0) :
    spectralSupport eig V = 1 := by
  unfold spectralSupport
  have hd : (fun i => if eig i = 0 then (0 : ℂ) else 1) = fun _ => 1 := by
    funext i
    rw [if_neg (hne i)]
  rw [hd, Matrix.diagonal_one, Matrix.mul_one]
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hV

/-- Paper Eq. (1), p. 2: on the invertible Hermitian input class the canonical
pseudoinverse readout is the ordinary inverse, `A^+ = A^{-1}`, so the algorithm
target `A^{-1}|b>` is the Frozen least-squares output `A^+ |b>`. -/
theorem pseudoinverse_eq_inv_of_ne_zero {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hne : ∀ i, eig i ≠ 0) :
    matrixPseudoinverse (continuousHHLMatrix eig V) = (continuousHHLMatrix eig V)⁻¹ := by
  obtain ⟨hinv, hAA, -⟩ :=
    singular_hermitian_pseudoinverse_and_least_squares D eig V hV
  have h : continuousHHLMatrix eig V *
      (V * Matrix.diagonal (fun i => ((eig i : ℂ)⁻¹)) * Vᴴ) = 1 := by
    rw [← hinv, hAA, spectralSupport_eq_one_of_ne_zero eig V hV hne]
  rw [hinv]
  exact (Matrix.inv_eq_right_inv h).symm

/-- Paper Eq. (1), p. 2 (solution property): the readout vector `A^+ |b>` is an
exact solution of the linear system `A x = b` for every right-hand side `b`
(invertible Hermitian input class). -/
theorem pseudoinverse_mulVec_solves {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hne : ∀ i, eig i ≠ 0)
    (b : QState (Fin D)) :
    continuousHHLMatrix eig V *ᵥ
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b) = b := by
  obtain ⟨-, hAA, -⟩ :=
    singular_hermitian_pseudoinverse_and_least_squares D eig V hV
  rw [Matrix.mulVec_mulVec, hAA, spectralSupport_eq_one_of_ne_zero eig V hV hne,
    Matrix.one_mulVec]

/-- Paper Eq. (1), p. 2 (normalization premise): for a nonzero right-hand side
the readout vector is nonzero, so `A^{-1}|b> / ||A^{-1}|b>||` is well defined. -/
theorem pseudoinverse_solution_ne_zero {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hne : ∀ i, eig i ≠ 0)
    {b : QState (Fin D)} (hb : b ≠ 0) :
    matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b ≠ 0 := by
  intro hzero
  apply hb
  rw [← pseudoinverse_mulVec_solves eig V hV hne b, hzero, Matrix.mulVec_zero]

/-- Paper Eqs. (1)-(2), p. 2 (least-squares readout spec): the readout vector
`A^+ |b>` is the minimum Euclidean-norm least-squares solution, inherited
verbatim from the Frozen concept `QlsReadoutSpec.PseudoInverse`. -/
theorem pseudoinverse_mulVec_leastSquares {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (b : QState (Fin D)) :
    IsEuclideanLeastSquares (continuousHHLMatrix eig V) b
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b) := by
  obtain ⟨-, -, hls⟩ :=
    singular_hermitian_pseudoinverse_and_least_squares D eig V hV
  exact hls b

/-- Paper Eq. (1), p. 2, assembled: for a Hermitian operator given by its
spectral decomposition with all eigenvalues nonzero, the Frozen pseudoinverse
readout is simultaneously the ordinary inverse, solves `A x = b`, and is the
minimum-norm least-squares solution. -/
theorem eq1_pseudoinverse_readout {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hne : ∀ i, eig i ≠ 0) :
    matrixPseudoinverse (continuousHHLMatrix eig V) = (continuousHHLMatrix eig V)⁻¹ ∧
    (∀ b : QState (Fin D),
      continuousHHLMatrix eig V *ᵥ
        (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b) = b) ∧
    (∀ b : QState (Fin D),
      IsEuclideanLeastSquares (continuousHHLMatrix eig V) b
        (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b)) :=
  ⟨pseudoinverse_eq_inv_of_ne_zero eig V hV hne,
   fun b => pseudoinverse_mulVec_solves eig V hV hne b,
   fun b => pseudoinverse_mulVec_leastSquares eig V hV b⟩

end Qatlib.Papers.QLinearSolver18.MainResults.Readout.PseudoinverseReadout
