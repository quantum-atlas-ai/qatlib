/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Spectral identities for finite Hamiltonian evolution

These lemmas relate rank-one state matrices, the quantum-state inner product, and matrix
exponentials. Eigenvectors evolve by scalar phases, and squared overlaps with the columns of a
unitary matrix sum to one for a normalized state. This development supports the treatment in
[FarhiGutmann1998a].

## Main statements

* `matrix_exp_mulVec_of_eigen`: exponentiation preserves the eigenvector relation.
* `hamiltonianEvolution_eigenvector`: the energy-dependent evolution phase.
* `spectral_weights_sum`: normalization of unitary-basis overlap weights.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998a]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
namespace Qatlib.Papers.AnalogDigital96.MainResults
variable {I : Type} [Fintype I] [DecidableEq I]
omit [Fintype I] [DecidableEq I] in

/-- The rank-one matrix formed from a complex state vector is Hermitian. -/
theorem outerProduct_isHermitian (w : QState I) :
    (outerProduct w).IsHermitian := by
  ext i j
  simp [outerProduct,Matrix.conjTranspose_apply,mul_comm]
omit [DecidableEq I] in

/-- The quantum-state inner product is complex linear under scalar multiplication in its second
argument. -/
theorem inner_smul_state (s x : QState I) (a : ℂ) : Inner s (a • x) = a * Inner s x := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul, smul_eq_mul]
omit [DecidableEq I] in

/-- The quantum-state inner product distributes over addition in its second argument. -/
theorem inner_add_state (s x y : QState I) : Inner s (x+y) = Inner s x+Inner s y :=
  dotProduct_add _ _ _
omit [DecidableEq I] in

/-- The quantum-state inner product distributes over subtraction in its second argument. -/
theorem inner_sub_state (s x y : QState I) : Inner s (x-y) = Inner s x-Inner s y :=
  dotProduct_sub _ _ _
omit [DecidableEq I] in

/-- Complex conjugation of the quantum-state inner product swaps its two arguments. -/
theorem inner_conj_state (s x : QState I) : star (Inner s x) = Inner x s := by
  exact (Matrix.star_dotProduct x s).symm

/-- If `A *ᵥ u = z • u`, then the matrix exponential acts on `u` by multiplication by `exp z`. -/
theorem matrix_exp_mulVec_of_eigen (A : Matrix I I ℂ) (u : QState I) (z : ℂ)
    (hu : A *ᵥ u = z • u) : NormedSpace.exp A *ᵥ u = Complex.exp z • u := by
  let L : Matrix I I ℂ →L[ℂ] QState I :=
    ((Matrix.mulVecBilin ℂ ℂ).flip u).toContinuousLinearMap
  have hp (n : ℕ) : A ^ n *ᵥ u = z ^ n • u := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hu, smul_smul]
      rw [pow_succ, mul_comm]
  have hm := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL L
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).smul_const u
  have he : (fun n => L ((n.factorial : ℂ)⁻¹ • A ^ n)) =
      (fun n => (((n.factorial : ℂ)⁻¹ • z ^ n) • u)) := by
    funext n
    change ((n.factorial : ℂ)⁻¹ • A ^ n) *ᵥ u = _
    rw [Matrix.smul_mulVec, hp, smul_smul]
    rfl
  rw [he] at hm
  rw [← Complex.exp_eq_exp_ℂ] at hs
  exact hm.unique hs

/-- A vector satisfying the energy relation `H *ᵥ u = ℓ • u` evolves by the scalar phase `exp(-I
* t * ℓ)`. -/
theorem hamiltonianEvolution_eigenvector (H : Matrix I I ℂ) (u : QState I) (ℓ t : ℝ)
    (hu : H *ᵥ u = (ℓ : ℂ) • u) :
    HamiltonianEvolution H t *ᵥ u = Complex.exp ((-Complex.I*(t : ℂ))*(ℓ : ℂ)) • u := by
  unfold HamiltonianEvolution
  apply matrix_exp_mulVec_of_eigen
  rw [Matrix.smul_mulVec, hu, smul_smul]

/-- For a normalized state, the squared overlaps with the columns of a unitary matrix sum to
one. -/
theorem spectral_weights_sum (V : Matrix I I ℂ) (w : QState I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hw : Normalized w) :
    ∑ i, ‖Inner (fun j => V j i) w‖^2 = 1 := by
  have hVs : Vᴴ ∈ Matrix.unitaryGroup I ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose] using hV
  have hn := normalized_applyGate hVs hw
  have hi (i : I) : Inner (fun j => V j i) w = (Vᴴ *ᵥ w) i := rfl
  simpa only [Normalized,ApplyGate,hi] using hn
end Qatlib.Papers.AnalogDigital96.MainResults
