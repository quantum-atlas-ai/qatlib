/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option backward.isDefEq.respectTransparency false

/-!
# Shadow Hamiltonian simulation — paper model

Source: "Shadow Hamiltonian Simulation", arXiv:2407.21775v1 (fixed version,
`assets/2407.21775.pdf`).  This module fixes the finite-dimensional shadow-state
model used by every claim of the paper's `MainResults` block.

The paper works with operators `O_m` on a finite-dimensional system, the
expectations `⟨O_m⟩ = tr(ρ O_m)` (Eq. (1)), and the shadow state
`|ρ;S⟩ = (1/√A) ∑_m ⟨O_m⟩ |m⟩`.  We work with the *unnormalised amplitude
vector* `shadowState ρ O m = tr(ρ O_m)`; the paper's normalisation by the
positive scalar `√A` does not affect any of the linear evolution equations
(Theorem 1, Theorem 2).  All matrices are `N × N` complex matrices with
`N` finite (`Fintype N`, `DecidableEq N`).
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius Kronecker

namespace Qatlib.Papers.ShadowHam24.MainResults

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

/-! ## Paper objects -/

/-- Paper Eq. (1): the expectation (amplitude) `⟨O⟩ = tr(ρ O)`. -/
def expectation (ρ O : Matrix N N ℂ) : ℂ := (ρ * O).trace

/-- Paper Eq. (1): the **shadow state amplitude vector** `m ↦ tr(ρ O_m)`.
The paper normalises this vector by `1/√A`; all stated evolution equations are
linear and are unaffected by that positive scalar. -/
def shadowState (ρ : Matrix N N ℂ) (O : M → Matrix N N ℂ) : M → ℂ :=
  fun m => expectation ρ (O m)

/-- Paper Eq. (2)–(3): the invariance property (IP).  The commutator of `H`
with every `O_m` is a linear combination of the `O_m'` with coefficients the
entries of `H_S`. -/
def InvarianceProperty (H : Matrix N N ℂ) (O : M → Matrix N N ℂ)
    (hS : Matrix M M ℂ) : Prop :=
  ∀ m, H * O m - O m * H = - ∑ m', hS m m' • O m'

/-- Paper Eq. (19): the entries of the shadow Hamiltonian under operator
orthogonality, `h_{mm'} = -(1/λ) tr(O_{m'}^† [H, O_m])`. -/
def shadowCoefficient (H : Matrix N N ℂ) (O : M → Matrix N N ℂ)
    (lam : ℂ) (m m' : M) : ℂ :=
  -(1 / lam) * ((O m')ᴴ * (H * O m - O m * H)).trace

/-- The shadow Hamiltonian `H_S` with entries `shadowCoefficient`. -/
def shadowHamiltonian (H : Matrix N N ℂ) (O : M → Matrix N N ℂ)
    (lam : ℂ) : Matrix M M ℂ :=
  fun m m' => shadowCoefficient H O lam m m'

/-- Gram matrix of an operator family, `(ij,i'j') ↦ tr(O_{ij} O_{i'j'}^†)`.
This is the (conjugate of the) Hilbert–Schmidt inner product used in paper
Eq. (19): under the paper's orthogonality `tr(O_{ij}^† O_{i'j'}) = λ δ` with
`λ > 0`, this equals `λ δ` as well since `δ` is real.  Orthonormality of the
operator basis is the statement `gramMatrix O = 1`. -/
def gramMatrix (O : N × N → Matrix N N ℂ) : Matrix (N × N) (N × N) ℂ :=
  fun ij i'j' => ((O ij) * (O i'j')ᴴ).trace

/-- Paper Eq. (42): the matrix of the shadow change-of-basis operator `V_S`,
in Mathlib's column-major vectorisation (`Matrix.vec A (i,j) = A j i`):
`(shadowTransform O *ᵥ vec ρ) (i,j) = ∑_{p,q} (O_{ij})_{p,q} (vec ρ)(p,q)`.
This is the paper's `V_S` up to the Bell-basis index convention (see
`pure_shadow_eq`). -/
def shadowTransform (O : N × N → Matrix N N ℂ) : Matrix (N × N) (N × N) ℂ :=
  fun ij pq => O ij pq.1 pq.2

/-- Pure-state density matrix `ρ = |ψ⟩⟨ψ|`. -/
def rankOne (ψ : N → ℂ) : Matrix N N ℂ := vecMulVec ψ (star ψ)

/-- The vectorised Bell pair `|ψ⟩ ⊗ |ψ̄⟩` in Mathlib's `vec` index convention:
`bellVector ψ (i,j) = ψ_j conj(ψ_i)`. -/
def bellVector (ψ : N → ℂ) : N × N → ℂ := fun ij => ψ ij.2 * star (ψ ij.1)

/-- Paper Eq. (51): the operator `Ũ = V_S (U ⊗ U) V_S^†` on shadow space,
with the Kronecker factor `U* ⊗ₖ U` (`U* = U.map star`). -/
def vecConjOp (U : Matrix N N ℂ) : Matrix (N × N) (N × N) ℂ :=
  (U.map star) ⊗ₖ U

/-- The shadow-space operator `Ũ = V_S (U ⊗ U) V_S^†` of paper Eq. (51). -/
def tildeOperator (U : Matrix N N ℂ) (O : N × N → Matrix N N ℂ) :
    Matrix (N × N) (N × N) ℂ :=
  shadowTransform O * vecConjOp U * (shadowTransform O)ᴴ

/-! ## Matrix-calculus helpers -/

/-- Cyclic invariance of the trace of a product of three square matrices;
used in the trace manipulations of paper Theorem 1, p. 3, Eq. (4). -/
lemma trace_cycle3 (A B C : Matrix N N ℂ) :
    (A * B * C).trace = (C * A * B).trace := by
  calc (A * B * C).trace = (C * (A * B)).trace := Matrix.trace_mul_comm (A * B) C
    _ = (C * A * B).trace := by rw [Matrix.mul_assoc]

/-- Von Neumann / Heisenberg identity behind Theorem 1: if
`ρ' = -i [H, ρ]` then `tr(ρ' O) = i tr(ρ [H, O])`. -/
lemma trace_vonNeumann_mul (ρ H O : Matrix N N ℂ) :
    ((-(Complex.I)) • (H * ρ - ρ * H) * O).trace =
      Complex.I * (ρ * (H * O - O * H)).trace := by
  rw [Matrix.smul_mul, Matrix.trace_smul]
  have hX : ((H * ρ - ρ * H) * O).trace = - (ρ * (H * O - O * H)).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_sub, Matrix.trace_sub]
    have h1 : (H * ρ * O).trace = (ρ * O * H).trace := by
      rw [trace_cycle3 H ρ O, trace_cycle3 O H ρ]
    rw [h1, ← Matrix.mul_assoc ρ H O, ← Matrix.mul_assoc ρ O H]
    ring
  rw [hX]; ring

/-- Derivative of the trace of a matrix-valued function of a real parameter;
used to differentiate the shadow amplitudes in paper Theorem 1, p. 3, Eq. (4). -/
lemma hasDerivAt_trace (A : ℝ → Matrix N N ℂ) (A' : Matrix N N ℂ) (t : ℝ)
    (h : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).trace) A'.trace t := by
  have h_entry : ∀ i, HasDerivAt (fun s => A s i i) (A' i i) t :=
    fun i => (hasDerivAt_pi.mp ((hasDerivAt_pi.mp h) i)) i
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (A := fun i s => A s i i) (A' := fun i => A' i i) (fun i _ => h_entry i)
  have hfun : (∑ i, fun s => A s i i) = (fun s => ∑ i, A s i i) := by
    funext s; simp
  rw [hfun] at hsum
  simpa [Matrix.trace] using hsum

/-- Derivative of `s ↦ tr(ρ(s) · B)` for a fixed matrix `B`
(paper Theorem 1, p. 3, Eq. (4)). -/
lemma hasDerivAt_trace_mul_const (ρ : ℝ → Matrix N N ℂ) (ρ' : Matrix N N ℂ)
    (B : Matrix N N ℂ) (t : ℝ) (hρ : HasDerivAt ρ ρ' t) :
    HasDerivAt (fun s => (ρ s * B).trace) ((ρ' * B).trace) t :=
  hasDerivAt_trace (fun s => ρ s * B) (ρ' * B) t (hρ.mul_const B)

/-- Derivative of `s ↦ tr(ρ · C(s))` for a fixed matrix `ρ`
(paper Theorem 2, p. 6, Eq. (8)). -/
lemma hasDerivAt_trace_const_mul (ρ : Matrix N N ℂ) (C : ℝ → Matrix N N ℂ)
    (C' : Matrix N N ℂ) (t : ℝ) (hC : HasDerivAt C C' t) :
    HasDerivAt (fun s => (ρ * C s).trace) (ρ * C').trace t :=
  hasDerivAt_trace (fun s => ρ * C s) (ρ * C') t (hC.const_mul ρ)

/-! ## Trace / vectorisation algebra -/

/-- `(ρ * O).trace` as a double sum matching `Matrix.vec`
(paper Lemma 5, p. 17, Eq. (43), vectorisation of the shadow state). -/
lemma trace_mul_eq_sum (ρ O : Matrix N N ℂ) :
    (ρ * O).trace = ∑ ab : N × N, O ab.1 ab.2 * ρ ab.2 ab.1 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  conv_rhs => rw [Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-- `(A * B^†).trace` as the sum defining `gramMatrix`
(paper Lemma 6, p. 18, Eq. (47)). -/
lemma trace_mul_conjTranspose_eq_sum (A B : Matrix N N ℂ) :
    (A * Bᴴ).trace = ∑ pq : N × N, A pq.1 pq.2 * star (B pq.1 pq.2) := by
  rw [trace_mul_eq_sum A Bᴴ]
  simp only [Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The shadow state is the shadow transform applied to the vectorised state
(paper Lemma 5, p. 17, Eq. (43), at the level of the linear map). -/
lemma shadowState_eq_shadowTransform_mulVec (ρ : Matrix N N ℂ)
    (O : N × N → Matrix N N ℂ) :
    shadowState ρ O = shadowTransform O *ᵥ Matrix.vec ρ := by
  funext ij
  simpa [shadowState, expectation, shadowTransform, Matrix.mulVec, dotProduct,
    Matrix.vec] using trace_mul_eq_sum ρ (O ij)

/-- For Hermitian `ρ`, `tr(O^† ρ) = conj(tr(ρ O))`; used to turn the expansion
coefficient in paper Lemma 6, p. 18, Eq. (47), into a shadow-state amplitude. -/
lemma trace_conjTranspose_mul_eq_star (ρ O : Matrix N N ℂ) (hρ : ρ.IsHermitian) :
    ((O)ᴴ * ρ).trace = star ((ρ * O).trace) := by
  have h : star (((O)ᴴ * ρ).trace) = (ρ * O).trace := by
    rw [← Matrix.trace_conjTranspose]
    congr 1
    rw [Matrix.conjTranspose_mul, hρ.eq, Matrix.conjTranspose_conjTranspose]
  rw [← h, star_star]

/-- The shadow transform is an isometry when the operator family is
orthonormal: `V_S V_S^† = 1` (paper Lemma 5, p. 17, Eq. (42), unitary of `V_S`). -/
lemma shadowTransform_mul_conjTranspose (O : N × N → Matrix N N ℂ) :
    shadowTransform O * (shadowTransform O)ᴴ = gramMatrix O := by
  ext ij i'j'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, shadowTransform, gramMatrix]
  exact (trace_mul_conjTranspose_eq_sum (O ij) (O i'j')).symm

/-- Orthonormality gives full unitarity of `V_S` (both sides)
(paper Lemma 5, p. 17, Eq. (42)). -/
lemma shadowTransform_conjTranspose_mul_self (O : N × N → Matrix N N ℂ)
    (horth : gramMatrix O = 1) :
    (shadowTransform O)ᴴ * shadowTransform O = 1 :=
  mul_eq_one_comm.mp (by rw [shadowTransform_mul_conjTranspose, horth])

/-- Sum identity used to rewrite `tr(ρ · (-∑ c • O))` in paper Theorem 1,
p. 3, Eq. (4), and Theorem 2, p. 6, Eq. (7). -/
lemma trace_mul_neg_sum_smul (ρ : Matrix N N ℂ) (O : M → Matrix N N ℂ)
    (c : M → ℂ) :
    (ρ * (- ∑ m', c m' • O m')).trace = - ∑ m', c m' * (ρ * O m').trace := by
  rw [Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  rw [Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl; intro m' _
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp

/-- Sum identity for a commutator in the middle of a trace
(paper Theorem 2, p. 6, Eq. (7)). -/
lemma trace_mul_neg_sum_smul_mul (ρ B : Matrix N N ℂ) (A : M → Matrix N N ℂ)
    (c : M → ℂ) :
    (ρ * (- ∑ m', c m' • A m') * B).trace =
      - ∑ m', c m' * (ρ * A m' * B).trace := by
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl; intro m' _
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
  simp

/-- Pull a scalar out of a middle factor of a trace
(paper Theorem 2, p. 6, Eq. (7)). -/
lemma trace_mul_smul_mul (ρ B : Matrix N N ℂ) (c : ℂ) (X : Matrix N N ℂ) :
    (ρ * (c • X) * B).trace = c * (ρ * X * B).trace := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
  simp

/-- Pull a scalar out of the right factor of a trace
(paper Theorem 2, p. 6, Eq. (8)). -/
lemma trace_mul_smul (ρ : Matrix N N ℂ) (c : ℂ) (X : Matrix N N ℂ) :
    (ρ * (c • X)).trace = c * (ρ * X).trace := by
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp

/-- `rankOne ψ` is Hermitian; used for the pure-state case of paper Lemma 5,
p. 17, Eq. (43). -/
lemma rankOne_isHermitian (ψ : N → ℂ) : (rankOne ψ).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp [rankOne, vecMulVec, star_mul]

/-- Vectorised form of `U σ U^†` (paper Lemma 7, p. 19, Eq. (51)):
`vec (U σ U^†) = (U* ⊗ U) vec σ`, where `U* = U.map star`. -/
lemma vec_mul_mul_conjTranspose (U σ : Matrix N N ℂ) :
    Matrix.vec (U * σ * Uᴴ) = vecConjOp U *ᵥ Matrix.vec σ := by
  rw [vecConjOp, kronecker_mulVec_vec U σ (U.map star)]
  congr 1

/-- `vec (rankOne ψ)` is the vectorised Bell pair `|ψ⟩ ⊗ |ψ̄⟩`
(paper Lemma 5, p. 17, Eq. (43)). -/
lemma vec_rankOne (ψ : N → ℂ) :
    Matrix.vec (rankOne ψ) = bellVector ψ := by
  funext ij
  simp [Matrix.vec, rankOne, vecMulVec, bellVector]

/-- Paper Lemma 5, p. 17, Eq. (43): for a pure state the shadow state is obtained by
applying the shadow transform to the vectorised Bell pair `|ψ⟩ ⊗ |ψ̄⟩`. -/
theorem pure_shadow_eq (ψ : N → ℂ) (O : N × N → Matrix N N ℂ) :
    shadowState (rankOne ψ) O = shadowTransform O *ᵥ bellVector ψ := by
  rw [shadowState_eq_shadowTransform_mulVec, vec_rankOne]

end Qatlib.Papers.ShadowHam24.MainResults
