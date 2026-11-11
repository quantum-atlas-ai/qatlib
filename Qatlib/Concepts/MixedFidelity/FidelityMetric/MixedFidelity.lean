/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.MixedFidelity.FidelityMetric.RankOneTraceNormBound
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import QuantumInfo.States.Mixed.Fidelity

/-!
# Root fidelity, purifications, and trace distance

`Froot` and `traceDistance` satisfy the basic range, symmetry, pure-state, classical-state,
unitary-invariance, and tensor-product identities collected in `g1`. Matrix square-root and
polar-decomposition lemmas support the purification-overlap characterization of root fidelity in
`g2`.

The module proves that quantum channels increase root fidelity and contract trace distance.
These properties accompany the two Fuchs–van de Graaf inequalities collected in `g3`. See
[Uhlmann1976].

## Main statements

* `g1`: basic identities for root fidelity and trace distance.
* `g2`: root fidelity is the maximal overlap of purifications with sufficient ancillary
  dimension.
* `g3`: Fuchs–van de Graaf inequalities and channel monotonicity.

## References

* [Uhlmann, 1976][Uhlmann1976]
* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
* [Wilde, 2017][Wilde2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.DensityToRaw

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

/-- The root-fidelity expression given by the trace norm of the product of two matrix square
roots, for an arbitrary finite index type. -/
private noncomputable def FrootG {I : Type} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) : ℝ :=
  Matrix.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

section Sqrt

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The continuous-functional-calculus square root of a complex matrix is Hermitian. -/
private theorem cfc_sqrt_conjTranspose (A : Matrix I I ℂ) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).1

/-- The continuous-functional-calculus square root of a positive semidefinite matrix squares to
that matrix. -/
private theorem cfc_sqrt_sq_of_posSemidef {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A (Matrix.PosSemidef.nonneg hA)

/-- A positive semidefinite matrix whose square is `A` equals the continuous-functional-calculus
square root of `A`. -/
private theorem cfc_sqrt_unique {A B : Matrix I I ℂ} (hB : B.PosSemidef)
    (h : B * B = A) : CFC.sqrt A = B :=
  CFC.sqrt_unique h (Matrix.PosSemidef.nonneg hB)

/-- The bundled Hermitian-matrix square root of a positive semidefinite matrix agrees with its
continuous-functional-calculus square root. -/
private theorem hermMat_sqrt_eq_cfc {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (HermitianMat.sqrt ⟨A, hA.1⟩).mat = CFC.sqrt A := by
  rw [HermitianMat.sqrt, HermitianMat.mat_cfc,
    CFC.sqrt_eq_real_sqrt A (Matrix.PosSemidef.nonneg hA), cfcₙ_eq_cfc]
  rfl

end Sqrt

section TraceNorm

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The trace norm of a product of two Hermitian matrices is unchanged by swapping the factors. -/
private theorem traceNorm_mul_hermitian_swap {A B : Matrix I I ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) :
    Matrix.traceNorm (A * B) = Matrix.traceNorm (B * A) := by
  rw [← Matrix.traceNorm_conjTranspose, Matrix.conjTranspose_mul, hA, hB]

omit [DecidableEq I] in

/-- The trace norm of a positive semidefinite matrix equals the real part of its trace. -/
private theorem psd_traceNorm_eq_re_trace {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    Matrix.traceNorm A = (Matrix.trace A).re := by
  simpa using congrArg Complex.re hA.traceNorm_eq_trace

/-- Every density operator has trace norm one. -/
private theorem density_traceNorm_eq_one {D : ℕ} {ρ : Operator D}
    (hρ : IsDensityOperator ρ) : Matrix.traceNorm ρ = 1 := by
  rw [psd_traceNorm_eq_re_trace hρ.1, hρ.2, Complex.one_re]

end TraceNorm

section Bridge

variable {D : ℕ}

/-- The bundled mixed state associated with an operator satisfying `IsDensityOperator`. -/
private noncomputable def toMState {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    MState (Fin D) :=
  Qatlib.Foundations.PureStateMath.BornBridge.densityOperatorEquivMState D ⟨ρ, hρ⟩

/-- The square root of the bundled mixed state agrees with the continuous-functional-calculus
square root of its operator. -/
private theorem toMState_sqrt_mat {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    (toMState hρ).M.sqrt.mat = CFC.sqrt ρ := by
  have : (toMState hρ).M = ⟨ρ, hρ.1.1⟩ := rfl
  rw [this]
  exact hermMat_sqrt_eq_cfc hρ.1

/-- For density operators, `Froot` agrees with the bundled mixed-state fidelity. -/
private theorem froot_eq_fidelity {ρ σ : Operator D} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) :
    Froot ρ σ = MState.fidelity (toMState hρ) (toMState hσ) := by
  rw [MState.fidelity_eq_traceNorm_sqrt_mul_sqrt, toMState_sqrt_mat hσ,
    toMState_sqrt_mat hρ, Froot]
  exact traceNorm_mul_hermitian_swap (cfc_sqrt_conjTranspose ρ)
    (cfc_sqrt_conjTranspose σ)

/-- The root fidelity between two density operators is at most one. -/
private theorem froot_le_one {ρ σ : Operator D} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : Froot ρ σ ≤ 1 := by
  rw [froot_eq_fidelity hρ hσ]
  exact MState.fidelity_le_one _ _

/-- Two density operators have root fidelity one exactly when they are equal. -/
private theorem froot_eq_one_iff {ρ σ : Operator D} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : Froot ρ σ = 1 ↔ ρ = σ := by
  rw [froot_eq_fidelity hρ hσ]
  constructor
  · intro h
    have hM : toMState hρ = toMState hσ :=
      (MState.fidelity_eq_one_iff_self _ _).mp h
    have hm : (toMState hρ).m = (toMState hσ).m := by rw [hM]
    exact hm
  · intro h
    subst h
    exact MState.fidelity_self_eq_one _

end Bridge

section Pure

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- A state's outer-product matrix is its vector outer product with its conjugate. -/
private theorem outerProduct_eq_vecMulVec (ψ : QState I) :
    outerProduct ψ = Matrix.vecMulVec ψ (star ψ) := by
  ext i j
  rfl

/-- The outer product of a normalized vector is its own positive square root. -/
private theorem cfc_sqrt_outerProduct {ψ : QState I} (hψ : Normalized ψ) :
    CFC.sqrt (outerProduct ψ) = outerProduct ψ :=
  cfc_sqrt_unique (outerProduct_posSemidef ψ) (isOrthogonalProjector_outerProduct hψ).1

/-- The rank-one outer product of two normalized vectors has trace norm one. -/
private theorem traceNorm_vecMulVec_normalized {u v : QState I}
    (hu : Normalized u) (hv : Normalized v) :
    Matrix.traceNorm (Matrix.vecMulVec u (star v)) = 1 := by
  have hin : (star u ⬝ᵥ u) • star v = star v := by
    show (Qatlib.Foundations.PureStateMath.Inner u u) • star v = star v
    rw [inner_self_eq_one hu, one_smul]
  have hAA : (Matrix.vecMulVec u (star v))ᴴ * Matrix.vecMulVec u (star v)
      = outerProduct v := by
    rw [Matrix.conjTranspose_vecMulVec, star_star, Matrix.vecMulVec_mul_vecMulVec, hin,
      outerProduct_eq_vecMulVec]
  have hvv : Qatlib.Foundations.PureStateMath.Inner v v = 1 := inner_self_eq_one hv
  unfold Matrix.traceNorm
  rw [hAA, cfc_sqrt_outerProduct hv, outerProduct_eq_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm]
  exact congrArg RCLike.re hvv

/-- For normalized pure vectors, the trace norm of the product of their outer-product square
roots equals the modulus of their inner product. -/
private theorem froot_outerProduct {ψ φ : QState I} (hψ : Normalized ψ)
    (hφ : Normalized φ) :
    Matrix.traceNorm (CFC.sqrt (outerProduct ψ) * CFC.sqrt (outerProduct φ))
      = ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ := by
  rw [cfc_sqrt_outerProduct hψ, cfc_sqrt_outerProduct hφ]
  have hmul : outerProduct ψ * outerProduct φ
      = (Qatlib.Foundations.PureStateMath.Inner ψ φ) • Matrix.vecMulVec ψ (star φ) := by
    ext i j
    simp only [Matrix.mul_apply, outerProduct_apply, Matrix.vecMulVec_apply,
      Matrix.smul_apply, smul_eq_mul, dotProduct, Qatlib.Foundations.PureStateMath.Inner, Pi.star_apply]
    have hterm : ∀ x : I, ψ i * (starRingEnd ℂ) (ψ x) * (φ x * (starRingEnd ℂ) (φ j))
        = ((starRingEnd ℂ) (ψ x) * φ x) * (ψ i * star (φ j)) := by
      intro x
      rw [show star (φ j) = (starRingEnd ℂ) (φ j) from rfl]
      ring
    conv_lhs => rw [Finset.sum_congr rfl fun x _ => hterm x]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => rfl
  rw [hmul, Matrix.traceNorm_smul, traceNorm_vecMulVec_normalized hψ hφ, mul_one]

end Pure

section Classical

variable {D : ℕ}

/-- The positive square root of a diagonal probability matrix is obtained by taking square roots
of its diagonal probabilities. -/
private theorem cfc_sqrt_diagDensity {p : Fin D → ℝ} (hp : IsProbVector p) :
    CFC.sqrt (diagDensity p) = diagDensity (fun i => Real.sqrt (p i)) := by
  apply cfc_sqrt_unique
  · show (diagDensity (fun i => Real.sqrt (p i))).PosSemidef
    rw [diagDensity, Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast Real.sqrt_nonneg (p i)
  · have hsq : diagDensity (fun i => Real.sqrt (p i)) * diagDensity (fun i => Real.sqrt (p i))
        = diagDensity p := by
      simp only [diagDensity, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, Complex.ofReal_inj]
      exact Real.mul_self_sqrt (hp.1 i)
    exact hsq

/-- The root fidelity of diagonal probability matrices is the sum of the square roots of their
coordinatewise probability products. -/
private theorem froot_diagDensity {p q : Fin D → ℝ} (hp : IsProbVector p)
    (hq : IsProbVector q) :
    Froot (diagDensity p) (diagDensity q) = ∑ i, Real.sqrt (p i * q i) := by
  rw [Froot, cfc_sqrt_diagDensity hp, cfc_sqrt_diagDensity hq]
  have hdiag : diagDensity (fun i => Real.sqrt (p i)) * diagDensity (fun i => Real.sqrt (q i))
      = Matrix.diagonal fun i => ((Real.sqrt (p i) * Real.sqrt (q i) : ℝ) : ℂ) := by
    simp only [diagDensity, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul]
  rw [hdiag]
  have hpsd : (Matrix.diagonal fun i => ((Real.sqrt (p i) * Real.sqrt (q i) : ℝ) : ℂ)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [psd_traceNorm_eq_re_trace hpsd, Matrix.trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]
  exact Finset.sum_congr rfl fun i _ => (Real.sqrt_mul (hp.1 i) (q i)).symm

end Classical

section Unitary

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Conjugation by a square matrix satisfying `Uᴴ * U = 1` preserves matrix multiplication. -/
private theorem unitary_conj_mul {U X Y : Matrix I I ℂ} (hU : Uᴴ * U = 1) :
    (U * X * Uᴴ) * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U (Y * Uᴴ), hU, Matrix.one_mul]

/-- A matrix in the unitary group satisfies `Uᴴ * U = 1`. -/
private theorem unitary_star_mul {D : ℕ} {U : Matrix (Fin D) (Fin D) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) : Uᴴ * U = 1 :=
  (Matrix.mem_unitaryGroup_iff').mp hU

omit [DecidableEq I] in

/-- The adjoint of `U * A * Uᴴ` is `U * Aᴴ * Uᴴ`. -/
private theorem conjTranspose_unitary_conj {U A : Matrix I I ℂ} :
    (U * A * Uᴴ)ᴴ = U * Aᴴ * Uᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Conjugation by a square matrix satisfying `Uᴴ * U = 1` preserves trace. -/
private theorem trace_unitary_conj {U S : Matrix I I ℂ} (hU : Uᴴ * U = 1) :
    (U * S * Uᴴ).trace = S.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- Conjugation by a square matrix satisfying `Uᴴ * U = 1` preserves the trace norm. -/
private theorem traceNorm_unitary_conj' {U A : Matrix I I ℂ} (hU : Uᴴ * U = 1) :
    Matrix.traceNorm (U * A * Uᴴ) = Matrix.traceNorm A := by
  have hS : (CFC.sqrt (Aᴴ * A)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have hconj : CFC.sqrt ((U * A * Uᴴ)ᴴ * (U * A * Uᴴ))
      = U * CFC.sqrt (Aᴴ * A) * Uᴴ := by
    rw [conjTranspose_unitary_conj, unitary_conj_mul hU]
    exact cfc_sqrt_unique (hS.mul_mul_conjTranspose_same U)
      (by rw [unitary_conj_mul hU,
        cfc_sqrt_sq_of_posSemidef A.posSemidef_conjTranspose_mul_self])
  unfold Matrix.traceNorm
  rw [hconj, trace_unitary_conj hU]

/-- The positive square root of a density operator commutes with unitary conjugation. -/
private theorem cfc_sqrt_unitary_conj {D : ℕ} {U : Matrix (Fin D) (Fin D) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) :
    CFC.sqrt (U * ρ * Uᴴ) = U * CFC.sqrt ρ * Uᴴ := by
  apply cfc_sqrt_unique
  · exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).mul_mul_conjTranspose_same U
  · rw [unitary_conj_mul (unitary_star_mul hU), cfc_sqrt_sq_of_posSemidef hρ.1]

/-- Applying the same unitary conjugation to two density operators preserves their root
fidelity. -/
private theorem froot_unitary_conj {D : ℕ} {U : Matrix (Fin D) (Fin D) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    Froot (U * ρ * Uᴴ) (U * σ * Uᴴ) = Froot ρ σ := by
  rw [Froot, Froot, cfc_sqrt_unitary_conj hU hρ, cfc_sqrt_unitary_conj hU hσ,
    unitary_conj_mul (unitary_star_mul hU),
    traceNorm_unitary_conj' (unitary_star_mul hU)]

/-- Applying the same unitary conjugation to two operators preserves their trace distance. -/
private theorem traceDistance_unitary_conj {D : ℕ} {U : Matrix (Fin D) (Fin D) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ σ : Operator D) :
    traceDistance (U * ρ * Uᴴ) (U * σ * Uᴴ) = traceDistance ρ σ := by
  rw [traceDistance, traceDistance, ← Matrix.sub_mul, ← Matrix.mul_sub,
    traceNorm_unitary_conj' (unitary_star_mul hU)]

end Unitary

section Tensor

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

open scoped Kronecker

/-- The positive square root of a Kronecker product of positive semidefinite matrices is the
Kronecker product of their square roots. -/
private theorem cfc_sqrt_kronecker {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {B : Matrix J J ℂ} (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B) = (CFC.sqrt A) ⊗ₖ (CFC.sqrt B) := by
  apply cfc_sqrt_unique
  · exact Matrix.PosSemidef.PosSemidef_kronecker
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))
  · rw [← Matrix.mul_kronecker_mul, cfc_sqrt_sq_of_posSemidef hA,
      cfc_sqrt_sq_of_posSemidef hB]

/-- The trace norm of a Kronecker product is the product of the two trace norms. -/
private theorem traceNorm_kronecker (M : Matrix I I ℂ) (N : Matrix J J ℂ) :
    Matrix.traceNorm (M ⊗ₖ N) = Matrix.traceNorm M * Matrix.traceNorm N := by
  have hkey : CFC.sqrt ((M ⊗ₖ N)ᴴ * (M ⊗ₖ N))
      = (CFC.sqrt (Mᴴ * M)) ⊗ₖ (CFC.sqrt (Nᴴ * N)) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    exact cfc_sqrt_kronecker M.posSemidef_conjTranspose_mul_self
      N.posSemidef_conjTranspose_mul_self
  have hSM : (CFC.sqrt (Mᴴ * M)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᴴ * M))
  have hSN : (CFC.sqrt (Nᴴ * N)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Nᴴ * N))
  have himM : ((CFC.sqrt (Mᴴ * M)).trace).im = 0 :=
    (Complex.nonneg_iff.mp hSM.trace_nonneg).2.symm
  have himN : ((CFC.sqrt (Nᴴ * N)).trace).im = 0 :=
    (Complex.nonneg_iff.mp hSN.trace_nonneg).2.symm
  have hre : ∀ a b : ℂ, a.im = 0 → b.im = 0 →
      RCLike.re (a * b) = RCLike.re a * RCLike.re b := by
    intro a b ha hb
    show Complex.re (a * b) = Complex.re a * Complex.re b
    rw [Complex.mul_re, ha, hb, mul_zero, sub_zero]
  unfold Matrix.traceNorm
  rw [hkey, Matrix.trace_kronecker, hre _ _ himM himN]

open scoped Kronecker in

/-- The root-fidelity expression is multiplicative on tensor products of positive semidefinite
matrices. -/
private theorem frootG_tensor {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) {τ ω : Matrix J J ℂ} (hτ : τ.PosSemidef)
    (hω : ω.PosSemidef) :
    FrootG (TensorGate ρ τ) (TensorGate σ ω) = FrootG ρ σ * FrootG τ ω := by
  simp only [FrootG, TensorGate]
  rw [cfc_sqrt_kronecker hρ hτ, cfc_sqrt_kronecker hσ hω,
    ← Matrix.mul_kronecker_mul, traceNorm_kronecker]

end Tensor

section Range

variable {D : ℕ}

/-- Root fidelity is symmetric in its two operator arguments. -/
private theorem froot_symm (ρ σ : Operator D) : Froot ρ σ = Froot σ ρ := by
  rw [Froot, Froot]
  exact traceNorm_mul_hermitian_swap (cfc_sqrt_conjTranspose ρ) (cfc_sqrt_conjTranspose σ)

/-- The trace distance between two density operators is at most one. -/
private theorem traceDistance_le_one {ρ σ : Operator D} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : traceDistance ρ σ ≤ 1 := by
  have h : Matrix.traceNorm (ρ - σ) ≤ 2 := by
    have h1 : (ρ + -σ).traceNorm ≤ ρ.traceNorm + (-σ).traceNorm :=
      Matrix.traceNorm_add_le ρ (-σ)
    rw [Matrix.traceNorm_neg, density_traceNorm_eq_one hρ,
      density_traceNorm_eq_one hσ] at h1
    rw [sub_eq_add_neg]
    linarith
  rw [traceDistance, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

end Range

/-- Collect the range, symmetry, equality, pure-state, diagonal-state, unitary-invariance, and
tensor-product identities for root fidelity and trace distance. The commuting-state formula
is stated for a supplied simultaneous unitary diagonalization. -/
theorem g1 :
  (∀ (D : ℕ) (ρ σ : Operator D), IsDensityOperator ρ → IsDensityOperator σ →
    (FrootG ρ σ = Froot ρ σ) ∧
    (0 ≤ Froot ρ σ ∧ Froot ρ σ ≤ 1 ∧
      0 ≤ traceDistance ρ σ ∧ traceDistance ρ σ ≤ 1) ∧
    (Froot ρ σ = Froot σ ρ) ∧
    (Froot ρ σ = 1 ↔ ρ = σ) ∧
    (∀ ψ φ : QState (Fin D), Normalized ψ → Normalized φ →
      Froot (outerProduct ψ) (outerProduct φ) = ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖) ∧
    (∀ (p q : Fin D → ℝ), IsProbVector p → IsProbVector q →
      Froot (diagDensity p) (diagDensity q) = ∑ i, Real.sqrt (p i * q i)) ∧
    (CommutesToClassical ρ σ → ρ * σ = σ * ρ →
      ∀ (p q : Fin D → ℝ), IsProbVector p → IsProbVector q →
        ∀ U : Matrix (Fin D) (Fin D) ℂ, U ∈ Matrix.unitaryGroup (Fin D) ℂ →
          U * ρ * Uᴴ = diagDensity p → U * σ * Uᴴ = diagDensity q →
          Froot ρ σ = ∑ i, Real.sqrt (p i * q i)) ∧
    (∀ U : Matrix (Fin D) (Fin D) ℂ, U ∈ Matrix.unitaryGroup (Fin D) ℂ →
      Froot (U * ρ * Uᴴ) (U * σ * Uᴴ) = Froot ρ σ ∧
      traceDistance (U * ρ * Uᴴ) (U * σ * Uᴴ) = traceDistance ρ σ) ∧
    (∀ (E : ℕ) (τ ω : Operator E), IsDensityOperator τ → IsDensityOperator ω →
      FrootG (TensorGate ρ τ) (TensorGate σ ω) = FrootG ρ σ * FrootG τ ω)) := by
  intro D ρ σ hρ hσ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact ⟨Froot_nonneg ρ σ, froot_le_one hρ hσ, traceDistance_nonneg ρ σ,
      traceDistance_le_one hρ hσ⟩
  · exact froot_symm ρ σ
  · exact froot_eq_one_iff hρ hσ
  · intro ψ φ hψ hφ
    exact froot_outerProduct hψ hφ
  · intro p q hp hq
    exact froot_diagDensity hp hq
  · intro _ _ p q hp hq U hU hρd hσd
    rw [(froot_unitary_conj hU hρ hσ).symm, hρd, hσd]
    exact froot_diagDensity hp hq
  · intro U hU
    exact ⟨froot_unitary_conj hU hρ hσ, traceDistance_unitary_conj hU ρ σ⟩
  · intro E τ ω hτ hω
    exact frootG_tensor hρ.1 hσ.1 hτ.1 hω.1

/-- A bundled unitary matrix satisfies the left adjoint identity `U.valᴴ * U.val = 1`. -/
private theorem uhlmann_unitary_left {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) : U.valᴴ * U.val = 1 := by
  exact (Matrix.mem_unitaryGroup_iff').mp U.property

/-- A bundled unitary matrix satisfies the right adjoint identity `U.val * U.valᴴ = 1`. -/
private theorem uhlmann_unitary_right {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) : U.val * U.valᴴ = 1 := by
  exact (Matrix.mem_unitaryGroup_iff).mp U.property

/-- Right multiplication by the adjoint of a rectangular isometry preserves the trace norm. -/
private theorem uhlmann_traceNorm_isometry_right {I J K : Type}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq J]
    (A : Matrix I J ℂ) {U : Matrix K J ℂ} (hU : U.Isometry) :
    Matrix.traceNorm (A * Uᴴ) = Matrix.traceNorm A := by
  apply Matrix.traceNorm_isometry_right
  ext i j
  by_cases hij : i = j <;>
    simpa [Matrix.one_apply, hij] using congrFun (congrFun hU i) j

/-- Left multiplication by a rectangular isometry preserves the trace norm. -/
private theorem uhlmann_traceNorm_isometry_left {I J K : Type}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
    (A : Matrix I J ℂ) {U : Matrix K I ℂ} (hU : U.Isometry) :
    Matrix.traceNorm (U * A) = Matrix.traceNorm A := by
  apply Matrix.traceNorm_isometry_left
  ext i j
  by_cases hij : i = j <;>
    simpa [Matrix.one_apply, hij] using congrFun (congrFun hU i) j

/-- Every finite square complex matrix factors as `CFC.sqrt (A * Aᴴ) * U.val` for a unitary
matrix `U`. -/
theorem exists_unitary_sqrt_mul_adjoint {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    ∃ U : Matrix.unitaryGroup I ℂ, A = CFC.sqrt (A * Aᴴ) * U.val := by
  classical
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose
  obtain ⟨V, W, hA⟩ := Matrix.exists_svd_sqrt_eigenvalues A
  let S : Matrix I I ℂ := Matrix.diagonal fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)
  have hA' : A = V.val * S * W.valᴴ := hA
  have hV := uhlmann_unitary_left V
  have hW := uhlmann_unitary_left W
  have hS : S.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr fun i => by
    exact_mod_cast Real.sqrt_nonneg (hH.eigenvalues i)
  have hSH : Sᴴ = S := hS.1
  have hB : (V.val * S * V.valᴴ).PosSemidef := hS.mul_mul_conjTranspose_same V.val
  have hBB : (V.val * S * V.valᴴ) * (V.val * S * V.valᴴ) = A * Aᴴ := by
    rw [hA']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W.valᴴ W.val, hW, Matrix.one_mul,
      ← Matrix.mul_assoc V.valᴴ V.val, hV, Matrix.one_mul]
  have hroot : CFC.sqrt (A * Aᴴ) = V.val * S * V.valᴴ :=
    CFC.sqrt_unique hBB hB.nonneg
  refine ⟨V * star W, ?_⟩
  change A = CFC.sqrt (A * Aᴴ) * (V.val * W.valᴴ)
  rw [hroot]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V.valᴴ V.val, hV, Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using hA'

/-- The positive square root commutes with isometric conjugation of a positive semidefinite
matrix. -/
theorem sqrt_isometry_conjugation {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    {Jm : Matrix J I ℂ} (hJ : Jm.Isometry) :
    CFC.sqrt (Jm * ρ * Jmᴴ) = Jm * CFC.sqrt ρ * Jmᴴ := by
  have hS : (CFC.sqrt ρ).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  apply CFC.sqrt_unique _ (hS.mul_mul_conjTranspose_same Jm).nonneg
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Jmᴴ Jm, show Jmᴴ * Jm = 1 from hJ, Matrix.one_mul,
    ← Matrix.mul_assoc (CFC.sqrt ρ) (CFC.sqrt ρ), CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

/-- The modulus of the trace overlap of two square matrices is at most the trace norm of the
product of the square roots of their row Gram matrices. -/
theorem trace_overlap_le_sqrt_gram_square {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) :
    ‖(Xᴴ * Y).trace‖ ≤ Matrix.traceNorm (CFC.sqrt (X * Xᴴ) * CFC.sqrt (Y * Yᴴ)) := by
  obtain ⟨U, hX⟩ := exists_unitary_sqrt_mul_adjoint X
  obtain ⟨V, hY⟩ := exists_unitary_sqrt_mul_adjoint Y
  have hS : (CFC.sqrt (X * Xᴴ))ᴴ = CFC.sqrt (X * Xᴴ) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1
  have hU : U.valᴴ.Isometry := by
    change (U.valᴴ)ᴴ * U.valᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact uhlmann_unitary_right U
  have hV : V.valᴴ.Isometry := by
    change (V.valᴴ)ᴴ * V.valᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact uhlmann_unitary_right V
  refine (Matrix.abs_trace_le_traceNorm (Xᴴ * Y)).trans_eq ?_
  calc
    Matrix.traceNorm (Xᴴ * Y) =
        Matrix.traceNorm (U.valᴴ * (CFC.sqrt (X * Xᴴ) * CFC.sqrt (Y * Yᴴ)) * (V.valᴴ)ᴴ) := by
      conv_lhs => rw [hX, hY]
      simp only [Matrix.conjTranspose_mul, hS, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = _ := by rw [uhlmann_traceNorm_isometry_right _ hV, uhlmann_traceNorm_isometry_left _ hU]

/-- Given an isometry from the row index space into the column index space, rectangular matrix
overlap is bounded by the trace norm of the product of the square roots of the row Gram
matrices. -/
theorem trace_overlap_le_sqrt_gram_of_isometry {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Jm : Matrix J I ℂ) (hJ : Jm.Isometry)
    (X Y : Matrix I J ℂ) :
    ‖(Xᴴ * Y).trace‖ ≤ Matrix.traceNorm (CFC.sqrt (X * Xᴴ) * CFC.sqrt (Y * Yᴴ)) := by
  have hXX : (Jm * X) * (Jm * X)ᴴ = Jm * (X * Xᴴ) * Jmᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hYY : (Jm * Y) * (Jm * Y)ᴴ = Jm * (Y * Yᴴ) * Jmᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hXY : (Jm * X)ᴴ * (Jm * Y) = Xᴴ * Y := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jmᴴ Jm, show Jmᴴ * Jm = 1 from hJ, Matrix.one_mul]
  have h := trace_overlap_le_sqrt_gram_square (Jm * X) (Jm * Y)
  rw [hXY, hXX, hYY,
    sqrt_isometry_conjugation (Matrix.posSemidef_self_mul_conjTranspose X) hJ,
    sqrt_isometry_conjugation (Matrix.posSemidef_self_mul_conjTranspose Y) hJ] at h
  have hprod : (Jm * CFC.sqrt (X * Xᴴ) * Jmᴴ) * (Jm * CFC.sqrt (Y * Yᴴ) * Jmᴴ) =
      Jm * (CFC.sqrt (X * Xᴴ) * CFC.sqrt (Y * Yᴴ)) * Jmᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jmᴴ Jm, show Jmᴴ * Jm = 1 from hJ, Matrix.one_mul]
  rwa [hprod, uhlmann_traceNorm_isometry_right _ hJ, uhlmann_traceNorm_isometry_left _ hJ] at h

/-- For rectangular matrices with at least as many columns as rows, the modulus of their trace
overlap is bounded by the root-fidelity expression of their row Gram matrices. -/
theorem trace_overlap_le_sqrt_gram {D E : ℕ} (hDE : D ≤ E)
    (X Y : Matrix (Fin D) (Fin E) ℂ) :
    ‖(Xᴴ * Y).trace‖ ≤ Matrix.traceNorm (CFC.sqrt (X * Xᴴ) * CFC.sqrt (Y * Yᴴ)) := by
  let J : Matrix (Fin E) (Fin D) ℂ := (1 : Operator E).submatrix id (Fin.castLE hDE)
  exact trace_overlap_le_sqrt_gram_of_isometry J
    (Matrix.submatrix_one_id_right_isometry (Fin.castLE_injective hDE)) X Y

/-- The rectangular amplitude matrix of a bipartite state vector. -/
private def purificationMatrix {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    Matrix (Fin D) (Fin E) ℂ := fun i e => ψ (i,e)

/-- The row Gram matrix of a bipartite amplitude matrix equals the partial trace of its pure
outer product. -/
private theorem purificationMatrix_gram {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    purificationMatrix ψ * (purificationMatrix ψ)ᴴ = PartialTrace (outerProduct ψ) := by
  ext i j
  simp [purificationMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    PartialTrace, outerProduct]

/-- The inner product of bipartite vectors equals the trace overlap of their amplitude matrices. -/
private theorem purificationMatrix_inner {D E : ℕ} (ψ φ : QState (Fin D × Fin E)) :
    Qatlib.Foundations.PureStateMath.Inner ψ φ = ((purificationMatrix ψ)ᴴ * purificationMatrix φ).trace := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, purificationMatrix]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- When the ancillary dimension is at least the system dimension, the overlap modulus of any
two purifications is bounded by the root fidelity of their reduced operators. -/
theorem purification_overlap_le_froot {D E : ℕ} (hDE : D ≤ E)
    {ρ σ : Operator D} {ψ φ : QState (Fin D × Fin E)}
    (hψ : IsPurification ψ ρ) (hφ : IsPurification φ σ) :
    ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ≤ Froot ρ σ := by
  rw [purificationMatrix_inner]
  have h := trace_overlap_le_sqrt_gram hDE (purificationMatrix ψ) (purificationMatrix φ)
  simpa only [purificationMatrix_gram, hψ.2, hφ.2, Froot] using h

/-- An amplitude matrix with row Gram matrix `ρ` of trace one defines a normalized purification
of `ρ`. -/
theorem isPurification_of_amplitude_gram {D E : ℕ}
    {ρ : Operator D} (hρ : ρ.trace = 1) (X : Matrix (Fin D) (Fin E) ℂ)
    (hX : X * Xᴴ = ρ) : IsPurification (fun q => X q.1 q.2) ρ := by
  have hp : PartialTrace (outerProduct (fun q => X q.1 q.2)) = ρ := by
    rw [← purificationMatrix_gram]
    exact hX
  refine ⟨?_, hp⟩
  have ht := congrArg Matrix.trace hp
  rw [trace_partialTrace, trace_outerProduct, hρ] at ht
  exact_mod_cast ht

/-- Two density operators possess purifications attaining their root fidelity as overlap modulus
whenever the ancillary dimension is at least the system dimension. -/
theorem exists_purifications_overlap_eq_froot {D E : ℕ} (hDE : D ≤ E)
    {ρ σ : Operator D} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    ∃ ψ φ : QState (Fin D × Fin E),
      IsPurification ψ ρ ∧ IsPurification φ σ ∧ ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ = Froot ρ σ := by
  let J : Matrix (Fin E) (Fin D) ℂ := (1 : Operator E).submatrix id (Fin.castLE hDE)
  have hJ : J.Isometry := Matrix.submatrix_one_id_right_isometry (Fin.castLE_injective hDE)
  let R := CFC.sqrt ρ
  let S := CFC.sqrt σ
  have hR : Rᴴ = R := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).1
  have hS : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).1
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.1.nonneg
  obtain ⟨U, hUmax⟩ := (Matrix.traceNorm_eq_max_re_tr_U (R * S)).1
  have hU : U.val * U.valᴴ = (1 : Operator D) := by
    ext i j
    by_cases hij : i = j <;>
      simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, hij] using
        congrFun (congrFun U.property.2 i) j
  let X : Matrix (Fin D) (Fin E) ℂ := R * Jᴴ
  let Y : Matrix (Fin D) (Fin E) ℂ := S * U.val * Jᴴ
  have hX : X * Xᴴ = ρ := by
    dsimp [X]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hR,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ J, show Jᴴ * J = 1 from hJ, Matrix.one_mul, hRR]
  have hY : Y * Yᴴ = σ := by
    dsimp [Y]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ J, show Jᴴ * J = 1 from hJ, Matrix.one_mul,
      ← Matrix.mul_assoc U.val U.valᴴ, hU, Matrix.one_mul, hSS]
  let ψ : QState (Fin D × Fin E) := fun q => X q.1 q.2
  let φ : QState (Fin D × Fin E) := fun q => Y q.1 q.2
  have hψ : IsPurification ψ ρ := isPurification_of_amplitude_gram hρ.2 X hX
  have hφ : IsPurification φ σ := isPurification_of_amplitude_gram hσ.2 Y hY
  refine ⟨ψ, φ, hψ, hφ, le_antisymm (purification_overlap_le_froot hDE hψ hφ) ?_⟩
  have hoverlap : Qatlib.Foundations.PureStateMath.Inner ψ φ = (U.val * (R * S)).trace := by
    rw [purificationMatrix_inner]
    change (Xᴴ * Y).trace = _
    dsimp [X, Y]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hR]
    calc
      (J * R * (S * U.val * Jᴴ)).trace = (J * (R * S * U.val) * Jᴴ).trace := by
        simp only [Matrix.mul_assoc]
      _ = (Jᴴ * J * (R * S * U.val)).trace := by
        rw [Matrix.trace_mul_comm _ Jᴴ]
        simp only [Matrix.mul_assoc]
      _ = (R * S * U.val).trace := by rw [show Jᴴ * J = 1 from hJ, Matrix.one_mul]
      _ = (U.val * (R * S)).trace := Matrix.trace_mul_comm _ _
  rw [hoverlap]
  change Matrix.traceNorm (R * S) ≤ _
  rw [← hUmax]
  exact Complex.re_le_norm _

/-- For sufficient ancillary dimension, all purification overlaps are bounded by root fidelity
and some purifications attain equality. This is the root-fidelity form of [Wilde, Theorem
9.2.1][Wilde2017]. -/
theorem g2 :
  ∀ (D E : ℕ), D ≤ E → ∀ (ρ σ : Operator D),
    IsDensityOperator ρ → IsDensityOperator σ →
    (∀ ψ φ : QState (Fin D × Fin E),
      IsPurification ψ ρ → IsPurification φ σ →
      ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ≤ Froot ρ σ) ∧
    (∃ ψ φ : QState (Fin D × Fin E),
      IsPurification ψ ρ ∧ IsPurification φ σ ∧
      ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ = Froot ρ σ) := by
  intro D E hDE ρ σ hρ hσ
  exact ⟨fun _ _ hψ hφ => purification_overlap_le_froot hDE hψ hφ,
    exists_purifications_overlap_eq_froot hDE hρ hσ⟩

/-- Applying a quantum channel to both density operators cannot decrease their root fidelity. -/
theorem froot_channel_le {D E : ℕ} (Λ : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel D E)
    {ρ σ : Operator D} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    Froot ρ σ ≤ Froot (Λ.map ρ) (Λ.map σ) := by
  obtain ⟨ψ, φ, hψ, hφ, hmax⟩ := (g2 D D le_rfl ρ σ hρ hσ).2
  let X : Operator D := fun i j => ψ (i,j)
  let Y : Operator D := fun i j => φ (i,j)
  have hX : X * Xᴴ = ρ := hψ.2
  have hY : Y * Yᴴ = σ := hφ.2
  have hi : Qatlib.Foundations.PureStateMath.Inner ψ φ = (Xᴴ * Y).trace := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, X, Y]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  let Z : Matrix (Fin 2 × Fin D) (Fin D) ℂ :=
    fun q j => if q.1 = 0 then X q.2 j else Y q.2 j
  let H := Qatlib.Concepts.AdaptiveCP.BranchTrace.ChannelAmplification Λ.map 2 (Z * Zᴴ)
  have hH : H.PosSemidef := Λ.completelyPositive 2 _ (Matrix.posSemidef_self_mul_conjTranspose Z)
  let W := CFC.sqrt H
  have hW : W * Wᴴ = H := by
    have hWH : Wᴴ = W := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).1
    rw [hWH]
    exact CFC.sqrt_mul_sqrt_self H hH.nonneg
  let A : Matrix (Fin E) (Fin 2 × Fin E) ℂ := fun i q => W (0,i) q
  let B : Matrix (Fin E) (Fin 2 × Fin E) ℂ := fun i q => W (1,i) q
  have hblocks (a b : Fin 2) :
      (fun i j => (W * Wᴴ) (a,i) (b,j)) =
        Λ.map (fun i j => (Z * Zᴴ) (a,i) (b,j)) := by
    rw [hW]
    rfl
  have hAA : A * Aᴴ = Λ.map ρ := by
    change (fun i j => (W * Wᴴ) (0,i) (0,j)) = _
    rw [hblocks]
    have heq : (fun i j => (Z * Zᴴ) (0,i) (0,j)) = X * Xᴴ := by
      ext i j; simp [Z, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [heq, hX]
  have hBB : B * Bᴴ = Λ.map σ := by
    change (fun i j => (W * Wᴴ) (1,i) (1,j)) = _
    rw [hblocks]
    have heq : (fun i j => (Z * Zᴴ) (1,i) (1,j)) = Y * Yᴴ := by
      ext i j; simp [Z, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [heq, hY]
  have hBA : B * Aᴴ = Λ.map (Y * Xᴴ) := by
    change (fun i j => (W * Wᴴ) (1,i) (0,j)) = _
    rw [hblocks]
    congr 1
  have hab : (Aᴴ * B).trace = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
    rw [Matrix.trace_mul_comm, hBA, Λ.tracePreserving, hi, Matrix.trace_mul_comm Xᴴ Y]
  let J : Matrix (Fin 2 × Fin E) (Fin E) ℂ :=
    (1 : Matrix (Fin 2 × Fin E) (Fin 2 × Fin E) ℂ).submatrix id (fun i => (0,i))
  have hJ : J.Isometry := Matrix.submatrix_one_id_right_isometry
    (show Function.Injective (fun i : Fin E => ((0 : Fin 2),i)) from
      fun _ _ h => congrArg Prod.snd h)
  have h := trace_overlap_le_sqrt_gram_of_isometry J hJ A B
  rwa [hab, hmax, hAA, hBB] at h

/-- Applying a quantum channel to both density operators cannot increase their trace distance. -/
theorem traceDistance_channel_le {D E : ℕ} (Λ : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel D E)
    {ρ σ : Operator D} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    traceDistance (Λ.map ρ) (Λ.map σ) ≤ traceDistance ρ σ := by
  unfold traceDistance
  rw [← map_sub]
  exact div_le_div_of_nonneg_right
    (channel_hermitian_trace_contraction Λ (hρ.1.1.sub hσ.1.1)) (by norm_num)

/-- For normalized pure vectors, half the trace norm of their outer-product difference is at
most the square root of one minus the square of the real part of their inner product. -/
theorem pure_trace_distance_le_re_inner {I : Type} [Fintype I] [DecidableEq I]
    (u v : QState I) (hu : Normalized u) (hv : Normalized v) :
    (outerProduct u - outerProduct v).traceNorm / 2 ≤
      Real.sqrt (1 - (Qatlib.Foundations.PureStateMath.Inner u v).re ^ 2) := by
  have huN : (∑ i, Complex.normSq (u i)) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq, Normalized] using hu
  have hvN : (∑ i, Complex.normSq (v i)) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq, Normalized] using hv
  have hcross (i : I) : (u i * (starRingEnd ℂ) (v i)).re =
      ((starRingEnd ℂ) (u i) * v i).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hplus : (∑ i, Complex.normSq ((u + v) i)) = 2 + 2 * (Qatlib.Foundations.PureStateMath.Inner u v).re := by
    simp only [Pi.add_apply, Complex.normSq_add]
    simp_rw [hcross]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      huN, hvN, ← Complex.re_sum, ← inner_apply]
    ring
  have hminus : (∑ i, Complex.normSq ((u - v) i)) = 2 - 2 * (Qatlib.Foundations.PureStateMath.Inner u v).re := by
    simp only [Pi.sub_apply, Complex.normSq_sub]
    simp_rw [hcross]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      huN, hvN, ← Complex.re_sum, ← inner_apply]
    ring
  let A := Matrix.vecMulVec (u + v) (star (u - v))
  let B := Matrix.vecMulVec (u - v) (star (u + v))
  have hAB : outerProduct u - outerProduct v = (1 / 2 : ℂ) • (A + B) := by
    ext i j
    simp only [A, B, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      outerProduct_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.sub_apply,
      Pi.star_apply, star_sub, star_add, smul_eq_mul, Complex.star_def]
    ring
  have hA := traceNorm_rankOne_le (u + v) (u - v)
  have hB := traceNorm_rankOne_le (u - v) (u + v)
  rw [hplus, hminus] at hA
  rw [hplus, hminus, mul_comm (2 - _)] at hB
  have ht := Matrix.traceNorm_add_le A B
  have htr : (outerProduct u - outerProduct v).traceNorm ≤
      Real.sqrt ((2 + 2 * (Qatlib.Foundations.PureStateMath.Inner u v).re) * (2 - 2 * (Qatlib.Foundations.PureStateMath.Inner u v).re)) := by
    rw [hAB, Matrix.traceNorm_smul]
    norm_num
    change (1 / 2 : ℝ) * (A + B).traceNorm ≤ _
    change A.traceNorm ≤ _ at hA
    change B.traceNorm ≤ _ at hB
    linarith
  have hprod : (2 + 2 * (Qatlib.Foundations.PureStateMath.Inner u v).re) * (2 - 2 * (Qatlib.Foundations.PureStateMath.Inner u v).re) =
      4 * (1 - (Qatlib.Foundations.PureStateMath.Inner u v).re ^ 2) := by ring
  have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hprod, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at htr
  norm_num [h4] at htr
  linarith

/-- Multiplying a vector by a complex scalar of modulus one preserves its outer-product matrix. -/
private theorem phase_outerProduct {I : Type} [Fintype I] [DecidableEq I]
    (c : ℂ) (hc : ‖c‖ = 1) (v : QState I) : outerProduct (c • v) = outerProduct v := by
  have hcc : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  ext i j
  change (c * v i) * star (c * v j) = v i * star (v j)
  rw [star_mul]
  calc
    (c * v i) * (star (v j) * star c) = (c * star c) * (v i * star (v j)) := by ring
    _ = _ := by rw [hcc, one_mul]

/-- The trace distance between density operators is at most `Real.sqrt (1 - Froot ρ σ ^ 2)`. -/
theorem traceDistance_le_sqrt_one_sub_froot_sq {D : ℕ} {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    traceDistance ρ σ ≤ Real.sqrt (1 - Froot ρ σ ^ 2) := by
  obtain ⟨ψ, φ, hψ, hφ, hmax⟩ := (g2 D D le_rfl ρ σ hρ hσ).2
  obtain ⟨c, hc, hz⟩ :=
      Complex.exists_norm_eq_mul_self (Qatlib.Foundations.PureStateMath.Inner ψ φ)
  have houter : outerProduct (c • φ) = outerProduct φ := phase_outerProduct c hc φ
  have hnorm : Normalized (c • φ) := by
    simpa only [Normalized, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hc,
      one_pow, one_mul] using hφ.1
  have hi : Qatlib.Foundations.PureStateMath.Inner ψ (c • φ) = (Froot ρ σ : ℂ) := by
    calc
      Qatlib.Foundations.PureStateMath.Inner ψ (c • φ) = c * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
        simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply,
            Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ : ℂ) := hz.symm
      _ = _ := congrArg (fun x : ℝ => (x : ℂ)) hmax
  have hrightψ : Matrix.traceRight (outerProduct ψ) = ρ := hψ.2
  have hrightφ : Matrix.traceRight (outerProduct (c • φ)) = σ := by rw [houter]; exact hφ.2
  have hcontract := Qatlib.Concepts.ReferenceError.DensityToRaw.traceRight_hermitian_trace_contraction
    (outerProduct ψ - outerProduct (c • φ))
    ((outerProduct_posSemidef ψ).1.sub (outerProduct_posSemidef (c • φ)).1)
  rw [Matrix.traceRight_sub, hrightψ, hrightφ] at hcontract
  have h := pure_trace_distance_le_re_inner ψ (c • φ) hψ.1 hnorm
  rw [hi, Complex.ofReal_re] at h
  exact (div_le_div_of_nonneg_right hcontract (by norm_num : (0 : ℝ) ≤ 2)).trans h

/-- For positive semidefinite `R` and `S`, the real trace of `(R - S) * (R - S)` is at most the
trace norm of `R * R - S * S`. -/
theorem positive_square_difference_trace_le {I : Type} [Fintype I] [DecidableEq I]
    {R S : Matrix I I ℂ} (hR : R.PosSemidef) (hS : S.PosSemidef) :
    ((R - S) * (R - S)).trace.re ≤ (R * R - S * S).traceNorm := by
  classical
  let hH : (R - S).IsHermitian := hR.1.sub hS.1
  let U := hH.eigenvectorUnitary
  let l := hH.eigenvalues
  have hUl : U.valᴴ * U.val = 1 := (Matrix.mem_unitaryGroup_iff').mp U.property
  have hUr : U.val * U.valᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp U.property
  let A := U.valᴴ * R * U.val
  let B := U.valᴴ * S * U.val
  have hA : A.PosSemidef := hR.conjTranspose_mul_mul_same U.val
  have hB : B.PosSemidef := hS.conjTranspose_mul_mul_same U.val
  have hconjMul (X Y : Matrix I I ℂ) :
      (U.valᴴ * X * U.val) * (U.valᴴ * Y * U.val) = U.valᴴ * (X * Y) * U.val := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.val U.valᴴ, hUr, Matrix.one_mul]
  have htrace (X : Matrix I I ℂ) : (U.valᴴ * X * U.val).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUr, Matrix.one_mul]
  have hdiag : A - B = Matrix.diagonal (fun i => (l i : ℂ)) := by
    have hspec : R - S = U.val * Matrix.diagonal (fun i => (l i : ℂ)) * U.valᴴ :=
      hH.spectral_theorem
    change U.valᴴ * R * U.val - U.valᴴ * S * U.val = _
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.valᴴ U.val, hUl, Matrix.one_mul, Matrix.mul_one]
  have hdelta : U.valᴴ * (R * R - S * S) * U.val = A * A - B * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← hconjMul R R, ← hconjMul S S]
  have hdiff : A * A - B * B =
      Matrix.diagonal (fun i => (l i : ℂ)) * A + B * Matrix.diagonal (fun i => (l i : ℂ)) := by
    rw [← hdiag]
    noncomm_ring
  have hsq : U.valᴴ * ((R - S) * (R - S)) * U.val =
      Matrix.diagonal (fun i => (l i : ℂ)) * Matrix.diagonal (fun i => (l i : ℂ)) := by
    rw [← hconjMul, ← hdiag]
    simp only [A, B, Matrix.mul_sub, Matrix.sub_mul]
  have hsqtrace : ((R - S) * (R - S)).trace.re = ∑ i, l i ^ 2 := by
    rw [← htrace ((R - S) * (R - S)), hsq, Matrix.diagonal_mul_diagonal]
    simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, pow_two]
  let d : I → ℝ := fun i => if 0 ≤ l i then 1 else -1
  let Dm : Matrix I I ℂ := Matrix.diagonal (fun i => (d i : ℂ))
  have hDm : Dmᴴ * Dm = 1 := by
    dsimp only [Dm]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hl : 0 ≤ l i <;> simp [d, Matrix.diagonal, hl]
    · simp [Matrix.diagonal, hij]
  let V := U.val * Dm * U.valᴴ
  have hV : V.Isometry := by
    change Vᴴ * V = 1
    dsimp [V]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.valᴴ U.val, hUl, Matrix.one_mul,
      ← Matrix.mul_assoc Dmᴴ Dm, hDm, Matrix.one_mul, hUr]
  have hn : (V * (R * R - S * S)).traceNorm = (R * R - S * S).traceNorm := by
    apply Matrix.traceNorm_isometry_left
    ext i j
    by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using congrFun (congrFun hV i) j
  have hb : (V * (R * R - S * S)).trace.re ≤ (R * R - S * S).traceNorm := by
    exact (Complex.re_le_norm _).trans ((Matrix.abs_trace_le_traceNorm _).trans_eq hn)
  have ht : (V * (R * R - S * S)).trace =
      (Dm * (A * A - B * B)).trace := by
    rw [← hdelta]
    dsimp [V]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm U.val (Dm * (U.valᴴ * (R * R - S * S)))
  have hentry : (V * (R * R - S * S)).trace.re =
      ∑ i, d i * l i * ((A i i).re + (B i i).re) := by
    rw [ht, hdiff]
    simp only [Dm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.trace,
      Matrix.diag_apply, Matrix.add_apply, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      zero_mul, mul_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hscalar (i : I) : l i ^ 2 ≤ d i * l i * ((A i i).re + (B i i).re) := by
    have hposA : 0 ≤ (A i i).re := (Complex.nonneg_iff.mp hA.diag_nonneg).1
    have hposB : 0 ≤ (B i i).re := (Complex.nonneg_iff.mp hB.diag_nonneg).1
    have hdiag' := congrArg Complex.re (congrFun (congrFun hdiag i) i)
    simp only [Matrix.sub_apply, Complex.sub_re, Matrix.diagonal_apply_eq,
      Complex.ofReal_re] at hdiag'
    by_cases hl : 0 ≤ l i
    · simp only [d, if_pos hl, one_mul]
      nlinarith
    · simp only [d, if_neg hl, neg_one_mul]
      nlinarith
  rw [hsqtrace]
  exact (Finset.sum_le_sum (fun i _ => hscalar i)).trans (hentry ▸ hb)

/-- One minus the root fidelity of two density operators is at most their trace distance. -/
theorem one_sub_froot_le_traceDistance {D : ℕ} {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    1 - Froot ρ σ ≤ traceDistance ρ σ := by
  let R := CFC.sqrt ρ
  let S := CFC.sqrt σ
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.1.nonneg
  have h := positive_square_difference_trace_le hR hS
  rw [hRR, hSS] at h
  have hexp : (R - S) * (R - S) = R * R + S * S - (R * S + S * R) := by
    noncomm_ring
  have ht : ((R - S) * (R - S)).trace.re = 2 - 2 * (R * S).trace.re := by
    rw [hexp, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add, hRR, hSS,
      hρ.2, hσ.2, Matrix.trace_mul_comm S R]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    ring
  have hf : (R * S).trace.re ≤ Froot ρ σ :=
    (Complex.re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  rw [ht] at h
  unfold traceDistance
  linarith

/-- The Fuchs–van de Graaf inequalities bound trace distance between `1 - Froot ρ σ` and
`Real.sqrt (1 - Froot ρ σ ^ 2)`; quantum channels contract trace distance and increase root
fidelity. Compare [Fuchs and van de Graaf, Theorem 1][FuchsVanDeGraaf1999] and [Wilde,
Theorem 9.3.1][Wilde2017]. -/
theorem g3 :
  ∀ (D : ℕ) (ρ σ : Operator D), IsDensityOperator ρ → IsDensityOperator σ →
    (1 - Froot ρ σ ≤ traceDistance ρ σ ∧
      traceDistance ρ σ ≤ Real.sqrt (1 - (Froot ρ σ) ^ 2)) ∧
    (∀ (E : ℕ) (Λ : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel D E),
      traceDistance (Λ.map ρ) (Λ.map σ) ≤ traceDistance ρ σ ∧
        Froot ρ σ ≤ Froot (Λ.map ρ) (Λ.map σ)) := by
  intro D ρ σ hρ hσ
  exact ⟨⟨one_sub_froot_le_traceDistance hρ hσ,
    traceDistance_le_sqrt_one_sub_froot_sq hρ hσ⟩,
    fun _ Λ => ⟨traceDistance_channel_le Λ hρ hσ, Qatlib.Concepts.MixedFidelity.FidelityMetric.froot_channel_le Λ hρ hσ⟩⟩

end Qatlib.Concepts.MixedFidelity.FidelityMetric
