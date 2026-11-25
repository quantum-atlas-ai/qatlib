/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DoubleBracket22.MainResults.Algebra.Orthogonality
public import Qatlib.Papers.DoubleBracket22.MainResults.Algebra.CommutatorFormulas
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Off-diagonal Hilbert–Schmidt decay

Equations (22) and (217) of arXiv:2206.11772v4 use the same trace
identity, once for an exponential rotation and once for a path solving
the GWW flow equation.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius ComplexOrder
open Qatlib.Papers.DoubleBracket22.MainResults.Model
open Qatlib.Papers.DoubleBracket22.MainResults.Algebra

namespace Qatlib.Papers.DoubleBracket22.MainResults

variable {D : ℕ}

/-- The paper's off-diagonal projection as a continuous real-linear map. -/
private def offDiagCLM : Mat D →L[ℝ] Mat D :=
  ((LinearMap.id : Mat D →ₗ[ℝ] Mat D) -
    (Matrix.diagonalLinearMap (Fin D) ℝ ℂ).comp (Matrix.diagLinearMap (Fin D) ℝ ℂ)
  ).toContinuousLinearMap

/-- Matrix adjoint is continuous and real-linear in finite dimension. -/
private def adjointCLM : Mat D →L[ℝ] Mat D :=
  (show Mat D →ₗ[ℝ] Mat D from
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun r A => by simp only [Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply] }
  ).toContinuousLinearMap

/-- The real trace as a continuous linear functional. -/
private def traceReCLM : Mat D →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap (Fin D) ℝ ℂ).toContinuousLinearMap

/-- The off-diagonal projection preserves a Hermitian matrix's adjoint symmetry. -/
private theorem offDiag_conjTranspose (A : Mat D) : (offDiag A)ᴴ = offDiag Aᴴ := by
  simp only [offDiag, diagPart, Matrix.conjTranspose_sub, Matrix.diagonal_conjTranspose]
  rfl

/-- The canonical bracket of a Hermitian matrix is skew-Hermitian. -/
private theorem canonicalBracket_skew (J : Mat D) (hJ : Jᴴ = J) :
    (canonicalBracket J)ᴴ = -canonicalBracket J := by
  have hd : (diagPart J)ᴴ = diagPart J := by
    rw [diagPart, Matrix.diagonal_conjTranspose]
    change diagPart Jᴴ = diagPart J
    rw [hJ]
  rw [canonicalBracket, commMat, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hJ, hd, neg_sub]

/-- The real Hilbert–Schmidt pairing computes the trace of the off-diagonal
double bracket. The diagonal component drops out by Lemma 8. -/
private theorem trace_offDiag_bracket (J W : Mat D) (hW : Wᴴ = -W) :
    (offDiag J * offDiag (commMat W J)).trace.re = -hsInner W (canonicalBracket J) := by
  have hbr : commMat J (offDiag J) = canonicalBracket J := by
    simp only [commMat, offDiag, canonicalBracket]
    noncomm_ring
  rw [show offDiag (commMat W J) = commMat W J - diagPart (commMat W J) from rfl,
    mul_sub, Matrix.trace_sub, lemma8_diagonalOffDiagonalOrthogonality, sub_zero,
    lemma6_traceCyclicity, hbr, hsInner, hW, neg_mul, Matrix.trace_neg, Complex.neg_re, neg_neg]

/-- At a Hermitian point with tangent `[W,J]`, the derivative of squared
off-diagonal Hilbert–Schmidt norm is the canonical pairing in Eq. (22). -/
theorem offDiag_hasDerivAt_doubleBracket (F : ℝ → Mat D) (t : ℝ) (W : Mat D)
    (hF : HasDerivAt F (commMat W (F t)) t) (hJ : (F t)ᴴ = F t) (hW : Wᴴ = -W) :
    HasDerivAt (fun s => hsNormSq (offDiag (F s))) (-2 * hsInner W (canonicalBracket (F t))) t := by
  have hB : (commMat W (F t))ᴴ = commMat W (F t) := by
    simp only [commMat, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJ, hW]
    noncomm_ring
  have hoff : HasDerivAt (fun s => offDiag (F s)) (offDiag (commMat W (F t))) t :=
    offDiagCLM.hasFDerivAt.comp_hasDerivAt t hF
  have hadj :
      HasDerivAt (fun s => (offDiag (F s))ᴴ) (offDiag (commMat W (F t))) t := by
    have h := (adjointCLM (D := D)).hasFDerivAt.comp_hasDerivAt t hoff
    change HasDerivAt (fun s => (offDiag (F s))ᴴ) (offDiag (commMat W (F t)))ᴴ t at h
    simpa only [offDiag_conjTranspose, hB] using h
  have hd := (traceReCLM (D := D)).hasFDerivAt.comp_hasDerivAt t (hadj.mul hoff)
  change HasDerivAt (fun s => hsNormSq (offDiag (F s)))
    ((offDiag (commMat W (F t)) * offDiag (F t) +
      (offDiag (F t))ᴴ * offDiag (commMat W (F t))).trace.re) t at hd
  rw [offDiag_conjTranspose, hJ, Matrix.trace_add, Matrix.trace_mul_comm
    (offDiag (commMat W (F t))) (offDiag (F t)), Complex.add_re, trace_offDiag_bracket (F t) W hW,
    ← two_mul, mul_neg, ← neg_mul] at hd
  exact hd

set_option backward.isDefEq.respectTransparency false in
/-- The initial tangent of the rotation in Eq. (18) is `[W,J]`. -/
private theorem rotation_hasDerivAt_zero (W J : Mat D) :
    HasDerivAt (fun s => rotation s W J) (commMat W J) 0 := by
  have hp := (hasDerivAt_exp_smul_const (𝕂 := ℝ) W 0).mul_const J
  have hn : HasDerivAt (fun t : ℝ => NormedSpace.exp (-(t • W))) (-W) 0 := by
    simpa only [smul_neg, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-W) 0
  simpa only [rotation, commMat, Pi.mul_def, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul, mul_one,
    mul_neg, sub_eq_add_neg] using hp.mul hn

/-- Eq. (22): the first derivative at zero of the off-diagonal norm along
the double-bracket rotation, for a Hermitian association. -/
theorem lemma2_pinchedNorm_hasDerivAt (ΔZ : Mat D → Mat D) (J : Mat D)
    (hJ : Jᴴ = J) (hΔ : (ΔZ J)ᴴ = ΔZ J) :
    HasDerivAt (fun s => hsNormSq (offDiag (rotation s (assocBracket ΔZ J) J)))
      (-2 * hsInner (assocBracket ΔZ J) (canonicalBracket J)) 0 := by
  have hskew : (assocBracket ΔZ J)ᴴ = -assocBracket ΔZ J := by
    rw [assocBracket, commMat, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hJ, hΔ, neg_sub]
  have hzero : rotation 0 (assocBracket ΔZ J) J = J := by simp [rotation, NormedSpace.exp_zero]
  have hrot : HasDerivAt (fun s => rotation s (assocBracket ΔZ J) J)
      (commMat (assocBracket ΔZ J) (rotation 0 (assocBracket ΔZ J) J)) 0 := by
    rw [hzero]
    exact rotation_hasDerivAt_zero (assocBracket ΔZ J) J
  have hherm : (rotation 0 (assocBracket ΔZ J) J)ᴴ = rotation 0 (assocBracket ΔZ J) J := by
    rwa [hzero]
  have h := offDiag_hasDerivAt_doubleBracket _ 0 _ hrot hherm hskew
  simpa only [hzero] using h

/-- Proposition 18, Eq. (217), at any nonnegative time of a Hermitian GWW flow. -/
theorem prop18_gwwFlow_monotonicity (Φ : ℝ → Mat D → Mat D) (hΦ : IsGWWFlowMap Φ)
    (J : Mat D) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hJ : (Φ ℓ J)ᴴ = Φ ℓ J) :
    HasDerivAt (fun s => hsNormSq (offDiag (Φ s J)))
      (-2 * hsNormSq (canonicalBracket (Φ ℓ J))) ℓ :=
  offDiag_hasDerivAt_doubleBracket (fun s => Φ s J) ℓ _ (hΦ.2 ℓ hℓ J) hJ
    (canonicalBracket_skew (Φ ℓ J) hJ)

/-- A Hermitian GWW flow has nonincreasing off-diagonal Hilbert–Schmidt energy
on the nonnegative time axis. -/
theorem prop18_gwwFlow_antitone (Φ : ℝ → Mat D → Mat D) (hΦ : IsGWWFlowMap Φ)
    (J : Mat D) (hHerm : ∀ t, 0 ≤ t → (Φ t J)ᴴ = Φ t J) :
    AntitoneOn (fun s => hsNormSq (offDiag (Φ s J))) (Set.Ici 0) := by
  have h (t : ℝ) (ht : 0 ≤ t) := prop18_gwwFlow_monotonicity Φ hΦ J ht (hHerm t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun t ht => (h t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (h t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(h t (interior_subset ht)).deriv]
    have hnn : 0 ≤ hsNormSq (canonicalBracket (Φ t J)) := by
      unfold hsNormSq hsInner
      have hp := (Matrix.posSemidef_conjTranspose_mul_self (canonicalBracket (Φ t J))).trace_nonneg
      exact (Complex.le_def.mp hp).1
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hnn

/-- A unitary lift preserves the Hermitian hypothesis in Proposition 18,
so the off-diagonal energy is antitone from a Hermitian start. -/
theorem prop18_unitaryLift_antitone (Φ U : ℝ → Mat D → Mat D) (hΦ : IsGWWFlowMap Φ)
    (hU : IsUnitaryLift Φ U) (J : Mat D) (hJ : Jᴴ = J) :
    AntitoneOn (fun s => hsNormSq (offDiag (Φ s J))) (Set.Ici 0) := by
  apply prop18_gwwFlow_antitone Φ hΦ J
  intro t ht
  rw [hU.2.2 t ht J, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]

end Qatlib.Papers.DoubleBracket22.MainResults
