/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization

open Qatlib.Concepts.SchattenDiamond.DiamondNorm

set_option backward.isDefEq.respectTransparency false

/-!
# Completely bounded trace-norm duality and rank-one maximization

This file formalizes Section 1 (Eqs. (1)–(2), p. 3) of [Watrous, 2013][Watrous2013]:

* Eq. (1) (`completeBoundedTrace_dual_spectral`): `|||Φ|||₁ = |||Φ*|||∞`, i.e. the completely
  bounded trace norm (`finiteDiamondNorm`) of a linear map between matrix spaces equals the
  completely bounded spectral norm (`finiteDiamondSpectralNorm`) of its Hilbert–Schmidt
  adjoint `hsAdjoint`.
* Eq. (2) (`finiteDiamondNorm_eq_rankOneSup`, `rankOne_max_attained`): the completely bounded
  trace norm equals the supremum (attained when `D > 0`) of `‖(Φ ⊗ 1)(u v*)‖₁` over unit joint
  vectors `u, v ∈ X ⊗ X`.

## Main statements

* `finiteDiamondNorm_eq_rankOneSup`: rank-one supremum formula for `finiteDiamondNorm` (Eq. (2)).
* `rankOne_max_attained`: attainment of the rank-one supremum for `0 < D`.
* `hsAdjoint`: the Hilbert–Schmidt adjoint `T*` satisfying `Tr(Yᴴ (T X)) = Tr((T* Y)ᴴ X)`.
* `completeBoundedTrace_dual_spectral`: duality `finiteDiamondNorm T = finiteDiamondSpectralNorm T*`
  (Eq. (1)).

## References

* [Watrous, 2013][Watrous2013]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ENNReal BigOperators ComplexOrder

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceDuality

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace.CompletelyPositive
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.RandCompile.ChannelBudget

/-- A unit joint vector of `X ⊗ X` with `X = ℂ^D`: the pair `u v*` ranges over the
rank-one operators of trace norm one ([Watrous, 2013][Watrous2013], Eq. (2), p. 3). -/
def UnitJoint (D : ℕ) : Type :=
  {u : Fin D × Fin D → ℂ // ∑ a, star (u a) * u a = 1}

/-- The value `‖(Φ ⊗ 1)(u v*)‖₁` attached to a pair of joint vectors, as an
extended nonnegative real ([Watrous, 2013][Watrous2013], Eq. (2), p. 3). -/
def rankOneValue {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (u v : Fin D × Fin D → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.traceNorm (tensorLeft T (fun a b => u a * star (v b))))

/-- Supremum of `rankOneValue` over unit joint vectors ([Watrous, 2013][Watrous2013], p. 3). -/
def rankOneSup {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ u : UnitJoint D, ⨆ v : UnitJoint D, rankOneValue T u.1 v.1

/-- **Eq. (2)** ([Watrous, 2013][Watrous2013], §1, p. 3): the completely bounded trace norm
equals the supremum of `‖(Φ ⊗ 1)(u v*)‖₁` over unit joint vectors `u, v`. -/
theorem finiteDiamondNorm_eq_rankOneSup {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondNorm T = rankOneSup T := by
  rw [finiteDiamondNorm_eq_choi]
  unfold rankOneSup diamondChoiValue
  apply le_antisymm
  · refine iSup_le fun ρ => iSup_le fun σ => ?_
    rw [diamondChoiScore_as_raw]
    exact le_iSup_of_le ⟨densityVector ρ, densityVector_normalized ρ⟩
      (le_iSup_of_le ⟨densityVector σ, densityVector_normalized σ⟩ le_rfl)
  · refine iSup_le fun u => iSup_le fun v => ?_
    obtain ⟨ρ, σ, hρσ⟩ := raw_rankOne_as_diamondChoiScore T u.1 v.1 u.2 v.2
    rw [rankOneValue, hρσ]
    exact le_iSup_of_le ρ (le_iSup_of_le σ le_rfl)

/-- **Eq. (2), maximum form** ([Watrous, 2013][Watrous2013], §1, p. 3): for positive input
dimension the rank-one supremum is attained at an actual pair of unit joint vectors. -/
theorem rankOne_max_attained {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ u v : Fin D × Fin D → ℂ,
      (∑ a, star (u a) * u a = 1) ∧ (∑ a, star (v a) * v a = 1) ∧
      finiteDiamondNorm T = rankOneValue T u v := by
  obtain ⟨ρ, σ, hnorm, -⟩ := diamondChoi_attained hD T
  refine ⟨densityVector ρ, densityVector σ, densityVector_normalized ρ,
    densityVector_normalized σ, ?_⟩
  rw [rankOneValue, ← diamondChoiScore_as_raw]
  exact hnorm

/-- The finite-reference completely bounded spectral norm `|||S|||∞`, defined with the L2
operator (spectral) norm in place of the trace norm:
`⨆_{r} ⨆_{‖X‖∞ ≤ 1} ‖(S ⊗ 1_{ℂ^r})(X)‖∞` ([Watrous, 2013][Watrous2013], §1, p. 3). -/
def finiteDiamondSpectralNorm {M N : ℕ} (S : Operator M →ₗ[ℂ] Operator N) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ X : Matrix (Fin M × Fin r) (Fin M × Fin r) ℂ,
    if ‖X‖ ≤ 1 then ENNReal.ofReal ‖tensorLeft S X‖ else 0

/-- Elementary matrix unit `|j⟩⟨i|` on `ℂ^D`. -/
private def basisOp {D : ℕ} (j i : Fin D) : Operator D :=
  fun a b => if a = j then if b = i then 1 else 0 else 0

private lemma matrix_eq_sum_basisOp {D : ℕ} (X : Operator D) :
    X = ∑ j : Fin D, ∑ i : Fin D, X j i • basisOp j i := by
  ext a b
  simp [basisOp, Matrix.sum_apply]

/-- The Hilbert–Schmidt adjoint `T* : Operator E →ₗ[ℂ] Operator D` of a linear map `T`,
defined entrywise by `(T* Y)_{j,i} = conj(Tr(Yᴴ (T E_{j,i})))`. -/
def hsAdjoint {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Operator E →ₗ[ℂ] Operator D where
  toFun Y j i := star (Matrix.trace (Yᴴ * T (basisOp j i)))
  map_add' Y₁ Y₂ := by
    ext j i
    simp [Matrix.conjTranspose_add, add_mul, Matrix.trace_add]
  map_smul' c Y := by
    ext j i
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      star_mul, star_star, RingHom.id_apply, Matrix.smul_apply]
    ring

/-- Base Hilbert–Schmidt adjoint pairing `Tr(Yᴴ (T X)) = Tr((T* Y)ᴴ X)`. -/
theorem hsAdjoint_pairing {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (X : Operator D) (Y : Operator E) :
    Matrix.trace (Yᴴ * T X) = Matrix.trace ((hsAdjoint T Y)ᴴ * X) := by
  conv_lhs => rw [matrix_eq_sum_basisOp X]
  simp only [map_sum, map_smul, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul]
  calc ∑ x : Fin D, ∑ x_1 : Fin D, X x x_1 * Matrix.trace (Yᴴ * T (basisOp x x_1))
      = ∑ i : Fin D, ∑ j : Fin D, star (hsAdjoint T Y j i) * X j i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hsAdjoint, LinearMap.coe_mk, AddHom.coe_mk, star_star]
        ring
    _ = Matrix.trace ((hsAdjoint T Y)ᴴ * X) := by
        simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Amplified Hilbert–Schmidt pairing `(T ⊗ I_r)* = T* ⊗ I_r`. -/
private theorem tensorLeft_hsAdjoint_pairing {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (Y : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ) :
    Matrix.trace (Yᴴ * tensorLeft T X) = Matrix.trace ((tensorLeft (hsAdjoint T) Y)ᴴ * X) := by
  let Xblk (l k : Fin r) : Operator D := fun i j => X (i, l) (j, k)
  let Yblk (l k : Fin r) : Operator E := fun a b => Y (a, l) (b, k)
  have hlhs : Matrix.trace (Yᴴ * tensorLeft T X) =
      ∑ k : Fin r, ∑ l : Fin r, Matrix.trace ((Yblk l k)ᴴ * T (Xblk l k)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      tensorLeft, Fintype.sum_prod_type, Xblk, Yblk]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc (∑ a : Fin E, ∑ b : Fin E, ∑ l : Fin r,
            star (Y (b, l) (a, k)) * T (fun i j => X (i, l) (j, k)) b a)
        = ∑ a : Fin E, ∑ l : Fin r, ∑ b : Fin E,
            star (Y (b, l) (a, k)) * T (fun i j => X (i, l) (j, k)) b a :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ l : Fin r, ∑ a : Fin E, ∑ b : Fin E,
            star (Y (b, l) (a, k)) * T (fun i j => X (i, l) (j, k)) b a :=
          Finset.sum_comm
  have hrhs : Matrix.trace ((tensorLeft (hsAdjoint T) Y)ᴴ * X) =
      ∑ k : Fin r, ∑ l : Fin r, Matrix.trace ((hsAdjoint T (Yblk l k))ᴴ * Xblk l k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      tensorLeft, Fintype.sum_prod_type, Xblk, Yblk]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc (∑ i : Fin D, ∑ j : Fin D, ∑ l : Fin r,
            star (hsAdjoint T (fun a b => Y (a, l) (b, k)) j i) * X (j, l) (i, k))
        = ∑ i : Fin D, ∑ l : Fin r, ∑ j : Fin D,
            star (hsAdjoint T (fun a b => Y (a, l) (b, k)) j i) * X (j, l) (i, k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l : Fin r, ∑ i : Fin D, ∑ j : Fin D,
            star (hsAdjoint T (fun a b => Y (a, l) (b, k)) j i) * X (j, l) (i, k) :=
          Finset.sum_comm
  rw [hlhs, hrhs]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact hsAdjoint_pairing T (Xblk l k) (Yblk l k)

/-- Euclidean norm squared of `WithLp.toLp 2 u` from `∑ a, star (u a) * u a = 1`. -/
private lemma toLp_norm_eq_one {I : Type} [Fintype I] (u : I → ℂ)
    (hu : ∑ a, star (u a) * u a = 1) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ I)‖ = 1 := by
  have hsq : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ I)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hre := congrArg Complex.re hu
    simp only [Complex.one_re] at hre
    rw [← hre]
    change ∑ a : I, ‖u a‖ ^ 2 = (∑ a : I, star (u a) * u a).re
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hmul : star (u a) * u a = ((‖u a‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [hmul, Complex.ofReal_re]
  nlinarith [norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℂ I), hsq]

/-- Trace-spectral Hölder inequality `‖Tr(Bᴴ A)‖ ≤ ‖B‖ · traceNorm A` via the rank-one SVD
decomposition `diamond_svd_trace_decomposition`. -/
private theorem norm_trace_conjTranspose_mul_le {I : Type} [Fintype I] [DecidableEq I]
    (B A : Matrix I I ℂ) :
    ‖Matrix.trace (Bᴴ * A)‖ ≤ ‖B‖ * Matrix.traceNorm A := by
  obtain ⟨s, u, v, hs_nonneg, hA_eq, -, htn_eq, huv_unit⟩ := diamond_svd_trace_decomposition A
  have crank : ∀ i : I,
      ‖Matrix.trace (Bᴴ * Matrix.of (fun a b => u i a * star (v i b)))‖ ≤ ‖B‖ := by
    intro i
    let ui : EuclideanSpace ℂ I := WithLp.toLp 2 (u i)
    let vi : EuclideanSpace ℂ I := WithLp.toLp 2 (v i)
    have hui : ‖ui‖ = 1 := toLp_norm_eq_one (u i) (huv_unit i).1
    have hvi : ‖vi‖ = 1 := toLp_norm_eq_one (v i) (huv_unit i).2
    have htr : Matrix.trace (Bᴴ * Matrix.of (fun a b => u i a * star (v i b))) =
        inner ℂ (B.toEuclideanLin vi) ui := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, dotProduct, Pi.star_apply]
      change (∑ b : I, ∑ a : I, star (B a b) * (u i a * star (v i b))) =
        ∑ a : I, u i a * star ((B *ᵥ v i) a)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Matrix.mulVec, dotProduct, star_sum, star_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [htr]
    calc ‖inner ℂ (B.toEuclideanLin vi) ui‖
        ≤ ‖B.toEuclideanLin vi‖ * ‖ui‖ := norm_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖vi‖) * ‖ui‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mulVec B vi) (norm_nonneg _)
      _ = ‖B‖ := by rw [hui, hvi, mul_one, mul_one]
  conv_lhs => rw [hA_eq]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  calc ‖∑ i : I, (s i : ℂ) * Matrix.trace (Bᴴ * Matrix.of (fun a b => u i a * star (v i b)))‖
      ≤ ∑ i : I, ‖(s i : ℂ) * Matrix.trace (Bᴴ * Matrix.of (fun a b => u i a * star (v i b)))‖ :=
        norm_sum_le _ _
    _ = ∑ i : I, s i * ‖Matrix.trace (Bᴴ * Matrix.of (fun a b => u i a * star (v i b)))‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg i)]
    _ ≤ ∑ i : I, s i * ‖B‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (crank i) (hs_nonneg i)
    _ = ‖B‖ * Matrix.traceNorm A := by
        rw [← Finset.sum_mul, htn_eq, mul_comm]

/-- A unitary matrix has L2 operator norm at most `1`. -/
private lemma opNorm_le_one_of_unitary {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound (LinearMap.toContinuousLinearMap U.toEuclideanLin)
    zero_le_one fun x => ?_
  rw [one_mul, LinearMap.coe_toContinuousLinearMap']
  have hsq : ‖U.toEuclideanLin x‖ ^ 2 = ‖x‖ ^ 2 := by
    have hinner : inner ℂ (U.toEuclideanLin x) (U.toEuclideanLin x) = inner ℂ x x := by
      rw [← LinearMap.adjoint_inner_left, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      have hcomp : Uᴴ.toEuclideanLin (U.toEuclideanLin x) = (Uᴴ * U).toEuclideanLin x := by
        ext k
        change (Uᴴ *ᵥ (U *ᵥ x.ofLp)) k = ((Uᴴ * U) *ᵥ x.ofLp) k
        exact congrFun (Matrix.mulVec_mulVec x.ofLp Uᴴ U) k
      rw [hcomp, hU]
      have hone : (1 : Matrix I I ℂ).toEuclideanLin x = x := by
        ext k
        exact congrFun (Matrix.one_mulVec x.ofLp) k
      rw [hone]
    have hc := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (U.toEuclideanLin x)).symm.trans
      (hinner.trans (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x))
    simp only [RCLike.ofReal_eq_complex_ofReal] at hc
    exact_mod_cast hc
  nlinarith [norm_nonneg (U.toEuclideanLin x), norm_nonneg x, hsq]

/-- Polar attainment for trace norm: for any square matrix `A`, there exists `U` with `‖U‖ ≤ 1`
such that `‖Tr(Uᴴ A)‖ = traceNorm A`. -/
private theorem exists_opNorm_le_one_trace_eq_traceNorm {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, ‖U‖ ≤ 1 ∧ ‖Matrix.trace (Uᴴ * A)‖ = Matrix.traceNorm A := by
  classical
  obtain ⟨V, W, hA⟩ := Matrix.exists_svd_sqrt_eigenvalues A
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose
  let s : I → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hV : V.valᴴ * V.val = 1 :=
    (Matrix.mem_unitaryGroup_iff_isometry V.val).mp V.property |>.1
  have hW : W.valᴴ * W.val = 1 :=
    (Matrix.mem_unitaryGroup_iff_isometry W.val).mp W.property |>.1
  have hWW : W.val * W.valᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp W.property
  let U : Matrix I I ℂ := V.val * W.valᴴ
  have hU_iso : Uᴴ * U = 1 := by
    dsimp [U]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (W.val * V.valᴴ) * (V.val * W.valᴴ)
        = W.val * (V.valᴴ * V.val) * W.valᴴ := by simp [Matrix.mul_assoc]
      _ = W.val * W.valᴴ := by rw [hV, Matrix.mul_one]
      _ = 1 := hWW
  refine ⟨U, opNorm_le_one_of_unitary U hU_iso, ?_⟩
  have htn : Matrix.traceNorm A = ∑ i : I, s i := by
    have hAd : A = V.val * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ := hA
    rw [hAd,
      Matrix.traceNorm_isometry_right (u := W.val) (by
        ext a b
        by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using congrFun (congrFun hW a) b),
      Matrix.traceNorm_isometry_left (u := V.val) (by
        ext a b
        by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using congrFun (congrFun hV a) b)]
    have hp : (Matrix.diagonal (fun i => (s i : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast Real.sqrt_nonneg (hH.eigenvalues i)
    simpa [Matrix.trace] using congrArg Complex.re hp.traceNorm_eq_trace
  have htr : Matrix.trace (Uᴴ * A) = ∑ i : I, (s i : ℂ) := by
    have hAd : A = V.val * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ := hA
    dsimp [U]
    rw [hAd, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hprod : (W.val * V.valᴴ) * (V.val * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ) =
        W.val * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ := by
      calc (W.val * V.valᴴ) * (V.val * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ)
          = W.val * (V.valᴴ * V.val) * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ := by
            simp [Matrix.mul_assoc]
        _ = W.val * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ := by
            rw [hV, Matrix.mul_one]
    rw [hprod, Matrix.trace_mul_comm]
    have hprod2 : W.valᴴ * (W.val * Matrix.diagonal (fun i => (s i : ℂ))) =
        Matrix.diagonal (fun i => (s i : ℂ)) := by
      rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
    rw [hprod2]
    simp [Matrix.trace]
  rw [htr, htn, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)]

/-- Dual characterization of the L2 operator norm: if `‖Tr(Bᴴ X)‖ ≤ δ` for every matrix `X` of
trace norm at most `1` (with `δ ≥ 0`), then `‖B‖ ≤ δ`. -/
private theorem opNorm_le_of_trace_dual {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ X : Matrix I I ℂ, Matrix.traceNorm X ≤ 1 → ‖Matrix.trace (Bᴴ * X)‖ ≤ δ) :
    ‖B‖ ≤ δ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound (LinearMap.toContinuousLinearMap B.toEuclideanLin)
    hδ fun x => ?_
  rw [LinearMap.coe_toContinuousLinearMap']
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hBx0 : B.toEuclideanLin x = 0
  · rw [hBx0, norm_zero]
    exact mul_nonneg hδ (norm_nonneg x)
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : EuclideanSpace ℂ I := ((‖x‖⁻¹ : ℝ) : ℂ) • x
  have hv_norm : ‖v‖ = 1 := by
    simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx_pos)]
    exact inv_mul_cancel₀ hx_pos.ne'
  have hBv_ne : B.toEuclideanLin v ≠ 0 := by
    intro hzero
    apply hBx0
    have hsmul : B.toEuclideanLin v = ((‖x‖⁻¹ : ℝ) : ℂ) • B.toEuclideanLin x := map_smul _ _ _
    rw [hsmul] at hzero
    rcases smul_eq_zero.mp hzero with hc | hvec
    · exact absurd (Complex.ofReal_eq_zero.mp hc) (inv_ne_zero hx_pos.ne')
    · exact hvec
  have hBv_pos : 0 < ‖B.toEuclideanLin v‖ := norm_pos_iff.mpr hBv_ne
  let u : EuclideanSpace ℂ I := ((‖B.toEuclideanLin v‖⁻¹ : ℝ) : ℂ) • B.toEuclideanLin v
  have hu_norm : ‖u‖ = 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hBv_pos)]
    exact inv_mul_cancel₀ hBv_pos.ne'
  have unit_sum : ∀ w : EuclideanSpace ℂ I, ‖w‖ = 1 → ∑ a : I, star (w.ofLp a) * w.ofLp a = 1 := by
    intro w hw
    have hsq : ∑ a : I, ‖w.ofLp a‖ ^ 2 = 1 := by
      have h1 := EuclideanSpace.norm_sq_eq w
      rw [hw, one_pow] at h1
      exact h1.symm
    calc ∑ a : I, star (w.ofLp a) * w.ofLp a
        = ∑ a : I, ((‖w.ofLp a‖ ^ 2 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [RCLike.star_def, Complex.conj_mul', Complex.ofReal_pow]
      _ = ((∑ a : I, ‖w.ofLp a‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_sum _ _).symm
      _ = 1 := by rw [hsq, Complex.ofReal_one]
  let X : Matrix I I ℂ := fun a b => u.ofLp a * star (v.ofLp b)
  have hX_tn : Matrix.traceNorm X ≤ 1 := by
    rw [diamond_unit_rank_one_traceNorm u.ofLp v.ofLp (unit_sum u hu_norm) (unit_sum v hv_norm)]
  have htr_eq : Matrix.trace (Bᴴ * X) = (‖B.toEuclideanLin v‖ : ℂ) := by
    have h1 : Matrix.trace (Bᴴ * X) = inner ℂ (B.toEuclideanLin v) u := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [X, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        dotProduct, Pi.star_apply]
      change (∑ b : I, ∑ a : I, star (B a b) * (u.ofLp a * star (v.ofLp b))) =
        ∑ a : I, u.ofLp a * star ((B *ᵥ v.ofLp) a)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Matrix.mulVec, dotProduct, star_sum, star_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [h1]
    simp only [u, inner_smul_right, inner_self_eq_norm_sq_to_K]
    have hpos_c : (‖B.toEuclideanLin v‖ : ℂ) ≠ 0 := by exact_mod_cast hBv_pos.ne'
    push_cast
    field_simp
    norm_cast
  have hBv_le : ‖B.toEuclideanLin v‖ ≤ δ := by
    have hb := hbound X hX_tn
    rwa [htr_eq, Complex.norm_real, Real.norm_of_nonneg hBv_pos.le] at hb
  have hBx_eq : ‖B.toEuclideanLin x‖ = ‖B.toEuclideanLin v‖ * ‖x‖ := by
    have hsmul : B.toEuclideanLin v = ((‖x‖⁻¹ : ℝ) : ℂ) • B.toEuclideanLin x := map_smul _ _ _
    have hn := congrArg norm hsmul
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hx_pos)] at hn
    calc ‖B.toEuclideanLin x‖ = ‖x‖ * (‖x‖⁻¹ * ‖B.toEuclideanLin x‖) := by
          field_simp [hx_pos.ne']
      _ = ‖B.toEuclideanLin v‖ * ‖x‖ := by rw [← hn, mul_comm]
  rw [hBx_eq]
  exact mul_le_mul_of_nonneg_right hBv_le hx_pos.le

/-- **Eq. (1)** ([Watrous, 2013][Watrous2013], §1, p. 3): the completely bounded trace norm of
`T` equals the completely bounded spectral norm of its Hilbert–Schmidt adjoint `T*`,
characterized by `Tr(Yᴴ (T X)) = Tr((T* Y)ᴴ X)`. -/
theorem completeBoundedTrace_dual_spectral {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ Tstar : Operator E →ₗ[ℂ] Operator D,
      (∀ (X : Operator D) (Y : Operator E),
        Matrix.trace (Yᴴ * T X) = Matrix.trace ((Tstar Y)ᴴ * X)) ∧
      finiteDiamondNorm T = finiteDiamondSpectralNorm Tstar := by
  refine ⟨hsAdjoint T, hsAdjoint_pairing T, ?_⟩
  apply le_antisymm
  · unfold finiteDiamondNorm
    refine iSup_le fun r => iSup_le fun X => ?_
    split_ifs with hX
    · obtain ⟨Y, hY_norm, hY_tr⟩ := exists_opNorm_le_one_trace_eq_traceNorm (tensorLeft T X)
      have hpair : Matrix.trace (Yᴴ * tensorLeft T X) =
          Matrix.trace ((tensorLeft (hsAdjoint T) Y)ᴴ * X) :=
        tensorLeft_hsAdjoint_pairing T X Y
      have hle_real : Matrix.traceNorm (tensorLeft T X) ≤ ‖tensorLeft (hsAdjoint T) Y‖ := by
        calc Matrix.traceNorm (tensorLeft T X)
            = ‖Matrix.trace (Yᴴ * tensorLeft T X)‖ := hY_tr.symm
          _ = ‖Matrix.trace ((tensorLeft (hsAdjoint T) Y)ᴴ * X)‖ := by rw [hpair]
          _ ≤ ‖tensorLeft (hsAdjoint T) Y‖ * Matrix.traceNorm X :=
              norm_trace_conjTranspose_mul_le _ _
          _ ≤ ‖tensorLeft (hsAdjoint T) Y‖ * 1 :=
              mul_le_mul_of_nonneg_left hX (norm_nonneg _)
          _ = ‖tensorLeft (hsAdjoint T) Y‖ := mul_one _
      unfold finiteDiamondSpectralNorm
      refine le_iSup_of_le r (le_iSup_of_le Y ?_)
      simp only [hY_norm, ↓reduceIte]
      exact ENNReal.ofReal_le_ofReal hle_real
    · exact bot_le
  · obtain ⟨hfin, -⟩ := diamond_finite_attained_maximum D E T
    let δ : ℝ := (finiteDiamondNorm T).toReal
    have hδ_nonneg : 0 ≤ δ := ENNReal.toReal_nonneg
    have hδ_eq : ENNReal.ofReal δ = finiteDiamondNorm T := ENNReal.ofReal_toReal hfin.ne
    have hunif := (finiteDiamondNorm_le_iff_uniform D E T δ hδ_nonneg).mp hδ_eq.symm.le
    unfold finiteDiamondSpectralNorm
    refine iSup_le fun r => iSup_le fun Y => ?_
    split_ifs with hY
    · have hnorm_le : ‖tensorLeft (hsAdjoint T) Y‖ ≤ δ := by
        refine opNorm_le_of_trace_dual (tensorLeft (hsAdjoint T) Y) δ hδ_nonneg fun X hX => ?_
        calc ‖Matrix.trace ((tensorLeft (hsAdjoint T) Y)ᴴ * X)‖
            = ‖Matrix.trace (Yᴴ * tensorLeft T X)‖ := by
              rw [tensorLeft_hsAdjoint_pairing]
          _ ≤ ‖Y‖ * Matrix.traceNorm (tensorLeft T X) :=
              norm_trace_conjTranspose_mul_le Y _
          _ ≤ 1 * (δ * Matrix.traceNorm X) :=
              mul_le_mul hY (hunif r X) (Matrix.traceNorm_nonneg _) zero_le_one
          _ ≤ 1 * (δ * 1) := by nlinarith [hX, hδ_nonneg]
          _ = δ := by ring
      rw [← hδ_eq]
      exact ENNReal.ofReal_le_ofReal hnorm_le
    · exact bot_le

end Qatlib.Papers.BddNormSDP12.MainResults.SourceDuality
