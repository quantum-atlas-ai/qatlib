/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues

/-!
# Input-dimension stabilization of the diamond norm

This module defines `diamondAtInput`, restricting the reference dimension to the input
dimension, and proves that it equals `finiteDiamondNorm` for every complex-linear map between
finite matrix spaces. The proof compresses rank-one matrices using separate isometric reference
frames and extends their bounds to arbitrary matrices by a singular-value decomposition. The
stabilization setting is treated in [Watrous2018].

The theorem `diamond_finite_attained_maximum` also proves finiteness and attainment on the
trace-norm unit ball with reference dimension equal to the input dimension.

## Main statements

* `diamond_rank_one_two_frame_compression`: compresses both rank-one vectors while preserving
  the amplified output trace norm.
* `diamond_uniform_bound_of_input_bound`: extends a bound at the input reference dimension to
  every finite reference.
* `diamond_input_dimension_stabilization`: identifies `finiteDiamondNorm` with `diamondAtInput`.
* `diamond_finite_attained_maximum`: realizes the finite norm at a matrix in the
  fixed-dimensional unit ball.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Concepts.RandCompile.ChannelBudget
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Classical BigOperators ENNReal ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The supremum of amplified output trace norms over the trace-norm unit ball with reference
dimension fixed to the input dimension, valued in the extended nonnegative reals. -/
noncomputable def diamondAtInput {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
    if Matrix.traceNorm X ≤ 1 then ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) else 0

/-- Tensoring an isometric reference frame `L` with the identity on `Fin D` yields an isometry. -/
theorem diamond_kronecker_frame_isometry {D r s : ℕ}
    {L : Matrix (Fin r) (Fin s) ℂ} (hL : IsIsometry L) :
    IsIsometry (Matrix.kronecker (1 : Operator D) L) := by
  unfold IsIsometry at *
  change (Matrix.kroneckerMap (· * ·) (1 : Operator D) L)ᴴ *
    Matrix.kroneckerMap (· * ·) (1 : Operator D) L = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp [hL]

/-- If `D <= r`, every `r`-by-`D` matrix has an isometric `r`-by-`D` frame whose range
projection fixes that matrix. -/
theorem diamond_exists_column_frame {D r : ℕ} (A : Matrix (Fin r) (Fin D) ℂ)
    (hdr : D ≤ r) :
    ∃ L : Matrix (Fin r) (Fin D) ℂ, IsIsometry L ∧ L * Lᴴ * A = A := by
  let b : OrthonormalBasis (Fin r) ℂ (EuclideanSpace ℂ (Fin r)) :=
    (leftSingularBasis A).reindex (finCongr (by simp))
  let e : Fin D → Fin r := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hdr⟩
  let L : Matrix (Fin r) (Fin D) ℂ := fun j i => b (e i) j
  have he : Function.Injective e := by
    intro i j h; exact Fin.ext (congrArg (fun k : Fin r => k.val) h)
  have hL : IsIsometry L := by
    ext i j
    change star (b (e i)).ofLp ⬝ᵥ (b (e j)).ofLp = (1 : Operator D) i j
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    rw [b.inner_eq_ite]
    simp [Matrix.one_apply, he.eq_iff]
  have hfix (i : Fin D) : (L * Lᴴ).mulVec (b (e i)) = b (e i) := by
    have hcol : L.mulVec (Pi.single i 1) = b (e i) := by
      ext j
      simp [Matrix.mulVec_single, L]
    rw [← hcol, Matrix.mulVec_mulVec, Matrix.mul_assoc, show Lᴴ * L = 1 from hL]
    simp
  refine ⟨L, hL, ?_⟩
  rw [matrix_eq_sum_singularVectors A]
  simp only [Matrix.mul_sum, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hσ : matrixSingularValues A i = 0
  · simp [hσ]
  · have hpos : 0 < matrixSingularValues A i :=
      lt_of_le_of_ne (matrixSingularValues_nonneg A i) (Ne.symm hσ)
    have hiRank := (matrixSingularValues_pos_iff_lt_finrank_range A).mp hpos
    have hb : b (e ⟨i.val, by simpa using! i.isLt⟩) = leftSingularVector A i := by
      simpa [b, e] using! leftSingularBasis_apply_of_lt A
        ⟨i.val, lt_of_lt_of_le hiRank (by simpa using! Submodule.finrank_le A.toEuclideanLin.range)⟩ hiRank
    rw [Matrix.mul_vecMulVec, ← hb, hfix]

/-- The `(i, j)` component of applying the identity tensored with `L` to `u` is the sum of `L j
k * u (i, k)` over reference indices `k`. -/
theorem diamond_reference_frame_mulVec {D r s : ℕ}
    (L : Matrix (Fin r) (Fin s) ℂ) (u : QState (Fin D × Fin s)) (i : Fin D) (j : Fin r) :
    (Matrix.kronecker (1 : Operator D) L *ᵥ u) (i,j) =
      ∑ k, L j k * u (i,k) := by
  simp [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul]

/-- If `D <= r`, every vector on `Fin D` times `Fin r` is the image of a vector on `Fin D` times
`Fin D` under an isometric reference frame. The compressed vector has the same Euclidean
norm. -/
theorem diamond_exists_vector_frame {D r : ℕ} (u : QState (Fin D × Fin r))
    (hdr : D ≤ r) :
    ∃ (L : Matrix (Fin r) (Fin D) ℂ) (u' : QState (Fin D × Fin D)),
      IsIsometry L ∧ u = Matrix.kronecker (1 : Operator D) L *ᵥ u' ∧
      ‖toEuclidean_fromVec u'‖ = ‖toEuclidean_fromVec u‖ := by
  let A : Matrix (Fin r) (Fin D) ℂ := fun j i => u (i,j)
  obtain ⟨L,hL,hA⟩ := diamond_exists_column_frame A hdr
  let u' : QState (Fin D × Fin D) := fun p => (Lᴴ * A) p.2 p.1
  have hu : u = Matrix.kronecker (1 : Operator D) L *ᵥ u' := by
    ext p
    rw [diamond_reference_frame_mulVec]
    have hA' : L * (Lᴴ * A) = A := by rwa [← Matrix.mul_assoc]
    have hp := congrFun (congrFun hA' p.2) p.1
    simpa only [Matrix.mul_assoc, Matrix.mul_apply, A, u'] using! hp.symm
  refine ⟨L,u',hL,hu,?_⟩
  rw [hu]
  exact (isometry_mulVec_norm (diamond_kronecker_frame_isometry hL) u').symm

/-- Amplifying `T` commutes with multiplying the reference factor by a left frame `L` and the
conjugate transpose of a right frame `R`. The system identities in the frame matrices change
from input dimension `D` to output dimension `E`. -/
theorem diamond_tensorLeft_frames {D E r s : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (L R : Matrix (Fin r) (Fin s) ℂ)
    (X : Matrix (Fin D × Fin s) (Fin D × Fin s) ℂ) :
    tensorLeft T (Matrix.kronecker (1 : Operator D) L * X *
        (Matrix.kronecker (1 : Operator D) R)ᴴ) =
      Matrix.kronecker (1 : Operator E) L * tensorLeft T X *
        (Matrix.kronecker (1 : Operator E) R)ᴴ := by
  have hentry {n : ℕ} (Y : Matrix (Fin n × Fin s) (Fin n × Fin s) ℂ)
      (a b : Fin n × Fin r) :
      (Matrix.kronecker (1 : Operator n) L * Y *
        (Matrix.kronecker (1 : Operator n) R)ᴴ) a b =
      ∑ j, ∑ k, (L a.2 j * star (R b.2 k)) * Y (a.1,j) (b.1,k) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
      apply_ite, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    exact Finset.sum_comm
  ext a b
  change (T (fun i j =>
    (Matrix.kronecker (1 : Operator D) L * X *
      (Matrix.kronecker (1 : Operator D) R)ᴴ) (i,a.2) (j,b.2))) a.1 b.1 = _
  let B : Fin s → Fin s → Operator D := fun k l => Matrix.of (fun i j => X (i,k) (j,l))
  have hblock : ((fun i j =>
      (Matrix.kronecker (1 : Operator D) L * X *
        (Matrix.kronecker (1 : Operator D) R)ᴴ) (i,a.2) (j,b.2)) : Operator D) =
      ∑ k, ∑ l, (L a.2 k * star (R b.2 l)) •
        B k l := by
    ext i j
    simp only [hentry, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, B, Matrix.of_apply]
  rw [hblock]
  simp only [_root_.map_sum, LinearMap.map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ k, ∑ l, (L a.2 k * star (R b.2 l)) * T (B k l) a.1 b.1) = _
  exact (hentry (tensorLeft T X) a b).symm

/-- For `D <= r`, the vectors defining any rank-one input can be compressed to reference
dimension `D` using separate isometric frames, preserving their Euclidean norms. The
amplified rank-one output has the same trace norm after this compression. -/
theorem diamond_rank_one_two_frame_compression : ∀ (D E r : ℕ)
    (T : Operator D →ₗ[ℂ] Operator E) (u v : QState (Fin D × Fin r)), D ≤ r →
    ∃ (L R : Matrix (Fin r) (Fin D) ℂ) (u' v' : QState (Fin D × Fin D)),
      IsIsometry L ∧ IsIsometry R ∧
      u = Matrix.kronecker (1 : Operator D) L *ᵥ u' ∧
      v = Matrix.kronecker (1 : Operator D) R *ᵥ v' ∧
      ‖toEuclidean_fromVec u'‖ = ‖toEuclidean_fromVec u‖ ∧
      ‖toEuclidean_fromVec v'‖ = ‖toEuclidean_fromVec v‖ ∧
      Matrix.traceNorm (tensorLeft T (fun i j => u i * star (v j))) =
        Matrix.traceNorm (tensorLeft T (fun i j => u' i * star (v' j))) := by
  intro D E r T u v hdr
  obtain ⟨L,u',hL,hu,hun⟩ := diamond_exists_vector_frame u hdr
  obtain ⟨R,v',hR,hv,hvn⟩ := diamond_exists_vector_frame v hdr
  refine ⟨L,R,u',v',hL,hR,hu,hv,hun,hvn,?_⟩
  let X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun i j => u' i * star (v' j)
  have houter : (fun i j => u i * star (v j)) =
      Matrix.kronecker (1 : Operator D) L * X *
        (Matrix.kronecker (1 : Operator D) R)ᴴ := by
    rw [hu,hv]
    ext i j
    simp [X, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Finset.mul_sum, star_sum, star_mul, mul_assoc, mul_comm, mul_left_comm]
  rw [houter, diamond_tensorLeft_frames,
    Matrix.traceNorm_isometry_right (u := Matrix.kronecker (1 : Operator E) R)
      (by
        have h := diamond_kronecker_frame_isometry (D := E) hR
        ext a b
        by_cases hab : a = b <;>
          simpa [Matrix.one_apply, hab] using! congrFun (congrFun h a) b),
    Matrix.traceNorm_isometry_left (u := Matrix.kronecker (1 : Operator E) L)
      (by
        have h := diamond_kronecker_frame_isometry (D := E) hL
        ext a b
        by_cases hab : a = b <;>
          simpa [Matrix.one_apply, hab] using! congrFun (congrFun h a) b)]

/-- Multiplication by independent isometric reference frames on the left and right preserves the
trace norm of a matrix. -/
theorem diamond_traceNorm_frames {D r s : ℕ} (L R : Matrix (Fin r) (Fin s) ℂ)
    (hL : IsIsometry L) (hR : IsIsometry R)
    (X : Matrix (Fin D × Fin s) (Fin D × Fin s) ℂ) :
    Matrix.traceNorm (Matrix.kronecker (1 : Operator D) L * X *
      (Matrix.kronecker (1 : Operator D) R)ᴴ) = Matrix.traceNorm X := by
  rw [Matrix.traceNorm_isometry_right (u := Matrix.kronecker (1 : Operator D) R) (by
    have h := diamond_kronecker_frame_isometry (D := D) hR
    ext a b
    by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using! congrFun (congrFun h a) b)]
  rw [Matrix.traceNorm_isometry_left (u := Matrix.kronecker (1 : Operator D) L) (by
    have h := diamond_kronecker_frame_isometry (D := D) hL
    ext a b
    by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using! congrFun (congrFun h a) b)]

/-- At reference dimension `D`, the extended nonnegative trace norm of `tensorLeft T X` is at
most `diamondAtInput T` times the extended nonnegative trace norm of `X`. -/
theorem diamondAtInput_apply {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) ≤
      diamondAtInput T * ENNReal.ofReal (Matrix.traceNorm X) := by
  by_cases hz : Matrix.traceNorm X = 0
  · have hX := (Matrix.traceNorm_zero_iff X).mp hz
    subst X
    have ht : tensorLeft T (0 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) = 0 := by
      ext a b
      exact congrFun (congrFun T.map_zero a.1) b.1
    simp [ht]
  · let q := Matrix.traceNorm X
    have hq : 0 < q := lt_of_le_of_ne (Matrix.traceNorm_nonneg X) (Ne.symm hz)
    let Y := ((q⁻¹ : ℝ) : ℂ) • X
    have hY : Matrix.traceNorm Y = 1 := by
      rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hq)]
      exact inv_mul_cancel₀ (ne_of_gt hq)
    have hXY : X = (q : ℂ) • Y := by
      have hc : (q : ℂ)*((q⁻¹ : ℝ) : ℂ) = 1 := by
        exact_mod_cast mul_inv_cancel₀ (ne_of_gt hq)
      ext a b
      change X a b = (q : ℂ)*(((q⁻¹ : ℝ) : ℂ)*X a b)
      rw [← mul_assoc, hc, one_mul]
    have hbound : ENNReal.ofReal (Matrix.traceNorm (tensorLeft T Y)) ≤ diamondAtInput T := by
      unfold diamondAtInput
      exact le_iSup_of_le Y (by simp [hY])
    calc
      _ = ENNReal.ofReal q * ENNReal.ofReal (Matrix.traceNorm (tensorLeft T Y)) := by
        conv_lhs => rw [hXY]
        rw [diamond_tensorLeft_input_smul, Matrix.traceNorm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hq, ENNReal.ofReal_mul hq.le]
      _ ≤ ENNReal.ofReal q * diamondAtInput T := mul_le_mul_right hbound _
      _ = _ := mul_comm _ _

/-- For nonnegative real `delta`, `diamondAtInput T <= ofReal delta` is equivalent to the
uniform bound `traceNorm (tensorLeft T X) <= delta * traceNorm X` at reference dimension
`D`. -/
theorem diamondAtInput_le_iff_uniform {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    diamondAtInput T ≤ ENNReal.ofReal δ ↔
      ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
        Matrix.traceNorm (tensorLeft T X) ≤ δ * Matrix.traceNorm X := by
  constructor
  · intro h X
    have he := (diamondAtInput_apply T X).trans
      (mul_le_mul_left h (ENNReal.ofReal (Matrix.traceNorm X)))
    rw [← ENNReal.ofReal_mul hδ] at he
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hδ (Matrix.traceNorm_nonneg X))).mp he
  · intro h
    unfold diamondAtInput
    apply iSup_le
    intro X
    split_ifs with hx
    · exact ENNReal.ofReal_le_ofReal ((h X).trans
        ((mul_le_mul_of_nonneg_left hx hδ).trans_eq (mul_one δ)))
    · exact bot_le

/-- A uniform trace-norm amplification bound at reference dimension `D` also holds for every
rank-one input with reference dimension `r >= D`. -/
theorem diamond_rank_one_bound_of_input_bound {D E r : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) (δ : ℝ)
    (h : ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm (tensorLeft T X) ≤ δ * Matrix.traceNorm X)
    (u v : QState (Fin D × Fin r)) (hdr : D ≤ r) :
    Matrix.traceNorm (tensorLeft T (fun i j => u i * star (v j))) ≤
      δ * Matrix.traceNorm (fun i j => u i * star (v j) :
        Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) := by
  obtain ⟨L,R,u',v',hL,hR,hu,hv,_,_,he⟩ :=
    diamond_rank_one_two_frame_compression D E r T u v hdr
  let X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun i j => u' i * star (v' j)
  have ho : (fun i j => u i * star (v j)) =
      Matrix.kronecker (1 : Operator D) L * X *
        (Matrix.kronecker (1 : Operator D) R)ᴴ := by
    rw [hu,hv]
    ext i j
    simp [X, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Finset.mul_sum, star_sum, star_mul, mul_assoc, mul_comm, mul_left_comm]
  rw [he, ho, diamond_traceNorm_frames L R hL hR]
  exact h X

/-- A uniform trace-norm amplification bound at reference dimension `D` also holds for every
matrix with reference dimension `r <= D`. -/
theorem diamond_small_reference_bound_of_input_bound {D E r : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) (δ : ℝ)
    (h : ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm (tensorLeft T X) ≤ δ * Matrix.traceNorm X)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hrd : r ≤ D) :
    Matrix.traceNorm (tensorLeft T X) ≤ δ * Matrix.traceNorm X := by
  let e : Fin r → Fin D := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hrd⟩
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin D => k.val) h)
  let L : Matrix (Fin D) (Fin r) ℂ := (1 : Operator D).submatrix id e
  have hL : IsIsometry L := by
    have hi := Matrix.submatrix_one_id_right_isometry he (R := ℂ)
    ext a b
    by_cases hab : a = b <;> simpa [L, Matrix.one_apply, hab] using! congrFun (congrFun hi a) b
  have hx := h (Matrix.kronecker (1 : Operator D) L * X *
    (Matrix.kronecker (1 : Operator D) L)ᴴ)
  rw [diamond_tensorLeft_frames, diamond_traceNorm_frames L L hL hL,
    diamond_traceNorm_frames L L hL hL] at hx
  exact hx

/-- The outer product of two vectors each having squared Euclidean norm one has trace norm one. -/
theorem diamond_unit_rank_one_traceNorm {I : Type} [Fintype I] [DecidableEq I]
    (u v : I → ℂ) (hu : ∑ i, star (u i) * u i = 1)
    (hv : ∑ i, star (v i) * v i = 1) :
    Matrix.traceNorm (fun i j => u i * star (v j) : Matrix I I ℂ) = 1 := by
  let L : Matrix I (Fin 1) ℂ := fun i _ => u i
  let R : Matrix I (Fin 1) ℂ := fun i _ => v i
  have ho : (fun i j => u i * star (v j)) = L * (1 : Operator 1) * Rᴴ := by
    ext i j
    simp [L,R,Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [ho, Matrix.traceNorm_isometry_right (u := R) (by
    ext a b
    have hab : a = b := Subsingleton.elim _ _
    subst b
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, R, Matrix.one_apply] using! hv)]
  rw [Matrix.traceNorm_isometry_left (u := L) (by
    ext a b
    have hab : a = b := Subsingleton.elim _ _
    subst b
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, L, Matrix.one_apply] using! hu)]
  have hh := (Matrix.PosSemidef.one : (1 : Operator 1).PosSemidef).traceNorm_eq_trace
  simpa [Matrix.trace] using! congrArg Complex.re hh

/-- Every finite square complex matrix is a sum of rank-one outer products of unit vectors with
nonnegative real coefficients. Each outer product has trace norm one, and the sum of the
coefficients equals the matrix trace norm. -/
theorem diamond_svd_trace_decomposition {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) :
    ∃ (s : I → ℝ) (u v : I → I → ℂ),
      (∀ i, 0 ≤ s i) ∧
      X = ∑ i, (s i : ℂ) • Matrix.of (fun a b => u i a * star (v i b)) ∧
      (∀ i, Matrix.traceNorm (Matrix.of (fun a b => u i a * star (v i b))) = 1) ∧
      Matrix.traceNorm X = ∑ i, s i ∧
      (∀ i, (∑ a, star (u i a) * u i a = 1) ∧ (∑ a, star (v i a) * v i a = 1)) := by
  classical
  obtain ⟨V,W,hX⟩ := Matrix.exists_svd_sqrt_eigenvalues X
  let hH : (Xᴴ * X).IsHermitian := by
    simpa using! Matrix.isHermitian_mul_conjTranspose_self X.conjTranspose
  let s : I → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  let u : I → I → ℂ := fun i a => V.val a i
  let v : I → I → ℂ := fun i a => W.val a i
  have hV : V.valᴴ * V.val = 1 :=
    (Matrix.mem_unitaryGroup_iff_isometry V.val).mp V.property |>.1
  have hW : W.valᴴ * W.val = 1 :=
    (Matrix.mem_unitaryGroup_iff_isometry W.val).mp W.property |>.1
  refine ⟨s,u,v,(fun i => Real.sqrt_nonneg _),?_,?_,?_,?_⟩
  · conv_lhs => rw [hX]
    ext a b
    simp only [s,u,v, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Matrix.diagonal, Matrix.of_apply, mul_comm, mul_assoc]

  · intro i
    apply diamond_unit_rank_one_traceNorm
    · simpa [u, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using!
        congrFun (congrFun hV i) i
    · simpa [v, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using!
        congrFun (congrFun hW i) i

  · have hXd : X = V.val * Matrix.diagonal (fun i => (s i : ℂ)) * W.valᴴ := hX
    rw [hXd, Matrix.traceNorm_isometry_right
      (u := W.val) (by
        ext a b
        by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using! congrFun (congrFun hW a) b),
      Matrix.traceNorm_isometry_left
      (u := V.val) (by
        ext a b
        by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using! congrFun (congrFun hV a) b)]
    have hp : (Matrix.diagonal (fun i => (s i : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast Real.sqrt_nonneg (hH.eigenvalues i)
    simpa [Matrix.trace] using! congrArg Complex.re hp.traceNorm_eq_trace
  · intro i
    constructor
    · simpa [u, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using!
        congrFun (congrFun hV i) i
    · simpa [v, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using!
        congrFun (congrFun hW i) i

/-- Packages `tensorLeft T` at reference dimension `r` as a complex-linear map between the
corresponding matrix spaces. -/
noncomputable def diamondAmplification {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (r : ℕ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ →ₗ[ℂ]
      Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ where
  toFun := tensorLeft T
  map_add' X Y := by
    ext a b
    exact congrFun (congrFun (T.map_add
      (fun i j => X (i,a.2) (j,b.2)) (fun i j => Y (i,a.2) (j,b.2))) a.1) b.1
  map_smul' c X := diamond_tensorLeft_input_smul T c X

/-- The trace norm of a finite sum of matrices is at most the sum of their trace norms. -/
theorem diamond_traceNorm_sum_le {I J : Type} [Fintype I] [DecidableEq I]
    (s : Finset J) (A : J → Matrix I I ℂ) :
    Matrix.traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, Matrix.traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Matrix.traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- A uniform trace-norm amplification bound at reference dimension `D` extends to every finite
reference dimension and every input matrix. -/
theorem diamond_uniform_bound_of_input_bound {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) (δ : ℝ)
    (h : ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm (tensorLeft T X) ≤ δ * Matrix.traceNorm X)
    (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (tensorLeft T X) ≤ δ * Matrix.traceNorm X := by
  by_cases hrd : r ≤ D
  · exact diamond_small_reference_bound_of_input_bound T δ h X hrd
  · have hdr : D ≤ r := le_of_lt (lt_of_not_ge hrd)
    obtain ⟨s,u,v,hs,hX,hunit,htrace,_⟩ := diamond_svd_trace_decomposition X
    let P : (Fin D × Fin r) → Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
      fun i a b => u i a * star (v i b)
    have hP (i : Fin D × Fin r) : Matrix.traceNorm (tensorLeft T (P i)) ≤ δ := by
      have hb := diamond_rank_one_bound_of_input_bound T δ h (u i) (v i) hdr
      change Matrix.traceNorm (tensorLeft T (P i)) ≤ δ * Matrix.traceNorm (P i) at hb
      have hui : Matrix.traceNorm (P i) = 1 := by simpa [P, Matrix.of] using! hunit i
      simpa only [hui, mul_one] using! hb
    have hsum : tensorLeft T X = ∑ i, (s i : ℂ) • tensorLeft T (P i) := by
      change diamondAmplification T r X = _
      rw [hX, map_sum]
      simp only [map_smul]
      rfl
    calc
      _ ≤ ∑ i, Matrix.traceNorm ((s i : ℂ) • tensorLeft T (P i)) := by
        rw [hsum]
        exact diamond_traceNorm_sum_le Finset.univ _
      _ = ∑ i, s i * Matrix.traceNorm (tensorLeft T (P i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_of_nonneg (hs i)]
      _ ≤ ∑ i, s i * δ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hP i) (hs i)
      _ = δ * Matrix.traceNorm X := by rw [htrace]; simp [Finset.mul_sum, mul_comm]

/-- For every complex-linear map between finite matrix spaces, the supremum over all finite
reference systems equals the supremum at reference dimension equal to the input dimension. -/
theorem diamond_input_dimension_stabilization : ∀ (D E : ℕ)
    (T : Operator D →ₗ[ℂ] Operator E), finiteDiamondNorm T = diamondAtInput T := by
  intro D E T
  apply le_antisymm
  · by_cases ht : diamondAtInput T = ⊤
    · simp [ht]
    · have hδ : 0 ≤ (diamondAtInput T).toReal := ENNReal.toReal_nonneg
      have he : diamondAtInput T = ENNReal.ofReal (diamondAtInput T).toReal :=
        (ENNReal.ofReal_toReal ht).symm
      have hb := (diamondAtInput_le_iff_uniform T _ hδ).mp he.le
      rw [he]
      exact (finiteDiamondNorm_le_iff_uniform D E T _ hδ).mpr
        (diamond_uniform_bound_of_input_bound T _ hb)
  · unfold diamondAtInput
    apply iSup_le
    intro X
    unfold finiteDiamondNorm
    exact le_iSup_of_le D (le_iSup_of_le X le_rfl)

/-- The finite diamond norm is below infinity and is attained at an input of trace norm at most
one with reference dimension equal to the input dimension. -/
theorem diamond_finite_attained_maximum : ∀ (D E : ℕ)
    (T : Operator D →ₗ[ℂ] Operator E), finiteDiamondNorm T < ⊤ ∧
    ∃ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm X ≤ 1 ∧
      finiteDiamondNorm T = ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) := by
  intro D E T
  letI : Norm (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := ⟨Matrix.traceNorm⟩
  let cD : NormedSpace.Core ℂ (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := {
    norm_nonneg := Matrix.traceNorm_nonneg
    norm_smul := fun c X => Matrix.traceNorm_smul X c
    norm_triangle := Matrix.traceNorm_add_le
    norm_eq_zero_iff := Matrix.traceNorm_zero_iff }
  letI : NormedAddCommGroup (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :=
    NormedAddCommGroup.ofCore cD
  letI : SeminormedAddCommGroup (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :=
    (NormedAddCommGroup.ofCore cD).toSeminormedAddCommGroup
  letI : MetricSpace (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := (NormedAddCommGroup.ofCore cD).toMetricSpace
  letI : TopologicalSpace (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := (NormedAddCommGroup.ofCore cD).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedSpace ℂ (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := NormedSpace.ofCore cD
  letI : Norm (Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) := ⟨Matrix.traceNorm⟩
  let cE : NormedSpace.Core ℂ (Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) := {
    norm_nonneg := Matrix.traceNorm_nonneg
    norm_smul := fun c X => Matrix.traceNorm_smul X c
    norm_triangle := Matrix.traceNorm_add_le
    norm_eq_zero_iff := Matrix.traceNorm_zero_iff }
  letI : NormedAddCommGroup (Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :=
    NormedAddCommGroup.ofCore cE
  letI : SeminormedAddCommGroup (Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :=
    (NormedAddCommGroup.ofCore cE).toSeminormedAddCommGroup
  letI : MetricSpace (Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) := (NormedAddCommGroup.ofCore cE).toMetricSpace
  letI : TopologicalSpace (Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) := (NormedAddCommGroup.ofCore cE).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedSpace ℂ (Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) := NormedSpace.ofCore cE
  let f := diamondAmplification T D
  have hf : Continuous (fun X => ‖f X‖) :=
    continuous_norm.comp f.continuous_of_finiteDimensional
  have hc := isCompact_closedBall (0 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (1 : ℝ)
  obtain ⟨X,hX,hmax⟩ := hc.exists_isMaxOn ⟨0, by simp⟩ hf.continuousOn
  have hx : Matrix.traceNorm X ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using! hX
  have he : diamondAtInput T = ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) := by
    apply le_antisymm
    · unfold diamondAtInput
      apply iSup_le
      intro Y
      split_ifs with hy
      · apply ENNReal.ofReal_le_ofReal
        exact hmax (by simpa only [Metric.mem_closedBall, dist_zero_right] using! hy)
      · exact bot_le
    · unfold diamondAtInput
      exact le_iSup_of_le X (by simp [hx])
  rw [diamond_input_dimension_stabilization, he]
  exact ⟨ENNReal.ofReal_lt_top, X, hx, rfl⟩

end Qatlib.Concepts.SchattenDiamond.DiamondNorm
