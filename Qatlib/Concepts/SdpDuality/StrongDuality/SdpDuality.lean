/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
import Mathlib.Analysis.LocallyConvex.Separation
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization

/-!
# Semidefinite duality and diamond norm optimization

This module proves separation and Slater strong duality for semidefinite programs over finite
complex Hermitian matrices. It establishes self-duality of `psdCone`, identifies its interior
with positive definite matrices, and proves optimizer existence through
`Program.primalSlater_strong_duality`, `Program.dualSlater_strong_duality`, and
`Program.bothSlater_optimizers`. The `boundaryPrimal` and `boundaryDual` example exhibits a dual
infimum that is not attained.

The fidelity and diamond norm formulations use the semidefinite programming viewpoint of
[Watrous2018]. The module identifies their values, relates Choi and Stinespring descriptions,
and constructs bounded dyadic witnesses and exact rational separation oracles. Its rational
ellipsoid analysis proves preservation of feasible sublevel points, determinant contraction, and
finite search guarantees when a positive-radius inner ball is available.

## Main statements

* `psd_trace_self_dual`: positivity characterized by nonnegative real trace pairings.
* `Program.bothSlater_optimizers`: equal attained primal and dual optima under both Slater
  conditions.
* `boundary_dual_infimum_not_attained`: a boundary example with dual infimum zero and no dual
  minimizer.
* `fidelity_source_rootFidelity`: the fidelity block program has value equal to root fidelity.
* `diamondSource_norm_both_optimizers`: the Choi source formulations attain the finite diamond
  norm for positive input dimension.
* `finiteDiamondNorm_stinespring`: the Stinespring cross norm equals maximum output root
  fidelity.
* `diamondProgram_rational_binary_witness`: a bounded binary certificate for a strictly feasible
  dual point close to the optimum.
* `diamondRationalSublevelOracle_cut`: certified separation of the real dual sublevel set.
* `diamondEllipsoidSolve_outcome`: feasible output or an exhausted search threshold below the
  optimum plus tolerance.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.DyadicFloor.FloorRounding.Program
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.SdpDuality.StrongDuality

open Matrix
open scoped InnerProductSpace
open scoped ComplexOrder

/-- The cone of positive semidefinite Hermitian matrices is closed and convex over the reals. -/
theorem psdCone_closed_convex (I : Type*) [Fintype I] [DecidableEq I] :
    IsClosed (psdCone I : Set (HermitianMat I ℂ)) ∧
      Convex ℝ (psdCone I : Set (HermitianMat I ℂ)) :=
  ⟨(psdCone I).isClosed, (psdCone I).convex⟩

/-- The real inner product of Hermitian matrices equals the real part of the trace of their
product. -/
theorem inner_eq_real_trace {I : Type*} [Fintype I] [DecidableEq I]
    (A B : HermitianMat I ℂ) :
    ⟪A, B⟫_ℝ = (Matrix.trace (A.mat * B.mat)).re := by
  have h := HermitianMat.inner_eq_trace_mul (R := ℝ) A B
  exact (congrArg Complex.re h).symm

/-- The positive semidefinite cone is self-dual for the real inner product. -/
theorem psdCone_self_dual (I : Type*) [Fintype I] [DecidableEq I] :
    ProperCone.innerDual (psdCone I : Set (HermitianMat I ℂ)) = psdCone I := by
  ext A
  change (∀ ⦃B : HermitianMat I ℂ⦄, 0 ≤ B → 0 ≤ ⟪B, A⟫_ℝ) ↔ 0 ≤ A
  simpa only [real_inner_comm] using! (HermitianMat.nonneg_iff_inner_nonneg A).symm

/-- A Hermitian matrix is positive semidefinite exactly when its real trace pairing with every
positive semidefinite matrix is nonnegative. -/
theorem psd_trace_self_dual {I : Type*} [Fintype I] [DecidableEq I]
    (A : HermitianMat I ℂ) :
    0 ≤ A ↔ ∀ B : HermitianMat I ℂ, 0 ≤ B →
      0 ≤ (Matrix.trace (A.mat * B.mat)).re := by
  simpa only [inner_eq_real_trace] using! HermitianMat.nonneg_iff_inner_nonneg A

/-- Membership in the closed cone image `(psdCone I).map A` is equivalent to nonnegative pairing
with every vector whose adjoint image is positive semidefinite. -/
theorem psd_closed_image_iff {I : Type*} [Fintype I] [DecidableEq I]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : HermitianMat I ℂ →L[ℝ] F) (b : F) :
    b ∈ (psdCone I).map A ↔ ∀ y : F, 0 ≤ A.adjoint y → 0 ≤ ⟪b, y⟫_ℝ := by
  have h := ProperCone.relative_hyperplane_separation
    (C := psdCone I) (f := A) (b := b)
  constructor
  · intro hb y hy
    apply h.mp hb y
    intro X hX
    exact HermitianMat.inner_ge_zero hX hy
  · intro hb
    apply h.mpr
    intro y hy
    apply hb y
    apply (HermitianMat.nonneg_iff_inner_nonneg _).mpr
    intro X hX
    simpa only [real_inner_comm] using! hy hX

/-- A point lies outside `(psdCone I).map A` exactly when a vector with positive semidefinite
adjoint image has strictly negative pairing with it. -/
theorem psd_strict_separator_iff {I : Type*} [Fintype I] [DecidableEq I]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : HermitianMat I ℂ →L[ℝ] F) (b : F) :
    b ∉ (psdCone I).map A ↔
      ∃ y : F, 0 ≤ A.adjoint y ∧ ⟪b, y⟫_ℝ < 0 := by
  rw [psd_closed_image_iff]
  push Not
  rfl

/-- A point in `(psdCone I).map A` has no strictly negative separator with positive semidefinite
adjoint image. -/
theorem no_strict_separator_of_closed_image {I : Type*} [Fintype I] [DecidableEq I]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : HermitianMat I ℂ →L[ℝ] F) (b : F) (hb : b ∈ (psdCone I).map A) :
    ¬ ∃ y : F, 0 ≤ A.adjoint y ∧ ⟪b, y⟫_ℝ < 0 := by
  rw [← psd_strict_separator_iff]
  exact not_not.mpr hb

/-- For a positive semidefinite two by two matrix, a zero first diagonal entry forces the upper
off-diagonal entry to vanish. -/
theorem zero_corner_forces_zero_offdiagonal (X : HermitianMat (Fin 2) ℂ)
    (hX : 0 ≤ X) (hzero : (X.mat 0 0).re = 0) : X.mat 0 1 = 0 := by
  have hz : X.mat 0 0 = 0 := by
    apply Complex.ext hzero
    have h := congrArg Complex.im (X.H.apply 0 0)
    simp only [RCLike.star_def, Complex.conj_im] at h
    simp only [Complex.zero_im]
    linarith
  have hquad : star (![1,0] : Fin 2 → ℂ) ⬝ᵥ (X.mat *ᵥ ![1,0]) = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using! hz
  have hk := (HermitianMat.zero_le_iff.mp hX).dotProduct_mulVec_zero_iff.mp hquad
  have hcol : X.mat 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using! congrFun hk 1
  simpa only [hcol, star_zero] using! (X.H.apply 0 1).symm

/-- No positive semidefinite two by two matrix has first diagonal real part zero and upper
off-diagonal real part one. -/
theorem weak_corner_infeasible :
    ¬ ∃ X : HermitianMat (Fin 2) ℂ,
      0 ≤ X ∧ (X.mat 0 0).re = 0 ∧ (X.mat 0 1).re = 1 := by
  rintro ⟨X, hX, hzero, hone⟩
  rw [zero_corner_forces_zero_offdiagonal X hX hzero] at hone
  norm_num at hone

/-- For every positive `ε`, a positive semidefinite two by two matrix has first diagonal real
part `ε` and upper off-diagonal real part one. -/
theorem weak_corner_approximate (ε : ℝ) (hε : 0 < ε) :
    ∃ X : HermitianMat (Fin 2) ℂ,
      0 ≤ X ∧ (X.mat 0 0).re = ε ∧ (X.mat 0 1).re = 1 := by
  let v : Fin 2 → ℂ := ![(Real.sqrt ε : ℂ), ((Real.sqrt ε)⁻¹ : ℝ)]
  have hp := Matrix.posSemidef_vecMulVec_self_star v
  refine ⟨⟨Matrix.vecMulVec v (star v), hp.1⟩, HermitianMat.zero_le_iff.mpr hp, ?_, ?_⟩
  · simp only [HermitianMat.mat_mk, Matrix.vecMulVec_apply, v, Matrix.cons_val_zero,
      Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    exact Real.mul_self_sqrt hε.le
  · have hs : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε).ne'
    change (v 0 * star (v 1)).re = 1
    simp [v, hs]

/-- A linear functional nonnegative on the indicated positive semidefinite matrix coordinates
has nonnegative coefficient `b`. -/
theorem weak_corner_no_strict_separator (a b : ℝ)
    (hdual : ∀ X : HermitianMat (Fin 2) ℂ, 0 ≤ X →
      0 ≤ a * (X.mat 0 0).re + b * (X.mat 0 1).re) : 0 ≤ b := by
  by_contra hb
  have hb' : b < 0 := lt_of_not_ge hb
  let ε : ℝ := -b / (|a| + 1)
  have hd : 0 < |a| + 1 := by positivity
  have hε : 0 < ε := div_pos (neg_pos.mpr hb') hd
  obtain ⟨X, hX, hzero, hone⟩ := weak_corner_approximate ε hε
  have h := hdual X hX
  rw [hzero, hone, mul_one] at h
  have heq : (|a| + 1) * ε = -b := by
    dsimp [ε]
    field_simp
  have ha := mul_le_mul_of_nonneg_right (le_abs_self a) hε.le
  nlinarith

/-- Every entry in a row of a positive semidefinite matrix vanishes if the diagonal entry in
that row has real part zero. -/
theorem zero_diagonal_row {I : Type*} [Fintype I] [DecidableEq I]
    (X : HermitianMat I ℂ) (hX : 0 ≤ X) (i : I) (hi : (X.mat i i).re = 0)
    (j : I) : X.mat i j = 0 := by
  have hz : X.mat i i = 0 := by
    apply Complex.ext hi
    have h := congrArg Complex.im (X.H.apply i i)
    simp only [RCLike.star_def, Complex.conj_im] at h
    simp only [Complex.zero_im]
    linarith
  have hquad : star (Pi.single i 1 : I → ℂ) ⬝ᵥ
      (X.mat *ᵥ Pi.single i 1) = 0 := by
    simpa [dotProduct, Pi.single_apply] using! hz
  have hk := (HermitianMat.zero_le_iff.mp hX).dotProduct_mulVec_zero_iff.mp hquad
  have hc : X.mat j i = 0 := by simpa using! congrFun hk j
  simpa only [hc, star_zero] using! (X.H.apply i j).symm

/-- Feasibility for the boundary example: a positive semidefinite two by two matrix with
diagonal entries of real parts one and zero. -/
def boundaryPrimal (X : HermitianMat (Fin 2) ℂ) : Prop :=
  0 ≤ X ∧ (X.mat 0 0).re = 1 ∧ (X.mat 1 1).re = 0

/-- The two by two dual slack matrix with diagonal entries `s` and `t` and off-diagonal entries
minus one. -/
def boundaryDual (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(s : ℂ), -1; -1, (t : ℂ)]

/-- The real trace pairing with `boundaryDual s t` equals the weighted diagonal sum minus twice
the real upper off-diagonal entry. -/
theorem boundary_dual_pairing (s t : ℝ) (X : HermitianMat (Fin 2) ℂ) :
    (Matrix.trace (boundaryDual s t * X.mat)).re =
      s * (X.mat 0 0).re + t * (X.mat 1 1).re - 2 * (X.mat 0 1).re := by
  have h := congrArg Complex.re (X.H.apply 0 1)
  simp only [RCLike.star_def, Complex.conj_re] at h
  change (X 1 0).re = (X 0 1).re at h
  simp only [boundaryDual, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [Matrix.of_apply, Complex.mul_re]
  linarith

/-- Every boundary primal feasible matrix has objective value zero. -/
theorem boundary_primal_value (X : HermitianMat (Fin 2) ℂ) (hX : boundaryPrimal X) :
    2 * (X.mat 0 1).re = 0 := by
  have hz := zero_diagonal_row X hX.1 1 hX.2.2 0
  have h := congrArg Complex.re (X.H.apply 0 1)
  simp only [hz, RCLike.star_def, Complex.conj_re, Complex.zero_re] at h
  linarith

/-- A boundary primal feasible matrix cannot be positive definite. -/
theorem boundary_primal_no_strict_feasibility (X : HermitianMat (Fin 2) ℂ)
    (hX : boundaryPrimal X) : ¬ X.mat.PosDef := by
  intro hp
  have hz := zero_diagonal_row X hX.1 1 hX.2.2 1
  have hpos := hp.diag_pos (i := 1)
  rw [hz] at hpos
  exact (lt_irrefl _) hpos

/-- The boundary primal problem has a feasible matrix attaining objective value zero. -/
theorem boundary_primal_attained :
    ∃ X : HermitianMat (Fin 2) ℂ, boundaryPrimal X ∧ 2 * (X.mat 0 1).re = 0 := by
  let v : Fin 2 → ℂ := ![1,0]
  have hp := Matrix.posSemidef_vecMulVec_self_star v
  refine ⟨⟨_,hp.1⟩, ⟨HermitianMat.zero_le_iff.mpr hp, ?_, ?_⟩, ?_⟩
  · change (v 0 * star (v 0)).re = 1
    norm_num [v]
  · change (v 1 * star (v 1)).re = 0
    norm_num [v]
  · change 2 * (v 0 * star (v 1)).re = 0
    norm_num [v]

/-- A positive semidefinite boundary dual slack with first diagonal entry `s` exists exactly
when `s` is positive. -/
theorem boundary_dual_feasible_iff (s : ℝ) :
    (∃ t : ℝ, (boundaryDual s t).PosSemidef) ↔ 0 < s := by
  constructor
  · rintro ⟨t, ht⟩
    have hs : 0 ≤ s := by
      have h := ht.diag_nonneg (i := 0)
      simpa [boundaryDual] using! h
    apply lt_of_le_of_ne hs
    intro hz
    let X : HermitianMat (Fin 2) ℂ := ⟨boundaryDual s t, ht.1⟩
    have hzero : (X.mat 0 0).re = 0 := by
      change s = 0
      exact hz.symm
    have h := zero_diagonal_row X (HermitianMat.zero_le_iff.mpr ht) 0 hzero 1
    change (-1 : ℂ) = 0 at h
    norm_num at h
  · intro hs
    let v : Fin 2 → ℂ := ![(Real.sqrt s : ℂ), (-(Real.sqrt s)⁻¹ : ℝ)]
    have hp := Matrix.posSemidef_vecMulVec_self_star v
    have heq : Matrix.vecMulVec v (star v) = boundaryDual s s⁻¹ := by
      have hroot : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
      have hsq := Real.mul_self_sqrt hs.le
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [v, boundaryDual, Matrix.vecMulVec, hroot, ← Complex.ofReal_mul,
          hsq, ← _root_.mul_inv_rev]
    exact ⟨s⁻¹, heq ▸ hp⟩

/-- The boundary dual objective values have infimum zero, and no boundary dual feasible point
attains zero. -/
theorem boundary_dual_infimum_not_attained :
    IsGLB {s : ℝ | ∃ t : ℝ, (boundaryDual s t).PosSemidef} 0 ∧
      ¬ ∃ t : ℝ, (boundaryDual 0 t).PosSemidef := by
  constructor
  · constructor
    · intro s hs
      exact ((boundary_dual_feasible_iff s).mp hs).le
    · intro b hb
      by_contra h
      have hbpos : 0 < b := lt_of_not_ge h
      have hhalf := hb ((boundary_dual_feasible_iff (b/2)).mpr (by positivity))
      linarith
  · rw [boundary_dual_feasible_iff]
    exact lt_irrefl _

/-- Positive definite Hermitian matrices form an open set. -/
theorem posDef_isOpen (I : Type*) [Fintype I] [DecidableEq I] :
    IsOpen {X : HermitianMat I ℂ | X.mat.PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro X hX
  have hs : spectrum ℝ X.mat ⊆ Set.Ioi 0 := by
    rw [X.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact (X.H.posDef_iff_eigenvalues_pos.mp hX) i
  filter_upwards [HermitianMat.spectrum_subset_of_isOpen X (Set.Ioi 0) isOpen_Ioi hs] with Y hY
  exact Y.H.posDef_iff_eigenvalues_pos.mpr fun i =>
    hY (Y.H.spectrum_real_eq_range_eigenvalues.symm ▸ Set.mem_range_self i)

/-- A positive definite matrix lies in the interior of the positive semidefinite cone. -/
theorem posDef_mem_interior {I : Type*} [Fintype I] [DecidableEq I]
    {X : HermitianMat I ℂ} (hX : X.mat.PosDef) :
    X ∈ interior (psdCone I : Set (HermitianMat I ℂ)) := by
  exact (posDef_isOpen I).subset_interior_iff.mpr
    (fun Y hY => HermitianMat.zero_le_iff.mpr hY.posSemidef) hX

/-- Every interior point of the positive semidefinite cone is positive definite. -/
theorem interior_posDef {I : Type*} [Fintype I] [DecidableEq I]
    {X : HermitianMat I ℂ} (hX : X ∈ interior (psdCone I : Set (HermitianMat I ℂ))) :
    X.mat.PosDef := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hX)
  let t : ℝ := ε / (2 * (‖(1 : HermitianMat I ℂ)‖ + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : dist (X - t • 1) X < ε := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖(1 : HermitianMat I ℂ)‖ + 1))).mpr
    nlinarith [norm_nonneg (1 : HermitianMat I ℂ)]
  have hPSD := HermitianMat.zero_le_iff.mp (hball hdist)
  have hp : (t • (1 : HermitianMat I ℂ)).mat.PosDef := Matrix.PosDef.one.smul ht
  have h := hp.add_posSemidef hPSD
  change (t • (1 : HermitianMat I ℂ) + (X - t • 1)).mat.PosDef at h
  have heq : t • (1 : HermitianMat I ℂ) + (X - t • 1) = X := by abel
  rwa [heq] at h

/-- Positive definiteness is equivalent to membership in the interior of the positive
semidefinite cone. -/
theorem posDef_iff_mem_interior {I : Type*} [Fintype I] [DecidableEq I]
    (X : HermitianMat I ℂ) :
    X.mat.PosDef ↔ X ∈ interior (psdCone I : Set (HermitianMat I ℂ)) :=
  ⟨posDef_mem_interior, interior_posDef⟩

/-- Pairing with a positive definite matrix bounds the norm of every positive semidefinite
matrix below by a fixed positive multiple. -/
theorem posDef_coercive {I : Type*} [Fintype I] [DecidableEq I]
    {S : HermitianMat I ℂ} (hS : S.mat.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : HermitianMat I ℂ, 0 ≤ X → c * ‖X‖ ≤ ⟪S, X⟫_ℝ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp (posDef_mem_interior hS))
  refine ⟨ε / 2, half_pos hε, fun X hX => ?_⟩
  by_cases hz : X = 0
  · simp [hz]
  have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hz
  let r : ℝ := (ε / 2) / ‖X‖
  have hr : 0 < r := div_pos (half_pos hε) hnorm
  have hmul : r * ‖X‖ = ε / 2 := div_mul_cancel₀ _ hnorm.ne'
  have hd : dist (S - r • X) S < ε := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, hmul]
    linarith
  have hY : 0 ≤ S - r • X := hball hd
  have h := HermitianMat.inner_ge_zero hX hY
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hs : r * ‖X‖ ^ 2 = ε / 2 * ‖X‖ := by rw [pow_two, ← mul_assoc, hmul]
  rw [hs] at h
  simpa only [real_inner_comm] using! (sub_nonneg.mp h)

namespace Program
variable {I F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Every primal feasible score is at most every dual feasible score. -/
theorem weak_duality (P : Program I F) {X : HermitianMat I ℂ} {y : F}
    (hX : P.PrimalFeasible X) (hy : P.DualFeasible y) :
    P.primalScore X ≤ P.dualScore y := by
  calc
    ⟪P.objective, X⟫_ℝ ≤ ⟪P.constraint.adjoint y, X⟫_ℝ :=
      HermitianMat.inner_mono' hX.1 (sub_nonneg.mp hy)
    _ = ⟪y, P.constraint X⟫_ℝ := P.constraint.adjoint_inner_left X y
    _ = ⟪y, P.rhs⟫_ℝ := congrArg (fun z : F => ⟪y, z⟫_ℝ) hX.2
    _ = ⟪P.rhs, y⟫_ℝ := real_inner_comm _ _

/-- Primal and dual feasibility make both value sets nonempty, with primal values bounded above
and dual values bounded below. -/
theorem feasible_values_bounded (P : Program I F)
    {X : HermitianMat I ℂ} {y : F} (hX : P.PrimalFeasible X) (hy : P.DualFeasible y) :
    P.primalValues.Nonempty ∧ BddAbove P.primalValues ∧
      P.dualValues.Nonempty ∧ BddBelow P.dualValues := by
  refine ⟨⟨_, X, hX, rfl⟩, ⟨P.dualScore y, ?_⟩, ⟨_, y, hy, rfl⟩,
    ⟨P.primalScore X, ?_⟩⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality P) hZ hy
  · rintro _ ⟨z, hz, rfl⟩
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality P) hX hz

/-- If every positive multiple of `a` is strictly below a fixed real bound, then `a` is
nonpositive. -/
private theorem nonpos_of_bounded_ray (a b : ℝ) (h : ∀ t : ℝ, 0 < t → t * a < b) :
    a ≤ 0 := by
  by_contra hn
  have ha : 0 < a := lt_of_not_ge hn
  have hh := h ((|b| + 1) / a) (by positivity)
  rw [div_mul_cancel₀ _ ha.ne'] at hh
  linarith [le_abs_self b]

/-- A strict upper bound for all positive multiples of a real number is nonnegative. -/
private theorem nonneg_of_scaled_upper (a b : ℝ) (h : ∀ t : ℝ, 0 < t → t * a < b) :
    0 ≤ b := by
  by_contra hn
  have hb : b < 0 := lt_of_not_ge hn
  let t : ℝ := -b / (|a| + 1)
  have ht : 0 < t := div_pos (neg_pos.mpr hb) (by positivity)
  have heq : t * (|a| + 1) = -b := by dsimp [t]; field_simp
  have hh := h t ht
  have hlow := mul_le_mul_of_nonneg_left (neg_abs_le a) ht.le
  nlinarith

/-- For a surjective constraint map, primal Slater feasibility makes any finite primal supremum
attainable by a dual feasible point. -/
theorem primalSlater_dual_attained_of_surjective (P : Program I F)
    [FiniteDimensional ℝ F] (honto : Function.Surjective P.constraint)
    (hslater : P.PrimalSlater) {α : ℝ} (hα : IsLUB P.primalValues α) :
    ∃ y : F, P.DualFeasible y ∧ P.dualScore y = α := by
  classical
  obtain ⟨X₀, hX₀, hb₀⟩ := hslater
  let U : Set (HermitianMat I ℂ × ℝ) :=
    {X : HermitianMat I ℂ | X.mat.PosDef} ×ˢ Set.Ioi 0
  let Ω : Set (F × ℝ) := P.perturbationMap '' U
  have hopenU : IsOpen U := (posDef_isOpen I).prod isOpen_Ioi
  have hconvPD : Convex ℝ {X : HermitianMat I ℂ | X.mat.PosDef} := by
    intro X hX Y hY a b ha hb hab
    exact Matrix.PosDef.Convex hX hY ha hb hab
  have hconvU : Convex ℝ U := hconvPD.prod (convex_Ioi 0)
  have hontoL : Function.Surjective P.perturbationMap := by
    rintro ⟨b, a⟩
    obtain ⟨X, hX⟩ := honto b
    refine ⟨(X, P.primalScore X - a), ?_⟩
    change (P.constraint X, ⟪P.objective, X⟫_ℝ - (P.primalScore X - a)) = (b, a)
    simp only [hX, primalScore, sub_sub_cancel]
  have hopen : IsOpen Ω := P.perturbationMap.isOpenMap hontoL U hopenU
  have hconv : Convex ℝ Ω := hconvU.linear_image P.perturbationMap.toLinearMap
  have houtside : (P.rhs, α) ∉ Ω := by
    rintro ⟨⟨X, r⟩, ⟨hX, hr⟩, heq⟩
    have hb : P.constraint X = P.rhs := congrArg Prod.fst heq
    have ha : P.primalScore X - r = α := congrArg Prod.snd heq
    have hupper : P.primalScore X ≤ α :=
        hα.1 ⟨X, ⟨HermitianMat.zero_le_iff.mpr hX.posSemidef, hb⟩, rfl⟩
    change 0 < r at hr
    linarith
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv hopen houtside
  let y : F := (InnerProductSpace.toDual ℝ F).symm
    (f.comp (ContinuousLinearMap.inl ℝ F ℝ))
  let β : ℝ := f (0,1)
  have hy (b : F) : ⟪y, b⟫_ℝ = f (b,0) := InnerProductSpace.toDual_symm_apply
  have hfz (v : F × ℝ) : f v = ⟪y, v.1⟫_ℝ + β * v.2 := by
    rw [hy]
    have heq : v = (v.1,0) + v.2 • (0,1) := by ext <;> simp
    calc
      f v = f ((v.1,0) + v.2 • (0,1)) := congrArg f heq
      _ = f (v.1,0) + β * v.2 := by rw [map_add, map_smul]; dsimp [β]; ring
  have hsep (X : HermitianMat I ℂ) (hX : X.mat.PosDef) (r : ℝ) (hr : 0 < r) :
      ⟪y, P.constraint X⟫_ℝ + β * (P.primalScore X - r) <
        ⟪y, P.rhs⟫_ℝ + β * α := by
    have h := hf (P.perturbationMap (X, r)) ⟨(X,r), ⟨hX,hr⟩, rfl⟩
    rw [hfz, hfz] at h
    exact h
  have hβnonneg : 0 ≤ β := by
    have h := nonpos_of_bounded_ray (-β)
      (β * α - β * P.primalScore X₀) (fun r hr => by
        have hh := hsep X₀ hX₀ r hr
        rw [hb₀] at hh
        linarith)
    linarith
  have hβ : 0 < β := by
    apply lt_of_le_of_ne hβnonneg
    intro heq
    have h := hsep X₀ hX₀ 1 zero_lt_one
    rw [hb₀, ← heq] at h
    simp at h
  have hnegative : 0 ≤ -(P.constraint.adjoint y + β • P.objective) := by
    apply (HermitianMat.nonneg_iff_inner_nonneg _).mpr
    intro X hX
    have hbound := nonpos_of_bounded_ray
      (⟪y, P.constraint X⟫_ℝ + β * P.primalScore X)
      (⟪y, P.rhs⟫_ℝ + β * α - ⟪y, P.constraint X₀⟫_ℝ -
        β * (P.primalScore X₀ - 1)) (fun t ht => by
          have hpd : (X₀ + t • X).mat.PosDef :=
            hX₀.add_posSemidef ((HermitianMat.zero_le_iff.mp hX).smul ht.le)
          have hh := hsep (X₀ + t • X) hpd 1 zero_lt_one
          simp only [map_add, map_smul, inner_add_right, inner_smul_right,
            primalScore] at hh ⊢
          nlinarith)
    simpa only [inner_neg_right, inner_add_right, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right, real_inner_comm, primalScore]
      using! neg_nonneg.mpr hbound
  have hconstant : 0 ≤ ⟪y, P.rhs⟫_ℝ + β * α := by
    apply nonneg_of_scaled_upper
      (⟪y, P.constraint X₀⟫_ℝ + β * (P.primalScore X₀ - 1))
    intro t ht
    have hpd : (t • X₀).mat.PosDef := hX₀.smul ht
    have hh := hsep (t • X₀) hpd t ht
    simp only [map_smul, inner_smul_right, primalScore] at hh ⊢
    nlinarith
  let ystar : F := -(β⁻¹) • y
  have hdual : P.DualFeasible ystar := by
    have heq : P.constraint.adjoint ystar - P.objective =
        β⁻¹ • -(P.constraint.adjoint y + β • P.objective) := by
      simp only [ystar, map_smul, smul_neg, smul_add, smul_smul,
        inv_mul_cancel₀ hβ.ne', one_smul]
      module
    rw [DualFeasible, heq]
    exact smul_nonneg (inv_nonneg.mpr hβ.le) hnegative
  have hscore : P.dualScore ystar = -⟪y, P.rhs⟫_ℝ / β := by
    simp only [dualScore, ystar, inner_smul_right, real_inner_comm, div_eq_mul_inv]
    ring
  refine ⟨ystar, hdual, le_antisymm ?_ ?_⟩
  · rw [hscore]
    exact (div_le_iff₀ hβ).mpr (by linarith)
  · apply hα.2
    rintro _ ⟨X, hX, rfl⟩
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality P) hX hdual

/-- Primal Slater feasibility makes any finite primal supremum attainable by a dual feasible
point. -/
theorem primalSlater_dual_attained (P : Program I F) (hslater : P.PrimalSlater)
    {α : ℝ} (hα : IsLUB P.primalValues α) :
    ∃ y : F, P.DualFeasible y ∧ P.dualScore y = α := by
  classical
  obtain ⟨X₀, hX₀, hb₀⟩ := hslater
  let R : Submodule ℝ F := LinearMap.range P.constraint.toLinearMap
  let Q : Program I R :=
    { constraint := P.constraint.codRestrict R (fun X => ⟨X, rfl⟩)
      rhs := ⟨P.rhs, ⟨X₀, hb₀⟩⟩
      objective := P.objective }
  have honto : Function.Surjective Q.constraint := by
    rintro ⟨b, ⟨X, hX⟩⟩
    exact ⟨X, Subtype.ext hX⟩
  have hstrict : Q.PrimalSlater :=
    ⟨X₀, hX₀, Subtype.ext hb₀⟩
  have hvalues : Q.primalValues = P.primalValues := by
    ext a
    constructor
    · rintro ⟨X, ⟨hX, hb⟩, ha⟩
      exact ⟨X, ⟨hX, congrArg Subtype.val hb⟩, ha⟩
    · rintro ⟨X, ⟨hX, hb⟩, ha⟩
      exact ⟨X, ⟨hX, Subtype.ext hb⟩, ha⟩
  obtain ⟨y, hy, hscore⟩ := (Qatlib.Concepts.SdpDuality.StrongDuality.Program.primalSlater_dual_attained_of_surjective Q) honto hstrict
    (hvalues ▸ hα)
  have hadj : Q.constraint.adjoint y = P.constraint.adjoint (y : F) := by
    apply ext_inner_right ℝ
    intro X
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    rfl
  refine ⟨(y : F), ?_, hscore⟩
  change 0 ≤ P.constraint.adjoint (y : F) - P.objective
  rw [← hadj]
  exact hy

/-- Primal Slater feasibility and dual feasibility yield a common primal supremum and dual
infimum, attained on the dual side; see [Watrous2018]. -/
theorem primalSlater_strong_duality (P : Program I F) (hslater : P.PrimalSlater)
    {y₀ : F} (hy₀ : P.DualFeasible y₀) :
    ∃ α : ℝ, IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
      ∃ y : F, P.DualFeasible y ∧ P.dualScore y = α := by
  obtain ⟨X₀, hX₀, hb₀⟩ := hslater
  have hfeas : P.PrimalFeasible X₀ := ⟨HermitianMat.zero_le_iff.mpr hX₀.posSemidef, hb₀⟩
  obtain ⟨hne, hbdd, -, -⟩ :=
      (Qatlib.Concepts.SdpDuality.StrongDuality.Program.feasible_values_bounded (P := P)) hfeas hy₀
  let α : ℝ := sSup P.primalValues
  have hα : IsLUB P.primalValues α := isLUB_csSup hne hbdd
  obtain ⟨y, hy, hscore⟩ :=
      (Qatlib.Concepts.SdpDuality.StrongDuality.Program.primalSlater_dual_attained (P := P)) ⟨X₀, hX₀, hb₀⟩ hα
  refine ⟨α, hα, ⟨?_, ?_⟩, y, hy, hscore⟩
  · rintro _ ⟨z, hz, rfl⟩
    apply hα.2
    rintro _ ⟨X, hX, rfl⟩
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality P) hX hz
  · intro b hb
    exact hscore ▸ hb ⟨y, hy, rfl⟩

/-- Primal feasible points of the dual slack program are exactly the slack matrices of dual
feasible points of `P`. -/
theorem dualSlackProgram_primal_iff (P : Program I F) (X₀ S : HermitianMat I ℂ) :
    (P.dualSlackProgram X₀).PrimalFeasible S ↔
      ∃ y : F, P.DualFeasible y ∧ P.constraint.adjoint y - P.objective = S := by
  let K : Submodule ℝ (HermitianMat I ℂ) := P.constraint.ker
  have horth : Kᗮ = P.constraint.adjoint.range := by
    rw [P.constraint.orthogonal_ker]
    exact P.constraint.adjoint.range.topologicalClosure_eq_self
  constructor
  · rintro ⟨hS, heq⟩
    have hp : K.orthogonalProjection (S + P.objective) = 0 := by
      change K.orthogonalProjection S = -K.orthogonalProjection P.objective at heq
      rw [map_add, heq, neg_add_cancel]
    have hr := Submodule.orthogonalProjection_eq_zero_iff.mp hp
    rw [horth] at hr
    obtain ⟨y, hy⟩ := hr
    change P.constraint.adjoint y = S + P.objective at hy
    have hs : P.constraint.adjoint y - P.objective = S := by rw [hy]; abel
    refine ⟨y, ?_, hs⟩
    change 0 ≤ P.constraint.adjoint y - P.objective
    rwa [hs]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hy, ?_⟩
    change K.orthogonalProjection (P.constraint.adjoint y - P.objective) =
      -K.orthogonalProjection P.objective
    have hp : K.orthogonalProjection (P.constraint.adjoint y) = 0 := by
      apply Submodule.orthogonalProjection_eq_zero_iff.mpr
      rw [horth]
      exact ⟨y, rfl⟩
    rw [map_sub, hp, zero_sub]

omit [CompleteSpace F] in

/-- Dual feasibility in the dual slack program is equivalent to primal feasibility of the
corresponding kernel translate of `X₀`. -/
theorem dualSlackProgram_dual_iff (P : Program I F) {X₀ : HermitianMat I ℂ}
    (hX₀ : P.PrimalFeasible X₀) (z : P.constraint.ker) :
    (P.dualSlackProgram X₀).DualFeasible z ↔ P.PrimalFeasible (X₀ + (z : HermitianMat I ℂ)) := by
  have hadj : (P.dualSlackProgram X₀).constraint.adjoint z = (z : HermitianMat I ℂ) := by
    exact congrArg (fun L => L z) (Submodule.adjoint_orthogonalProjection P.constraint.ker)
  have heq : P.constraint (X₀ + (z : HermitianMat I ℂ)) = P.rhs := by
    rw [map_add, show P.constraint (z : HermitianMat I ℂ) = 0 from z.property,
      add_zero]
    exact hX₀.2
  change (0 ≤ (P.dualSlackProgram X₀).constraint.adjoint z - -X₀) ↔
    0 ≤ X₀ + (z : HermitianMat I ℂ) ∧ _
  rw [hadj, sub_neg_eq_add, add_comm (z : HermitianMat I ℂ) X₀]
  exact ⟨fun h => ⟨h, heq⟩, And.left⟩

/-- At a dual slack, the dual slack program's primal score is the original primal score at `X₀`
minus the original dual score. -/
theorem dualSlackProgram_primalScore (P : Program I F) {X₀ : HermitianMat I ℂ}
    (hX₀ : P.constraint X₀ = P.rhs) (y : F) :
    (P.dualSlackProgram X₀).primalScore (P.constraint.adjoint y - P.objective) =
      P.primalScore X₀ - P.dualScore y := by
  change ⟪-X₀, P.constraint.adjoint y - P.objective⟫_ℝ =
    ⟪P.objective, X₀⟫_ℝ - ⟪P.rhs, y⟫_ℝ
  rw [inner_neg_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  have heq : ⟪P.constraint X₀, y⟫_ℝ = ⟪P.rhs, y⟫_ℝ := congrArg (fun b => ⟪b,y⟫_ℝ) hX₀
  change -(⟪P.constraint X₀, y⟫_ℝ - ⟪X₀, P.objective⟫_ℝ) =
    ⟪P.objective, X₀⟫_ℝ - ⟪P.rhs, y⟫_ℝ
  rw [heq, real_inner_comm X₀ P.objective]
  ring

omit [CompleteSpace F] in

/-- The dual slack program's dual score is the drop in the original primal score under the
kernel translate. -/
theorem dualSlackProgram_dualScore (P : Program I F) (X₀ : HermitianMat I ℂ)
    (z : P.constraint.ker) :
    (P.dualSlackProgram X₀).dualScore z =
      P.primalScore X₀ - P.primalScore (X₀ + (z : HermitianMat I ℂ)) := by
  change ⟪-P.constraint.ker.orthogonalProjection P.objective, z⟫_ℝ =
    ⟪P.objective, X₀⟫_ℝ - ⟪P.objective, X₀ + (z : HermitianMat I ℂ)⟫_ℝ
  rw [inner_neg_left, Submodule.inner_orthogonalProjection_eq_of_mem_right,
    inner_add_right]
  ring

/-- Dual Slater feasibility and primal feasibility yield a common primal supremum and dual
infimum, attained on the primal side; see [Watrous2018]. -/
theorem dualSlater_strong_duality (P : Program I F) (hslater : P.DualSlater)
    {X₀ : HermitianMat I ℂ} (hX₀ : P.PrimalFeasible X₀) :
    ∃ α : ℝ, IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
      ∃ X : HermitianMat I ℂ, P.PrimalFeasible X ∧ P.primalScore X = α := by
  obtain ⟨y₀, hy₀⟩ := hslater
  let Q := P.dualSlackProgram X₀
  have hstrict : Q.PrimalSlater := by
    refine ⟨P.constraint.adjoint y₀ - P.objective, hy₀, ?_⟩
    exact (((Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlackProgram_primal_iff (P := P)) X₀ _).mpr
      ⟨y₀, HermitianMat.zero_le_iff.mpr hy₀.posSemidef, rfl⟩).2
  have hzero : Q.DualFeasible 0 := by
    apply ((Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlackProgram_dual_iff (P := P)) hX₀ 0).mpr
    simpa using! hX₀
  obtain ⟨β, hβlub, -, z, hz, hscore⟩ :=
      (Qatlib.Concepts.SdpDuality.StrongDuality.Program.primalSlater_strong_duality (P := Q)) hstrict hzero
  let X : HermitianMat I ℂ := X₀ + (z : HermitianMat I ℂ)
  let α : ℝ := P.primalScore X₀ - β
  have hX : P.PrimalFeasible X :=
      ((Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlackProgram_dual_iff (P := P)) hX₀ z).mp hz
  have hscoreX : P.primalScore X = α := by
    rw [(Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlackProgram_dualScore (P := P))] at hscore
    dsimp [X, α]
    linarith
  have hglb : IsGLB P.dualValues α := by
    constructor
    · rintro _ ⟨y, hy, rfl⟩
      rw [← hscoreX]
      exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality P) hX hy
    · intro b hb
      have hupper : β ≤ P.primalScore X₀ - b := by
        apply hβlub.2
        rintro _ ⟨S, hS, rfl⟩
        obtain ⟨y, hy, heq⟩ :=
            ((Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlackProgram_primal_iff (P := P)) X₀ S).mp hS
        rw [← heq,
            (Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlackProgram_primalScore (P := P)) hX₀.2]
        have hh := hb ⟨y, hy, rfl⟩
        linarith
      dsimp [α]
      linarith
  refine ⟨α, ⟨?_, ?_⟩, hglb, X, hX, hscoreX⟩
  · rintro _ ⟨Y, hY, rfl⟩
    apply hglb.2
    rintro _ ⟨y, hy, rfl⟩
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality P) hY hy
  · intro b hb
    rw [← hscoreX]
    exact hb ⟨X, hX, rfl⟩

/-- Under dual Slater feasibility, every primal superlevel set is compact. -/
theorem dualSlater_compact_superlevel (P : Program I F) (hslater : P.DualSlater) (a : ℝ) :
    IsCompact (P.primalSuperlevel a) := by
  obtain ⟨y, hy⟩ := hslater
  obtain ⟨c, hc, hbound⟩ := posDef_coercive hy
  have hclosed : IsClosed (P.primalSuperlevel a) :=
    ((psdCone I).isClosed.inter (isClosed_eq P.constraint.continuous continuous_const)).inter
      (isClosed_le continuous_const (innerSL ℝ P.objective).continuous)
  apply (isCompact_closedBall (0 : HermitianMat I ℂ) ((P.dualScore y - a) / c)).of_isClosed_subset hclosed
  intro X hX
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (le_div_iff₀ hc).mpr
  have h := hbound X hX.1.1
  have heq : ⟪P.constraint.adjoint y - P.objective, X⟫_ℝ =
      P.dualScore y - P.primalScore X := by
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
    change ⟪y, P.constraint X⟫_ℝ - ⟪P.objective, X⟫_ℝ = _
    rw [hX.1.2]
    exact congrArg (fun v => v - ⟪P.objective, X⟫_ℝ) (real_inner_comm _ _)
  rw [heq] at h
  have ha : a ≤ P.primalScore X := hX.2
  nlinarith

/-- Slater feasibility on both sides yields primal and dual optimizers with the same value; see
[Watrous2018]. -/
theorem bothSlater_optimizers (P : Program I F) (hp : P.PrimalSlater) (hd : P.DualSlater) :
    ∃ (α : ℝ) (X : HermitianMat I ℂ) (y : F),
      P.PrimalFeasible X ∧ P.DualFeasible y ∧
      IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
      P.primalScore X = α ∧ P.dualScore y = α := by
  obtain ⟨X₀, hX₀, hb₀⟩ := hp
  obtain ⟨y₀, hy₀⟩ := hd
  have hpf : P.PrimalFeasible X₀ := ⟨HermitianMat.zero_le_iff.mpr hX₀.posSemidef, hb₀⟩
  have hdf : P.DualFeasible y₀ := HermitianMat.zero_le_iff.mpr hy₀.posSemidef
  obtain ⟨α, hα, hglb, y, hy, hsy⟩ :=
    (Qatlib.Concepts.SdpDuality.StrongDuality.Program.primalSlater_strong_duality (P := P)) ⟨X₀, hX₀, hb₀⟩ hdf
  obtain ⟨β, hβ, -, X, hX, hsX⟩ :=
    (Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlater_strong_duality (P := P)) ⟨y₀, hy₀⟩ hpf
  have heq : β = α := hβ.unique hα
  exact ⟨α, X, y, hX, hy, hα, hglb, heq ▸ hsX, hsy⟩

end Program

/-- Block pinching retains the two diagonal blocks and sets the off-diagonal blocks to zero. -/
@[simp] theorem blockPinch_apply {I : Type*} [Fintype I] (X : HermitianMat (I ⊕ I) ℂ)
    (r c : I ⊕ I) :
    (blockPinch X).mat r c = match r, c with
      | Sum.inl i, Sum.inl j => X.mat (Sum.inl i) (Sum.inl j)
      | Sum.inr i, Sum.inr j => X.mat (Sum.inr i) (Sum.inr j)
      | _, _ => 0 := rfl

/-- Block pinching can be moved between the two arguments of the real inner product. -/
theorem blockPinch_inner {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : HermitianMat (I ⊕ I) ℂ) :
    ⟪blockPinch X, Y⟫_ℝ = ⟪X, blockPinch Y⟫_ℝ := by
  rw [inner_eq_real_trace, inner_eq_real_trace]
  apply congrArg Complex.re
  change (∑ i, ∑ j, (blockPinch X).mat i j * Y.mat j i) =
    ∑ i, ∑ j, X.mat i j * (blockPinch Y).mat j i
  simp only [Fintype.sum_sum_type, blockPinch_apply, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]

/-- Block pinching is self-adjoint as a real continuous linear map. -/
@[simp] theorem blockPinch_adjoint {I : Type*} [Fintype I] [DecidableEq I] :
    (blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint = blockPinch := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact blockPinch_inner

/-- Block pinching fixes block diagonal Hermitian matrices. -/
@[simp] theorem blockPinch_blockDiagonal {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ) :
    blockPinch (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q) = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q := by
  apply HermitianMat.ext
  ext r c
  cases r <;> cases c <;> rfl

/-- Block pinching fixes the identity matrix. -/
@[simp] theorem blockPinch_one {I : Type*} [Fintype I] [DecidableEq I] :
    blockPinch (1 : HermitianMat (I ⊕ I) ℂ) = 1 := by
  apply HermitianMat.ext
  ext r c
  change (blockPinch (1 : HermitianMat (I ⊕ I) ℂ)).mat r c =
    (1 : Matrix (I ⊕ I) (I ⊕ I) ℂ) r c
  rw [blockPinch_apply]
  cases r <;> cases c <;> simp [Matrix.one_apply]

/-- A block diagonal matrix with positive semidefinite diagonal blocks is positive semidefinite. -/
theorem blockDiagonal_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) : 0 ≤ Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q := by
  apply HermitianMat.zero_le_iff.mpr
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨(Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q).H, fun v => ?_⟩
  have hp' := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (HermitianMat.zero_le_iff.mp hP)).2 (fun i => v (Sum.inl i))
  have hq' := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (HermitianMat.zero_le_iff.mp hQ)).2 (fun i => v (Sum.inr i))
  simpa only [Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal, HermitianMat.mat_mk, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    Pi.star_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
    using! add_nonneg hp' hq'

/-- The fidelity program satisfies dual Slater feasibility for every pair of Hermitian input
matrices. -/
theorem fidelityProgram_dual_strict {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : (fidelityProgram P Q).DualSlater := by
  refine ⟨1, ?_⟩
  change ((blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint 1 -
    (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ)).mat.PosDef
  rw [blockPinch_adjoint]
  change ((blockPinch (1 : HermitianMat (I ⊕ I) ℂ)) -
    (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ)).mat.PosDef
  rw [blockPinch_one]
  have hg : (Matrix.fromBlocks (1 : Matrix I I ℂ) (-1 : Matrix I I ℂ) (-1 : Matrix I I ℂ) (1 : Matrix I I ℂ)).PosSemidef := by
    simpa using! Matrix.fromBlocks_gram_posSemidef (-1 : Matrix I I ℂ) (1 : Matrix I I ℂ)
  have heq : ((1 : HermitianMat (I ⊕ I) ℂ) -
      (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ)).mat =
      (1/2 : ℝ) • (1 : Matrix (I ⊕ I) (I ⊕ I) ℂ) +
        (1/2 : ℝ) • Matrix.fromBlocks (1 : Matrix I I ℂ) (-1 : Matrix I I ℂ) (-1 : Matrix I I ℂ) (1 : Matrix I I ℂ) := by
    simp only [HermitianMat.mat_sub, HermitianMat.mat_smul, HermitianMat.mat_one,
      offDiagonal, HermitianMat.mat_mk, Matrix.conjTranspose_one]
    ext r c
    cases r <;> cases c <;> simp [Matrix.one_apply]
    all_goals split_ifs <;> norm_num
  rw [heq]
  exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1/2)).add_posSemidef
    (hg.smul (by norm_num : (0 : ℝ) ≤ 1/2))

/-- For positive semidefinite inputs, the fidelity program has equal primal and dual optimal
values and a primal optimizer. -/
theorem fidelityProgram_strong_duality {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ∃ α : ℝ, IsLUB (fidelityProgram P Q).primalValues α ∧
      IsGLB (fidelityProgram P Q).dualValues α ∧
      ∃ X : HermitianMat (I ⊕ I) ℂ,
        (fidelityProgram P Q).PrimalFeasible X ∧
        (fidelityProgram P Q).primalScore X = α := by
  apply (Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlater_strong_duality (P := (fidelityProgram P Q))) (fidelityProgram_dual_strict P Q)
    (X₀ := Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q)
  exact ⟨blockDiagonal_nonneg hP hQ, blockPinch_blockDiagonal P Q⟩

/-- The trace of a block matrix is the sum of the traces of its diagonal blocks. -/
private theorem block_trace {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℂ) (B : Matrix I J ℂ) (C : Matrix J I ℂ) (D : Matrix J J ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  change (∑ i, Matrix.fromBlocks A B C D i i) = (∑ i, A i i) + ∑ i, D i i
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- Pinching a fidelity primal block yields the block diagonal matrix of its two fixed inputs. -/
@[simp] theorem blockPinch_fidelityPrimalBlock {I : Type*} [Fintype I]
    (P Q : HermitianMat I ℂ) (X : Matrix I I ℂ) :
    blockPinch (fidelityPrimalBlock P Q X) = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q := by
  apply HermitianMat.ext
  ext r c
  cases r <;> cases c <;> rfl

/-- The fidelity primal score of a block matrix is the real part of the trace of its
off-diagonal block. -/
theorem fidelityProgram_primalScore {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (X : Matrix I I ℂ) :
    (fidelityProgram P Q).primalScore (fidelityPrimalBlock P Q X) =
      (Matrix.trace X).re := by
  change ⟪(1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ), fidelityPrimalBlock P Q X⟫_ℝ = _
  rw [real_inner_smul_left, inner_eq_real_trace]
  simp only [offDiagonal, fidelityPrimalBlock, HermitianMat.mat_mk,
    Matrix.conjTranspose_one]
  change (1/2 : ℝ) * (Matrix.trace (Matrix.fromBlocks 0 (1 : Matrix I I ℂ) 1 0 *
    Matrix.fromBlocks P.mat X Xᴴ Q.mat)).re = _
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, one_mul, zero_add, add_zero, block_trace,
    Matrix.trace_conjTranspose, RCLike.star_def, Complex.add_re, Complex.conj_re]
  ring

/-- A fidelity primal block is feasible exactly when its underlying block matrix is positive
semidefinite. -/
theorem fidelityProgram_primal_block_iff {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (X : Matrix I I ℂ) :
    (fidelityProgram P Q).PrimalFeasible (fidelityPrimalBlock P Q X) ↔
      (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef := by
  change (0 ≤ fidelityPrimalBlock P Q X ∧
    blockPinch (fidelityPrimalBlock P Q X) = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q) ↔ _
  simp only [blockPinch_fidelityPrimalBlock, and_true, HermitianMat.zero_le_iff]
  rfl

/-- Every feasible fidelity primal matrix has the prescribed diagonal blocks and a freely chosen
cross block. -/
theorem fidelityProgram_primal_shape {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} {M : HermitianMat (I ⊕ I) ℂ}
    (hM : (fidelityProgram P Q).PrimalFeasible M) :
    ∃ X : Matrix I I ℂ, M = fidelityPrimalBlock P Q X := by
  refine ⟨M.mat.submatrix Sum.inl Sum.inr, ?_⟩
  apply HermitianMat.ext
  ext r c
  have hpinch : blockPinch M = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q :=
      hM.2
  cases r with
  | inl i =>
    cases c with
    | inl j =>
      change M.mat (Sum.inl i) (Sum.inl j) = P.mat i j
      exact congrArg (fun A : HermitianMat (I ⊕ I) ℂ => A.mat (Sum.inl i) (Sum.inl j)) hpinch
    | inr j => rfl
  | inr i =>
    cases c with
    | inl j =>
      change M.mat (Sum.inr i) (Sum.inl j) = star (M.mat (Sum.inl j) (Sum.inr i))
      exact (M.H.apply _ _).symm
    | inr j =>
      change M.mat (Sum.inr i) (Sum.inr j) = Q.mat i j
      exact congrArg (fun A : HermitianMat (I ⊕ I) ℂ => A.mat (Sum.inr i) (Sum.inr j)) hpinch

/-- The real inner product of block diagonal matrices is the sum of the inner products of
corresponding diagonal blocks. -/
theorem blockDiagonal_inner {I : Type*} [Fintype I] [DecidableEq I]
    (P Q Y Z : HermitianMat I ℂ) :
    ⟪Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q, Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z⟫_ℝ = ⟪P,Y⟫_ℝ + ⟪Q,Z⟫_ℝ := by
  simp only [inner_eq_real_trace]
  change (Matrix.trace (Matrix.fromBlocks P.mat 0 0 Q.mat *
    Matrix.fromBlocks Y.mat 0 0 Z.mat)).re = _
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, block_trace, Complex.add_re]

/-- The fidelity dual score at half a block diagonal matrix is half the sum of the two input
pairings. -/
theorem fidelityProgram_dualScore {I : Type*} [Fintype I] [DecidableEq I]
    (P Q Y Z : HermitianMat I ℂ) :
    (fidelityProgram P Q).dualScore ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) =
      (1/2 : ℝ) * ⟪P,Y⟫_ℝ + (1/2 : ℝ) * ⟪Q,Z⟫_ℝ := by
  change ⟪Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q,
      (1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z⟫_ℝ = _
  rw [inner_smul_right, blockDiagonal_inner, mul_add]

/-- The fidelity dual slack at half a block diagonal matrix is half the corresponding
`fidelityDualBlock`. -/
theorem fidelityProgram_dual_slack {I : Type*} [Fintype I] [DecidableEq I]
    (P Q Y Z : HermitianMat I ℂ) :
    (fidelityProgram P Q).constraint.adjoint ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) -
      (fidelityProgram P Q).objective = (1/2 : ℝ) • fidelityDualBlock Y Z := by
  change (blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint
    ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) - _ = _
  rw [blockPinch_adjoint]
  change blockPinch ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) -
    (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ) = _
  rw [map_smul]
  change (1/2 : ℝ) • blockPinch
      (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) - _ = _
  rw [blockPinch_blockDiagonal]
  exact (smul_sub (1/2 : ℝ) (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) (offDiagonal (1 : Matrix I I ℂ))).symm

/-- Block pinching is idempotent. -/
@[simp] theorem blockPinch_idempotent {I : Type*} [Fintype I]
    (Y : HermitianMat (I ⊕ I) ℂ) : blockPinch (blockPinch Y) = blockPinch Y := by
  apply HermitianMat.ext
  ext r c
  cases r <;> cases c <;> rfl

/-- The pinched matrix is half the block diagonal matrix formed from twice its two principal
blocks. -/
theorem fidelity_dual_coordinates {I : Type*} [Fintype I]
    (Y : HermitianMat (I ⊕ I) ℂ) :
    (1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal ((2 : ℝ) • principalBlock Y Sum.inl)
      ((2 : ℝ) • principalBlock Y Sum.inr) = blockPinch Y := by
  apply HermitianMat.ext
  ext r c
  change ((1/2 : ℝ) • Matrix.fromBlocks
    ((2 : ℝ) • Y.mat.submatrix Sum.inl Sum.inl) 0 0
    ((2 : ℝ) • Y.mat.submatrix Sum.inr Sum.inr)) r c = (blockPinch Y).mat r c
  rw [blockPinch_apply]
  cases r <;> cases c <;> simp [Matrix.smul_apply]

/-- Pinching preserves both dual feasibility and the dual score of the fidelity program. -/
theorem fidelityProgram_pinched_dual {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (Y : HermitianMat (I ⊕ I) ℂ) :
    ((fidelityProgram P Q).DualFeasible (blockPinch Y) ↔
      (fidelityProgram P Q).DualFeasible Y) ∧
      (fidelityProgram P Q).dualScore (blockPinch Y) = (fidelityProgram P Q).dualScore Y := by
  constructor
  · change (0 ≤ (blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint (blockPinch Y) - _) ↔
      (0 ≤ (blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint Y - _)
    rw [blockPinch_adjoint]
    change (0 ≤ blockPinch (blockPinch Y) - _) ↔ (0 ≤ blockPinch Y - _)
    rw [blockPinch_idempotent]
  · change ⟪Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q, blockPinch Y⟫_ℝ = ⟪Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q, Y⟫_ℝ
    rw [← blockPinch_inner, blockPinch_blockDiagonal]

/-- A half-scaled block diagonal dual point is fidelity dual feasible exactly when its
`fidelityDualBlock` is positive semidefinite. -/
theorem fidelityProgram_dual_block_iff {I : Type*} [Fintype I] [DecidableEq I]
    (P Q Y Z : HermitianMat I ℂ) :
    (fidelityProgram P Q).DualFeasible ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) ↔
      0 ≤ fidelityDualBlock Y Z := by
  change (0 ≤ (fidelityProgram P Q).constraint.adjoint ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) - _) ↔ _
  rw [fidelityProgram_dual_slack]
  constructor
  · intro h
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h
    simpa only [smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul] using! hh
  · exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)

/-- The fidelity program's primal value set equals `fidelityPrimalValues`. -/
theorem fidelityProgram_primalValues {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) :
    (fidelityProgram P Q).primalValues = fidelityPrimalValues P Q := by
  ext a
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨X, rfl⟩ := fidelityProgram_primal_shape hM
    exact ⟨X, (fidelityProgram_primal_block_iff P Q X).mp hM,
      (fidelityProgram_primalScore P Q X).symm⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨fidelityPrimalBlock P Q X, (fidelityProgram_primal_block_iff P Q X).mpr hX,
      fidelityProgram_primalScore P Q X⟩

/-- The fidelity program's dual value set equals `fidelityDualValues`. -/
theorem fidelityProgram_dualValues {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) :
    (fidelityProgram P Q).dualValues = fidelityDualValues P Q := by
  ext a
  constructor
  · rintro ⟨M, hM, rfl⟩
    refine ⟨(2 : ℝ) • principalBlock M Sum.inl, (2 : ℝ) • principalBlock M Sum.inr, ?_, ?_⟩
    · apply (fidelityProgram_dual_block_iff P Q _ _).mp
      rw [fidelity_dual_coordinates]
      exact (fidelityProgram_pinched_dual P Q M).1.mpr hM
    · rw [← fidelityProgram_dualScore, fidelity_dual_coordinates]
      exact (fidelityProgram_pinched_dual P Q M).2
  · rintro ⟨Y, Z, hYZ, rfl⟩
    exact ⟨(1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z,
      (fidelityProgram_dual_block_iff P Q Y Z).mpr hYZ,
      fidelityProgram_dualScore P Q Y Z⟩

/-- For positive semidefinite inputs, the block formulation of fidelity has a common primal
supremum and dual infimum, attained by a primal cross block. -/
theorem fidelity_source_strong_duality {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ∃ α : ℝ, IsLUB (fidelityPrimalValues P Q) α ∧ IsGLB (fidelityDualValues P Q) α ∧
      ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
        (Matrix.trace X).re = α := by
  obtain ⟨α, hp, hd, M, hM, hscore⟩ := fidelityProgram_strong_duality hP hQ
  obtain ⟨X, rfl⟩ := fidelityProgram_primal_shape hM
  rw [fidelityProgram_primalValues] at hp
  rw [fidelityProgram_dualValues] at hd
  rw [fidelityProgram_primalScore] at hscore
  exact ⟨α, hp, hd, X, (fidelityProgram_primal_block_iff P Q X).mp hM, hscore⟩

/-- Sandwiching a positive semidefinite matrix by its inverse square root on its support yields
its support projection. -/
theorem inverseSqrtOnSupport_sandwich {I : Type*} [Fintype I] [DecidableEq I]
    {P : HermitianMat I ℂ} (hP : 0 ≤ P) :
    (inverseSqrtOnSupport P).mat * P.mat * (inverseSqrtOnSupport P).mat = P.supportProj.mat := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  calc
    _ = (P.cfc f).mat * (P.cfc id).mat * (P.cfc f).mat := by rw [P.cfc_id]; rfl
    _ = (P.cfc (fun x => (f x * x) * f x)).mat := by
      rw [HermitianMat.mat_cfc_mul_apply, HermitianMat.mat_cfc_mul_apply]
      rfl
    _ = P.supportProj.mat := by
      rw [HermitianMat.supportProj_eq_cfc]
      apply congrArg HermitianMat.mat
      apply HermitianMat.cfc_congr_of_nonneg hP
      intro x hx
      by_cases hz : x = 0
      · simp [f, hz]
      · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm hz))
        simp only [f, if_neg hz]
        have hsq := Real.mul_self_sqrt hx
        field_simp
        nlinarith

/-- The square root times the inverse square root on the support of a positive semidefinite
matrix equals its support projection. -/
theorem sqrt_mul_inverseSqrtOnSupport {I : Type*} [Fintype I] [DecidableEq I]
    {P : HermitianMat I ℂ} (hP : 0 ≤ P) :
    P.sqrt.mat * (inverseSqrtOnSupport P).mat = P.supportProj.mat := by
  change (P.cfc Real.sqrt).mat * (P.cfc (fun x => (Real.sqrt x)⁻¹)).mat = _
  rw [← HermitianMat.mat_cfc_mul_apply, HermitianMat.supportProj_eq_cfc]
  apply congrArg HermitianMat.mat
  apply HermitianMat.cfc_congr_of_nonneg hP
  intro x hx
  by_cases hz : x = 0
  · simp [hz]
  · simp [hz, Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm hz))]

/-- The inverse square root on the support times the square root of a positive semidefinite
matrix equals its support projection. -/
theorem inverseSqrtOnSupport_mul_sqrt {I : Type*} [Fintype I] [DecidableEq I]
    {P : HermitianMat I ℂ} (hP : 0 ≤ P) :
    (inverseSqrtOnSupport P).mat * P.sqrt.mat = P.supportProj.mat := by
  have h := congrArg Matrix.conjTranspose (sqrt_mul_inverseSqrtOnSupport hP)
  simpa only [Matrix.conjTranspose_mul, (inverseSqrtOnSupport P).H.eq,
    P.sqrt.H.eq, P.supportProj.H.eq] using! h

/-- Positive semidefinite matrices with zero real inner product have product `B.mat * A.mat`
equal to zero. -/
theorem psd_inner_zero_product {I : Type*} [Fintype I] [DecidableEq I]
    {A B : HermitianMat I ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hz : ⟪A,B⟫_ℝ = 0) :
    B.mat * A.mat = 0 := by
  have hrange := (HermitianMat.inner_zero_iff hA hB).mp hz
  have hc := LinearMap.range_le_ker_iff.mp hrange
  ext i j
  have hh := LinearMap.congr_fun hc (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have hi := congrArg (fun v : EuclideanSpace ℂ I => v i) hh
  simpa [HermitianMat.lin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply, Matrix.mul_apply] using! hi

/-- Multiplying a Hermitian matrix on the right by its support projection leaves it unchanged. -/
theorem mat_mul_supportProj {I : Type*} [Fintype I] [DecidableEq I]
    (P : HermitianMat I ℂ) : P.mat * P.supportProj.mat = P.mat := by
  calc
    _ = (P.cfc id).mat * (P.cfc (fun x => if x = 0 then 0 else 1)).mat := by
      rw [P.cfc_id, ← P.supportProj_eq_cfc]
    _ = (P.cfc (fun x => x * (if x = 0 then 0 else 1))).mat := by
      rw [HermitianMat.mat_cfc_mul_apply]
      rfl
    _ = P.mat := by
      have hf : (fun x : ℝ => x * (if x = 0 then 0 else 1)) = _root_.id := by
        funext x
        by_cases hx : x = 0 <;> simp [hx]
      rw [hf, P.cfc_id]

/-- Multiplying a Hermitian matrix on the right by its kernel projection gives zero. -/
theorem mat_mul_kerProj {I : Type*} [Fintype I] [DecidableEq I]
    (P : HermitianMat I ℂ) : P.mat * P.kerProj.mat = 0 := by
  have heq : P.kerProj = 1 - P.supportProj :=
    eq_sub_iff_add_eq.mpr P.kerProj_add_supportProj
  rw [heq, HermitianMat.mat_sub, HermitianMat.mat_one, Matrix.mul_sub,
    Matrix.mul_one, mat_mul_supportProj, sub_self]

/-- Positivity of a fidelity block matrix forces its cross block to lie in the left support of
`P`. -/
theorem fidelity_cross_left_support {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} {X : Matrix I I ℂ}
    (hM : (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef) :
    P.supportProj.mat * X = X := by
  let M := fidelityPrimalBlock P Q X
  let B :=
      Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P.kerProj (0 : HermitianMat I ℂ)
  have hB : 0 ≤ B := blockDiagonal_nonneg (HermitianMat.projector_nonneg _) le_rfl
  have hz : ⟪M,B⟫_ℝ = 0 := by
    calc
      _ = ⟪blockPinch M,B⟫_ℝ := by
        simpa only [B, blockPinch_blockDiagonal] using! (blockPinch_inner M B).symm
      _ = ⟪P,P.kerProj⟫_ℝ + ⟪Q,(0 : HermitianMat I ℂ)⟫_ℝ := by
        rw [show blockPinch M = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q from blockPinch_fidelityPrimalBlock P Q X]
        exact blockDiagonal_inner _ _ _ _
      _ = 0 := by rw [inner_zero_right, inner_eq_real_trace, mat_mul_kerProj]; simp
  have hMpos : 0 ≤ M := HermitianMat.zero_le_iff.mpr hM
  have hprod := psd_inner_zero_product hMpos hB hz
  have hk : P.kerProj.mat * X = 0 := by
    change Matrix.fromBlocks P.kerProj.mat 0 0 (0 : Matrix I I ℂ) *
      Matrix.fromBlocks P.mat X Xᴴ Q.mat = 0 at hprod
    rw [Matrix.fromBlocks_multiply] at hprod
    have h := congrArg (fun R : Matrix (I ⊕ I) (I ⊕ I) ℂ => R.submatrix Sum.inl Sum.inr) hprod
    simpa using! h
  have heq : P.supportProj = 1 - P.kerProj := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact P.kerProj_add_supportProj
  rw [heq, HermitianMat.mat_sub, HermitianMat.mat_one, Matrix.sub_mul, Matrix.one_mul, hk, sub_zero]

/-- Positivity of a fidelity block matrix forces its cross block to lie in the right support of
`Q`. -/
theorem fidelity_cross_right_support {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} {X : Matrix I I ℂ}
    (hM : (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef) :
    X * Q.supportProj.mat = X := by
  have hswap := hM.submatrix Sum.swap
  rw [Matrix.fromBlocks_submatrix_sum_swap_sum_swap] at hswap
  have hcross : Q.supportProj.mat * Xᴴ = Xᴴ :=
    fidelity_cross_left_support (by simpa only [Matrix.conjTranspose_conjTranspose] using! hswap)
  have h := congrArg Matrix.conjTranspose hcross
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Q.supportProj.H.eq] using! h

section Contraction
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable local instance sdpMatrixCStar {J : Type*} [Fintype J] [DecidableEq J] :
    CStarAlgebra (Matrix J J ℂ) where

/-- The block matrix with identity diagonal blocks and cross block `K` is positive semidefinite
exactly when `K` has norm at most one. -/
theorem unit_block_positive_iff {I : Type*} [Fintype I] [DecidableEq I]
    (K : Matrix I I ℂ) :
    (Matrix.fromBlocks (1 : Matrix I I ℂ) K Kᴴ 1).PosSemidef ↔ ‖K‖ ≤ 1 := by
  letI : Invertible (1 : Matrix I I ℂ) := invertibleOne
  rw [Matrix.PosDef.fromBlocks₁₁ K (1 : Matrix I I ℂ) Matrix.PosDef.one]
  simp only [inv_one, Matrix.mul_one]
  rw [← Matrix.nonneg_iff_posSemidef, sub_nonneg,
    ← CStarAlgebra.norm_le_one_iff_of_nonneg (Kᴴ * K)
      (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self K)),
    Matrix.l2_opNorm_conjTranspose_mul_self]
  constructor <;> intro h <;> nlinarith [norm_nonneg K]

/-- Normalizing the cross block of a positive semidefinite block matrix by the inverse square
roots on the two supports gives a contraction. -/
theorem inverseSqrt_cross_contraction {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} {X : Matrix I I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hM : (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef) :
    ‖(inverseSqrtOnSupport P).mat * X * (inverseSqrtOnSupport Q).mat‖ ≤ 1 := by
  let A := inverseSqrtOnSupport P
  let B := inverseSqrtOnSupport Q
  let K := A.mat * X * B.mat
  have hD :=
      hM.conjTranspose_mul_mul_same
      (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal A B).mat
  have hker : (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P.kerProj Q.kerProj).mat.PosSemidef :=
    HermitianMat.zero_le_iff.mp (blockDiagonal_nonneg
      (HermitianMat.projector_nonneg _) (HermitianMat.projector_nonneg _))
  have heq : (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal A B).matᴴ * Matrix.fromBlocks P.mat X Xᴴ Q.mat *
      (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal A B).mat + (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P.kerProj Q.kerProj).mat =
      Matrix.fromBlocks (1 : Matrix I I ℂ) K Kᴴ 1 := by
    simp only [Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal, HermitianMat.mat_mk, Matrix.fromBlocks_conjTranspose,
      A.H.eq, B.H.eq, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
      zero_mul, mul_zero, zero_add, add_zero]
    have hPsum : A.mat * P.mat * A.mat + P.kerProj.mat = 1 := by
      rw [show A.mat * P.mat * A.mat = P.supportProj.mat from inverseSqrtOnSupport_sandwich hP]
      have h := congrArg HermitianMat.mat P.kerProj_add_supportProj
      simpa only [HermitianMat.mat_add, HermitianMat.mat_one, add_comm] using! h
    have hQsum : B.mat * Q.mat * B.mat + Q.kerProj.mat = 1 := by
      rw [show B.mat * Q.mat * B.mat = Q.supportProj.mat from inverseSqrtOnSupport_sandwich hQ]
      have h := congrArg HermitianMat.mat Q.kerProj_add_supportProj
      simpa only [HermitianMat.mat_add, HermitianMat.mat_one, add_comm] using! h
    rw [Matrix.fromBlocks_add]
    simp only [add_zero]
    rw [hPsum, hQsum]
    congr 1
    dsimp [K]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, A.H.eq, B.H.eq]
    exact Matrix.mul_assoc _ _ _
  apply (unit_block_positive_iff K).mp
  rw [← heq]
  exact hD.add hker

/-- The cross block of a positive semidefinite block matrix factors through the two square roots
and a contraction. -/
theorem fidelity_block_contraction {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} {X : Matrix I I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hM : (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef) :
    ∃ K : Matrix I I ℂ, ‖K‖ ≤ 1 ∧ X = P.sqrt.mat * K * Q.sqrt.mat := by
  refine ⟨(inverseSqrtOnSupport P).mat * X * (inverseSqrtOnSupport Q).mat,
    inverseSqrt_cross_contraction hP hQ hM, ?_⟩
  calc
    X = P.supportProj.mat * X * Q.supportProj.mat := by
      rw [fidelity_cross_left_support hM, fidelity_cross_right_support hM]
    _ = P.sqrt.mat * ((inverseSqrtOnSupport P).mat * X *
        (inverseSqrtOnSupport Q).mat) * Q.sqrt.mat := by
      rw [← sqrt_mul_inverseSqrtOnSupport hP, ← inverseSqrtOnSupport_mul_sqrt hQ]
      simp only [Matrix.mul_assoc]

/-- A contraction placed between the square roots of positive semidefinite diagonal blocks
produces a positive semidefinite block matrix. -/
theorem fidelity_block_of_contraction {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {K : Matrix I I ℂ} (hK : ‖K‖ ≤ 1) :
    (Matrix.fromBlocks P.mat (P.sqrt.mat * K * Q.sqrt.mat)
      (P.sqrt.mat * K * Q.sqrt.mat)ᴴ Q.mat).PosSemidef := by
  have h := ((unit_block_positive_iff K).mpr hK).conjTranspose_mul_mul_same
    (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P.sqrt Q.sqrt).mat
  have heq : (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P.sqrt Q.sqrt).matᴴ *
      Matrix.fromBlocks (1 : Matrix I I ℂ) K Kᴴ 1 * (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P.sqrt Q.sqrt).mat =
      Matrix.fromBlocks P.mat (P.sqrt.mat * K * Q.sqrt.mat)
        (P.sqrt.mat * K * Q.sqrt.mat)ᴴ Q.mat := by
    simp only [Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal, HermitianMat.mat_mk, Matrix.fromBlocks_conjTranspose,
      P.sqrt.H.eq, Q.sqrt.H.eq, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
      zero_mul, mul_zero, zero_add, add_zero, Matrix.mul_one,
      HermitianMat.sqrt_sq hP, HermitianMat.sqrt_sq hQ]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, P.sqrt.H.eq, Q.sqrt.H.eq]
    exact Matrix.mul_assoc _ _ _
  rwa [heq] at h

/-- A block matrix with positive semidefinite diagonal blocks is positive semidefinite exactly
when its cross block factors through their square roots and a contraction. -/
theorem fidelity_block_iff_contraction {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (X : Matrix I I ℂ) :
    (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ↔
      ∃ K : Matrix I I ℂ, ‖K‖ ≤ 1 ∧ X = P.sqrt.mat * K * Q.sqrt.mat := by
  constructor
  · exact fidelity_block_contraction hP hQ
  · rintro ⟨K, hK, rfl⟩
    exact fidelity_block_of_contraction hP hQ hK

/-- Reversing the order of the two square roots in the trace norm gives `rootFidelity P Q`. -/
theorem rootFidelity_reverse {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : Matrix.traceNorm (Q.sqrt.mat * P.sqrt.mat) = rootFidelity P Q := by
  have h := Matrix.traceNorm_conjTranspose (P.sqrt.mat * Q.sqrt.mat)
  simpa only [Matrix.conjTranspose_mul, P.sqrt.H.eq, Q.sqrt.H.eq, rootFidelity] using! h

/-- The real trace of any feasible fidelity cross block is at most `rootFidelity P Q`. -/
theorem fidelity_block_score_le_rootFidelity {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) {X : Matrix I I ℂ}
    (hX : (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef) :
    (Matrix.trace X).re ≤ rootFidelity P Q := by
  obtain ⟨K, hK, rfl⟩ := fidelity_block_contraction hP hQ hX
  have hcycle : Matrix.trace (P.sqrt.mat * K * Q.sqrt.mat) =
      Matrix.trace (K * (Q.sqrt.mat * P.sqrt.mat)) := by
    calc
      _ = Matrix.trace (Q.sqrt.mat * (P.sqrt.mat * K)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Q.sqrt.mat * P.sqrt.mat) * K) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (K * (Q.sqrt.mat * P.sqrt.mat)) := Matrix.trace_mul_comm _ _
  rw [hcycle]
  calc
    _ ≤ ‖Matrix.trace (K * (Q.sqrt.mat * P.sqrt.mat))‖ := Complex.re_le_norm _
    _ ≤ Matrix.traceNorm (K * (Q.sqrt.mat * P.sqrt.mat)) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖K‖ * Matrix.traceNorm (Q.sqrt.mat * P.sqrt.mat) := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 * Matrix.traceNorm (Q.sqrt.mat * P.sqrt.mat) :=
      mul_le_mul_of_nonneg_right hK (Matrix.traceNorm_nonneg _)
    _ = rootFidelity P Q := by rw [one_mul, rootFidelity_reverse]

/-- For positive semidefinite inputs, some feasible fidelity cross block has real trace equal to
`rootFidelity P Q`. -/
theorem rootFidelity_block_attained {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
      (Matrix.trace X).re = rootFidelity P Q := by
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (Q.sqrt.mat * P.sqrt.mat)).1
  have hGram := Matrix.fromBlocks_gram_posSemidef U.val (1 : Matrix I I ℂ)
  have hunit : U.valᴴ * U.val = 1 := by
    ext i j
    have h := congrArg (fun A : Matrix I I ℂ => A i j) U.prop.1
    by_cases hij : i = j
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply, if_pos hij] using! h
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply, if_neg hij] using! h
  have hK : ‖U.val‖ ≤ 1 := (unit_block_positive_iff U.val).mp (by simpa [hunit] using! hGram)
  refine ⟨P.sqrt.mat * U.val * Q.sqrt.mat, fidelity_block_of_contraction hP hQ hK, ?_⟩
  have hcycle : Matrix.trace (P.sqrt.mat * U.val * Q.sqrt.mat) =
      Matrix.trace (U.val * (Q.sqrt.mat * P.sqrt.mat)) := by
    calc
      _ = Matrix.trace (Q.sqrt.mat * (P.sqrt.mat * U.val)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Q.sqrt.mat * P.sqrt.mat) * U.val) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (U.val * (Q.sqrt.mat * P.sqrt.mat)) := Matrix.trace_mul_comm _ _
  rw [hcycle, hU, rootFidelity_reverse]

/-- Root fidelity is both the primal supremum and dual infimum of the block formulation, and the
primal supremum is attained; see [Watrous2018]. -/
theorem fidelity_source_rootFidelity {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    IsLUB (fidelityPrimalValues P Q) (rootFidelity P Q) ∧
      IsGLB (fidelityDualValues P Q) (rootFidelity P Q) ∧
      ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
        (Matrix.trace X).re = rootFidelity P Q := by
  obtain ⟨X, hX, hscore⟩ := rootFidelity_block_attained hP hQ
  have hlub : IsLUB (fidelityPrimalValues P Q) (rootFidelity P Q) := by
    constructor
    · rintro _ ⟨Y, hY, rfl⟩
      exact fidelity_block_score_le_rootFidelity hP hQ hY
    · intro b hb
      rw [← hscore]
      exact hb ⟨X, hX, rfl⟩
  obtain ⟨α, hα, hdual, -⟩ := fidelity_source_strong_duality hP hQ
  have heq : α = rootFidelity P Q := hα.unique hlub
  exact ⟨hlub, heq ▸ hdual, X, hX, hscore⟩

end Contraction

/-- The weighted block primal score is the real trace pairing of `C` with the cross block. -/
theorem weightedBlockProgram_primalScore {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C X : Matrix I I ℂ) :
    (weightedBlockProgram P Q C).primalScore (fidelityPrimalBlock P Q X) =
      (Matrix.trace (Cᴴ * X)).re := by
  have hc : (Matrix.trace (C * Xᴴ)).re = (Matrix.trace (Cᴴ * X)).re := by
    calc
      _ = (Matrix.trace (Xᴴ * C)).re := congrArg Complex.re (Matrix.trace_mul_comm _ _)
      _ = (star (Matrix.trace (Cᴴ * X))).re := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
      _ = _ := Complex.conj_re _
  change ⟪(1/2 : ℝ) • offDiagonal C, fidelityPrimalBlock P Q X⟫_ℝ = _
  rw [real_inner_smul_left, inner_eq_real_trace]
  change (1/2 : ℝ) * (Matrix.trace (Matrix.fromBlocks 0 C Cᴴ 0 *
    Matrix.fromBlocks P.mat X Xᴴ Q.mat)).re = _
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, zero_add, add_zero, block_trace, Complex.add_re, hc]
  ring

/-- Every weighted block primal feasible matrix has the prescribed fidelity block form. -/
theorem weightedBlockProgram_primal_shape {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} {C : Matrix I I ℂ} {M : HermitianMat (I ⊕ I) ℂ}
    (hM : (weightedBlockProgram P Q C).PrimalFeasible M) :
    ∃ X : Matrix I I ℂ, M = fidelityPrimalBlock P Q X :=
  fidelityProgram_primal_shape hM

/-- A weighted block primal matrix is feasible exactly when its underlying block matrix is
positive semidefinite. -/
theorem weightedBlockProgram_primal_block_iff {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C X : Matrix I I ℂ) :
    (weightedBlockProgram P Q C).PrimalFeasible (fidelityPrimalBlock P Q X) ↔
      (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef :=
  fidelityProgram_primal_block_iff P Q X

/-- The weighted block dual score at half a block diagonal matrix is half the sum of the two
input pairings. -/
theorem weightedBlockProgram_dualScore {I : Type*} [Fintype I] [DecidableEq I]
    (P Q Y Z : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    (weightedBlockProgram P Q C).dualScore ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) =
      (1/2 : ℝ) * ⟪P,Y⟫_ℝ + (1/2 : ℝ) * ⟪Q,Z⟫_ℝ :=
  fidelityProgram_dualScore P Q Y Z

/-- The weighted block dual slack at half a block diagonal matrix is half the corresponding
`weightedDualBlock`. -/
theorem weightedBlockProgram_dual_slack {I : Type*} [Fintype I] [DecidableEq I]
    (P Q Y Z : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    (weightedBlockProgram P Q C).constraint.adjoint ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) -
      (weightedBlockProgram P Q C).objective = (1/2 : ℝ) • weightedDualBlock C Y Z := by
  change (blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint
    ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) - _ = _
  rw [blockPinch_adjoint]
  change blockPinch ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) -
      (1/2 : ℝ) • offDiagonal C = _
  rw [map_smul]
  change (1/2 : ℝ) • blockPinch
      (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) - _ = _
  rw [blockPinch_blockDiagonal]
  exact (smul_sub (1/2 : ℝ) (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) (offDiagonal C)).symm

/-- A half-scaled block diagonal point is weighted block dual feasible exactly when its
`weightedDualBlock` is positive semidefinite. -/
theorem weightedBlockProgram_dual_block_iff {I : Type*} [Fintype I] [DecidableEq I]
    (P Q Y Z : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    (weightedBlockProgram P Q C).DualFeasible ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) ↔
      0 ≤ weightedDualBlock C Y Z := by
  change (0 ≤ (weightedBlockProgram P Q C).constraint.adjoint ((1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z) - _) ↔ _
  rw [weightedBlockProgram_dual_slack]
  constructor
  · intro h
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h
    simpa only [smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul] using! hh
  · exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)

/-- Pinching preserves both dual feasibility and the dual score of the weighted block program. -/
theorem weightedBlockProgram_pinched_dual {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) (Y : HermitianMat (I ⊕ I) ℂ) :
    ((weightedBlockProgram P Q C).DualFeasible (blockPinch Y) ↔
      (weightedBlockProgram P Q C).DualFeasible Y) ∧
      (weightedBlockProgram P Q C).dualScore (blockPinch Y) =
        (weightedBlockProgram P Q C).dualScore Y := by
  constructor
  · change (0 ≤ (blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint (blockPinch Y) - _) ↔
      (0 ≤ (blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint Y - _)
    rw [blockPinch_adjoint]
    change (0 ≤ blockPinch (blockPinch Y) - _) ↔ (0 ≤ blockPinch Y - _)
    rw [blockPinch_idempotent]
  · exact (fidelityProgram_pinched_dual P Q Y).2

/-- The weighted block program's primal value set equals `weightedBlockPrimalValues`. -/
theorem weightedBlockProgram_primalValues {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    (weightedBlockProgram P Q C).primalValues = weightedBlockPrimalValues P Q C := by
  ext a
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨X, rfl⟩ := weightedBlockProgram_primal_shape hM
    exact ⟨X, (weightedBlockProgram_primal_block_iff P Q C X).mp hM,
      (weightedBlockProgram_primalScore P Q C X).symm⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨fidelityPrimalBlock P Q X, (weightedBlockProgram_primal_block_iff P Q C X).mpr hX,
      weightedBlockProgram_primalScore P Q C X⟩

/-- The weighted block program's dual value set equals `weightedBlockDualValues`. -/
theorem weightedBlockProgram_dualValues {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    (weightedBlockProgram P Q C).dualValues = weightedBlockDualValues P Q C := by
  ext a
  constructor
  · rintro ⟨M, hM, rfl⟩
    refine ⟨(2 : ℝ) • principalBlock M Sum.inl, (2 : ℝ) • principalBlock M Sum.inr, ?_, ?_⟩
    · apply (weightedBlockProgram_dual_block_iff P Q _ _ C).mp
      rw [fidelity_dual_coordinates]
      exact (weightedBlockProgram_pinched_dual P Q C M).1.mpr hM
    · rw [← weightedBlockProgram_dualScore P Q _ _ C, fidelity_dual_coordinates]
      exact (weightedBlockProgram_pinched_dual P Q C M).2
  · rintro ⟨Y, Z, hYZ, rfl⟩
    exact ⟨(1/2 : ℝ) • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z,
      (weightedBlockProgram_dual_block_iff P Q Y Z C).mpr hYZ,
      weightedBlockProgram_dualScore P Q Y Z C⟩

section WeightedContraction
open scoped Matrix.Norms.L2Operator

/-- The weighted block program satisfies dual Slater feasibility for every choice of Hermitian
inputs and weight matrix. -/
theorem weightedBlockProgram_dual_strict {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) : (weightedBlockProgram P Q C).DualSlater := by
  let n : ℝ := ‖C‖ + 1
  have hn : 0 < n := by dsimp [n]; positivity
  let T : Matrix I I ℂ := -n⁻¹ • C
  have hT : ‖T‖ ≤ 1 := by
    rw [show T = -n⁻¹ • C from rfl, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (inv_pos.mpr hn)]
    have h := (div_le_one hn).mpr (show ‖C‖ ≤ n by dsimp [n]; linarith)
    simpa only [div_eq_mul_inv, mul_comm] using! h
  have hscale : n • T = -C := by
    dsimp [T]
    rw [smul_smul, mul_neg, mul_inv_cancel₀ hn.ne', neg_one_smul]
  have hstar : n • Tᴴ = -Cᴴ := by
    have h := congrArg Matrix.conjTranspose hscale
    simpa using! h
  let H : HermitianMat (I ⊕ I) ℂ := n • 1 - offDiagonal C
  have hH : 0 ≤ H := by
    apply HermitianMat.zero_le_iff.mpr
    have h := ((unit_block_positive_iff T).mpr hT).smul hn.le
    have heq : H.mat = n • Matrix.fromBlocks (1 : Matrix I I ℂ) T Tᴴ 1 := by
      simp only [H, HermitianMat.mat_sub, HermitianMat.mat_smul, HermitianMat.mat_one,
        offDiagonal, HermitianMat.mat_mk, Matrix.fromBlocks_smul, hscale, hstar]
      conv_lhs => rw [← Matrix.fromBlocks_one (l := I) (m := I)]
      rw [Matrix.fromBlocks_smul, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
      simp only [smul_zero, add_zero, zero_add, neg_zero]
    rwa [heq]
  refine ⟨(‖C‖/2 + 1) • (1 : HermitianMat (I ⊕ I) ℂ), ?_⟩
  change ((blockPinch : HermitianMat (I ⊕ I) ℂ →L[ℝ] _).adjoint
    ((‖C‖/2 + 1) • 1) - (1/2 : ℝ) • offDiagonal C).mat.PosDef
  rw [blockPinch_adjoint]
  change (blockPinch ((‖C‖/2 + 1) • (1 : HermitianMat (I ⊕ I) ℂ)) -
    (1/2 : ℝ) • offDiagonal C).mat.PosDef
  rw [map_smul]
  change ((‖C‖/2 + 1) • blockPinch (1 : HermitianMat (I ⊕ I) ℂ) -
    (1/2 : ℝ) • offDiagonal C).mat.PosDef
  rw [blockPinch_one]
  have heq : (‖C‖/2 + 1) • (1 : HermitianMat (I ⊕ I) ℂ) -
      (1/2 : ℝ) • offDiagonal C = (1/2 : ℝ) • 1 + (1/2 : ℝ) • H := by
    dsimp [H,n]
    module
  rw [heq, HermitianMat.mat_add, HermitianMat.mat_smul]
  exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1/2)).add_posSemidef
    ((HermitianMat.zero_le_iff.mp hH).smul (by norm_num : (0 : ℝ) ≤ 1/2))

/-- For positive semidefinite inputs, the weighted block formulation has a common primal
supremum and dual infimum, attained by a primal cross block. -/
theorem weightedBlock_source_strong_duality {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (C : Matrix I I ℂ) :
    ∃ α : ℝ, IsLUB (weightedBlockPrimalValues P Q C) α ∧
      IsGLB (weightedBlockDualValues P Q C) α ∧
      ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
        (Matrix.trace (Cᴴ * X)).re = α := by
  have hfeas : (weightedBlockProgram P Q C).PrimalFeasible (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q) :=
    ⟨blockDiagonal_nonneg hP hQ, blockPinch_blockDiagonal P Q⟩
  obtain ⟨α, hp, hd, M, hM, hscore⟩ := (Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlater_strong_duality (P := (weightedBlockProgram P Q C)))
    (weightedBlockProgram_dual_strict P Q C) hfeas
  obtain ⟨X, rfl⟩ := weightedBlockProgram_primal_shape hM
  rw [weightedBlockProgram_primalValues] at hp
  rw [weightedBlockProgram_dualValues] at hd
  rw [weightedBlockProgram_primalScore] at hscore
  exact ⟨α, hp, hd, X, (weightedBlockProgram_primal_block_iff P Q C X).mp hM, hscore⟩

/-- The trace of a product of four square matrices is unchanged by cyclically moving the first
two factors to the end. -/
private theorem cross_trace_cycle {I : Type*} [Fintype I] (A B C D : Matrix I I ℂ) :
    Matrix.trace (A * (B * C * D)) = Matrix.trace (C * (D * A * B)) := by
  calc
    _ = Matrix.trace (((A * B) * C) * D) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (D * ((A * B) * C)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((D * A) * B) * C) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (C * (D * A * B)) := Matrix.trace_mul_comm _ _

/-- Taking the conjugate transpose and reversing the square root factors preserves the
sandwiched trace norm. -/
theorem sandwichedTraceNorm_adjoint {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    Matrix.traceNorm (Q.sqrt.mat * Cᴴ * P.sqrt.mat) = sandwichedTraceNorm P Q C := by
  have h := Matrix.traceNorm_conjTranspose (P.sqrt.mat * C * Q.sqrt.mat)
  simpa only [Matrix.conjTranspose_mul, P.sqrt.H.eq, Q.sqrt.H.eq,
    Matrix.mul_assoc, sandwichedTraceNorm] using! h

/-- Every feasible weighted cross block has score at most `sandwichedTraceNorm P Q C`. -/
theorem weightedBlock_score_le_norm {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (C : Matrix I I ℂ)
    {X : Matrix I I ℂ} (hX : (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef) :
    (Matrix.trace (Cᴴ * X)).re ≤ sandwichedTraceNorm P Q C := by
  obtain ⟨K, hK, rfl⟩ := fidelity_block_contraction hP hQ hX
  rw [cross_trace_cycle]
  calc
    _ ≤ ‖Matrix.trace (K * (Q.sqrt.mat * Cᴴ * P.sqrt.mat))‖ := Complex.re_le_norm _
    _ ≤ Matrix.traceNorm (K * (Q.sqrt.mat * Cᴴ * P.sqrt.mat)) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖K‖ * Matrix.traceNorm (Q.sqrt.mat * Cᴴ * P.sqrt.mat) := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 * Matrix.traceNorm (Q.sqrt.mat * Cᴴ * P.sqrt.mat) :=
      mul_le_mul_of_nonneg_right hK (Matrix.traceNorm_nonneg _)
    _ = sandwichedTraceNorm P Q C := by rw [one_mul, sandwichedTraceNorm_adjoint]

/-- A feasible weighted cross block attains `sandwichedTraceNorm P Q C` for positive
semidefinite inputs. -/
theorem weightedBlock_norm_attained {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (C : Matrix I I ℂ) :
    ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
      (Matrix.trace (Cᴴ * X)).re = sandwichedTraceNorm P Q C := by
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (Q.sqrt.mat * Cᴴ * P.sqrt.mat)).1
  have hunit : U.valᴴ * U.val = 1 := by
    ext i j
    have h := congrArg (fun A : Matrix I I ℂ => A i j) U.prop.1
    by_cases hij : i = j
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply, if_pos hij] using! h
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply, if_neg hij] using! h
  have hGram := Matrix.fromBlocks_gram_posSemidef U.val (1 : Matrix I I ℂ)
  have hK : ‖U.val‖ ≤ 1 := (unit_block_positive_iff U.val).mp (by simpa [hunit] using! hGram)
  refine ⟨P.sqrt.mat * U.val * Q.sqrt.mat, fidelity_block_of_contraction hP hQ hK, ?_⟩
  rw [cross_trace_cycle, hU, sandwichedTraceNorm_adjoint]

/-- The sandwiched trace norm is the common primal supremum and dual infimum of the weighted
block formulation, with primal attainment. -/
theorem weightedBlock_source_norm {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (C : Matrix I I ℂ) :
    IsLUB (weightedBlockPrimalValues P Q C) (sandwichedTraceNorm P Q C) ∧
      IsGLB (weightedBlockDualValues P Q C) (sandwichedTraceNorm P Q C) ∧
      ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
        (Matrix.trace (Cᴴ * X)).re = sandwichedTraceNorm P Q C := by
  obtain ⟨X, hX, hscore⟩ := weightedBlock_norm_attained hP hQ C
  have hlub : IsLUB (weightedBlockPrimalValues P Q C) (sandwichedTraceNorm P Q C) := by
    constructor
    · rintro _ ⟨Y, hY, rfl⟩
      exact weightedBlock_score_le_norm hP hQ C hY
    · intro b hb
      rw [← hscore]
      exact hb ⟨X, hX, rfl⟩
  obtain ⟨α, hα, hdual, -⟩ := weightedBlock_source_strong_duality hP hQ C
  have heq : α = sandwichedTraceNorm P Q C := hα.unique hlub
  exact ⟨hlub, heq ▸ hdual, X, hX, hscore⟩

end WeightedContraction

/-- The positive square root of the square of a positive semidefinite Hermitian matrix is the
original matrix. -/
theorem sqrt_square_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {P : HermitianMat I ℂ} (hP : 0 ≤ P) : (P ^ 2).sqrt = P := by
  rw [HermitianMat.sqrt, ← P.cfc_pow, ← P.cfc_comp]
  calc
    P.cfc (Real.sqrt ∘ (· ^ 2)) = P.cfc id := by
      apply HermitianMat.cfc_congr_of_nonneg hP
      intro x hx
      exact Real.sqrt_sq hx
    _ = P := P.cfc_id

/-- Every square complex matrix factors as a unitary matrix times the positive square root of
its input Gram matrix. -/
theorem inputGram_polar {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ A = U * (inputGram A).sqrt.mat := by
  let hH : (Aᴴ * A).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self A).1
  obtain ⟨V, W, hA⟩ := Matrix.exists_svd_sqrt_eigenvalues A
  let D : HermitianMat I ℂ := HermitianMat.diagonal ℂ (fun i => Real.sqrt (hH.eigenvalues i))
  have hA' : A = V.val * D.mat * W.valᴴ := hA
  have hV : V.valᴴ * V.val = 1 := V.prop.1
  have hV' : V.val * V.valᴴ = 1 := V.prop.2
  have hW : W.valᴴ * W.val = 1 := W.prop.1
  have hW' : W.val * W.valᴴ = 1 := W.prop.2
  let B := D.conj W.val
  have hD : 0 ≤ D := by
    apply HermitianMat.zero_le_iff.mpr
    exact Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))
  have hB : 0 ≤ B := HermitianMat.zero_le_iff.mpr
    ((HermitianMat.zero_le_iff.mp hD).mul_mul_conjTranspose_same W.val)
  have hBsquare : B ^ 2 = inputGram A := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_pow, pow_two]
    change (W.val * D.mat * W.valᴴ) * (W.val * D.mat * W.valᴴ) = Aᴴ * A
    calc
      _ = W.val * D.mat * (W.valᴴ * W.val) * D.mat * W.valᴴ := by simp only [Matrix.mul_assoc]
      _ = W.val * D.mat * D.mat * W.valᴴ := by rw [hW, Matrix.mul_one]
      _ = W.val * D.mat * (V.valᴴ * V.val) * D.mat * W.valᴴ := by rw [hV, Matrix.mul_one]
      _ = Aᴴ * A := by
        rw [hA']
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, D.H.eq,
            Matrix.mul_assoc]
  have hsqrt : (inputGram A).sqrt = B := by
    rw [← hBsquare, sqrt_square_nonneg hB]
  refine ⟨V.val * W.valᴴ, ?_, ?_, ?_⟩
  · calc
      _ = W.val * (V.valᴴ * V.val) * W.valᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [hV, Matrix.mul_one, hW']
  · calc
      _ = V.val * (W.valᴴ * W.val) * V.valᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [hW, Matrix.mul_one, hV']
  · rw [hsqrt]
    change A = V.val * W.valᴴ * (W.val * D.mat * W.valᴴ)
    calc
      A = V.val * D.mat * W.valᴴ := hA'
      _ = V.val * W.valᴴ * (W.val * D.mat * W.valᴴ) := by
        have heq : V.val * W.valᴴ * (W.val * D.mat * W.valᴴ) =
            V.val * (W.valᴴ * W.val) * D.mat * W.valᴴ := by simp only [Matrix.mul_assoc]
        rw [heq, hW, Matrix.mul_one]

/-- Applying `tensorLeft T` to a rank-one matrix gives the Choi matrix sandwiched by the
corresponding input frames. -/
theorem tensorLeft_rankOne_choi {D E R : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (u v : Fin D × Fin R → ℂ) :
    tensorLeft T (fun a b => u a * star (v b)) =
      Matrix.kronecker (1 : Operator E) (inputFrame u) * MatrixMap.choi_matrix T *
        (Matrix.kronecker (1 : Operator E) (inputFrame v))ᴴ := by
  ext a b
  have hexpand : T (fun i j => u (i,a.2) * star (v (j,b.2))) a.1 b.1 =
      ∑ i, ∑ j, (u (i,a.2) * star (v (j,b.2))) *
        MatrixMap.choi_matrix T (a.1,i) (b.1,j) := by
    have h := congrArg (fun S : MatrixMap (Fin D) (Fin E) ℂ =>
      S (fun i j => u (i,a.2) * star (v (j,b.2))) a.1 b.1) (MatrixMap.choi_map_inv T).symm
    exact h
  change T (fun i j => u (i,a.2) * star (v (j,b.2))) a.1 b.1 = _
  rw [hexpand]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, inputFrame,
    apply_ite, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The trace of the Gram matrix of an input frame is the squared norm sum of the original
vector. -/
theorem inputFrame_gram_trace {D : ℕ} (u : Fin D × Fin D → ℂ) :
    Matrix.trace (inputGram (inputFrame u)).mat = ∑ a, star (u a) * u a := by
  change (∑ i, ∑ j, star (u (i,j)) * u (i,j)) = _
  rw [Fintype.sum_prod_type]

/-- The Gram matrix of a normalized input frame is positive semidefinite with trace one. -/
theorem inputFrame_density {D : ℕ} {u : Fin D × Fin D → ℂ}
    (hu : ∑ a, star (u a) * u a = 1) :
    0 ≤ inputGram (inputFrame u) ∧ (inputGram (inputFrame u)).trace = (1 : ℝ) := by
  constructor
  · exact HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_conjTranspose_mul_self _)
  · rw [HermitianMat.trace_eq_re_trace, inputFrame_gram_trace, hu]
    rfl

/-- The input frame of a density vector equals the square root of its density matrix. -/
@[simp] theorem inputFrame_densityVector {D : ℕ} (ρ : DensityInput D) :
    inputFrame (densityVector ρ) = ρ.val.sqrt.mat := rfl

/-- The density vector associated to a density input has squared norm sum one. -/
theorem densityVector_normalized {D : ℕ} (ρ : DensityInput D) :
    ∑ a, star (densityVector ρ a) * densityVector ρ a = 1 := by
  rw [← inputFrame_gram_trace, inputFrame_densityVector]
  change Matrix.trace (ρ.val.sqrt.matᴴ * ρ.val.sqrt.mat) = 1
  rw [ρ.val.sqrt.H.eq, HermitianMat.sqrt_sq ρ.property.1,
    ← HermitianMat.trace_eq_trace (R := ℝ) ρ.val, ρ.property.2]
  rfl

/-- The Choi score equals the trace norm of the amplified map on the rank-one matrix formed from
the two density vectors. -/
theorem diamondChoiScore_as_raw {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ σ : DensityInput D) :
    diamondChoiScore T ρ σ = Matrix.traceNorm
      (tensorLeft T (fun a b => densityVector ρ a * star (densityVector σ b))) := by
  rw [tensorLeft_rankOne_choi, inputFrame_densityVector, inputFrame_densityVector]
  simp only [diamondChoiScore, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, σ.val.sqrt.H.eq]

/-- Multiplication on the left and right by isometries preserves the trace norm. -/
private theorem traceNorm_two_isometries {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
    (U : Matrix J I ℂ) (V : Matrix K I ℂ) (M : Matrix I I ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    Matrix.traceNorm (U * M * Vᴴ) = Matrix.traceNorm M := by
  rw [Matrix.traceNorm_isometry_right (u := V) (by
    ext i j
    have h := congrArg (fun A : Matrix I I ℂ => A i j) hV
    by_cases hij : i = j
    · simpa only [Matrix.one_apply, if_pos hij] using! h
    · simpa only [Matrix.one_apply, if_neg hij] using! h)]
  apply Matrix.traceNorm_isometry_left
  ext i j
  have h := congrArg (fun A : Matrix I I ℂ => A i j) hU
  by_cases hij : i = j
  · simpa only [Matrix.one_apply, if_pos hij] using! h
  · simpa only [Matrix.one_apply, if_neg hij] using! h

/-- The amplified trace norm of normalized rank-one input data is realized as a Choi score for
two density inputs. -/
theorem raw_rankOne_as_diamondChoiScore {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (u v : Fin D × Fin D → ℂ)
    (hu : ∑ a, star (u a) * u a = 1) (hv : ∑ a, star (v a) * v a = 1) :
    ∃ ρ σ : DensityInput D,
      Matrix.traceNorm (tensorLeft T (fun a b => u a * star (v b))) = diamondChoiScore T ρ σ := by
  let ρ : DensityInput D := ⟨inputGram (inputFrame u), inputFrame_density hu⟩
  let σ : DensityInput D := ⟨inputGram (inputFrame v), inputFrame_density hv⟩
  obtain ⟨U, hU, -, huf⟩ := inputGram_polar (inputFrame u)
  obtain ⟨V, hV, -, hvf⟩ := inputGram_polar (inputFrame v)
  let L := Matrix.kronecker (1 : Operator E) U
  let R := Matrix.kronecker (1 : Operator E) V
  let A := Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat
  let B := Matrix.kronecker (1 : Operator E) σ.val.sqrt.mat
  have hL : L.Isometry := diamond_kronecker_frame_isometry hU
  have hR : R.Isometry := diamond_kronecker_frame_isometry hV
  have huf' : Matrix.kronecker (1 : Operator E) (inputFrame u) = L * A := by
    dsimp [L,A,ρ]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    exact congrArg (fun M : Operator D => Matrix.kronecker (1 : Operator E) M) huf
  have hvf' : Matrix.kronecker (1 : Operator E) (inputFrame v) = R * B := by
    dsimp [R,B,σ]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    exact congrArg (fun M : Operator D => Matrix.kronecker (1 : Operator E) M) hvf
  have hB : Bᴴ = B := by
    dsimp [B]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, σ.val.sqrt.H.eq]
  refine ⟨ρ,σ,?_⟩
  rw [tensorLeft_rankOne_choi, huf', hvf', Matrix.conjTranspose_mul, hB]
  have heq : L * A * MatrixMap.choi_matrix T * (B * Rᴴ) =
      L * (A * MatrixMap.choi_matrix T * B) * Rᴴ := by simp only [Matrix.mul_assoc]
  rw [heq]
  exact traceNorm_two_isometries L R (A * MatrixMap.choi_matrix T * B) hL hR

/-- The Choi variational value is bounded above by the finite diamond norm. -/
theorem diamondChoiValue_le_finiteDiamond {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    diamondChoiValue T ≤ finiteDiamondNorm T := by
  unfold diamondChoiValue
  apply iSup_le
  intro ρ
  apply iSup_le
  intro σ
  rw [diamondChoiScore_as_raw]
  have hnorm := diamond_unit_rank_one_traceNorm (densityVector ρ) (densityVector σ)
    (densityVector_normalized ρ) (densityVector_normalized σ)
  have h := finiteDiamondNorm_apply T D
    (fun a b => densityVector ρ a * star (densityVector σ b))
  rw [hnorm, ENNReal.ofReal_one, mul_one] at h
  exact h

/-- The finite diamond norm equals its Choi variational value; see [Watrous2018]. -/
theorem finiteDiamondNorm_eq_choi {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondNorm T = diamondChoiValue T := by
  apply le_antisymm ?_ (diamondChoiValue_le_finiteDiamond T)
  have hfinite : diamondChoiValue T ≠ ⊤ := ne_of_lt
    ((diamondChoiValue_le_finiteDiamond T).trans_lt (diamond_finite_attained_maximum D E T).1)
  let δ : ℝ := (diamondChoiValue T).toReal
  have hδ : 0 ≤ δ := ENNReal.toReal_nonneg
  have hinput (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
      Matrix.traceNorm (tensorLeft T X) ≤ δ * Matrix.traceNorm X := by
    obtain ⟨s,u,v,hs,hX,_,htrace,hnormal⟩ := diamond_svd_trace_decomposition X
    let P : (Fin D × Fin D) → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
      fun i a b => u i a * star (v i b)
    have hP (i : Fin D × Fin D) : Matrix.traceNorm (tensorLeft T (P i)) ≤ δ := by
      obtain ⟨ρ,σ,hscore⟩ := raw_rankOne_as_diamondChoiScore T (u i) (v i)
        (hnormal i).1 (hnormal i).2
      change Matrix.traceNorm (tensorLeft T (fun a b => u i a * star (v i b))) ≤ δ
      rw [hscore]
      apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
      exact le_iSup_of_le ρ (le_iSup_of_le σ le_rfl)
    have hsum : tensorLeft T X = ∑ i, (s i : ℂ) • tensorLeft T (P i) := by
      change diamondAmplification T D X = _
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
      _ = δ * Matrix.traceNorm X := by
        rw [htrace, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
  calc
    _ ≤ ENNReal.ofReal δ := (finiteDiamondNorm_le_iff_uniform D E T δ hδ).mpr
      (diamond_uniform_bound_of_input_bound T δ hinput)
    _ = diamondChoiValue T := ENNReal.ofReal_toReal hfinite

/-- For positive input dimension, a pair of density inputs attains both the finite diamond norm
and the Choi variational value. -/
theorem diamondChoi_attained {D E : ℕ} (hD : 0 < D) (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ ρ σ : DensityInput D,
      finiteDiamondNorm T = ENNReal.ofReal (diamondChoiScore T ρ σ) ∧
      diamondChoiValue T = ENNReal.ofReal (diamondChoiScore T ρ σ) := by
  classical
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  obtain ⟨-, X, hXnorm, hvalue⟩ := diamond_finite_attained_maximum D E T
  let δ : ℝ := Matrix.traceNorm (tensorLeft T X)
  have hδ : 0 ≤ δ := Matrix.traceNorm_nonneg _
  obtain ⟨s,u,v,hs,hX,hunit,htrace,hnormal⟩ := diamond_svd_trace_decomposition X
  let P : (Fin D × Fin D) → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    fun i a b => u i a * star (v i b)
  let q : (Fin D × Fin D) → ℝ := fun i => Matrix.traceNorm (tensorLeft T (P i))
  obtain ⟨i, -, hmax⟩ := Finset.univ.exists_max_image q Finset.univ_nonempty
  have hqnonneg : 0 ≤ q i := Matrix.traceNorm_nonneg _
  have hsum : tensorLeft T X = ∑ j, (s j : ℂ) • tensorLeft T (P j) := by
    change diamondAmplification T D X = _
    rw [hX, map_sum]
    simp only [map_smul]
    rfl
  have hlower : δ ≤ q i := by
    calc
      δ ≤ ∑ j, Matrix.traceNorm ((s j : ℂ) • tensorLeft T (P j)) := by
        dsimp [δ]
        rw [hsum]
        exact diamond_traceNorm_sum_le Finset.univ _
      _ = ∑ j, s j * q j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_of_nonneg (hs j)]
      _ ≤ ∑ j, s j * q i := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hs j)
      _ = (Matrix.traceNorm X) * q i := by rw [htrace, Finset.sum_mul]
      _ ≤ 1 * q i := mul_le_mul_of_nonneg_right hXnorm hqnonneg
      _ = q i := one_mul _
  have hupper : q i ≤ δ := by
    have hnorm : Matrix.traceNorm (P i) = 1 := by simpa only [P, Matrix.of_apply] using! hunit i
    have hb := finiteDiamondNorm_apply T D (P i)
    rw [hnorm, hvalue, ENNReal.ofReal_one, mul_one] at hb
    exact (ENNReal.ofReal_le_ofReal_iff hδ).mp hb
  obtain ⟨ρ,σ,hscore⟩ := raw_rankOne_as_diamondChoiScore T (u i) (v i)
    (hnormal i).1 (hnormal i).2
  have hreal : δ = diamondChoiScore T ρ σ := by
    change Matrix.traceNorm (tensorLeft T (P i)) = _ at hscore
    exact (le_antisymm hlower hupper).trans hscore
  have hnorm : finiteDiamondNorm T = ENNReal.ofReal (diamondChoiScore T ρ σ) :=
    hvalue.trans (congrArg ENNReal.ofReal hreal)
  exact ⟨ρ,σ,hnorm, (finiteDiamondNorm_eq_choi T).symm.trans hnorm⟩

/-- There is no density input in dimension zero. -/
theorem densityInput_zero_empty : IsEmpty (DensityInput 0) := by
  constructor
  intro ρ
  have h := ρ.property.2
  simp [HermitianMat.trace, Matrix.trace] at h

/-- The finite diamond distance is half the Choi variational value of the difference of the two
maps. -/
theorem finiteDiamondDistance_choi {D E : ℕ} (T S : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondDistance T S = (1/2 : ENNReal) * diamondChoiValue (T-S) := by
  unfold finiteDiamondDistance
  rw [finiteDiamondNorm_eq_choi]

/-- The Choi variational value is zero when the input dimension is zero. -/
theorem diamondChoiValue_zero_input {E : ℕ} (T : Operator 0 →ₗ[ℂ] Operator E) :
    diamondChoiValue T = 0 := by
  letI := densityInput_zero_empty
  simp [diamondChoiValue]

set_option backward.isDefEq.respectTransparency false

/-- The direct sum of positive semidefinite Hermitian matrices is positive semidefinite. -/
theorem directSum_nonneg {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {P : HermitianMat I ℂ} {Q : HermitianMat J ℂ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) : 0 ≤ directSum P Q := by
  apply HermitianMat.zero_le_iff.mpr
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨(directSum P Q).H, fun v => ?_⟩
  have hp := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (HermitianMat.zero_le_iff.mp hP)).2 (fun i => v (Sum.inl i))
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (HermitianMat.zero_le_iff.mp hQ)).2 (fun i => v (Sum.inr i))
  simpa only [directSum, HermitianMat.mat_mk, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    Pi.star_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
    using! add_nonneg hp hq

/-- The left principal block of a direct sum is its first summand. -/
@[simp] theorem principalBlock_directSum_left {I J : Type*} [Fintype I] [Fintype J]
    (P : HermitianMat I ℂ) (Q : HermitianMat J ℂ) :
    principalBlock (directSum P Q) Sum.inl = P := by
  apply HermitianMat.ext
  rfl

/-- The right principal block of a direct sum is its second summand. -/
@[simp] theorem principalBlock_directSum_right {I J : Type*} [Fintype I] [Fintype J]
    (P : HermitianMat I ℂ) (Q : HermitianMat J ℂ) :
    principalBlock (directSum P Q) Sum.inr = Q := by
  apply HermitianMat.ext
  rfl

/-- Pairing a direct sum with a Hermitian matrix splits into pairings with the corresponding
principal blocks. -/
theorem directSum_inner {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (P : HermitianMat I ℂ) (Q : HermitianMat J ℂ)
    (M : HermitianMat (I ⊕ J) ℂ) :
    ⟪directSum P Q, M⟫_ℝ =
      ⟪P, principalBlock M Sum.inl⟫_ℝ + ⟪Q, principalBlock M Sum.inr⟫_ℝ := by
  simp only [inner_eq_real_trace, ← Complex.add_re]
  apply congrArg Complex.re
  change (∑ i, ∑ j, (directSum P Q).mat i j * M.mat j i) =
    (∑ i, ∑ j, P.mat i j * M.mat (Sum.inl j) (Sum.inl i)) +
      (∑ i, ∑ j, Q.mat i j * M.mat (Sum.inr j) (Sum.inr i))
  simp only [Fintype.sum_sum_type, directSum, HermitianMat.mat_mk,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]

/-- Density lifting is adjoint to the left partial trace for the real inner product. -/
theorem densityLift_inner {D E : ℕ} (ρ : HermitianMat (Fin D) ℂ)
    (Y : HermitianMat (Fin E × Fin D) ℂ) :
    ⟪densityLift ρ, Y⟫_ℝ = ⟪ρ, Y.traceLeft⟫_ℝ := by
  rw [real_inner_comm Y (densityLift ρ), real_inner_comm Y.traceLeft ρ]
  simp only [inner_eq_real_trace, densityLift, HermitianMat.kronecker_mat,
    HermitianMat.mat_one, HermitianMat.traceLeft_mat]
  exact congrArg Complex.re (Matrix.trace_mul_one_kron_right Y.mat ρ.mat)

/-- The diamond equality map sends primal block data to the two input traces and zero residual
blocks. -/
@[simp] theorem diamondEqMap_primalData {D E : ℕ}
    (ρ σ : HermitianMat (Fin D) ℂ)
    (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :
    diamondEqMap D E (diamondPrimalData ρ σ X) = diamondDualData ρ.trace σ.trace 0 0 := by
  change WithLp.toLp 2 (WithLp.toLp 2 (ρ.trace, σ.trace),
    WithLp.toLp 2 (densityLift ρ - densityLift ρ, densityLift σ - densityLift σ)) = _
  simp only [sub_self, diamondDualData]

/-- The diamond program's primal score on block data is the real trace pairing of the Choi
matrix with the cross block. -/
theorem diamondProgram_primalScore {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ σ : HermitianMat (Fin D) ℂ)
    (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :
    (diamondProgram T).primalScore (diamondPrimalData ρ σ X) =
      (Matrix.trace ((MatrixMap.choi_matrix T)ᴴ * X)).re := by
  change ⟪directSum 0 ((1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T)),
    directSum (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal ρ σ) (fidelityPrimalBlock (densityLift ρ) (densityLift σ) X)⟫_ℝ = _
  rw [directSum_inner, principalBlock_directSum_left, principalBlock_directSum_right,
    inner_zero_left, zero_add]
  exact weightedBlockProgram_primalScore _ _ _ _

/-- Pairing a block diagonal matrix with a Hermitian matrix splits into pairings with its two
principal blocks. -/
theorem blockDiagonal_inner_general {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (M : HermitianMat (I ⊕ I) ℂ) :
    ⟪Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q, M⟫_ℝ =
      ⟪P, principalBlock M Sum.inl⟫_ℝ + ⟪Q, principalBlock M Sum.inr⟫_ℝ :=
  directSum_inner P Q M

/-- The diamond equality map records the two input traces and the deviations of the output
diagonal blocks from the lifted input blocks. -/
theorem diamondEqMap_apply {D E : ℕ} (M : HermitianMat (DiamondRegister D E) ℂ) :
    diamondEqMap D E M = diamondDualData
      (principalBlock (principalBlock M Sum.inl) Sum.inl).trace
      (principalBlock (principalBlock M Sum.inl) Sum.inr).trace
      (principalBlock (principalBlock M Sum.inr) Sum.inl -
        densityLift (principalBlock (principalBlock M Sum.inl) Sum.inl))
      (principalBlock (principalBlock M Sum.inr) Sum.inr -
        densityLift (principalBlock (principalBlock M Sum.inl) Sum.inr)) := by
  rfl

/-- Pairing `diamondAdjointData` with a primal matrix equals pairing its dual data with the
image under `diamondEqMap`. -/
theorem diamondAdjointData_inner {D E : ℕ} (a b : ℝ)
    (Y Z : HermitianMat (Fin E × Fin D) ℂ)
    (M : HermitianMat (DiamondRegister D E) ℂ) :
    ⟪diamondAdjointData a b Y Z, M⟫_ℝ =
      ⟪diamondDualData a b Y Z, diamondEqMap D E M⟫_ℝ := by
  let ρ := principalBlock M (fun i : Fin D => (Sum.inl (Sum.inl i) : DiamondRegister D E))
  let σ := principalBlock M (fun i : Fin D => (Sum.inl (Sum.inr i) : DiamondRegister D E))
  let P := principalBlock M (fun i : Fin E × Fin D => (Sum.inr (Sum.inl i) : DiamondRegister D E))
  let Q := principalBlock M (fun i : Fin E × Fin D => (Sum.inr (Sum.inr i) : DiamondRegister D E))
  have hl : ⟪diamondAdjointData a b Y Z, M⟫_ℝ =
      a * ρ.trace - ⟪Y.traceLeft, ρ⟫_ℝ +
        (b * σ.trace - ⟪Z.traceLeft, σ⟫_ℝ) + ⟪Y, P⟫_ℝ + ⟪Z, Q⟫_ℝ := by
    unfold diamondAdjointData
    rw [directSum_inner, blockDiagonal_inner_general, blockDiagonal_inner_general]
    simp only [inner_sub_left, real_inner_smul_left, HermitianMat.one_inner]
    change a * ρ.trace - ⟪Y.traceLeft, ρ⟫_ℝ +
      (b * σ.trace - ⟪Z.traceLeft, σ⟫_ℝ) + (⟪Y, P⟫_ℝ + ⟪Z, Q⟫_ℝ) =
      a * ρ.trace - ⟪Y.traceLeft, ρ⟫_ℝ +
      (b * σ.trace - ⟪Z.traceLeft, σ⟫_ℝ) + ⟪Y, P⟫_ℝ + ⟪Z, Q⟫_ℝ
    ring
  rw [hl]
  rw [diamondEqMap_apply]
  change _ = ⟪diamondDualData a b Y Z,
    diamondDualData ρ.trace σ.trace (P - densityLift ρ) (Q - densityLift σ)⟫_ℝ
  change _ = (ρ.trace * a + σ.trace * b) +
    (⟪Y, P - densityLift ρ⟫_ℝ + ⟪Z, Q - densityLift σ⟫_ℝ)
  rw [inner_sub_right, inner_sub_right]
  rw [real_inner_comm ρ Y.traceLeft, real_inner_comm σ Z.traceLeft,
    real_inner_comm (densityLift ρ) Y, real_inner_comm (densityLift σ) Z,
    densityLift_inner, densityLift_inner]
  ring

/-- The adjoint of `diamondEqMap` on dual data is `diamondAdjointData`. -/
@[simp] theorem diamondEqMap_adjoint {D E : ℕ} (a b : ℝ)
    (Y Z : HermitianMat (Fin E × Fin D) ℂ) :
    (diamondEqMap D E).adjoint (diamondDualData a b Y Z) =
      diamondAdjointData a b Y Z := by
  apply ext_inner_right ℝ
  intro M
  rw [ContinuousLinearMap.adjoint_inner_left, diamondAdjointData_inner]

/-- The diamond program's dual score on `diamondDualData a b Y Z` is `a + b`. -/
@[simp] theorem diamondProgram_dualScore {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (a b : ℝ) (Y Z : HermitianMat (Fin E × Fin D) ℂ) :
    (diamondProgram T).dualScore (diamondDualData a b Y Z) = a + b := by
  change ⟪diamondDualData 1 1 0 0, diamondDualData a b Y Z⟫_ℝ = _
  simp [diamondDualData, WithLp.prod_inner_apply]

/-- Restricting a positive semidefinite Hermitian matrix along any index map preserves positive
semidefiniteness. -/
theorem principalBlock_nonneg {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {M : HermitianMat J ℂ} (hM : 0 ≤ M) (e : I → J) :
    0 ≤ principalBlock M e :=
  HermitianMat.zero_le_iff.mpr ((HermitianMat.zero_le_iff.mp hM).submatrix e)

/-- A direct sum is positive semidefinite exactly when both summands are positive semidefinite. -/
theorem directSum_nonneg_iff {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (P : HermitianMat I ℂ) (Q : HermitianMat J ℂ) :
    0 ≤ directSum P Q ↔ 0 ≤ P ∧ 0 ≤ Q := by
  constructor
  · intro h
    exact ⟨by simpa using! principalBlock_nonneg h Sum.inl,
      by simpa using! principalBlock_nonneg h Sum.inr⟩
  · rintro ⟨hP,hQ⟩
    exact directSum_nonneg hP hQ

/-- A block diagonal matrix is positive semidefinite exactly when both diagonal blocks are
positive semidefinite. -/
theorem blockDiagonal_nonneg_iff {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : 0 ≤ Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q ↔ 0 ≤ P ∧ 0 ≤ Q :=
  directSum_nonneg_iff P Q

/-- Diamond primal block data are feasible exactly when the two inputs are density matrices and
the lifted fidelity block is positive semidefinite. -/
theorem diamondProgram_primal_block_iff {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ σ : HermitianMat (Fin D) ℂ)
    (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :
    (diamondProgram T).PrimalFeasible (diamondPrimalData ρ σ X) ↔
      (0 ≤ ρ ∧ ρ.trace = 1) ∧ (0 ≤ σ ∧ σ.trace = 1) ∧
        (fidelityPrimalBlock (densityLift ρ) (densityLift σ) X).mat.PosSemidef := by
  change (0 ≤ diamondPrimalData ρ σ X ∧
    diamondEqMap D E (diamondPrimalData ρ σ X) = diamondDualData 1 1 0 0) ↔ _
  rw [diamondEqMap_primalData]
  have heq : diamondDualData (D := D) (E := E) ρ.trace σ.trace 0 0 = diamondDualData 1 1 0 0 ↔
      ρ.trace = 1 ∧ σ.trace = 1 := by
    unfold diamondDualData
    rw [(WithLp.toLp_injective 2).eq_iff, Prod.mk.injEq,
      (WithLp.toLp_injective 2).eq_iff, Prod.mk.injEq]
    simp only [and_true]
  rw [heq]
  unfold diamondPrimalData
  rw [directSum_nonneg_iff, blockDiagonal_nonneg_iff]
  simp only [HermitianMat.zero_le_iff]
  tauto

/-- The direct sum of positive definite Hermitian matrices is positive definite. -/
theorem directSum_posDef {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {P : HermitianMat I ℂ} {Q : HermitianMat J ℂ}
    (hP : P.mat.PosDef) (hQ : Q.mat.PosDef) : (directSum P Q).mat.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (directSum P Q).H
  intro v hv
  have heq : star v ⬝ᵥ ((directSum P Q).mat *ᵥ v) =
      star (fun i => v (Sum.inl i)) ⬝ᵥ (P.mat *ᵥ (fun i => v (Sum.inl i))) +
        star (fun i => v (Sum.inr i)) ⬝ᵥ (Q.mat *ᵥ (fun i => v (Sum.inr i))) := by
    simp only [directSum, HermitianMat.mat_mk, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Pi.star_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  rw [heq]
  by_cases hl : (fun i => v (Sum.inl i)) = 0
  · have hr : (fun i => v (Sum.inr i)) ≠ 0 := by
      intro hr
      apply hv
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    exact add_pos_of_nonneg_of_pos (hP.posSemidef.dotProduct_mulVec_nonneg _)
      (hQ.dotProduct_mulVec_pos hr)
  · exact add_pos_of_pos_of_nonneg (hP.dotProduct_mulVec_pos hl)
      (hQ.posSemidef.dotProduct_mulVec_nonneg _)

/-- The diamond program satisfies primal Slater feasibility when the input dimension is
positive. -/
theorem diamondProgram_primal_strict {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) : (diamondProgram T).PrimalSlater := by
  let ρ : HermitianMat (Fin D) ℂ := (D : ℝ)⁻¹ • 1
  have hp : ρ.mat.PosDef := by
    exact Matrix.PosDef.one.smul (inv_pos.mpr (Nat.cast_pos.mpr hD))
  have hl : (densityLift (E := E) ρ).mat.PosDef := by
    exact Matrix.PosDef.one.kronecker hp
  have htrace : ρ.trace = 1 := by
    simp only [ρ, HermitianMat.trace_smul, HermitianMat.trace_one, Fintype.card_fin]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD))
  refine ⟨diamondPrimalData (E := E) ρ ρ 0, ?_, ?_⟩
  · have hz : fidelityPrimalBlock (densityLift (E := E) ρ) (densityLift ρ) 0 =
        directSum (densityLift ρ) (densityLift ρ) := by
      apply HermitianMat.ext
      simp only [fidelityPrimalBlock, directSum, HermitianMat.mat_mk, Matrix.conjTranspose_zero]
    change (directSum (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal ρ ρ) (fidelityPrimalBlock (densityLift ρ) (densityLift ρ) 0)).mat.PosDef
    rw [hz]
    exact directSum_posDef (directSum_posDef hp hp) (directSum_posDef hl hl)
  · change diamondEqMap D E (diamondPrimalData ρ ρ 0) = diamondDualData 1 1 0 0
    rw [diamondEqMap_primalData, htrace]

/-- Subtracting a Hermitian matrix from the identity scaled by its norm plus one gives a
positive definite matrix. -/
theorem scalar_majorant_posDef {I : Type*} [Fintype I] [DecidableEq I]
    (A : HermitianMat I ℂ) : (((‖A‖ + 1) • (1 : HermitianMat I ℂ)) - A).mat.PosDef := by
  have hA : A ≤ ‖A‖ • (1 : HermitianMat I ℂ) :=
    A.eigenvalues_le_imp_le_smul_one ‖A‖ fun i =>
      (le_abs_self _).trans (A.eigenvalue_norm_le i)
  have hp : (‖A‖ • (1 : HermitianMat I ℂ) - A).mat.PosSemidef :=
    HermitianMat.zero_le_iff.mp (sub_nonneg.mpr hA)
  have heq : (‖A‖ + 1) • (1 : HermitianMat I ℂ) - A =
      1 + (‖A‖ • 1 - A) := by module
  rw [heq, HermitianMat.mat_add, HermitianMat.mat_one]
  exact Matrix.PosDef.one.add_posSemidef hp

/-- The diamond program satisfies dual Slater feasibility. -/
theorem diamondProgram_dual_strict {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    (diamondProgram T).DualSlater := by
  obtain ⟨W, hW⟩ := weightedBlockProgram_dual_strict
    (0 : HermitianMat (Fin E × Fin D) ℂ) 0 (MatrixMap.choi_matrix T)
  let Y := principalBlock W Sum.inl
  let Z := principalBlock W Sum.inr
  have hw : (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z - (1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T)).mat.PosDef := by
    change (((blockPinch : HermitianMat ((Fin E × Fin D) ⊕ (Fin E × Fin D)) ℂ →L[ℝ] _).adjoint W) -
      (1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T)).mat.PosDef at hW
    rw [blockPinch_adjoint] at hW
    have heq : blockPinch W = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z := by
      apply HermitianMat.ext
      ext i j
      cases i <;> cases j <;> rfl
    rwa [heq] at hW
  refine ⟨diamondDualData (‖Y.traceLeft‖ + 1) (‖Z.traceLeft‖ + 1) Y Z, ?_⟩
  change ((diamondEqMap D E).adjoint _ - (diamondProgram T).objective).mat.PosDef
  rw [diamondEqMap_adjoint]
  have heq : diamondAdjointData (‖Y.traceLeft‖ + 1) (‖Z.traceLeft‖ + 1) Y Z -
      (diamondProgram T).objective =
      directSum (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal ((‖Y.traceLeft‖ + 1) • 1 - Y.traceLeft)
        ((‖Z.traceLeft‖ + 1) • 1 - Z.traceLeft))
        (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z - (1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T)) := by
    apply HermitianMat.ext
    change Matrix.fromBlocks _ 0 0 _ - Matrix.fromBlocks 0 0 0 _ =
      Matrix.fromBlocks _ 0 0 _
    rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp only [neg_zero, add_zero, sub_eq_add_neg, HermitianMat.mat_add, HermitianMat.mat_neg]
  rw [heq]
  exact directSum_posDef
    (directSum_posDef (scalar_majorant_posDef _) (scalar_majorant_posDef _)) hw

/-- For positive input dimension, the diamond program has primal and dual optimizers with a
common supremum and infimum. -/
theorem diamondProgram_both_optimizers {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (y : DiamondConstraints D E),
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).DualFeasible y ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      (diamondProgram T).primalScore M = α ∧ (diamondProgram T).dualScore y = α :=
  Program.bothSlater_optimizers _ (diamondProgram_primal_strict hD T)
    (diamondProgram_dual_strict T)

/-- Every diamond primal feasible matrix yields two density inputs and a positive semidefinite
fidelity block with the same primal score. -/
theorem diamondProgram_primal_reduction {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {M : HermitianMat (DiamondRegister D E) ℂ} (hM : (diamondProgram T).PrimalFeasible M) :
    ∃ (ρ σ : DensityInput D) (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ),
      (fidelityPrimalBlock (densityLift ρ.val) (densityLift σ.val) X).mat.PosSemidef ∧
        (diamondProgram T).primalScore M = (Matrix.trace ((MatrixMap.choi_matrix T)ᴴ * X)).re := by
  let A := principalBlock M Sum.inl
  let B := principalBlock M Sum.inr
  let ρ := principalBlock A Sum.inl
  let σ := principalBlock A Sum.inr
  let P := principalBlock B Sum.inl
  let Q := principalBlock B Sum.inr
  have hρ : 0 ≤ ρ := principalBlock_nonneg (principalBlock_nonneg hM.1 Sum.inl) Sum.inl
  have hσ : 0 ≤ σ := principalBlock_nonneg (principalBlock_nonneg hM.1 Sum.inl) Sum.inr
  have heq : diamondDualData ρ.trace σ.trace (P - densityLift ρ) (Q - densityLift σ) =
      diamondDualData 1 1 0 0 := hM.2
  unfold diamondDualData at heq
  rw [(WithLp.toLp_injective 2).eq_iff, Prod.mk.injEq] at heq
  have htr := (WithLp.toLp_injective 2) heq.1
  have hres := (WithLp.toLp_injective 2) heq.2
  have hρtr : ρ.trace = 1 := congrArg Prod.fst htr
  have hσtr : σ.trace = 1 := congrArg Prod.snd htr
  have hP : P = densityLift ρ := sub_eq_zero.mp (congrArg Prod.fst hres)
  have hQ : Q = densityLift σ := sub_eq_zero.mp (congrArg Prod.snd hres)
  have hp : blockPinch B = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (densityLift ρ) (densityLift σ) := by
    rw [← hP, ← hQ]
    apply HermitianMat.ext
    ext i j
    cases i <;> cases j <;> rfl
  have hb : (weightedBlockProgram (densityLift ρ) (densityLift σ)
      (MatrixMap.choi_matrix T)).PrimalFeasible B :=
    ⟨principalBlock_nonneg hM.1 Sum.inr, hp⟩
  obtain ⟨X, hX⟩ := weightedBlockProgram_primal_shape hb
  refine ⟨⟨ρ,hρ,hρtr⟩, ⟨σ,hσ,hσtr⟩, X, ?_, ?_⟩
  · simpa only [hX, HermitianMat.zero_le_iff] using! hb.1
  · change ⟪directSum 0 ((1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T)), M⟫_ℝ = _
    rw [directSum_inner, inner_zero_left, zero_add]
    change (weightedBlockProgram (densityLift ρ) (densityLift σ)
      (MatrixMap.choi_matrix T)).primalScore B = _
    rw [hX, weightedBlockProgram_primalScore]

/-- Taking the positive square root commutes with density lifting for positive semidefinite
input matrices. -/
theorem densityLift_sqrt {D E : ℕ} {ρ : HermitianMat (Fin D) ℂ} (hρ : 0 ≤ ρ) :
    (densityLift (E := E) ρ).sqrt = densityLift ρ.sqrt := by
  have hs : (densityLift (E := E) ρ.sqrt)^2 = densityLift ρ := by
    apply HermitianMat.ext
    simp only [HermitianMat.mat_pow, pow_two, densityLift, HermitianMat.kronecker_mat,
      HermitianMat.mat_one]
    rw [← Matrix.mul_kronecker_mul, one_mul, HermitianMat.sqrt_sq hρ]
  rw [← hs]
  exact sqrt_square_nonneg (show 0 ≤ densityLift (E := E) ρ.sqrt from
    HermitianMat.kronecker_nonneg (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one) ρ.sqrt_nonneg)

/-- The sandwiched trace norm of the Choi matrix between lifted density inputs is
`diamondChoiScore`. -/
theorem densityLift_sandwichedTraceNorm {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ σ : DensityInput D) :
    sandwichedTraceNorm (densityLift ρ.val) (densityLift σ.val) (MatrixMap.choi_matrix T) =
      diamondChoiScore T ρ σ := by
  unfold sandwichedTraceNorm diamondChoiScore
  rw [densityLift_sqrt ρ.property.1, densityLift_sqrt σ.property.1]
  rfl

/-- For positive input dimension, the diamond program attains a primal supremum whose image
under `ENNReal.ofReal` is the finite diamond norm. -/
theorem diamondProgram_primal_norm_attained {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      IsLUB (diamondProgram T).primalValues α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α := by
  obtain ⟨ρ,σ,hnorm,hchoi⟩ := diamondChoi_attained hD T
  have hp : 0 ≤ densityLift (E := E) ρ.val :=
    HermitianMat.kronecker_nonneg (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one) ρ.property.1
  have hq : 0 ≤ densityLift (E := E) σ.val :=
    HermitianMat.kronecker_nonneg (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one) σ.property.1
  obtain ⟨X,hX,hscore⟩ := weightedBlock_norm_attained hp hq (MatrixMap.choi_matrix T)
  rw [densityLift_sandwichedTraceNorm] at hscore
  let M := diamondPrimalData ρ.val σ.val X
  have hfeas : (diamondProgram T).PrimalFeasible M :=
    (diamondProgram_primal_block_iff T ρ.val σ.val X).mpr ⟨ρ.property,σ.property,hX⟩
  have hMscore : (diamondProgram T).primalScore M = diamondChoiScore T ρ σ := by
    rw [diamondProgram_primalScore]
    exact hscore
  refine ⟨diamondChoiScore T ρ σ, M, hnorm, ?_, hfeas, hMscore⟩
  have hm : diamondChoiScore T ρ σ ∈ (diamondProgram T).primalValues :=
    ⟨M,hfeas,hMscore⟩
  refine ⟨?_, fun b hb => hb hm⟩
  rintro a ⟨N,hN,rfl⟩
  obtain ⟨ρ',σ',X',hX',hs⟩ := diamondProgram_primal_reduction T hN
  rw [hs]
  have hb := weightedBlock_score_le_norm
    (show 0 ≤ densityLift (E := E) ρ'.val from HermitianMat.kronecker_nonneg
      (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one) ρ'.property.1)
    (show 0 ≤ densityLift (E := E) σ'.val from HermitianMat.kronecker_nonneg
      (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one) σ'.property.1)
    (MatrixMap.choi_matrix T) hX'
  rw [densityLift_sandwichedTraceNorm] at hb
  apply hb.trans
  have he : ENNReal.ofReal (diamondChoiScore T ρ' σ') ≤
      ENNReal.ofReal (diamondChoiScore T ρ σ) := by
    rw [← hchoi]
    exact le_iSup_of_le ρ' (le_iSup_of_le σ' le_rfl)
  exact (ENNReal.ofReal_le_ofReal_iff (Matrix.traceNorm_nonneg _)).mp he

/-- For positive input dimension, primal and dual optimizers of the diamond program attain the
finite diamond norm; see [Watrous2018]. -/
theorem diamondProgram_norm_both_optimizers {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (y : DiamondConstraints D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).DualFeasible y ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      (diamondProgram T).primalScore M = α ∧ (diamondProgram T).dualScore y = α := by
  obtain ⟨α,M,y,hM,hy,hp,hd,hsM,hsy⟩ := diamondProgram_both_optimizers hD T
  obtain ⟨β,N,hnorm,hβ,-,-⟩ := diamondProgram_primal_norm_attained hD T
  have heq : β = α := hβ.unique hp
  exact ⟨α,M,y,heq ▸ hnorm,hM,hy,hp,hd,hsM,hsy⟩

section DiamondNormDual
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable local instance diamondMatrixCStar {J : Type*} [Fintype J] [DecidableEq J] :
    CStarAlgebra (Matrix J J ℂ) where

/-- The operator norm of a positive semidefinite matrix times the identity dominates that
matrix. -/
theorem nonneg_opNorm_slack {I : Type*} [Fintype I] [DecidableEq I]
    {A : HermitianMat I ℂ} (hA : 0 ≤ A) :
    0 ≤ ‖A.mat‖ • (1 : HermitianMat I ℂ) - A := by
  have ha : 0 ≤ A.mat := Matrix.nonneg_iff_posSemidef.mpr (HermitianMat.zero_le_iff.mp hA)
  have h := (CStarAlgebra.norm_le_iff_le_algebraMap A.mat (norm_nonneg _) ha).mp le_rfl
  apply HermitianMat.zero_le_iff.mpr
  rw [HermitianMat.mat_sub, HermitianMat.mat_smul, HermitianMat.mat_one]
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  simpa only [Algebra.algebraMap_eq_smul_one] using! h

/-- On a nonempty index type, a scalar identity dominating a positive semidefinite matrix has
scalar at least its operator norm. -/
theorem opNorm_le_of_nonneg_scalar_slack {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : HermitianMat I ℂ} {a : ℝ} (hA : 0 ≤ A) (hslack : 0 ≤ a • 1 - A) :
    ‖A.mat‖ ≤ a := by
  have hs : 0 ≤ a • (1 : HermitianMat I ℂ) := by
    simpa only [sub_add_cancel] using! add_nonneg hslack hA
  obtain ⟨i⟩ := ‹Nonempty I›
  have hd := (HermitianMat.zero_le_iff.mp hs).diag_nonneg (i := i)
  have ha : 0 ≤ a := by
    have hd' : (0 : ℂ) ≤ (a : ℂ) := by simpa using! hd
    exact_mod_cast hd'
  apply (CStarAlgebra.norm_le_iff_le_algebraMap A.mat ha
    (Matrix.nonneg_iff_posSemidef.mpr (HermitianMat.zero_le_iff.mp hA))).mpr
  rw [Algebra.algebraMap_eq_smul_one]
  simpa only [HermitianMat.mat_sub, HermitianMat.mat_smul, HermitianMat.mat_one,
    Matrix.nonneg_iff_posSemidef, sub_nonneg] using! HermitianMat.zero_le_iff.mp hslack

/-- The diamond dual slack splits into partial trace scalar slacks and the Choi coupling block. -/
theorem diamondProgram_dual_slack {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (a b : ℝ) (Y Z : HermitianMat (Fin E × Fin D) ℂ) :
    (diamondProgram T).constraint.adjoint (diamondDualData a b Y Z) -
      (diamondProgram T).objective =
      directSum (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (a • 1 - Y.traceLeft) (b • 1 - Z.traceLeft))
        (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z - (1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T)) := by
  change (diamondEqMap D E).adjoint _ - _ = _
  rw [diamondEqMap_adjoint]
  apply HermitianMat.ext
  change Matrix.fromBlocks _ 0 0 _ - Matrix.fromBlocks 0 0 0 _ = Matrix.fromBlocks _ 0 0 _
  rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp only [neg_zero, add_zero, sub_eq_add_neg, HermitianMat.mat_add, HermitianMat.mat_neg]

/-- Diamond dual feasibility is equivalent to positive semidefiniteness of the two partial trace
scalar slacks and the Choi coupling block. -/
theorem diamondProgram_dual_block_iff {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (a b : ℝ) (Y Z : HermitianMat (Fin E × Fin D) ℂ) :
    (diamondProgram T).DualFeasible (diamondDualData a b Y Z) ↔
      0 ≤ a • 1 - Y.traceLeft ∧ 0 ≤ b • 1 - Z.traceLeft ∧
        0 ≤ Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z - (1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T) := by
  unfold Program.DualFeasible
  rw [diamondProgram_dual_slack, directSum_nonneg_iff, blockDiagonal_nonneg_iff, and_assoc]

/-- The left principal block of `weightedDualBlock C Y Z` is `Y`. -/
theorem weightedDualBlock_principal_left {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℂ) (Y Z : HermitianMat I ℂ) :
    principalBlock (weightedDualBlock C Y Z) Sum.inl = Y := by
  apply HermitianMat.ext
  ext i j
  change Y.mat i j - 0 = Y.mat i j
  simp

/-- The right principal block of `weightedDualBlock C Y Z` is `Z`. -/
theorem weightedDualBlock_principal_right {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℂ) (Y Z : HermitianMat I ℂ) :
    principalBlock (weightedDualBlock C Y Z) Sum.inr = Z := by
  apply HermitianMat.ext
  ext i j
  change Z.mat i j - 0 = Z.mat i j
  simp

/-- Positive semidefiniteness of a weighted dual block implies positive semidefiniteness of both
diagonal blocks. -/
theorem weightedDualBlock_diagonal_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℂ} {Y Z : HermitianMat I ℂ} (h : 0 ≤ weightedDualBlock C Y Z) :
    0 ≤ Y ∧ 0 ≤ Z := by
  exact ⟨by simpa only [weightedDualBlock_principal_left] using! principalBlock_nonneg h Sum.inl,
    by simpa only [weightedDualBlock_principal_right] using! principalBlock_nonneg h Sum.inr⟩

/-- Forming a block diagonal matrix commutes with real scalar multiplication. -/
theorem blockDiagonal_smul {I : Type*} [Fintype I] (r : ℝ) (Y Z : HermitianMat I ℂ) :
    Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (r • Y) (r • Z) = r • Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z := by
  apply HermitianMat.ext
  simp only [Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal, HermitianMat.mat_mk, HermitianMat.mat_smul,
    Matrix.fromBlocks_smul, smul_zero]

/-- The diamond coupling block formed from half-scaled diagonal blocks is half the weighted dual
block. -/
theorem diamond_half_dual_block {I : Type*} [Fintype I] (C : Matrix I I ℂ)
    (Y Z : HermitianMat I ℂ) :
    Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal ((1/2 : ℝ) • Y) ((1/2 : ℝ) • Z) - (1/2 : ℝ) • offDiagonal C =
      (1/2 : ℝ) • weightedDualBlock C Y Z := by
  rw [blockDiagonal_smul, weightedDualBlock, smul_sub]

/-- Doubling the diagonal blocks in a weighted dual block gives twice the diamond coupling
block. -/
theorem diamond_double_dual_block {I : Type*} [Fintype I] (C : Matrix I I ℂ)
    (Y Z : HermitianMat I ℂ) :
    weightedDualBlock C ((2 : ℝ) • Y) ((2 : ℝ) • Z) =
      (2 : ℝ) • (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z - (1/2 : ℝ) • offDiagonal C) := by
  rw [weightedDualBlock, blockDiagonal_smul, smul_sub, smul_smul]
  norm_num

/-- A positive semidefinite source dual block lifts to diamond dual feasible data with score
equal to `diamondDualObjective`. -/
theorem diamondSourceDual_lift {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {Y Z : HermitianMat (Fin E × Fin D) ℂ}
    (h : 0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) Y Z) :
    (diamondProgram T).DualFeasible (diamondDualData
      ((1/2 : ℝ) * ‖Y.traceLeft.mat‖) ((1/2 : ℝ) * ‖Z.traceLeft.mat‖)
      ((1/2 : ℝ) • Y) ((1/2 : ℝ) • Z)) ∧
    (diamondProgram T).dualScore (diamondDualData
      ((1/2 : ℝ) * ‖Y.traceLeft.mat‖) ((1/2 : ℝ) * ‖Z.traceLeft.mat‖)
      ((1/2 : ℝ) • Y) ((1/2 : ℝ) • Z)) = diamondDualObjective Y Z := by
  obtain ⟨hY,hZ⟩ := weightedDualBlock_diagonal_nonneg h
  have hy : 0 ≤ Y.traceLeft :=
    HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp hY).traceLeft
  have hz : 0 ≤ Z.traceLeft :=
    HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp hZ).traceLeft
  refine ⟨(diamondProgram_dual_block_iff _ _ _ _ _).mpr ⟨?_,?_,?_⟩,?_⟩
  · rw [HermitianMat.traceLeft_smul]
    have heq : ((1/2 : ℝ) * ‖Y.traceLeft.mat‖) • (1 : HermitianMat (Fin D) ℂ) -
        (1/2 : ℝ) • Y.traceLeft = (1/2 : ℝ) • (‖Y.traceLeft.mat‖ • 1 - Y.traceLeft) := by module
    rw [heq]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (nonneg_opNorm_slack hy)
  · rw [HermitianMat.traceLeft_smul]
    have heq : ((1/2 : ℝ) * ‖Z.traceLeft.mat‖) • (1 : HermitianMat (Fin D) ℂ) -
        (1/2 : ℝ) • Z.traceLeft = (1/2 : ℝ) • (‖Z.traceLeft.mat‖ • 1 - Z.traceLeft) := by module
    rw [heq]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (nonneg_opNorm_slack hz)
  · rw [diamond_half_dual_block]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) h
  · rw [diamondProgram_dualScore]
    rfl

/-- For positive input dimension, diamond dual feasible data reduce to a source dual block whose
objective is no larger. -/
theorem diamondProgram_dual_reduction {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {y : DiamondConstraints D E}
    (hy : (diamondProgram T).DualFeasible y) :
    ∃ Y Z : HermitianMat (Fin E × Fin D) ℂ,
      0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) Y Z ∧
        diamondDualObjective Y Z ≤ (diamondProgram T).dualScore y := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  let a := (WithLp.ofLp (WithLp.ofLp y).1).1
  let b := (WithLp.ofLp (WithLp.ofLp y).1).2
  let Y := (WithLp.ofLp (WithLp.ofLp y).2).1
  let Z := (WithLp.ofLp (WithLp.ofLp y).2).2
  have heq : y = diamondDualData a b Y Z := rfl
  rw [heq] at hy ⊢
  obtain ⟨ha,hb,hblock⟩ := (diamondProgram_dual_block_iff T a b Y Z).mp hy
  have hd : 0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) ((2 : ℝ) • Y) ((2 : ℝ) • Z) := by
    rw [diamond_double_dual_block]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hblock
  obtain ⟨hY,hZ⟩ := weightedDualBlock_diagonal_nonneg hd
  have hy0 : 0 ≤ Y := by
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hY
    simpa only [smul_smul, show (1/2 : ℝ) * 2 = 1 by norm_num, one_smul] using! hh
  have hz0 : 0 ≤ Z := by
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hZ
    simpa only [smul_smul, show (1/2 : ℝ) * 2 = 1 by norm_num, one_smul] using! hh
  have hYnorm := opNorm_le_of_nonneg_scalar_slack
    (show 0 ≤ Y.traceLeft from
      HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp hy0).traceLeft) ha
  have hZnorm := opNorm_le_of_nonneg_scalar_slack
    (show 0 ≤ Z.traceLeft from
      HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp hz0).traceLeft) hb
  refine ⟨(2 : ℝ) • Y,(2 : ℝ) • Z,hd,?_⟩
  rw [diamondProgram_dualScore]
  unfold diamondDualObjective
  simp only [HermitianMat.traceLeft_smul, HermitianMat.mat_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The diamond program's primal value set equals `diamondSourcePrimalValues`. -/
theorem diamondProgram_primalValues_eq_source {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) :
    (diamondProgram T).primalValues = diamondSourcePrimalValues T := by
  ext a
  constructor
  · rintro ⟨M,hM,rfl⟩
    obtain ⟨ρ,σ,X,hX,hs⟩ := diamondProgram_primal_reduction T hM
    exact ⟨ρ,σ,X,hX,hs.symm⟩
  · rintro ⟨ρ,σ,X,hX,hs⟩
    refine ⟨diamondPrimalData ρ.val σ.val X,
      (diamondProgram_primal_block_iff T ρ.val σ.val X).mpr ⟨ρ.property,σ.property,hX⟩,?_⟩
    rw [diamondProgram_primalScore]
    exact hs

/-- For positive input dimension, a diamond primal optimizer and a source dual optimizer attain
the finite diamond norm. -/
theorem diamondSourceDual_norm_attained {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ)
        (Y Z : HermitianMat (Fin E × Fin D) ℂ),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧
      0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) Y Z ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondSourceDualValues T) α ∧
      (diamondProgram T).primalScore M = α ∧ diamondDualObjective Y Z = α := by
  obtain ⟨α,M,y,hnorm,hM,hy,hp,hd,hsM,hsy⟩ := diamondProgram_norm_both_optimizers hD T
  obtain ⟨Y,Z,hblock,hbound⟩ := diamondProgram_dual_reduction hD T hy
  have hlower : α ≤ diamondDualObjective Y Z := by
    have hw :=
        (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality (P := (diamondProgram T))) hM (diamondSourceDual_lift T hblock).1
    rwa [hsM,(diamondSourceDual_lift T hblock).2] at hw
  have heq : diamondDualObjective Y Z = α := le_antisymm (hbound.trans_eq hsy) hlower
  refine ⟨α,M,Y,Z,hnorm,hM,hblock,hp,?_,hsM,heq⟩
  have hm : α ∈ diamondSourceDualValues T := ⟨Y,Z,hblock,heq⟩
  refine ⟨?_,fun b hb => hb hm⟩
  rintro a ⟨Y',Z',hb,rfl⟩
  have hw :=
      (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality (P := (diamondProgram T))) hM (diamondSourceDual_lift T hb).1
  rwa [hsM,(diamondSourceDual_lift T hb).2] at hw

/-- For positive input dimension, the source primal and dual formulations attain a common value
equal to the finite diamond norm; see [Watrous2018]. -/
theorem diamondSource_norm_both_optimizers {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ (α : ℝ) (ρ σ : DensityInput D)
        (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ)
        (Y Z : HermitianMat (Fin E × Fin D) ℂ),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (fidelityPrimalBlock (densityLift ρ.val) (densityLift σ.val) X).mat.PosSemidef ∧
      0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) Y Z ∧ 0 ≤ Y ∧ 0 ≤ Z ∧
      IsLUB (diamondSourcePrimalValues T) α ∧ IsGLB (diamondSourceDualValues T) α ∧
      (Matrix.trace ((MatrixMap.choi_matrix T)ᴴ * X)).re = α ∧ diamondDualObjective Y Z = α := by
  obtain ⟨α,M,Y,Z,hnorm,hM,hblock,hp,hd,hsM,hsYZ⟩ := diamondSourceDual_norm_attained hD T
  obtain ⟨ρ,σ,X,hX,hsX⟩ := diamondProgram_primal_reduction T hM
  obtain ⟨hY,hZ⟩ := weightedDualBlock_diagonal_nonneg hblock
  rw [diamondProgram_primalValues_eq_source] at hp
  exact ⟨α,ρ,σ,X,Y,Z,hnorm,hX,hblock,hY,hZ,hp,hd,hsX.symm.trans hsM,hsYZ⟩

end DiamondNormDual

/-- The trace norm of `A * Bᴴ` equals the root fidelity of the two input Gram matrices. -/
theorem square_frame_cross_traceNorm {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) :
    Matrix.traceNorm (A * Bᴴ) = rootFidelity (inputGram A) (inputGram B) := by
  obtain ⟨U,hU,-,hA⟩ := inputGram_polar A
  obtain ⟨V,hV,-,hB⟩ := inputGram_polar B
  have heq : A * Bᴴ = U * ((inputGram A).sqrt.mat * (inputGram B).sqrt.mat) * Vᴴ := by
    calc
      _ = (U * (inputGram A).sqrt.mat) * (V * (inputGram B).sqrt.mat)ᴴ :=
        congrArg₂ (fun X Y => X * Yᴴ) hA hB
      _ = _ := by
        simp only [Matrix.conjTranspose_mul, (inputGram B).sqrt.H.eq, Matrix.mul_assoc]
  rw [heq,traceNorm_two_isometries U V _ hU hV]
  rfl

/-- The positive square root commutes with conjugation by an isometry for positive semidefinite
matrices. -/
theorem sqrt_isometry_conj {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {P : HermitianMat I ℂ} (hP : 0 ≤ P)
    (U : Matrix J I ℂ) (hU : Uᴴ * U = 1) : (P.conj U).sqrt = P.sqrt.conj U := by
  have hs : (P.sqrt.conj U)^2 = P.conj U := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_pow,pow_two]
    simp only [HermitianMat.conj_apply_mat]
    calc
      _ = U * P.sqrt.mat * (Uᴴ * U) * P.sqrt.mat * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * P.mat * Uᴴ := by
        rw [hU,Matrix.mul_one]
        simp only [Matrix.mul_assoc,← Matrix.mul_assoc P.sqrt.mat, HermitianMat.sqrt_sq hP]
  rw [← hs]
  exact sqrt_square_nonneg (HermitianMat.conj_nonneg U P.sqrt_nonneg)

/-- Simultaneous conjugation by an isometry preserves the root fidelity of positive semidefinite
matrices. -/
theorem rootFidelity_isometry_conj {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (U : Matrix J I ℂ) (hU : Uᴴ * U = 1) :
    rootFidelity (P.conj U) (Q.conj U) = rootFidelity P Q := by
  unfold rootFidelity
  rw [sqrt_isometry_conj hP U hU,sqrt_isometry_conj hQ U hU]
  simp only [HermitianMat.conj_apply_mat]
  have heq : U * P.sqrt.mat * Uᴴ * (U * Q.sqrt.mat * Uᴴ) =
      U * (P.sqrt.mat * Q.sqrt.mat) * Uᴴ := by
    calc
      _ = U * P.sqrt.mat * (Uᴴ * U) * Q.sqrt.mat * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU,Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [heq]
  exact traceNorm_two_isometries U U _ hU hU

/-- The trace norm of `A * Bᴴ` equals the root fidelity of the two frame Gram matrices. -/
theorem frame_cross_traceNorm {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A B : Matrix J I ℂ) :
    Matrix.traceNorm (A * Bᴴ) = rootFidelity (frameGram A) (frameGram B) := by
  let U : Matrix (J ⊕ I) J ℂ := (1 : Matrix (J ⊕ I) (J ⊕ I) ℂ).submatrix id Sum.inl
  let V : Matrix (J ⊕ I) I ℂ := (1 : Matrix (J ⊕ I) (J ⊕ I) ℂ).submatrix id Sum.inr
  have hU : Uᴴ * U = 1 := Matrix.submatrix_one_id_right_isometry Sum.inl_injective
  have hV : Vᴴ * V = 1 := Matrix.submatrix_one_id_right_isometry Sum.inr_injective
  let A' := U * A * Vᴴ
  let B' := U * B * Vᴴ
  have hprod : A' * B'ᴴ = U * (A * Bᴴ) * Uᴴ := by
    dsimp [A',B']
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = U * A * (Vᴴ * V) * Bᴴ * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV,Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hGram (C : Matrix J I ℂ) : inputGram (U * C * Vᴴ) = (frameGram C).conj V := by
    apply HermitianMat.ext
    change (U * C * Vᴴ)ᴴ * (U * C * Vᴴ) = V * (Cᴴ * C) * Vᴴ
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = V * Cᴴ * (Uᴴ * U) * C * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU,Matrix.mul_one]; simp only [Matrix.mul_assoc]
  calc
    _ = Matrix.traceNorm (A' * B'ᴴ) := by
      rw [hprod,traceNorm_two_isometries U U _ hU hU]
    _ = rootFidelity (inputGram A') (inputGram B') := square_frame_cross_traceNorm A' B'
    _ = rootFidelity ((frameGram A).conj V) ((frameGram B).conj V) := by rw [hGram,hGram]
    _ = rootFidelity (frameGram A) (frameGram B) :=
      rootFidelity_isometry_conj
        (HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_conjTranspose_mul_self A))
        (HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_conjTranspose_mul_self B)) V hV

/-- Transposition preserves the trace norm of a square complex matrix. -/
theorem traceNorm_transpose {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) : Matrix.traceNorm Mᵀ = Matrix.traceNorm M := by
  let hH : (Mᴴ * M).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self M).1
  obtain ⟨U,V,hM⟩ := Matrix.exists_svd_sqrt_eigenvalues M
  let D : Matrix I I ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hform : M = U.val * D * V.valᴴ := hM
  have hU : U.valᴴ * U.val = 1 := U.prop.1
  have hV : V.valᴴ * V.val = 1 := V.prop.1
  have hct (W : Matrix I I ℂ) : (Wᴴᵀ)ᴴ = Wᵀ := by
    rw [Matrix.transpose_conjTranspose, ← Matrix.conjTranspose_transpose,
      Matrix.conjTranspose_conjTranspose]
  have hc (W : Matrix I I ℂ) (hW : Wᴴ * W = 1) : (Wᴴᵀ)ᴴ * Wᴴᵀ = 1 := by
    rw [hct,← Matrix.transpose_mul,hW,Matrix.transpose_one]
  calc
    _ = Matrix.traceNorm ((U.val * D * V.valᴴ)ᵀ) := congrArg (fun A => Matrix.traceNorm Aᵀ) hform
    _ = Matrix.traceNorm (V.valᴴᵀ * D * (U.valᴴᵀ)ᴴ) := by
      rw [hct]
      simp only [Matrix.transpose_mul,D,Matrix.diagonal_transpose,Matrix.mul_assoc]
    _ = Matrix.traceNorm D := traceNorm_two_isometries _ _ _ (hc _ hV) (hc _ hU)
    _ = Matrix.traceNorm (U.val * D * V.valᴴ) := (traceNorm_two_isometries _ _ _ hU hV).symm
    _ = Matrix.traceNorm M := congrArg Matrix.traceNorm hform.symm

/-- Hermitian transposition is involutive. -/
@[simp] theorem hermitianTranspose_involutive {I : Type*} [Fintype I] (P : HermitianMat I ℂ) :
    hermitianTranspose (hermitianTranspose P) = P := by
  apply HermitianMat.ext
  exact Matrix.transpose_transpose P.mat

/-- Hermitian transposition preserves positive semidefiniteness. -/
theorem hermitianTranspose_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {P : HermitianMat I ℂ} (hP : 0 ≤ P) : 0 ≤ hermitianTranspose P :=
  HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp hP).transpose

/-- Hermitian transposition preserves the real trace. -/
@[simp] theorem hermitianTranspose_trace {I : Type*} [Fintype I] (P : HermitianMat I ℂ) :
    (hermitianTranspose P).trace = P.trace := by
  simp only [HermitianMat.trace_eq_re_trace,hermitianTranspose,HermitianMat.mat_mk,
    Matrix.trace_transpose]

/-- For positive semidefinite matrices, Hermitian transposition commutes with the positive
square root. -/
theorem hermitianTranspose_sqrt {I : Type*} [Fintype I] [DecidableEq I]
    {P : HermitianMat I ℂ} (hP : 0 ≤ P) :
    (hermitianTranspose P).sqrt = hermitianTranspose P.sqrt := by
  have hs : (hermitianTranspose P.sqrt)^2 = hermitianTranspose P := by
    apply HermitianMat.ext
    simp only [HermitianMat.mat_pow,pow_two,hermitianTranspose,HermitianMat.mat_mk]
    rw [← Matrix.transpose_mul,HermitianMat.sqrt_sq hP]
  rw [← hs]
  exact sqrt_square_nonneg (hermitianTranspose_nonneg P.sqrt_nonneg)

/-- Simultaneous Hermitian transposition preserves the root fidelity of positive semidefinite
matrices. -/
theorem rootFidelity_transpose {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    rootFidelity (hermitianTranspose P) (hermitianTranspose Q) = rootFidelity P Q := by
  unfold rootFidelity
  rw [hermitianTranspose_sqrt hP,hermitianTranspose_sqrt hQ]
  change Matrix.traceNorm (P.sqrt.matᵀ * Q.sqrt.matᵀ) = _
  rw [← Matrix.transpose_mul,traceNorm_transpose]
  exact rootFidelity_reverse P Q

/-- The density input obtained by transposing its Hermitian matrix. -/
def densityTranspose {D : ℕ} (ρ : DensityInput D) : DensityInput D :=
  ⟨hermitianTranspose ρ.val,hermitianTranspose_nonneg ρ.property.1,
    (hermitianTranspose_trace ρ.val).trans ρ.property.2⟩

/-- Transposing a density input twice returns the original density input. -/
@[simp] theorem densityTranspose_involutive {D : ℕ} (ρ : DensityInput D) :
    densityTranspose (densityTranspose ρ) = ρ := by
  apply Subtype.ext
  exact hermitianTranspose_involutive ρ.val

/-- The Choi matrix of a Stinespring cross map factors as one Stinespring factor times the
conjugate transpose of the other. -/
theorem stinespringCross_choi {D E : ℕ} {Z : Type*} [Fintype Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    MatrixMap.choi_matrix (stinespringCross A B) = stinespringFactor A * (stinespringFactor B)ᴴ := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp [MatrixMap.choi_matrix,stinespringCross,stinespringFactor,Matrix.traceRight,
    Matrix.mul_apply,Matrix.single,Matrix.conjTranspose_apply,Finset.sum_mul,ite_and]

/-- A Stinespring frame equals its Stinespring factor multiplied on the left by the lifted
square root of the density input. -/
theorem stinespringFrame_eq_factor {D E : ℕ} {Z : Type*} [Fintype Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (ρ : DensityInput D) :
    stinespringFrame A ρ = Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat * stinespringFactor A := by
  ext ⟨a,r⟩ z
  simp [stinespringFrame,stinespringFactor,Matrix.mul_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Fintype.sum_prod_type,Matrix.one_apply,mul_comm]

/-- The Gram matrix of a Stinespring frame is the transpose of the complementary output on the
transposed density matrix. -/
theorem stinespringFrame_gram {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (ρ : DensityInput D) :
    frameGram (stinespringFrame A ρ) =
      hermitianTranspose (stinespringComplement A (hermitianTranspose ρ.val)) := by
  have hgram : frameGram (stinespringFrame A ρ) =
      (densityLift (E := E) ρ.val).conj (stinespringFactor A)ᴴ := by
    apply HermitianMat.ext
    rw [stinespringFrame_eq_factor]
    simp only [frameGram,HermitianMat.mat_mk,HermitianMat.conj_apply_mat,
      Matrix.conjTranspose_conjTranspose,densityLift,HermitianMat.kronecker_mat,HermitianMat.mat_one]
    change (Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat * stinespringFactor A)ᴴ *
      (Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat * stinespringFactor A) =
      (stinespringFactor A)ᴴ * Matrix.kronecker (1 : Operator E) ρ.val.mat * stinespringFactor A
    have hS : (Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat)ᴴ =
        Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat := (densityLift (E := E) ρ.val.sqrt).H.eq
    rw [Matrix.conjTranspose_mul,hS]
    calc
      _ = (stinespringFactor A)ᴴ *
          (Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat *
            Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat) * stinespringFactor A := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        dsimp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,HermitianMat.sqrt_sq ρ.property.1]
  rw [hgram]
  apply HermitianMat.ext
  ext z w
  simp only [HermitianMat.conj_apply_mat,hermitianTranspose,stinespringComplement,
    HermitianMat.mat_mk,HermitianMat.traceLeft_mat,Matrix.transpose_apply,
    Matrix.conjTranspose_conjTranspose]
  change (∑ q, (∑ p, star (stinespringFactor A p z) *
    Matrix.kronecker (1 : Operator E) ρ.val.mat p q) * stinespringFactor A q w) =
    ∑ a, (∑ j, (∑ i, A (a,w) i * ρ.val.mat j i) * star (A (a,z) j))
  simp only [stinespringFactor,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type,Matrix.one_apply,ite_mul,one_mul,zero_mul,mul_ite,mul_zero,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A Stinespring complementary map sends positive semidefinite matrices to positive
semidefinite matrices. -/
theorem stinespringComplement_nonneg {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) {ρ : HermitianMat (Fin D) ℂ} (hρ : 0 ≤ ρ) :
    0 ≤ stinespringComplement A ρ := by
  exact HermitianMat.zero_le_iff.mpr
      ((HermitianMat.zero_le_iff.mp hρ).mul_mul_conjTranspose_same A).traceLeft

/-- The Choi score of a Stinespring cross map equals the root fidelity of its complementary
outputs on transposed density inputs. -/
theorem stinespring_choiScore_fidelity {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (ρ σ : DensityInput D) :
    diamondChoiScore (stinespringCross A B) ρ σ =
      rootFidelity (stinespringComplement A (densityTranspose ρ).val)
        (stinespringComplement B (densityTranspose σ).val) := by
  have heq : Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat *
      MatrixMap.choi_matrix (stinespringCross A B) * Matrix.kronecker (1 : Operator E) σ.val.sqrt.mat =
      stinespringFrame A ρ * (stinespringFrame B σ)ᴴ := by
    rw [stinespringCross_choi,stinespringFrame_eq_factor,stinespringFrame_eq_factor]
    have hS : (Matrix.kronecker (1 : Operator E) σ.val.sqrt.mat)ᴴ =
        Matrix.kronecker (1 : Operator E) σ.val.sqrt.mat := (densityLift (E := E) σ.val.sqrt).H.eq
    simp only [Matrix.conjTranspose_mul,hS,Matrix.mul_assoc]
  unfold diamondChoiScore
  rw [heq,frame_cross_traceNorm,stinespringFrame_gram,stinespringFrame_gram]
  exact rootFidelity_transpose
    (stinespringComplement_nonneg A (densityTranspose ρ).property.1)
    (stinespringComplement_nonneg B (densityTranspose σ).property.1)

/-- The finite diamond norm of a Stinespring cross map equals the maximum output root fidelity;
see [Watrous2018]. -/
theorem finiteDiamondNorm_stinespring {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    finiteDiamondNorm (stinespringCross A B) = maxOutputRootFidelity A B := by
  rw [finiteDiamondNorm_eq_choi]
  unfold diamondChoiValue maxOutputRootFidelity
  apply le_antisymm
  · refine iSup_le fun ρ => iSup_le fun σ => ?_
    rw [stinespring_choiScore_fidelity]
    exact le_iSup_of_le (densityTranspose ρ) (le_iSup_of_le (densityTranspose σ) le_rfl)
  · refine iSup_le fun ρ => iSup_le fun σ => ?_
    have heq := stinespring_choiScore_fidelity A B (densityTranspose ρ) (densityTranspose σ)
    simp only [densityTranspose_involutive] at heq
    rw [← heq]
    exact le_iSup_of_le (densityTranspose ρ) (le_iSup_of_le (densityTranspose σ) le_rfl)

/-- For positive input dimension, two density inputs attain the maximum complementary output
root fidelity and the finite diamond norm. -/
theorem maxOutputRootFidelity_attained {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    ∃ ρ σ : DensityInput D,
      finiteDiamondNorm (stinespringCross A B) = ENNReal.ofReal
        (rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val)) ∧
      maxOutputRootFidelity A B = ENNReal.ofReal
        (rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val)) := by
  obtain ⟨ρ,σ,hnorm,-⟩ := diamondChoi_attained hD (stinespringCross A B)
  rw [stinespring_choiScore_fidelity] at hnorm
  exact ⟨densityTranspose ρ,densityTranspose σ,hnorm,
    (finiteDiamondNorm_stinespring A B).symm.trans hnorm⟩

/-- The cross map of the canonical left and right Stinespring data is the original linear map. -/
theorem canonicalStinespring_cross {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    stinespringCross (canonicalStinespringLeft T) (canonicalStinespringRight D E) = T := by
  apply MatrixMap.choi_matrix_inj
  rw [stinespringCross_choi]
  change MatrixMap.choi_matrix T * (1 : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ)ᴴ = _
  rw [Matrix.conjTranspose_one,Matrix.mul_one]

/-- The finite diamond norm equals the maximum output root fidelity for the canonical
Stinespring data. -/
theorem finiteDiamondNorm_canonical_maxOutputFidelity {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondNorm T = maxOutputRootFidelity (canonicalStinespringLeft T) (canonicalStinespringRight D E) := by
  have h :=
      finiteDiamondNorm_stinespring (canonicalStinespringLeft T) (canonicalStinespringRight D E)
  rwa [canonicalStinespring_cross] at h

/-- The linear Stinespring complementary map evaluates to `stinespringComplement`. -/
@[simp] theorem stinespringComplementLinear_apply {D E : ℕ} {Z : Type*}
    [Fintype Z] [DecidableEq Z] (A : Matrix (Fin E × Z) (Fin D) ℂ)
    (ρ : HermitianMat (Fin D) ℂ) :
    stinespringComplementLinear A ρ = stinespringComplement A ρ := rfl

/-- The Stinespring equality map records input traces and deviations of output diagonal blocks
from their complementary images. -/
theorem stinespringEqMap_apply {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (M : HermitianMat (StinespringRegister D Z) ℂ) :
    stinespringEqMap A B M = stinespringDualData
      (principalBlock (principalBlock M Sum.inl) Sum.inl).trace
      (principalBlock (principalBlock M Sum.inl) Sum.inr).trace
      (principalBlock (principalBlock M Sum.inr) Sum.inl -
        stinespringComplement A (principalBlock (principalBlock M Sum.inl) Sum.inl))
      (principalBlock (principalBlock M Sum.inr) Sum.inr -
        stinespringComplement B (principalBlock (principalBlock M Sum.inl) Sum.inr)) := rfl

/-- Pairing Stinespring adjoint data with a primal matrix equals pairing dual data with its
Stinespring equality image. -/
theorem stinespringAdjointData_inner {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (a b : ℝ) (Y W : HermitianMat Z ℂ)
    (M : HermitianMat (StinespringRegister D Z) ℂ) :
    ⟪stinespringAdjointData A B a b Y W,M⟫_ℝ =
      ⟪stinespringDualData a b Y W,stinespringEqMap A B M⟫_ℝ := by
  let ρ := principalBlock (principalBlock M Sum.inl) Sum.inl
  let σ := principalBlock (principalBlock M Sum.inl) Sum.inr
  let P := principalBlock (principalBlock M Sum.inr) Sum.inl
  let Q := principalBlock (principalBlock M Sum.inr) Sum.inr
  have hl : ⟪stinespringAdjointData A B a b Y W,M⟫_ℝ =
      a * ρ.trace - ⟪Y,stinespringComplement A ρ⟫_ℝ +
        (b * σ.trace - ⟪W,stinespringComplement B σ⟫_ℝ) + ⟪Y,P⟫_ℝ + ⟪W,Q⟫_ℝ := by
    unfold stinespringAdjointData
    rw [directSum_inner,blockDiagonal_inner_general,blockDiagonal_inner_general]
    simp only [inner_sub_left,real_inner_smul_left,HermitianMat.one_inner,
      ContinuousLinearMap.adjoint_inner_left,stinespringComplementLinear_apply]
    change a * ρ.trace - ⟪Y,stinespringComplement A ρ⟫_ℝ +
      (b * σ.trace - ⟪W,stinespringComplement B σ⟫_ℝ) + (⟪Y,P⟫_ℝ + ⟪W,Q⟫_ℝ) = _
    ring
  rw [hl,stinespringEqMap_apply]
  change _ = (ρ.trace * a + σ.trace * b) +
    (⟪Y,P - stinespringComplement A ρ⟫_ℝ + ⟪W,Q - stinespringComplement B σ⟫_ℝ)
  rw [inner_sub_right,inner_sub_right]
  ring

/-- The adjoint of the Stinespring equality map evaluates on dual data as
`stinespringAdjointData`. -/
@[simp] theorem stinespringEqMap_adjoint {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (a b : ℝ) (Y W : HermitianMat Z ℂ) :
    (stinespringEqMap A B).adjoint (stinespringDualData a b Y W) =
      stinespringAdjointData A B a b Y W := by
  apply ext_inner_right ℝ
  intro M
  rw [ContinuousLinearMap.adjoint_inner_left,stinespringAdjointData_inner]

/-- The Stinespring dual slack splits into two scalar adjoint slacks and the fidelity coupling
block. -/
theorem stinespringProgram_dual_slack {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (a b : ℝ) (Y W : HermitianMat Z ℂ) :
    (stinespringProgram A B).constraint.adjoint (stinespringDualData a b Y W) -
      (stinespringProgram A B).objective =
      directSum (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (a • 1 - (stinespringComplementLinear A).adjoint Y)
        (b • 1 - (stinespringComplementLinear B).adjoint W))
        (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y W - (1/2 : ℝ) • offDiagonal (1 : Matrix Z Z ℂ)) := by
  change (stinespringEqMap A B).adjoint _ - _ = _
  rw [stinespringEqMap_adjoint]
  apply HermitianMat.ext
  change Matrix.fromBlocks _ 0 0 _ - Matrix.fromBlocks 0 0 0 _ = Matrix.fromBlocks _ 0 0 _
  rw [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
  simp only [neg_zero,add_zero,sub_eq_add_neg,HermitianMat.mat_add,HermitianMat.mat_neg]

/-- The Stinespring program's dual score on `stinespringDualData a b Y W` is `a + b`. -/
@[simp] theorem stinespringProgram_dualScore {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (a b : ℝ) (Y W : HermitianMat Z ℂ) :
    (stinespringProgram A B).dualScore (stinespringDualData a b Y W) = a + b := by
  change ⟪stinespringDualData 1 1 0 0,stinespringDualData a b Y W⟫_ℝ = _
  simp [stinespringDualData,WithLp.prod_inner_apply]

/-- The Stinespring equality map sends primal block data to the two input traces and zero
residual blocks. -/
@[simp] theorem stinespringEqMap_primalData {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (ρ σ : HermitianMat (Fin D) ℂ) (X : Matrix Z Z ℂ) :
    stinespringEqMap A B (stinespringPrimalData A B ρ σ X) =
      stinespringDualData ρ.trace σ.trace 0 0 := by
  rw [stinespringEqMap_apply]
  change stinespringDualData ρ.trace σ.trace
    (stinespringComplement A ρ - stinespringComplement A ρ)
    (stinespringComplement B σ - stinespringComplement B σ) = _
  rw [sub_self,sub_self]

/-- Stinespring primal block data are feasible exactly when both inputs are density matrices and
their complementary fidelity block is positive semidefinite. -/
theorem stinespringProgram_primal_block_iff {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (ρ σ : HermitianMat (Fin D) ℂ) (X : Matrix Z Z ℂ) :
    (stinespringProgram A B).PrimalFeasible (stinespringPrimalData A B ρ σ X) ↔
      (0 ≤ ρ ∧ ρ.trace = 1) ∧ (0 ≤ σ ∧ σ.trace = 1) ∧
        (fidelityPrimalBlock (stinespringComplement A ρ) (stinespringComplement B σ) X).mat.PosSemidef := by
  change (0 ≤ stinespringPrimalData A B ρ σ X ∧
    stinespringEqMap A B (stinespringPrimalData A B ρ σ X) = stinespringDualData 1 1 0 0) ↔ _
  rw [stinespringEqMap_primalData]
  have heq : stinespringDualData (Z := Z) ρ.trace σ.trace 0 0 = stinespringDualData 1 1 0 0 ↔
      ρ.trace = 1 ∧ σ.trace = 1 := by
    unfold stinespringDualData
    rw [(WithLp.toLp_injective 2).eq_iff,Prod.mk.injEq,
      (WithLp.toLp_injective 2).eq_iff,Prod.mk.injEq]
    simp only [and_true]
  rw [heq]
  unfold stinespringPrimalData
  rw [directSum_nonneg_iff,blockDiagonal_nonneg_iff]
  simp only [HermitianMat.zero_le_iff]
  tauto

/-- The Stinespring primal score on block data is the real part of the trace of the cross block. -/
theorem stinespringProgram_primalScore {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (ρ σ : HermitianMat (Fin D) ℂ) (X : Matrix Z Z ℂ) :
    (stinespringProgram A B).primalScore (stinespringPrimalData A B ρ σ X) = (Matrix.trace X).re := by
  change ⟪directSum 0 ((1/2 : ℝ) • offDiagonal (1 : Matrix Z Z ℂ)),
    directSum (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal ρ σ)
      (fidelityPrimalBlock (stinespringComplement A ρ) (stinespringComplement B σ) X)⟫_ℝ = _
  rw [directSum_inner,principalBlock_directSum_left,principalBlock_directSum_right,inner_zero_left,zero_add]
  exact fidelityProgram_primalScore _ _ _

/-- The identity minus half the off-diagonal identity block is positive definite. -/
theorem fidelity_identity_slack_posDef {I : Type*} [Fintype I] [DecidableEq I] :
    ((1 : HermitianMat (I ⊕ I) ℂ) - (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ)).mat.PosDef := by
  have hg : (Matrix.fromBlocks (1 : Matrix I I ℂ) (-1 : Matrix I I ℂ)
      (-1 : Matrix I I ℂ) (1 : Matrix I I ℂ)).PosSemidef := by
    simpa using! Matrix.fromBlocks_gram_posSemidef (-1 : Matrix I I ℂ) (1 : Matrix I I ℂ)
  have heq : ((1 : HermitianMat (I ⊕ I) ℂ) -
      (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ)).mat =
      (1/2 : ℝ) • (1 : Matrix (I ⊕ I) (I ⊕ I) ℂ) +
        (1/2 : ℝ) • Matrix.fromBlocks (1 : Matrix I I ℂ) (-1 : Matrix I I ℂ)
          (-1 : Matrix I I ℂ) (1 : Matrix I I ℂ) := by
    simp only [HermitianMat.mat_sub,HermitianMat.mat_smul,HermitianMat.mat_one,
      offDiagonal,HermitianMat.mat_mk,Matrix.conjTranspose_one]
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]
    all_goals split_ifs <;> norm_num
  rw [heq]
  exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1/2)).add_posSemidef
    (hg.smul (by norm_num : (0 : ℝ) ≤ 1/2))

/-- The Stinespring program satisfies dual Slater feasibility. -/
theorem stinespringProgram_dual_strict {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : (stinespringProgram A B).DualSlater := by
  let P := (stinespringComplementLinear A).adjoint 1
  let Q := (stinespringComplementLinear B).adjoint 1
  refine ⟨stinespringDualData (‖P‖+1) (‖Q‖+1) (1 : HermitianMat Z ℂ) 1,?_⟩
  rw [stinespringProgram_dual_slack]
  have hdiag : Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (1 : HermitianMat Z ℂ) 1 = 1 := by
    apply HermitianMat.ext
    exact Matrix.fromBlocks_one
  rw [hdiag]
  exact directSum_posDef (directSum_posDef (scalar_majorant_posDef P) (scalar_majorant_posDef Q))
    fidelity_identity_slack_posDef

/-- A fidelity primal block with zero cross block is the block diagonal matrix of its two
inputs. -/
@[simp] theorem fidelityPrimalBlock_zero {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ) :
    fidelityPrimalBlock P Q 0 = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q := by
  apply HermitianMat.ext
  simp only [fidelityPrimalBlock,Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal,HermitianMat.mat_mk,Matrix.conjTranspose_zero]

/-- The Stinespring program has a primal feasible point when the input dimension is positive. -/
theorem stinespringProgram_primal_feasible {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    ∃ M, (stinespringProgram A B).PrimalFeasible M := by
  let ρ : HermitianMat (Fin D) ℂ := (D : ℝ)⁻¹ • 1
  have hp : 0 ≤ ρ := smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one)
  have ht : ρ.trace = 1 := by
    simp only [ρ,HermitianMat.trace_smul,HermitianMat.trace_one,Fintype.card_fin]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD))
  refine ⟨stinespringPrimalData A B ρ ρ 0,
    (stinespringProgram_primal_block_iff A B ρ ρ 0).mpr ⟨⟨hp,ht⟩,⟨hp,ht⟩,?_⟩⟩
  rw [fidelityPrimalBlock_zero]
  exact HermitianMat.zero_le_iff.mp (blockDiagonal_nonneg
    (stinespringComplement_nonneg A hp) (stinespringComplement_nonneg B hp))

/-- Every Stinespring primal feasible matrix yields density inputs and a positive semidefinite
complementary fidelity block with the same score. -/
theorem stinespringProgram_primal_reduction {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) {M : HermitianMat (StinespringRegister D Z) ℂ}
    (hM : (stinespringProgram A B).PrimalFeasible M) :
    ∃ (ρ σ : DensityInput D) (X : Matrix Z Z ℂ),
      (fidelityPrimalBlock (stinespringComplement A ρ.val) (stinespringComplement B σ.val) X).mat.PosSemidef ∧
        (stinespringProgram A B).primalScore M = (Matrix.trace X).re := by
  let R := principalBlock M Sum.inl
  let S := principalBlock M Sum.inr
  let ρ := principalBlock R Sum.inl
  let σ := principalBlock R Sum.inr
  let P := principalBlock S Sum.inl
  let Q := principalBlock S Sum.inr
  have hρ : 0 ≤ ρ := principalBlock_nonneg (principalBlock_nonneg hM.1 Sum.inl) Sum.inl
  have hσ : 0 ≤ σ := principalBlock_nonneg (principalBlock_nonneg hM.1 Sum.inl) Sum.inr
  have heq : stinespringDualData ρ.trace σ.trace
      (P - stinespringComplement A ρ) (Q - stinespringComplement B σ) =
      stinespringDualData 1 1 0 0 := by
    have he := hM.2
    change stinespringEqMap A B M = _ at he
    rw [stinespringEqMap_apply] at he
    exact he
  unfold stinespringDualData at heq
  rw [(WithLp.toLp_injective 2).eq_iff,Prod.mk.injEq] at heq
  have htr := (WithLp.toLp_injective 2) heq.1
  have hres := (WithLp.toLp_injective 2) heq.2
  have hρtr : ρ.trace = 1 := congrArg Prod.fst htr
  have hσtr : σ.trace = 1 := congrArg Prod.snd htr
  have hP : P = stinespringComplement A ρ := sub_eq_zero.mp (congrArg Prod.fst hres)
  have hQ : Q = stinespringComplement B σ := sub_eq_zero.mp (congrArg Prod.snd hres)
  have hpinch : blockPinch S = Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (stinespringComplement A ρ) (stinespringComplement B σ) := by
    rw [← hP,← hQ]
    apply HermitianMat.ext
    ext i j
    cases i <;> cases j <;> rfl
  have hS : (fidelityProgram (stinespringComplement A ρ) (stinespringComplement B σ)).PrimalFeasible S :=
    ⟨principalBlock_nonneg hM.1 Sum.inr,hpinch⟩
  obtain ⟨X,hX⟩ := fidelityProgram_primal_shape hS
  refine ⟨⟨ρ,hρ,hρtr⟩,⟨σ,hσ,hσtr⟩,X,?_,?_⟩
  · simpa only [hX,HermitianMat.zero_le_iff] using! hS.1
  · change ⟪directSum 0 ((1/2 : ℝ) • offDiagonal (1 : Matrix Z Z ℂ)),M⟫_ℝ = _
    rw [directSum_inner,inner_zero_left,zero_add]
    change (fidelityProgram (stinespringComplement A ρ) (stinespringComplement B σ)).primalScore S = _
    rw [hX,fidelityProgram_primalScore]

/-- The Stinespring program's primal value set equals `stinespringSourcePrimalValues`. -/
theorem stinespringProgram_primalValues_eq_source {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    (stinespringProgram A B).primalValues = stinespringSourcePrimalValues A B := by
  ext a
  constructor
  · rintro ⟨M,hM,rfl⟩
    obtain ⟨ρ,σ,X,hX,hs⟩ := stinespringProgram_primal_reduction A B hM
    exact ⟨ρ,σ,X,hX,hs.symm⟩
  · rintro ⟨ρ,σ,X,hX,hs⟩
    refine ⟨stinespringPrimalData A B ρ.val σ.val X,
      (stinespringProgram_primal_block_iff A B ρ.val σ.val X).mpr ⟨ρ.property,σ.property,hX⟩,?_⟩
    rw [stinespringProgram_primalScore]
    exact hs

/-- For positive input dimension, the Stinespring program has a common primal supremum and dual
infimum equal to the finite diamond norm, with primal attainment. -/
theorem stinespringProgram_norm_strong_duality {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    ∃ (α : ℝ) (M : HermitianMat (StinespringRegister D Z) ℂ),
      finiteDiamondNorm (stinespringCross A B) = ENNReal.ofReal α ∧
      (stinespringProgram A B).PrimalFeasible M ∧
      IsLUB (stinespringProgram A B).primalValues α ∧ IsGLB (stinespringProgram A B).dualValues α ∧
      (stinespringProgram A B).primalScore M = α := by
  obtain ⟨M₀,hM₀⟩ := stinespringProgram_primal_feasible hD A B
  obtain ⟨α,hp,hd,M,hM,hscore⟩ := (Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlater_strong_duality (P := (stinespringProgram A B)))
    (stinespringProgram_dual_strict A B) hM₀
  have hUpper (ρ σ : DensityInput D) :
      rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val) ≤ α := by
    obtain ⟨X,hX,hs⟩ := rootFidelity_block_attained
      (stinespringComplement_nonneg A ρ.property.1) (stinespringComplement_nonneg B σ.property.1)
    apply hp.1
    refine ⟨stinespringPrimalData A B ρ.val σ.val X,
      (stinespringProgram_primal_block_iff A B ρ.val σ.val X).mpr ⟨ρ.property,σ.property,hX⟩,?_⟩
    rw [stinespringProgram_primalScore]
    exact hs
  obtain ⟨ρ,σ,X,hX,hs⟩ := stinespringProgram_primal_reduction A B hM
  have hLower : α ≤ rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val) := by
    rw [← hscore,hs]
    exact fidelity_block_score_le_rootFidelity
      (stinespringComplement_nonneg A ρ.property.1) (stinespringComplement_nonneg B σ.property.1) hX
  have heq := le_antisymm (hUpper ρ σ) hLower
  refine ⟨α,M,?_,hM,hp,hd,hscore⟩
  rw [finiteDiamondNorm_stinespring]
  unfold maxOutputRootFidelity
  apply le_antisymm
  · exact iSup_le fun ρ => iSup_le fun σ => ENNReal.ofReal_le_ofReal (hUpper ρ σ)
  · rw [← heq]
    exact le_iSup_of_le ρ (le_iSup_of_le σ le_rfl)

/-- For positive input dimension, density inputs and a complementary cross block attain the
finite diamond norm and the source primal supremum. -/
theorem stinespringSource_norm_primal_attained {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    ∃ (α : ℝ) (ρ σ : DensityInput D) (X : Matrix Z Z ℂ),
      finiteDiamondNorm (stinespringCross A B) = ENNReal.ofReal α ∧
      (fidelityPrimalBlock (stinespringComplement A ρ.val) (stinespringComplement B σ.val) X).mat.PosSemidef ∧
      IsLUB (stinespringSourcePrimalValues A B) α ∧ IsGLB (stinespringProgram A B).dualValues α ∧
      (Matrix.trace X).re = α := by
  obtain ⟨α,M,hnorm,hM,hp,hd,hscore⟩ := stinespringProgram_norm_strong_duality hD A B
  obtain ⟨ρ,σ,X,hX,hs⟩ := stinespringProgram_primal_reduction A B hM
  rw [stinespringProgram_primalValues_eq_source] at hp
  exact ⟨α,ρ,σ,X,hnorm,hX,hp,hd,hs.symm.trans hscore⟩

/-- The adjoint of the Stinespring complementary map is conjugation of the lifted environment
matrix by the conjugate transpose of the Stinespring matrix. -/
theorem stinespringComplementLinear_adjoint {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (Y : HermitianMat Z ℂ) :
    (stinespringComplementLinear A).adjoint Y =
      (HermitianMat.kronecker (1 : HermitianMat (Fin E) ℂ) Y).conj Aᴴ := by
  apply ext_inner_right ℝ
  intro ρ
  rw [ContinuousLinearMap.adjoint_inner_left,stinespringComplementLinear_apply,
    real_inner_comm (stinespringComplement A ρ) Y]
  simp only [inner_eq_real_trace,stinespringComplement,HermitianMat.traceLeft_mat,
    HermitianMat.conj_apply_mat,HermitianMat.kronecker_mat,HermitianMat.mat_one,
    Matrix.conjTranspose_conjTranspose]
  apply congrArg Complex.re
  calc
    _ = Matrix.trace ((A * ρ.mat * Aᴴ) * Matrix.kronecker (1 : Operator E) Y.mat) :=
      (Matrix.trace_mul_one_kron_right (A * ρ.mat * Aᴴ) Y.mat).symm
    _ = Matrix.trace ((Aᴴ * Matrix.kronecker (1 : Operator E) Y.mat * A) * ρ.mat) := by
      have h := Matrix.trace_mul_cycle Aᴴ (Matrix.kronecker (1 : Operator E) Y.mat) (A * ρ.mat)
      simpa only [Matrix.mul_assoc] using! h.symm

/-- Positive semidefiniteness of a fidelity dual block forces its left diagonal block to be
positive definite. -/
theorem fidelityDualBlock_left_posDef {I : Type*} [Fintype I] [DecidableEq I]
    {Y W : HermitianMat I ℂ} (h : 0 ≤ fidelityDualBlock Y W) : Y.mat.PosDef := by
  have hdiag := weightedDualBlock_diagonal_nonneg (C := (1 : Matrix I I ℂ)) h
  have hraw : (Matrix.fromBlocks Y.mat (-1 : Matrix I I ℂ) (-1 : Matrix I I ℂ) W.mat).PosSemidef := by
    have hm := HermitianMat.zero_le_iff.mp h
    simp only [fidelityDualBlock,HermitianMat.mat_sub,Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal,offDiagonal,
      HermitianMat.mat_mk,Matrix.conjTranspose_one] at hm
    rw [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add] at hm
    simpa only [neg_zero,add_zero,zero_add] using! hm
  have hs := fidelity_cross_left_support (X := (-1 : Matrix I I ℂ)) (by simpa using! hraw)
  have hproj : Y.supportProj = 1 := by
    apply HermitianMat.ext
    simpa only [Matrix.mul_neg,Matrix.mul_one,neg_inj,HermitianMat.mat_one] using! hs
  have hk : Y.ker = ⊥ := by
    rw [← Y.supportProj_ker,hproj]
    exact HermitianMat.nonSingular_ker_bot (A := (1 : HermitianMat I ℂ))
  exact (Y.nonSingular_iff_posDef_of_PSD hdiag.1).mp ((Y.nonSingular_iff_ker_bot).mpr hk)

/-- A fidelity dual block is positive semidefinite exactly when its left block is positive
definite and its right block dominates the inverse left block. -/
theorem fidelityDualBlock_iff_inverse_slack {I : Type*} [Fintype I] [DecidableEq I]
    (Y W : HermitianMat I ℂ) :
    0 ≤ fidelityDualBlock Y W ↔ Y.mat.PosDef ∧ 0 ≤ W - Y⁻¹ := by
  have hform : (fidelityDualBlock Y W).mat =
      Matrix.fromBlocks Y.mat (-1 : Matrix I I ℂ) (-1 : Matrix I I ℂ) W.mat := by
    simp only [fidelityDualBlock,HermitianMat.mat_sub,Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal,offDiagonal,
      HermitianMat.mat_mk,Matrix.conjTranspose_one]
    rw [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
    simp only [neg_zero,add_zero,zero_add]
  constructor
  · intro h
    have hp := fidelityDualBlock_left_posDef h
    letI : Invertible Y.mat := hp.isUnit.invertible
    have hs := (Matrix.PosDef.fromBlocks₁₁ (-1 : Matrix I I ℂ) W.mat hp).mp
      (by simpa only [Matrix.conjTranspose_neg,Matrix.conjTranspose_one,hform]
        using! HermitianMat.zero_le_iff.mp h)
    refine ⟨hp,HermitianMat.zero_le_iff.mpr ?_⟩
    simpa only [Matrix.conjTranspose_neg,Matrix.conjTranspose_one,Matrix.neg_mul,
      Matrix.mul_neg,Matrix.one_mul,Matrix.mul_one,neg_neg,HermitianMat.mat_sub,HermitianMat.mat_inv] using! hs
  · rintro ⟨hp,hs⟩
    letI : Invertible Y.mat := hp.isUnit.invertible
    apply HermitianMat.zero_le_iff.mpr
    rw [hform]
    have hm := (Matrix.PosDef.fromBlocks₁₁ (-1 : Matrix I I ℂ) W.mat hp).mpr (by
      simpa only [Matrix.conjTranspose_neg,Matrix.conjTranspose_one,Matrix.neg_mul,
        Matrix.mul_neg,Matrix.one_mul,Matrix.mul_one,neg_neg,HermitianMat.mat_sub,HermitianMat.mat_inv]
        using! HermitianMat.zero_le_iff.mp hs)
    simpa only [Matrix.conjTranspose_neg,Matrix.conjTranspose_one] using! hm

/-- The adjoint of a Stinespring complementary map preserves positive semidefiniteness. -/
theorem stinespringComplement_adjoint_nonneg {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) {Y : HermitianMat Z ℂ} (hY : 0 ≤ Y) :
    0 ≤ (stinespringComplementLinear A).adjoint Y := by
  rw [stinespringComplementLinear_adjoint]
  exact HermitianMat.conj_nonneg Aᴴ (HermitianMat.kronecker_nonneg
    (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one) hY)

/-- Stinespring dual feasibility is equivalent to positive semidefiniteness of the two scalar
adjoint slacks and the fidelity coupling block. -/
theorem stinespringProgram_dual_block_iff {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (a b : ℝ) (Y W : HermitianMat Z ℂ) :
    (stinespringProgram A B).DualFeasible (stinespringDualData a b Y W) ↔
      0 ≤ a • 1 - (stinespringComplementLinear A).adjoint Y ∧
      0 ≤ b • 1 - (stinespringComplementLinear B).adjoint W ∧
      0 ≤ Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y W - (1/2 : ℝ) • offDiagonal (1 : Matrix Z Z ℂ) := by
  unfold Program.DualFeasible
  rw [stinespringProgram_dual_slack,directSum_nonneg_iff,blockDiagonal_nonneg_iff,and_assoc]

section StinespringNormDual
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable local instance stinespringMatrixCStar {J : Type*} [Fintype J] [DecidableEq J] :
    CStarAlgebra (Matrix J J ℂ) where

/-- The operator norm is monotone between Hermitian matrices when the smaller matrix is positive
semidefinite. -/
theorem hermitian_opNorm_mono {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hPQ : P ≤ Q) : ‖P.mat‖ ≤ ‖Q.mat‖ := by
  have hm := Matrix.nonneg_iff_posSemidef.mpr (HermitianMat.zero_le_iff.mp (sub_nonneg.mpr hPQ))
  have hle : P.mat ≤ Q.mat := by simpa only [HermitianMat.mat_sub,sub_nonneg] using! hm
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
    (Matrix.nonneg_iff_posSemidef.mpr (HermitianMat.zero_le_iff.mp hP))

/-- A positive semidefinite fidelity dual block lifts to Stinespring dual feasible data with
score equal to `stinespringBlockDualObjective`. -/
theorem stinespringBlockDual_lift {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) {Y W : HermitianMat Z ℂ}
    (h : 0 ≤ fidelityDualBlock Y W) :
    (stinespringProgram A B).DualFeasible (stinespringDualData
      ((1/2 : ℝ) * ‖((stinespringComplementLinear A).adjoint Y).mat‖)
      ((1/2 : ℝ) * ‖((stinespringComplementLinear B).adjoint W).mat‖)
      ((1/2 : ℝ) • Y) ((1/2 : ℝ) • W)) ∧
    (stinespringProgram A B).dualScore (stinespringDualData
      ((1/2 : ℝ) * ‖((stinespringComplementLinear A).adjoint Y).mat‖)
      ((1/2 : ℝ) * ‖((stinespringComplementLinear B).adjoint W).mat‖)
      ((1/2 : ℝ) • Y) ((1/2 : ℝ) • W)) = stinespringBlockDualObjective A B Y W := by
  obtain ⟨hY,hW⟩ := weightedDualBlock_diagonal_nonneg (C := (1 : Matrix Z Z ℂ)) h
  have hy := stinespringComplement_adjoint_nonneg A hY
  have hw := stinespringComplement_adjoint_nonneg B hW
  refine ⟨(stinespringProgram_dual_block_iff _ _ _ _ _ _).mpr ⟨?_,?_,?_⟩,?_⟩
  · rw [map_smul]
    change 0 ≤ ((1/2 : ℝ) * ‖((stinespringComplementLinear A).adjoint Y).mat‖) • 1 -
      (1/2 : ℝ) • (stinespringComplementLinear A).adjoint Y
    have heq : ((1/2 : ℝ) * ‖((stinespringComplementLinear A).adjoint Y).mat‖) •
        (1 : HermitianMat (Fin D) ℂ) - (1/2 : ℝ) • (stinespringComplementLinear A).adjoint Y =
        (1/2 : ℝ) • (‖((stinespringComplementLinear A).adjoint Y).mat‖ • 1 -
          (stinespringComplementLinear A).adjoint Y) := by module
    rw [heq]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (nonneg_opNorm_slack hy)
  · rw [map_smul]
    change 0 ≤ ((1/2 : ℝ) * ‖((stinespringComplementLinear B).adjoint W).mat‖) • 1 -
      (1/2 : ℝ) • (stinespringComplementLinear B).adjoint W
    have heq : ((1/2 : ℝ) * ‖((stinespringComplementLinear B).adjoint W).mat‖) •
        (1 : HermitianMat (Fin D) ℂ) - (1/2 : ℝ) • (stinespringComplementLinear B).adjoint W =
        (1/2 : ℝ) • (‖((stinespringComplementLinear B).adjoint W).mat‖ • 1 -
          (stinespringComplementLinear B).adjoint W) := by module
    rw [heq]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (nonneg_opNorm_slack hw)
  · rw [diamond_half_dual_block]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) h
  · rw [stinespringProgram_dualScore]
    rfl

/-- For positive input dimension, every Stinespring dual feasible point reduces to a fidelity
dual block with no larger objective. -/
theorem stinespringProgram_dual_reduction {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) {y : StinespringConstraints Z}
    (hy : (stinespringProgram A B).DualFeasible y) :
    ∃ Y W : HermitianMat Z ℂ, 0 ≤ fidelityDualBlock Y W ∧
      stinespringBlockDualObjective A B Y W ≤ (stinespringProgram A B).dualScore y := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  let a := (WithLp.ofLp (WithLp.ofLp y).1).1
  let b := (WithLp.ofLp (WithLp.ofLp y).1).2
  let Y := (WithLp.ofLp (WithLp.ofLp y).2).1
  let W := (WithLp.ofLp (WithLp.ofLp y).2).2
  have heq : y = stinespringDualData a b Y W := rfl
  rw [heq] at hy ⊢
  obtain ⟨ha,hb,hblock⟩ := (stinespringProgram_dual_block_iff A B a b Y W).mp hy
  have hd : 0 ≤ fidelityDualBlock ((2 : ℝ) • Y) ((2 : ℝ) • W) := by
    change 0 ≤ weightedDualBlock (1 : Matrix Z Z ℂ) ((2 : ℝ) • Y) ((2 : ℝ) • W)
    rw [diamond_double_dual_block]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hblock
  obtain ⟨hY,hW⟩ := weightedDualBlock_diagonal_nonneg (C := (1 : Matrix Z Z ℂ)) hd
  have hy0 : 0 ≤ Y := by
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hY
    simpa only [smul_smul,show (1/2 : ℝ) * 2 = 1 by norm_num,one_smul] using! hh
  have hw0 : 0 ≤ W := by
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hW
    simpa only [smul_smul,show (1/2 : ℝ) * 2 = 1 by norm_num,one_smul] using! hh
  have hAnorm := opNorm_le_of_nonneg_scalar_slack (stinespringComplement_adjoint_nonneg A hy0) ha
  have hBnorm := opNorm_le_of_nonneg_scalar_slack (stinespringComplement_adjoint_nonneg B hw0) hb
  refine ⟨(2 : ℝ) • Y,(2 : ℝ) • W,hd,?_⟩
  rw [stinespringProgram_dualScore]
  unfold stinespringBlockDualObjective
  simp only [map_smul,HermitianMat.mat_smul,norm_smul,
    Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- For a positive semidefinite fidelity dual block, the left block is positive definite and
replacing the right block by its inverse cannot increase the objective. -/
theorem stinespringBlockDual_to_inverse {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) {Y W : HermitianMat Z ℂ}
    (h : 0 ≤ fidelityDualBlock Y W) :
    Y.mat.PosDef ∧ stinespringBlockDualObjective A B Y Y⁻¹ ≤ stinespringBlockDualObjective A B Y W := by
  obtain ⟨hp,hslack⟩ := (fidelityDualBlock_iff_inverse_slack Y W).mp h
  have hi : 0 ≤ fidelityDualBlock Y Y⁻¹ :=
    (fidelityDualBlock_iff_inverse_slack Y Y⁻¹).mpr ⟨hp,by rw [sub_self]⟩
  have hInv := (weightedDualBlock_diagonal_nonneg (C := (1 : Matrix Z Z ℂ)) hi).2
  have hmono : (stinespringComplementLinear B).adjoint Y⁻¹ ≤
      (stinespringComplementLinear B).adjoint W := by
    apply sub_nonneg.mp
    rw [← map_sub]
    exact stinespringComplement_adjoint_nonneg B hslack
  have hn := hermitian_opNorm_mono (stinespringComplement_adjoint_nonneg B hInv) hmono
  refine ⟨hp,?_⟩
  unfold stinespringBlockDualObjective
  linarith

end StinespringNormDual

/-- For positive input dimension, the Stinespring source primal supremum and both block and
inverse dual infima equal the finite diamond norm, with primal attainment. -/
theorem stinespringSource_norm_duality {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    ∃ (α : ℝ) (ρ σ : DensityInput D) (X : Matrix Z Z ℂ),
      finiteDiamondNorm (stinespringCross A B) = ENNReal.ofReal α ∧
      (fidelityPrimalBlock (stinespringComplement A ρ.val) (stinespringComplement B σ.val) X).mat.PosSemidef ∧
      IsLUB (stinespringSourcePrimalValues A B) α ∧ IsGLB (stinespringBlockDualValues A B) α ∧
      IsGLB (stinespringInverseDualValues A B) α ∧ (Matrix.trace X).re = α := by
  obtain ⟨α,M,hnorm,hM,hp,hd,hscore⟩ := stinespringProgram_norm_strong_duality hD A B
  have hblockGLB : IsGLB (stinespringBlockDualValues A B) α := by
    refine ⟨?_,?_⟩
    · rintro a ⟨Y,W,h,rfl⟩
      have hw :=
          (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality (P := (stinespringProgram A B))) hM (stinespringBlockDual_lift A B h).1
      rwa [hscore,(stinespringBlockDual_lift A B h).2] at hw
    · intro b hb
      apply hd.2
      rintro a ⟨y,hy,rfl⟩
      obtain ⟨Y,W,h,hbound⟩ := stinespringProgram_dual_reduction hD A B hy
      exact (hb ⟨Y,W,h,rfl⟩).trans hbound
  have hInvGLB : IsGLB (stinespringInverseDualValues A B) α := by
    refine ⟨?_,?_⟩
    · rintro a ⟨Y,hY,rfl⟩
      apply hblockGLB.1
      exact ⟨Y,Y⁻¹,(fidelityDualBlock_iff_inverse_slack Y Y⁻¹).mpr ⟨hY,by simp⟩,rfl⟩
    · intro b hb
      apply hblockGLB.2
      rintro a ⟨Y,W,h,rfl⟩
      obtain ⟨hY,hbound⟩ := stinespringBlockDual_to_inverse A B h
      exact (hb ⟨Y,hY,rfl⟩).trans hbound
  obtain ⟨ρ,σ,X,hX,hs⟩ := stinespringProgram_primal_reduction A B hM
  rw [stinespringProgram_primalValues_eq_source] at hp
  exact ⟨α,ρ,σ,X,hnorm,hX,hp,hblockGLB,hInvGLB,hs.symm.trans hscore⟩

/-- For positive input dimension, positive definite inverse dual points approximate the finite
diamond norm from above to every positive tolerance. -/
theorem stinespringInverseDual_approximation {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    ∃ α : ℝ, finiteDiamondNorm (stinespringCross A B) = ENNReal.ofReal α ∧
      IsGLB (stinespringInverseDualValues A B) α ∧
      ∀ ε : ℝ, 0 < ε → ∃ Y : HermitianMat Z ℂ, Y.mat.PosDef ∧
        α ≤ stinespringBlockDualObjective A B Y Y⁻¹ ∧
        stinespringBlockDualObjective A B Y Y⁻¹ < α + ε := by
  obtain ⟨α,ρ,σ,X,hnorm,hX,hp,hblock,hi,hscore⟩ := stinespringSource_norm_duality hD A B
  refine ⟨α,hnorm,hi,fun ε hε => ?_⟩
  obtain ⟨v,⟨Y,hY,hs⟩,hlo,hnear⟩ := hi.exists_between (lt_add_of_pos_right α hε)
  rw [← hs] at hlo hnear
  exact ⟨Y,hY,hlo,hnear⟩

section SdpInteriorRadius
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable local instance interiorMatrixCStar {J : Type*} [Fintype J] [DecidableEq J] :
    CStarAlgebra (Matrix J J ℂ) where

/-- The order on Hermitian matrices agrees with the order on their underlying matrices. -/
theorem hermitian_le_iff_mat_le {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : P ≤ Q ↔ P.mat ≤ Q.mat := by
  rw [HermitianMat.le_iff,HermitianMat.mat_sub,← Matrix.nonneg_iff_posSemidef,sub_nonneg]

/-- The operator norm of the underlying matrix is bounded by the Hermitian matrix norm. -/
theorem hermitian_opNorm_le_norm {I : Type*} [Fintype I] [DecidableEq I]
    (H : HermitianMat I ℂ) : ‖H.mat‖ ≤ ‖H‖ := by
  have hh : ‖cfc (fun x : ℝ => x) H.mat‖ ≤ ‖H‖ :=
    norm_cfc_le (norm_nonneg H) fun x hx => by
      rw [H.H.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i,rfl⟩ := hx
      simpa only [Real.norm_eq_abs] using! H.eigenvalue_norm_le i
  have hid : cfc (fun x : ℝ => x) H.mat = H.mat := cfc_id' ℝ H.mat H.H
  rw [hid] at hh
  exact hh

/-- Every Hermitian matrix is bounded above by its operator norm times the identity. -/
theorem hermitian_le_opNorm_smul_one {I : Type*} [Fintype I] [DecidableEq I]
    (H : HermitianMat I ℂ) : H ≤ ‖H.mat‖ • (1 : HermitianMat I ℂ) := by
  apply (hermitian_le_iff_mat_le _ _).mpr
  simp only [HermitianMat.mat_smul,HermitianMat.mat_one,← Algebra.algebraMap_eq_smul_one]
  exact H.H.isSelfAdjoint.le_algebraMap_norm_self

/-- Every Hermitian matrix is bounded below by the negative of its operator norm times the
identity. -/
theorem hermitian_neg_opNorm_smul_one_le {I : Type*} [Fintype I] [DecidableEq I]
    (H : HermitianMat I ℂ) : (-‖H.mat‖) • (1 : HermitianMat I ℂ) ≤ H := by
  have hh := neg_le_neg (hermitian_le_opNorm_smul_one (-H))
  simpa only [HermitianMat.mat_neg,norm_neg,neg_smul,neg_neg] using! hh

/-- Two-sided scalar identity bounds of radius `r` bound the operator norm by `r`. -/
theorem hermitian_opNorm_le_of_bounds {I : Type*} [Fintype I] [DecidableEq I]
    {H : HermitianMat I ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hlo : (-r) • (1 : HermitianMat I ℂ) ≤ H) (hhi : H ≤ r • 1) : ‖H.mat‖ ≤ r := by
  have hml := (hermitian_le_iff_mat_le _ _).mp hlo
  have hmu := (hermitian_le_iff_mat_le _ _).mp hhi
  rw [HermitianMat.mat_smul,HermitianMat.mat_one,← Algebra.algebraMap_eq_smul_one] at hml hmu
  have hsl := (algebraMap_le_iff_le_spectrum (R := ℝ) H.H).mp hml
  have hsu := (le_algebraMap_iff_spectrum_le (R := ℝ) H.H).mp hmu
  have hh : ‖cfc (fun x : ℝ => x) H.mat‖ ≤ r := norm_cfc_le hr fun x hx => by
    simpa only [Real.norm_eq_abs] using! abs_le.mpr ⟨hsl x hx,hsu x hx⟩
  have hid : cfc (fun x : ℝ => x) H.mat = H.mat := cfc_id' ℝ H.mat H.H
  rw [hid] at hh
  exact hh

/-- The adjoint of a Stinespring complementary map is monotone. -/
theorem stinespringAdjoint_mono {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) {Y W : HermitianMat Z ℂ} (h : Y ≤ W) :
    (stinespringComplementLinear A).adjoint Y ≤ (stinespringComplementLinear A).adjoint W := by
  apply sub_nonneg.mp
  rw [← map_sub]
  exact stinespringComplement_adjoint_nonneg A (sub_nonneg.mpr h)

/-- The Stinespring complementary adjoint is bounded above by the product of the input operator
norm and its identity-image operator norm, times the identity. -/
theorem stinespringAdjoint_upper_bound {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (Y : HermitianMat Z ℂ) :
    (stinespringComplementLinear A).adjoint Y ≤
      (‖Y.mat‖ * ‖((stinespringComplementLinear A).adjoint 1).mat‖) • 1 := by
  have h₀ := stinespringAdjoint_mono A (hermitian_le_opNorm_smul_one Y)
  rw [map_smul] at h₀
  calc
    _ ≤ ‖Y.mat‖ • (stinespringComplementLinear A).adjoint 1 := h₀
    _ ≤ ‖Y.mat‖ • (‖((stinespringComplementLinear A).adjoint 1).mat‖ • 1) :=
      smul_le_smul_of_nonneg_left (hermitian_le_opNorm_smul_one _) (norm_nonneg _)
    _ = _ := by rw [smul_smul]

/-- Subtraction of direct sums equals the direct sum of the respective differences. -/
theorem directSum_sub {I J : Type*} [Fintype I] [Fintype J]
    (P R : HermitianMat I ℂ) (Q S : HermitianMat J ℂ) :
    directSum P Q - directSum R S = directSum (P - R) (Q - S) := by
  apply HermitianMat.ext
  simp only [directSum,HermitianMat.mat_mk,HermitianMat.mat_sub,HermitianMat.mat_add,HermitianMat.mat_neg,sub_eq_add_neg,
    Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,add_zero]

/-- Direct sums preserve the order of both summands. -/
theorem directSum_mono {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {P R : HermitianMat I ℂ} {Q S : HermitianMat J ℂ} (hP : P ≤ R) (hQ : Q ≤ S) :
    directSum P Q ≤ directSum R S := by
  apply sub_nonneg.mp
  rw [directSum_sub]
  exact directSum_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hQ)

/-- Forming block diagonal matrices preserves the order of both blocks. -/
theorem blockDiagonal_mono {I : Type*} [Fintype I] [DecidableEq I]
    {P R Q S : HermitianMat I ℂ} (hP : P ≤ R) (hQ : Q ≤ S) :
    Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal P Q ≤ Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal R S := directSum_mono hP hQ

/-- The direct sum of equally scaled identity matrices is the equally scaled identity on the sum
type. -/
@[simp] theorem directSum_scalar_one {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (r : ℝ) :
    directSum (r • (1 : HermitianMat I ℂ)) (r • (1 : HermitianMat J ℂ)) = r • 1 := by
  apply HermitianMat.ext
  simp only [directSum,HermitianMat.mat_mk,HermitianMat.mat_smul,HermitianMat.mat_one]
  rw [← Matrix.fromBlocks_one (l := I) (m := J),Matrix.fromBlocks_smul]
  simp only [smul_zero]

/-- A block diagonal matrix of equally scaled identity blocks is the equally scaled identity. -/
@[simp] theorem blockDiagonal_scalar_one {I : Type*} [Fintype I] [DecidableEq I] (r : ℝ) :
    Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (r • (1 : HermitianMat I ℂ)) (r • 1) = r • 1 := directSum_scalar_one r

/-- Each scalar or matrix coordinate of Stinespring dual data is bounded in absolute value or
norm by the norm of the full data. -/
theorem stinespringDual_coordinates_norm_le {Z : Type*} [Fintype Z] [DecidableEq Z]
    (h : StinespringConstraints Z) :
    |(WithLp.ofLp (WithLp.ofLp h).1).1| ≤ ‖h‖ ∧
    |(WithLp.ofLp (WithLp.ofLp h).1).2| ≤ ‖h‖ ∧
    ‖(WithLp.ofLp (WithLp.ofLp h).2).1‖ ≤ ‖h‖ ∧
    ‖(WithLp.ofLp (WithLp.ofLp h).2).2‖ ≤ ‖h‖ := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Real.norm_eq_abs] using!
      (WithLp.norm_fst_le ℝ (WithLp.ofLp h).1).trans (WithLp.norm_fst_le _ h)
  · simpa only [Real.norm_eq_abs] using!
      (WithLp.norm_snd_le ℝ (WithLp.ofLp h).1).trans (WithLp.norm_fst_le _ h)
  · exact (WithLp.norm_fst_le _ (WithLp.ofLp h).2).trans (WithLp.norm_snd_le _ h)
  · exact (WithLp.norm_snd_le _ (WithLp.ofLp h).2).trans (WithLp.norm_snd_le _ h)

/-- Bounds on the scalar and matrix perturbations give a scalar identity upper bound for the
input slack perturbation. -/
theorem stinespringInputPerturbation_upper_bound {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) {a t : ℝ} {Y : HermitianMat Z ℂ}
    (ha : a ≤ t) (hY : ‖Y.mat‖ ≤ t) :
    a • 1 - (stinespringComplementLinear A).adjoint Y ≤
      (t * (1 + ‖((stinespringComplementLinear A).adjoint 1).mat‖)) • 1 := by
  have hneg := stinespringAdjoint_upper_bound A (-Y)
  simp only [map_neg,HermitianMat.mat_neg,norm_neg] at hneg
  have hscale : ‖Y.mat‖ * ‖((stinespringComplementLinear A).adjoint 1).mat‖ ≤
      t * ‖((stinespringComplementLinear A).adjoint 1).mat‖ :=
    mul_le_mul_of_nonneg_right hY (norm_nonneg _)
  have hi : (0 : HermitianMat (Fin D) ℂ) ≤ 1 := HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  calc
    _ = a • 1 + -((stinespringComplementLinear A).adjoint Y) := sub_eq_add_neg _ _
    _ ≤ t • 1 + (t * ‖((stinespringComplementLinear A).adjoint 1).mat‖) • 1 :=
      add_le_add (smul_le_smul_of_nonneg_right ha hi)
        (hneg.trans (smul_le_smul_of_nonneg_right hscale hi))
    _ = _ := by module

/-- The Stinespring equality adjoint is bounded above by `stinespringPerturbationScale A B`
times the data norm, times the identity. -/
theorem stinespringEqMap_adjoint_upper_bound {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (h : StinespringConstraints Z) :
    (stinespringEqMap A B).adjoint h ≤
      (stinespringPerturbationScale A B * ‖h‖) • 1 := by
  let a := (WithLp.ofLp (WithLp.ofLp h).1).1
  let b := (WithLp.ofLp (WithLp.ofLp h).1).2
  let Y := (WithLp.ofLp (WithLp.ofLp h).2).1
  let W := (WithLp.ofLp (WithLp.ofLp h).2).2
  have heq : h = stinespringDualData a b Y W := rfl
  obtain ⟨ha,hb,hY,hW⟩ := stinespringDual_coordinates_norm_le h
  have hYop : ‖Y.mat‖ ≤ ‖h‖ := (hermitian_opNorm_le_norm Y).trans hY
  have hWop : ‖W.mat‖ ≤ ‖h‖ := (hermitian_opNorm_le_norm W).trans hW
  have hi : (0 : HermitianMat (Fin D) ℂ) ≤ 1 := HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hcoeffA : ‖h‖ * (1 + ‖((stinespringComplementLinear A).adjoint 1).mat‖) ≤
      stinespringPerturbationScale A B * ‖h‖ := by
    unfold stinespringPerturbationScale
    nlinarith [norm_nonneg h,norm_nonneg (((stinespringComplementLinear B).adjoint 1).mat)]
  have hcoeffB : ‖h‖ * (1 + ‖((stinespringComplementLinear B).adjoint 1).mat‖) ≤
      stinespringPerturbationScale A B * ‖h‖ := by
    unfold stinespringPerturbationScale
    nlinarith [norm_nonneg h,norm_nonneg (((stinespringComplementLinear A).adjoint 1).mat)]
  have hP := (stinespringInputPerturbation_upper_bound A ((le_abs_self a).trans ha) hYop).trans
    (smul_le_smul_of_nonneg_right hcoeffA hi)
  have hQ := (stinespringInputPerturbation_upper_bound B ((le_abs_self b).trans hb) hWop).trans
    (smul_le_smul_of_nonneg_right hcoeffB hi)
  have hk : 1 ≤ stinespringPerturbationScale A B := by
    unfold stinespringPerturbationScale
    nlinarith [norm_nonneg (((stinespringComplementLinear A).adjoint 1).mat),
      norm_nonneg (((stinespringComplementLinear B).adjoint 1).mat)]
  have hcoef : ‖h‖ ≤ stinespringPerturbationScale A B * ‖h‖ :=
    (one_mul ‖h‖).symm.trans_le (mul_le_mul_of_nonneg_right hk (norm_nonneg h))
  have hz : (0 : HermitianMat Z ℂ) ≤ 1 := HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hYbound : Y ≤ (stinespringPerturbationScale A B * ‖h‖) • 1 :=
    (hermitian_le_opNorm_smul_one Y).trans
      (smul_le_smul_of_nonneg_right (hYop.trans hcoef) hz)
  have hWbound : W ≤ (stinespringPerturbationScale A B * ‖h‖) • 1 :=
    (hermitian_le_opNorm_smul_one W).trans
      (smul_le_smul_of_nonneg_right (hWop.trans hcoef) hz)
  have hh := directSum_mono (blockDiagonal_mono hP hQ) (blockDiagonal_mono hYbound hWbound)
  have hadj : (stinespringEqMap A B).adjoint h = stinespringAdjointData A B a b Y W := by
    rw [heq,stinespringEqMap_adjoint]
  rw [hadj]
  simpa only [blockDiagonal_scalar_one,directSum_scalar_one] using! hh

/-- The Stinespring perturbation scale is strictly positive. -/
theorem stinespringPerturbationScale_pos {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : 0 < stinespringPerturbationScale A B := by
  unfold stinespringPerturbationScale
  positivity

/-- The operator norm of a Stinespring equality adjoint image is bounded by the perturbation
scale times the data norm. -/
theorem stinespringEqMap_adjoint_norm_bound {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (h : StinespringConstraints Z) :
    ‖((stinespringEqMap A B).adjoint h).mat‖ ≤ stinespringPerturbationScale A B * ‖h‖ := by
  have hh := stinespringEqMap_adjoint_upper_bound A B (-h)
  rw [map_neg,norm_neg] at hh
  have hlo := neg_le_neg hh
  simp only [neg_neg,← neg_smul] at hlo
  exact hermitian_opNorm_le_of_bounds
    (mul_nonneg (stinespringPerturbationScale_pos A B).le (norm_nonneg h)) hlo
    (stinespringEqMap_adjoint_upper_bound A B h)

/-- The fidelity identity slack dominates half the identity. -/
theorem fidelity_identity_slack_margin {I : Type*} [Fintype I] [DecidableEq I] :
    (1/2 : ℝ) • (1 : HermitianMat (I ⊕ I) ℂ) ≤
      1 - (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ) := by
  have hdiag : Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (1 : HermitianMat I ℂ) 1 = 1 := by
    simpa only [one_smul] using! blockDiagonal_scalar_one (I := I) (1 : ℝ)
  have hg : 0 ≤ fidelityDualBlock (1 : HermitianMat I ℂ) 1 := by
    apply HermitianMat.zero_le_iff.mpr
    simp only [fidelityDualBlock,HermitianMat.mat_sub,Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal,offDiagonal,
      HermitianMat.mat_mk,HermitianMat.mat_one,Matrix.conjTranspose_one]
    rw [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
    simpa using! Matrix.fromBlocks_gram_posSemidef (-1 : Matrix I I ℂ) (1 : Matrix I I ℂ)
  change 0 ≤ Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal
      (1 : HermitianMat I ℂ) 1 - offDiagonal (1 : Matrix I I ℂ) at hg
  rw [hdiag] at hg
  apply sub_nonneg.mp
  have heq : (1 : HermitianMat (I ⊕ I) ℂ) - (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ) -
      (1/2 : ℝ) • 1 = (1/2 : ℝ) • (1 - offDiagonal (1 : Matrix I I ℂ)) := by module
  rw [heq]
  exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hg

/-- Adding the operator norm of a Hermitian matrix to a scalar identity shift gives slack at
least the original scalar identity shift. -/
theorem hermitian_scalar_slack_margin {I : Type*} [Fintype I] [DecidableEq I]
    (H : HermitianMat I ℂ) (r : ℝ) :
    r • (1 : HermitianMat I ℂ) ≤ (r + ‖H.mat‖) • 1 - H := by
  have hn := sub_nonneg.mpr (hermitian_le_opNorm_smul_one H)
  rw [add_smul,add_sub_assoc]
  exact le_add_of_nonneg_right hn

/-- The dual slack at `stinespringDualCenter A B` dominates half the identity. -/
theorem stinespringDualCenter_margin {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    (1/2 : ℝ) • (1 : HermitianMat (StinespringRegister D Z) ℂ) ≤
      (stinespringProgram A B).constraint.adjoint (stinespringDualCenter A B) -
        (stinespringProgram A B).objective := by
  have hP := hermitian_scalar_slack_margin
    ((stinespringComplementLinear A).adjoint (1 : HermitianMat Z ℂ)) (1/2 : ℝ)
  have hQ := hermitian_scalar_slack_margin
    ((stinespringComplementLinear B).adjoint (1 : HermitianMat Z ℂ)) (1/2 : ℝ)
  unfold stinespringDualCenter
  rw [stinespringProgram_dual_slack]
  have hdiag : Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (1 : HermitianMat Z ℂ) 1 = 1 := by
    simpa only [one_smul] using! blockDiagonal_scalar_one (I := Z) (1 : ℝ)
  rw [hdiag]
  have hh := directSum_mono (blockDiagonal_mono hP hQ) (fidelity_identity_slack_margin (I := Z))
  simpa only [blockDiagonal_scalar_one,directSum_scalar_one] using! hh

/-- The Stinespring interior radius is strictly positive. -/
theorem stinespringInteriorRadius_pos {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : 0 < stinespringInteriorRadius A B := by
  unfold stinespringInteriorRadius
  exact inv_pos.mpr (mul_pos (by norm_num) (stinespringPerturbationScale_pos A B))

/-- The product of the Stinespring perturbation scale and interior radius is one quarter. -/
theorem stinespringInteriorRadius_scale {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    stinespringPerturbationScale A B * stinespringInteriorRadius A B = (1/4 : ℝ) := by
  unfold stinespringInteriorRadius
  have hk := (stinespringPerturbationScale_pos A B).ne'
  field_simp

/-- Perturbations within the Stinespring interior radius leave dual slack at least one quarter
of the identity. -/
theorem stinespringDualCenter_ball_margin {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) {h : StinespringConstraints Z}
    (hh : ‖h‖ ≤ stinespringInteriorRadius A B) :
    (1/4 : ℝ) • (1 : HermitianMat (StinespringRegister D Z) ℂ) ≤
      (stinespringProgram A B).constraint.adjoint (stinespringDualCenter A B + h) -
        (stinespringProgram A B).objective := by
  have hbound : ‖((stinespringEqMap A B).adjoint h).mat‖ ≤ (1/4 : ℝ) := by
    calc
      _ ≤ stinespringPerturbationScale A B * ‖h‖ := stinespringEqMap_adjoint_norm_bound A B h
      _ ≤ stinespringPerturbationScale A B * stinespringInteriorRadius A B :=
        mul_le_mul_of_nonneg_left hh (stinespringPerturbationScale_pos A B).le
      _ = _ := stinespringInteriorRadius_scale A B
  have hi : (0 : HermitianMat (StinespringRegister D Z) ℂ) ≤ 1 :=
    HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hlo : (-(1/4) : ℝ) • 1 ≤ (stinespringEqMap A B).adjoint h :=
    (smul_le_smul_of_nonneg_right (neg_le_neg hbound) hi).trans (hermitian_neg_opNorm_smul_one_le _)
  let S := (stinespringProgram A B).constraint.adjoint (stinespringDualCenter A B + h) -
    (stinespringProgram A B).objective
  have hmargin : (1/4 : ℝ) • (1 : HermitianMat (StinespringRegister D Z) ℂ) ≤ S := by
    have hm := add_le_add (stinespringDualCenter_margin A B) hlo
    have heq : (1/2 : ℝ) • (1 : HermitianMat (StinespringRegister D Z) ℂ) + (-(1/4) : ℝ) • 1 =
        (1/4 : ℝ) • 1 := by module
    rw [heq] at hm
    dsimp [S]
    change _ ≤ (stinespringEqMap A B).adjoint (stinespringDualCenter A B + h) - _
    rw [map_add]
    change (1/4 : ℝ) • (1 : HermitianMat (StinespringRegister D Z) ℂ) ≤
      (stinespringEqMap A B).adjoint (stinespringDualCenter A B) -
        (stinespringProgram A B).objective + (stinespringEqMap A B).adjoint h at hm
    convert! hm using 1 <;> abel
  exact hmargin

/-- Every perturbation within the Stinespring interior radius gives positive definite dual
slack. -/
theorem stinespringDualCenter_ball_posDef {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) {h : StinespringConstraints Z}
    (hh : ‖h‖ ≤ stinespringInteriorRadius A B) :
    ((stinespringProgram A B).constraint.adjoint (stinespringDualCenter A B + h) -
      (stinespringProgram A B).objective).mat.PosDef := by
  let S := (stinespringProgram A B).constraint.adjoint (stinespringDualCenter A B + h) -
    (stinespringProgram A B).objective
  have hmargin : (1/4 : ℝ) • (1 : HermitianMat (StinespringRegister D Z) ℂ) ≤ S :=
    stinespringDualCenter_ball_margin A B hh
  have hs : 0 ≤ S - (1/4 : ℝ) • 1 := sub_nonneg.mpr hmargin
  have heq : S = (1/4 : ℝ) • 1 + (S - (1/4 : ℝ) • 1) := by abel
  change S.mat.PosDef
  rw [heq,HermitianMat.mat_add,HermitianMat.mat_smul,HermitianMat.mat_one]
  exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1/4)).add_posSemidef
    (HermitianMat.zero_le_iff.mp hs)

/-- The Stinespring dual center and interior radius define a dual interior ball. -/
theorem stinespringDualCenter_interior_ball {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    (stinespringProgram A B).DualInteriorBall (stinespringDualCenter A B) (stinespringInteriorRadius A B) := by
  intro h hh
  exact HermitianMat.zero_le_iff.mpr (stinespringDualCenter_ball_posDef A B hh).posSemidef

end SdpInteriorRadius

section ChoiInteriorRadius
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable local instance choiInteriorMatrixCStar {J : Type*} [Fintype J] [DecidableEq J] :
    CStarAlgebra (Matrix J J ℂ) where

/-- The off-diagonal construction sends the zero matrix to zero. -/
@[simp] theorem offDiagonal_zero {I : Type*} [Fintype I] :
    offDiagonal (0 : Matrix I I ℂ) = 0 := by
  apply HermitianMat.ext
  simp only [offDiagonal,HermitianMat.mat_mk,Matrix.conjTranspose_zero]
  ext i j
  cases i <;> cases j <;> rfl

/-- The norm of a cross block times the identity dominates its Hermitian off-diagonal dilation. -/
theorem norm_cross_dilation_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℂ) : 0 ≤ ‖C‖ • (1 : HermitianMat (I ⊕ I) ℂ) - offDiagonal C := by
  by_cases hc : C = 0
  · subst C
    simp
  have hn : 0 < ‖C‖ := norm_pos_iff.mpr hc
  let K : Matrix I I ℂ := -‖C‖⁻¹ • C
  have hK : ‖K‖ ≤ 1 := by
    dsimp [K]
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hn)]
    exact le_of_eq (inv_mul_cancel₀ hn.ne')
  have hscale : ‖C‖ • K = -C := by
    dsimp [K]
    rw [smul_smul,mul_neg,mul_inv_cancel₀ hn.ne',neg_one_smul]
  have hstar : ‖C‖ • Kᴴ = -Cᴴ := by
    have hh := congrArg Matrix.conjTranspose hscale
    simpa using! hh
  apply HermitianMat.zero_le_iff.mpr
  have hp := ((unit_block_positive_iff K).mpr hK).smul hn.le
  have heq : (‖C‖ • (1 : HermitianMat (I ⊕ I) ℂ) - offDiagonal C).mat =
      ‖C‖ • Matrix.fromBlocks (1 : Matrix I I ℂ) K Kᴴ 1 := by
    simp only [HermitianMat.mat_sub,HermitianMat.mat_smul,HermitianMat.mat_one,
      offDiagonal,HermitianMat.mat_mk]
    conv_lhs => rw [← Matrix.fromBlocks_one (l := I) (m := I)]
    rw [Matrix.fromBlocks_smul,sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
    simp only [Matrix.fromBlocks_smul,smul_zero,add_zero,zero_add,neg_zero,hscale,hstar]
  rwa [heq]

/-- The scalar shift `‖C‖ / 2 + 1` makes the half-scaled cross-block slack dominate the
identity. -/
theorem weighted_block_unit_margin {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℂ) :
    (1 : HermitianMat (I ⊕ I) ℂ) ≤ (‖C‖/2 + 1) • 1 - (1/2 : ℝ) • offDiagonal C := by
  have hp := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (norm_cross_dilation_nonneg C)
  apply sub_nonneg.mp
  have heq : (‖C‖/2 + 1) • (1 : HermitianMat (I ⊕ I) ℂ) - (1/2 : ℝ) • offDiagonal C - 1 =
      (1/2 : ℝ) • (‖C‖ • 1 - offDiagonal C) := by module
  rwa [heq]

/-- The left partial trace of the identity on `Fin E × Fin D` is `E` times the identity. -/
@[simp] theorem traceLeft_one_fin (D E : ℕ) :
    (1 : HermitianMat (Fin E × Fin D) ℂ).traceLeft = (E : ℝ) • 1 := by
  rw [← HermitianMat.kronecker_one_one,HermitianMat.traceLeft_kron]
  simp only [HermitianMat.trace_one,Fintype.card_fin]

/-- The scalar slack `(1 + a * b) • 1 - a • (b • 1)` equals the identity. -/
theorem scalar_center_cancel {I : Type*} [Fintype I] [DecidableEq I] (a b : ℝ) :
    (1 + a * b) • (1 : HermitianMat I ℂ) - a • (b • 1) = 1 := by
  rw [smul_smul,add_smul,one_smul,add_sub_cancel_right]

/-- The dual slack at `diamondDualCenter T` dominates the identity. -/
theorem diamondDualCenter_margin {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
      (diamondProgram T).constraint.adjoint (diamondDualCenter T) - (diamondProgram T).objective := by
  unfold diamondDualCenter
  rw [diamondProgram_dual_slack,HermitianMat.traceLeft_smul,traceLeft_one_fin,
    scalar_center_cancel]
  rw [blockDiagonal_scalar_one (I := Fin E × Fin D) (‖MatrixMap.choi_matrix T‖/2 + 1)]
  have hi : Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (1 : HermitianMat (Fin D) ℂ) 1 = 1 := by
    simpa only [one_smul] using! blockDiagonal_scalar_one (I := Fin D) (1 : ℝ)
  rw [hi]
  have hh := directSum_mono (le_refl (1 : HermitianMat (Fin D ⊕ Fin D) ℂ))
    (weighted_block_unit_margin (MatrixMap.choi_matrix T))
  have hsum : directSum (1 : HermitianMat (Fin D ⊕ Fin D) ℂ)
      (1 : HermitianMat ((Fin E × Fin D) ⊕ (Fin E × Fin D)) ℂ) = 1 := by
    apply HermitianMat.ext
    exact Matrix.fromBlocks_one
  rwa [hsum] at hh

/-- The left partial trace preserves the Hermitian matrix order. -/
theorem traceLeft_mono_fin {D E : ℕ} {Y W : HermitianMat (Fin E × Fin D) ℂ}
    (h : Y ≤ W) : Y.traceLeft ≤ W.traceLeft := by
  apply sub_nonneg.mp
  rw [← HermitianMat.traceLeft_sub]
  exact HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp (sub_nonneg.mpr h)).traceLeft

/-- The left partial trace is bounded above by the matrix operator norm times the traced
dimension, times the identity. -/
theorem traceLeft_upper_bound_fin {D E : ℕ} (Y : HermitianMat (Fin E × Fin D) ℂ) :
    Y.traceLeft ≤ (‖Y.mat‖ * E) • 1 := by
  have hh := traceLeft_mono_fin (hermitian_le_opNorm_smul_one Y)
  rwa [HermitianMat.traceLeft_smul,traceLeft_one_fin,smul_smul] at hh

/-- Scalar and matrix perturbation bounds yield a scalar identity bound of `t * (1 + E)` on the
partial trace slack perturbation. -/
theorem diamondInputPerturbation_upper_bound {D E : ℕ} {a t : ℝ}
    {Y : HermitianMat (Fin E × Fin D) ℂ} (ha : a ≤ t) (hY : ‖Y.mat‖ ≤ t) :
    a • 1 - Y.traceLeft ≤ (t * (1 + E)) • 1 := by
  have hneg := traceLeft_upper_bound_fin (-Y)
  simp only [HermitianMat.traceLeft_neg,HermitianMat.mat_neg,norm_neg] at hneg
  have hscale : ‖Y.mat‖ * E ≤ t * E := mul_le_mul_of_nonneg_right hY (Nat.cast_nonneg E)
  have hi : (0 : HermitianMat (Fin D) ℂ) ≤ 1 := HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  calc
    _ = a • 1 + -Y.traceLeft := sub_eq_add_neg _ _
    _ ≤ t • 1 + (t * E) • 1 := add_le_add (smul_le_smul_of_nonneg_right ha hi)
      (hneg.trans (smul_le_smul_of_nonneg_right hscale hi))
    _ = _ := by module

/-- The diamond equality adjoint is bounded above by `1 + E` times the data norm, times the
identity. -/
theorem diamondEqMap_adjoint_upper_bound {D E : ℕ} (h : DiamondConstraints D E) :
    (diamondEqMap D E).adjoint h ≤ ((1 + (E : ℝ)) * ‖h‖) • 1 := by
  let a := (WithLp.ofLp (WithLp.ofLp h).1).1
  let b := (WithLp.ofLp (WithLp.ofLp h).1).2
  let Y := (WithLp.ofLp (WithLp.ofLp h).2).1
  let W := (WithLp.ofLp (WithLp.ofLp h).2).2
  have heq : h = diamondDualData a b Y W := rfl
  obtain ⟨ha,hb,hY,hW⟩ := stinespringDual_coordinates_norm_le h
  have hYop : ‖Y.mat‖ ≤ ‖h‖ := (hermitian_opNorm_le_norm Y).trans hY
  have hWop : ‖W.mat‖ ≤ ‖h‖ := (hermitian_opNorm_le_norm W).trans hW
  have hP : a • 1 - Y.traceLeft ≤ ((1 + (E : ℝ)) * ‖h‖) • 1 := by
    simpa only [mul_comm] using!
        diamondInputPerturbation_upper_bound ((le_abs_self a).trans ha) hYop
  have hQ : b • 1 - W.traceLeft ≤ ((1 + (E : ℝ)) * ‖h‖) • 1 := by
    simpa only [mul_comm] using!
        diamondInputPerturbation_upper_bound ((le_abs_self b).trans hb) hWop
  have hcoef : ‖h‖ ≤ (1 + (E : ℝ)) * ‖h‖ := by
    nlinarith [norm_nonneg h,Nat.cast_nonneg (α := ℝ) E]
  have hi : (0 : HermitianMat (Fin E × Fin D) ℂ) ≤ 1 :=
    HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hYbound : Y ≤ ((1 + (E : ℝ)) * ‖h‖) • 1 := (hermitian_le_opNorm_smul_one Y).trans
    (smul_le_smul_of_nonneg_right (hYop.trans hcoef) hi)
  have hWbound : W ≤ ((1 + (E : ℝ)) * ‖h‖) • 1 := (hermitian_le_opNorm_smul_one W).trans
    (smul_le_smul_of_nonneg_right (hWop.trans hcoef) hi)
  have hh := directSum_mono (blockDiagonal_mono hP hQ) (blockDiagonal_mono hYbound hWbound)
  have hadj : (diamondEqMap D E).adjoint h = diamondAdjointData a b Y W := by
    rw [heq,diamondEqMap_adjoint]
  rw [hadj]
  simpa only [blockDiagonal_scalar_one,directSum_scalar_one] using! hh

/-- The operator norm of a diamond equality adjoint image is at most `1 + E` times the data
norm. -/
theorem diamondEqMap_adjoint_norm_bound {D E : ℕ} (h : DiamondConstraints D E) :
    ‖((diamondEqMap D E).adjoint h).mat‖ ≤ (1 + (E : ℝ)) * ‖h‖ := by
  have hh := diamondEqMap_adjoint_upper_bound (-h)
  rw [map_neg,norm_neg] at hh
  have hlo := neg_le_neg hh
  simp only [neg_neg,← neg_smul] at hlo
  exact hermitian_opNorm_le_of_bounds
    (mul_nonneg (by positivity) (norm_nonneg h)) hlo (diamondEqMap_adjoint_upper_bound h)

/-- The diamond interior radius is strictly positive. -/
theorem diamondInteriorRadius_pos (E : ℕ) : 0 < diamondInteriorRadius E := by
  unfold diamondInteriorRadius
  apply inv_pos.mpr
  have hm : 0 < max 1 E := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 E)
  exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) hm)

/-- For positive output dimension, the diamond interior radius is the reciprocal of twice that
dimension. -/
theorem diamondInteriorRadius_eq_of_pos {E : ℕ} (hE : 0 < E) :
    diamondInteriorRadius E = (2 * (E : ℝ))⁻¹ := by
  unfold diamondInteriorRadius
  rw [max_eq_right (Nat.succ_le_iff.mpr hE)]

/-- Multiplying the diamond interior radius by `1 + E` gives a value at most one. -/
theorem diamondInteriorRadius_scale (E : ℕ) :
    (1 + (E : ℝ)) * diamondInteriorRadius E ≤ 1 := by
  have hm : (1 : ℝ) ≤ (max 1 E : ℕ) := by exact_mod_cast le_max_left 1 E
  have he : (E : ℝ) ≤ (max 1 E : ℕ) := by exact_mod_cast le_max_right 1 E
  have hp : (0 : ℝ) < 2 * (max 1 E : ℕ) := by positivity
  have hcoef : 1 + (E : ℝ) ≤ 2 * (max 1 E : ℕ) := by linarith
  have hh := (div_le_one hp).mpr hcoef
  simpa only [diamondInteriorRadius,Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv] using! hh

/-- The diamond dual center and interior radius define a dual interior ball. -/
theorem diamondDualCenter_interior_ball {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    (diamondProgram T).DualInteriorBall (diamondDualCenter T) (diamondInteriorRadius E) := by
  intro h hh
  have hnorm : ‖((diamondEqMap D E).adjoint h).mat‖ ≤ (1 : ℝ) := by
    calc
      _ ≤ (1 + (E : ℝ)) * ‖h‖ := diamondEqMap_adjoint_norm_bound h
      _ ≤ (1 + (E : ℝ)) * diamondInteriorRadius E := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := diamondInteriorRadius_scale E
  have hi : (0 : HermitianMat (DiamondRegister D E) ℂ) ≤ 1 :=
    HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hlo : -(1 : HermitianMat (DiamondRegister D E) ℂ) ≤ (diamondEqMap D E).adjoint h := by
    have hl := (smul_le_smul_of_nonneg_right (neg_le_neg hnorm) hi).trans
      (hermitian_neg_opNorm_smul_one_le ((diamondEqMap D E).adjoint h))
    simpa only [neg_one_smul] using! hl
  have hm := add_le_add (diamondDualCenter_margin T) hlo
  simp only [add_neg_cancel] at hm
  change 0 ≤ (diamondEqMap D E).adjoint (diamondDualCenter T + h) - (diamondProgram T).objective
  rw [map_add]
  change 0 ≤ (diamondEqMap D E).adjoint (diamondDualCenter T) - (diamondProgram T).objective +
    (diamondEqMap D E).adjoint h at hm
  convert! hm using 1 <;> abel

end ChoiInteriorRadius

section ChoiDualOuterBound
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable local instance outerMatrixCStar {I : Type*} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- The norm of a positive semidefinite Hermitian matrix is at most its trace. -/
theorem hermitian_norm_le_trace {I : Type*} [Fintype I] [DecidableEq I]
    {Y : HermitianMat I ℂ} (hY : 0 ≤ Y) : ‖Y‖ ≤ Y.trace := by
  have hh := HermitianMat.inner_le_mul_trace hY hY
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [HermitianMat.trace_nonneg hY,norm_nonneg Y]

/-- The Hilbert product norm of a pair is at most the sum of the two component norms. -/
theorem hilbertPair_norm_le_sum {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (v : V) (w : W) : ‖WithLp.toLp 2 (v,w)‖ ≤ ‖v‖ + ‖w‖ := by
  have heq : WithLp.toLp 2 (v,w) =
      WithLp.toLp 2 (v,(0 : W)) + WithLp.toLp 2 ((0 : V),w) := by
    rw [← WithLp.toLp_add]
    simp
  rw [heq]
  simpa only [WithLp.norm_toLp_fst,WithLp.norm_toLp_snd] using!
    norm_add_le (WithLp.toLp 2 (v,(0 : W))) (WithLp.toLp 2 ((0 : V),w))

/-- For nonnegative scalar and matrix coordinates, the diamond dual data norm is bounded by the
scalar sum plus the two traces. -/
theorem diamondDualData_norm_le_trace {D E : ℕ} {a b : ℝ}
    {Y W : HermitianMat (Fin E × Fin D) ℂ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hY : 0 ≤ Y) (hW : 0 ≤ W) :
    ‖diamondDualData a b Y W‖ ≤ a + b + Y.trace + W.trace := by
  have h1 := hilbertPair_norm_le_sum (WithLp.toLp 2 (a,b)) (WithLp.toLp 2 (Y,W))
  have h2 := hilbertPair_norm_le_sum a b
  have h3 := hilbertPair_norm_le_sum Y W
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at h2
  change ‖diamondDualData a b Y W‖ ≤ _ at h1
  linarith [hermitian_norm_le_trace hY,hermitian_norm_le_trace hW]

/-- For positive input dimension, feasible diamond dual data have nonnegative coordinates and
matrix traces bounded by the corresponding scalars times `D`. -/
theorem diamondProgram_dual_size_data {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {a b : ℝ}
    {Y W : HermitianMat (Fin E × Fin D) ℂ}
    (hy : (diamondProgram T).DualFeasible (diamondDualData a b Y W)) :
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ Y ∧ 0 ≤ W ∧
      Y.trace ≤ a * D ∧ W.trace ≤ b * D := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  obtain ⟨ha,hb,hblock⟩ := (diamondProgram_dual_block_iff T a b Y W).mp hy
  have hd : 0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) ((2 : ℝ) • Y) ((2 : ℝ) • W) := by
    rw [diamond_double_dual_block]
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hblock
  obtain ⟨hY2,hW2⟩ := weightedDualBlock_diagonal_nonneg hd
  have hY : 0 ≤ Y := by
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hY2
    simpa only [smul_smul,show (1/2 : ℝ) * 2 = 1 by norm_num,one_smul] using! hh
  have hW : 0 ≤ W := by
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hW2
    simpa only [smul_smul,show (1/2 : ℝ) * 2 = 1 by norm_num,one_smul] using! hh
  have hYtr : 0 ≤ Y.traceLeft :=
    HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp hY).traceLeft
  have hWtr : 0 ≤ W.traceLeft :=
    HermitianMat.zero_le_iff.mpr (HermitianMat.zero_le_iff.mp hW).traceLeft
  have ha0 : 0 ≤ a := (norm_nonneg Y.traceLeft.mat).trans
    (opNorm_le_of_nonneg_scalar_slack hYtr ha)
  have hb0 : 0 ≤ b := (norm_nonneg W.traceLeft.mat).trans
    (opNorm_le_of_nonneg_scalar_slack hWtr hb)
  have htY := HermitianMat.trace_nonneg ha
  have htW := HermitianMat.trace_nonneg hb
  simp only [HermitianMat.trace_sub,HermitianMat.trace_smul,HermitianMat.trace_one,
    Fintype.card_fin,HermitianMat.traceLeft_trace] at htY htW
  exact ⟨ha0,hb0,hY,hW,by linarith,by linarith⟩

/-- For positive input dimension, the norm of any diamond dual feasible point is at most `D + 1`
times its score. -/
theorem diamondProgram_dual_norm_le_score {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {y : DiamondConstraints D E}
    (hy : (diamondProgram T).DualFeasible y) :
    ‖y‖ ≤ (D + 1 : ℝ) * (diamondProgram T).dualScore y := by
  let a := (WithLp.ofLp (WithLp.ofLp y).1).1
  let b := (WithLp.ofLp (WithLp.ofLp y).1).2
  let Y := (WithLp.ofLp (WithLp.ofLp y).2).1
  let W := (WithLp.ofLp (WithLp.ofLp y).2).2
  have heq : y = diamondDualData a b Y W := rfl
  rw [heq] at hy ⊢
  obtain ⟨ha,hb,hY,hW,htY,htW⟩ := diamondProgram_dual_size_data hD T hy
  rw [diamondProgram_dualScore]
  have hh := diamondDualData_norm_le_trace ha hb hY hW
  nlinarith

/-- The diamond program has a dual feasible point with score `E` times the norm of its Choi
matrix. -/
theorem diamondProgram_norm_bound_point {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ y : DiamondConstraints D E, (diamondProgram T).DualFeasible y ∧
      (diamondProgram T).dualScore y = E * ‖MatrixMap.choi_matrix T‖ := by
  let c : ℝ := ‖MatrixMap.choi_matrix T‖ / 2
  refine ⟨diamondDualData (c * E) (c * E) (c • 1) (c • 1),?_,?_⟩
  · apply (diamondProgram_dual_block_iff T _ _ _ _).mpr
    have heq : (c * E) • (1 : HermitianMat (Fin D) ℂ) -
        (c • (1 : HermitianMat (Fin E × Fin D) ℂ)).traceLeft = 0 := by
      rw [HermitianMat.traceLeft_smul,traceLeft_one_fin,smul_smul,sub_self]
    refine ⟨by rw [heq],by rw [heq],?_⟩
    rw [blockDiagonal_scalar_one]
    have hh := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
      (norm_cross_dilation_nonneg (MatrixMap.choi_matrix T))
    have he : c • (1 : HermitianMat ((Fin E × Fin D) ⊕ (Fin E × Fin D)) ℂ) -
        (1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T) =
        (1/2 : ℝ) • (‖MatrixMap.choi_matrix T‖ • 1 - offDiagonal (MatrixMap.choi_matrix T)) := by
      dsimp [c]
      module
    rwa [he]
  · rw [diamondProgram_dualScore]
    dsimp [c]
    ring

/-- For positive input dimension, primal and dual optimizers attain a common value `α`
representing the finite diamond norm, with `0 ≤ α ≤ E * ‖MatrixMap.choi_matrix T‖`. The dual
optimizer has norm at most `2 * ‖MatrixMap.choi_matrix T‖ * D * E`. -/
theorem diamondProgram_bounded_optimizers {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (y : DiamondConstraints D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).DualFeasible y ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      (diamondProgram T).primalScore M = α ∧ (diamondProgram T).dualScore y = α ∧
      0 ≤ α ∧ α ≤ E * ‖MatrixMap.choi_matrix T‖ ∧
      ‖y‖ ≤ 2 * ‖MatrixMap.choi_matrix T‖ * D * E := by
  obtain ⟨α,M,y,hnorm,hM,hy,hp,hd,hsM,hsy⟩ := diamondProgram_norm_both_optimizers hD T
  obtain ⟨v,hv,hsv⟩ := diamondProgram_norm_bound_point T
  have hu : α ≤ E * ‖MatrixMap.choi_matrix T‖ := by
    have hh :=
        (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality (P := (diamondProgram T))) hM hv
    rwa [hsM,hsv] at hh
  have hlo : 0 ≤ α := by
    have heq : y = diamondDualData
        (WithLp.ofLp (WithLp.ofLp y).1).1 (WithLp.ofLp (WithLp.ofLp y).1).2
        (WithLp.ofLp (WithLp.ofLp y).2).1 (WithLp.ofLp (WithLp.ofLp y).2).2 := rfl
    rw [heq] at hy hsy
    obtain ⟨ha,hb,-,-,-,-⟩ := diamondProgram_dual_size_data hD T hy
    rw [diamondProgram_dualScore] at hsy
    linarith
  have hn := diamondProgram_dual_norm_le_score hD T hy
  rw [hsy] at hn
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hnon : (0 : ℝ) ≤ E * ‖MatrixMap.choi_matrix T‖ :=
      mul_nonneg (Nat.cast_nonneg E) (norm_nonneg _)
  refine ⟨α,M,y,hnorm,hM,hy,hp,hd,hsM,hsy,hlo,hu,?_⟩
  calc
    ‖y‖ ≤ (D + 1 : ℝ) * α := hn
    _ ≤ (D + 1 : ℝ) * (E * ‖MatrixMap.choi_matrix T‖) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ ≤ _ := by nlinarith

/-- For positive input dimension, each feasible diamond dual score sublevel set is compact. -/
theorem diamondProgram_dual_sublevel_compact {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) (t : ℝ) :
    IsCompact {y : DiamondConstraints D E |
      (diamondProgram T).DualFeasible y ∧ (diamondProgram T).dualScore y ≤ t} := by
  have hf : IsClosed {y : DiamondConstraints D E | (diamondProgram T).DualFeasible y} :=
    (psdCone (DiamondRegister D E)).isClosed.preimage
      ((diamondProgram T).constraint.adjoint.continuous.sub continuous_const)
  have hs : IsClosed {y : DiamondConstraints D E | (diamondProgram T).dualScore y ≤ t} :=
    isClosed_le (innerSL ℝ (diamondProgram T).rhs).continuous continuous_const
  apply (isCompact_closedBall (0 : DiamondConstraints D E) ((D + 1 : ℝ) * t)).of_isClosed_subset
    (hf.inter hs)
  intro y hy
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (diamondProgram_dual_norm_le_score hD T hy.1).trans
    (mul_le_mul_of_nonneg_left hy.2 (by positivity))

end ChoiDualOuterBound

section ChoiDualRegularization
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable local instance regularizationMatrixCStar {I : Type*} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- The diamond dual center has score `2 + (‖MatrixMap.choi_matrix T‖ + 2) * E`. -/
theorem diamondDualCenter_score {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    (diamondProgram T).dualScore (diamondDualCenter T) =
      2 + (‖MatrixMap.choi_matrix T‖ + 2) * E := by
  unfold diamondDualCenter
  rw [diamondProgram_dualScore]
  ring

/-- The diamond dual center has nonnegative score. -/
theorem diamondDualCenter_score_nonneg {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    0 ≤ (diamondProgram T).dualScore (diamondDualCenter T) := by
  rw [diamondDualCenter_score]
  positivity

/-- The diamond regularization weight is positive for a positive tolerance. -/
theorem diamondRegularizationWeight_pos {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {ε : ℝ} (hε : 0 < ε) : 0 < diamondRegularizationWeight T ε := by
  unfold diamondRegularizationWeight
  exact lt_min (by norm_num) (div_pos hε (by positivity))

/-- The diamond regularization weight is at most one. -/
theorem diamondRegularizationWeight_le_one {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ε : ℝ) : diamondRegularizationWeight T ε ≤ 1 := min_le_left _ _

/-- The regularization weight times the dual center score plus one is at most half the
tolerance. -/
theorem diamondRegularizationWeight_budget {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ε : ℝ) :
    diamondRegularizationWeight T ε * ((diamondProgram T).dualScore (diamondDualCenter T) + 1) ≤ ε/2 := by
  have hh := min_le_right (1 : ℝ) (ε / (2 * (3 + (‖MatrixMap.choi_matrix T‖ + 2) * E)))
  have hp : 0 < (2 : ℝ) * (3 + (‖MatrixMap.choi_matrix T‖ + 2) * E) := by positivity
  have hb := (le_div_iff₀ hp).mp hh
  change diamondRegularizationWeight T ε * _ ≤ ε at hb
  rw [diamondDualCenter_score]
  nlinarith

/-- The diamond rounding radius is positive for a positive tolerance. -/
theorem diamondRoundingRadius_pos {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {ε : ℝ} (hε : 0 < ε) : 0 < diamondRoundingRadius T ε :=
  div_pos (diamondRegularizationWeight_pos T hε) (by positivity)

/-- Regularizing a dual feasible point with weight between zero and one gives dual slack at
least that weight times the identity. -/
theorem diamondRegularizedDual_margin {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {y : DiamondConstraints D E} (hy : (diamondProgram T).DualFeasible y)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
      (diamondProgram T).constraint.adjoint (diamondRegularizedDual T θ y) -
        (diamondProgram T).objective := by
  have hpos : 0 ≤ (1-θ) • ((diamondProgram T).constraint.adjoint y - (diamondProgram T).objective) :=
    smul_nonneg (sub_nonneg.mpr hθ1) hy
  have hcenter := smul_le_smul_of_nonneg_left (diamondDualCenter_margin T) hθ
  have hh := add_le_add hpos hcenter
  simp only [zero_add] at hh
  have heq : (diamondProgram T).constraint.adjoint (diamondRegularizedDual T θ y) -
      (diamondProgram T).objective =
      (1-θ) • ((diamondProgram T).constraint.adjoint y - (diamondProgram T).objective) +
        θ • ((diamondProgram T).constraint.adjoint (diamondDualCenter T) - (diamondProgram T).objective) := by
    unfold diamondRegularizedDual
    rw [map_add,map_smul,map_smul]
    module
  rwa [heq]

/-- A perturbation of norm at most `θ / (2 * (1 + E))` preserves half the regularized scalar
slack margin. -/
theorem diamondRegularizedDual_perturbation_margin {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {y : DiamondConstraints D E} (hy : (diamondProgram T).DualFeasible y)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {h : DiamondConstraints D E}
    (hh : ‖h‖ ≤ θ / (2 * (1 + E))) :
    (θ/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
      (diamondProgram T).constraint.adjoint (diamondRegularizedDual T θ y + h) -
        (diamondProgram T).objective := by
  have hp : (0 : ℝ) < 2 * (1 + E) := by positivity
  have hb := (le_div_iff₀ hp).mp hh
  have hnorm : ‖((diamondEqMap D E).adjoint h).mat‖ ≤ θ/2 :=
    (diamondEqMap_adjoint_norm_bound h).trans (by nlinarith)
  have hi : (0 : HermitianMat (DiamondRegister D E) ℂ) ≤ 1 :=
    HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hl : (-θ/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤ (diamondEqMap D E).adjoint h := by
    have hscale := smul_le_smul_of_nonneg_right (neg_le_neg hnorm) hi
    have hscale' : (-θ/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
        (-‖((diamondEqMap D E).adjoint h).mat‖) • 1 := by
      simpa only [neg_div] using! hscale
    exact hscale'.trans (hermitian_neg_opNorm_smul_one_le ((diamondEqMap D E).adjoint h))
  have hm := add_le_add (diamondRegularizedDual_margin T hy hθ hθ1) hl
  change _ ≤ (diamondEqMap D E).adjoint (diamondRegularizedDual T θ y + h) -
    (diamondProgram T).objective
  rw [map_add]
  change θ • (1 : HermitianMat (DiamondRegister D E) ℂ) + (-θ/2) • 1 ≤
    (diamondEqMap D E).adjoint (diamondRegularizedDual T θ y) -
      (diamondProgram T).objective + (diamondEqMap D E).adjoint h at hm
  convert! hm using 1 <;> module

/-- A Hermitian matrix dominating a strictly positive scalar multiple of the identity is
positive definite. -/
theorem hermitian_posDef_of_scalar_margin {I : Type*} [Fintype I] [DecidableEq I]
    {S : HermitianMat I ℂ} {r : ℝ} (hr : 0 < r) (hs : r • 1 ≤ S) : S.mat.PosDef := by
  have hp : 0 ≤ S - r • 1 := sub_nonneg.mpr hs
  have heq : S = r • 1 + (S - r • 1) := by abel
  rw [heq,HermitianMat.mat_add,HermitianMat.mat_smul,HermitianMat.mat_one]
  exact (Matrix.PosDef.one.smul hr).add_posSemidef (HermitianMat.zero_le_iff.mp hp)

/-- Perturbing diamond dual data by `h` changes the dual score by at most twice `‖h‖`. -/
theorem diamondDualScore_perturbation_bound {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (y h : DiamondConstraints D E) :
    |(diamondProgram T).dualScore (y+h) - (diamondProgram T).dualScore y| ≤ 2 * ‖h‖ := by
  have hr : ‖(diamondProgram T).rhs‖ ≤ 2 := by
    change ‖diamondDualData 1 1 (0 : HermitianMat (Fin E × Fin D) ℂ) 0‖ ≤ _
    have hh := diamondDualData_norm_le_trace (D := D) (E := E)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) (le_refl 0) (le_refl 0)
    simpa only [HermitianMat.trace_zero,add_zero,show (1 : ℝ)+1=2 by norm_num] using! hh
  simp only [Program.dualScore,inner_add_right,add_sub_cancel_left]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg h))

/-- The score of a regularized diamond dual point is the corresponding affine combination of its
original score and the center score. -/
theorem diamondRegularizedDual_score {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (θ : ℝ) (y : DiamondConstraints D E) :
    (diamondProgram T).dualScore (diamondRegularizedDual T θ y) =
      (1-θ) * (diamondProgram T).dualScore y + θ * (diamondProgram T).dualScore (diamondDualCenter T) := by
  simp only [diamondRegularizedDual,Program.dualScore,inner_add_right,real_inner_smul_right]

/-- For positive input dimension and tolerance, there is a ball of strictly dual feasible points
with scores within the tolerance above the diamond optimum. The ball has the stated uniform
slack margin and norm bound. -/
theorem diamondProgram_near_optimal_ball {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (z : DiamondConstraints D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α ∧
      0 ≤ α ∧ α ≤ E * ‖MatrixMap.choi_matrix T‖ ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      ∀ h : DiamondConstraints D E, ‖h‖ ≤ diamondRoundingRadius T ε →
        (diamondRegularizationWeight T ε/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
          (diamondProgram T).constraint.adjoint (z+h) - (diamondProgram T).objective ∧
        ((diamondProgram T).constraint.adjoint (z+h) - (diamondProgram T).objective).mat.PosDef ∧
        α ≤ (diamondProgram T).dualScore (z+h) ∧ (diamondProgram T).dualScore (z+h) < α+ε ∧
        ‖z+h‖ ≤ (D+1 : ℝ) * (E * ‖MatrixMap.choi_matrix T‖ + ε) := by
  obtain ⟨α,M,y,hnorm,hM,hy,hp,hd,hsM,hsy,hlo,hu,hsize⟩ := diamondProgram_bounded_optimizers hD T
  let θ := diamondRegularizationWeight T ε
  have hθ : 0 < θ := diamondRegularizationWeight_pos T hε
  have hθ1 : θ ≤ 1 := diamondRegularizationWeight_le_one T ε
  refine ⟨α,M,diamondRegularizedDual T θ y,hnorm,hM,hsM,hlo,hu,hp,hd,?_⟩
  intro h hh
  have hmargin := diamondRegularizedDual_perturbation_margin T hy hθ.le hθ1 hh
  have hpd := hermitian_posDef_of_scalar_margin (by positivity : 0 < θ/2) hmargin
  have hfeas : (diamondProgram T).DualFeasible (diamondRegularizedDual T θ y+h) :=
    HermitianMat.zero_le_iff.mpr hpd.posSemidef
  have hlower : α ≤ (diamondProgram T).dualScore (diamondRegularizedDual T θ y+h) := by
    have hw :=
        (Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality (P := (diamondProgram T))) hM hfeas
    rwa [hsM] at hw
  have hweight : θ * ((diamondProgram T).dualScore (diamondDualCenter T)+1) ≤ ε/2 :=
    diamondRegularizationWeight_budget T ε
  have herror : 2 * ‖h‖ ≤ θ := by
    change ‖h‖ ≤ θ / (2 * (1+E)) at hh
    have hb := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (1+E))).mp hh
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) E) (norm_nonneg h)]
  have hv :=
      (le_abs_self _).trans (diamondDualScore_perturbation_bound T (diamondRegularizedDual T θ y) h)
  have hscore := diamondRegularizedDual_score T θ y
  rw [hsy] at hscore
  have hupp : (diamondProgram T).dualScore (diamondRegularizedDual T θ y+h) < α+ε := by
    nlinarith [mul_nonneg hθ.le hlo]
  have hbound := diamondProgram_dual_norm_le_score hD T hfeas
  refine ⟨hmargin,hpd,hlower,hupp,?_⟩
  exact hbound.trans (mul_le_mul_of_nonneg_left (hupp.le.trans (by linarith)) (by positivity))

end ChoiDualRegularization

section DyadicSdpRounding

/-- The rational dyadic payload agrees with the complex dyadic payload after embedding the
Gaussian rational matrix. -/
theorem rationalDyadicPayload_eq {I : Type*} (p : ℕ) (A : Matrix I I (ℚ × ℚ)) :
    rationalDyadicPayload p A = complexDyadicPayload p (gaussianRatMatrix A) := by
  ext i j
  · change ⌊(2 : ℚ)^p * (A i j).1⌋ = ⌊(2 : ℝ)^p * ((A i j).1 : ℝ)⌋
    norm_cast
  · change ⌊(2 : ℚ)^p * (A i j).2⌋ = ⌊(2 : ℝ)^p * ((A i j).2 : ℝ)⌋
    norm_cast

/-- Dyadic floor rounding at precision `p` has absolute error at most `1 / 2^p`. -/
theorem dyadicFloor_error (p : ℕ) (x : ℝ) :
    |(⌊(2 : ℝ)^p * x⌋ : ℝ) / (2 : ℝ)^p - x| ≤ 1 / (2 : ℝ)^p := by
  have hs : 0 < (2 : ℝ)^p := pow_pos (by norm_num) p
  have hl := Int.floor_le ((2 : ℝ)^p * x)
  have hu := Int.lt_floor_add_one ((2 : ℝ)^p * x)
  have heq : (⌊(2 : ℝ)^p * x⌋ : ℝ) / (2 : ℝ)^p - x =
      ((⌊(2 : ℝ)^p * x⌋ : ℝ) - (2 : ℝ)^p * x) / (2 : ℝ)^p := by
    field_simp
  rw [heq,abs_div,abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  rw [abs_le]
  constructor <;> linarith

/-- Each entry of a Gaussian dyadic reconstruction differs from its original complex entry by
norm at most `2 / 2^p`. -/
theorem gaussianDyadicDecode_entry_error {I : Type*} (p : ℕ) (A : Matrix I I ℂ) (i j : I) :
    ‖gaussianDyadicDecode p (complexDyadicPayload p A) i j - A i j‖ ≤ 2 / (2 : ℝ)^p := by
  have hr := dyadicFloor_error p (A i j).re
  have hi := dyadicFloor_error p (A i j).im
  have hh :=
      Complex.norm_le_abs_re_add_abs_im
      (gaussianDyadicDecode p (complexDyadicPayload p A) i j - A i j)
  change ‖_‖ ≤ 2 / (2 : ℝ)^p
  calc
    _ ≤ |(⌊(2 : ℝ)^p * (A i j).re⌋ : ℝ) / (2 : ℝ)^p - (A i j).re| +
        |(⌊(2 : ℝ)^p * (A i j).im⌋ : ℝ) / (2 : ℝ)^p - (A i j).im| := hh
    _ ≤ 1 / (2 : ℝ)^p + 1 / (2 : ℝ)^p := add_le_add hr hi
    _ = _ := by ring

/-- Each entry of a Hermitian dyadic reconstruction differs from the original matrix entry by
norm at most `2 / 2^p`. -/
theorem hermitianDyadicDecode_entry_error {I : Type*} [Fintype I]
    (p : ℕ) (Y : HermitianMat I ℂ) (i j : I) :
    ‖(hermitianDyadicDecode p (complexDyadicPayload p Y.mat) - Y).mat i j‖ ≤ 2 / (2 : ℝ)^p := by
  let R := gaussianDyadicDecode p (complexDyadicPayload p Y.mat)
  have heq : (hermitianDyadicDecode p (complexDyadicPayload p Y.mat) - Y).mat i j =
      (1/2 : ℝ) • ((R i j - Y.mat i j) + star (R j i - Y.mat j i)) := by
    change (1/2 : ℝ) • (R i j + star (R j i)) - Y.mat i j = _
    rw [star_sub,Y.H.apply i j]
    module
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  have htri := norm_add_le (R i j - Y.mat i j) (star (R j i - Y.mat j i))
  rw [norm_star] at htri
  have h1 := gaussianDyadicDecode_entry_error p Y.mat i j
  have h2 := gaussianDyadicDecode_entry_error p Y.mat j i
  change ‖R i j - Y.mat i j‖ ≤ _ at h1
  change ‖R j i - Y.mat j i‖ ≤ _ at h2
  nlinarith

/-- The square of the Hermitian matrix norm is the sum of squared entry norms. -/
theorem hermitian_norm_sq_entries {I : Type*} [Fintype I] (Y : HermitianMat I ℂ) :
    ‖Y‖^2 = ∑ i, ∑ j, ‖Y.mat i j‖^2 := by
  rw [HermitianMat.norm_eq_frobenius,← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (by positivity)

/-- A uniform nonnegative entry bound bounds the Hermitian matrix norm by the index cardinality
times that bound. -/
theorem hermitian_norm_le_card_mul_entry_bound {I : Type*} [Fintype I]
    (Y : HermitianMat I ℂ) {r : ℝ} (hr : 0 ≤ r) (hb : ∀ i j, ‖Y.mat i j‖ ≤ r) :
    ‖Y‖ ≤ Fintype.card I * r := by
  have hs : ‖Y‖^2 ≤ (Fintype.card I * r)^2 := by
    rw [hermitian_norm_sq_entries]
    calc
      _ ≤ ∑ _i : I, ∑ _j : I, r^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact (sq_le_sq₀ (norm_nonneg _) hr).mpr (hb i j)
      _ = _ := by simp; ring
  nlinarith [norm_nonneg Y,mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card I)) hr]

/-- Hermitian dyadic reconstruction at precision `p` has norm error at most twice the index
cardinality divided by `2^p`. -/
theorem hermitianDyadicDecode_error {I : Type*} [Fintype I]
    (p : ℕ) (Y : HermitianMat I ℂ) :
    ‖hermitianDyadicDecode p (complexDyadicPayload p Y.mat) - Y‖ ≤
      2 * Fintype.card I / (2 : ℝ)^p := by
  have hh := hermitian_norm_le_card_mul_entry_bound
    (hermitianDyadicDecode p (complexDyadicPayload p Y.mat) - Y)
    (by positivity : (0 : ℝ) ≤ 2 / (2 : ℝ)^p) (hermitianDyadicDecode_entry_error p Y)
  convert! hh using 1
  ring

/-- The norm of diamond dual data is at most the sum of the norms of its four coordinates. -/
theorem diamondDualData_norm_le_sum {D E : ℕ} (a b : ℝ)
    (Y W : HermitianMat (Fin E × Fin D) ℂ) :
    ‖diamondDualData a b Y W‖ ≤ ‖a‖ + ‖b‖ + ‖Y‖ + ‖W‖ := by
  have h1 := hilbertPair_norm_le_sum (WithLp.toLp 2 (a,b)) (WithLp.toLp 2 (Y,W))
  have h2 := hilbertPair_norm_le_sum a b
  have h3 := hilbertPair_norm_le_sum Y W
  change ‖diamondDualData a b Y W‖ ≤ _ at h1
  linarith

/-- Dyadic reconstruction of diamond dual data has norm error at most `(2 + 4 * E * D) / 2^p`. -/
theorem diamondDyadicDecode_error {D E : ℕ} (p : ℕ) (y : DiamondConstraints D E) :
    ‖diamondDyadicDecode p (diamondDyadicPayload p y) - y‖ ≤
      (2 + 4 * (E : ℝ) * D) / (2 : ℝ)^p := by
  let a := (WithLp.ofLp (WithLp.ofLp y).1).1
  let b := (WithLp.ofLp (WithLp.ofLp y).1).2
  let Y := (WithLp.ofLp (WithLp.ofLp y).2).1
  let W := (WithLp.ofLp (WithLp.ofLp y).2).2
  let a' := (⌊(2 : ℝ)^p * a⌋ : ℝ) / (2 : ℝ)^p
  let b' := (⌊(2 : ℝ)^p * b⌋ : ℝ) / (2 : ℝ)^p
  let Y' := hermitianDyadicDecode p (complexDyadicPayload p Y.mat)
  let W' := hermitianDyadicDecode p (complexDyadicPayload p W.mat)
  have heq : diamondDyadicDecode p (diamondDyadicPayload p y) - y =
      diamondDualData (a'-a) (b'-b) (Y'-Y) (W'-W) := by
    change diamondDualData a' b' Y' W' - diamondDualData a b Y W = _
    simp only [diamondDualData,← WithLp.toLp_sub,Prod.mk_sub_mk]
  rw [heq]
  have ha : ‖a'-a‖ ≤ 1 / (2 : ℝ)^p := dyadicFloor_error p a
  have hb : ‖b'-b‖ ≤ 1 / (2 : ℝ)^p := dyadicFloor_error p b
  have hY : ‖Y'-Y‖ ≤ 2 * (E : ℝ) * D / (2 : ℝ)^p := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,mul_assoc] using!
        hermitianDyadicDecode_error p Y
  have hW : ‖W'-W‖ ≤ 2 * (E : ℝ) * D / (2 : ℝ)^p := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,mul_assoc] using!
        hermitianDyadicDecode_error p W
  calc
    _ ≤ ‖a'-a‖ + ‖b'-b‖ + ‖Y'-Y‖ + ‖W'-W‖ := diamondDualData_norm_le_sum _ _ _ _
    _ ≤ 1/(2:ℝ)^p + 1/(2:ℝ)^p + 2*(E:ℝ)*D/(2:ℝ)^p + 2*(E:ℝ)*D/(2:ℝ)^p := by
      exact add_le_add (add_le_add (add_le_add ha hb) hY) hW
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator in

/-- If the dyadic reconstruction error fits inside the rounding radius, a dyadic dual witness
has positive definite slack and score within the tolerance above the attained primal
optimum. Its slack margin and norm satisfy the stated bounds. -/
theorem diamondProgram_dyadic_near_optimal {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {ε : ℝ} (hε : 0 < ε) (p : ℕ)
    (hp : (2 + 4 * (E : ℝ) * D) / (2 : ℝ)^p ≤ diamondRoundingRadius T ε) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (P : DiamondDyadicData D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      (diamondRegularizationWeight T ε/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
        (diamondProgram T).constraint.adjoint (diamondDyadicDecode p P) - (diamondProgram T).objective ∧
      ((diamondProgram T).constraint.adjoint (diamondDyadicDecode p P) - (diamondProgram T).objective).mat.PosDef ∧
      α ≤ (diamondProgram T).dualScore (diamondDyadicDecode p P) ∧
      (diamondProgram T).dualScore (diamondDyadicDecode p P) < α+ε ∧
      ‖diamondDyadicDecode p P‖ ≤ (D+1 : ℝ) * (E * ‖MatrixMap.choi_matrix T‖ + ε) := by
  obtain ⟨α,M,z,hnorm,hM,hsM,hlo,hu,hpr,hdu,hball⟩ := diamondProgram_near_optimal_ball hD T hε
  let P := diamondDyadicPayload p z
  have herr : ‖diamondDyadicDecode p P-z‖ ≤ diamondRoundingRadius T ε :=
    (diamondDyadicDecode_error p z).trans hp
  have hh := hball (diamondDyadicDecode p P-z) herr
  rw [add_sub_cancel] at hh
  exact ⟨α,M,P,hnorm,hM,hsM,hpr,hdu,hh⟩

/-- If `q` bounds `c / r` for positive `r`, precision `dyadicPrecision q` makes `c / 2^p` at
most `r`. -/
theorem dyadicPrecision_sufficient {c r : ℝ} (hr : 0 < r) (q : ℕ) (hq : c/r ≤ q) :
    c / (2 : ℝ)^(dyadicPrecision q) ≤ r := by
  have hn := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q
  rw [← Nat.log2_eq_log_two] at hn
  have hp : (q : ℝ) < (2 : ℝ)^(dyadicPrecision q) := by exact_mod_cast hn
  have hc := (div_le_iff₀ hr).mp hq
  have hh := mul_le_mul_of_nonneg_right hp.le hr.le
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  nlinarith

/-- The selected diamond dyadic precision makes the reconstruction error bound fit within the
rounding radius. -/
theorem diamondDyadicPrecision_sufficient {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {ε : ℝ} (hε : 0 < ε) :
    (2 + 4 * (E : ℝ) * D) / (2 : ℝ)^(diamondDyadicPrecision T ε) ≤ diamondRoundingRadius T ε :=
  dyadicPrecision_sufficient (diamondRoundingRadius_pos T hε) _ (Nat.le_ceil _)

open scoped Matrix.Norms.L2Operator in

/-- For positive input dimension and tolerance, the selected precision yields a dyadic dual
witness with positive definite slack and score within the tolerance above the diamond
optimum. A primal optimizer and the stated slack and norm bounds hold simultaneously. -/
theorem diamondProgram_dyadic_witness {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (P : DiamondDyadicData D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      (diamondRegularizationWeight T ε/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
        (diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondDyadicPrecision T ε) P) -
          (diamondProgram T).objective ∧
      ((diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondDyadicPrecision T ε) P) -
        (diamondProgram T).objective).mat.PosDef ∧
      α ≤ (diamondProgram T).dualScore (diamondDyadicDecode (diamondDyadicPrecision T ε) P) ∧
      (diamondProgram T).dualScore (diamondDyadicDecode (diamondDyadicPrecision T ε) P) < α+ε ∧
      ‖diamondDyadicDecode (diamondDyadicPrecision T ε) P‖ ≤
        (D+1 : ℝ) * (E * ‖MatrixMap.choi_matrix T‖ + ε) :=
  diamondProgram_dyadic_near_optimal hD T hε _ (diamondDyadicPrecision_sufficient T hε)

/-- Embedding the rational Hermitian dyadic decoder gives the matrix of the complex Hermitian
dyadic decoder. -/
theorem hermitianDyadicRatDecode_correct {I : Type*} [Fintype I] (p : ℕ) (P : GaussianDyadicPayload I) :
    gaussianRatMatrix (hermitianDyadicRatDecode p P) = (hermitianDyadicDecode p P).mat := by
  ext i j
  change gaussianRatMatrix (hermitianDyadicRatDecode p P) i j =
    ((1/2 : ℝ) • (gaussianDyadicDecode p P + (gaussianDyadicDecode p P)ᴴ)) i j
  apply Complex.ext
  all_goals
    simp [gaussianRatMatrix,hermitianDyadicRatDecode,gaussianDyadicDecode,Matrix.conjTranspose_apply,pow_succ]
    ring

end DyadicSdpRounding

section DyadicSdpWords

/-- The norm of each Hermitian matrix entry is at most the norm of the matrix. -/
theorem hermitian_entry_norm_le {I : Type*} [Fintype I] (Y : HermitianMat I ℂ) (i j : I) :
    ‖Y.mat i j‖ ≤ ‖Y‖ := by
  have h1 : ‖Y.mat i j‖^2 ≤ ∑ k, ‖Y.mat i k‖^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖Y.mat i k‖) (Finset.mem_univ j)
  have h2 : (∑ k, ‖Y.mat i k‖^2) ≤ ∑ l, ∑ k, ‖Y.mat l k‖^2 :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg ‖Y.mat l k‖)) (Finset.mem_univ i)
  rw [← hermitian_norm_sq_entries] at h2
  nlinarith [norm_nonneg (Y.mat i j),norm_nonneg Y]

/-- An absolute bound `R` on a real number bounds its scaled dyadic floor magnitude by `2^p * R
+ 1`. -/
theorem dyadicFloor_magnitude (p : ℕ) {x R : ℝ} (hx : |x| ≤ R) :
    |(⌊(2 : ℝ)^p*x⌋ : ℝ)| ≤ (2 : ℝ)^p*R + 1 := by
  have hs : 0 ≤ (2 : ℝ)^p := by positivity
  have hl := Int.floor_le ((2 : ℝ)^p*x)
  have hu := Int.sub_one_lt_floor ((2 : ℝ)^p*x)
  have hxp := mul_le_mul_of_nonneg_left ((le_abs_self x).trans hx) hs
  have hxn := mul_le_mul_of_nonneg_left ((neg_le_neg hx).trans (neg_abs_le x)) hs
  rw [abs_le]
  constructor <;> linarith

/-- A norm bound on a Hermitian matrix bounds both integer coordinates of each complex dyadic
payload entry by `2^p * R + 1`. -/
theorem complexDyadicPayload_magnitude {I : Type*} [Fintype I] (p : ℕ)
    (Y : HermitianMat I ℂ) {R : ℝ} (hY : ‖Y‖ ≤ R) (i j : I) :
    |((complexDyadicPayload p Y.mat i j).1 : ℝ)| ≤ (2 : ℝ)^p*R + 1 ∧
    |((complexDyadicPayload p Y.mat i j).2 : ℝ)| ≤ (2 : ℝ)^p*R + 1 := by
  refine ⟨dyadicFloor_magnitude p ?_,dyadicFloor_magnitude p ?_⟩
  · exact (Complex.abs_re_le_norm _).trans ((hermitian_entry_norm_le Y i j).trans hY)
  · exact (Complex.abs_im_le_norm _).trans ((hermitian_entry_norm_le Y i j).trans hY)

/-- The Gaussian dyadic word encoding has length `gaussianDyadicWordCount D E`. -/
@[simp] theorem gaussianDyadicWords_length {D E : ℕ} (P : GaussianDyadicPayload (Fin E × Fin D)) :
    (gaussianDyadicWords P).length = gaussianDyadicWordCount D E := List.length_ofFn

/-- Decoding the Gaussian dyadic word encoding recovers the original payload. -/
@[simp] theorem gaussianDyadicFromWords_words {D E : ℕ} (P : GaussianDyadicPayload (Fin E × Fin D)) :
    gaussianDyadicFromWords D E (gaussianDyadicWords P) = P := by
  funext i j
  apply Prod.ext
  · simp [gaussianDyadicFromWords,gaussianDyadicWords,gaussianDyadicWord]
  · simp [gaussianDyadicFromWords,gaussianDyadicWords,gaussianDyadicWord]

/-- The diamond dyadic word encoding has length `diamondDyadicWordCount D E`. -/
@[simp] theorem diamondDyadicWords_length {D E : ℕ} (P : DiamondDyadicData D E) :
    (diamondDyadicWords P).length = diamondDyadicWordCount D E := by
  simp [diamondDyadicWords,diamondDyadicWordCount]
  omega

/-- The diamond dyadic word count is `2 + 4 * (E * D)^2`. -/
theorem diamondDyadicWordCount_eq (D E : ℕ) : diamondDyadicWordCount D E = 2 + 4*(E*D)^2 := by
  unfold diamondDyadicWordCount gaussianDyadicWordCount
  ring

/-- Decoding a diamond dyadic word encoding succeeds and recovers its original data. -/
@[simp] theorem diamondDyadicFromWords_words {D E : ℕ} (P : DiamondDyadicData D E) :
    diamondDyadicFromWords D E (diamondDyadicWords P) = some P := by
  unfold diamondDyadicFromWords
  rw [if_pos (diamondDyadicWords_length P)]
  cases P with
  | mk a b Y W =>
    simp [diamondDyadicWords,List.drop_append]

/-- The rational dyadic word width equals the real dyadic word width after coercing the radius. -/
theorem rationalDyadicWordWidth_eq (p : ℕ) (R : ℚ) :
    rationalDyadicWordWidth p R = dyadicWordWidth p (R : ℝ) := by
  unfold rationalDyadicWordWidth dyadicWordWidth
  congr 1
  rw [← Int.ceil_toNat,← Int.ceil_toNat]
  congr 1
  norm_cast

/-- The dyadic word width bounds the natural absolute value of every integer satisfying the
prescribed scaled magnitude bound. -/
theorem dyadicWordWidth_bound (p : ℕ) (R : ℝ) {n : ℤ}
    (hn : |(n : ℝ)| ≤ (2 : ℝ)^p*R + 1) : n.natAbs < 2^(dyadicWordWidth p R) := by
  have hq := Nat.le_ceil ((2 : ℝ)^p*R + 1)
  have hpow := Nat.lt_pow_succ_log_self (by decide : 1 < 2) ⌈(2 : ℝ)^p*R + 1⌉₊
  rw [← Nat.log2_eq_log_two] at hpow
  have hp : (⌈(2 : ℝ)^p*R + 1⌉₊ : ℝ) < (2 : ℝ)^(dyadicWordWidth p R) := by
    dsimp only [dyadicWordWidth,dyadicPrecision]
    exact_mod_cast hpow
  have hr : |(n : ℝ)| < (2 : ℝ)^(dyadicWordWidth p R) := hn.trans_lt (hq.trans_lt hp)
  have hi : |n| < (2 : ℤ)^(dyadicWordWidth p R) := by exact_mod_cast hr
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

/-- A uniform bound on both Gaussian integer coordinates of a payload bounds every integer in
its word encoding. -/
theorem gaussianDyadicWords_magnitude {D E : ℕ} (P : GaussianDyadicPayload (Fin E × Fin D))
    {R : ℝ} (hP : ∀ i j, |((P i j).1 : ℝ)| ≤ R ∧ |((P i j).2 : ℝ)| ≤ R) :
    ∀ n ∈ gaussianDyadicWords P, |(n : ℝ)| ≤ R := by
  intro n hn
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hn
  dsimp only [gaussianDyadicWord]
  split_ifs
  · exact (hP _ _).1
  · exact (hP _ _).2

/-- A norm bound `R` on diamond dual data gives the word bound `dyadicWordWidth p R` for its
dyadic payload. -/
theorem diamondDyadicPayload_word_bound {D E : ℕ} (p : ℕ) (y : DiamondConstraints D E)
    {R : ℝ} (hy : ‖y‖ ≤ R) : (diamondDyadicPayload p y).WordBound (dyadicWordWidth p R) := by
  obtain ⟨ha,hb,hY,hW⟩ := stinespringDual_coordinates_norm_le y
  have hsa := dyadicFloor_magnitude p (ha.trans hy)
  have hsb := dyadicFloor_magnitude p (hb.trans hy)
  have hsY := gaussianDyadicWords_magnitude _ (complexDyadicPayload_magnitude p _ (hY.trans hy))
  have hsW := gaussianDyadicWords_magnitude _ (complexDyadicPayload_magnitude p _ (hW.trans hy))
  intro n hn
  apply dyadicWordWidth_bound p R
  change n ∈ [_,_] ++ gaussianDyadicWords _ ++ gaussianDyadicWords _ at hn
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with ((h | h) | h) | h
  · subst n
    exact hsa
  · subst n
    exact hsb
  · exact hsY _ h
  · exact hsW _ h

/-- The diamond dyadic word decoder rejects lists whose length differs from the required word
count. -/
theorem diamondDyadicFromWords_reject_length {D E : ℕ} {xs : List ℤ}
    (h : xs.length ≠ diamondDyadicWordCount D E) : diamondDyadicFromWords D E xs = none := by
  exact if_neg h

/-- For positive input dimension and tolerance, a bounded dyadic word witness decodes to a
strictly dual feasible point within the tolerance above the diamond optimum. Its encoding
has `2 + 4 * (E * D)^2` words and satisfies the prescribed width and outer size bounds. -/
theorem diamondProgram_bounded_dyadic_words {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (P : DiamondDyadicData D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      P.WordBound (diamondDyadicWordWidth T ε) ∧
      (diamondDyadicWords P).length = 2 + 4*(E*D)^2 ∧
      diamondDyadicFromWords D E (diamondDyadicWords P) = some P ∧
      (diamondRegularizationWeight T ε/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
        (diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondDyadicPrecision T ε) P) -
          (diamondProgram T).objective ∧
      ((diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondDyadicPrecision T ε) P) -
        (diamondProgram T).objective).mat.PosDef ∧
      α ≤ (diamondProgram T).dualScore (diamondDyadicDecode (diamondDyadicPrecision T ε) P) ∧
      (diamondProgram T).dualScore (diamondDyadicDecode (diamondDyadicPrecision T ε) P) < α+ε ∧
      ‖diamondDyadicDecode (diamondDyadicPrecision T ε) P‖ ≤ diamondDyadicOuterSize T ε := by
  obtain ⟨α,M,z,hnorm,hM,hsM,hlo,hu,hpr,hdu,hball⟩ := diamondProgram_near_optimal_ball hD T hε
  let p := diamondDyadicPrecision T ε
  let P := diamondDyadicPayload p z
  have hz : ‖z‖ ≤ diamondDyadicOuterSize T ε := by
    have h0 := hball 0 (by simpa only [norm_zero] using! (diamondRoundingRadius_pos T hε).le)
    simpa only [add_zero,diamondDyadicOuterSize] using! h0.2.2.2.2
  have hb : P.WordBound (diamondDyadicWordWidth T ε) := diamondDyadicPayload_word_bound p z hz
  have herr : ‖diamondDyadicDecode p P-z‖ ≤ diamondRoundingRadius T ε :=
    (diamondDyadicDecode_error p z).trans (diamondDyadicPrecision_sufficient T hε)
  have hh := hball (diamondDyadicDecode p P-z) herr
  rw [add_sub_cancel] at hh
  refine ⟨α,M,P,hnorm,hM,hsM,hpr,hdu,hb,?_,diamondDyadicFromWords_words P,hh⟩
  rw [diamondDyadicWords_length,diamondDyadicWordCount_eq]

end DyadicSdpWords

section DyadicSdpBinaryCodec

/-- The bit list of a bit vector has length equal to its width. -/
@[simp] theorem dyadicBitVecBits_length {w : ℕ} (v : BitVec w) :
    (dyadicBitVecBits v).length = w := List.length_ofFn

/-- Reconstructing a bit vector from its little-endian bit list preserves its signed integer
value. -/
theorem dyadicBitVecBits_toInt {w : ℕ} (v : BitVec w) :
    (BitVec.ofBoolListLE (dyadicBitVecBits v)).toInt = v.toInt := by
  have heq : (BitVec.ofBoolListLE (dyadicBitVecBits v)).cast (dyadicBitVecBits_length v) = v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    simp [dyadicBitVecBits,hi]
  have hh := congrArg BitVec.toInt heq
  simpa only [BitVec.toInt_eq_toNat_cond,BitVec.toNat_cast,dyadicBitVecBits_length] using! hh

/-- The signed dyadic encoding of one integer uses `b + 1` bits. -/
@[simp] theorem signedDyadicWordBits_length (b : ℕ) (n : ℤ) :
    (signedDyadicWordBits b n).length = b+1 := List.length_ofFn

/-- Decoding a signed dyadic word recovers the original integer when its natural absolute value
is below `2^b`. -/
theorem signedDyadicWord_roundtrip (b : ℕ) (n : ℤ) (hn : n.natAbs < 2^b) :
    signedDyadicWordFromBits (signedDyadicWordBits b n) = n := by
  have ha : |n| < (2 : ℤ)^b := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  obtain ⟨hl,hu⟩ := abs_lt.mp ha
  have hp := BitVec.toInt_ofInt_eq_self (by omega : 0 < b+1)
    (by simpa only [Nat.add_sub_cancel] using! hl.le)
    (by simpa only [Nat.add_sub_cancel] using! hu)
  exact (dyadicBitVecBits_toInt (BitVec.ofInt (b+1) n)).trans hp

/-- Encoding a list of signed dyadic words uses the list length times `b + 1` bits. -/
theorem signedDyadicWordsBits_length (b : ℕ) (xs : List ℤ) :
    (signedDyadicWordsBits b xs).length = xs.length*(b+1) := by
  induction xs with
  | nil => simp [signedDyadicWordsBits]
  | cons n xs ih =>
    change (signedDyadicWordBits b n ++ signedDyadicWordsBits b xs).length = (xs.length+1)*(b+1)
    rw [List.length_append,signedDyadicWordBits_length,ih]
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Reading the signed dyadic encoding recovers every word when all natural absolute values are
below `2^b`. -/
theorem signedDyadicWordsRead_bits (b : ℕ) (xs : List ℤ)
    (h : ∀ n ∈ xs, n.natAbs < 2^b) :
    signedDyadicWordsRead b xs.length (signedDyadicWordsBits b xs) = xs := by
  revert h
  induction xs with
  | nil => intro h; rfl
  | cons n xs ih =>
    intro h
    have hn : n.natAbs < 2^b := h n (List.mem_cons_self)
    have ht : ∀ k ∈ xs, k.natAbs < 2^b := fun k hk => h k (List.mem_cons_of_mem n hk)
    have htake : (signedDyadicWordBits b n ++ signedDyadicWordsBits b xs).take (b+1) = signedDyadicWordBits b n := by
      rw [← signedDyadicWordBits_length b n]
      exact List.take_left
    have hdrop : (signedDyadicWordBits b n ++ signedDyadicWordsBits b xs).drop (b+1) = signedDyadicWordsBits b xs := by
      rw [← signedDyadicWordBits_length b n]
      exact List.drop_left
    change signedDyadicWordFromBits ((signedDyadicWordBits b n ++ signedDyadicWordsBits b xs).take (b+1)) ::
      signedDyadicWordsRead b xs.length ((signedDyadicWordBits b n ++ signedDyadicWordsBits b xs).drop (b+1)) = n :: xs
    rw [htake,hdrop,signedDyadicWord_roundtrip b n hn,ih ht]

/-- The diamond dyadic bit encoding has length `diamondDyadicBitCount D E b`. -/
@[simp] theorem diamondDyadicBits_length {D E : ℕ} (b : ℕ) (P : DiamondDyadicData D E) :
    (diamondDyadicBits b P).length = diamondDyadicBitCount D E b := by
  rw [diamondDyadicBits,signedDyadicWordsBits_length,diamondDyadicWords_length]
  rfl

/-- The diamond dyadic bit count is `(2 + 4 * (E * D)^2) * (b + 1)`. -/
theorem diamondDyadicBitCount_eq (D E b : ℕ) :
    diamondDyadicBitCount D E b = (2+4*(E*D)^2)*(b+1) := by
  rw [diamondDyadicBitCount,diamondDyadicWordCount_eq]

/-- The diamond dyadic bit decoder recovers the original data when the word bound holds. -/
theorem diamondDyadicFromBits_bits {D E : ℕ} (b : ℕ) (P : DiamondDyadicData D E)
    (hP : P.WordBound b) : diamondDyadicFromBits D E b (diamondDyadicBits b P) = some P := by
  unfold diamondDyadicFromBits
  rw [if_pos (diamondDyadicBits_length b P)]
  rw [diamondDyadicBits,← diamondDyadicWords_length P,signedDyadicWordsRead_bits b _ hP]
  exact diamondDyadicFromWords_words P

/-- The diamond dyadic bit decoder rejects lists of an incorrect length. -/
theorem diamondDyadicFromBits_reject_length {D E b : ℕ} {bs : List Bool}
    (h : bs.length ≠ diamondDyadicBitCount D E b) : diamondDyadicFromBits D E b bs = none := if_neg h

/-- For positive input dimension and tolerance, a bounded dyadic dual witness has a binary
encoding that decodes exactly and yields a strictly dual feasible point within the tolerance
above the diamond optimum. The bit count is `(2 + 4 * (E * D)^2) * (diamondDyadicWordWidth T
ε + 1)`. -/
theorem diamondProgram_binary_dyadic_witness {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (P : DiamondDyadicData D E) (bs : List Bool),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      P.WordBound (diamondDyadicWordWidth T ε) ∧
      bs = diamondDyadicBits (diamondDyadicWordWidth T ε) P ∧
      bs.length = (2+4*(E*D)^2)*(diamondDyadicWordWidth T ε+1) ∧
      diamondDyadicFromBits D E (diamondDyadicWordWidth T ε) bs = some P ∧
      (diamondRegularizationWeight T ε/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
        (diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondDyadicPrecision T ε) P) -
          (diamondProgram T).objective ∧
      ((diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondDyadicPrecision T ε) P) -
        (diamondProgram T).objective).mat.PosDef ∧
      α ≤ (diamondProgram T).dualScore (diamondDyadicDecode (diamondDyadicPrecision T ε) P) ∧
      (diamondProgram T).dualScore (diamondDyadicDecode (diamondDyadicPrecision T ε) P) < α+ε ∧
      ‖diamondDyadicDecode (diamondDyadicPrecision T ε) P‖ ≤ diamondDyadicOuterSize T ε := by
  obtain ⟨α,M,P,hnorm,hM,hsM,hpr,hdu,hbound,hlen,hparse,hmargin,hpd,hl,hu,hsize⟩ :=
    diamondProgram_bounded_dyadic_words hD T hε
  refine ⟨α,M,P,diamondDyadicBits (diamondDyadicWordWidth T ε) P,
    hnorm,hM,hsM,hpr,hdu,hbound,rfl,?_,?_,hmargin,hpd,hl,hu,hsize⟩
  · rw [diamondDyadicBits_length,diamondDyadicBitCount_eq]
  · exact diamondDyadicFromBits_bits _ P hbound

end DyadicSdpBinaryCodec

section RationalPsdDecision

/-- The real part of the Gaussian rational embedding is the coerced rational real part. -/
@[simp] theorem gaussianRationalEmbed_re (z : GaussianRational) : (gaussianRationalEmbed z).re = z.re := rfl

/-- The imaginary part of the Gaussian rational embedding is the coerced rational imaginary
part. -/
@[simp] theorem gaussianRationalEmbed_im (z : GaussianRational) : (gaussianRationalEmbed z).im = z.im := rfl

/-- Embedding Gaussian rationals commutes with conjugation. -/
@[simp] theorem gaussianRationalEmbed_star (z : GaussianRational) :
    gaussianRationalEmbed (star z) = star (gaussianRationalEmbed z) := by
  apply Complex.ext <;> simp
      [gaussianRationalEmbed,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]

/-- The embedding of Gaussian rationals into complex numbers is injective. -/
theorem gaussianRationalEmbed_injective : Function.Injective gaussianRationalEmbed :=
    gaussianRationalEmbed.injective

/-- A Gaussian rational matrix is Hermitian exactly when its complex embedding is Hermitian. -/
theorem gaussianRationalMatrix_hermitian_iff {I : Type*} (Q : Matrix I I GaussianRational) :
    (gaussianRationalMatrix Q).IsHermitian ↔ Q.IsHermitian :=
  Matrix.isHermitian_map_iff (fun z => gaussianRationalEmbed_star z) gaussianRationalEmbed_injective

/-- Converting a Gaussian rational matrix to a table and back recovers the matrix. -/
@[simp] theorem gaussianRationalTableMatrix_table {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational) :
    gaussianRationalTableMatrix (gaussianRationalTable Q) = Q := by
  funext i j
  simp [gaussianRationalTableMatrix,gaussianRationalTable]

/-- The leading diagonal entry of a Hermitian Gaussian rational matrix has zero imaginary part. -/
theorem gaussianRational_head_real {n : ℕ} {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational}
    (hQ : Q.IsHermitian) : (Q 0 0).im = 0 := by
  have h := congrArg (fun z : GaussianRational => z.im) (hQ.apply 0 0)
  simp only [QuadraticAlgebra.im_star] at h
  linarith

/-- The index equivalence splitting off the first coordinate of `Fin (n + 1)` as `Fin 1 ⊕ Fin
n`. -/
def psdHeadEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl 0) Sum.inr
  left_inv x := by
    cases x with
    | inl i => have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl
    | inr j => rfl
  right_inv x := by
    refine Fin.cases ?_ (fun j => ?_) x <;> rfl

/-- Reindexing a Hermitian Gaussian rational matrix by `psdHeadEquiv` displays its leading
entry, first row and column, and tail as a block matrix. -/
theorem gaussianRational_block {n : ℕ} {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational}
    (hQ : Q.IsHermitian) :
    (gaussianRationalMatrix Q).submatrix (psdHeadEquiv n) (psdHeadEquiv n) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 1 => gaussianRationalEmbed (Q 0 0)))
        (fun (_ : Fin 1) (j : Fin n) => gaussianRationalEmbed (Q 0 j.succ))
        (fun (i : Fin n) (_ : Fin 1) => star (gaussianRationalEmbed (Q 0 i.succ)))
        (gaussianRationalMatrix (gaussianRationalTail Q)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => fin_cases i; fin_cases j; rfl
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j =>
      change gaussianRationalEmbed (Q i.succ 0) = star (gaussianRationalEmbed (Q 0 i.succ))
      rw [← gaussianRationalEmbed_star,hQ.apply i.succ 0]
    | inr j => rfl

/-- The real part of the leading diagonal entry of a positive semidefinite Gaussian rational
matrix is nonnegative. -/
theorem gaussianRational_psd_head_nonneg {n : ℕ} {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational}
    (hQ : (gaussianRationalMatrix Q).PosSemidef) : 0 ≤ (Q 0 0).re := by
  have h := (RCLike.nonneg_iff.mp (hQ.diag_nonneg (i := 0))).1
  change (0 : ℝ) ≤ ((Q 0 0).re : ℝ) at h
  exact_mod_cast h

/-- If the leading diagonal real part of a positive semidefinite Gaussian rational matrix
vanishes, all remaining entries of its first row vanish. -/
theorem gaussianRational_psd_zero_row {n : ℕ} {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational}
    (hQ : (gaussianRationalMatrix Q).PosSemidef) (hz : (Q 0 0).re = 0) :
    ∀ j : Fin n, Q 0 j.succ = 0 := by
  intro j
  let H : HermitianMat (Fin (n+1)) ℂ := ⟨gaussianRationalMatrix Q,hQ.1⟩
  have hh : (H.mat 0 0).re = 0 := by
    change ((Q 0 0).re : ℝ) = 0
    exact_mod_cast hz
  have h := zero_diagonal_row H (HermitianMat.zero_le_iff.mpr hQ) 0 hh j.succ
  change gaussianRationalEmbed (Q 0 j.succ) = 0 at h
  apply gaussianRationalEmbed_injective
  simpa only [map_zero] using! h

/-- The leading diagonal entry of a Hermitian Gaussian rational matrix embeds as its real part. -/
theorem gaussianRational_head_embed {n : ℕ} {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational}
    (hQ : Q.IsHermitian) : gaussianRationalEmbed (Q 0 0) = ((Q 0 0).re : ℂ) := by
  apply Complex.ext <;> simp [gaussianRationalEmbed,gaussianRational_head_real hQ]

/-- For a Hermitian Gaussian rational matrix with positive leading diagonal real part, positive
semidefiniteness is equivalent to that of its Schur complement. -/
theorem gaussianRational_psd_schur_iff {n : ℕ}
    {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational} (hQ : Q.IsHermitian)
    (hp : 0 < (Q 0 0).re) :
    (gaussianRationalMatrix Q).PosSemidef ↔ (gaussianRationalMatrix (gaussianRationalSchur Q)).PosSemidef := by
  let A : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal (fun _ => gaussianRationalEmbed (Q 0 0))
  let B : Matrix (Fin 1) (Fin n) ℂ := fun _ j => gaussianRationalEmbed (Q 0 j.succ)
  let D := gaussianRationalMatrix (gaussianRationalTail Q)
  have hA : A.PosDef := Matrix.PosDef.diagonal fun _ => by
    rw [gaussianRational_head_embed hQ]
    rw [RCLike.pos_iff]
    constructor
    · simpa using! (Rat.cast_pos.mpr hp : (0 : ℝ) < ((Q 0 0).re : ℝ))
    · simp
  letI : Invertible A := hA.isUnit.invertible
  have hblock : (gaussianRationalMatrix Q).submatrix (psdHeadEquiv n) (psdHeadEquiv n) =
      Matrix.fromBlocks A B Bᴴ D := gaussianRational_block hQ
  have hschur : gaussianRationalMatrix (gaussianRationalSchur Q) = D - Bᴴ * A⁻¹ * B := by
    ext i j
    have hl : gaussianRationalEmbed (Q i.succ 0) = star (gaussianRationalEmbed (Q 0 i.succ)) := by
      rw [← gaussianRationalEmbed_star,hQ.apply i.succ 0]
    simp only [gaussianRationalMatrix,gaussianRationalSchur,gaussianRationalTail,Matrix.map_apply,map_sub,map_mul,map_inv₀,
      D,B,A,Matrix.sub_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.inv_subsingleton,
      Matrix.diagonal_apply,Fin.sum_univ_one,if_true,hl,Ring.inverse_eq_inv]
  rw [← Matrix.posSemidef_submatrix_equiv (psdHeadEquiv n),hblock,
    Matrix.PosDef.fromBlocks₁₁ B D hA,← hschur]

/-- For a Hermitian Gaussian rational matrix with zero leading diagonal real part and zero
remaining first row, positive semidefiniteness is equivalent to that of its tail. -/
theorem gaussianRational_psd_zero_iff {n : ℕ}
    {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational} (hQ : Q.IsHermitian)
    (hz : (Q 0 0).re = 0) (hr : ∀ j : Fin n, Q 0 j.succ = 0) :
    (gaussianRationalMatrix Q).PosSemidef ↔ (gaussianRationalMatrix (gaussianRationalTail Q)).PosSemidef := by
  constructor
  · intro h
    exact h.submatrix Fin.succ
  · intro htail
    have hzero : Q 0 0 = 0 := by
      apply QuadraticAlgebra.ext
      · exact hz
      · exact gaussianRational_head_real hQ
    let T : HermitianMat (Fin n) ℂ := ⟨gaussianRationalMatrix (gaussianRationalTail Q),htail.1⟩
    have heq : (gaussianRationalMatrix Q).submatrix (psdHeadEquiv n) (psdHeadEquiv n) =
        (directSum (0 : HermitianMat (Fin 1) ℂ) T).mat := by
      rw [gaussianRational_block hQ]
      ext i j
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          change (Matrix.diagonal (fun _ : Fin 1 => gaussianRationalEmbed (Q 0 0))) i j = 0
          simp [hzero]
        | inr j =>
          change gaussianRationalEmbed (Q 0 j.succ) = 0
          rw [hr j,map_zero]
      | inr i =>
        cases j with
        | inl j =>
          change star (gaussianRationalEmbed (Q 0 i.succ)) = 0
          rw [hr i,map_zero,star_zero]
        | inr j => rfl
    apply (Matrix.posSemidef_submatrix_equiv (psdHeadEquiv n)).mp
    rw [heq]
    exact HermitianMat.zero_le_iff.mp
        (directSum_nonneg (le_refl 0) (HermitianMat.zero_le_iff.mpr htail))

/-- The recursive Gaussian rational positivity checker returns true exactly when the complex
matrix represented by its table is positive semidefinite. -/
theorem gaussianRationalPsdCore_correct (n : ℕ) (A : GaussianRationalTable n) :
    gaussianRationalPsdCore n A = true ↔
      (gaussianRationalMatrix (gaussianRationalTableMatrix A)).PosSemidef := by
  induction n with
  | zero =>
    have hz : gaussianRationalMatrix (gaussianRationalTableMatrix A) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact ⟨fun _ => Matrix.PosSemidef.zero,fun _ => rfl⟩
  | succ n ih =>
    let Q := gaussianRationalTableMatrix A
    change (if Q.IsHermitian then
      if (Q 0 0).re < 0 then false
      else if (Q 0 0).re = 0 then
        if ∀ j : Fin n, Q 0 j.succ = 0 then gaussianRationalPsdCore n (gaussianRationalTable (gaussianRationalTail Q)) else false
      else gaussianRationalPsdCore n (gaussianRationalTable (gaussianRationalSchur Q))
      else false) = true ↔ (gaussianRationalMatrix Q).PosSemidef
    by_cases hQ : Q.IsHermitian
    · rw [if_pos hQ]
      by_cases hn : (Q 0 0).re < 0
      · rw [if_pos hn]
        simp only [Bool.false_eq_true,false_iff]
        intro h
        exact (not_lt_of_ge (gaussianRational_psd_head_nonneg h)) hn
      · rw [if_neg hn]
        by_cases hz : (Q 0 0).re = 0
        · rw [if_pos hz]
          by_cases hr : ∀ j : Fin n, Q 0 j.succ = 0
          · rw [if_pos hr,ih,gaussianRationalTableMatrix_table]
            exact (gaussianRational_psd_zero_iff hQ hz hr).symm
          · rw [if_neg hr]
            simp only [Bool.false_eq_true,false_iff]
            intro h
            exact hr (gaussianRational_psd_zero_row h hz)
        · rw [if_neg hz,ih,gaussianRationalTableMatrix_table]
          have hp : 0 < (Q 0 0).re := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
          exact (gaussianRational_psd_schur_iff hQ hp).symm
    · rw [if_neg hQ]
      simp only [Bool.false_eq_true,false_iff]
      intro h
      exact hQ ((gaussianRationalMatrix_hermitian_iff Q).mp h.1)

/-- The Gaussian rational positivity check returns true exactly when the represented complex
matrix is positive semidefinite. -/
theorem gaussianRationalPsdCheck_correct {n : ℕ} (A : GaussianRationalTable n) :
    gaussianRationalPsdCheck A = true ↔
      (gaussianRationalMatrix (gaussianRationalTableMatrix A)).PosSemidef :=
  gaussianRationalPsdCore_correct n A

/-- The rational-pair positivity check returns true exactly when the corresponding complex
matrix is positive semidefinite. -/
theorem rationalPairPsdCheck_correct {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ℚ × ℚ)) :
    rationalPairPsdCheck Q = true ↔ (gaussianRatMatrix Q).PosSemidef := by
  rw [rationalPairPsdCheck,gaussianRationalPsdCheck_correct,gaussianRationalTableMatrix_table]
  rfl

/-- The dyadic block positivity check returns true exactly when the decoded Hermitian matrix is
positive semidefinite. -/
theorem dyadicBlockPsdCheck_correct (D E p : ℕ) (P : GaussianDyadicPayload (Fin E × Fin D)) :
    dyadicBlockPsdCheck D E p P = true ↔ (hermitianDyadicDecode p P).mat.PosSemidef := by
  rw [dyadicBlockPsdCheck,rationalPairPsdCheck_correct]
  change ((gaussianRatMatrix (hermitianDyadicRatDecode p P)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).PosSemidef ↔ _
  rw [Matrix.posSemidef_submatrix_equiv,hermitianDyadicRatDecode_correct]

/-- The Gaussian rational quadratic form on a vector with a leading coordinate expands into its
leading row and tail contributions. -/
theorem gaussianRationalQuadratic_cons {n : ℕ}
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) (a : GaussianRational) (v : Fin n → GaussianRational) :
    gaussianRationalQuadratic Q (Fin.cons a v) =
      star a * (Q 0 0 * a + ∑ j, Q 0 j.succ * v j) +
      ∑ i, star (v i) * (Q i.succ 0 * a + ∑ j, Q i.succ j.succ * v j) := by
  simp [gaussianRationalQuadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

/-- The quadratic form on a Schur-lifted vector equals the Schur complement quadratic form when
the leading entry is nonzero. -/
theorem gaussianRationalQuadratic_schurLift {n : ℕ}
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) (h : Q 0 0 ≠ 0)
    (v : Fin n → GaussianRational) :
    gaussianRationalQuadratic Q (gaussianRationalSchurLift Q v) =
      gaussianRationalQuadratic (gaussianRationalSchur Q) v := by
  rw [gaussianRationalSchurLift, gaussianRationalQuadratic_cons]
  have hz : Q 0 0 * (-(Q 0 0)⁻¹ * ∑ j, Q 0 j.succ * v j) + ∑ j, Q 0 j.succ * v j = 0 := by
    field_simp
    ring
  rw [hz, mul_zero, zero_add]
  simp only [gaussianRationalQuadratic, dotProduct, Matrix.mulVec, gaussianRationalSchur]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- Prepending a zero coordinate reduces the Gaussian rational quadratic form to that of the
tail matrix. -/
theorem gaussianRationalQuadratic_zeroLift {n : ℕ}
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) (v : Fin n → GaussianRational) :
    gaussianRationalQuadratic Q (Fin.cons 0 v) = gaussianRationalQuadratic (gaussianRationalTail Q) v := by
  rw [gaussianRationalQuadratic_cons]
  simp [gaussianRationalQuadratic, gaussianRationalTail, dotProduct, Matrix.mulVec]

/-- The quadratic form on a standard basis vector equals the corresponding diagonal entry. -/
theorem gaussianRationalQuadratic_single {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) GaussianRational) (j : Fin n) :
    gaussianRationalQuadratic Q (Pi.single j 1) = Q j j := by
  simp [gaussianRationalQuadratic, Pi.star_single, Matrix.mulVec_single, single_dotProduct]

/-- A nonzero cross entry beside a zero leading diagonal in a Hermitian Gaussian rational matrix
produces a cross vector with quadratic value minus one. -/
theorem gaussianRationalQuadratic_cross {n : ℕ}
    {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational} (hQ : Q.IsHermitian)
    (hz : (Q 0 0).re = 0) (j : Fin n) (hb : Q 0 j.succ ≠ 0) :
    gaussianRationalQuadratic Q (gaussianRationalCrossVector Q j) = -1 := by
  have hzero : Q 0 0 = 0 := by
    apply QuadraticAlgebra.ext
    · exact hz
    · exact gaussianRational_head_real hQ
  have hd : star (Q j.succ j.succ) = Q j.succ j.succ := hQ.apply _ _
  have hc : Q j.succ 0 = star (Q 0 j.succ) := (hQ.apply _ _).symm
  have hbs : star (Q 0 j.succ) ≠ 0 := star_ne_zero.mpr hb
  rw [gaussianRationalCrossVector, gaussianRationalQuadratic_cons]
  simp only [Pi.single_apply, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hzero, zero_mul, zero_add, ite_mul, one_mul, zero_mul]
  simp only [hc, star_div₀, star_neg, star_add, star_one, star_mul, star_ofNat, star_star, hd]
  field_simp
  ring

/-- The tail of a Hermitian Gaussian rational matrix is Hermitian. -/
theorem gaussianRationalTail_hermitian {n : ℕ}
    {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational} (hQ : Q.IsHermitian) :
    (gaussianRationalTail Q).IsHermitian := hQ.submatrix Fin.succ

/-- The Schur complement of a Hermitian Gaussian rational matrix is Hermitian. -/
theorem gaussianRationalSchur_hermitian {n : ℕ}
    {Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational} (hQ : Q.IsHermitian) :
    (gaussianRationalSchur Q).IsHermitian := by
  apply Matrix.ext
  intro i j
  change star (Q j.succ i.succ - Q j.succ 0 * (Q 0 0)⁻¹ * Q 0 i.succ) = _
  simp only [star_sub, star_mul, star_inv₀, hQ.apply]
  simp only [gaussianRationalSchur]
  ring

/-- For Hermitian Gaussian rational input, the negative-vector search returns none exactly for
positive semidefinite matrices, and every returned vector has strictly negative quadratic
real part. -/
theorem gaussianRationalNegativeCore_correct (n : ℕ) (A : GaussianRationalTable n)
    (hQ : (gaussianRationalTableMatrix A).IsHermitian) :
    (gaussianRationalNegativeCore n A = none ↔
      (gaussianRationalMatrix (gaussianRationalTableMatrix A)).PosSemidef) ∧
    ∀ v, gaussianRationalNegativeCore n A = some v →
      (gaussianRationalQuadratic (gaussianRationalTableMatrix A) (fun i => v[i])).re < 0 := by
  induction n with
  | zero =>
    constructor
    · have hz : gaussianRationalMatrix (gaussianRationalTableMatrix A) = 0 := Subsingleton.elim _ _
      simp [gaussianRationalNegativeCore, hz, Matrix.PosSemidef.zero]
    · intro v h
      simp [gaussianRationalNegativeCore] at h
  | succ n ih =>
    let Q := gaussianRationalTableMatrix A
    change (gaussianRationalNegativeCore (n+1) A = none ↔ (gaussianRationalMatrix Q).PosSemidef) ∧
      ∀ v, gaussianRationalNegativeCore (n+1) A = some v →
        (gaussianRationalQuadratic Q (fun i => v[i])).re < 0
    have heq : gaussianRationalNegativeCore (n+1) A =
        (if (Q 0 0).re < 0 then some (Vector.ofFn (Pi.single 0 1))
        else if (Q 0 0).re = 0 then
          match Fin.find? (fun j : Fin n => decide (Q 0 j.succ ≠ 0)) with
          | some j => some (Vector.ofFn (gaussianRationalCrossVector Q j))
          | none => (gaussianRationalNegativeCore n (gaussianRationalTable (gaussianRationalTail Q))).map
              (fun v => Vector.ofFn (Fin.cons 0 (fun i => v[i])))
        else (gaussianRationalNegativeCore n (gaussianRationalTable (gaussianRationalSchur Q))).map
              (fun v => Vector.ofFn (gaussianRationalSchurLift Q (fun i => v[i])))) := rfl
    rw [heq]
    by_cases hn : (Q 0 0).re < 0
    · simp only [if_pos hn]
      constructor
      · simp only [Option.some_ne_none, false_iff]
        exact fun hp => (not_lt_of_ge (gaussianRational_psd_head_nonneg hp)) hn
      · intro v hv
        cases Option.some.inj hv
        simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
            gaussianRationalQuadratic_single] using! hn
    · simp only [if_neg hn]
      by_cases hz : (Q 0 0).re = 0
      · simp only [if_pos hz]
        cases hf : Fin.find? (fun j : Fin n => decide (Q 0 j.succ ≠ 0)) with
        | none =>
          have hr : ∀ j : Fin n, Q 0 j.succ = 0 := by
            have hh := hf
            rw [Fin.find?_eq_dite] at hh
            split_ifs at hh with hex
            simpa using! hex
          have ht := ih (gaussianRationalTable (gaussianRationalTail Q)) (by
            simpa using! gaussianRationalTail_hermitian hQ)
          constructor
          · rw [Option.map_eq_none_iff, ht.1, gaussianRationalTableMatrix_table]
            exact (gaussianRational_psd_zero_iff hQ hz hr).symm
          · intro v hv
            obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
            simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, gaussianRationalQuadratic_zeroLift,
              gaussianRationalTableMatrix_table] using! ht.2 w hw
        | some j =>
          have hb : Q 0 j.succ ≠ 0 := by
            have hh : j ∈ Fin.find? (fun k : Fin n => decide (Q 0 k.succ ≠ 0)) :=
                hf.symm ▸ Option.mem_some_self j
            simpa using! (Fin.mem_find?_iff.mp hh).1
          constructor
          · simp only [Option.some_ne_none, false_iff]
            exact fun hp => hb (gaussianRational_psd_zero_row hp hz j)
          · intro v hv
            cases Option.some.inj hv
            simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
            change (gaussianRationalQuadratic Q (gaussianRationalCrossVector Q j)).re < 0
            rw [gaussianRationalQuadratic_cross hQ hz j hb]
            norm_num [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one]
      · simp only [if_neg hz]
        have hp : 0 < (Q 0 0).re := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
        have ha : Q 0 0 ≠ 0 := by intro he; simp [he] at hp
        have ht := ih (gaussianRationalTable (gaussianRationalSchur Q)) (by
          simpa using! gaussianRationalSchur_hermitian hQ)
        constructor
        · rw [Option.map_eq_none_iff, ht.1, gaussianRationalTableMatrix_table]
          exact (gaussianRational_psd_schur_iff hQ hp).symm
        · intro v hv
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
          simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, gaussianRationalQuadratic_schurLift Q ha,
            gaussianRationalTableMatrix_table] using! ht.2 w hw

/-- The Gaussian rational separator reports non-Hermitian input exactly when the represented
matrix is not Hermitian. -/
theorem gaussianRationalPsdSeparate_nonHermitian_iff {n : ℕ} (A : GaussianRationalTable n) :
    gaussianRationalPsdSeparate A = .nonHermitian ↔ ¬ (gaussianRationalTableMatrix A).IsHermitian := by
  unfold gaussianRationalPsdSeparate
  split_ifs with hQ
  · cases gaussianRationalNegativeCore n A <;> simp [hQ]
  · simp [hQ]

/-- The Gaussian rational separator reports positivity exactly when the represented complex
matrix is positive semidefinite. -/
theorem gaussianRationalPsdSeparate_psd_iff {n : ℕ} (A : GaussianRationalTable n) :
    gaussianRationalPsdSeparate A = .psd ↔
      (gaussianRationalMatrix (gaussianRationalTableMatrix A)).PosSemidef := by
  by_cases hQ : (gaussianRationalTableMatrix A).IsHermitian
  · have ht := (gaussianRationalNegativeCore_correct n A hQ).1
    unfold gaussianRationalPsdSeparate
    rw [if_pos hQ]
    cases hc : gaussianRationalNegativeCore n A <;> simpa [hc] using! ht
  · simp only [gaussianRationalPsdSeparate, if_neg hQ, reduceCtorEq, false_iff]
    intro hp
    exact hQ ((gaussianRationalMatrix_hermitian_iff _).mp hp.1)

/-- A negative-vector result certifies Hermitian input and strictly negative real quadratic
value. -/
theorem gaussianRationalPsdSeparate_negative {n : ℕ} (A : GaussianRationalTable n)
    (v : Vector GaussianRational n) (hv : gaussianRationalPsdSeparate A = .negative v) :
    (gaussianRationalTableMatrix A).IsHermitian ∧
    (gaussianRationalQuadratic (gaussianRationalTableMatrix A) (fun i => v[i])).re < 0 := by
  unfold gaussianRationalPsdSeparate at hv
  split_ifs at hv with hQ
  · cases hc : gaussianRationalNegativeCore n A with
    | none => simp [hc] at hv
    | some w =>
      simp only [hc, GaussianRationalPsdResult.negative.injEq] at hv
      subst w
      exact ⟨hQ, (gaussianRationalNegativeCore_correct n A hQ).2 v hc⟩

/-- Embedding a Gaussian rational quadratic form yields the complex matrix quadratic form on the
embedded vector. -/
theorem gaussianRationalEmbed_quadratic {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational)
    (v : Fin n → GaussianRational) :
    gaussianRationalEmbed (gaussianRationalQuadratic Q v) =
      star (gaussianRationalEmbed ∘ v) ⬝ᵥ (gaussianRationalMatrix Q *ᵥ (gaussianRationalEmbed ∘ v)) := by
  simp [gaussianRationalQuadratic, dotProduct, Matrix.mulVec, gaussianRationalMatrix,
    map_sum, gaussianRationalEmbed_star, Function.comp_def]

/-- A negative result from the Gaussian rational separator gives an embedded vector with
negative quadratic real part on the input and nonnegative quadratic real part on every
positive semidefinite matrix. -/
theorem gaussianRationalPsdSeparate_separates {n : ℕ} (A : GaussianRationalTable n)
    (v : Vector GaussianRational n) (hv : gaussianRationalPsdSeparate A = .negative v) :
    let w := fun i : Fin n => gaussianRationalEmbed v[i]
    (star w ⬝ᵥ (gaussianRationalMatrix (gaussianRationalTableMatrix A) *ᵥ w)).re < 0 ∧
    ∀ P : Matrix (Fin n) (Fin n) ℂ, P.PosSemidef → 0 ≤ (star w ⬝ᵥ (P *ᵥ w)).re := by
  (try dsimp only)
  constructor
  · have hneg := (gaussianRationalPsdSeparate_negative A v hv).2
    have he := gaussianRationalEmbed_quadratic (gaussianRationalTableMatrix A) (fun i => v[i])
    change ((star (gaussianRationalEmbed ∘ (fun i => v[i]))) ⬝ᵥ
      (gaussianRationalMatrix (gaussianRationalTableMatrix A) *ᵥ (gaussianRationalEmbed ∘ (fun i => v[i])))).re < 0
    rw [← he, gaussianRationalEmbed_re]
    exact_mod_cast hneg
  · intro P hP
    exact hP.re_dotProduct_nonneg _

/-- Every Hermitian Gaussian rational matrix whose complex embedding is not positive
semidefinite yields a negative-vector result. -/
theorem gaussianRationalPsdSeparate_complete {n : ℕ} (A : GaussianRationalTable n)
    (hQ : (gaussianRationalTableMatrix A).IsHermitian)
    (hp : ¬ (gaussianRationalMatrix (gaussianRationalTableMatrix A)).PosSemidef) :
    ∃ v, gaussianRationalPsdSeparate A = .negative v ∧
      (gaussianRationalQuadratic (gaussianRationalTableMatrix A) (fun i => v[i])).re < 0 := by
  cases hc : gaussianRationalPsdSeparate A with
  | nonHermitian => exact False.elim ((gaussianRationalPsdSeparate_nonHermitian_iff A).mp hc hQ)
  | psd => exact False.elim (hp ((gaussianRationalPsdSeparate_psd_iff A).mp hc))
  | negative v => exact ⟨v,rfl,(gaussianRationalPsdSeparate_negative A v hc).2⟩

/-- The rational-pair separator reports positivity exactly when the corresponding complex matrix
is positive semidefinite. -/
theorem rationalPairPsdSeparate_psd_iff {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ℚ × ℚ)) :
    rationalPairPsdSeparate Q = .psd ↔ (gaussianRatMatrix Q).PosSemidef := by
  rw [rationalPairPsdSeparate,gaussianRationalPsdSeparate_psd_iff,gaussianRationalTableMatrix_table]
  rfl

/-- A negative rational-pair separator result gives a complex vector with negative quadratic
real part on the input and nonnegative quadratic real part on every positive semidefinite
matrix. -/
theorem rationalPairPsdSeparate_separates {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ℚ × ℚ))
    (v : Vector GaussianRational n) (hv : rationalPairPsdSeparate Q = .negative v) :
    let w := fun i : Fin n => gaussianRationalEmbed v[i]
    (star w ⬝ᵥ (gaussianRatMatrix Q *ᵥ w)).re < 0 ∧
    ∀ P : Matrix (Fin n) (Fin n) ℂ, P.PosSemidef → 0 ≤ (star w ⬝ᵥ (P *ᵥ w)).re := by
  simpa only [gaussianRationalTableMatrix_table] using!
    gaussianRationalPsdSeparate_separates (gaussianRationalTable (Q.map gaussianRationalOfPair)) v hv

/-- Embedding a rational scalar as a Gaussian rational agrees with its direct complex coercion. -/
@[simp] theorem gaussianRationalEmbed_ratCast (a : ℚ) :
    gaussianRationalEmbed (a : GaussianRational) = (a : ℂ) := by simp

/-- Embedding a Gaussian rational matrix commutes with the left partial trace. -/
theorem gaussianRationalMatrix_traceLeft {D E : ℕ}
    (Y : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) :
    gaussianRationalMatrix Y.traceLeft = (gaussianRationalMatrix Y).traceLeft := by
  ext i j
  simp [gaussianRationalMatrix,Matrix.traceLeft,map_sum]

/-- The embedded rational diamond slack is the block decomposition formed from the scalar
partial trace slacks and the Choi coupling block. -/
theorem diamondRationalSlack_embed {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (Y Z : HermitianMat (Fin E × Fin D) ℂ)
    (Yq Zq : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hY : gaussianRationalMatrix Yq = Y.mat) (hZ : gaussianRationalMatrix Zq = Z.mat) (a b : ℚ) :
    gaussianRationalMatrix (diamondRationalSlack J Yq Zq a b) =
      (directSum (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal ((a : ℝ) • 1 - Y.traceLeft) ((b : ℝ) • 1 - Z.traceLeft))
        (Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal Y Z - (1/2 : ℝ) • offDiagonal (gaussianRationalMatrix J))).mat := by
  change gaussianRationalMatrix (diamondRationalSlack J Yq Zq a b) =
    Matrix.fromBlocks
      (Matrix.fromBlocks ((a : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) - Y.mat.traceLeft) 0 0
        ((b : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) - Z.mat.traceLeft)) 0 0
      (Matrix.fromBlocks Y.mat 0 0 Z.mat - (1/2 : ℝ) •
        Matrix.fromBlocks 0 (gaussianRationalMatrix J) (gaussianRationalMatrix J)ᴴ 0)
  have hytr := gaussianRationalMatrix_traceLeft Yq
  have hztr := gaussianRationalMatrix_traceLeft Zq
  rw [hY] at hytr
  rw [hZ] at hztr
  have hdiag (q : ℚ) (i j : Fin D) :
      gaussianRationalEmbed ((Matrix.diagonal (fun _ : Fin D => (q : GaussianRational))) i j) =
      ((q : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)) i j := by
    by_cases h : i = j <;> simp [h]
  have hhalf (z : GaussianRational) :
      gaussianRationalEmbed (-(1/2 : GaussianRational) * z) = -(1/2 : ℝ) • gaussianRationalEmbed z := by
    simp only [map_mul,map_neg,map_div₀,map_one,map_ofNat]
    norm_num
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          change gaussianRationalEmbed (_ - _) = _ - _
          rw [map_sub,hdiag]
          exact congrArg (fun z => ((a : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)) i j - z)
            (congrFun (congrFun hytr i) j)
        | inr j => exact map_zero gaussianRationalEmbed
      | inr i =>
        cases j with
        | inl j => exact map_zero gaussianRationalEmbed
        | inr j =>
          change gaussianRationalEmbed (_ - _) = _ - _
          rw [map_sub,hdiag]
          exact congrArg (fun z => ((b : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)) i j - z)
            (congrFun (congrFun hztr i) j)
    | inr j => exact map_zero gaussianRationalEmbed
  | inr i =>
    cases j with
    | inl j => exact map_zero gaussianRationalEmbed
    | inr j =>
      cases i with
      | inl i =>
        cases j with
        | inl j => simpa using! congrFun (congrFun hY i) j
        | inr j =>
          change gaussianRationalEmbed (-(1/2 : GaussianRational) * J i j) = 0 - (1/2 : ℝ) • _
          rw [hhalf,zero_sub,neg_smul]
          rfl
      | inr i =>
        cases j with
        | inl j =>
          change gaussianRationalEmbed (-(1/2 : GaussianRational) * star (J j i)) = 0 -
              (1/2 : ℝ) • star _
          rw [hhalf,gaussianRationalEmbed_star,zero_sub,neg_smul]
          rfl
        | inr j => simpa using! congrFun (congrFun hZ i) j

/-- For rational Choi data representing `T`, embedding the dyadic rational slack gives the dual
slack of the decoded diamond data. -/
theorem diamondDyadicRationalSlack_embed {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E) :
    gaussianRationalMatrix (diamondDyadicRationalSlack J p P) =
      ((diamondProgram T).constraint.adjoint (diamondDyadicDecode p P) -
        (diamondProgram T).objective).mat := by
  have hY : gaussianRationalMatrix ((hermitianDyadicRatDecode p P.block0).map gaussianRationalOfPair) =
      (hermitianDyadicDecode p P.block0).mat := hermitianDyadicRatDecode_correct p P.block0
  have hZ : gaussianRationalMatrix ((hermitianDyadicRatDecode p P.block1).map gaussianRationalOfPair) =
      (hermitianDyadicDecode p P.block1).mat := hermitianDyadicRatDecode_correct p P.block1
  have hs := diamondRationalSlack_embed J (hermitianDyadicDecode p P.block0) (hermitianDyadicDecode p P.block1)
    _ _ hY hZ ((P.scalar0 : ℚ) / 2^p) ((P.scalar1 : ℚ) / 2^p)
  push_cast at hs
  rw [hJ] at hs
  rw [diamondDyadicDecode,diamondProgram_dual_slack]
  exact hs

/-- For rational Choi data representing `T`, the dyadic feasibility check returns true exactly
when the decoded data are diamond dual feasible. -/
theorem diamondDyadicFeasibleCheck_correct {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E) :
    diamondDyadicFeasibleCheck J p P = true ↔
      (diamondProgram T).DualFeasible (diamondDyadicDecode p P) := by
  rw [diamondDyadicFeasibleCheck,gaussianRationalPsdCheck_correct,
    diamondDyadicSlackTable,gaussianRationalTableMatrix_table]
  change ((gaussianRationalMatrix (diamondDyadicRationalSlack J p P)).submatrix
    (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm).PosSemidef ↔ _
  rw [Matrix.posSemidef_submatrix_equiv,diamondDyadicRationalSlack_embed T J hJ]
  exact HermitianMat.zero_le_iff.symm

/-- Embedding the dyadic slack table gives the diamond dual slack reindexed by the rational
register equivalence. -/
theorem diamondDyadicSlackTable_embed {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E) :
    gaussianRationalMatrix (gaussianRationalTableMatrix (diamondDyadicSlackTable J p P)) =
      (((diamondProgram T).constraint.adjoint (diamondDyadicDecode p P) -
        (diamondProgram T).objective).mat).submatrix
          (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm := by
  rw [diamondDyadicSlackTable,gaussianRationalTableMatrix_table]
  change (gaussianRationalMatrix (diamondDyadicRationalSlack J p P)).submatrix _ _ = _
  rw [diamondDyadicRationalSlack_embed T J hJ]

/-- For rational Choi data representing `T`, the dyadic slack table represents a Hermitian
matrix. -/
theorem diamondDyadicSlackTable_hermitian {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E) :
    (gaussianRationalTableMatrix (diamondDyadicSlackTable J p P)).IsHermitian := by
  apply (gaussianRationalMatrix_hermitian_iff _).mp
  rw [diamondDyadicSlackTable_embed T J hJ]
  exact ((diamondProgram T).constraint.adjoint (diamondDyadicDecode p P) -
    (diamondProgram T).objective).H.submatrix _

/-- For rational Choi data representing `T`, the dyadic feasibility separator reports positivity
exactly when the decoded data are diamond dual feasible. -/
theorem diamondDyadicFeasibleSeparate_psd_iff {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E) :
    diamondDyadicFeasibleSeparate J p P = .psd ↔
      (diamondProgram T).DualFeasible (diamondDyadicDecode p P) := by
  rw [diamondDyadicFeasibleSeparate,gaussianRationalPsdSeparate_psd_iff,
    ← gaussianRationalPsdCheck_correct]
  exact diamondDyadicFeasibleCheck_correct T J hJ p P

/-- For rational Choi data representing `T`, the dyadic feasibility separator never reports
non-Hermitian input. -/
theorem diamondDyadicFeasibleSeparate_not_nonHermitian {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E) :
    diamondDyadicFeasibleSeparate J p P ≠ .nonHermitian := by
  intro h
  exact (gaussianRationalPsdSeparate_nonHermitian_iff _).mp h
    (diamondDyadicSlackTable_hermitian T J hJ p P)

/-- Reindexing a matrix by an equivalence transports its quadratic form to the vector composed
with that equivalence. -/
theorem quadratic_submatrix_equiv {I K : Type*} [Fintype I] [Fintype K]
    (M : Matrix I I ℂ) (e : I ≃ K) (v : K → ℂ) :
    star v ⬝ᵥ (M.submatrix e.symm e.symm *ᵥ v) =
      star (v ∘ e) ⬝ᵥ (M *ᵥ (v ∘ e)) := by
  rw [Matrix.submatrix_mulVec_equiv,dotProduct_comp_equiv_symm]
  rfl

/-- A negative dyadic feasibility result yields a vector with negative quadratic real part on
the decoded dual slack and nonnegative quadratic real part on every feasible diamond dual
slack. -/
theorem diamondDyadicFeasibleSeparate_separates {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D)))
    (hv : diamondDyadicFeasibleSeparate J p P = .negative v) :
    let w :=
        fun i : DiamondRegister D E => gaussianRationalEmbed v[diamondRationalRegisterEquiv D E i]
    (star w ⬝ᵥ (((diamondProgram T).constraint.adjoint (diamondDyadicDecode p P) -
      (diamondProgram T).objective).mat *ᵥ w)).re < 0 ∧
    ∀ y, (diamondProgram T).DualFeasible y →
      0 ≤ (star w ⬝ᵥ (((diamondProgram T).constraint.adjoint y - (diamondProgram T).objective).mat *ᵥ w)).re := by
  (try dsimp only)
  constructor
  · have h := (gaussianRationalPsdSeparate_separates (diamondDyadicSlackTable J p P) v hv).1
    rw [diamondDyadicSlackTable_embed T J hJ,quadratic_submatrix_equiv] at h
    exact h
  · intro y hy
    exact (HermitianMat.zero_le_iff.mp hy).re_dotProduct_nonneg _

/-- For rational Choi data representing `T`, infeasible decoded dyadic data cause the separator
to return a negative vector. -/
theorem diamondDyadicFeasibleSeparate_complete {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p : ℕ) (P : DiamondDyadicData D E)
    (hp : ¬ (diamondProgram T).DualFeasible (diamondDyadicDecode p P)) :
    ∃ v, diamondDyadicFeasibleSeparate J p P = .negative v := by
  cases hc : diamondDyadicFeasibleSeparate J p P with
  | nonHermitian => exact False.elim (diamondDyadicFeasibleSeparate_not_nonHermitian T J hJ p P hc)
  | psd => exact False.elim (hp ((diamondDyadicFeasibleSeparate_psd_iff T J hJ p P).mp hc))
  | negative v => exact ⟨v,rfl⟩

/-- The binary dyadic feasibility check returns `some true` exactly when the bits decode to
diamond dual feasible data. -/
theorem diamondDyadicBinaryFeasibleCheck_correct {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p b : ℕ) (bs : List Bool) :
    diamondDyadicBinaryFeasibleCheck J p b bs = some true ↔
      ∃ P, diamondDyadicFromBits D E b bs = some P ∧
        (diamondProgram T).DualFeasible (diamondDyadicDecode p P) := by
  rw [diamondDyadicBinaryFeasibleCheck,Option.map_eq_some_iff]
  simp only [diamondDyadicFeasibleCheck_correct T J hJ]

/-- For data satisfying the word bound, checking their binary encoding is equivalent to diamond
dual feasibility of their dyadic decoding. -/
theorem diamondDyadicBinaryFeasibleCheck_bits {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (p b : ℕ) (P : DiamondDyadicData D E) (hP : P.WordBound b) :
    diamondDyadicBinaryFeasibleCheck J p b (diamondDyadicBits b P) = some true ↔
      (diamondProgram T).DualFeasible (diamondDyadicDecode p P) := by
  rw [diamondDyadicBinaryFeasibleCheck,diamondDyadicFromBits_bits b P hP]
  simp only [Option.map_some,Option.some.injEq,diamondDyadicFeasibleCheck_correct T J hJ]

section RationalSdpConditioning
open scoped Matrix.Norms.L2Operator

/-- The norm of a complex Euclidean vector is at most the sum of its coordinate norms. -/
theorem euclidean_norm_le_sum {I : Type*} [Fintype I] [DecidableEq I] (x : EuclideanSpace ℂ I) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have hx : x = ∑ i, PiLp.single 2 i (x i) := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ i, PiLp.single 2 i (x i)‖ := congrArg norm hx
    _ ≤ ∑ i, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℂ I)‖ := norm_sum_le _ _
    _ = _ := by simp

/-- The operator norm of a complex square matrix is at most the sum of the norms of its entries. -/
theorem matrix_opNorm_le_sum_entries {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤ _
  calc
    _ ≤ ∑ i, ‖(A *ᵥ WithLp.ofLp x) i‖ := euclidean_norm_le_sum _
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x j‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (by simp only [norm_mul]; rfl)
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

/-- The rational bound `gaussianRationalNormBound J` is nonnegative. -/
theorem gaussianRationalNormBound_nonneg {I : Type*} [Fintype I] (J : Matrix I I GaussianRational) :
    0 ≤ gaussianRationalNormBound J := by unfold gaussianRationalNormBound; positivity

/-- The operator norm of an embedded Gaussian rational matrix is at most
`gaussianRationalNormBound J`. -/
theorem gaussianRationalMatrix_norm_bound {I : Type*} [Fintype I] [DecidableEq I]
    (J : Matrix I I GaussianRational) : ‖gaussianRationalMatrix J‖ ≤ (gaussianRationalNormBound J : ℝ) := by
  apply (matrix_opNorm_le_sum_entries _).trans
  unfold gaussianRationalNormBound
  push_cast
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := Complex.norm_le_abs_re_add_abs_im (gaussianRationalEmbed (J i j))
  simpa only [gaussianRationalEmbed_re,gaussianRationalEmbed_im,Rat.cast_abs,gaussianRationalMatrix,Matrix.map_apply] using! h

/-- The rational diamond regularization weight is positive for a positive rational tolerance. -/
theorem diamondRationalWeight_pos {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) {ε : ℚ} (hε : 0 < ε) :
    0 < diamondRationalWeight J ε := by
  have hR := gaussianRationalNormBound_nonneg J
  unfold diamondRationalWeight
  exact lt_min (by norm_num) (div_pos hε (by positivity))

/-- The rational diamond rounding radius is positive for a positive rational tolerance. -/
theorem diamondRationalRadius_pos {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) {ε : ℚ} (hε : 0 < ε) :
    0 < diamondRationalRadius J ε := div_pos (diamondRationalWeight_pos J hε) (by positivity)

/-- For rational Choi data and nonnegative tolerance, the rational regularization weight is at
most the real diamond regularization weight. -/
theorem diamondRationalWeight_le {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 ≤ ε) :
    (diamondRationalWeight J ε : ℝ) ≤ diamondRegularizationWeight T (ε : ℝ) := by
  have hR := gaussianRationalMatrix_norm_bound J
  rw [hJ] at hR
  have he : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  unfold diamondRationalWeight diamondRegularizationWeight
  push_cast
  apply min_le_min le_rfl
  apply div_le_div_of_nonneg_left he (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg (α := ℝ) E)]

/-- For rational Choi data and nonnegative tolerance, the rational rounding radius is at most
the real diamond rounding radius. -/
theorem diamondRationalRadius_le {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 ≤ ε) :
    (diamondRationalRadius J ε : ℝ) ≤ diamondRoundingRadius T (ε : ℝ) := by
  unfold diamondRationalRadius diamondRoundingRadius
  push_cast
  exact div_le_div_of_nonneg_right (diamondRationalWeight_le T J hJ hε) (by positivity)

/-- For rational Choi data and positive tolerance, `diamondRationalPrecision` makes the dyadic
error bound fit within the real rounding radius. -/
theorem diamondRationalPrecision_sufficient {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 < ε) :
    (2 + 4 * (E : ℝ) * D) / (2 : ℝ)^(diamondRationalPrecision J ε) ≤ diamondRoundingRadius T (ε : ℝ) := by
  apply le_trans _ (diamondRationalRadius_le T J hJ hε.le)
  apply dyadicPrecision_sufficient (by exact_mod_cast diamondRationalRadius_pos J hε)
  have h := Nat.le_ceil ((2 + 4 * (E : ℚ) * D) / diamondRationalRadius J ε)
  exact_mod_cast h

/-- For rational Choi data, the rational outer size bounds the real dyadic outer size. -/
theorem diamondRationalOuterSize_bound {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (ε : ℚ) :
    diamondDyadicOuterSize T (ε : ℝ) ≤ (diamondRationalOuterSize J ε : ℝ) := by
  have hR := gaussianRationalMatrix_norm_bound J
  rw [hJ] at hR
  unfold diamondRationalOuterSize diamondDyadicOuterSize
  push_cast
  gcongr

/-- For rational Choi data, the dual slack at `diamondRationalCenter J` dominates the identity. -/
theorem diamondRationalCenter_margin {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) :
    (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
      (diamondProgram T).constraint.adjoint (diamondRationalCenter J) - (diamondProgram T).objective := by
  have hR := gaussianRationalMatrix_norm_bound J
  rw [hJ] at hR
  have hn := norm_cross_dilation_nonneg (MatrixMap.choi_matrix T)
  have hi : (0 : HermitianMat ((Fin E × Fin D) ⊕ (Fin E × Fin D)) ℂ) ≤ 1 :=
    HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hh := add_nonneg (smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hn)
    (smul_nonneg (by linarith : (0 : ℝ) ≤ ((gaussianRationalNormBound J : ℝ) - ‖MatrixMap.choi_matrix T‖)/2) hi)
  have henv : (1 : HermitianMat ((Fin E × Fin D) ⊕ (Fin E × Fin D)) ℂ) ≤
      (diamondRationalCenterScale J : ℝ) • 1 - (1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T) := by
    apply sub_nonneg.mp
    convert! hh using 1
    unfold diamondRationalCenterScale
    push_cast
    module
  unfold diamondRationalCenter diamondRationalCenterScalar
  push_cast
  rw [diamondProgram_dual_slack,HermitianMat.traceLeft_smul,traceLeft_one_fin,scalar_center_cancel]
  rw [blockDiagonal_scalar_one]
  have hinput : Qatlib.Concepts.DyadicFloor.FloorRounding.blockDiagonal (1 : HermitianMat (Fin D) ℂ) 1 = 1 := by
    simpa only [one_smul] using! blockDiagonal_scalar_one (I := Fin D) (1 : ℝ)
  rw [hinput]
  have ht := directSum_mono (le_refl (1 : HermitianMat (Fin D ⊕ Fin D) ℂ)) henv
  have heq : directSum (1 : HermitianMat (Fin D ⊕ Fin D) ℂ)
      (1 : HermitianMat ((Fin E × Fin D) ⊕ (Fin E × Fin D)) ℂ) = 1 := by
    apply HermitianMat.ext
    exact Matrix.fromBlocks_one
  rwa [heq] at ht

/-- Embedding `diamondRationalCenterSlack J` gives the dual slack at the rational diamond
center. -/
theorem diamondRationalCenterSlack_embed {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) :
    gaussianRationalMatrix (diamondRationalCenterSlack J) =
      ((diamondProgram T).constraint.adjoint (diamondRationalCenter J) - (diamondProgram T).objective).mat := by
  have hc : gaussianRationalMatrix (Matrix.diagonal (fun _ : Fin E × Fin D => (diamondRationalCenterScale J : GaussianRational))) =
      ((diamondRationalCenterScale J : ℝ) • (1 : HermitianMat (Fin E × Fin D) ℂ)).mat := by
    rw [HermitianMat.mat_smul,HermitianMat.mat_one]
    ext i j
    by_cases h : i = j <;> simp [gaussianRationalMatrix,h]
  unfold diamondRationalCenterSlack
  rw [diamondRationalSlack_embed _ _ _ _ _ hc hc,hJ]
  rw [diamondRationalCenter,diamondProgram_dual_slack]

/-- Perturbations within the rational diamond interior radius leave dual slack at least half the
identity. -/
theorem diamondRationalCenter_interior_ball {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    {h : DiamondConstraints D E} (hh : ‖h‖ ≤ (diamondRationalInteriorRadius E : ℝ)) :
    (1/2 : ℝ) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
      (diamondProgram T).constraint.adjoint (diamondRationalCenter J + h) - (diamondProgram T).objective := by
  have hb : (1 + E : ℝ) * ‖h‖ ≤ 1/2 := by
    unfold diamondRationalInteriorRadius at hh
    push_cast at hh
    have hd : (0 : ℝ) < 2 * (1 + E) := by positivity
    have hh' : ‖h‖ ≤ 1 / (2 * (1 + E : ℝ)) := by simpa only [one_div] using! hh
    have hm := (le_div_iff₀ hd).mp hh'
    nlinarith
  have hn := (diamondEqMap_adjoint_norm_bound h).trans hb
  have hi : (0 : HermitianMat (DiamondRegister D E) ℂ) ≤ 1 :=
      HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
  have hl : (-1/2 : ℝ) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤ (diamondEqMap D E).adjoint h := by
    simpa only [neg_div] using! (smul_le_smul_of_nonneg_right (neg_le_neg hn) hi).trans
      (hermitian_neg_opNorm_smul_one_le ((diamondEqMap D E).adjoint h))
  have hm := add_le_add (diamondRationalCenter_margin T J hJ) hl
  change _ ≤ (diamondEqMap D E).adjoint (diamondRationalCenter J + h) - (diamondProgram T).objective
  rw [map_add]
  change (1 : HermitianMat (DiamondRegister D E) ℂ) + (-1/2 : ℝ) • 1 ≤
    (diamondEqMap D E).adjoint (diamondRationalCenter J) - (diamondProgram T).objective + (diamondEqMap D E).adjoint h at hm
  rw [← one_smul ℝ (1 : HermitianMat (DiamondRegister D E) ℂ)] at hm
  convert! hm using 1 <;> module

/-- For positive input dimension and rational tolerance, rational Choi data possess a bounded
binary dyadic witness accepted by the feasibility checker and with score within the
tolerance above the diamond optimum. The witness has the specified bit length, strictly
positive slack margin, and rational outer size bound. -/
theorem diamondProgram_rational_binary_witness {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 < ε) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (P : DiamondDyadicData D E) (bs : List Bool),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      P.WordBound (diamondRationalWidth J ε) ∧
      bs = diamondDyadicBits (diamondRationalWidth J ε) P ∧
      bs.length = (2 + 4*(E*D)^2) * (diamondRationalWidth J ε+1) ∧
      diamondDyadicFromBits D E (diamondRationalWidth J ε) bs = some P ∧
      diamondDyadicBinaryFeasibleCheck J (diamondRationalPrecision J ε) (diamondRationalWidth J ε) bs = some true ∧
      ((diamondRationalWeight J ε : ℝ)/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
        (diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondRationalPrecision J ε) P) -
          (diamondProgram T).objective ∧
      ((diamondProgram T).constraint.adjoint (diamondDyadicDecode (diamondRationalPrecision J ε) P) -
        (diamondProgram T).objective).mat.PosDef ∧
      α ≤ (diamondProgram T).dualScore (diamondDyadicDecode (diamondRationalPrecision J ε) P) ∧
      (diamondProgram T).dualScore (diamondDyadicDecode (diamondRationalPrecision J ε) P) < α+(ε : ℝ) ∧
      ‖diamondDyadicDecode (diamondRationalPrecision J ε) P‖ ≤ (diamondRationalOuterSize J ε : ℝ) := by
  have he : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨α,M,z,hnorm,hM,hsM,hlo,hu,hpr,hdu,hball⟩ := diamondProgram_near_optimal_ball hD T he
  let p := diamondRationalPrecision J ε
  let P := diamondDyadicPayload p z
  have hz : ‖z‖ ≤ (diamondRationalOuterSize J ε : ℝ) := by
    have h0 := hball 0 (by simpa only [norm_zero] using! (diamondRoundingRadius_pos T he).le)
    have hb0 : ‖z‖ ≤ diamondDyadicOuterSize T (ε : ℝ) := by
      simpa only [add_zero,diamondDyadicOuterSize] using! h0.2.2.2.2
    exact hb0.trans (diamondRationalOuterSize_bound T J hJ ε)
  have hwords : P.WordBound (diamondRationalWidth J ε) := by
    rw [diamondRationalWidth,rationalDyadicWordWidth_eq]
    exact diamondDyadicPayload_word_bound p z hz
  have herr : ‖diamondDyadicDecode p P-z‖ ≤ diamondRoundingRadius T (ε : ℝ) :=
    (diamondDyadicDecode_error p z).trans (diamondRationalPrecision_sufficient T J hJ hε)
  obtain ⟨hmargin,hpd,hl,hupper,hsize⟩ := hball (diamondDyadicDecode p P-z) herr
  rw [add_sub_cancel] at hmargin hpd hl hupper hsize
  have hm : ((diamondRationalWeight J ε : ℝ)/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
      (diamondProgram T).constraint.adjoint (diamondDyadicDecode p P) - (diamondProgram T).objective := by
    have hscale :=
        div_le_div_of_nonneg_right (diamondRationalWeight_le T J hJ hε.le)
        (by norm_num : (0 : ℝ) ≤ 2)
    have hi : (0 : HermitianMat (DiamondRegister D E) ℂ) ≤ 1 :=
        HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
    exact (smul_le_smul_of_nonneg_right hscale hi).trans hmargin
  let bs := diamondDyadicBits (diamondRationalWidth J ε) P
  have hparse : diamondDyadicFromBits D E (diamondRationalWidth J ε) bs = some P :=
    diamondDyadicFromBits_bits _ P hwords
  have hcheck : diamondDyadicBinaryFeasibleCheck J p (diamondRationalWidth J ε) bs = some true :=
    (diamondDyadicBinaryFeasibleCheck_correct T J hJ _ _ _).mpr
      ⟨P,hparse,HermitianMat.zero_le_iff.mpr hpd.posSemidef⟩
  refine ⟨α,M,P,bs,hnorm,hM,hsM,hpr,hdu,hwords,rfl,?_,hparse,hcheck,hm,hpd,hl,hupper,?_⟩
  · rw [diamondDyadicBits_length,diamondDyadicBitCount_eq]
  · exact hsize.trans (diamondRationalOuterSize_bound T J hJ ε)

/-- Extracting a rational raw block from diamond coordinates preserves addition. -/
theorem diamondRationalRawBlock_add {D E : ℕ} (b : Bool) (x y : DiamondRationalCoordinates D E) :
    diamondRationalRawBlock b (x+y) = diamondRationalRawBlock b x + diamondRationalRawBlock b y := by
  ext i j <;> rfl

/-- Extracting a rational raw block from diamond coordinates preserves rational scalar
multiplication. -/
theorem diamondRationalRawBlock_smul {D E : ℕ} (b : Bool) (q : ℚ) (x : DiamondRationalCoordinates D E) :
    diamondRationalRawBlock b (q • x) = q • diamondRationalRawBlock b x := by
  ext i j <;> simp [diamondRationalRawBlock,gaussianRationalOfPair]

/-- Gaussian rational symmetrization preserves addition. -/
theorem gaussianRationalSymmetrize_add {I : Type*} (Q R : Matrix I I GaussianRational) :
    gaussianRationalSymmetrize (Q+R) = gaussianRationalSymmetrize Q + gaussianRationalSymmetrize R := by
  simp only [gaussianRationalSymmetrize,Matrix.conjTranspose_add,smul_add]
  abel

/-- Gaussian rational symmetrization preserves rational scalar multiplication. -/
theorem gaussianRationalSymmetrize_smul {I : Type*} (q : ℚ) (Q : Matrix I I GaussianRational) :
    gaussianRationalSymmetrize (q • Q) = q • gaussianRationalSymmetrize Q := by
  simp only [gaussianRationalSymmetrize,Matrix.conjTranspose_smul,star_trivial,← smul_add]
  exact smul_comm _ _ _

/-- Gaussian rational symmetrization produces a Hermitian matrix. -/
theorem gaussianRationalSymmetrize_hermitian {I : Type*} (Q : Matrix I I GaussianRational) :
    (gaussianRationalSymmetrize Q).IsHermitian := by
  change ((1/2 : GaussianRational) • (Q+Qᴴ))ᴴ = (1/2 : GaussianRational) • (Q+Qᴴ)
  simp [Matrix.conjTranspose_smul,Matrix.conjTranspose_add,add_comm]

/-- With zero Choi data, the rational candidate slack preserves addition of coordinates. -/
theorem diamondRationalCandidateSlack_linear_add {D E : ℕ} (x y : DiamondRationalCoordinates D E) :
    diamondRationalCandidateSlack (0 : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x+y) =
      diamondRationalCandidateSlack 0 x + diamondRationalCandidateSlack 0 y := by
  simp only [diamondRationalCandidateSlack,diamondRationalSymBlock,diamondRationalRawBlock_add,
    gaussianRationalSymmetrize_add,Pi.add_apply,diamondRationalSlack]
  apply Matrix.ext
  intro i j
  rcases i with (i|i)|(i|i) <;> rcases j with (j|j)|(j|j) <;>
    simp [Matrix.traceLeft,Finset.sum_add_distrib,Matrix.diagonal_apply]
  all_goals split_ifs <;> ring

/-- With zero Choi data, the rational candidate slack preserves rational scalar multiplication. -/
theorem diamondRationalCandidateSlack_linear_smul {D E : ℕ} (q : ℚ) (x : DiamondRationalCoordinates D E) :
    diamondRationalCandidateSlack (0 : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (q • x) =
      q • diamondRationalCandidateSlack 0 x := by
  simp only [diamondRationalCandidateSlack,diamondRationalSymBlock,diamondRationalRawBlock_smul,
    gaussianRationalSymmetrize_smul,Pi.smul_apply,diamondRationalSlack]
  apply Matrix.ext
  intro i j
  rcases i with (i|i)|(i|i) <;> rcases j with (j|j)|(j|j) <;>
    simp [Matrix.traceLeft,Finset.smul_sum,Matrix.diagonal_apply,smul_sub]
  all_goals simp [Algebra.smul_def]

/-- The rational linear map sending diamond coordinates to their candidate slack with zero Choi
data. -/
def diamondRationalSlackLinear (D E : ℕ) : DiamondRationalCoordinates D E →ₗ[ℚ]
    Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational where
  toFun := diamondRationalCandidateSlack 0
  map_add' := diamondRationalCandidateSlack_linear_add
  map_smul' := diamondRationalCandidateSlack_linear_smul

/-- Embedding the Gaussian rational symmetrization gives the underlying matrix of the Hermitian
decoder. -/
theorem gaussianRationalSymmetrize_embed {I : Type*} [Fintype I]
    (Q : Matrix I I GaussianRational) :
    gaussianRationalMatrix (gaussianRationalSymmetrize Q) = (gaussianRationalHermitianDecode Q).mat := by
  apply Matrix.ext
  intro i j
  change gaussianRationalEmbed ((1/2 : GaussianRational) * (Q i j + star (Q j i))) =
    (1/2 : ℝ) • (gaussianRationalEmbed (Q i j) + star (gaussianRationalEmbed (Q j i)))
  simp only [map_mul,map_div₀,map_one,map_ofNat,map_add,gaussianRationalEmbed_star]
  norm_num
  ring

/-- For rational Choi data, embedding the rational candidate slack gives the diamond dual slack
of the decoded coordinates. -/
theorem diamondRationalCandidateSlack_embed {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E) :
    gaussianRationalMatrix (diamondRationalCandidateSlack J x) =
      ((diamondProgram T).constraint.adjoint (diamondRationalDecode x) - (diamondProgram T).objective).mat := by
  unfold diamondRationalCandidateSlack diamondRationalSymBlock
  rw [diamondRationalSlack_embed _ _ _ _ _ (gaussianRationalSymmetrize_embed _) (gaussianRationalSymmetrize_embed _),hJ]
  rw [diamondRationalDecode,diamondProgram_dual_slack]

/-- The rational linear functional taking a Gaussian rational matrix to the real part of its
quadratic form at `v`. -/
def gaussianRationalQuadraticLinear (n : ℕ) (v : Fin n → GaussianRational) :
    Matrix (Fin n) (Fin n) GaussianRational →ₗ[ℚ] ℚ where
  toFun Q := (gaussianRationalQuadratic Q v).re
  map_add' Q R := by
    simp [gaussianRationalQuadratic,dotProduct,Matrix.mulVec,add_mul,mul_add,Finset.sum_add_distrib,QuadraticAlgebra.re_add]
  map_smul' q Q := by
    simp only [gaussianRationalQuadratic,dotProduct,Matrix.mulVec,Matrix.smul_apply,smul_mul_assoc,
      mul_smul_comm,← Finset.smul_sum,QuadraticAlgebra.re_smul,smul_eq_mul,RingHom.id_apply]

/-- The rational linear reindexing of a diamond register matrix to the finite index type used by
the rational separator. -/
def diamondRationalSlackReindexLinear (D E : ℕ) : Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational →ₗ[ℚ]
    Matrix (Fin ((D+D)+(E*D+E*D))) (Fin ((D+D)+(E*D+E*D))) GaussianRational where
  toFun Q := Q.submatrix (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The rational linear functional obtained by evaluating a fixed vector's real quadratic form
on the reindexed linear part of the diamond slack. -/
def diamondRationalSlackQuadraticLinear {D E : ℕ} (v : Vector GaussianRational ((D+D)+(E*D+E*D))) :
    DiamondRationalCoordinates D E →ₗ[ℚ] ℚ :=
  (gaussianRationalQuadraticLinear _ (fun i => v[i])).comp
    ((diamondRationalSlackReindexLinear D E).comp (diamondRationalSlackLinear D E))

/-- A rational linear functional on finite coordinate vectors is the sum of its standard basis
values times the coordinates. -/
theorem linearMap_eq_sum_basis {n : ℕ} (f : (Fin n → ℚ) →ₗ[ℚ] ℚ) (x : Fin n → ℚ) :
    f x = ∑ k, f (Pi.single k 1) * x k := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → ℚ) := by
    funext i
    simp [Pi.single_apply]
  calc
    f x = f (∑ k, x k • (Pi.single k 1 : Fin n → ℚ)) := congrArg f hx
    _ = _ := by simp [map_sum,map_smul,mul_comm]

/-- Evaluating the rational separation cut gives the linear slack quadratic functional at the
candidate coordinates. -/
theorem diamondRationalSeparationCut_eval {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) (x : DiamondRationalCoordinates D E) :
    (diamondRationalSeparationCut J v).eval x = diamondRationalSlackQuadraticLinear v x := by
  rw [linearMap_eq_sum_basis]
  apply Finset.sum_congr rfl
  intro k _
  simp [diamondRationalSeparationCut,diamondRationalSlackQuadraticLinear,
    diamondRationalSlackReindexLinear,diamondRationalSlackLinear,gaussianRationalQuadraticLinear]

/-- The rational candidate slack is the sum of its coordinate-linear part and its value at zero
coordinates. -/
theorem diamondRationalCandidateSlack_affine {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    diamondRationalCandidateSlack J x = diamondRationalCandidateSlack 0 x + diamondRationalCandidateSlack J 0 := by
  have hz (b : Bool) : diamondRationalSymBlock b (0 : DiamondRationalCoordinates D E) = 0 := by
    ext i j <;> simp [diamondRationalSymBlock,gaussianRationalSymmetrize,diamondRationalRawBlock,gaussianRationalOfPair]
  simp only [diamondRationalCandidateSlack,hz,Pi.zero_apply,diamondRationalSlack]
  apply Matrix.ext
  intro i j
  rcases i with (i|i)|(i|i) <;> rcases j with (j|j)|(j|j) <;> simp [Matrix.traceLeft]

/-- A rational separation cut's evaluation minus its bound equals the real quadratic value of
the reindexed candidate slack. -/
theorem diamondRationalSeparationCut_identity {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) (x : DiamondRationalCoordinates D E) :
    (diamondRationalSeparationCut J v).eval x - (diamondRationalSeparationCut J v).bound =
      (gaussianRationalQuadratic ((diamondRationalCandidateSlack J x).submatrix
        (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm) (fun i => v[i])).re := by
  rw [diamondRationalSeparationCut_eval,diamondRationalCandidateSlack_affine]
  change _ - -_ = gaussianRationalQuadraticLinear _ (fun i => v[i])
    (((diamondRationalSlackReindexLinear D E) _)+((diamondRationalSlackReindexLinear D E) _))
  rw [map_add]
  simp only [sub_neg_eq_add]
  rfl

/-- For rational Choi data, embedding the candidate table gives the decoded diamond dual slack
reindexed to the separator's finite register. -/
theorem diamondRationalCandidateTable_embed {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E) :
    gaussianRationalMatrix (gaussianRationalTableMatrix (diamondRationalCandidateTable J x)) =
      (((diamondProgram T).constraint.adjoint (diamondRationalDecode x) - (diamondProgram T).objective).mat).submatrix
        (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm := by
  rw [diamondRationalCandidateTable,gaussianRationalTableMatrix_table]
  change (gaussianRationalMatrix (diamondRationalCandidateSlack J x)).submatrix _ _ = _
  rw [diamondRationalCandidateSlack_embed T J hJ]

/-- The rational candidate separator reports positivity exactly when the decoded coordinates are
diamond dual feasible. -/
theorem diamondRationalCandidateSeparate_psd_iff {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E) :
    diamondRationalCandidateSeparate J x = .psd ↔ (diamondProgram T).DualFeasible (diamondRationalDecode x) := by
  rw [diamondRationalCandidateSeparate,gaussianRationalPsdSeparate_psd_iff,
    diamondRationalCandidateTable_embed T J hJ,Matrix.posSemidef_submatrix_equiv]
  exact HermitianMat.zero_le_iff.symm

/-- For rational Choi data, the rational candidate separator never reports non-Hermitian input. -/
theorem diamondRationalCandidateSeparate_not_nonHermitian {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E) :
    diamondRationalCandidateSeparate J x ≠ .nonHermitian := by
  intro hc
  have hn := (gaussianRationalPsdSeparate_nonHermitian_iff _).mp hc
  apply hn
  apply (gaussianRationalMatrix_hermitian_iff _).mp
  rw [diamondRationalCandidateTable_embed T J hJ]
  exact ((diamondProgram T).constraint.adjoint (diamondRationalDecode x) - (diamondProgram T).objective).H.submatrix _

/-- A negative vector returned for a rational candidate gives a separation cut whose evaluation
at that candidate is strictly below its bound. -/
theorem diamondRationalSeparationCut_rejects {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) (hv : diamondRationalCandidateSeparate J x = .negative v) :
    (diamondRationalSeparationCut J v).eval x < (diamondRationalSeparationCut J v).bound := by
  have hn := (gaussianRationalPsdSeparate_negative (diamondRationalCandidateTable J x) v hv).2
  rw [diamondRationalCandidateTable,gaussianRationalTableMatrix_table] at hn
  have he := diamondRationalSeparationCut_identity J v x
  linarith

/-- Every rational coordinate point decoding to diamond dual feasible data satisfies the
rational separation cut. -/
theorem diamondRationalSeparationCut_preserves {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) (y : DiamondRationalCoordinates D E)
    (hy : (diamondProgram T).DualFeasible (diamondRationalDecode y)) :
    (diamondRationalSeparationCut J v).bound ≤ (diamondRationalSeparationCut J v).eval y := by
  have hp := (HermitianMat.zero_le_iff.mp hy).submatrix (diamondRationalRegisterEquiv D E).symm
  rw [← diamondRationalCandidateTable_embed T J hJ y] at hp
  have hq := hp.re_dotProduct_nonneg (fun i => gaussianRationalEmbed v[i])
  have he :=
      gaussianRationalEmbed_quadratic
      (gaussianRationalTableMatrix (diamondRationalCandidateTable J y)) (fun i => v[i])
  change (0 : ℝ) ≤ (star (gaussianRationalEmbed ∘ (fun i => v[i])) ⬝ᵥ
    (gaussianRationalMatrix (gaussianRationalTableMatrix (diamondRationalCandidateTable J y)) *ᵥ
      (gaussianRationalEmbed ∘ (fun i => v[i])))).re at hq
  rw [← he] at hq
  change (0 : ℝ) ≤ ((gaussianRationalQuadratic (gaussianRationalTableMatrix (diamondRationalCandidateTable J y))
    (fun i => v[i])).re : ℝ) at hq
  have hr : (0 : ℚ) ≤ (gaussianRationalQuadratic (gaussianRationalTableMatrix (diamondRationalCandidateTable J y))
      (fun i => v[i])).re := by exact_mod_cast hq
  rw [diamondRationalCandidateTable,gaussianRationalTableMatrix_table] at hr
  rw [← diamondRationalSeparationCut_identity J v y] at hr
  linarith

/-- The rational separation oracle reports feasibility exactly when the decoded coordinates are
diamond dual feasible. -/
theorem diamondRationalSeparationOracle_feasible_iff {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E) :
    diamondRationalSeparationOracle J x = .feasible ↔ (diamondProgram T).DualFeasible (diamondRationalDecode x) := by
  unfold diamondRationalSeparationOracle
  rw [← diamondRationalCandidateSeparate_psd_iff T J hJ]
  cases diamondRationalCandidateSeparate J x <;> simp

/-- For rational Choi data, the rational separation oracle never returns an invalid result. -/
theorem diamondRationalSeparationOracle_not_invalid {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E) :
    diamondRationalSeparationOracle J x ≠ .invalid := by
  unfold diamondRationalSeparationOracle
  have hn := diamondRationalCandidateSeparate_not_nonHermitian T J hJ x
  cases hc : diamondRationalCandidateSeparate J x <;> simp_all

/-- Every cut returned by the rational separation oracle strictly rejects its candidate and
preserves all rational coordinates decoding to dual feasible data. -/
theorem diamondRationalSeparationOracle_cut {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSeparationOracle J x = .cut C) :
    C.eval x < C.bound ∧ ∀ y : DiamondRationalCoordinates D E,
      (diamondProgram T).DualFeasible (diamondRationalDecode y) → C.bound ≤ C.eval y := by
  unfold diamondRationalSeparationOracle at hc
  cases hv : diamondRationalCandidateSeparate J x with
  | nonHermitian => simp [hv] at hc
  | psd => simp [hv] at hc
  | negative v =>
    simp only [hv,RationalSeparationResult.cut.injEq] at hc
    subst C
    exact ⟨diamondRationalSeparationCut_rejects J x v hv,fun y hy => diamondRationalSeparationCut_preserves T J hJ v y hy⟩

/-- The first scalar coordinate of packed rational diamond data is `a`. -/
@[simp] theorem diamondRationalPack_scalar0 {D E : ℕ} (a b : ℚ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) :
    diamondRationalPack a b Y Z (diamondRationalScalarIndex D E 0) = a := by
  simp [diamondRationalPack,diamondRationalScalarIndex]

/-- The second scalar coordinate of packed rational diamond data is `b`. -/
@[simp] theorem diamondRationalPack_scalar1 {D E : ℕ} (a b : ℚ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) :
    diamondRationalPack a b Y Z (diamondRationalScalarIndex D E 1) = b := by
  simp [diamondRationalPack,diamondRationalScalarIndex]

/-- Extracting a raw block from packed rational diamond data returns `Y` for false and `Z` for
true. -/
theorem diamondRationalPack_block {D E : ℕ} (a b : ℚ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (which : Bool) :
    diamondRationalRawBlock which (diamondRationalPack a b Y Z) = if which then Z else Y := by
  have hword (Q : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (i j) (part : Fin 2) :
      gaussianRationalCoordinateWord Q (gaussianDyadicWordIndex D E ((i,j),part)) =
        if part = 0 then (Q i j).re else (Q i j).im := by
    simp [gaussianRationalCoordinateWord]
  have hget (i j : Fin E × Fin D) (part : Fin 2) :
      diamondRationalPack a b Y Z (diamondRationalBlockIndex D E which i j part) =
        gaussianRationalCoordinateWord (if which then Z else Y) (gaussianDyadicWordIndex D E ((i,j),part)) := by
    let k := gaussianDyadicWordIndex D E ((i,j),part)
    have hk := k.isLt
    have h2 : ¬ 2 + (if which then gaussianDyadicWordCount D E else 0) + k.val < 2 := by omega
    dsimp only [diamondRationalBlockIndex,diamondRationalPack]
    rw [dif_neg h2]
    cases which with
    | false =>
      simp only [Bool.false_eq_true,if_false,add_zero]
      rw [dif_pos (by omega)]
      congr 1
      apply Fin.ext
      simp
    | true =>
      simp only [if_true]
      rw [dif_neg (by omega)]
      congr 1
      apply Fin.ext
      simp
  apply Matrix.ext
  intro i j
  apply QuadraticAlgebra.ext
  · simp [diamondRationalRawBlock,gaussianRationalOfPair,hget,hword]
  · simp [diamondRationalRawBlock,gaussianRationalOfPair,hget,hword]

/-- Hermitian decoding of a constant rational diagonal matrix gives that scalar times the
identity. -/
theorem gaussianRationalHermitianDecode_diagonal {I : Type*} [Fintype I] [DecidableEq I] (c : ℚ) :
    gaussianRationalHermitianDecode (Matrix.diagonal (fun _ : I => (c : GaussianRational))) =
      (c : ℝ) • (1 : HermitianMat I ℂ) := by
  have hd : gaussianRationalMatrix (Matrix.diagonal (fun _ : I => (c : GaussianRational))) =
      (c : ℝ) • (1 : Matrix I I ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [gaussianRationalMatrix,h]
  apply HermitianMat.ext
  change (1/2 : ℝ) • (_ + _ᴴ) = _
  rw [hd]
  rw [Matrix.conjTranspose_smul,Matrix.conjTranspose_one]
  simp only [star_trivial]
  rw [HermitianMat.mat_smul,HermitianMat.mat_one]
  module

/-- Decoding the rational center coordinates gives the rational diamond dual center. -/
theorem diamondRationalCenterCoordinates_decode {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) :
    diamondRationalDecode (diamondRationalCenterCoordinates J) = diamondRationalCenter J := by
  unfold diamondRationalDecode diamondRationalCenterCoordinates diamondRationalCenter
  rw [diamondRationalPack_scalar0,diamondRationalPack_scalar1,diamondRationalPack_block,
    diamondRationalPack_block]
  simp [gaussianRationalHermitianDecode_diagonal]

/-- Every cut returned by the rational separation oracle has at least one nonzero coefficient. -/
theorem diamondRationalSeparationOracle_cut_nonzero {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (x : DiamondRationalCoordinates D E)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSeparationOracle J x = .cut C) :
    ∃ k : Fin (diamondDyadicWordCount D E), C.coefficients[k] ≠ 0 := by
  classical
  obtain ⟨hrej,hkeep⟩ := diamondRationalSeparationOracle_cut T J hJ x C hc
  have hy : (diamondProgram T).DualFeasible (diamondRationalDecode (diamondRationalCenterCoordinates J)) := by
    rw [diamondRationalCenterCoordinates_decode]
    have hm := diamondRationalCenter_margin T J hJ
    have hi : (0 : HermitianMat (DiamondRegister D E) ℂ) ≤ 1 :=
        HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
    exact le_trans hi hm
  have hbound := hkeep (diamondRationalCenterCoordinates J) hy
  by_contra hn
  push Not at hn
  have hz (y : DiamondRationalCoordinates D E) : C.eval y = 0 := by
    simp [RationalAffineCut.eval,hn]
  rw [hz] at hrej hbound
  linarith

section RealSdpCoordinates

/-- Extracting a real raw block from diamond coordinates preserves addition. -/
theorem diamondRealRawBlock_add {D E : ℕ} (b : Bool) (x y : DiamondRealCoordinates D E) :
    diamondRealRawBlock b (x+y) = diamondRealRawBlock b x + diamondRealRawBlock b y := by
  ext i j
  rfl

/-- Extracting a real raw block from diamond coordinates preserves real scalar multiplication. -/
theorem diamondRealRawBlock_smul {D E : ℕ} (b : Bool) (r : ℝ) (x : DiamondRealCoordinates D E) :
    diamondRealRawBlock b (r • x) = r • diamondRealRawBlock b x := by
  ext i j
  simp [diamondRealRawBlock,Complex.ext_iff]

/-- Extracting a real Hermitian block from diamond coordinates preserves addition. -/
theorem diamondRealHermitianBlock_add {D E : ℕ} (b : Bool) (x y : DiamondRealCoordinates D E) :
    diamondRealHermitianBlock b (x+y) = diamondRealHermitianBlock b x + diamondRealHermitianBlock b y := by
  apply HermitianMat.ext
  change (1/2 : ℝ) • (diamondRealRawBlock b (x+y) + (diamondRealRawBlock b (x+y))ᴴ) =
    (1/2 : ℝ) • (diamondRealRawBlock b x + (diamondRealRawBlock b x)ᴴ) +
    (1/2 : ℝ) • (diamondRealRawBlock b y + (diamondRealRawBlock b y)ᴴ)
  rw [diamondRealRawBlock_add,Matrix.conjTranspose_add]
  simp only [smul_add]
  abel

/-- Extracting a real Hermitian block from diamond coordinates preserves real scalar
multiplication. -/
theorem diamondRealHermitianBlock_smul {D E : ℕ} (b : Bool) (r : ℝ) (x : DiamondRealCoordinates D E) :
    diamondRealHermitianBlock b (r • x) = r • diamondRealHermitianBlock b x := by
  apply HermitianMat.ext
  change (1/2 : ℝ) • (_ + _ᴴ) = r • _
  rw [diamondRealRawBlock_smul,Matrix.conjTranspose_smul]
  simp only [star_trivial,← smul_add]
  exact smul_comm _ _ _

/-- Forming diamond dual data preserves coordinatewise addition. -/
theorem diamondDualData_add {D E : ℕ} (a b c d : ℝ) (Y Z U V : HermitianMat (Fin E × Fin D) ℂ) :
    diamondDualData (a+c) (b+d) (Y+U) (Z+V) = diamondDualData a b Y Z + diamondDualData c d U V := by
  rfl

/-- Forming diamond dual data preserves simultaneous real scalar multiplication of all
coordinates. -/
theorem diamondDualData_smul {D E : ℕ} (r a b : ℝ) (Y Z : HermitianMat (Fin E × Fin D) ℂ) :
    diamondDualData (r*a) (r*b) (r • Y) (r • Z) = r • diamondDualData a b Y Z := by
  rfl

/-- The real linear map decoding diamond real coordinates into diamond dual data. -/
def diamondRealDecodeLinear (D E : ℕ) : DiamondRealCoordinates D E →ₗ[ℝ] DiamondConstraints D E where
  toFun := diamondRealDecode
  map_add' x y := by
    simp only [diamondRealDecode,Pi.add_apply,diamondRealHermitianBlock_add,diamondDualData_add]
  map_smul' r x := by
    simp only [diamondRealDecode,Pi.smul_apply,smul_eq_mul,diamondRealHermitianBlock_smul,diamondDualData_smul,RingHom.id_apply]

/-- Extracting a real raw block after embedding rational coordinates equals embedding their
rational raw block. -/
theorem diamondRealRawBlock_rational {D E : ℕ} (b : Bool) (x : DiamondRationalCoordinates D E) :
    diamondRealRawBlock b (diamondRationalCoordinatesReal x) = gaussianRationalMatrix (diamondRationalRawBlock b x) := rfl

/-- Real decoding of embedded rational diamond coordinates agrees with rational decoding. -/
theorem diamondRealDecode_rational {D E : ℕ} (x : DiamondRationalCoordinates D E) :
    diamondRealDecode (diamondRationalCoordinatesReal x) = diamondRationalDecode x := rfl

/-- The real linear functional taking a Hermitian matrix to the real part of its quadratic form
at `w`. -/
def hermitianQuadraticLinear {I : Type*} [Fintype I] (w : I → ℂ) : HermitianMat I ℂ →ₗ[ℝ] ℝ where
  toFun H := (star w ⬝ᵥ (H.mat *ᵥ w)).re
  map_add' H K := by
    simp [HermitianMat.mat_add,Matrix.add_mulVec,dotProduct_add]
  map_smul' r H := by
    simp [HermitianMat.mat_smul,Matrix.smul_mulVec,dotProduct_smul]

/-- The real linear functional given by the coefficient evaluation of a rational affine cut. -/
def RationalAffineCut.realLinear {n : ℕ} (C : RationalAffineCut n) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := C.evalReal
  map_add' x y := by simp [RationalAffineCut.evalReal,mul_add,Finset.sum_add_distrib]
  map_smul' r x := by simp [RationalAffineCut.evalReal,Finset.mul_sum,mul_left_comm]

/-- Real evaluation of a rational affine cut on rational coordinates equals the coercion of its
rational evaluation. -/
theorem RationalAffineCut.evalReal_rational {n : ℕ} (C : RationalAffineCut n) (x : Fin n → ℚ) :
    C.evalReal (fun k => (x k : ℝ)) = (C.eval x : ℝ) := by
  simp [RationalAffineCut.evalReal,RationalAffineCut.eval,Rat.cast_sum,Rat.cast_mul]

/-- Real linear functionals on finite coordinates are equal if they agree on every rational
coordinate vector. -/
theorem realLinearMap_eq_of_rational {n : ℕ} (f g : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ q : Fin n → ℚ, f (fun i => (q i : ℝ)) = g (fun i => (q i : ℝ))) : f = g := by
  have he (k : Fin n) : (fun i => ((Pi.single k 1 : Fin n → ℚ) i : ℝ)) =
      (Pi.single k 1 : Fin n → ℝ) := by
    funext i
    by_cases hi : i = k <;> simp [Pi.single_apply,hi]
  have hb (k : Fin n) : f (Pi.single k 1) = g (Pi.single k 1) := by
    rw [← he]
    exact h _
  apply LinearMap.ext
  intro x
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → ℝ) := by
    funext i
    simp [Pi.single_apply]
  rw [hx,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul,map_smul,hb]

/-- Real affine functionals on finite coordinates agree everywhere if they agree on every
rational coordinate vector. -/
theorem realAffine_eq_of_rational {n : ℕ} (f g : (Fin n → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ)
    (h : ∀ q : Fin n → ℚ, f (fun i => (q i : ℝ)) + a = g (fun i => (q i : ℝ)) + b) :
    ∀ x, f x + a = g x + b := by
  have hab : a = b := by
    have h0 := h 0
    simp only [Pi.zero_apply,Rat.cast_zero] at h0
    change f 0 + a = g 0 + b at h0
    simpa using! h0
  have hfg : f = g := realLinearMap_eq_of_rational f g (fun q => by have hh := h q; linarith)
  intro x
  rw [hfg,hab]

/-- The coerced real quadratic value of a rational candidate slack equals the Hermitian
quadratic functional on its decoded diamond dual slack. -/
theorem diamondRationalQuadratic_real {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) (q : DiamondRationalCoordinates D E) :
    ((gaussianRationalQuadratic ((diamondRationalCandidateSlack J q).submatrix
        (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm) (fun i => v[i])).re : ℝ) =
      hermitianQuadraticLinear (fun i => gaussianRationalEmbed v[diamondRationalRegisterEquiv D E i])
        ((diamondProgram T).constraint.adjoint (diamondRationalDecode q) - (diamondProgram T).objective) := by
  let Q := (diamondRationalCandidateSlack J q).submatrix (diamondRationalRegisterEquiv D E).symm
    (diamondRationalRegisterEquiv D E).symm
  have he := gaussianRationalEmbed_quadratic Q (fun i => v[i])
  have hmat : gaussianRationalMatrix Q =
      (((diamondProgram T).constraint.adjoint (diamondRationalDecode q) - (diamondProgram T).objective).mat).submatrix
        (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm := by
    change (gaussianRationalMatrix (diamondRationalCandidateSlack J q)).submatrix _ _ = _
    rw [diamondRationalCandidateSlack_embed T J hJ]
  change (gaussianRationalEmbed (gaussianRationalQuadratic Q (fun i => v[i]))).re = _
  rw [he,hmat,quadratic_submatrix_equiv]
  rfl

/-- Over real coordinates, a rational separation cut's evaluation minus its bound equals the
quadratic functional on the decoded diamond dual slack. -/
theorem diamondRationalSeparationCut_real_identity {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) (x : DiamondRealCoordinates D E) :
    (diamondRationalSeparationCut J v).evalReal x - ((diamondRationalSeparationCut J v).bound : ℝ) =
      hermitianQuadraticLinear (fun i => gaussianRationalEmbed v[diamondRationalRegisterEquiv D E i])
        ((diamondProgram T).constraint.adjoint (diamondRealDecode x) - (diamondProgram T).objective) := by
  let L :=
      hermitianQuadraticLinear
      (fun i => gaussianRationalEmbed v[diamondRationalRegisterEquiv D E i])
  let f :=
      (Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.realLinear (C := (diamondRationalSeparationCut J v)))
  let g :=
      L.comp ((diamondProgram T).constraint.adjoint.toLinearMap.comp (diamondRealDecodeLinear D E))
  have hr (q : DiamondRationalCoordinates D E) :
      f (diamondRationalCoordinatesReal q) + -((diamondRationalSeparationCut J v).bound : ℝ) =
      g (diamondRationalCoordinatesReal q) + -(L (diamondProgram T).objective) := by
    have hh := congrArg (fun r : ℚ => (r : ℝ)) (diamondRationalSeparationCut_identity J v q)
    push_cast at hh
    rw [diamondRationalQuadratic_real T J hJ] at hh
    change (diamondRationalSeparationCut J v).evalReal (diamondRationalCoordinatesReal q) + _ = _
    have hev := RationalAffineCut.evalReal_rational (diamondRationalSeparationCut J v) q
    change (diamondRationalSeparationCut J v).evalReal (diamondRationalCoordinatesReal q) = _ at hev
    rw [hev]
    change _ = L
        ((diamondProgram T).constraint.adjoint (diamondRealDecode (diamondRationalCoordinatesReal q))) + _
    rw [diamondRealDecode_rational]
    change ((diamondRationalSeparationCut J v).eval q : ℝ) - ((diamondRationalSeparationCut J v).bound : ℝ) =
      L ((diamondProgram T).constraint.adjoint (diamondRationalDecode q) - (diamondProgram T).objective) at hh
    rw [map_sub] at hh
    simpa only [sub_eq_add_neg] using! hh
  have hh := realAffine_eq_of_rational f g (-((diamondRationalSeparationCut J v).bound : ℝ))
    (-(L (diamondProgram T).objective)) hr x
  change _ + -_ = L ((diamondProgram T).constraint.adjoint (diamondRealDecode x)) + _ at hh
  simp only [← sub_eq_add_neg] at hh
  rw [← map_sub] at hh
  exact hh

/-- Every real coordinate point decoding to diamond dual feasible data satisfies the real
extension of a rational separation cut. -/
theorem diamondRationalSeparationCut_preserves_real {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) (x : DiamondRealCoordinates D E)
    (hx : (diamondProgram T).DualFeasible (diamondRealDecode x)) :
    ((diamondRationalSeparationCut J v).bound : ℝ) ≤ (diamondRationalSeparationCut J v).evalReal x := by
  have hn := (HermitianMat.zero_le_iff.mp hx).re_dotProduct_nonneg
    (fun i => gaussianRationalEmbed v[diamondRationalRegisterEquiv D E i])
  change 0 ≤ hermitianQuadraticLinear _ _ at hn
  rw [← diamondRationalSeparationCut_real_identity T J hJ v x] at hn
  linarith

/-- A rational separation oracle cut strictly rejects its candidate and preserves all real
coordinates decoding to diamond dual feasible data. -/
theorem diamondRationalSeparationOracle_cut_real {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (q : DiamondRationalCoordinates D E)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSeparationOracle J q = .cut C) :
    C.eval q < C.bound ∧ ∀ x : DiamondRealCoordinates D E,
      (diamondProgram T).DualFeasible (diamondRealDecode x) → (C.bound : ℝ) ≤ C.evalReal x := by
  unfold diamondRationalSeparationOracle at hc
  cases hv : diamondRationalCandidateSeparate J q with
  | nonHermitian => simp [hv] at hc
  | psd => simp [hv] at hc
  | negative v =>
    simp only [hv,RationalSeparationResult.cut.injEq] at hc
    subst C
    exact ⟨diamondRationalSeparationCut_rejects J q v hv,
      fun x hx => diamondRationalSeparationCut_preserves_real T J hJ v x hx⟩

/-- The rational coordinate score coerces to the diamond dual score of the rational decoding. -/
theorem diamondRationalScore_cast {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (x : DiamondRationalCoordinates D E) :
    (diamondRationalScore x : ℝ) = (diamondProgram T).dualScore (diamondRationalDecode x) := by
  unfold diamondRationalScore diamondRationalDecode
  rw [diamondProgram_dualScore]
  push_cast
  rfl

/-- The real coordinate score equals the diamond dual score of the real decoding. -/
theorem diamondRealScore_eq {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (x : DiamondRealCoordinates D E) :
    diamondRealScore x = (diamondProgram T).dualScore (diamondRealDecode x) := by
  unfold diamondRealScore diamondRealDecode
  rw [diamondProgram_dualScore]

/-- The objective cut evaluates on rational coordinates as the negative rational diamond score. -/
theorem diamondRationalObjectiveCut_eval (D E : ℕ) (γ : ℚ) (x : DiamondRationalCoordinates D E) :
    (diamondRationalObjectiveCut D E γ).eval x = -diamondRationalScore x := by
  simp [RationalAffineCut.eval,diamondRationalObjectiveCut,diamondRationalScore,add_mul,Finset.sum_add_distrib,ite_mul,add_comm]

/-- The objective cut evaluates on real coordinates as the negative real diamond score. -/
theorem diamondRationalObjectiveCut_evalReal (D E : ℕ) (γ : ℚ) (x : DiamondRealCoordinates D E) :
    (diamondRationalObjectiveCut D E γ).evalReal x = -diamondRealScore x := by
  have hc (p : Prop) [Decidable p] : (((if p then (-1 : ℚ) else 0) : ℚ) : ℝ) =
      if p then (-1 : ℝ) else 0 := by split_ifs <;> norm_num
  simp [RationalAffineCut.evalReal,diamondRationalObjectiveCut,diamondRealScore,add_mul,Finset.sum_add_distrib,hc,ite_mul,add_comm]

/-- The objective cut has at least one nonzero coefficient. -/
theorem diamondRationalObjectiveCut_nonzero (D E : ℕ) (γ : ℚ) :
    ∃ k : Fin (diamondDyadicWordCount D E), (diamondRationalObjectiveCut D E γ).coefficients[k] ≠ 0 := by
  refine ⟨diamondRationalScalarIndex D E 0,?_⟩
  have hn : diamondRationalScalarIndex D E 0 ≠ diamondRationalScalarIndex D E 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [diamondRationalScalarIndex] at hv
  simp [diamondRationalObjectiveCut,hn]

/-- The rational sublevel oracle reports feasibility exactly when the decoded data are dual
feasible with score at most `γ`. -/
theorem diamondRationalSublevelOracle_feasible_iff {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (x : DiamondRationalCoordinates D E) :
    diamondRationalSublevelOracle J γ x = .feasible ↔
      (diamondProgram T).DualFeasible (diamondRationalDecode x) ∧
        (diamondProgram T).dualScore (diamondRationalDecode x) ≤ (γ : ℝ) := by
  have hb : diamondRationalScore x ≤ γ ↔ (diamondProgram T).dualScore (diamondRationalDecode x) ≤ (γ : ℝ) := by
    rw [← diamondRationalScore_cast T x]
    exact_mod_cast Iff.rfl
  unfold diamondRationalSublevelOracle
  by_cases hs : diamondRationalScore x ≤ γ
  · rw [if_pos hs,diamondRationalSeparationOracle_feasible_iff T J hJ]
    exact ⟨fun h => ⟨h,hb.mp hs⟩,fun h => h.1⟩
  · rw [if_neg hs]
    simp only [reduceCtorEq,false_iff]
    rintro ⟨_,hscore⟩
    exact hs (hb.mpr hscore)

/-- For rational Choi data, the rational sublevel oracle never returns an invalid result. -/
theorem diamondRationalSublevelOracle_not_invalid {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (x : DiamondRationalCoordinates D E) :
    diamondRationalSublevelOracle J γ x ≠ .invalid := by
  unfold diamondRationalSublevelOracle
  split_ifs
  · exact diamondRationalSeparationOracle_not_invalid T J hJ x
  · simp

/-- Every rational sublevel oracle cut strictly rejects its candidate, preserves the real dual
score sublevel set, and has a nonzero coefficient. -/
theorem diamondRationalSublevelOracle_cut {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (q : DiamondRationalCoordinates D E)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSublevelOracle J γ q = .cut C) :
    C.eval q < C.bound ∧
    (∀ x : DiamondRealCoordinates D E, (diamondProgram T).DualFeasible (diamondRealDecode x) →
      (diamondProgram T).dualScore (diamondRealDecode x) ≤ (γ : ℝ) → (C.bound : ℝ) ≤ C.evalReal x) ∧
    (∃ k : Fin (diamondDyadicWordCount D E), C.coefficients[k] ≠ 0) := by
  unfold diamondRationalSublevelOracle at hc
  by_cases hs : diamondRationalScore q ≤ γ
  · rw [if_pos hs] at hc
    obtain ⟨hrej,hkeep⟩ := diamondRationalSeparationOracle_cut_real T J hJ q C hc
    exact ⟨hrej,fun x hx _ => hkeep x hx,diamondRationalSeparationOracle_cut_nonzero T J hJ q C hc⟩
  · rw [if_neg hs] at hc
    cases RationalSeparationResult.cut.inj hc
    refine ⟨?_,?_,diamondRationalObjectiveCut_nonzero D E γ⟩
    · rw [diamondRationalObjectiveCut_eval]
      change -diamondRationalScore q < -γ
      exact neg_lt_neg (lt_of_not_ge hs)
    · intro x _ hscore
      rw [diamondRationalObjectiveCut_evalReal,diamondRealScore_eq T x]
      change ((-γ : ℚ) : ℝ) ≤ -(diamondProgram T).dualScore (diamondRealDecode x)
      rw [Rat.cast_neg]
      exact neg_le_neg hscore

/-- The first scalar coordinate of packed real diamond data is `a`. -/
@[simp] theorem diamondRealPack_scalar0 {D E : ℕ} (a b : ℝ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :
    diamondRealPack a b Y Z (diamondRationalScalarIndex D E 0) = a := by
  simp [diamondRealPack,diamondRationalScalarIndex]

/-- The second scalar coordinate of packed real diamond data is `b`. -/
@[simp] theorem diamondRealPack_scalar1 {D E : ℕ} (a b : ℝ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :
    diamondRealPack a b Y Z (diamondRationalScalarIndex D E 1) = b := by
  simp [diamondRealPack,diamondRationalScalarIndex]

/-- Extracting a raw block from packed real diamond data returns `Y` for false and `Z` for true. -/
theorem diamondRealPack_block {D E : ℕ} (a b : ℝ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) (which : Bool) :
    diamondRealRawBlock which (diamondRealPack a b Y Z) = if which then Z else Y := by
  have hword (Q : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) (i j) (part : Fin 2) :
      diamondRealCoordinateWord Q (gaussianDyadicWordIndex D E ((i,j),part)) =
        if part = 0 then (Q i j).re else (Q i j).im := by
    simp [diamondRealCoordinateWord]
  have hget (i j : Fin E × Fin D) (part : Fin 2) :
      diamondRealPack a b Y Z (diamondRationalBlockIndex D E which i j part) =
        diamondRealCoordinateWord (if which then Z else Y) (gaussianDyadicWordIndex D E ((i,j),part)) := by
    let k := gaussianDyadicWordIndex D E ((i,j),part)
    have hk := k.isLt
    have h2 : ¬ 2 + (if which then gaussianDyadicWordCount D E else 0) + k.val < 2 := by omega
    dsimp only [diamondRationalBlockIndex,diamondRealPack]
    rw [dif_neg h2]
    cases which with
    | false =>
      simp only [Bool.false_eq_true,if_false,add_zero]
      rw [dif_pos (by omega)]
      congr 1
      apply Fin.ext
      simp
    | true =>
      simp only [if_true]
      rw [dif_neg (by omega)]
      congr 1
      apply Fin.ext
      simp
  apply Matrix.ext
  intro i j
  apply Complex.ext
  · simp [diamondRealRawBlock,hget,hword]
  · simp [diamondRealRawBlock,hget,hword]

/-- Decoding packed real scalars and Hermitian matrix blocks gives their diamond dual data. -/
theorem diamondRealDecode_pack {D E : ℕ} (a b : ℝ) (Y Z : HermitianMat (Fin E × Fin D) ℂ) :
    diamondRealDecode (diamondRealPack a b Y.mat Z.mat) = diamondDualData a b Y Z := by
  have hb (H : HermitianMat (Fin E × Fin D) ℂ) : (1/2 : ℝ) • (H.mat + H.matᴴ) = H.mat := by
    rw [H.H.eq]
    module
  unfold diamondRealDecode
  rw [diamondRealPack_scalar0,diamondRealPack_scalar1]
  congr 1
  all_goals
    apply HermitianMat.ext
    change (1/2 : ℝ) • (diamondRealRawBlock _ _ + (diamondRealRawBlock _ _)ᴴ) = _
    rw [diamondRealPack_block]
    simp only [Bool.false_eq_true,if_false,if_true]
    exact hb _

/-- Decoding the real coordinate encoding recovers the original diamond dual data. -/
theorem diamondRealDecode_encode {D E : ℕ} (y : DiamondConstraints D E) :
    diamondRealDecode (diamondRealEncode y) = y := by
  unfold diamondRealEncode
  rw [diamondRealDecode_pack]
  rfl

/-- The real diamond coordinate decoder is surjective. -/
theorem diamondRealDecode_surjective (D E : ℕ) : Function.Surjective (@diamondRealDecode D E) :=
  fun y => ⟨diamondRealEncode y,diamondRealDecode_encode y⟩

local instance realCoordinatesProdTopGroup {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] :
    IsTopologicalAddGroup (WithLp 2 (A × B)) where
  continuous_add := by
    apply continuous_induced_rng.mpr
    exact ((WithLp.prod_continuous_ofLp 2 A B).comp continuous_fst).add
      ((WithLp.prod_continuous_ofLp 2 A B).comp continuous_snd)
  continuous_neg := by
    apply continuous_induced_rng.mpr
    exact (WithLp.prod_continuous_ofLp 2 A B).neg

local instance realCoordinatesProdContinuousSMul {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [SMul ℝ A] [SMul ℝ B] [ContinuousSMul ℝ A] [ContinuousSMul ℝ B] :
    ContinuousSMul ℝ (WithLp 2 (A × B)) where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    exact continuous_fst.smul ((WithLp.prod_continuous_ofLp 2 A B).comp continuous_snd)

/-- The real diamond coordinate decoder is continuous. -/
theorem diamondRealDecode_continuous (D E : ℕ) : Continuous (@diamondRealDecode D E) :=
  (diamondRealDecodeLinear D E).toContinuousLinearMap.continuous

/-- The real coordinate dual score sublevel set is closed. -/
theorem diamondRealSublevel_closed {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (γ : ℝ) :
    IsClosed (diamondRealSublevel T γ) := by
  have hΦ := diamondRealDecode_continuous D E
  have hF : IsClosed {x : DiamondRealCoordinates D E | (diamondProgram T).DualFeasible (diamondRealDecode x)} :=
    (psdCone (DiamondRegister D E)).isClosed.preimage
      (((diamondProgram T).constraint.adjoint.continuous.comp hΦ).sub continuous_const)
  have hO : IsClosed {x : DiamondRealCoordinates D E | (diamondProgram T).dualScore (diamondRealDecode x) ≤ γ} :=
    isClosed_le ((innerSL ℝ (diamondProgram T).rhs).continuous.comp hΦ) continuous_const
  exact hF.inter hO

/-- The real coordinate dual score sublevel set is convex. -/
theorem diamondRealSublevel_convex {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (γ : ℝ) :
    Convex ℝ (diamondRealSublevel T γ) := by
  intro x hx y hy a b ha hb hab
  have hΦ : diamondRealDecode (a • x+b • y) = a • diamondRealDecode x+b • diamondRealDecode y := by
    exact (diamondRealDecodeLinear D E).map_add (a • x) (b • y) |>.trans
        (by rw [map_smul,map_smul]; rfl)
  have hs : (diamondProgram T).constraint.adjoint (diamondRealDecode (a • x+b • y)) - (diamondProgram T).objective =
      a • ((diamondProgram T).constraint.adjoint (diamondRealDecode x) - (diamondProgram T).objective) +
      b • ((diamondProgram T).constraint.adjoint (diamondRealDecode y) - (diamondProgram T).objective) := by
    rw [hΦ,map_add,map_smul,map_smul]
    have hb' : b = 1-a := by linarith
    rw [hb']
    module
  constructor
  · change 0 ≤ _
    rw [hs]
    exact add_nonneg (smul_nonneg ha hx.1) (smul_nonneg hb hy.1)
  · have hscore : (diamondProgram T).dualScore (diamondRealDecode (a • x+b • y)) =
        a * (diamondProgram T).dualScore (diamondRealDecode x) + b * (diamondProgram T).dualScore (diamondRealDecode y) := by
      simp only [hΦ,Program.dualScore,inner_add_right,real_inner_smul_right]
    rw [hscore]
    calc
      _ ≤ a*γ+b*γ := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = γ := by rw [← add_mul,hab,one_mul]

section SdpCoordinateBalls

/-- The diamond coordinate norm is nonnegative. -/
theorem diamondCoordinateNorm_nonneg {D E : ℕ} (x : DiamondRealCoordinates D E) :
    0 ≤ diamondCoordinateNorm x := norm_nonneg _

/-- The absolute value of each coordinate is at most the diamond coordinate norm. -/
theorem diamondCoordinateNorm_apply_le {D E : ℕ} (x : DiamondRealCoordinates D E)
    (k : Fin (diamondDyadicWordCount D E)) : |x k| ≤ diamondCoordinateNorm x := by
  simpa only [Real.norm_eq_abs] using!
    PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) k

/-- The diamond coordinate norm is at most the sum of the absolute coordinate values. -/
theorem diamondCoordinateNorm_le_sum {D E : ℕ} (x : DiamondRealCoordinates D E) :
    diamondCoordinateNorm x ≤ ∑ k, |x k| := by
  let v : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E)) := WithLp.toLp 2 x
  have hx : v = ∑ k, PiLp.single 2 k (x k) := by ext k; simp [v]
  change ‖v‖ ≤ _
  calc
    ‖v‖ = ‖∑ k, PiLp.single 2 k (x k)‖ := congrArg norm hx
    _ ≤ ∑ k, ‖(PiLp.single 2 k (x k) : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E)))‖ := norm_sum_le _ _
    _ = _ := by simp

/-- A uniform absolute coordinate bound bounds the diamond coordinate norm by the word count
times that bound. -/
theorem diamondCoordinateNorm_le_card {D E : ℕ} (x : DiamondRealCoordinates D E) {r : ℝ}
    (hx : ∀ k, |x k| ≤ r) : diamondCoordinateNorm x ≤ diamondDyadicWordCount D E * r := by
  apply (diamondCoordinateNorm_le_sum x).trans
  calc
    ∑ k, |x k| ≤ ∑ _k : Fin (diamondDyadicWordCount D E), r := Finset.sum_le_sum (fun k _ => hx k)
    _ = _ := by simp

/-- Each coordinate of the real diamond encoding is bounded in absolute value by the norm of the
encoded dual data. -/
theorem diamondRealEncode_entry_bound {D E : ℕ} (y : DiamondConstraints D E)
    (k : Fin (diamondDyadicWordCount D E)) : |diamondRealEncode y k| ≤ ‖y‖ := by
  obtain ⟨ha,hb,hY,hZ⟩ := stinespringDual_coordinates_norm_le y
  have hw (H : HermitianMat (Fin E × Fin D) ℂ) (hH : ‖H‖ ≤ ‖y‖)
      (j : Fin (gaussianDyadicWordCount D E)) : |diamondRealCoordinateWord H.mat j| ≤ ‖y‖ := by
    dsimp only [diamondRealCoordinateWord]
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans ((hermitian_entry_norm_le H _ _).trans hH)
    · exact (Complex.abs_im_le_norm _).trans ((hermitian_entry_norm_le H _ _).trans hH)
  unfold diamondRealEncode diamondRealPack
  split_ifs
  · exact ha
  · exact hb
  · exact hw _ hY _
  · exact hw _ hZ _

/-- The real diamond encoding has coordinate norm at most the word count times the dual data
norm. -/
theorem diamondRealEncode_norm_bound {D E : ℕ} (y : DiamondConstraints D E) :
    diamondCoordinateNorm (diamondRealEncode y) ≤ diamondDyadicWordCount D E * ‖y‖ :=
  diamondCoordinateNorm_le_card _ (diamondRealEncode_entry_bound y)

/-- Each entry of a decoded real Hermitian block has norm at most twice the diamond coordinate
norm. -/
theorem diamondRealHermitianBlock_entry_bound {D E : ℕ} (b : Bool) (x : DiamondRealCoordinates D E)
    (i j : Fin E × Fin D) : ‖(diamondRealHermitianBlock b x).mat i j‖ ≤ 2 * diamondCoordinateNorm x := by
  have hr (u v : Fin E × Fin D) : ‖diamondRealRawBlock b x u v‖ ≤ 2 * diamondCoordinateNorm x := by
    have hh := Complex.norm_le_abs_re_add_abs_im (diamondRealRawBlock b x u v)
    change ‖diamondRealRawBlock b x u v‖ ≤ |x (diamondRationalBlockIndex D E b u v 0)| +
      |x (diamondRationalBlockIndex D E b u v 1)| at hh
    exact hh.trans (by linarith [diamondCoordinateNorm_apply_le x (diamondRationalBlockIndex D E b u v 0),
      diamondCoordinateNorm_apply_le x (diamondRationalBlockIndex D E b u v 1)])
  change ‖(1/2 : ℝ) • (diamondRealRawBlock b x i j + star (diamondRealRawBlock b x j i))‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have hh := norm_add_le (diamondRealRawBlock b x i j) (star (diamondRealRawBlock b x j i))
  rw [norm_star] at hh
  nlinarith [hr i j,hr j i]

/-- A decoded real Hermitian block has norm at most `2 * E * D` times the diamond coordinate
norm. -/
theorem diamondRealHermitianBlock_norm_bound {D E : ℕ} (b : Bool) (x : DiamondRealCoordinates D E) :
    ‖diamondRealHermitianBlock b x‖ ≤ 2 * (E : ℝ) * D * diamondCoordinateNorm x := by
  have h := hermitian_norm_le_card_mul_entry_bound (diamondRealHermitianBlock b x)
    (mul_nonneg (by norm_num) (diamondCoordinateNorm_nonneg x)) (diamondRealHermitianBlock_entry_bound b x)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at h
  nlinarith

/-- The real diamond decoder's norm is bounded by `diamondCoordinateLipschitz D E` times the
coordinate norm. -/
theorem diamondRealDecode_norm_bound {D E : ℕ} (x : DiamondRealCoordinates D E) :
    ‖diamondRealDecode x‖ ≤ (diamondCoordinateLipschitz D E : ℝ) * diamondCoordinateNorm x := by
  have hh := diamondDualData_norm_le_sum (x (diamondRationalScalarIndex D E 0))
    (x (diamondRationalScalarIndex D E 1)) (diamondRealHermitianBlock false x) (diamondRealHermitianBlock true x)
  change ‖diamondRealDecode x‖ ≤ _ at hh
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at hh
  have h0 := diamondCoordinateNorm_apply_le x (diamondRationalScalarIndex D E 0)
  have h1 := diamondCoordinateNorm_apply_le x (diamondRationalScalarIndex D E 1)
  have hY := diamondRealHermitianBlock_norm_bound false x
  have hZ := diamondRealHermitianBlock_norm_bound true x
  unfold diamondCoordinateLipschitz
  push_cast
  nlinarith

/-- The diamond coordinate norm of zero is zero. -/
@[simp] theorem diamondCoordinateNorm_zero (D E : ℕ) : diamondCoordinateNorm (0 : DiamondRealCoordinates D E) = 0 := by
  simp [diamondCoordinateNorm]

/-- The coordinate norm of `x` is at most the coordinate norm of `x - c` plus that of `c`. -/
theorem diamondCoordinateNorm_sub_add_le {D E : ℕ} (x c : DiamondRealCoordinates D E) :
    diamondCoordinateNorm x ≤ diamondCoordinateNorm (x-c) + diamondCoordinateNorm c := by
  have hx : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) =
      WithLp.toLp 2 (x-c) + WithLp.toLp 2 c := by
    rw [← WithLp.toLp_add]
    congr 1
    abel
  unfold diamondCoordinateNorm
  rw [hx]
  exact norm_add_le _ _

/-- Real diamond decoding preserves subtraction. -/
theorem diamondRealDecode_sub {D E : ℕ} (x c : DiamondRealCoordinates D E) :
    diamondRealDecode (x-c) = diamondRealDecode x - diamondRealDecode c :=
  (diamondRealDecodeLinear D E).map_sub x c

/-- The diamond coordinate Lipschitz constant is strictly positive. -/
theorem diamondCoordinateLipschitz_pos (D E : ℕ) : 0 < diamondCoordinateLipschitz D E := by
  unfold diamondCoordinateLipschitz
  positivity

/-- The diamond coordinate inner radius is positive for a positive rational tolerance. -/
theorem diamondCoordinateInnerRadius_pos {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) {ε : ℚ} (hε : 0 < ε) :
    0 < diamondCoordinateInnerRadius J ε :=
  div_pos (diamondRationalRadius_pos J hε) (diamondCoordinateLipschitz_pos D E)

/-- The diamond coordinate inner radius is at most one. -/
theorem diamondCoordinateInnerRadius_le_one {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) :
    diamondCoordinateInnerRadius J ε ≤ 1 := by
  have hw : diamondRationalWeight J ε ≤ 1 := min_le_left _ _
  have hd : (0 : ℚ) < 2 * (1 + E) := by positivity
  have hr : diamondRationalRadius J ε ≤ 1 := by
    unfold diamondRationalRadius
    apply (div_le_iff₀ hd).mpr
    nlinarith [Nat.cast_nonneg (α := ℚ) E]
  unfold diamondCoordinateInnerRadius
  apply (div_le_iff₀ (diamondCoordinateLipschitz_pos D E)).mpr
  unfold diamondCoordinateLipschitz
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) E) (Nat.cast_nonneg (α := ℚ) D)]

/-- A perturbation within the diamond coordinate inner radius decodes to data whose norm is at
most the rational diamond radius. -/
theorem diamondCoordinateInnerRadius_control {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ)
    (h : DiamondRealCoordinates D E) (hh : diamondCoordinateNorm h ≤ (diamondCoordinateInnerRadius J ε : ℝ)) :
    ‖diamondRealDecode h‖ ≤ (diamondRationalRadius J ε : ℝ) := by
  have hL : (0 : ℝ) < (diamondCoordinateLipschitz D E : ℝ) := by
    exact_mod_cast diamondCoordinateLipschitz_pos D E
  unfold diamondCoordinateInnerRadius at hh
  push_cast at hh
  have hm := (le_div_iff₀ hL).mp hh
  exact (diamondRealDecode_norm_bound h).trans (by nlinarith)

/-- For positive input dimension and rational tolerance, a bounded coordinate ball decodes to
strictly dual feasible points with scores within the tolerance above the diamond optimum.
Its slack is bounded below by half the rational regularization weight times the identity,
and its coordinate and decoded norms satisfy the outer radius and size bounds. -/
theorem diamondProgram_coordinate_near_optimal_ball {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 < ε) :
    ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ) (c : DiamondRealCoordinates D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      (diamondProgram T).PrimalFeasible M ∧ (diamondProgram T).primalScore M = α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      diamondCoordinateNorm c ≤ diamondDyadicWordCount D E * (diamondRationalOuterSize J ε : ℝ) ∧
      ∀ x : DiamondRealCoordinates D E, diamondCoordinateNorm (x-c) ≤ (diamondCoordinateInnerRadius J ε : ℝ) →
        ((diamondRationalWeight J ε : ℝ)/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
          (diamondProgram T).constraint.adjoint (diamondRealDecode x) - (diamondProgram T).objective ∧
        ((diamondProgram T).constraint.adjoint (diamondRealDecode x) - (diamondProgram T).objective).mat.PosDef ∧
        α ≤ (diamondProgram T).dualScore (diamondRealDecode x) ∧
        (diamondProgram T).dualScore (diamondRealDecode x) < α+(ε : ℝ) ∧
        diamondCoordinateNorm x ≤ (diamondCoordinateOuterRadius J ε : ℝ) ∧
        ‖diamondRealDecode x‖ ≤ (diamondRationalOuterSize J ε : ℝ) := by
  have he : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨α,M,z,hnorm,hM,hsM,hlo,hu,hpr,hdu,hball⟩ := diamondProgram_near_optimal_ball hD T he
  have h0 := hball 0 (by simpa only [norm_zero] using! (diamondRoundingRadius_pos T he).le)
  have hz : ‖z‖ ≤ (diamondRationalOuterSize J ε : ℝ) := by
    have hb0 : ‖z‖ ≤ diamondDyadicOuterSize T (ε : ℝ) := by
      simpa only [add_zero,diamondDyadicOuterSize] using! h0.2.2.2.2
    exact hb0.trans (diamondRationalOuterSize_bound T J hJ ε)
  let c := diamondRealEncode z
  have hc : diamondCoordinateNorm c ≤ diamondDyadicWordCount D E * (diamondRationalOuterSize J ε : ℝ) :=
    (diamondRealEncode_norm_bound z).trans (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _))
  refine ⟨α,M,c,hnorm,hM,hsM,hpr,hdu,hc,?_⟩
  intro x hx
  have hh : ‖diamondRealDecode (x-c)‖ ≤ diamondRoundingRadius T (ε : ℝ) :=
    (diamondCoordinateInnerRadius_control J ε _ hx).trans (diamondRationalRadius_le T J hJ hε.le)
  have heq : z + diamondRealDecode (x-c) = diamondRealDecode x := by
    change z + diamondRealDecode (x-diamondRealEncode z) = _
    rw [diamondRealDecode_sub,diamondRealDecode_encode]
    abel
  obtain ⟨hm,hpd,hl,hupper,hsize⟩ := hball (diamondRealDecode (x-c)) hh
  rw [heq] at hm hpd hl hupper hsize
  have hmargin : ((diamondRationalWeight J ε : ℝ)/2) • (1 : HermitianMat (DiamondRegister D E) ℂ) ≤
      (diamondProgram T).constraint.adjoint (diamondRealDecode x) - (diamondProgram T).objective := by
    have hs :=
        div_le_div_of_nonneg_right (diamondRationalWeight_le T J hJ hε.le)
        (by norm_num : (0 : ℝ) ≤ 2)
    have hi : (0 : HermitianMat (DiamondRegister D E) ℂ) ≤ 1 :=
        HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
    exact (smul_le_smul_of_nonneg_right hs hi).trans hm
  have hcoord : diamondCoordinateNorm x ≤ (diamondCoordinateOuterRadius J ε : ℝ) := by
    have ht := diamondCoordinateNorm_sub_add_le x c
    have hr : (diamondCoordinateInnerRadius J ε : ℝ) ≤ 1 := by
      exact_mod_cast diamondCoordinateInnerRadius_le_one J ε
    unfold diamondCoordinateOuterRadius
    push_cast
    linarith
  exact ⟨hmargin,hpd,hl,hupper,hcoord,hsize.trans (diamondRationalOuterSize_bound T J hJ ε)⟩

/-- The square of the diamond coordinate norm equals the sum of the squared real coordinates. -/
theorem diamondCoordinateNorm_sq {D E : ℕ} (x : DiamondRealCoordinates D E) :
    diamondCoordinateNorm x ^ 2 = ∑ k, (x k)^2 := by
  simpa only [diamondCoordinateNorm,Real.norm_eq_abs,sq_abs] using!
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin (diamondDyadicWordCount D E) => ℝ)
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E)))

/-- Membership in a diamond coordinate ball is equivalent to membership in the corresponding
Euclidean closed ball. -/
theorem diamondCoordinateBall_mem_iff {D E : ℕ} (c x : DiamondRealCoordinates D E) (r : ℝ) :
    x ∈ diamondCoordinateBall c r ↔
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ Metric.closedBall (WithLp.toLp 2 c) r := by
  rw [Metric.mem_closedBall,dist_eq_norm,← WithLp.toLp_sub]
  rfl

/-- The diamond coordinate outer radius is positive for a positive rational tolerance. -/
theorem diamondCoordinateOuterRadius_pos {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) {ε : ℚ} (hε : 0 < ε) :
    0 < diamondCoordinateOuterRadius J ε := by
  have hR := gaussianRationalNormBound_nonneg J
  have hsize : 0 < diamondRationalOuterSize J ε := by unfold diamondRationalOuterSize; positivity
  unfold diamondCoordinateOuterRadius
  positivity

/-- For positive input dimension and rational tolerance, every score threshold at least the
optimum plus the tolerance has a coordinate inner ball contained in both its dual sublevel
set and the coordinate outer ball. -/
theorem diamondProgram_coordinate_sublevel_ball {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 < ε) :
    ∃ (α : ℝ) (c : DiamondRealCoordinates D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      0 < diamondCoordinateInnerRadius J ε ∧ 0 < diamondCoordinateOuterRadius J ε ∧
      ∀ γ : ℝ, α+(ε : ℝ) ≤ γ →
        diamondCoordinateBall c (diamondCoordinateInnerRadius J ε : ℝ) ⊆
          diamondRealSublevel T γ ∩ diamondCoordinateBall 0 (diamondCoordinateOuterRadius J ε : ℝ) := by
  obtain ⟨α,M,c,hnorm,hM,hsM,hpr,hdu,hc,hball⟩ :=
      diamondProgram_coordinate_near_optimal_ball hD T J hJ hε
  refine ⟨α,c,hnorm,hpr,hdu,diamondCoordinateInnerRadius_pos J hε,diamondCoordinateOuterRadius_pos J hε,?_⟩
  intro γ hγ x hx
  obtain ⟨hm,hpd,hl,hu,hout,hsize⟩ := hball x hx
  constructor
  · exact ⟨HermitianMat.zero_le_iff.mpr hpd.posSemidef,hu.le.trans hγ⟩
  · simpa only [diamondCoordinateBall,Set.mem_setOf_eq,sub_zero] using! hout

end SdpCoordinateBalls

end RealSdpCoordinates

end RationalSdpConditioning

end RationalPsdDecision

section EuclideanCentralCut

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The retained half of a unit ball satisfies the central-cut quadratic bound with right-hand
side `n^2` for every real parameter `n > 1`. -/
theorem unitBall_centralCut_quadratic (n : ℝ) (hn : 1 < n) (u x : V) (hu : ‖u‖ = 1)
    (hx : ‖x‖ ≤ 1) (hcut : 0 ≤ ⟪u,x⟫_ℝ) :
    (n^2-1)*‖x-(1/(n+1)) • u‖^2 +
      2*(n+1)*⟪u,x-(1/(n+1)) • u⟫_ℝ^2 ≤ n^2 := by
  have hn0 : 0 < n+1 := by linarith
  have hnz : n+1 ≠ 0 := ne_of_gt hn0
  have ht : ⟪u,x⟫_ℝ ≤ 1 := by
    have hh := real_inner_le_norm u x
    rw [hu,one_mul] at hh
    exact hh.trans hx
  have hs : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hq : ⟪u,x⟫_ℝ^2 ≤ ⟪u,x⟫_ℝ := by nlinarith
  have hform : (n^2-1)*‖x-(1/(n+1)) • u‖^2 +
      2*(n+1)*⟪u,x-(1/(n+1)) • u⟫_ℝ^2 =
      (n^2-1)*‖x‖^2 + 2*(n+1)*⟪u,x⟫_ℝ^2 - 2*(n+1)*⟪u,x⟫_ℝ + 1 := by
    rw [norm_sub_sq_real,inner_sub_right,inner_smul_right,inner_smul_right,
      real_inner_self_eq_norm_sq,real_inner_comm x u,norm_smul,hu]
    simp only [one_pow,mul_one,Real.norm_eq_abs]
    rw [abs_of_pos (one_div_pos.mpr hn0)]
    field_simp
    ring
  rw [hform]
  have hfirst := mul_le_mul_of_nonneg_left hs (by nlinarith : 0 ≤ n^2-1)
  have hsecond := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ 2*(n+1))
  nlinarith

end

/-- Pairing a cut's Euclidean normal with a coordinate vector equals its real coefficient
evaluation. -/
theorem RationalAffineCut.euclideanNormal_inner {n : ℕ} (C : RationalAffineCut n) (x : Fin n → ℝ) :
    ⟪C.euclideanNormal,WithLp.toLp 2 x⟫_ℝ = C.evalReal x := by
  simp [RationalAffineCut.euclideanNormal,PiLp.inner_apply,RationalAffineCut.evalReal,mul_comm]

/-- A rational affine cut with a nonzero coefficient has nonzero Euclidean normal. -/
theorem RationalAffineCut.euclideanNormal_ne_zero {n : ℕ} (C : RationalAffineCut n)
    (hC : ∃ k : Fin n, C.coefficients[k] ≠ 0) : C.euclideanNormal ≠ 0 := by
  intro hz
  obtain ⟨k,hk⟩ := hC
  have ht := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v k) hz
  change ((C.coefficients[k] : ℚ) : ℝ) = 0 at ht
  exact hk (Rat.cast_eq_zero.mp ht)

/-- A rational affine cut with a nonzero coefficient has unit normal of norm one. -/
theorem RationalAffineCut.norm_unitNormal {n : ℕ} (C : RationalAffineCut n)
    (hC : ∃ k : Fin n, C.coefficients[k] ≠ 0) : ‖C.unitNormal‖ = 1 :=
  norm_smul_inv_norm ((Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_ne_zero (C := C)) hC)

/-- In dimension at least two, the central-cut ellipsoid contains every unit-ball point in the
retained half-space. -/
theorem euclideanCentralCutEllipsoid_contains {n : ℕ} (hn : 2 ≤ n)
    (u x : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) (hcut : 0 ≤ ⟪u,x⟫_ℝ) :
    x ∈ euclideanCentralCutEllipsoid u := by
  exact unitBall_centralCut_quadratic (n : ℝ)
      (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)) u x hu hx hcut

/-- If a cut rejects the center and retains a point in a positive-radius ball, the normalized
displacement lies in the cut's central ellipsoid. -/
theorem RationalAffineCut.centralCut_retains {n : ℕ} (hn : 2 ≤ n) (C : RationalAffineCut n)
    (hC : ∃ k : Fin n, C.coefficients[k] ≠ 0) (q : Fin n → ℚ) (x : Fin n → ℝ)
    (hreject : C.eval q < C.bound) (hkeep : (C.bound : ℝ) ≤ C.evalReal x)
    {R : ℝ} (hR : 0 < R)
    (hx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) - WithLp.toLp 2 (fun k => (q k : ℝ))‖ ≤ R) :
    R⁻¹ • ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) - WithLp.toLp 2 (fun k => (q k : ℝ))) ∈
      euclideanCentralCutEllipsoid C.unitNormal := by
  have hqr : C.evalReal (fun k => (q k : ℝ)) < (C.bound : ℝ) := by
    rw [(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.evalReal_rational (C := C))]
    exact_mod_cast hreject
  apply euclideanCentralCutEllipsoid_contains hn _ _
      ((Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.norm_unitNormal (C := C)) hC)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_one₀ hR).mpr hx
  · rw [RationalAffineCut.unitNormal,inner_smul_left,inner_smul_right,inner_sub_right,
      (Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_inner (C := C)),(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_inner (C := C))]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (mul_nonneg (inv_pos.mpr hR).le (by linarith))

/-- For a unit normal, the central-cut shape determinant is `(n^2 / (n^2 - 1))^n * ((n - 1) / (n
+ 1))`. -/
theorem euclideanCentralCutShape_det {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    (euclideanCentralCutShape u).det =
      ((n : ℝ)^2/((n : ℝ)^2-1))^n * (((n : ℝ)-1)/((n : ℝ)+1)) := by
  have hdot : WithLp.ofLp u ⬝ᵥ WithLp.ofLp u = 1 := by
    change ⟪u,u⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq,hu,one_pow]
  have heq : (1 : Matrix (Fin n) (Fin n) ℝ) - (2/((n : ℝ)+1)) •
      Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u) =
      1 + Matrix.replicateCol Unit ((-(2/((n : ℝ)+1))) • WithLp.ofLp u) * Matrix.replicateRow Unit (WithLp.ofLp u) := by
    rw [← Matrix.vecMulVec_eq Unit,Matrix.smul_vecMulVec]
    module
  unfold euclideanCentralCutShape
  rw [Matrix.det_smul,Fintype.card_fin,heq,Matrix.det_one_add_replicateCol_mul_replicateRow]
  rw [dotProduct_smul,hdot,smul_eq_mul,mul_one]
  congr 1
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- In dimension at least two, a central-cut shape with unit normal has positive determinant
bounded above by `n / (n + 1)`. -/
theorem euclideanCentralCutShape_det_bounds {n : ℕ} (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    0 < (euclideanCentralCutShape u).det ∧ (euclideanCentralCutShape u).det ≤ (n : ℝ)/((n : ℝ)+1) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by linarith
  have hnp : (0 : ℝ) < (n : ℝ)+1 := by linarith
  have hns : (0 : ℝ) < (n : ℝ)^2-1 := by nlinarith
  rw [euclideanCentralCutShape_det u hu]
  constructor
  · exact mul_pos (pow_pos (div_pos (sq_pos_of_pos hn0) hns) _) (div_pos hn1 hnp)
  · have hbase : (0 : ℝ) < 1 - 1/(n : ℝ)^2 := by
      apply sub_pos.mpr
      exact (div_lt_one (sq_pos_of_pos hn0)).mpr (by nlinarith)
    have hb := one_add_mul_le_pow (a := -(1/(n : ℝ)^2)) (by
      have hh : 1/(n : ℝ)^2 < 1 := by linarith
      linarith) n
    have hb' : ((n : ℝ)-1)/(n : ℝ) ≤ (1-1/(n : ℝ)^2)^n := by
      convert! hb using 1
      field_simp
      ring
    have hpow : ((n : ℝ)^2/((n : ℝ)^2-1))^n * (1-1/(n : ℝ)^2)^n = 1 := by
      rw [← mul_pow]
      have hi : (n : ℝ)^2/((n : ℝ)^2-1) * (1-1/(n : ℝ)^2) = 1 := by
        field_simp
      rw [hi,one_pow]
    have hm := mul_le_mul_of_nonneg_left hb' (pow_pos (div_pos (sq_pos_of_pos hn0) hns) n).le
    rw [hpow] at hm
    have hh : ((n : ℝ)^2/((n : ℝ)^2-1))^n ≤ (n : ℝ)/((n : ℝ)-1) := by
      apply (le_div_iff₀ hn1).mpr
      rw [← mul_div_assoc] at hm
      simpa only [one_mul] using! (div_le_iff₀ hn0).mp hm
    have hfinal := mul_le_mul_of_nonneg_right hh (div_pos hn1 hnp).le
    have heq : (n : ℝ)/((n : ℝ)-1) * (((n : ℝ)-1)/((n : ℝ)+1)) = (n : ℝ)/((n : ℝ)+1) := by
      field_simp
    simpa only [heq] using! hfinal

/-- The real coordinate dot product equals the Euclidean inner product after applying
`WithLp.toLp 2`. -/
theorem euclidean_dot_inner {n : ℕ} (v w : Fin n → ℝ) :
    v ⬝ᵥ w = ⟪(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)),WithLp.toLp 2 w⟫_ℝ := by
  simp [dotProduct,PiLp.inner_apply,mul_comm]

/-- The central-cut shape quadratic form is the scaled squared norm minus the corresponding
scaled squared normal component. -/
theorem euclideanCentralCutShape_quadratic {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ) :
    v ⬝ᵥ ((euclideanCentralCutShape u) *ᵥ v) =
      ((n : ℝ)^2/((n : ℝ)^2-1)) *
        (‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 -
          (2/((n : ℝ)+1))*⟪u,WithLp.toLp 2 v⟫_ℝ^2) := by
  rw [euclideanCentralCutShape,Matrix.smul_mulVec,dotProduct_smul,Matrix.sub_mulVec,
    dotProduct_sub,Matrix.one_mulVec,Matrix.smul_mulVec,dotProduct_smul,Matrix.vecMulVec_mulVec,
    dotProduct_smul,euclidean_dot_inner,euclidean_dot_inner,euclidean_dot_inner]
  simp only [WithLp.toLp_ofLp,op_smul_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [real_inner_comm (WithLp.toLp 2 v) u]
  ring

/-- In dimension at least two, a central-cut shape with unit normal is positive definite. -/
theorem euclideanCentralCutShape_posDef {n : ℕ} (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) : (euclideanCentralCutShape u).PosDef := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnp : (0 : ℝ) < (n : ℝ)+1 := by linarith
  have hns : (0 : ℝ) < (n : ℝ)^2-1 := by nlinarith
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.smul _ (by apply isSelfAdjoint_iff.mpr; rfl)
    apply Matrix.IsHermitian.sub Matrix.isHermitian_one
    apply Matrix.IsHermitian.smul _ (by apply isSelfAdjoint_iff.mpr; rfl)
    ext i j
    simp [Matrix.conjTranspose_apply,Matrix.vecMulVec,mul_comm]
  · intro v hv
    have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro hz
      apply hv
      exact congrArg WithLp.ofLp hz
    have hnv : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 :=
        sq_pos_of_pos (norm_pos_iff.mpr hv')
    have hinner := abs_real_inner_le_norm u (WithLp.toLp 2 v)
    rw [hu,one_mul] at hinner
    have hib : ⟪u,WithLp.toLp 2 v⟫_ℝ^2 ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 := by
      nlinarith [abs_nonneg ⟪u,WithLp.toLp 2 v⟫_ℝ,sq_abs ⟪u,WithLp.toLp 2 v⟫_ℝ]
    have hlam : (2 : ℝ)/((n : ℝ)+1) < 1 := (div_lt_one hnp).mpr (by linarith)
    have hlam0 : (0 : ℝ) ≤ 2/((n : ℝ)+1) := (div_pos (by norm_num) hnp).le
    have hb := mul_le_mul_of_nonneg_left hib hlam0
    have hp : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 -
        (2/((n : ℝ)+1))*⟪u,WithLp.toLp 2 v⟫_ℝ^2 := by nlinarith
    simp only [star_trivial]
    rw [euclideanCentralCutShape_quadratic]
    exact mul_pos (div_pos (sq_pos_of_pos hn0) hns) hp

/-- The inverse central-cut shape is the identity scaled by `(n^2 - 1) / n^2` plus the normal
outer product scaled by `2 * (n + 1) / n^2`. -/
theorem euclideanCentralCutShape_inv {n : ℕ} (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    (euclideanCentralCutShape u)⁻¹ = (((n : ℝ)^2-1)/(n : ℝ)^2) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      (2*((n : ℝ)+1)/(n : ℝ)^2) • Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hnp : (n : ℝ)+1 ≠ 0 := by linarith
  have hns : (n : ℝ)^2-1 ≠ 0 := by nlinarith
  let P := Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)
  have hdot : WithLp.ofLp u ⬝ᵥ WithLp.ofLp u = 1 := by
    change ⟪u,u⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq,hu,one_pow]
  have hP : P*P = P := by
    dsimp [P]
    rw [Matrix.vecMulVec_mul_vecMulVec,hdot,one_smul]
  let k := (n : ℝ)^2/((n : ℝ)^2-1)
  let l := 2/((n : ℝ)+1)
  let t := ((n : ℝ)^2-1)/(n : ℝ)^2
  let m := 2*((n : ℝ)+1)/(n : ℝ)^2
  change (k • (1-l • P))⁻¹ = t • 1+m • P
  apply Matrix.inv_eq_right_inv
  have heq : (k • (1-l • P))*(t • 1+m • P) =
      (k*t) • (1 : Matrix (Fin n) (Fin n) ℝ)+(k*m-k*l*t-k*l*m) • P := by
    simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.sub_mul,Matrix.mul_add,
      Matrix.one_mul,Matrix.mul_one,hP,smul_smul]
    module
  have ha : k*t = 1 := by dsimp [k,t]; field_simp
  have hb : k*m-k*l*t-k*l*m = 0 := by dsimp [k,l,t,m]; field_simp; ring
  rw [heq,ha,hb,one_smul,zero_smul,add_zero]

/-- Central-cut ellipsoid membership is equivalent to the inverse-shape quadratic bound on
displacement from its center. -/
theorem euclideanCentralCutEllipsoid_iff_inverse {n : ℕ} (hn : 2 ≤ n)
    (u x : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    x ∈ euclideanCentralCutEllipsoid u ↔
      WithLp.ofLp (x-euclideanCentralCutCenter u) ⬝ᵥ
        ((euclideanCentralCutShape u)⁻¹ *ᵥ WithLp.ofLp (x-euclideanCentralCutCenter u)) ≤ 1 := by
  rw [euclideanCentralCutShape_inv hn u hu]
  rw [Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,
    Matrix.smul_mulVec,dotProduct_smul,Matrix.vecMulVec_mulVec,dotProduct_smul,
    euclidean_dot_inner,euclidean_dot_inner,euclidean_dot_inner]
  simp only [WithLp.toLp_ofLp,op_smul_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [real_inner_comm (x-euclideanCentralCutCenter u) u]
  have hn0 : (0 : ℝ) < (n : ℝ)^2 := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  change _ ≤ (n : ℝ)^2 ↔ _ ≤ 1
  rw [real_inner_comm (x-euclideanCentralCutCenter u) u]
  rw [← div_le_one hn0]
  ring_nf

/-- A rational sublevel oracle cut has a unit normal and positive definite central-cut shape
with positive determinant at most `n / (n + 1)`, where `n` is the coordinate count. Its
central ellipsoid retains normalized displacements of sublevel points within the given
positive radius. -/
theorem diamondRationalSublevelOracle_centralCut {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (q : DiamondRationalCoordinates D E)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSublevelOracle J γ q = .cut C)
    {R : ℝ} (hR : 0 < R) :
    ‖C.unitNormal‖ = 1 ∧ (euclideanCentralCutShape C.unitNormal).PosDef ∧
      0 < (euclideanCentralCutShape C.unitNormal).det ∧
      (euclideanCentralCutShape C.unitNormal).det ≤
        (diamondDyadicWordCount D E : ℝ)/((diamondDyadicWordCount D E : ℝ)+1) ∧
      ∀ x ∈ diamondRealSublevel T (γ : ℝ),
        diamondCoordinateNorm (x-diamondRationalCoordinatesReal q) ≤ R →
        R⁻¹ • ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) -
          WithLp.toLp 2 (diamondRationalCoordinatesReal q)) ∈ euclideanCentralCutEllipsoid C.unitNormal := by
  obtain ⟨hrej,hkeep,hnz⟩ := diamondRationalSublevelOracle_cut T J hJ γ q C hc
  have hn : 2 ≤ diamondDyadicWordCount D E := by unfold diamondDyadicWordCount; omega
  have hu :=
      (Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.norm_unitNormal (C := C)) hnz
  obtain ⟨hdet,hbound⟩ := euclideanCentralCutShape_det_bounds hn C.unitNormal hu
  refine ⟨hu,euclideanCentralCutShape_posDef hn _ hu,hdet,hbound,?_⟩
  intro x hx hball
  apply (Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.centralCut_retains (C := C)) hn hnz q x hrej (hkeep x hx.1 hx.2) hR
  rw [← WithLp.toLp_sub]
  exact hball

end EuclideanCentralCut

section AffineEllipsoidCut

/-- Euclidean matrix application preserves subtraction. -/
theorem euclideanMatrixApply_sub {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : euclideanMatrixApply A (x-y) = euclideanMatrixApply A x - euclideanMatrixApply A y := by
  simp [euclideanMatrixApply,WithLp.ofLp_sub,Matrix.mulVec_sub,WithLp.toLp_sub]

/-- Euclidean application of a matrix product equals successive application of its factors. -/
theorem euclideanMatrixApply_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : euclideanMatrixApply (A*B) x = euclideanMatrixApply A (euclideanMatrixApply B x) := by
  simp [euclideanMatrixApply,Matrix.mulVec_mulVec]

/-- Euclidean application of the identity matrix fixes every vector. -/
theorem euclideanMatrixApply_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : euclideanMatrixApply 1 x = x := by
  simp [euclideanMatrixApply]

/-- An invertible congruence preserves the inverse-matrix quadratic form after the corresponding
change of vector. -/
theorem euclidean_congruence_inverse_quadratic {n : ℕ} (S B : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) (v : Fin n → ℝ) :
    (S *ᵥ v) ⬝ᵥ ((S*B*Sᵀ)⁻¹ *ᵥ (S *ᵥ v)) = v ⬝ᵥ (B⁻¹ *ᵥ v) := by
  have hcancel : S⁻¹ *ᵥ (S *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul S hS,Matrix.one_mulVec]
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,← Matrix.transpose_nonsing_inv]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec,hcancel]
  exact dotProduct_comm _ _

/-- An invertible affine change of coordinates transports shape ellipsoid membership to the
inverse quadratic bound for the original shape. -/
theorem euclideanShapeEllipsoid_affine_iff {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (S B : Matrix (Fin n) (Fin n) ℝ) (hS : IsUnit S.det) (v : EuclideanSpace ℝ (Fin n)) :
    c+euclideanMatrixApply S v ∈ euclideanShapeEllipsoid c (S*B*Sᵀ) ↔
      WithLp.ofLp v ⬝ᵥ (B⁻¹ *ᵥ WithLp.ofLp v) ≤ 1 := by
  change WithLp.ofLp (c+euclideanMatrixApply S v-c) ⬝ᵥ
    ((S*B*Sᵀ)⁻¹ *ᵥ WithLp.ofLp (c+euclideanMatrixApply S v-c)) ≤ 1 ↔ _
  rw [add_sub_cancel_left]
  exact (congrArg (fun t : ℝ => t ≤ 1) (euclidean_congruence_inverse_quadratic S B hS (WithLp.ofLp v))).to_iff

/-- Euclidean application of a transposed matrix is adjoint to application of the original
matrix. -/
theorem euclideanMatrixApply_transpose_inner {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (g v : EuclideanSpace ℝ (Fin n)) : ⟪euclideanMatrixApply Sᵀ g,v⟫_ℝ = ⟪g,euclideanMatrixApply S v⟫_ℝ := by
  change ⟪(WithLp.toLp 2 (Sᵀ *ᵥ WithLp.ofLp g) : EuclideanSpace ℝ (Fin n)),WithLp.toLp 2 (WithLp.ofLp v)⟫_ℝ =
    ⟪(WithLp.toLp 2 (WithLp.ofLp g) : EuclideanSpace ℝ (Fin n)),WithLp.toLp 2 (S *ᵥ WithLp.ofLp v)⟫_ℝ
  rw [← euclidean_dot_inner,← euclidean_dot_inner,dotProduct_comm]
  exact Matrix.dotProduct_transpose_mulVec S _ _

/-- An invertible matrix sends every nonzero Euclidean vector to a nonzero vector. -/
theorem euclideanMatrixApply_ne_zero {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) : euclideanMatrixApply S g ≠ 0 := by
  intro hz
  apply hg
  have hinj := Matrix.mulVec_injective_of_isUnit (S.isUnit_iff_isUnit_det.mpr hS)
  have hh : WithLp.ofLp g = 0 :=
      hinj (by simpa [euclideanMatrixApply] using! congrArg WithLp.ofLp hz)
  exact congrArg (WithLp.toLp 2) hh

/-- The normalized pullback of a nonzero normal through an invertible matrix has norm one. -/
theorem euclideanPullbackUnit_norm {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) : ‖euclideanPullbackUnit S g‖ = 1 := by
  exact norm_smul_inv_norm (euclideanMatrixApply_ne_zero Sᵀ (by simpa using! hS) hg)

/-- The affine image of a vector lies in the ellipsoid with shape `S * Sᵀ` exactly when the
vector has norm at most one. -/
theorem euclideanShapeEllipsoid_unit_affine_iff {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsUnit S.det) (v : EuclideanSpace ℝ (Fin n)) :
    c+euclideanMatrixApply S v ∈ euclideanShapeEllipsoid c (S*Sᵀ) ↔ ‖v‖ ≤ 1 := by
  have hh := euclideanShapeEllipsoid_affine_iff c S 1 hS v
  simp only [Matrix.mul_one,inv_one,Matrix.one_mulVec] at hh
  rw [euclidean_dot_inner,WithLp.toLp_ofLp,real_inner_self_eq_norm_sq] at hh
  exact hh.trans (by constructor <;> intro h <;> nlinarith [norm_nonneg v])

/-- In dimension at least two, an affine cut shape from an invertible matrix and a nonzero
normal is positive definite. -/
theorem euclideanAffineCutShape_posDef {n : ℕ} (hn : 2 ≤ n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsUnit S.det)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) : (euclideanAffineCutShape S g).PosDef := by
  have hB := euclideanCentralCutShape_posDef hn _ (euclideanPullbackUnit_norm S hS hg)
  have hi := Matrix.mulVec_injective_of_isUnit (Sᵀ.isUnit_iff_isUnit_det.mpr (by simpa using! hS))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using!
    hB.conjTranspose_mul_mul_same hi

/-- In dimension at least two, the affine cut shape for an invertible matrix and nonzero normal
has positive determinant at most `n / (n + 1)` times the determinant of `S * Sᵀ`. -/
theorem euclideanAffineCutShape_det_bounds {n : ℕ} (hn : 2 ≤ n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsUnit S.det)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) :
    0 < (euclideanAffineCutShape S g).det ∧
      (euclideanAffineCutShape S g).det ≤ ((n : ℝ)/((n : ℝ)+1)) * (S*Sᵀ).det := by
  obtain ⟨hpos,hbound⟩ :=
      euclideanCentralCutShape_det_bounds hn _ (euclideanPullbackUnit_norm S hS hg)
  have hs0 : 0 < S.det^2 := sq_pos_of_ne_zero (isUnit_iff_ne_zero.mp hS)
  have heq : (euclideanAffineCutShape S g).det = S.det^2 * (euclideanCentralCutShape (euclideanPullbackUnit S g)).det := by
    simp only [euclideanAffineCutShape,Matrix.det_mul,Matrix.det_transpose]
    ring
  rw [heq]
  constructor
  · exact mul_pos hs0 hpos
  · have hh := mul_le_mul_of_nonneg_left hbound hs0.le
    simpa only [Matrix.det_mul,Matrix.det_transpose,pow_two,mul_comm,mul_left_comm,mul_assoc] using! hh

/-- In dimension at least two, the affine cut for an invertible matrix and nonzero normal
retains all original ellipsoid points in the half-space through its center. -/
theorem euclideanAffineCut_retains {n : ℕ} (hn : 2 ≤ n) (c x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsUnit S.det)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0)
    (hx : x ∈ euclideanShapeEllipsoid c (S*Sᵀ)) (hcut : 0 ≤ ⟪g,x-c⟫_ℝ) :
    x ∈ euclideanShapeEllipsoid (euclideanAffineCutCenter c S g) (euclideanAffineCutShape S g) := by
  let v := euclideanMatrixApply S⁻¹ (x-c)
  have hv : c+euclideanMatrixApply S v = x := by
    dsimp [v]
    rw [← euclideanMatrixApply_mul,Matrix.mul_nonsing_inv S hS,euclideanMatrixApply_one]
    abel
  have hnv : ‖v‖ ≤ 1 := (euclideanShapeEllipsoid_unit_affine_iff c S hS v).mp (hv ▸ hx)
  have hc : 0 ≤ ⟪euclideanPullbackUnit S g,v⟫_ℝ := by
    rw [euclideanPullbackUnit,inner_smul_left,euclideanMatrixApply_transpose_inner]
    have hmv : euclideanMatrixApply S v = x-c := by rw [← hv]; abel
    rw [hmv]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hcut
  have hin :=
      euclideanCentralCutEllipsoid_contains hn _ v (euclideanPullbackUnit_norm S hS hg) hnv hc
  have hquad :=
      (euclideanCentralCutEllipsoid_iff_inverse hn _ v (euclideanPullbackUnit_norm S hS hg)).mp hin
  have hh := (euclideanShapeEllipsoid_affine_iff (euclideanAffineCutCenter c S g) S
    (euclideanCentralCutShape (euclideanPullbackUnit S g)) hS (v-euclideanCentralCutCenter (euclideanPullbackUnit S g))).mpr hquad
  have heq : euclideanAffineCutCenter c S g + euclideanMatrixApply S (v-euclideanCentralCutCenter (euclideanPullbackUnit S g)) = x := by
    rw [euclideanMatrixApply_sub,euclideanAffineCutCenter]
    rw [← hv]
    abel
  exact heq ▸ hh

/-- Euclidean matrix application preserves real scalar multiplication. -/
theorem euclideanMatrixApply_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : euclideanMatrixApply A (r • x) = r • euclideanMatrixApply A x := by
  simp [euclideanMatrixApply,WithLp.ofLp_smul,Matrix.mulVec_smul,WithLp.toLp_smul]

/-- Every real positive definite matrix factors as `S * Sᵀ` for a matrix `S` with invertible
determinant. -/
theorem euclidean_posDef_factor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, IsUnit S.det ∧ S*Sᵀ = A := by
  let H : HermitianMat (Fin n) ℝ := ⟨A,hA.isHermitian⟩
  let S := H.sqrt.mat
  have hpd : S.PosDef := HermitianMat.sqrt_posDef (A := H) hA
  have htranspose : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hpd.isHermitian
  refine ⟨S,isUnit_iff_ne_zero.mpr hpd.det_pos.ne',?_⟩
  rw [htranspose]
  exact HermitianMat.sqrt_sq (A := H) (HermitianMat.zero_le_iff.mpr hA.posSemidef)

/-- The squared norm of the transposed matrix applied to a vector is the quadratic form of `S *
Sᵀ` on that vector. -/
theorem euclideanMatrixApply_transpose_norm_sq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖euclideanMatrixApply Sᵀ g‖^2 = WithLp.ofLp g ⬝ᵥ ((S*Sᵀ) *ᵥ WithLp.ofLp g) := by
  rw [← real_inner_self_eq_norm_sq,euclideanMatrixApply_transpose_inner,← euclideanMatrixApply_mul]
  exact (euclidean_dot_inner _ _).symm

/-- Congruence of a vector outer product by `S` equals the outer product of `S *ᵥ v`. -/
theorem euclidean_outer_congruence {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    S * Matrix.vecMulVec v v * Sᵀ = Matrix.vecMulVec (S *ᵥ v) (S *ᵥ v) := by
  rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMul_transpose]

/-- The affine cut center agrees with the ellipsoid cut center expressed directly using shape `S
* Sᵀ`. -/
theorem euclideanAffineCutCenter_formula {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    euclideanAffineCutCenter c S g = euclideanEllipsoidCutCenter c (S*Sᵀ) g := by
  have hroot : Real.sqrt (WithLp.ofLp g ⬝ᵥ ((S*Sᵀ) *ᵥ WithLp.ofLp g)) = ‖euclideanMatrixApply Sᵀ g‖ := by
    rw [← euclideanMatrixApply_transpose_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  rw [euclideanAffineCutCenter,euclideanCentralCutCenter,euclideanPullbackUnit,
    euclideanMatrixApply_smul,euclideanMatrixApply_smul,← euclideanMatrixApply_mul,smul_smul,
    euclideanEllipsoidCutCenter,hroot]
  simp only [one_div,_root_.mul_inv_rev]
  module

/-- The affine cut shape agrees with the ellipsoid cut shape expressed directly using `S * Sᵀ`. -/
theorem euclideanAffineCutShape_formula {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    euclideanAffineCutShape S g = euclideanEllipsoidCutShape (S*Sᵀ) g := by
  let r := ‖euclideanMatrixApply Sᵀ g‖⁻¹
  have hv : S *ᵥ WithLp.ofLp (euclideanPullbackUnit S g) = r • ((S*Sᵀ) *ᵥ WithLp.ofLp g) := by
    change S *ᵥ (r • (Sᵀ *ᵥ WithLp.ofLp g)) = _
    rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec]
  have hs : WithLp.ofLp g ⬝ᵥ ((S*Sᵀ) *ᵥ WithLp.ofLp g) = ‖euclideanMatrixApply Sᵀ g‖^2 :=
    (euclideanMatrixApply_transpose_norm_sq S g).symm
  rw [euclideanAffineCutShape,euclideanCentralCutShape,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.mul_smul,Matrix.smul_mul,
    euclidean_outer_congruence,hv,Matrix.smul_vecMulVec,Matrix.vecMulVec_smul,smul_smul,smul_smul]
  unfold euclideanEllipsoidCutShape
  rw [hs]
  dsimp [r]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,← inv_pow]
  module

/-- In dimension at least two, an ellipsoid cut preserves positive definiteness and has positive
determinant at most `n / (n + 1)` times the original determinant. The new ellipsoid retains
all original points in the retained half-space. -/
theorem euclideanEllipsoidCut_correct {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (c : EuclideanSpace ℝ (Fin n)) {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) :
    (euclideanEllipsoidCutShape A g).PosDef ∧
      0 < (euclideanEllipsoidCutShape A g).det ∧
      (euclideanEllipsoidCutShape A g).det ≤ ((n : ℝ)/((n : ℝ)+1))*A.det ∧
      ∀ x ∈ euclideanShapeEllipsoid c A, 0 ≤ ⟪g,x-c⟫_ℝ →
        x ∈ euclideanShapeEllipsoid (euclideanEllipsoidCutCenter c A g) (euclideanEllipsoidCutShape A g) := by
  obtain ⟨S,hS,heq⟩ := euclidean_posDef_factor A hA
  subst A
  have hs := euclideanAffineCutShape_formula S g
  have hcen := euclideanAffineCutCenter_formula c S g
  obtain ⟨hdet,hbound⟩ := euclideanAffineCutShape_det_bounds hn S hS hg
  rw [hs] at hdet hbound
  refine ⟨hs ▸ euclideanAffineCutShape_posDef hn S hS hg,hdet,hbound,?_⟩
  intro x hx hc
  have hh := euclideanAffineCut_retains hn c x S hS hg hx hc
  rwa [hs,hcen] at hh

/-- Embedding the rational ellipsoid cut shape agrees with the real ellipsoid cut shape for the
embedded normal. -/
theorem rationalEllipsoidCutShape_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : Fin n → ℚ) :
    rationalEllipsoidShapeReal (rationalEllipsoidCutShape A g) =
      euclideanEllipsoidCutShape (rationalEllipsoidShapeReal A) (WithLp.toLp 2 (fun k => (g k : ℝ))) := by
  ext i j
  simp [rationalEllipsoidShapeReal,rationalEllipsoidCutShape,euclideanEllipsoidCutShape,
    Matrix.mulVec,dotProduct,Matrix.vecMulVec]

/-- A rational sublevel oracle cut gives a positive definite shape with positive determinant at
most `n / (n + 1)` times the original determinant, where `n` is the coordinate count. The
updated ellipsoid retains sublevel points in the original ellipsoid. -/
theorem diamondRationalSublevelOracle_ellipsoidCut {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (q : DiamondRationalCoordinates D E)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSublevelOracle J γ q = .cut C)
    (A : Matrix (Fin (diamondDyadicWordCount D E)) (Fin (diamondDyadicWordCount D E)) ℚ)
    (hA : (rationalEllipsoidShapeReal A).PosDef) :
    let A' := rationalEllipsoidShapeReal (rationalEllipsoidCutShape A (fun k => C.coefficients[k]))
    let c :=
        (WithLp.toLp 2 (diamondRationalCoordinatesReal q) : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E)))
    A'.PosDef ∧ 0 < A'.det ∧
      A'.det ≤ ((diamondDyadicWordCount D E : ℝ)/((diamondDyadicWordCount D E : ℝ)+1)) * (rationalEllipsoidShapeReal A).det ∧
      ∀ x ∈ diamondRealSublevel T (γ : ℝ),
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ euclideanShapeEllipsoid c (rationalEllipsoidShapeReal A) →
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ euclideanShapeEllipsoid
          (euclideanEllipsoidCutCenter c (rationalEllipsoidShapeReal A) C.euclideanNormal) A' := by
  (try dsimp only)
  rw [rationalEllipsoidCutShape_real]
  obtain ⟨hrej,hkeep,hnz⟩ := diamondRationalSublevelOracle_cut T J hJ γ q C hc
  have hn : 2 ≤ diamondDyadicWordCount D E := by unfold diamondDyadicWordCount; omega
  let c : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E)) :=
      WithLp.toLp 2 (diamondRationalCoordinatesReal q)
  have hh :=
      euclideanEllipsoidCut_correct hn (rationalEllipsoidShapeReal A) hA c
      ((Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_ne_zero (C := C)) hnz)
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  intro x hx hball
  apply hh.2.2.2 (WithLp.toLp 2 x) hball
  have hqr : C.evalReal (diamondRationalCoordinatesReal q) < (C.bound : ℝ) := by
    change C.evalReal (fun k => (q k : ℝ)) < (C.bound : ℝ)
    rw [(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.evalReal_rational (C := C))]
    exact_mod_cast hrej
  change 0 ≤ ⟪C.euclideanNormal,(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) -
    WithLp.toLp 2 (diamondRationalCoordinatesReal q)⟫_ℝ
  rw [inner_sub_right,(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_inner (C := C)),(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_inner (C := C))]
  linarith [hkeep x hx.1 hx.2]

/-- For positive `r`, an ellipsoid with shape `r^2` times the identity is the closed ball of
radius `r` about its center. -/
theorem euclideanShapeEllipsoid_scalar_ball {n : ℕ} (c x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : x ∈ euclideanShapeEllipsoid c (r^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ↔ ‖x-c‖ ≤ r := by
  have hrs : r^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hr)
  have hi : (r^2 • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = (r^2)⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul,mul_inv_cancel₀ hrs,one_smul]
  change WithLp.ofLp (x-c) ⬝ᵥ ((r^2 • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ *ᵥ WithLp.ofLp (x-c)) ≤ 1 ↔
      _
  rw [hi,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,euclidean_dot_inner,
    WithLp.toLp_ofLp,real_inner_self_eq_norm_sq,smul_eq_mul,← div_eq_inv_mul,div_le_one (sq_pos_of_pos hr)]
  constructor <;> intro h <;> nlinarith [norm_nonneg (x-c)]

end AffineEllipsoidCut

section RationalEllipsoidCenter

/-- The rational square root upper approximation is strictly positive. -/
theorem rationalSqrtUpper_pos (s : ℚ) (p : ℕ) : 0 < rationalSqrtUpper s p := by
  unfold rationalSqrtUpper
  positivity

/-- For nonnegative rational input, the rational square root approximation is strictly above the
real square root and at most `1 / 2^p` above it. -/
theorem rationalSqrtUpper_bounds {s : ℚ} (hs : 0 ≤ s) (p : ℕ) :
    Real.sqrt (s : ℝ) < (rationalSqrtUpper s p : ℝ) ∧
      (rationalSqrtUpper s p : ℝ) ≤ Real.sqrt (s : ℝ) + 1/(2 : ℝ)^p := by
  let m := ⌊s*(2 : ℚ)^(2*p)⌋₊
  let k := Nat.sqrt m
  let b : ℝ := (2 : ℝ)^p
  have hb : 0 < b := pow_pos (by norm_num) _
  have hsr : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have hpow : (2 : ℚ)^(2*p) = ((2 : ℚ)^p)^2 := by rw [Nat.mul_comm 2 p,pow_mul]
  have hsq := Real.sq_sqrt hsr
  have hr := Real.sqrt_nonneg (s : ℝ)
  have hl : (k : ℝ)^2 ≤ (s : ℝ)*b^2 := by
    have hk : (k : ℝ)^2 ≤ (m : ℝ) := by exact_mod_cast Nat.sqrt_le' m
    have hm : (m : ℝ) ≤ (s : ℝ)*b^2 := by
      have hf : (m : ℚ) ≤ s*((2 : ℚ)^p)^2 := by
        simpa only [m,hpow] using!
            Nat.floor_le (mul_nonneg hs (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) (2*p)))
      dsimp only [b]
      exact_mod_cast hf
    exact hk.trans hm
  have hu : (s : ℝ)*b^2 < ((k : ℝ)+1)^2 := by
    have hm : (s : ℝ)*b^2 < (m : ℝ)+1 := by
      have hf : s*((2 : ℚ)^p)^2 < (m : ℚ)+1 := by
        simpa only [m,hpow] using! Nat.lt_floor_add_one (s*(2 : ℚ)^(2*p))
      dsimp only [b]
      exact_mod_cast hf
    have hk : (m : ℝ)+1 ≤ ((k : ℝ)+1)^2 := by
      have hh := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' m)
      exact_mod_cast hh
    exact hm.trans_le hk
  have hlow : (k : ℝ)/b ≤ Real.sqrt (s : ℝ) := by
    apply (div_le_iff₀ hb).mpr
    nlinarith [mul_nonneg hr hb.le, Nat.cast_nonneg (α := ℝ) k, sq_nonneg ((k : ℝ)-Real.sqrt (s : ℝ)*b)]
  have hup : Real.sqrt (s : ℝ) < ((k : ℝ)+1)/b := by
    apply (lt_div_iff₀ hb).mpr
    nlinarith [mul_nonneg hr hb.le]
  have heq : (rationalSqrtUpper s p : ℝ) = ((k : ℝ)+1)/b := by
    simp [rationalSqrtUpper,k,b,m]
  rw [heq]
  refine ⟨hup,?_⟩
  change ((k : ℝ)+1)/b ≤ Real.sqrt (s : ℝ)+1/b
  rw [add_div]
  linarith

/-- For positive rational `s`, `min s 1` is a lower bound for its real square root. -/
theorem rationalSqrt_lower_bound {s : ℚ} (hs : 0 < s) :
    ((min s 1 : ℚ) : ℝ) ≤ Real.sqrt (s : ℝ) := by
  have h0 : (0 : ℝ) < (min s 1 : ℚ) := by exact_mod_cast lt_min hs (by norm_num : (0 : ℚ) < 1)
  have h1 : ((min s 1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast min_le_right s (1 : ℚ)
  have h2 : ((min s 1 : ℚ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast min_le_left s (1 : ℚ)
  have hs0 : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hr := Real.sqrt_nonneg (s : ℝ)
  have hrs := Real.sq_sqrt hs0
  nlinarith [mul_nonneg h0.le (sub_nonneg.mpr h1)]

/-- The chosen rational square root precision makes `1 / 2^p` at most `η * min s 1` for positive
`s` and `η`. -/
theorem rationalSqrtPrecision_sufficient {s η : ℚ} (hs : 0 < s) (hη : 0 < η) :
    1/(2 : ℝ)^(rationalSqrtPrecision s η) ≤ (η : ℝ)*((min s 1 : ℚ) : ℝ) := by
  unfold rationalSqrtPrecision
  apply dyadicPrecision_sufficient
      (by exact_mod_cast mul_pos hη (lt_min hs (by norm_num : (0 : ℚ) < 1)))
  exact_mod_cast Nat.le_ceil (1/(η*min s 1))

/-- For positive input and relative tolerance, the selected rational square root upper bound
lies between the square root and `1 + η` times it. The ratio of the square root to this
bound lies between `1 - η` and one. -/
theorem rationalSqrtUpper_relative {s η : ℚ} (hs : 0 < s) (hη : 0 < η) :
    let r := (rationalSqrtUpper s (rationalSqrtPrecision s η) : ℝ)
    0 < r ∧ Real.sqrt (s : ℝ) < r ∧ r ≤ (1+(η : ℝ))*Real.sqrt (s : ℝ) ∧
      1-(η : ℝ) ≤ Real.sqrt (s : ℝ)/r ∧ Real.sqrt (s : ℝ)/r ≤ 1 := by
  (try dsimp only)
  have hr : (0 : ℝ) < (rationalSqrtUpper s (rationalSqrtPrecision s η) : ℝ) := by
    exact_mod_cast rationalSqrtUpper_pos s (rationalSqrtPrecision s η)
  obtain ⟨hl,hu⟩ := rationalSqrtUpper_bounds hs.le (rationalSqrtPrecision s η)
  have hηr : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
  have he := rationalSqrtPrecision_sufficient hs hη
  have hsmall := mul_le_mul_of_nonneg_left (rationalSqrt_lower_bound hs) hηr
  have hupper : (rationalSqrtUpper s (rationalSqrtPrecision s η) : ℝ) ≤ (1+(η : ℝ))*Real.sqrt (s : ℝ) := by
    nlinarith
  refine ⟨hr,hl,hupper,?_,(div_le_one hr).mpr hl.le⟩
  apply (le_div_iff₀ hr).mpr
  nlinarith [mul_le_mul_of_nonneg_left hl.le hηr]

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For `n > 1`, nonnegative `η`, and center-shift factor between `1 - η` and one, every
retained unit-ball point has approximate central-cut quadratic expression at most `(n +
η)^2`. -/
theorem unitBall_approxCentralCut_quadratic (n : ℝ) (hn : 1 < n) (u x : V) (hu : ‖u‖ = 1)
    (hx : ‖x‖ ≤ 1) (hcut : 0 ≤ ⟪u,x⟫_ℝ) {η θ : ℝ}
    (hη : 0 ≤ η) (hθlo : 1-η ≤ θ) (hθhi : θ ≤ 1) :
    (n^2-1)*‖x-(θ/(n+1)) • u‖^2 +
      2*(n+1)*⟪u,x-(θ/(n+1)) • u⟫_ℝ^2 ≤ (n+η)^2 := by
  have hnp : 0 < n+1 := by linarith
  have hnz : n+1 ≠ 0 := ne_of_gt hnp
  have ht : ⟪u,x⟫_ℝ ≤ 1 := by
    have hh := real_inner_le_norm u x
    rw [hu,one_mul] at hh
    exact hh.trans hx
  have hs : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hq : ⟪u,x⟫_ℝ^2 ≤ ⟪u,x⟫_ℝ := by nlinarith
  have hform : (n^2-1)*‖x-(θ/(n+1)) • u‖^2 +
      2*(n+1)*⟪u,x-(θ/(n+1)) • u⟫_ℝ^2 =
      (n^2-1)*‖x‖^2 + 2*(n+1)*⟪u,x⟫_ℝ^2 - 2*(n+1)*θ*⟪u,x⟫_ℝ + θ^2 := by
    rw [norm_sub_sq_real,inner_sub_right,inner_smul_right,inner_smul_right,
      real_inner_self_eq_norm_sq,real_inner_comm x u,norm_smul,hu]
    simp only [one_pow,mul_one,Real.norm_eq_abs,sq_abs]
    field_simp
    ring
  rw [hform]
  have hfirst := mul_le_mul_of_nonneg_left hs (by nlinarith : 0 ≤ n^2-1)
  have hsecond := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ 2*(n+1))
  have hδ : 0 ≤ 1-θ := sub_nonneg.mpr hθhi
  have hthird := mul_le_mul_of_nonneg_left ht (mul_nonneg (by linarith : 0 ≤ 2*(n+1)) hδ)
  have hmid : (n^2-1)*‖x‖^2 + 2*(n+1)*⟪u,x⟫_ℝ^2 - 2*(n+1)*θ*⟪u,x⟫_ℝ + θ^2 ≤ (n+(1-θ))^2 := by
    nlinarith
  have hlast : (n+(1-θ))^2 ≤ (n+η)^2 := by nlinarith
  exact hmid.trans hlast

end

/-- The inverse of a nonzero scalar multiple of an invertible real matrix is the inverse matrix
scaled by the reciprocal scalar. -/
theorem realMatrix_inv_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) {t : ℝ} (ht : t ≠ 0) : (t • A)⁻¹ = t⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_nonsing_inv A hA,smul_smul,mul_inv_cancel₀ ht,one_smul]

/-- For positive shape scaling, ellipsoid membership is equivalent to bounding the original
inverse-shape quadratic form by the scale. -/
theorem euclideanShapeEllipsoid_smul_iff {n : ℕ} (c x : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) {t : ℝ} (ht : 0 < t) :
    x ∈ euclideanShapeEllipsoid c (t • A) ↔ WithLp.ofLp (x-c) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp (x-c)) ≤ t := by
  change _ ⬝ᵥ ((t • A)⁻¹ *ᵥ _) ≤ 1 ↔ _
  rw [realMatrix_inv_smul A hA ht.ne',Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,
    ← div_eq_inv_mul,div_le_one ht]

/-- The inverse central-cut shape quadratic form equals the weighted sum of the squared norm and
squared normal component divided by `n^2`. -/
theorem euclideanCentralCutShape_inverse_quadratic {n : ℕ} (hn : 2 ≤ n)
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    WithLp.ofLp v ⬝ᵥ ((euclideanCentralCutShape u)⁻¹ *ᵥ WithLp.ofLp v) =
      (((n : ℝ)^2-1)*‖v‖^2 + 2*((n : ℝ)+1)*⟪u,v⟫_ℝ^2)/(n : ℝ)^2 := by
  rw [euclideanCentralCutShape_inv hn u hu,Matrix.add_mulVec,dotProduct_add,
    Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,Matrix.smul_mulVec,dotProduct_smul,
    Matrix.vecMulVec_mulVec,dotProduct_smul,euclidean_dot_inner,euclidean_dot_inner,euclidean_dot_inner]
  simp only [WithLp.toLp_ofLp,op_smul_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [real_inner_comm v u]
  ring

/-- In dimension at least two, an approximate central cut with nonnegative `η` and shift factor
between `1 - η` and one retains the unit half-ball after inflating the shape by `(1 + η /
n)^2`. -/
theorem euclideanApproxCentralCut_contains {n : ℕ} (hn : 2 ≤ n)
    (u x : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) (hcut : 0 ≤ ⟪u,x⟫_ℝ)
    {η θ : ℝ} (hη : 0 ≤ η) (hθlo : 1-η ≤ θ) (hθhi : θ ≤ 1) :
    x ∈ euclideanShapeEllipsoid ((θ/((n : ℝ)+1)) • u)
      ((1+η/(n : ℝ))^2 • euclideanCentralCutShape u) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hf : 0 < (1+η/(n : ℝ))^2 := sq_pos_of_pos (by positivity)
  have hB := euclideanCentralCutShape_posDef hn u hu
  rw [euclideanShapeEllipsoid_smul_iff _ _ _ (isUnit_iff_ne_zero.mpr hB.det_pos.ne') hf,
    euclideanCentralCutShape_inverse_quadratic hn u _ hu]
  apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
  have hh := unitBall_approxCentralCut_quadratic (n : ℝ) (by linarith) u x hu hx hcut hη hθlo hθhi
  have heq : (1+η/(n : ℝ))^2*(n : ℝ)^2 = ((n : ℝ)+η)^2 := by
    field_simp
  rwa [heq]

/-- In dimension at least two, a positive definite ellipsoid cut with nonzero normal and
normalization ratio between `1 - η` and one retains the original half-ellipsoid after shape
inflation by `(1 + η / n)^2`, for nonnegative `η`. -/
theorem euclideanApproxCut_retains {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (c x : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (hθlo : 1-η ≤ Real.sqrt (WithLp.ofLp g ⬝ᵥ (A *ᵥ WithLp.ofLp g))/r)
    (hθhi : Real.sqrt (WithLp.ofLp g ⬝ᵥ (A *ᵥ WithLp.ofLp g))/r ≤ 1)
    (hx : x ∈ euclideanShapeEllipsoid c A) (hcut : 0 ≤ ⟪g,x-c⟫_ℝ) :
    x ∈ euclideanShapeEllipsoid (euclideanApproxCutCenter c A g r)
      ((1+η/(n : ℝ))^2 • euclideanEllipsoidCutShape A g) := by
  obtain ⟨S,hS,heq⟩ := euclidean_posDef_factor A hA
  subst A
  let u := euclideanPullbackUnit S g
  let v := euclideanMatrixApply S⁻¹ (x-c)
  let a := Real.sqrt (WithLp.ofLp g ⬝ᵥ ((S*Sᵀ) *ᵥ WithLp.ofLp g))
  let θ := a/r
  have ha : a = ‖euclideanMatrixApply Sᵀ g‖ := by
    dsimp [a]
    rw [← euclideanMatrixApply_transpose_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  have ha0 : 0 < a := by
    rw [ha]
    exact norm_pos_iff.mpr (euclideanMatrixApply_ne_zero Sᵀ (by simpa using! hS) hg)
  have hv : c+euclideanMatrixApply S v = x := by
    dsimp [v]
    rw [← euclideanMatrixApply_mul,Matrix.mul_nonsing_inv S hS,euclideanMatrixApply_one]
    abel
  have hnv : ‖v‖ ≤ 1 := (euclideanShapeEllipsoid_unit_affine_iff c S hS v).mp (hv ▸ hx)
  have hc : 0 ≤ ⟪u,v⟫_ℝ := by
    rw [show u = euclideanPullbackUnit S g from rfl,euclideanPullbackUnit,inner_smul_left,euclideanMatrixApply_transpose_inner]
    have hmv : euclideanMatrixApply S v = x-c := by rw [← hv]; abel
    rw [hmv]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hcut
  have hin :=
      euclideanApproxCentralCut_contains hn u v
      (euclideanPullbackUnit_norm S hS hg) hnv hc hη hθlo hθhi
  let z := (θ/((n : ℝ)+1)) • u
  have hcenter : c+euclideanMatrixApply S z = euclideanApproxCutCenter c (S*Sᵀ) g r := by
    dsimp only [z,u,θ]
    rw [euclideanPullbackUnit,euclideanMatrixApply_smul,euclideanMatrixApply_smul,
      ← euclideanMatrixApply_mul,smul_smul,← ha]
    unfold euclideanApproxCutCenter
    congr 2
    field_simp
  have hshape : S*((1+η/(n : ℝ))^2 • euclideanCentralCutShape u)*Sᵀ =
      (1+η/(n : ℝ))^2 • euclideanEllipsoidCutShape (S*Sᵀ) g := by
    rw [Matrix.mul_smul,Matrix.smul_mul]
    exact congrArg (fun B => (1+η/(n : ℝ))^2 • B) (euclideanAffineCutShape_formula S g)
  have hh := (euclideanShapeEllipsoid_affine_iff (c+euclideanMatrixApply S z) S
    ((1+η/(n : ℝ))^2 • euclideanCentralCutShape u) hS (v-z)).mpr hin
  have hpoint : c+euclideanMatrixApply S z+euclideanMatrixApply S (v-z) = x := by
    rw [euclideanMatrixApply_sub,← hv]
    abel
  rw [hpoint,hcenter,hshape] at hh
  exact hh

/-- Coercing a rational ellipsoid quadratic form to the reals equals evaluating the real
embedded shape and vector. -/
theorem rationalEllipsoid_quadratic_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : Fin n → ℚ) :
    ((g ⬝ᵥ (A *ᵥ g) : ℚ) : ℝ) =
      (fun k => (g k : ℝ)) ⬝ᵥ (rationalEllipsoidShapeReal A *ᵥ (fun k => (g k : ℝ))) := by
  simp [rationalEllipsoidShapeReal,Matrix.mulVec,dotProduct]

/-- The embedded rational ellipsoid cut center equals the approximate real cut center using the
selected rational square root upper bound. -/
theorem rationalEllipsoidCutCenter_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c g : Fin n → ℚ) (η : ℚ) :
    (WithLp.toLp 2 (fun k => (rationalEllipsoidCutCenter A c g η k : ℝ)) : EuclideanSpace ℝ (Fin n)) =
      euclideanApproxCutCenter (WithLp.toLp 2 (fun k => (c k : ℝ))) (rationalEllipsoidShapeReal A)
        (WithLp.toLp 2 (fun k => (g k : ℝ))) (rationalSqrtUpper (g ⬝ᵥ (A *ᵥ g)) (rationalSqrtPrecision (g ⬝ᵥ (A *ᵥ g)) η) : ℝ) := by
  ext k
  simp [rationalEllipsoidCutCenter,euclideanApproxCutCenter,euclideanMatrixApply,rationalEllipsoidShapeReal,Matrix.mulVec,dotProduct]

/-- Embedding the inflated rational cut shape gives the real cut shape scaled by `(1 + η /
n)^2`. -/
theorem rationalEllipsoidInflatedShape_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : Fin n → ℚ) (η : ℚ) :
    rationalEllipsoidShapeReal (rationalEllipsoidInflatedShape A g η) =
      (1+(η : ℝ)/(n : ℝ))^2 • euclideanEllipsoidCutShape (rationalEllipsoidShapeReal A)
        (WithLp.toLp 2 (fun k => (g k : ℝ))) := by
  rw [← rationalEllipsoidCutShape_real]
  ext i j
  simp [rationalEllipsoidShapeReal,rationalEllipsoidInflatedShape]

/-- A rational shape with positive definite real embedding has positive quadratic value on every
nonzero rational normal. -/
theorem rationalEllipsoid_quadratic_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (rationalEllipsoidShapeReal A).PosDef) (g : Fin n → ℚ) (hg : ∃ k, g k ≠ 0) :
    0 < g ⬝ᵥ (A *ᵥ g) := by
  have hg' : (fun k => (g k : ℝ)) ≠ 0 := by
    intro hz
    obtain ⟨k,hk⟩ := hg
    have hh := congrFun hz k
    exact hk (Rat.cast_eq_zero.mp hh)
  have hs := hA.dotProduct_mulVec_pos hg'
  simp only [star_trivial] at hs
  rw [← rationalEllipsoid_quadratic_real] at hs
  exact_mod_cast hs

/-- In dimension at least two, a rational approximate cut with nonzero normal and positive
tolerance preserves positive definiteness and retains the original half-ellipsoid. Its
positive determinant is bounded by `(1 + η / n)^(2 * n) * n / (n + 1)` times the original
determinant. -/
theorem rationalEllipsoidApproxCut_correct {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (rationalEllipsoidShapeReal A).PosDef)
    (c g : Fin n → ℚ) (hg : ∃ k, g k ≠ 0) {η : ℚ} (hη : 0 < η) :
    let A' := rationalEllipsoidShapeReal (rationalEllipsoidInflatedShape A g η)
    let c' :=
        (WithLp.toLp 2 (fun k => (rationalEllipsoidCutCenter A c g η k : ℝ)) : EuclideanSpace ℝ (Fin n))
    A'.PosDef ∧ 0 < A'.det ∧
      A'.det ≤ (1+(η : ℝ)/(n : ℝ))^(2*n) * ((n : ℝ)/((n : ℝ)+1)) * (rationalEllipsoidShapeReal A).det ∧
      ∀ x ∈ euclideanShapeEllipsoid (WithLp.toLp 2 (fun k => (c k : ℝ))) (rationalEllipsoidShapeReal A),
        0 ≤ ⟪(WithLp.toLp 2 (fun k => (g k : ℝ)) : EuclideanSpace ℝ (Fin n)),
          x-WithLp.toLp 2 (fun k => (c k : ℝ))⟫_ℝ → x ∈ euclideanShapeEllipsoid c' A' := by
  (try dsimp only)
  rw [rationalEllipsoidInflatedShape_real,rationalEllipsoidCutCenter_real]
  have hg' : (WithLp.toLp 2 (fun k => (g k : ℝ)) : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro hz
    obtain ⟨k,hk⟩ := hg
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v k) hz
    exact hk (Rat.cast_eq_zero.mp hh)
  have hs := rationalEllipsoid_quadratic_pos A hA g hg
  obtain ⟨hr,hl,hu,hθlo,hθhi⟩ := rationalSqrtUpper_relative hs hη
  rw [rationalEllipsoid_quadratic_real] at hθlo hθhi
  have hηr : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hf : 0 < (1+(η : ℝ)/(n : ℝ))^2 := sq_pos_of_pos (by positivity)
  obtain ⟨hpd,hdet,hbound,hkeep⟩ :=
      euclideanEllipsoidCut_correct hn _ hA (WithLp.toLp 2 (fun k => (c k : ℝ))) hg'
  have hpd' := hpd.smul hf
  refine ⟨hpd',hpd'.det_pos,?_,?_⟩
  · rw [Matrix.det_smul,Fintype.card_fin,← pow_mul]
    have hh :=
        mul_le_mul_of_nonneg_left hbound (pow_nonneg (by positivity : 0 ≤ 1+(η : ℝ)/(n : ℝ)) (2*n))
    exact hh.trans_eq (by ring)
  · intro x hx hc
    exact euclideanApproxCut_retains hn _ hA _ x hg' hr hηr hθlo hθhi hx hc

/-- For nonnegative `z` with `m * z < 1`, the power `(1 + z)^m` is at most `1 / (1 - m * z)`. -/
theorem one_add_pow_le_inv_sub_mul {z : ℝ} (hz : 0 ≤ z) (m : ℕ) (hm : (m : ℝ)*z < 1) :
    (1+z)^m ≤ 1/(1-(m : ℝ)*z) := by
  have hp : 0 < 1+z := by linarith
  have hf : z/(1+z) ≤ 1 := (div_le_one hp).mpr (by linarith)
  have hs : z/(1+z) ≤ z := (div_le_iff₀ hp).mpr (by nlinarith [sq_nonneg z])
  have hb := one_add_mul_le_pow (a := -(z/(1+z))) (by linarith) m
  have heq : 1 + -(z/(1+z)) = (1+z)⁻¹ := by field_simp; ring
  rw [heq] at hb
  have hlo : 1-(m : ℝ)*z ≤ ((1+z)⁻¹)^m := by
    have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) m)
    linarith
  have hprod : (1+z)^m * ((1+z)⁻¹)^m = 1 := by
    rw [← mul_pow,mul_inv_cancel₀ hp.ne',one_pow]
  have hh := mul_le_mul_of_nonneg_left hlo (pow_nonneg hp.le m)
  rw [hprod] at hh
  exact (le_div_iff₀ (by linarith : 0 < 1-(m : ℝ)*z)).mpr hh

/-- In dimension at least two, the center-rounding inflation and central-cut contraction
together are bounded by `1 - 1 / (2 * (n + 1))`. -/
theorem ellipsoid_center_inflation_factor {n : ℕ} (hn : 2 ≤ n) :
    (1+1/(16*(n : ℝ)^2))^(2*n) * ((n : ℝ)/((n : ℝ)+1)) ≤ 1-1/(2*((n : ℝ)+1)) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnp : (0 : ℝ) < (n : ℝ)+1 := by linarith
  have h8 : (0 : ℝ) < 8*(n : ℝ)-1 := by linarith
  have heq : ((2*n : ℕ) : ℝ)*(1/(16*(n : ℝ)^2)) = 1/(8*(n : ℝ)) := by
    push_cast
    field_simp
    norm_num
  have hm : ((2*n : ℕ) : ℝ)*(1/(16*(n : ℝ)^2)) < 1 := by
    rw [heq]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hh := one_add_pow_le_inv_sub_mul (z := 1/(16*(n : ℝ)^2)) (by positivity) (2*n) hm
  rw [heq] at hh
  have hs := mul_le_mul_of_nonneg_right hh (div_pos hn0 hnp).le
  apply hs.trans
  have hleft : 1/(1-1/(8*(n : ℝ))) * ((n : ℝ)/((n : ℝ)+1)) =
      8*(n : ℝ)^2/((8*(n : ℝ)-1)*((n : ℝ)+1)) := by
    field_simp
  have hright : 1-1/(2*((n : ℝ)+1)) = (2*(n : ℝ)+1)/(2*((n : ℝ)+1)) := by
    field_simp
    ring
  rw [hleft,hright]
  apply (div_le_div_iff₀ (mul_pos h8 hnp) (mul_pos (by norm_num) hnp)).mpr
  nlinarith

/-- The rational ellipsoid step tolerance is positive in dimension at least two. -/
theorem rationalEllipsoidStepTolerance_pos {n : ℕ} (hn : 2 ≤ n) : 0 < rationalEllipsoidStepTolerance n := by
  unfold rationalEllipsoidStepTolerance
  have hn0 : (0 : ℚ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  positivity

/-- In dimension at least two, the selected step tolerance makes a rational ellipsoid cut with
nonzero normal retain the original half-ellipsoid and preserve positive definiteness. Its
positive determinant is at most `1 - 1 / (2 * (n + 1))` times the original determinant. -/
theorem rationalEllipsoidStep_correct {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (rationalEllipsoidShapeReal A).PosDef)
    (c g : Fin n → ℚ) (hg : ∃ k, g k ≠ 0) :
    let η := rationalEllipsoidStepTolerance n
    let A' := rationalEllipsoidShapeReal (rationalEllipsoidInflatedShape A g η)
    let c' :=
        (WithLp.toLp 2 (fun k => (rationalEllipsoidCutCenter A c g η k : ℝ)) : EuclideanSpace ℝ (Fin n))
    A'.PosDef ∧ 0 < A'.det ∧
      A'.det ≤ (1-1/(2*((n : ℝ)+1))) * (rationalEllipsoidShapeReal A).det ∧
      ∀ x ∈ euclideanShapeEllipsoid (WithLp.toLp 2 (fun k => (c k : ℝ))) (rationalEllipsoidShapeReal A),
        0 ≤ ⟪(WithLp.toLp 2 (fun k => (g k : ℝ)) : EuclideanSpace ℝ (Fin n)),
          x-WithLp.toLp 2 (fun k => (c k : ℝ))⟫_ℝ → x ∈ euclideanShapeEllipsoid c' A' := by
  (try dsimp only)
  obtain ⟨hpd,hdet,hbound,hkeep⟩ :=
      rationalEllipsoidApproxCut_correct hn A hA c g hg (rationalEllipsoidStepTolerance_pos hn)
  refine ⟨hpd,hdet,?_,hkeep⟩
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht : (rationalEllipsoidStepTolerance n : ℝ)/(n : ℝ) = 1/(16*(n : ℝ)^2) := by
    unfold rationalEllipsoidStepTolerance
    push_cast
    field_simp
  rw [ht] at hbound
  have hh := mul_le_mul_of_nonneg_right (ellipsoid_center_inflation_factor hn) hA.det_pos.le
  exact hbound.trans (by simpa only [mul_assoc] using! hh)

/-- Rounding an ellipsoid update from the rational sublevel oracle preserves positive
definiteness and retains all sublevel points in the original ellipsoid. The determinant
stays positive and contracts by the factor `1 - 1 / (2 * (n + 1))`, where `n` is the
coordinate count. -/
theorem diamondRationalSublevelOracle_roundedEllipsoidCut {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (q : DiamondRationalCoordinates D E)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSublevelOracle J γ q = .cut C)
    (A : Matrix (Fin (diamondDyadicWordCount D E)) (Fin (diamondDyadicWordCount D E)) ℚ)
    (hA : (rationalEllipsoidShapeReal A).PosDef) :
    let η := rationalEllipsoidStepTolerance (diamondDyadicWordCount D E)
    let g := fun k => C.coefficients[k]
    let q' := rationalEllipsoidCutCenter A q g η
    let A' := rationalEllipsoidShapeReal (rationalEllipsoidInflatedShape A g η)
    A'.PosDef ∧ 0 < A'.det ∧
      A'.det ≤ (1-1/(2*((diamondDyadicWordCount D E : ℝ)+1))) * (rationalEllipsoidShapeReal A).det ∧
      ∀ x ∈ diamondRealSublevel T (γ : ℝ),
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ euclideanShapeEllipsoid
          (WithLp.toLp 2 (diamondRationalCoordinatesReal q)) (rationalEllipsoidShapeReal A) →
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ euclideanShapeEllipsoid
          (WithLp.toLp 2 (diamondRationalCoordinatesReal q')) A' := by
  (try dsimp only)
  obtain ⟨hrej,hkeep,hnz⟩ := diamondRationalSublevelOracle_cut T J hJ γ q C hc
  have hn : 2 ≤ diamondDyadicWordCount D E := by unfold diamondDyadicWordCount; omega
  obtain ⟨hpd,hdet,hbound,hstep⟩ :=
      rationalEllipsoidStep_correct hn A hA q (fun k => C.coefficients[k]) hnz
  refine ⟨hpd,hdet,hbound,?_⟩
  intro x hx hball
  apply hstep (WithLp.toLp 2 x) hball
  have hqr : C.evalReal (diamondRationalCoordinatesReal q) < (C.bound : ℝ) := by
    change C.evalReal (fun k => (q k : ℝ)) < (C.bound : ℝ)
    rw [(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.evalReal_rational (C := C))]
    exact_mod_cast hrej
  change 0 ≤ ⟪C.euclideanNormal,(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) -
    WithLp.toLp 2 (diamondRationalCoordinatesReal q)⟫_ℝ
  rw [inner_sub_right,(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_inner (C := C)),(Qatlib.Concepts.SdpDuality.StrongDuality.RationalAffineCut.euclideanNormal_inner (C := C))]
  linarith [hkeep x hx.1 hx.2]

end RationalEllipsoidCenter

section BoundedEllipsoidSearch

/-- The center of a rational ellipsoid state constructed from functions is the supplied center
function. -/
@[simp] theorem RationalEllipsoidState.center_ofFunctions {n : ℕ} (c : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (RationalEllipsoidState.ofFunctions c A).center = c := by
  funext i
  simp [RationalEllipsoidState.center,RationalEllipsoidState.ofFunctions]

/-- The shape of a rational ellipsoid state constructed from functions is the supplied shape
matrix. -/
@[simp] theorem RationalEllipsoidState.shape_ofFunctions {n : ℕ} (c : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (RationalEllipsoidState.ofFunctions c A).shape = A := by
  funext i j
  simp [RationalEllipsoidState.shape,RationalEllipsoidState.ofFunctions]

/-- The center after a rational ellipsoid state cut is the rational cut center computed with the
selected step tolerance. -/
@[simp] theorem RationalEllipsoidState.cut_center {n : ℕ} (s : RationalEllipsoidState n) (C : RationalAffineCut n) :
    (s.cut C).center = rationalEllipsoidCutCenter s.shape s.center (fun i => C.coefficients[i]) (rationalEllipsoidStepTolerance n) := by
  funext i
  simp [RationalEllipsoidState.cut,RationalEllipsoidState.center,RationalEllipsoidState.shape,rationalEllipsoidCutCenter,Matrix.mulVec,dotProduct]

/-- The shape after a rational ellipsoid state cut is the inflated rational cut shape computed
with the selected step tolerance. -/
@[simp] theorem RationalEllipsoidState.cut_shape {n : ℕ} (s : RationalEllipsoidState n) (C : RationalAffineCut n) :
    (s.cut C).shape = rationalEllipsoidInflatedShape s.shape (fun i => C.coefficients[i]) (rationalEllipsoidStepTolerance n) := by
  funext i j
  simp [RationalEllipsoidState.cut,RationalEllipsoidState.shape,rationalEllipsoidInflatedShape,rationalEllipsoidCutShape,
    Matrix.vecMulVec,Matrix.mulVec,dotProduct]
  ring

/-- A diamond ellipsoid run with budget `k` records at most `k` oracle calls. -/
theorem diamondEllipsoidRun_calls_le {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ : ℚ) (k : ℕ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) : (diamondEllipsoidRun J γ k s).trace.length ≤ k := by
  induction k generalizing s with
  | zero => simp [diamondEllipsoidRun]
  | succ k ih =>
    cases hc : diamondRationalSublevelOracle J γ s.center with
    | feasible => simp [diamondEllipsoidRun,hc]
    | invalid => simp [diamondEllipsoidRun,hc]
    | cut C => simpa only [diamondEllipsoidRun,hc,List.length_cons] using! Nat.succ_le_succ (ih (s.cut C))

/-- Every entry of a diamond ellipsoid run's trace records the sublevel oracle result at the
recorded state's center. -/
theorem diamondEllipsoidRun_trace_oracle {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ : ℚ) (k : ℕ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) :
    ∀ t ∈ (diamondEllipsoidRun J γ k s).trace, diamondRationalSublevelOracle J γ t.1.center = t.2 := by
  induction k generalizing s with
  | zero => simp [diamondEllipsoidRun]
  | succ k ih =>
    cases hc : diamondRationalSublevelOracle J γ s.center with
    | feasible => simp [diamondEllipsoidRun,hc]
    | invalid => simp [diamondEllipsoidRun,hc]
    | cut C =>
      intro t ht
      simp only [diamondEllipsoidRun,hc,List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hc
      · exact ih _ t ht

/-- For rational Choi data representing a linear map, a diamond ellipsoid run never has invalid
outcome. -/
theorem diamondEllipsoidRun_not_invalid {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (k : ℕ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) : (diamondEllipsoidRun J γ k s).outcome ≠ .invalid := by
  induction k generalizing s with
  | zero => simp [diamondEllipsoidRun]
  | succ k ih =>
    cases hc : diamondRationalSublevelOracle J γ s.center with
    | feasible => simp [diamondEllipsoidRun,hc]
    | invalid => exact False.elim ((diamondRationalSublevelOracle_not_invalid T J hJ γ s.center) hc)
    | cut C => simpa only [diamondEllipsoidRun,hc] using! ih (s.cut C)

/-- For rational Choi data representing `T`, a feasible diamond ellipsoid run returns a center
decoding to diamond dual feasible data with score at most `γ`. -/
theorem diamondEllipsoidRun_feasible {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (k : ℕ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) :
    (diamondEllipsoidRun J γ k s).outcome = .feasible →
      (diamondProgram T).DualFeasible (diamondRationalDecode (diamondEllipsoidRun J γ k s).state.center) ∧
        (diamondProgram T).dualScore (diamondRationalDecode (diamondEllipsoidRun J γ k s).state.center) ≤ (γ : ℝ) := by
  induction k generalizing s with
  | zero => simp [diamondEllipsoidRun]
  | succ k ih =>
    cases hc : diamondRationalSublevelOracle J γ s.center with
    | feasible =>
      intro _
      simpa only [diamondEllipsoidRun,hc] using!
          (diamondRationalSublevelOracle_feasible_iff T J hJ γ s.center).mp hc
    | invalid => simp [diamondEllipsoidRun,hc]
    | cut C => simpa only [diamondEllipsoidRun,hc] using! ih (s.cut C)

/-- A sublevel oracle cut of a state with positive definite shape preserves positive
definiteness and retains sublevel points in its region. The shape determinant contracts by
the factor `1 - 1 / (2 * (n + 1))`, where `n` is the coordinate count. -/
theorem diamondEllipsoidState_cut_correct {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) (hA : (rationalEllipsoidShapeReal s.shape).PosDef)
    (C : RationalAffineCut (diamondDyadicWordCount D E)) (hc : diamondRationalSublevelOracle J γ s.center = .cut C) :
    (rationalEllipsoidShapeReal (s.cut C).shape).PosDef ∧
      (rationalEllipsoidShapeReal (s.cut C).shape).det ≤
        (1-1/(2*((diamondDyadicWordCount D E : ℝ)+1))) * (rationalEllipsoidShapeReal s.shape).det ∧
      ∀ x ∈ diamondRealSublevel T (γ : ℝ),
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ s.region →
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ (s.cut C).region := by
  obtain ⟨hp,hd,hb,hkeep⟩ :=
      diamondRationalSublevelOracle_roundedEllipsoidCut T J hJ γ s.center C hc s.shape hA
  simpa only [RationalEllipsoidState.cut_center,RationalEllipsoidState.cut_shape,
    RationalEllipsoidState.region,diamondRationalCoordinatesReal] using! And.intro hp (And.intro hb hkeep)

/-- For rational Choi data and an initially positive definite shape, a diamond ellipsoid run
preserves positive definiteness and retains every sublevel point in the initial region. -/
theorem diamondEllipsoidRun_preserves {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (k : ℕ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) (hA : (rationalEllipsoidShapeReal s.shape).PosDef) :
    (rationalEllipsoidShapeReal (diamondEllipsoidRun J γ k s).state.shape).PosDef ∧
      ∀ x ∈ diamondRealSublevel T (γ : ℝ),
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ s.region →
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ (diamondEllipsoidRun J γ k s).state.region := by
  induction k generalizing s with
  | zero => exact ⟨hA,fun _ _ hx => hx⟩
  | succ k ih =>
    cases hc : diamondRationalSublevelOracle J γ s.center with
    | feasible => simpa only [diamondEllipsoidRun,hc] using! And.intro hA (fun _ _ hx => hx)
    | invalid => simpa only [diamondEllipsoidRun,hc] using! And.intro hA (fun _ _ hx => hx)
    | cut C =>
      obtain ⟨hnext,hd,hstep⟩ := diamondEllipsoidState_cut_correct T J hJ γ s hA C hc
      obtain ⟨hfinal,hkeep⟩ := ih (s.cut C) hnext
      simp only [diamondEllipsoidRun,hc]
      exact ⟨hfinal,fun x hx hs => hkeep x hx (hstep x hx hs)⟩

/-- The ellipsoid determinant contraction factor `1 - 1 / (2 * (n + 1))` lies strictly between
zero and one. -/
theorem ellipsoidContraction_bounds (n : ℕ) : 0 < (1-1/(2*((n : ℝ)+1))) ∧ (1-1/(2*((n : ℝ)+1))) < 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hd : (0 : ℝ) < 2*((n : ℝ)+1) := by positivity
  have hlt : (1 : ℝ)/(2*((n : ℝ)+1)) < 1 := (div_lt_one hd).mpr (by linarith)
  have hp : (0 : ℝ) < 1/(2*((n : ℝ)+1)) := one_div_pos.mpr hd
  constructor <;> linarith

/-- For rational Choi data and an initially positive definite shape, the final shape determinant
is bounded by the initial determinant times the contraction factor raised to the number of
recorded cuts. -/
theorem diamondEllipsoidRun_det_bound {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ) (k : ℕ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) (hA : (rationalEllipsoidShapeReal s.shape).PosDef) :
    (rationalEllipsoidShapeReal (diamondEllipsoidRun J γ k s).state.shape).det ≤
      (1-1/(2*((diamondDyadicWordCount D E : ℝ)+1)))^(rationalEllipsoidTraceCutCount (diamondEllipsoidRun J γ k s).trace) *
        (rationalEllipsoidShapeReal s.shape).det := by
  induction k generalizing s with
  | zero => simp [diamondEllipsoidRun,rationalEllipsoidTraceCutCount]
  | succ k ih =>
    cases hc : diamondRationalSublevelOracle J γ s.center with
    | feasible => simp [diamondEllipsoidRun,hc,rationalEllipsoidTraceCutCount]
    | invalid => simp [diamondEllipsoidRun,hc,rationalEllipsoidTraceCutCount]
    | cut C =>
      obtain ⟨hnext,hd,hstep⟩ := diamondEllipsoidState_cut_correct T J hJ γ s hA C hc
      have hh := ih (s.cut C) hnext
      have hm := mul_le_mul_of_nonneg_left hd
        (pow_nonneg (ellipsoidContraction_bounds (diamondDyadicWordCount D E)).1.le
          (rationalEllipsoidTraceCutCount (diamondEllipsoidRun J γ k (s.cut C)).trace))
      simp only [diamondEllipsoidRun,hc,rationalEllipsoidTraceCutCount,List.countP_cons,ite_true]
      apply hh.trans
      simpa only [rationalEllipsoidTraceCutCount,pow_succ,mul_assoc] using! hm

/-- An exhausted run with budget `k` has exactly `k` recorded cuts and exactly `k` trace
entries. -/
theorem diamondEllipsoidRun_exhausted_counts {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ : ℚ) (k : ℕ)
    (s : RationalEllipsoidState (diamondDyadicWordCount D E)) :
    (diamondEllipsoidRun J γ k s).outcome = .exhausted →
      rationalEllipsoidTraceCutCount (diamondEllipsoidRun J γ k s).trace = k ∧ (diamondEllipsoidRun J γ k s).trace.length = k := by
  induction k generalizing s with
  | zero => simp [diamondEllipsoidRun,rationalEllipsoidTraceCutCount]
  | succ k ih =>
    cases hc : diamondRationalSublevelOracle J γ s.center with
    | feasible => simp [diamondEllipsoidRun,hc]
    | invalid => simp [diamondEllipsoidRun,hc]
    | cut C =>
      intro he
      simp only [diamondEllipsoidRun,hc] at he ⊢
      have ht := ih (s.cut C) he
      simpa [diamondEllipsoidRun,hc,rationalEllipsoidTraceCutCount,List.countP_cons] using!
          And.intro (congrArg Nat.succ ht.1) (congrArg Nat.succ ht.2)

/-- The quadratic form of any real matrix satisfies the parallelogram identity. -/
theorem euclidean_quadratic_parallelogram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp (v+w) ⬝ᵥ (A *ᵥ WithLp.ofLp (v+w)) +
      WithLp.ofLp (v-w) ⬝ᵥ (A *ᵥ WithLp.ofLp (v-w)) =
      2*(WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v)) + 2*(WithLp.ofLp w ⬝ᵥ (A *ᵥ WithLp.ofLp w)) := by
  simp only [WithLp.ofLp_add,WithLp.ofLp_sub,Matrix.mulVec_add,Matrix.mulVec_sub,
    dotProduct_add,add_dotProduct,dotProduct_sub,sub_dotProduct]
  ring

/-- If a positive definite shape ellipsoid contains a closed ball of positive radius `r`, its
determinant is at least `r^(2 * n)`. -/
theorem euclideanShapeEllipsoid_ball_det_lower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (c d : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hball : ∀ x : EuclideanSpace ℝ (Fin n), ‖x-c‖ ≤ r → x ∈ euclideanShapeEllipsoid d A) :
    r^(2*n) ≤ A.det := by
  have hAi := hA.inv
  have hl (i : Fin n) : hAi.isHermitian.eigenvalues i ≤ 1/r^2 := by
    let u := hAi.isHermitian.eigenvectorBasis i
    have hu : ‖u‖ = 1 := hAi.isHermitian.eigenvectorBasis.norm_eq_one i
    have hp :=
        hball (c+r • u)
        (by simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hu,mul_one] using! (le_rfl : r ≤ r))
    have hm := hball (c-r • u) (by
      simpa only [show c-r • u-c = -(r • u) by abel,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hu,mul_one] using! (le_rfl : r ≤ r))
    change WithLp.ofLp (c+r • u-d) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp (c+r • u-d)) ≤ 1 at hp
    change WithLp.ofLp (c-r • u-d) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp (c-r • u-d)) ≤ 1 at hm
    rw [show c+r • u-d = (c-d)+r • u by abel] at hp
    rw [show c-r • u-d = (c-d)-r • u by abel] at hm
    have hpar := euclidean_quadratic_parallelogram A⁻¹ (c-d) (r • u)
    have hv := hAi.posSemidef.dotProduct_mulVec_nonneg (WithLp.ofLp (c-d))
    simp only [star_trivial] at hv
    have heig : A⁻¹ *ᵥ WithLp.ofLp u = (hAi.isHermitian.eigenvalues i) • WithLp.ofLp u :=
      hAi.isHermitian.mulVec_eigenvectorBasis i
    have hw : WithLp.ofLp (r • u) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp (r • u)) = r^2*hAi.isHermitian.eigenvalues i := by
      rw [WithLp.ofLp_smul,Matrix.mulVec_smul,heig,dotProduct_smul,dotProduct_smul,smul_dotProduct,
        euclidean_dot_inner,WithLp.toLp_ofLp,real_inner_self_eq_norm_sq,hu]
      simp only [smul_eq_mul,one_pow]
      ring
    rw [hw] at hpar
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith
  have hdet : A⁻¹.det ≤ (1/r^2)^n := by
    calc
      A⁻¹.det = ∏ i, hAi.isHermitian.eigenvalues i := hAi.isHermitian.det_eq_prod_eigenvalues
      _ ≤ ∏ _i : Fin n, (1/r^2 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => (hAi.eigenvalues_pos i).le) (fun i _ => hl i)
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_right hdet hA.det_pos.le
  rw [Matrix.det_nonsing_inv_mul_det A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')] at hh
  have hc : (r^2)^n*(1/r^2)^n = 1 := by
    rw [← mul_pow,one_div,mul_inv_cancel₀ (sq_pos_of_pos hr).ne',one_pow]
  have hf := mul_le_mul_of_nonneg_left hh (pow_nonneg (sq_nonneg r) n)
  rw [mul_one,← mul_assoc,hc,one_mul] at hf
  simpa only [← pow_mul] using! hf

/-- For every integer `m ≥ 2`, `(1 - 1 / m)^m` is at most one half. -/
theorem one_sub_one_div_pow_le_half {m : ℕ} (hm : 2 ≤ m) :
    (1-1/(m : ℝ))^m ≤ (1/2 : ℝ) := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ)-1 := by linarith
  have hρ : 0 ≤ 1-1/(m : ℝ) := by
    have hh : (1 : ℝ)/(m : ℝ) ≤ 1 := (div_le_one hm0).mpr (by linarith)
    linarith
  have hb := one_add_mul_le_pow (a := 1/((m : ℝ)-1)) (by have hh := one_div_pos.mpr hm1; linarith) m
  have hratio : (1 : ℝ) ≤ (m : ℝ)*(1/((m : ℝ)-1)) := by
    rw [mul_one_div]
    exact (le_div_iff₀ hm1).mpr (by linarith)
  have hlo : (2 : ℝ) ≤ (1+1/((m : ℝ)-1))^m := le_trans (by linarith) hb
  have hcoef : (1-1/(m : ℝ))*(1+1/((m : ℝ)-1)) = 1 := by
    field_simp
    ring
  have hprod : (1-1/(m : ℝ))^m*(1+1/((m : ℝ)-1))^m = 1 := by
    rw [← mul_pow,hcoef,one_pow]
  have hh := mul_le_mul_of_nonneg_left hlo (pow_nonneg hρ m)
  rw [hprod] at hh
  linarith

/-- For positive radii, the rational ellipsoid search budget makes the contracted outer
determinant bound strictly smaller than the inner ball determinant bound. -/
theorem rationalEllipsoidSearchBudget_det_small (n : ℕ) {R r : ℚ} (hR : 0 < R) (hr : 0 < r) :
    (1-1/(2*((n : ℝ)+1)))^(rationalEllipsoidSearchBudget n R r)*(R : ℝ)^(2*n) < (r : ℝ)^(2*n) := by
  let p := dyadicPrecision ⌈R/r⌉₊
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hp : (R : ℝ)/(2 : ℝ)^p ≤ (r : ℝ) := by
    dsimp [p]
    apply dyadicPrecision_sufficient hrr
    exact_mod_cast Nat.le_ceil (R/r)
  have hhalf : (1-1/(2*((n : ℝ)+1)))^(2*(n+1)) ≤ (1/2 : ℝ) := by
    have hh := one_sub_one_div_pow_le_half (m := 2*(n+1)) (by omega)
    norm_cast at hh ⊢
  have hρ : (0 : ℝ) ≤ 1-1/(2*((n : ℝ)+1)) := (by
    have hh : (1 : ℝ)/(2*((n : ℝ)+1)) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
    linarith)
  have hh := pow_le_pow_left₀ (pow_nonneg hρ (2*(n+1))) hhalf (2*n*p+1)
  have hupper : (1-1/(2*((n : ℝ)+1)))^(rationalEllipsoidSearchBudget n R r)*(R : ℝ)^(2*n) ≤
      (1/2 : ℝ)^(2*n*p+1)*(R : ℝ)^(2*n) := by
    change _^(2*(n+1)*(2*n*p+1))*_ ≤ _
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_right hh (pow_nonneg hRr.le _)
  have heq : (1/2 : ℝ)^(2*n*p+1)*(R : ℝ)^(2*n) = (1/2 : ℝ)*((R : ℝ)/(2 : ℝ)^p)^(2*n) := by
    rw [pow_succ,show 2*n*p = p*(2*n) by ring,pow_mul]
    simp only [div_pow,one_pow]
    ring
  rw [heq] at hupper
  have hb :=
      pow_le_pow_left₀ (div_nonneg hRr.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)) hp (2*n)
  have hs := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1/2)
  exact (hupper.trans hs).trans_lt (by nlinarith [pow_pos hrr (2*n)])

/-- Embedding a rational scalar multiple of the identity shape gives the corresponding real
scalar multiple of the identity. -/
theorem rationalEllipsoidShapeReal_smul_one {n : ℕ} (r : ℚ) :
    rationalEllipsoidShapeReal (r • (1 : Matrix (Fin n) (Fin n) ℚ)) = (r : ℝ) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [rationalEllipsoidShapeReal,h]

/-- For positive initial radius, the diamond ellipsoid initial shape is positive definite. -/
theorem diamondEllipsoidInitialState_posDef (D E : ℕ) {R : ℚ} (hR : 0 < R) :
    (rationalEllipsoidShapeReal (diamondEllipsoidInitialState D E R).shape).PosDef := by
  rw [diamondEllipsoidInitialState,RationalEllipsoidState.shape_ofFunctions,rationalEllipsoidShapeReal_smul_one,Rat.cast_pow]
  exact Matrix.PosDef.one.smul (sq_pos_of_pos (by exact_mod_cast hR))

/-- For positive initial radius, membership in the initial diamond ellipsoid region is
equivalent to the coordinate norm being at most that radius. -/
theorem diamondEllipsoidInitialState_region {D E : ℕ} {R : ℚ} (hR : 0 < R) (x : DiamondRealCoordinates D E) :
    (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ (diamondEllipsoidInitialState D E R).region ↔
      diamondCoordinateNorm x ≤ (R : ℝ) := by
  simp only [RationalEllipsoidState.region,diamondEllipsoidInitialState,RationalEllipsoidState.center_ofFunctions,
    RationalEllipsoidState.shape_ofFunctions,Pi.zero_apply,Rat.cast_zero]
  change (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ euclideanShapeEllipsoid 0
    (rationalEllipsoidShapeReal (R^2 • (1 : Matrix (Fin (diamondDyadicWordCount D E)) (Fin (diamondDyadicWordCount D E)) ℚ))) ↔ _
  rw [rationalEllipsoidShapeReal_smul_one,Rat.cast_pow,
    euclideanShapeEllipsoid_scalar_ball _ _ (by exact_mod_cast hR),sub_zero]
  rfl

/-- The initial diamond ellipsoid shape determinant is the radius raised to twice the coordinate
count. -/
theorem diamondEllipsoidInitialState_det (D E : ℕ) (R : ℚ) :
    (rationalEllipsoidShapeReal (diamondEllipsoidInitialState D E R).shape).det = (R : ℝ)^(2*diamondDyadicWordCount D E) := by
  rw [diamondEllipsoidInitialState,RationalEllipsoidState.shape_ofFunctions,rationalEllipsoidShapeReal_smul_one,
    Rat.cast_pow,Matrix.det_smul,Fintype.card_fin,Matrix.det_one,mul_one,← pow_mul]

/-- If a positive-radius ball lies in both the dual sublevel set and the initial outer ball, the
diamond ellipsoid run finds a feasible point within the prescribed search budget. -/
theorem diamondEllipsoidRun_feasible_of_ball {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ : ℚ)
    {R r : ℚ} (hR : 0 < R) (hr : 0 < r) (c : DiamondRealCoordinates D E)
    (hball : diamondCoordinateBall c (r : ℝ) ⊆ diamondRealSublevel T (γ : ℝ) ∩ diamondCoordinateBall 0 (R : ℝ)) :
    (diamondEllipsoidRun J γ (rationalEllipsoidSearchBudget (diamondDyadicWordCount D E) R r)
      (diamondEllipsoidInitialState D E R)).outcome = .feasible := by
  let k := rationalEllipsoidSearchBudget (diamondDyadicWordCount D E) R r
  let s := diamondEllipsoidInitialState D E R
  have hA := diamondEllipsoidInitialState_posDef D E hR
  have hgood := diamondEllipsoidRun_not_invalid T J hJ γ k s
  cases ho : (diamondEllipsoidRun J γ k s).outcome with
  | feasible => rfl
  | invalid => exact False.elim (hgood ho)
  | exhausted =>
    obtain ⟨hc,hcalls⟩ := diamondEllipsoidRun_exhausted_counts J γ k s ho
    obtain ⟨hpd,hkeep⟩ := diamondEllipsoidRun_preserves T J hJ γ k s hA
    have hdet := diamondEllipsoidRun_det_bound T J hJ γ k s hA
    rw [hc,diamondEllipsoidInitialState_det] at hdet
    have hlower : (r : ℝ)^(2*diamondDyadicWordCount D E) ≤ (rationalEllipsoidShapeReal (diamondEllipsoidRun J γ k s).state.shape).det := by
      apply euclideanShapeEllipsoid_ball_det_lower _ hpd (WithLp.toLp 2 c)
        (WithLp.toLp 2 (fun j => ((diamondEllipsoidRun J γ k s).state.center j : ℝ))) (by exact_mod_cast hr)
      intro z hz
      let x : DiamondRealCoordinates D E := WithLp.ofLp z
      have hx : x ∈ diamondCoordinateBall c (r : ℝ) := by
        rw [diamondCoordinateBall_mem_iff]
        simpa only [x,WithLp.toLp_ofLp,Metric.mem_closedBall,dist_eq_norm] using! hz
      obtain ⟨hsub,houter⟩ := hball hx
      have hi : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E))) ∈ s.region := by
        apply (diamondEllipsoidInitialState_region hR x).mpr
        simpa only [diamondCoordinateBall,Set.mem_setOf_eq,sub_zero] using! houter
      have hh := hkeep x hsub hi
      simpa only [x,WithLp.toLp_ofLp,RationalEllipsoidState.region] using! hh
    have hsmall := rationalEllipsoidSearchBudget_det_small (diamondDyadicWordCount D E) hR hr
    exact False.elim (not_lt_of_ge hlower (hdet.trans_lt hsmall))

/-- For positive input dimension and rational tolerance, the diamond ellipsoid solver succeeds
at every threshold at least the diamond optimum plus that tolerance. -/
theorem diamondEllipsoidSolve_feasible_above_optimum {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 < ε) :
    ∃ α : ℝ, finiteDiamondNorm T = ENNReal.ofReal α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      ∀ γ : ℚ, α+(ε : ℝ) ≤ (γ : ℝ) → (diamondEllipsoidSolve J γ ε).outcome = .feasible := by
  obtain ⟨α,c,hnorm,hpr,hdu,hr,hR,hball⟩ := diamondProgram_coordinate_sublevel_ball hD T J hJ hε
  refine ⟨α,hnorm,hpr,hdu,?_⟩
  intro γ hγ
  exact diamondEllipsoidRun_feasible_of_ball T J hJ γ hR hr c (hball (γ : ℝ) hγ)

/-- For rational Choi data representing `T`, a feasible diamond ellipsoid solver result gives
decoded dual feasible data with score at most the requested threshold. -/
theorem diamondEllipsoidSolve_feasible {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ ε : ℚ)
    (h : (diamondEllipsoidSolve J γ ε).outcome = .feasible) :
    (diamondProgram T).DualFeasible (diamondRationalDecode (diamondEllipsoidSolve J γ ε).state.center) ∧
      (diamondProgram T).dualScore (diamondRationalDecode (diamondEllipsoidSolve J γ ε).state.center) ≤ (γ : ℝ) :=
  diamondEllipsoidRun_feasible T J hJ γ _ _ h

/-- The diamond ellipsoid solver's trace length is at most the rational search budget determined
by its coordinate count and outer and inner radii. -/
theorem diamondEllipsoidSolve_calls_le {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ ε : ℚ) :
    (diamondEllipsoidSolve J γ ε).trace.length ≤
      rationalEllipsoidSearchBudget (diamondDyadicWordCount D E) (diamondCoordinateOuterRadius J ε) (diamondCoordinateInnerRadius J ε) :=
  diamondEllipsoidRun_calls_le J γ _ _

/-- For rational Choi data representing a linear map, the diamond ellipsoid solver never returns
an invalid outcome. -/
theorem diamondEllipsoidSolve_not_invalid {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) (γ ε : ℚ) :
    (diamondEllipsoidSolve J γ ε).outcome ≠ .invalid :=
  diamondEllipsoidRun_not_invalid T J hJ γ _ _

/-- For positive input dimension and rational tolerance, each solver run either returns dual
feasible data below the requested threshold or exhausts its budget with that threshold
strictly below the diamond optimum plus the tolerance. -/
theorem diamondEllipsoidSolve_outcome {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {ε : ℚ} (hε : 0 < ε) :
    ∃ α : ℝ, finiteDiamondNorm T = ENNReal.ofReal α ∧
      IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
      ∀ γ : ℚ,
        ((diamondEllipsoidSolve J γ ε).outcome = .feasible ∧
          (diamondProgram T).DualFeasible (diamondRationalDecode (diamondEllipsoidSolve J γ ε).state.center) ∧
          (diamondProgram T).dualScore (diamondRationalDecode (diamondEllipsoidSolve J γ ε).state.center) ≤ (γ : ℝ)) ∨
        ((diamondEllipsoidSolve J γ ε).outcome = .exhausted ∧ (γ : ℝ) < α+(ε : ℝ)) := by
  obtain ⟨α,hnorm,hpr,hdu,hcomplete⟩ := diamondEllipsoidSolve_feasible_above_optimum hD T J hJ hε
  refine ⟨α,hnorm,hpr,hdu,?_⟩
  intro γ
  cases ho : (diamondEllipsoidSolve J γ ε).outcome with
  | feasible => exact Or.inl ⟨rfl,diamondEllipsoidSolve_feasible T J hJ γ ε ho⟩
  | invalid => exact False.elim ((diamondEllipsoidSolve_not_invalid T J hJ γ ε) ho)
  | exhausted =>
    refine Or.inr ⟨rfl,?_⟩
    apply lt_of_not_ge
    intro hge
    have hh := hcomplete γ hge
    rw [ho] at hh
    cases hh

end BoundedEllipsoidSearch

end Qatlib.Concepts.SdpDuality.StrongDuality
