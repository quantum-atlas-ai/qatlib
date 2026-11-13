/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbFormsAux
import Qatlib.Concepts.QueryComplexity.NormObstruction.Lemma33FactorizationToAlgorithmStat

/-!
# From completely bounded factorizations to query algorithms

Constructs a sign algorithm from a completely bounded factorization of a real tensor of order `2
* t`. The proof builds unitary dilations of contractions, stores defect components in separate
position slots, and interferes two branches to recover the factorization sandwich as a sign
bias.

`lemma3_3FactorizationToAlgorithm` packages the resulting `t`-query construction. Completely
bounded maps provide the operator-theoretic background [Paulsen2002], and finite-dimensional
unitary dilation is also used in [AradLandau2010].

## Main statements

* `contraction_unitary_dilation`: a contraction extends to a unitary on a doubled register with
  the prescribed first output component.
* `lemma3_3FactorizationToAlgorithm`: a completely bounded factorization gives a sign algorithm
  for the tensor bias.

## References

* [Paulsen, 2002][Paulsen2002]
* [Arad and Landau, 2010][AradLandau2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QueryComplexity.CbDegreeBridge

namespace Qatlib.Concepts.QueryComplexity.NormObstruction

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator

section InnerHelpers

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The state inner product distributes over addition in its first argument. -/
private theorem inner_add_left (x y z : QState I) : Qatlib.Foundations.PureStateMath.Inner (x + y) z = Qatlib.Foundations.PureStateMath.Inner x z + Qatlib.Foundations.PureStateMath.Inner y z := by
  rw [inner_apply, inner_apply, inner_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add, add_mul]

/-- The state inner product distributes over addition in its second argument. -/
private theorem inner_add_right (x y z : QState I) : Qatlib.Foundations.PureStateMath.Inner x (y + z) = Qatlib.Foundations.PureStateMath.Inner x y + Qatlib.Foundations.PureStateMath.Inner x z := by
  rw [inner_apply, inner_apply, inner_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]

/-- The state inner product distributes over subtraction in its second argument. -/
private theorem inner_sub_right (x y z : QState I) : Qatlib.Foundations.PureStateMath.Inner x (y - z) = Qatlib.Foundations.PureStateMath.Inner x y - Qatlib.Foundations.PureStateMath.Inner x z := by
  rw [inner_apply, inner_apply, inner_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, mul_sub]

/-- Scaling the first argument of the state inner product multiplies the result by the conjugate
scalar. -/
private theorem inner_smul_left (c : ℂ) (x y : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (c • x) y = (starRingEnd ℂ) c * Qatlib.Foundations.PureStateMath.Inner x y := by
  rw [inner_apply, inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul, map_mul]
    ring

/-- Moves a conjugate-transpose matrix from the second argument of the state inner product to
the first. -/
private theorem inner_conjTranspose_mulVec (A : Matrix I J ℂ) (x : QState J) (y : QState I) :
    Qatlib.Foundations.PureStateMath.Inner x (Aᴴ *ᵥ y) = Qatlib.Foundations.PureStateMath.Inner (A *ᵥ x) y := by
  rw [inner_apply, inner_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- Moves a matrix from the first argument of the state inner product to its conjugate transpose
in the second. -/
private theorem inner_mulVec_left (A : Matrix I I ℂ) (x y : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (A *ᵥ x) y = Qatlib.Foundations.PureStateMath.Inner x (Aᴴ *ᵥ y) :=
  (inner_conjTranspose_mulVec (I := I) (J := I) A x y).symm

/-- States with disjoint supports have zero inner product. -/
private theorem inner_eq_zero_of_support_disjoint (z w : QState I)
    (h : ∀ i, z i ≠ 0 → w i = 0) : Qatlib.Foundations.PureStateMath.Inner z w = 0 := by
  rw [inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hz : z i = 0
  · rw [hz, map_zero, zero_mul]
  · rw [h i hz, mul_zero]

end InnerHelpers

section Dilation

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The defect matrix `1 - Mᴴ * M` is Hermitian. -/
private theorem dil_hermitian (M : Matrix R R ℂ) : (1 - Mᴴ * M).IsHermitian :=
  Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self M)

set_option maxHeartbeats 1000000 in

/-- Every eigenvalue of the defect matrix is nonnegative when `M` is a contraction. -/
private theorem dil_eigen_nonneg (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) (i : R) :
    0 ≤ (dil_hermitian M).eigenvalues i := by
  set hG := dil_hermitian M
  set e : EuclideanSpace ℂ R := hG.eigenvectorBasis i
  have he : (1 - Mᴴ * M : Matrix R R ℂ) *ᵥ (⇑e : QState R) = ((hG.eigenvalues i : ℂ)) • ⇑e := by
    simpa only [RCLike.real_smul_eq_coe_smul] using! hG.mulVec_eigenvectorBasis i
  have hnorm : ‖e‖ = 1 := hG.eigenvectorBasis.orthonormal.1 i
  have h3 : toEuclidean_fromVec (⇑e : QState R) = e := rfl
  have hself : Qatlib.Foundations.PureStateMath.Inner (⇑e : QState R) ⇑e = 1 := by
    have h1 : inner ℂ e e = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      simp
    have h2 := inner_euclidean_fromVec (⇑e : QState R) (⇑e : QState R)
    rw [h3] at h2
    rw [← h2, h1]
  have hquad : Qatlib.Foundations.PureStateMath.Inner (⇑e : QState R) ((1 - Mᴴ * M) *ᵥ ⇑e)
      = 1 - Qatlib.Foundations.PureStateMath.Inner (M *ᵥ ⇑e) (M *ᵥ ⇑e) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, inner_sub_right, hself]
    congr 1
    rw [← Matrix.mulVec_mulVec, inner_conjTranspose_mulVec]
  have heig : (hG.eigenvalues i : ℂ) = Qatlib.Foundations.PureStateMath.Inner (⇑e : QState R) ((1 - Mᴴ * M) *ᵥ ⇑e) := by
    rw [he, Qatlib.Concepts.QueryComplexity.CbDegreeBridge.inner_smul_right, hself, mul_one]
  have hle : ‖toEuclidean_fromVec (M *ᵥ (⇑e : QState R))‖ ≤ 1 := by
    refine le_trans (l2_norm_mulVec_fromVec_le M ⇑e) ?_
    calc ‖M‖ * ‖toEuclidean_fromVec (⇑e : QState R)‖ = ‖M‖ := by rw [h3, hnorm, mul_one]
      _ ≤ 1 := hM
  have hre : (Qatlib.Foundations.PureStateMath.Inner (⇑e : QState R) ((1 - Mᴴ * M) *ᵥ ⇑e)).re
      = 1 - ‖toEuclidean_fromVec (M *ᵥ (⇑e : QState R))‖ ^ 2 := by
    rw [hquad, Complex.sub_re, Complex.one_re, norm_toEuclidean_sq_eq_re_inner]
  have hsq : ‖toEuclidean_fromVec (M *ᵥ (⇑e : QState R))‖ ^ 2 ≤ 1 := by
    have h1 := sq_le_sq_nn (norm_nonneg _) zero_le_one hle
    rwa [one_pow] at h1
  have hfin : (0 : ℝ) ≤ 1 - ‖toEuclidean_fromVec (M *ᵥ (⇑e : QState R))‖ ^ 2 := by linarith
  calc (0 : ℝ) ≤ (Qatlib.Foundations.PureStateMath.Inner (⇑e : QState R) ((1 - Mᴴ * M) *ᵥ ⇑e)).re := by rw [hre]; exact hfin
    _ = hG.eigenvalues i := by rw [← heig]; exact Complex.ofReal_re _

/-- Applies the real square root to the eigenvalues of a Hermitian matrix in a unitary
eigenbasis. -/
private noncomputable def hermSqrt {A : Matrix R R ℂ} (hA : A.IsHermitian) : Matrix R R ℂ :=
  (hA.eigenvectorUnitary : Matrix R R ℂ) *
    Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)) *
    star (hA.eigenvectorUnitary : Matrix R R ℂ)

set_option maxHeartbeats 1000000 in

/-- For nonnegative eigenvalues, the square of the spectral square-root matrix equals the
original matrix. -/
private theorem hermSqrt_mul_self {A : Matrix R R ℂ} (hA : A.IsHermitian)
    (hnn : ∀ i, 0 ≤ hA.eigenvalues i) : hermSqrt hA * hermSqrt hA = A := by
  have hUU : star (hA.eigenvectorUnitary : Matrix R R ℂ) * (hA.eigenvectorUnitary : Matrix R R ℂ)
      = 1 := (Unitary.mem_iff.mp (hA.eigenvectorUnitary).2).1
  have hDD : Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)) *
      Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ))
      = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnn i)]
  have hspec : A = (hA.eigenvectorUnitary : Matrix R R ℂ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix R R ℂ) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    congr 2
  calc hermSqrt hA * hermSqrt hA
      = (hA.eigenvectorUnitary : Matrix R R ℂ) *
          Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)) *
          (star (hA.eigenvectorUnitary : Matrix R R ℂ) * (hA.eigenvectorUnitary : Matrix R R ℂ)) *
          Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)) *
          star (hA.eigenvectorUnitary : Matrix R R ℂ) := by
        unfold hermSqrt
        noncomm_ring
    _ = (hA.eigenvectorUnitary : Matrix R R ℂ) *
          Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          star (hA.eigenvectorUnitary : Matrix R R ℂ) := by
        rw [hUU, mul_one,
          mul_assoc (hA.eigenvectorUnitary : Matrix R R ℂ)
            (Matrix.diagonal fun i => (Real.sqrt (hA.eigenvalues i) : ℂ))
            (Matrix.diagonal fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)),
          hDD]
    _ = A := hspec.symm

/-- The matrix constructed by taking real square roots in a Hermitian eigenbasis is Hermitian. -/
private theorem hermSqrt_hermitian {A : Matrix R R ℂ} (hA : A.IsHermitian) :
    (hermSqrt hA)ᴴ = hermSqrt hA := by
  have hD : (Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)))ᴴ
      = Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    show star ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) = _
    rw [RCLike.star_def]
    exact Complex.conj_ofReal _
  have h1 : (star (hA.eigenvectorUnitary : Matrix R R ℂ))ᴴ
      = (hA.eigenvectorUnitary : Matrix R R ℂ) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have h2 : (hA.eigenvectorUnitary : Matrix R R ℂ)ᴴ
      = star (hA.eigenvectorUnitary : Matrix R R ℂ) := (Matrix.star_eq_conjTranspose _).symm
  unfold hermSqrt
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD, h1, h2, mul_assoc]

/-- The spectral square-root construction for the defect matrix `1 - Mᴴ * M`. -/
private noncomputable def dilSqrt (M : Matrix R R ℂ) : Matrix R R ℂ :=
  hermSqrt (dil_hermitian M)

/-- For a contraction, the square of `dilSqrt M` equals `1 - Mᴴ * M`. -/
private theorem dilSqrt_mul_self (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    dilSqrt M * dilSqrt M = 1 - Mᴴ * M :=
  hermSqrt_mul_self (dil_hermitian M) (dil_eigen_nonneg M hM)

/-- The defect square-root construction is Hermitian. -/
private theorem dilSqrt_hermitian (M : Matrix R R ℂ) : (dilSqrt M)ᴴ = dilSqrt M :=
  hermSqrt_hermitian (dil_hermitian M)

/-- Stacks `M` above its defect square-root matrix on a doubled output register. -/
private noncomputable def dilStack (M : Matrix R R ℂ) : Matrix (R ⊕ R) R ℂ :=
  Sum.elim M (dilSqrt M)

/-- The first block of the stacked dilation matrix is `M`. -/
@[simp] theorem dilStack_inl (M : Matrix R R ℂ) (a y : R) : dilStack M (Sum.inl a) y = M a y := rfl

/-- The second block of the stacked dilation matrix is `dilSqrt M`. -/
@[simp] theorem dilStack_inr (M : Matrix R R ℂ) (a y : R) :
    dilStack M (Sum.inr a) y = dilSqrt M a y := rfl

/-- The stacked dilation sends a vector to the pair of its images under `M` and `dilSqrt M`. -/
private theorem dilStack_mulVec (M : Matrix R R ℂ) (y : QState R) :
    dilStack M *ᵥ y = Sum.elim (M *ᵥ y) (dilSqrt M *ᵥ y) := by
  funext w
  cases w <;> rfl

set_option maxHeartbeats 1000000 in

/-- For a contraction, the stacked dilation matrix has orthonormal columns. -/
private theorem dilStack_unit (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) : (dilStack M)ᴴ * dilStack M = 1 := by
  have hSS : (dilSqrt M)ᴴ * dilSqrt M = 1 - Mᴴ * M := by
    rw [dilSqrt_hermitian]
    exact dilSqrt_mul_self M hM
  have e1 : ∀ a b : R, (Mᴴ * M) a b = ∑ r, star (M r a) * M r b := fun a b => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => by rw [Matrix.conjTranspose_apply]
  have e2 : ∀ a b : R, ((dilSqrt M)ᴴ * dilSqrt M) a b
      = ∑ r, star (dilSqrt M r a) * dilSqrt M r b := fun a b => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => by rw [Matrix.conjTranspose_apply]
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.conjTranspose_apply, dilStack_inl, dilStack_inr]
  rw [← e1, ← e2, hSS, ← Matrix.add_apply, add_sub_cancel]

/-- The linear embedding into the first summand of the doubled Euclidean space, with zero second
component. -/
private noncomputable def embInlLM : EuclideanSpace ℂ R →ₗ[ℂ] EuclideanSpace ℂ (R ⊕ R) where
  toFun x := WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) 0)
  map_add' := fun x y => by
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_add]
    funext i
    cases i <;> simp
  map_smul' := fun c x => by
    apply WithLp.ofLp_injective
    simp only [RingHom.id_apply, WithLp.ofLp_smul]
    funext i
    cases i <;> simp

omit [Fintype R] [DecidableEq R] in

/-- Evaluates the linear embedding as the original vector followed by a zero component. -/
@[simp] theorem embInlLM_apply (x : EuclideanSpace ℂ R) :
    embInlLM x = WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) 0) := rfl

/-- The linear isometry embedding a Euclidean vector into the first summand of the doubled
space. -/
private noncomputable def embInlE : EuclideanSpace ℂ R →ₗᵢ[ℂ] EuclideanSpace ℂ (R ⊕ R) :=
  ⟨embInlLM, fun x => by
    rw [EuclideanSpace.norm_eq, embInlLM_apply, EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_sum_type]
    have hz : (∑ r : R, ‖Sum.elim (WithLp.ofLp x) (0 : QState R) (Sum.inr r)‖ ^ 2) = 0 := by
      simp
    rw [hz, add_zero]
    exact Finset.sum_congr rfl fun r _ => rfl⟩

/-- Evaluates the isometric embedding as the original vector followed by a zero component. -/
private theorem embInlE_apply (x : EuclideanSpace ℂ R) :
    embInlE (R := R) x = WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) 0) := rfl

/-- The linear map on Euclidean spaces represented by the stacked dilation matrix. -/
private noncomputable def dilIsoLM (M : Matrix R R ℂ) : EuclideanSpace ℂ R →ₗ[ℂ] EuclideanSpace ℂ (R ⊕ R) where
  toFun x := WithLp.toLp 2 (dilStack M *ᵥ (WithLp.ofLp x))
  map_add' := fun x y => by
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_add, Matrix.mulVec_add]
  map_smul' := fun c x => by
    apply WithLp.ofLp_injective
    simp only [RingHom.id_apply, WithLp.ofLp_smul, Matrix.mulVec_smul]

/-- Evaluates the dilation linear map by matrix-vector multiplication with `dilStack M`. -/
@[simp] theorem dilIsoLM_apply (M : Matrix R R ℂ) (x : EuclideanSpace ℂ R) :
    dilIsoLM M x = WithLp.toLp 2 (dilStack M *ᵥ (WithLp.ofLp x)) := rfl

/-- The linear isometry associated with the stacked dilation of a contraction. -/
private noncomputable def dilIso (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    EuclideanSpace ℂ R →ₗᵢ[ℂ] EuclideanSpace ℂ (R ⊕ R) :=
  ⟨dilIsoLM M, fun x => by
    have hV : (dilStack M)ᴴ * dilStack M = 1 := dilStack_unit M hM
    rw [EuclideanSpace.norm_eq, dilIsoLM_apply, EuclideanSpace.norm_eq]
    congr 1
    have key : Qatlib.Foundations.PureStateMath.Inner (dilStack M *ᵥ (WithLp.ofLp x)) (dilStack M *ᵥ (WithLp.ofLp x))
        = Qatlib.Foundations.PureStateMath.Inner (WithLp.ofLp x) (WithLp.ofLp x) := by
      rw [← inner_conjTranspose_mulVec, Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
    rw [inner_self, inner_self, ← Complex.ofReal_sum, ← Complex.ofReal_sum] at key
    exact Complex.ofReal_injective key⟩

/-- The dilation isometry acts by multiplication with the stacked dilation matrix. -/
private theorem dilIso_apply (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) (x : EuclideanSpace ℂ R) :
    dilIso M hM x = WithLp.toLp 2 (dilStack M *ᵥ (WithLp.ofLp x)) := rfl

/-- The subspace of the doubled Euclidean space consisting of vectors supported in the first
summand. -/
private noncomputable def dilDom : Submodule ℂ (EuclideanSpace ℂ (R ⊕ R)) :=
  LinearMap.range (embInlLM (R := R))

/-- The linear equivalence identifying the original Euclidean space with its first-summand
image. -/
private noncomputable def dilDomEquiv :
    EuclideanSpace ℂ R ≃ₗ[ℂ] ↥(dilDom (R := R)) :=
  LinearEquiv.ofInjective (embInlLM (R := R)) ((embInlE (R := R)).injective)

/-- The underlying vector of `dilDomEquiv x` is the first-summand isometric embedding of `x`. -/
private theorem dilDomEquiv_apply_val (x : EuclideanSpace ℂ R) :
    ((dilDomEquiv (R := R)) x : EuclideanSpace ℂ (R ⊕ R)) = embInlE (R := R) x :=
  LinearEquiv.ofInjective_apply (f := embInlLM (R := R))
    (h := (embInlE (R := R)).injective) x

/-- The inverse domain equivalence recovers a vector from its first-summand embedding. -/
private theorem dilDomEquiv_symm_emb (x : EuclideanSpace ℂ R) :
    (dilDomEquiv (R := R)).symm ⟨embInlE (R := R) x,
      LinearMap.mem_range_self (embInlLM (R := R)) x⟩ = x := by
  apply (dilDomEquiv (R := R)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext (dilDomEquiv_apply_val x).symm

/-- Transports the dilation linear map to the first-summand subspace using `dilDomEquiv`. -/
private noncomputable def dilIsoSubLM (M : Matrix R R ℂ) :
    ↥(dilDom (R := R)) →ₗ[ℂ] EuclideanSpace ℂ (R ⊕ R) :=
  (dilIsoLM M).comp (dilDomEquiv (R := R)).symm.toLinearMap

/-- The dilation of a contraction, viewed as a linear isometry defined on the first-summand
subspace. -/
private noncomputable def dilIsoSub (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    ↥(dilDom (R := R)) →ₗᵢ[ℂ] EuclideanSpace ℂ (R ⊕ R) :=
  ⟨dilIsoSubLM M, fun s => by
    show ‖dilIsoLM M ((dilDomEquiv (R := R)).symm s)‖ = ‖(s : EuclideanSpace ℂ (R ⊕ R))‖
    rw [dilIsoLM_apply]
    have hnorm : ‖WithLp.toLp 2 (dilStack M *ᵥ (WithLp.ofLp ((dilDomEquiv (R := R)).symm s)))‖
        = ‖(dilDomEquiv (R := R)).symm s‖ := (dilIso M hM).norm_map _
    rw [hnorm]
    have h1 : (dilDomEquiv (R := R)) ((dilDomEquiv (R := R)).symm s) = s :=
      LinearEquiv.apply_symm_apply _ _
    have h2 := dilDomEquiv_apply_val ((dilDomEquiv (R := R)).symm s)
    rw [h1] at h2
    rw [h2]
    exact ((embInlE (R := R)).norm_map _).symm⟩

/-- Extends the dilation isometry from the first-summand subspace to the entire doubled
Euclidean space. -/
private noncomputable def dilExtend (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    EuclideanSpace ℂ (R ⊕ R) →ₗᵢ[ℂ] EuclideanSpace ℂ (R ⊕ R) :=
  (dilIsoSub M hM).extend

/-- The extended isometry agrees with the dilation isometry on first-summand embeddings. -/
private theorem dilExtend_emb (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) (x : EuclideanSpace ℂ R) :
    dilExtend M hM (embInlE (R := R) x) = dilIso M hM x := by
  have h1 := LinearIsometry.extend_apply (dilIsoSub M hM)
    ⟨embInlE (R := R) x, LinearMap.mem_range_self (embInlLM (R := R)) x⟩
  refine h1.trans ?_
  show dilIsoLM M ((dilDomEquiv (R := R)).symm ⟨embInlE (R := R) x, _⟩) = dilIso M hM x
  rw [dilDomEquiv_symm_emb]
  rfl

/-- The matrix of the extended dilation isometry in the standard basis of the doubled register. -/
private noncomputable def dilUnitaryMat (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    Matrix (R ⊕ R) (R ⊕ R) ℂ :=
  fun i j => (dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j))) i

set_option maxHeartbeats 1000000 in

/-- The matrix of the extended dilation isometry is unitary. -/
private theorem dilUnitaryMat_unitary (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    dilUnitaryMat M hM ∈ Matrix.unitaryGroup (R ⊕ R) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  have step1 : ((star (dilUnitaryMat M hM)) * dilUnitaryMat M hM) a b
      = inner ℂ (dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket a)))
          (dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket b))) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply]
    show (starRingEnd ℂ) ((dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket a))) i) *
          ((dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket b))) i)
        = ((dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket b))) i) *
          (starRingEnd ℂ) ((dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket a))) i)
    exact mul_comm _ _
  rw [step1, LinearIsometry.inner_map_map]
  have step2 : inner ℂ (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket a) : EuclideanSpace ℂ (R ⊕ R))
        (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket b))
      = Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket a) (Qatlib.Foundations.PureStateMath.Ket b) := inner_euclidean_fromVec _ _
  rw [step2, inner_ket_ket, Matrix.one_apply]

set_option maxHeartbeats 1000000 in

/-- On an input supported in the first summand, the dilation unitary produces the images under
`M` and its defect square root. -/
private theorem dilUnitaryMat_action (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) (x : QState R) :
    dilUnitaryMat M hM *ᵥ (Sum.elim x 0) = Sum.elim (M *ᵥ x) (dilSqrt M *ᵥ x) := by
  funext i
  have hlin : ∀ (y : QState (R ⊕ R)) (i : R ⊕ R),
      (dilUnitaryMat M hM *ᵥ y) i = (dilExtend M hM (WithLp.toLp 2 y)) i := by
    intro y i
    have hdec : y = ∑ j, y j • Qatlib.Foundations.PureStateMath.Ket j := by
      funext k
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single k]
      · simp [Qatlib.Foundations.PureStateMath.Ket]
      · intro j _ hj
        simp only [Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, smul_eq_mul]
        rw [ite_eq_right (Ne.symm hj), mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ k) hmem
    have htoLp : WithLp.toLp 2 (∑ j, y j • Qatlib.Foundations.PureStateMath.Ket j)
        = ∑ j, y j • (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j) : EuclideanSpace ℂ (R ⊕ R)) := by
      apply WithLp.ofLp_injective
      rw [WithLp.ofLp_toLp, WithLp.ofLp_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [WithLp.ofLp_smul, WithLp.ofLp_toLp]
    have hsum : dilExtend M hM (WithLp.toLp 2 y)
        = ∑ j, y j • dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j)) := by
      conv_lhs => rw [hdec]
      rw [htoLp]
      show (dilExtend M hM).toLinearMap
          (∑ j, y j • (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j) : EuclideanSpace ℂ (R ⊕ R))) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
    rw [hsum]
    show (∑ j, dilUnitaryMat M hM i j * y j)
        = ((∑ j, y j • dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j))) : EuclideanSpace ℂ (R ⊕ R)) i
    rw [show ((∑ j, y j • dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j))) : EuclideanSpace ℂ (R ⊕ R)) i
        = ∑ j, y j * (dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j))) i from by
      rw [show ((∑ j, y j • dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j))) : EuclideanSpace ℂ (R ⊕ R)) i
          = WithLp.ofLp (∑ j, y j • dilExtend M hM (WithLp.toLp 2 (Qatlib.Foundations.PureStateMath.Ket j))) i from rfl,
        WithLp.ofLp_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hlin]
  have h2 : WithLp.toLp 2 (Sum.elim x (0 : QState R)) = embInlE (R := R) (WithLp.toLp 2 x) := by
    rw [embInlE_apply, WithLp.ofLp_toLp]
  rw [h2, dilExtend_emb, dilIso_apply, WithLp.ofLp_toLp]
  show (dilStack M *ᵥ x) i = Sum.elim (M *ᵥ x) (dilSqrt M *ᵥ x) i
  rw [dilStack_mulVec]

set_option maxHeartbeats 1000000 in

/-- Every contraction possesses a unitary dilation on the doubled register whose first output
block is its action. -/
private theorem exists_unitary_dilation (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    ∃ (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) (S : Matrix R R ℂ),
      U ∈ Matrix.unitaryGroup (R ⊕ R) ℂ ∧
        ∀ x : QState R, U *ᵥ (Sum.elim x 0) = Sum.elim (M *ᵥ x) (S *ᵥ x) :=
  ⟨dilUnitaryMat M hM, dilSqrt M, dilUnitaryMat_unitary M hM, dilUnitaryMat_action M hM⟩

/-- A contraction possesses a unitary on the doubled register sending `x ⊕ 0` to `M x ⊕ S x` for
some matrix `S`. This is the finite-dimensional dilation used in [AradLandau2010]. -/
theorem contraction_unitary_dilation (M : Matrix R R ℂ) (hM : ‖M‖ ≤ 1) :
    ∃ (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) (S : Matrix R R ℂ),
      U ∈ Matrix.unitaryGroup (R ⊕ R) ℂ ∧
        ∀ x : QState R, U *ᵥ (Sum.elim x 0) = Sum.elim (M *ᵥ x) (S *ᵥ x) :=
  exists_unitary_dilation M hM

end Dilation

section Register

variable {R : Type} [Fintype R] [DecidableEq R] {n t : ℕ}

/-- The position register with `2 * t + 2` slots, each carrying a copy of `R`. -/
private abbrev Pos (t : ℕ) (R : Type) := Fin (2 * t + 2) × R

/-- The position register together with a Boolean branch register. -/
private abbrev RegB (t : ℕ) (R : Type) := Bool × Pos t R

/-- Embeds a state into one position slot and sets all other slots to zero. -/
private def embSlot (i : Fin (2 * t + 2)) (φ : QState R) : QState (Pos t R) :=
  fun p => if p.1 = i then φ p.2 else 0

omit [Fintype R] [DecidableEq R] in

/-- The embedded state equals the original state in the selected slot and vanishes elsewhere. -/
private theorem embSlot_apply (i : Fin (2 * t + 2)) (φ : QState R) (p : Pos t R) :
    embSlot i φ p = if p.1 = i then φ p.2 else 0 := rfl

/-- Embeds a position-register state into the false branch. -/
private def brF (X : QState (Pos t R)) : QState (RegB t R) :=
  fun q => if q.1 = false then X q.2 else 0

/-- Embeds a position-register state into the true branch. -/
private def brT (X : QState (Pos t R)) : QState (RegB t R) :=
  fun q => if q.1 = true then X q.2 else 0

/-- The block diagonal matrix acting by `Af` on the false branch and `At` on the true branch. -/
private noncomputable def branchMatrix (Af At : Matrix (Pos t R) (Pos t R) ℂ) :
    Matrix (RegB t R) (RegB t R) ℂ :=
  fun x y => if x.1 = y.1 then (if x.1 then At x.2 y.2 else Af x.2 y.2) else 0

omit [Fintype R] [DecidableEq R] in

/-- A branch-matrix entry vanishes between different branches and otherwise selects the matrix
for that branch. -/
private theorem branchMatrix_apply (Af At : Matrix (Pos t R) (Pos t R) ℂ) (x y : RegB t R) :
    branchMatrix Af At x y
      = if x.1 = y.1 then (if x.1 then At x.2 y.2 else Af x.2 y.2) else 0 := rfl

/-- The position indices outside slot zero and the selected slot `k`. -/
private abbrev RestPos (t : ℕ) (R : Type) (k : Fin (2 * t + 2)) : Type :=
  { p : Pos t R // p.1 ≠ 0 ∧ p.1 ≠ k }

/-- Separates slot zero and slot `k` from the remaining positions. -/
private def slotFwd (k : Fin (2 * t + 2)) : Pos t R → (R ⊕ R) ⊕ RestPos t R k :=
  fun p => if h : p.1 = 0 then Sum.inl (Sum.inl p.2)
    else if h2 : p.1 = k then Sum.inl (Sum.inr p.2)
    else Sum.inr ⟨p, h, h2⟩

/-- Reassembles the distinguished two slots and the remaining positions into the position
register. -/
private def slotBwd (k : Fin (2 * t + 2)) : (R ⊕ R) ⊕ RestPos t R k → Pos t R :=
  fun s => match s with
    | Sum.inl (Sum.inl r) => (0, r)
    | Sum.inl (Sum.inr r) => (k, r)
    | Sum.inr p => p.1

/-- For nonzero `k`, identifies the position register with two copies of `R` and the remaining
positions. -/
private def slotEquiv (k : Fin (2 * t + 2)) (hk : k ≠ 0) : Pos t R ≃ (R ⊕ R) ⊕ RestPos t R k where
  toFun := slotFwd k
  invFun := slotBwd k
  left_inv p := by
    show slotBwd k (slotFwd k p) = p
    by_cases h : p.1 = 0
    · have h' : slotFwd k p = Sum.inl (Sum.inl p.2) := by simp [slotFwd, h]
      rw [h']
      exact Prod.ext h.symm rfl
    · by_cases h2 : p.1 = k
      · have h' : slotFwd k p = Sum.inl (Sum.inr p.2) := by simp [slotFwd, h2, hk]
        rw [h']
        exact Prod.ext h2.symm rfl
      · have h' : slotFwd k p = Sum.inr ⟨p, h, h2⟩ := by simp [slotFwd, h, h2]
        rw [h']
        rfl
  right_inv s := by
    show slotFwd k (slotBwd k s) = s
    rcases s with (⟨r⟩ | ⟨r⟩) | ⟨⟨i, r⟩, h1, h2⟩
    · show slotFwd k (0, r) = Sum.inl (Sum.inl r)
      simp [slotFwd]
    · show slotFwd k (k, r) = Sum.inl (Sum.inr r)
      simp [slotFwd, hk]
    · show slotFwd k (i, r) = Sum.inr ⟨⟨i, r⟩, h1, h2⟩
      simp [slotFwd, h1, h2]

omit [Fintype R] [DecidableEq R] in

/-- The forward slot equivalence is given by `slotFwd`. -/
private theorem slotEquiv_apply (k : Fin (2 * t + 2)) (hk : k ≠ 0) (p : Pos t R) :
    slotEquiv k hk p = slotFwd k p := rfl

omit [Fintype R] [DecidableEq R] in

/-- The inverse slot equivalence is given by `slotBwd`. -/
private theorem slotEquiv_symm_apply (k : Fin (2 * t + 2)) (hk : k ≠ 0)
    (s : (R ⊕ R) ⊕ RestPos t R k) :
    (slotEquiv k hk).symm s = slotBwd k s := rfl

omit [Fintype R] [DecidableEq R] in

/-- The forward slot map sends slot zero into the first distinguished copy of `R`. -/
@[simp] theorem slotFwd_zero (k : Fin (2 * t + 2)) (r : R) :
    slotFwd k (0, r) = Sum.inl (Sum.inl r) := by
  simp [slotFwd]

omit [Fintype R] [DecidableEq R] in

/-- For nonzero `k`, the forward slot map sends slot `k` into the second distinguished copy of
`R`. -/
@[simp] theorem slotFwd_k (k : Fin (2 * t + 2)) (hk : k ≠ 0) (r : R) :
    slotFwd k (k, r) = Sum.inl (Sum.inr r) := by
  simp [slotFwd, hk]

omit [Fintype R] [DecidableEq R] in

/-- A position outside slots zero and `k` maps into the remaining-position summand. -/
@[simp] theorem slotFwd_other (k : Fin (2 * t + 2)) (i : Fin (2 * t + 2))
    (h1 : i ≠ 0) (h2 : i ≠ k) (r : R) :
    slotFwd k (i, r) = Sum.inr ⟨(i, r), h1, h2⟩ := by
  simp [slotFwd, h1, h2]

omit [Fintype R] [DecidableEq R] in

/-- The backward slot map sends the first distinguished copy of `R` to slot zero. -/
@[simp] theorem slotBwd_inl_inl (k : Fin (2 * t + 2)) (r : R) :
    slotBwd k (Sum.inl (Sum.inl r)) = (0, r) := rfl

omit [Fintype R] [DecidableEq R] in

/-- The backward slot map sends the second distinguished copy of `R` to slot `k`. -/
@[simp] theorem slotBwd_inl_inr (k : Fin (2 * t + 2)) (r : R) :
    slotBwd k (Sum.inl (Sum.inr r)) = (k, r) := rfl

omit [Fintype R] [DecidableEq R] in

/-- The backward slot map preserves a remaining-position index. -/
@[simp] theorem slotBwd_inr (k : Fin (2 * t + 2)) (p : RestPos t R k) :
    slotBwd k (Sum.inr p) = p.1 := rfl

/-- Extends a matrix on the two distinguished copies of `R` by the identity on all remaining
positions. -/
private noncomputable def blockU (k : Fin (2 * t + 2)) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) :
    Matrix ((R ⊕ R) ⊕ RestPos t R k) ((R ⊕ R) ⊕ RestPos t R k) ℂ :=
  fun x y => match x with
    | Sum.inl a => match y with
      | Sum.inl b => U a b
      | Sum.inr _ => 0
    | Sum.inr c => match y with
      | Sum.inl _ => 0
      | Sum.inr d => if c = d then 1 else 0

omit [Fintype R] in

/-- The distinguished block of `blockU k U` equals `U`. -/
@[simp] theorem blockU_inl_inl (k : Fin (2 * t + 2)) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) (a b : R ⊕ R) :
    blockU k U (Sum.inl a) (Sum.inl b) = U a b := rfl

omit [Fintype R] in

/-- The block from remaining positions into distinguished positions is zero. -/
@[simp] theorem blockU_inl_inr (k : Fin (2 * t + 2)) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (a : R ⊕ R) (c : RestPos t R k) :
    blockU k U (Sum.inl a) (Sum.inr c) = 0 := rfl

omit [Fintype R] in

/-- The block from distinguished positions into remaining positions is zero. -/
@[simp] theorem blockU_inr_inl (k : Fin (2 * t + 2)) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (c : RestPos t R k) (b : R ⊕ R) :
    blockU k U (Sum.inr c) (Sum.inl b) = 0 := rfl

omit [Fintype R] in

/-- The remaining-position block of `blockU k U` is the identity matrix. -/
@[simp] theorem blockU_inr_inr (k : Fin (2 * t + 2)) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (c d : RestPos t R k) :
    blockU k U (Sum.inr c) (Sum.inr d) = if c = d then 1 else 0 := rfl

set_option maxHeartbeats 1000000 in

/-- Extending a unitary matrix by an identity block preserves unitarity. -/
private theorem blockU_unitary (k : Fin (2 * t + 2)) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (R ⊕ R) ℂ) :
    blockU (t := t) (R := R) k U ∈ Matrix.unitaryGroup ((R ⊕ R) ⊕ RestPos t R k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
  have hU' : ∀ a b : R ⊕ R, ∑ c, star (U c a) * U c b = if a = b then 1 else 0 := by
    intro a b
    have h := congrFun (congrFun hU a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun c _ => by rw [Matrix.conjTranspose_apply]
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
  rcases x with a | c <;> rcases y with b | d
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, blockU_inl_inl,
      blockU_inr_inl, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [hU']
    by_cases hab : a = b
    · rw [ite_eq_left hab, ite_eq_left (by rw [hab])]
    · rw [ite_eq_right hab, ite_eq_right (fun h => hab (Sum.inl.inj h))]
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, blockU_inl_inr,
      blockU_inr_inl, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    rw [ite_eq_right (fun h => by simp at h)]
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, blockU_inr_inl,
      blockU_inr_inr, blockU_inl_inr, star_zero, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add]
    rw [ite_eq_right (fun h => by simp at h)]
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      blockU_inl_inr, star_zero, zero_mul, Finset.sum_const_zero, zero_add, blockU_inr_inr]
    by_cases hcd : c = d
    · subst hcd
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        simp [he]
      · intro hmem
        exact absurd (Finset.mem_univ c) hmem
    · rw [Finset.sum_eq_zero]
      · rw [ite_eq_right (fun h => hcd (Sum.inr.inj h))]
      · intro e _
        by_cases hec : e = c
        · subst hec
          simp [hcd]
        · simp [hec]

/-- Transports a two-slot matrix to slots zero and `k`, acting identically on the other
positions. -/
private noncomputable def liftP (k : Fin (2 * t + 2)) (hk : k ≠ 0) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) :
    Matrix (Pos t R) (Pos t R) ℂ :=
  (blockU (t := t) (R := R) k U).submatrix (slotEquiv k hk) (slotEquiv k hk)

/-- Expresses the action of the lifted matrix through the slot equivalence and the block
extension. -/
private theorem liftP_mulVec (k : Fin (2 * t + 2)) (hk : k ≠ 0) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (z : QState (Pos t R)) :
    liftP (t := t) k hk U *ᵥ z
      = (blockU k U *ᵥ (z ∘ (slotEquiv k hk).symm)) ∘ (slotEquiv k hk) :=
  Matrix.submatrix_mulVec_equiv _ _ _ _

/-- Lifting a unitary two-slot matrix to the position register preserves unitarity. -/
private theorem liftP_unitary (k : Fin (2 * t + 2)) (hk : k ≠ 0) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (R ⊕ R) ℂ) :
    liftP (t := t) k hk U ∈ Matrix.unitaryGroup (Pos t R) ℂ := by
  have hU' := blockU_unitary k U hU
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU' ⊢
  rw [liftP, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU']
  exact Matrix.submatrix_one_equiv _

set_option maxHeartbeats 1000000 in

/-- On a state in slot zero, the lifted matrix places its two output components in slots zero
and `k`. -/
private theorem liftP_act0 (k : Fin (2 * t + 2)) (hk : k ≠ 0) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (φ : QState R) :
    liftP (t := t) k hk U *ᵥ embSlot 0 φ
      = embSlot 0 (fun a => (U *ᵥ Sum.elim φ 0) (Sum.inl a)) +
        embSlot k (fun a => (U *ᵥ Sum.elim φ 0) (Sum.inr a)) := by
  have hw : embSlot 0 φ ∘ (slotEquiv k hk).symm
      = Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) := by
    funext s
    rcases s with (⟨r'⟩ | ⟨r'⟩) | ⟨⟨i', r'⟩, h1, h2⟩
    · show embSlot 0 φ ((slotEquiv k hk).symm (Sum.inl (Sum.inl r'))) = _
      rw [slotEquiv_symm_apply, slotBwd_inl_inl, embSlot_apply]
      simp
    · show embSlot 0 φ ((slotEquiv k hk).symm (Sum.inl (Sum.inr r'))) = _
      rw [slotEquiv_symm_apply, slotBwd_inl_inr, embSlot_apply]
      simp [hk]
    · show embSlot 0 φ ((slotEquiv k hk).symm (Sum.inr ⟨⟨i', r'⟩, h1, h2⟩)) = _
      rw [slotEquiv_symm_apply, slotBwd_inr, embSlot_apply, ite_eq_right h1, Sum.elim_inr, Pi.zero_apply]
  have hb : blockU (t := t) (R := R) k U *ᵥ Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k))
      = Sum.elim (U *ᵥ Sum.elim φ 0) (0 : QState (RestPos t R k)) := by
    funext s
    rcases s with (⟨r'⟩ | ⟨r'⟩) | ⟨⟨i', r'⟩, h1, h2⟩
    · show (∑ z, blockU k U (Sum.inl (Sum.inl r')) z *
          Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) z) = _
      rw [Fintype.sum_sum_type]
      rw [show (∑ e : RestPos t R k, blockU k U (Sum.inl (Sum.inl r')) (Sum.inr e) *
          Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) (Sum.inr e)) = 0 from
        Finset.sum_eq_zero fun e _ => by simp]
      rw [add_zero]
      show (∑ c : R ⊕ R, blockU k U (Sum.inl (Sum.inl r')) (Sum.inl c) * Sum.elim φ 0 c) = _
      simp only [blockU_inl_inl]
      rfl
    · show (∑ z, blockU k U (Sum.inl (Sum.inr r')) z *
          Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) z) = _
      rw [Fintype.sum_sum_type]
      rw [show (∑ e : RestPos t R k, blockU k U (Sum.inl (Sum.inr r')) (Sum.inr e) *
          Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) (Sum.inr e)) = 0 from
        Finset.sum_eq_zero fun e _ => by simp]
      rw [add_zero]
      show (∑ c : R ⊕ R, blockU k U (Sum.inl (Sum.inr r')) (Sum.inl c) * Sum.elim φ 0 c) = _
      simp only [blockU_inl_inl]
      rfl
    · show (∑ z, blockU k U (Sum.inr ⟨⟨i', r'⟩, h1, h2⟩) z *
          Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) z) = _
      rw [Fintype.sum_sum_type]
      rw [show (∑ c : R ⊕ R, blockU k U (Sum.inr ⟨⟨i', r'⟩, h1, h2⟩) (Sum.inl c) *
          Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) (Sum.inl c)) = 0 from
        Finset.sum_eq_zero fun c _ => by simp]
      rw [zero_add]
      show (∑ e : RestPos t R k, blockU k U (Sum.inr ⟨⟨i', r'⟩, h1, h2⟩) (Sum.inr e) *
          Sum.elim (Sum.elim φ 0) (0 : QState (RestPos t R k)) (Sum.inr e)) = _
      rw [Finset.sum_eq_single ⟨⟨i', r'⟩, h1, h2⟩]
      · simp
      · intro e _ he
        rw [blockU_inr_inr, ite_eq_right (Ne.symm he)]
        simp
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
  funext p
  obtain ⟨i, r⟩ := p
  rw [liftP_mulVec, hw, hb, Function.comp_apply]
  by_cases h0 : i = 0
  · subst h0
    rw [slotEquiv_apply, slotFwd_zero]
    show (U *ᵥ Sum.elim φ 0) (Sum.inl r) = _
    rw [Pi.add_apply, embSlot_apply, embSlot_apply, ite_eq_left rfl,
      ite_eq_right (by exact fun h => hk h.symm)]
    rw [add_zero]
  · by_cases hkk : i = k
    · subst i
      rw [slotEquiv_apply, slotFwd_k k hk]
      show (U *ᵥ Sum.elim φ 0) (Sum.inr r) = _
      rw [Pi.add_apply, embSlot_apply, embSlot_apply,
        ite_eq_right (by exact fun h => hk h), ite_eq_left rfl]
      rw [zero_add]
    · rw [slotEquiv_apply, slotFwd_other k i h0 hkk]
      show (0 : QState (RestPos t R k)) ⟨⟨i, r⟩, h0, hkk⟩ = _
      rw [Pi.zero_apply, Pi.add_apply, embSlot_apply, embSlot_apply, ite_eq_right h0, ite_eq_right hkk,
        add_zero]

/-- The Boolean phase-oracle entry equals the corresponding signed-variable diagonal entry. -/
private theorem cbPhaseEntry_eq_dzO (x : Fin n → Bool) (o : Option (Fin n ⊕ Fin n)) :
    cbPhaseEntry x o = dzO (signVecC x) o := by
  cases o with
  | none => rfl
  | some k => cases k with
    | inl i => rfl
    | inr i => rfl

/-- The Boolean phase oracle equals `cbDelta` evaluated at the complex sign vector. -/
private theorem cbPhaseOracle_eq_cbDelta (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) :
    cbPhaseOracle δ x = cbDelta δ (signVecC x) := by
  ext a b
  show (Matrix.diagonal (fun r => cbPhaseEntry x (δ r))) a b
    = (Matrix.diagonal (fun r => dzval δ (signVecC x) r)) a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, cbPhaseEntry_eq_dzO, dzval_eq_dzO]
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]

/-- A diagonal matrix multiplies each state coordinate by the corresponding diagonal entry. -/
private theorem diagonal_mulVec_apply {I : Type} [Fintype I] [DecidableEq I] (d : I → ℂ)
    (z : QState I) (i : I) :
    (Matrix.diagonal d *ᵥ z) i = d i * z i := by
  show ∑ j, (Matrix.diagonal d) i j * z j = d i * z i
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Applies the signed-variable phase oracle in slot zero and acts identically in all other
slots. -/
private noncomputable def figOracleP (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) :
    Matrix (Pos t R) (Pos t R) ℂ :=
  Matrix.diagonal fun p => if p.1 = 0 then dzval δ (signVecC x) p.2 else 1

/-- The position oracle acts on slot zero by the signed-variable diagonal oracle. -/
private theorem figOracleP_mulVec_main (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool)
    (φ : QState R) :
    figOracleP (t := t) δ x *ᵥ embSlot 0 φ = embSlot 0 (cbDelta δ (signVecC x) *ᵥ φ) := by
  funext p
  obtain ⟨i, r⟩ := p
  show ((Matrix.diagonal fun p => if p.1 = 0 then dzval δ (signVecC x) p.2 else 1) *ᵥ embSlot 0 φ)
      (i, r) = _
  rw [diagonal_mulVec_apply, embSlot_apply, embSlot_apply]
  by_cases h0 : i = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_left rfl]
    show dzval δ (signVecC x) r * φ r = (cbDelta δ (signVecC x) *ᵥ φ) r
    rw [cbDelta, diagonal_mulVec_apply]
    rfl
  · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right h0, mul_zero]

/-- The position oracle fixes every state embedded in a nonzero slot. -/
private theorem figOracleP_mulVec_junk (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool)
    (i : Fin (2 * t + 2)) (h0 : i ≠ 0) (φ : QState R) :
    figOracleP (t := t) δ x *ᵥ embSlot i φ = embSlot i φ := by
  funext p
  obtain ⟨j, r⟩ := p
  show ((Matrix.diagonal fun p => if p.1 = 0 then dzval δ (signVecC x) p.2 else 1) *ᵥ embSlot i φ)
      (j, r) = _
  rw [diagonal_mulVec_apply, embSlot_apply]
  by_cases hj : j = 0
  · subst hj
    rw [ite_eq_left rfl, ite_eq_right (fun h => h0 h.symm), mul_zero]
  · rw [ite_eq_right hj, one_mul]

/-- The position oracle fixes every state supported outside slot zero. -/
private theorem figOracleP_mulVec_of_support (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool)
    (z : QState (Pos t R)) (hz : ∀ p, z p ≠ 0 → p.1 ≠ 0) :
    figOracleP (t := t) δ x *ᵥ z = z := by
  funext p
  show ((Matrix.diagonal fun p => if p.1 = 0 then dzval δ (signVecC x) p.2 else 1) *ᵥ z) p = _
  rw [diagonal_mulVec_apply]
  by_cases h0 : p.1 = 0
  · have hz0 : z p = 0 := by
      by_contra hne
      exact hz p hne h0
    rw [ite_eq_left h0, hz0, mul_zero]
  · rw [ite_eq_right h0, one_mul]

/-- Labels the main slot by `δ` and all other slots by the inactive oracle label. -/
private def figLabel (δ : R → Option (Fin n ⊕ Fin n)) : RegB t R → Option (Fin n ⊕ Fin n) :=
  fun q => if q.2.1 = 0 then δ q.2.2 else none

set_option maxHeartbeats 1000000 in

/-- The phase oracle for `figLabel` is the same position oracle on both Boolean branches. -/
private theorem figOracle_eq (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) :
    cbPhaseOracle (figLabel (t := t) (R := R) δ) x
      = branchMatrix (figOracleP δ x) (figOracleP δ x) := by
  ext a b
  show (Matrix.diagonal (fun q => cbPhaseEntry x (figLabel δ q))) a b = _
  by_cases hab : a = b
  · subst hab
    obtain ⟨bb, i, r⟩ := a
    rw [Matrix.diagonal_apply_eq, branchMatrix_apply]
    simp only [ite_self]
    show cbPhaseEntry x (figLabel δ (bb, (i, r)))
      = Matrix.diagonal (fun p => if p.1 = 0 then dzval δ (signVecC x) p.2 else 1) (i, r) (i, r)
    rw [Matrix.diagonal_apply_eq]
    show cbPhaseEntry x (if i = 0 then δ r else none)
      = if i = 0 then dzval δ (signVecC x) r else 1
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact cbPhaseEntry_eq_dzO x (δ r)
    · rw [ite_eq_right h0, ite_eq_right h0]
      rfl
  · rw [Matrix.diagonal_apply_ne _ hab, branchMatrix_apply]
    by_cases h1 : a.1 = b.1
    · rw [ite_eq_left h1]
      have h2 : a.2 ≠ b.2 := fun h => hab (Prod.ext h1 h)
      split
      · exact (Matrix.diagonal_apply_ne _ h2).symm
      · exact (Matrix.diagonal_apply_ne _ h2).symm
    · rw [ite_eq_right h1]

/-- Embedding two states in the same slot preserves their inner product. -/
private theorem inner_embSlot (i : Fin (2 * t + 2)) (φ ψ : QState R) :
    Qatlib.Foundations.PureStateMath.Inner (embSlot i φ) (embSlot i ψ) = Qatlib.Foundations.PureStateMath.Inner φ ψ := by
  rw [inner_apply, inner_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun r _ => by simp [embSlot_apply]
  · intro j _ hj
    rw [Finset.sum_eq_zero]
    intro r _
    simp [embSlot_apply, hj]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- States embedded in distinct slots have zero inner product. -/
private theorem inner_embSlot_disjoint {i i' : Fin (2 * t + 2)} (h : i ≠ i') (φ ψ : QState R) :
    Qatlib.Foundations.PureStateMath.Inner (embSlot i φ) (embSlot i' ψ) = 0 :=
  inner_eq_zero_of_support_disjoint _ _ fun p hp => by
    by_cases hp1 : p.1 = i'
    · have hpi : p.1 = i := by
        by_contra hne
        rw [embSlot_apply, ite_eq_right hne] at hp
        exact hp rfl
      exact absurd (hpi ▸ hp1) h
    · rw [embSlot_apply, ite_eq_right hp1]

/-- A lifted two-slot matrix fixes every state in a slot outside its two active positions. -/
private theorem liftP_actOther (k : Fin (2 * t + 2)) (hk : k ≠ 0) (U : Matrix (R ⊕ R) (R ⊕ R) ℂ)
    (i : Fin (2 * t + 2)) (h0 : i ≠ 0) (hik : i ≠ k) (φ : QState R) :
    liftP (t := t) k hk U *ᵥ embSlot i φ = embSlot i φ := by
  have hw : embSlot i φ ∘ (slotEquiv k hk).symm
      = Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) := by
    funext s
    rcases s with (⟨r'⟩ | ⟨r'⟩) | ⟨⟨i', r'⟩, h1, h2⟩
    · rw [Function.comp_apply, slotEquiv_symm_apply, slotBwd_inl_inl, embSlot_apply,
        ite_eq_right (fun h => h0 h.symm), Sum.elim_inl, Pi.zero_apply]
    · rw [Function.comp_apply, slotEquiv_symm_apply, slotBwd_inl_inr, embSlot_apply,
        ite_eq_right (fun h => hik h.symm), Sum.elim_inl, Pi.zero_apply]
    · rw [Function.comp_apply, slotEquiv_symm_apply, slotBwd_inr, Sum.elim_inr]
  have hb : blockU (t := t) (R := R) k U *ᵥ
        Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k))
      = Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) := by
    funext s
    rcases s with (⟨r'⟩ | ⟨r'⟩) | ⟨⟨i', r'⟩, h1, h2⟩
    · show (∑ z, blockU k U (Sum.inl (Sum.inl r')) z *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) z) = _
      rw [Fintype.sum_sum_type]
      rw [show (∑ c : R ⊕ R, blockU k U (Sum.inl (Sum.inl r')) (Sum.inl c) *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) (Sum.inl c))
          = 0 from Finset.sum_eq_zero fun c _ => by
          rw [blockU_inl_inl, Sum.elim_inl, Pi.zero_apply, mul_zero]]
      rw [zero_add]
      rw [show (∑ e : RestPos t R k, blockU k U (Sum.inl (Sum.inl r')) (Sum.inr e) *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) (Sum.inr e))
          = 0 from Finset.sum_eq_zero fun e _ => by rw [blockU_inl_inr, zero_mul]]
      rw [Sum.elim_inl, Pi.zero_apply]
    · show (∑ z, blockU k U (Sum.inl (Sum.inr r')) z *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) z) = _
      rw [Fintype.sum_sum_type]
      rw [show (∑ c : R ⊕ R, blockU k U (Sum.inl (Sum.inr r')) (Sum.inl c) *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) (Sum.inl c))
          = 0 from Finset.sum_eq_zero fun c _ => by
          rw [blockU_inl_inl, Sum.elim_inl, Pi.zero_apply, mul_zero]]
      rw [zero_add]
      rw [show (∑ e : RestPos t R k, blockU k U (Sum.inl (Sum.inr r')) (Sum.inr e) *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) (Sum.inr e))
          = 0 from Finset.sum_eq_zero fun e _ => by rw [blockU_inl_inr, zero_mul]]
      rw [Sum.elim_inl, Pi.zero_apply]
    · show (∑ z, blockU k U (Sum.inr ⟨⟨i', r'⟩, h1, h2⟩) z *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) z) = _
      rw [Fintype.sum_sum_type]
      rw [show (∑ c : R ⊕ R, blockU k U (Sum.inr ⟨⟨i', r'⟩, h1, h2⟩) (Sum.inl c) *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) (Sum.inl c))
          = 0 from Finset.sum_eq_zero fun c _ => by rw [blockU_inr_inl, zero_mul]]
      rw [zero_add]
      rw [show (∑ e : RestPos t R k, blockU k U (Sum.inr ⟨⟨i', r'⟩, h1, h2⟩) (Sum.inr e) *
          Sum.elim (0 : QState (R ⊕ R)) (fun c => embSlot i φ (c : RestPos t R k)) (Sum.inr e))
          = embSlot i φ (i', r') from by
        rw [Finset.sum_eq_single ⟨⟨i', r'⟩, h1, h2⟩]
        · rw [blockU_inr_inr, ite_eq_left rfl, one_mul, Sum.elim_inr]
        · intro e _ he
          rw [blockU_inr_inr, ite_eq_right (Ne.symm he), zero_mul]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem]
      rw [Sum.elim_inr]
  funext p
  rw [liftP_mulVec, hw, hb, Function.comp_apply]
  obtain ⟨i', r⟩ := p
  by_cases h0' : i' = 0
  · subst i'
    rw [slotEquiv_apply, slotFwd_zero, Sum.elim_inl, Pi.zero_apply, embSlot_apply,
      ite_eq_right (fun h => h0 h.symm)]
  · by_cases hik' : i' = k
    · subst i'
      rw [slotEquiv_apply, slotFwd_k k hk, Sum.elim_inl, Pi.zero_apply, embSlot_apply,
        ite_eq_right (fun h => hik h.symm)]
    · rw [slotEquiv_apply, slotFwd_other k i' h0' hik', Sum.elim_inr]

/-- Every position-register state is the sum of its individual slot embeddings. -/
private theorem pos_decomp (z : QState (Pos t R)) :
    z = ∑ i : Fin (2 * t + 2), embSlot i (fun r => z (i, r)) := by
  funext p
  obtain ⟨i, r⟩ := p
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [embSlot_apply, ite_eq_left rfl]
  · intro j _ hj
    rw [embSlot_apply, ite_eq_right (fun h => hj h.symm)]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- Embedding the zero state in any slot gives the zero state. -/
private theorem embSlot_zero (i : Fin (2 * t + 2)) : embSlot i (0 : QState R) = (0 : QState (Pos t R)) := by
  funext p
  rw [embSlot_apply, Pi.zero_apply]
  simp

/-- The lifted matrix fixes every state supported outside slots zero and `k`. -/
private theorem liftP_mulVec_of_support (k : Fin (2 * t + 2)) (hk : k ≠ 0)
    (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) (z : QState (Pos t R))
    (hz : ∀ p, z p ≠ 0 → p.1 ≠ 0 ∧ p.1 ≠ k) :
    liftP (t := t) k hk U *ᵥ z = z := by
  conv_lhs => rw [pos_decomp z]
  conv_rhs => rw [pos_decomp z]
  rw [show liftP (t := t) k hk U *ᵥ (∑ i : Fin (2 * t + 2), embSlot i (fun r => z (i, r)))
      = ∑ i : Fin (2 * t + 2), liftP (t := t) k hk U *ᵥ embSlot i (fun r => z (i, r)) from
    (map_sum (Matrix.mulVecLin (liftP (t := t) k hk U)) _ _).trans
      (Finset.sum_congr rfl fun i _ => Matrix.mulVecLin_apply _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h0 : i = 0
  · subst h0
    have hz0 : (fun r => z (0, r)) = 0 := funext fun r => by
      by_contra hne
      exact (hz (0, r) (by simpa using hne)).1 rfl
    rw [hz0, embSlot_zero, Matrix.mulVec_zero]
  · by_cases hik : i = k
    · have hzk : (fun r => z (i, r)) = 0 := funext fun r => by
        by_contra hne
        exact absurd hik (hz (i, r) hne).2
      rw [hzk, embSlot_zero, Matrix.mulVec_zero]
    · exact liftP_actOther k hk U i h0 hik _

omit [DecidableEq R] in

/-- The branch matrix applies `Af` to a state in the false branch. -/
private theorem branchMatrix_mulVec_brF (Af At : Matrix (Pos t R) (Pos t R) ℂ) (X : QState (Pos t R)) :
    branchMatrix Af At *ᵥ brF X = brF (Af *ᵥ X) := by
  funext q
  obtain ⟨b, p⟩ := q
  show (∑ y : RegB t R, branchMatrix Af At (b, p) y * brF X y) = brF (Af *ᵥ X) (b, p)
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases b
  · rw [show (∑ q : Pos t R, branchMatrix Af At (false, p) (true, q) * brF X (true, q)) = 0 from
      Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply, brF], zero_add]
    have h1 : (∑ q : Pos t R, branchMatrix Af At (false, p) (false, q) * brF X (false, q))
        = ∑ q : Pos t R, Af p q * X q :=
      Finset.sum_congr rfl fun q _ => by simp [branchMatrix_apply, brF]
    rw [h1]
    rfl
  · rw [show (∑ q : Pos t R, branchMatrix Af At (true, p) (false, q) * brF X (false, q)) = 0 from
      Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply, brF], add_zero]
    have h1 : (∑ q : Pos t R, branchMatrix Af At (true, p) (true, q) * brF X (true, q)) = 0 :=
      Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply, brF]
    rw [h1]
    rfl

omit [DecidableEq R] in

/-- The branch matrix applies `At` to a state in the true branch. -/
private theorem branchMatrix_mulVec_brT (Af At : Matrix (Pos t R) (Pos t R) ℂ) (X : QState (Pos t R)) :
    branchMatrix Af At *ᵥ brT X = brT (At *ᵥ X) := by
  funext q
  obtain ⟨b, p⟩ := q
  show (∑ y : RegB t R, branchMatrix Af At (b, p) y * brT X y) = brT (At *ᵥ X) (b, p)
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases b
  · rw [show (∑ q : Pos t R, branchMatrix Af At (false, p) (true, q) * brT X (true, q)) = 0 from
      Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply, brT], zero_add]
    have h1 : (∑ q : Pos t R, branchMatrix Af At (false, p) (false, q) * brT X (false, q)) = 0 :=
      Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply, brT]
    rw [h1]
    rfl
  · rw [show (∑ q : Pos t R, branchMatrix Af At (true, p) (false, q) * brT X (false, q)) = 0 from
      Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply, brT], add_zero]
    have h1 : (∑ q : Pos t R, branchMatrix Af At (true, p) (true, q) * brT X (true, q))
        = ∑ q : Pos t R, At p q * X q :=
      Finset.sum_congr rfl fun q _ => by simp [branchMatrix_apply, brT]
    rw [h1]
    rfl

set_option maxHeartbeats 1000000 in

/-- A branch matrix is unitary when both of its branch matrices are unitary. -/
private theorem branchMatrix_unitary (Af At : Matrix (Pos t R) (Pos t R) ℂ)
    (hAf : Af ∈ Matrix.unitaryGroup (Pos t R) ℂ) (hAt : At ∈ Matrix.unitaryGroup (Pos t R) ℂ) :
    branchMatrix Af At ∈ Matrix.unitaryGroup (RegB t R) ℂ := by
  have hAf' : ∀ a b : Pos t R, ∑ c, star (Af c a) * Af c b = if a = b then 1 else 0 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hAf
    intro a b
    have h := congrFun (congrFun hAf a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun c _ => by rw [Matrix.conjTranspose_apply]
  have hAt' : ∀ a b : Pos t R, ∑ c, star (At c a) * At c b = if a = b then 1 else 0 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hAt
    intro a b
    have h := congrFun (congrFun hAt a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun c _ => by rw [Matrix.conjTranspose_apply]
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  obtain ⟨bx, px⟩ := x
  obtain ⟨by', py⟩ := y
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  by_cases hb : bx = by'
  · subst hb
    cases bx
    · rw [show (∑ q : Pos t R, star (branchMatrix Af At (true, q) (false, px)) *
          branchMatrix Af At (true, q) (false, py)) = 0 from
        Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply], zero_add]
      have h1 : (∑ q : Pos t R, star (branchMatrix Af At (false, q) (false, px)) *
            branchMatrix Af At (false, q) (false, py))
          = ∑ q, star (Af q px) * Af q py :=
        Finset.sum_congr rfl fun q _ => by simp [branchMatrix_apply]
      rw [h1, hAf']
      by_cases hpp : px = py
      · rw [ite_eq_left hpp]
        simp [hpp]
      · rw [ite_eq_right hpp]
        simp [hpp]
    · rw [show (∑ q : Pos t R, star (branchMatrix Af At (false, q) (true, px)) *
          branchMatrix Af At (false, q) (true, py)) = 0 from
        Finset.sum_eq_zero fun q _ => by simp [branchMatrix_apply], add_zero]
      have h1 : (∑ q : Pos t R, star (branchMatrix Af At (true, q) (true, px)) *
            branchMatrix Af At (true, q) (true, py))
          = ∑ q, star (At q px) * At q py :=
        Finset.sum_congr rfl fun q _ => by simp [branchMatrix_apply]
      rw [h1, hAt']
      by_cases hpp : px = py
      · rw [ite_eq_left hpp]
        simp [hpp]
      · rw [ite_eq_right hpp]
        simp [hpp]
  · have hz : ∀ c : Bool, (∑ q : Pos t R, star (branchMatrix Af At (c, q) (bx, px)) *
        branchMatrix Af At (c, q) (by', py)) = 0 := by
      intro c
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hq : c = bx
      · rw [show branchMatrix Af At (c, q) (by', py) = 0 from by
          rw [branchMatrix_apply, ite_eq_right (fun h => hb (hq ▸ h))]]
        simp
      · rw [show branchMatrix Af At (c, q) (bx, px) = 0 from by
          rw [branchMatrix_apply, ite_eq_right hq]]
        simp
    rw [hz true, hz false, add_zero, ite_eq_right (fun h => hb (congrArg Prod.fst h))]

/-- The Hadamard matrix on the Boolean branch register, tensored with the identity on positions. -/
private noncomputable def hadGate : Matrix (RegB t R) (RegB t R) ℂ :=
  fun x y => if x.2 = y.2 then Qatlib.Foundations.PureStateMath.Hadamard x.1 y.1 else 0

omit [Fintype R] in

/-- The branch Hadamard matrix has the usual Hadamard entries when positions agree and zero
entries otherwise. -/
private theorem hadGate_apply (x y : RegB t R) :
    hadGate (t := t) (R := R) x y
      = if x.2 = y.2 then Qatlib.Foundations.PureStateMath.Hadamard x.1 y.1 else 0 := rfl

set_option maxHeartbeats 1000000 in

/-- The Hadamard gate on the branch register is unitary. -/
private theorem hadGate_unitary : hadGate (t := t) (R := R) ∈ Matrix.unitaryGroup (RegB t R) ℂ := by
  have hH := hadamard_unitary
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hH
  have hH' : ∀ a b : Bool, ∑ c : Bool,
      star (Qatlib.Foundations.PureStateMath.Hadamard c a) * Qatlib.Foundations.PureStateMath.Hadamard c b
        = if a = b then 1 else 0 := by
    intro a b
    have h := congrFun (congrFun hH a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun c _ => by rw [Matrix.conjTranspose_apply]
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
  obtain ⟨bx, px⟩ := x
  obtain ⟨by', py⟩ := y
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hadGate_apply]
  by_cases hp : px = py
  · subst hp
    have h1 : ∀ c : Bool, (∑ q : Pos t R,
          star (if q = px then Qatlib.Foundations.PureStateMath.Hadamard c bx else 0) *
            (if q = px then Qatlib.Foundations.PureStateMath.Hadamard c by' else 0))
        = star (Qatlib.Foundations.PureStateMath.Hadamard c bx) * Qatlib.Foundations.PureStateMath.Hadamard c by' := by
      intro c
      rw [Finset.sum_eq_single px]
      · simp
      · intro q _ hq
        rw [ite_eq_right hq]
        simp
      · intro hmem
        exact absurd (Finset.mem_univ px) hmem
    have h2 : (∑ c : Bool, ∑ q : Pos t R,
          star (if q = px then Qatlib.Foundations.PureStateMath.Hadamard c bx else 0) *
            (if q = px then Qatlib.Foundations.PureStateMath.Hadamard c by' else 0))
        = ∑ c : Bool, star (Qatlib.Foundations.PureStateMath.Hadamard c bx) * Qatlib.Foundations.PureStateMath.Hadamard c by' :=
      Finset.sum_congr rfl fun c _ => h1 c
    rw [h2, hH']
    by_cases hbb : bx = by'
    · rw [ite_eq_left hbb]
      simp [hbb]
    · rw [ite_eq_right hbb]
      simp [hbb]
  · have h0 : ∀ c : Bool, (∑ q : Pos t R,
        star (if q = px then Qatlib.Foundations.PureStateMath.Hadamard c bx else 0) *
          (if q = py then Qatlib.Foundations.PureStateMath.Hadamard c by' else 0)) = 0 := by
      intro c
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hq : q = px
      · subst hq
        rw [ite_eq_left rfl, ite_eq_right hp, mul_zero]
      · rw [ite_eq_right hq, star_zero, zero_mul]
    have h0' : (∑ c : Bool, ∑ q : Pos t R,
        star (if q = px then Qatlib.Foundations.PureStateMath.Hadamard c bx else 0) *
          (if q = py then Qatlib.Foundations.PureStateMath.Hadamard c by' else 0)) = 0 :=
      Finset.sum_eq_zero fun c _ => h0 c
    rw [h0', ite_eq_right (fun h => hp (Prod.ext_iff.mp h).2)]

/-- Expands the branch Hadamard action on the sum of false-branch and true-branch states. -/
private theorem hadGate_mulVec (X Y : QState (Pos t R)) :
    hadGate (t := t) (R := R) *ᵥ (brF X + brT Y)
      = fun q => Qatlib.Foundations.PureStateMath.Hadamard q.1 false * X q.2
          + Qatlib.Foundations.PureStateMath.Hadamard q.1 true * Y q.2 := by
  funext q
  obtain ⟨b, p⟩ := q
  show (∑ y : RegB t R, hadGate (b, p) y * (brF X + brT Y) y) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hfalse : (∑ q : Pos t R, hadGate (b, p) (false, q) * (brF X + brT Y) (false, q))
      = Qatlib.Foundations.PureStateMath.Hadamard b false * X p := by
    rw [Finset.sum_eq_single p]
    · rw [hadGate_apply, ite_eq_left rfl]
      simp [brF, brT]
    · intro q' _ hq
      rw [hadGate_apply, ite_eq_right (fun h => hq h.symm)]
      simp
    · intro hmem
      exact absurd (Finset.mem_univ p) hmem
  have htrue : (∑ q : Pos t R, hadGate (b, p) (true, q) * (brF X + brT Y) (true, q))
      = Qatlib.Foundations.PureStateMath.Hadamard b true * Y p := by
    rw [Finset.sum_eq_single p]
    · rw [hadGate_apply, ite_eq_left rfl]
      simp [brF, brT]
    · intro q' _ hq
      rw [hadGate_apply, ite_eq_right (fun h => hq h.symm)]
      simp
    · intro hmem
      exact absurd (Finset.mem_univ p) hmem
  rw [htrue, hfalse, add_comm]

/-- The true-column Hadamard entry is the inverse square root of two with sign determined by the
output bit. -/
private theorem hadamard_entry_true (b : Bool) :
    Qatlib.Foundations.PureStateMath.Hadamard b true = (if b then -1 else 1) * (Real.sqrt 2 : ℂ)⁻¹ := by
  cases b <;> simp [Qatlib.Foundations.PureStateMath.Hadamard]

/-- Pointwise equal finite matrix families have equal ordered products. -/
private theorem matProdFin_congr {k : ℕ} (M N : Fin k → Matrix R R ℂ) (h : ∀ j, M j = N j) :
    matProdFin k M = matProdFin k N := by
  unfold matProdFin
  congr 1
  exact List.map_congr_left fun j _ => h j

set_option maxHeartbeats 1000000 in

/-- Reassociates a product of pairs into its first left factor, an ordered product of adjacent
middle pairs, and its last right factor. -/
private theorem matProdFin_mul_shift {k : ℕ} (f g : Fin (k + 1) → Matrix R R ℂ) :
    matProdFin (k + 1) (fun i => f i * g i)
      = f 0 * matProdFin k (fun j : Fin k => g j.castSucc * f j.succ) * g (Fin.last k) := by
  induction k with
  | zero =>
    rw [matProdFin_succ_left, matProdFin_zero, matProdFin_zero, mul_one, mul_one]
    congr 1
  | succ k ih =>
    rw [matProdFin_succ_right, ih (fun j => f j.castSucc) (fun j => g j.castSucc),
      matProdFin_succ_right (fun j : Fin (k + 1) => g j.castSucc * f j.succ)]
    have e1 : f (Fin.castSucc 0) = f 0 := congrArg f (Fin.ext (by simp))
    have e2 : f (Fin.last k).succ = f (Fin.last (k + 1)) := congrArg f (Fin.ext rfl)
    have e3 : matProdFin k (fun j : Fin k => g j.castSucc.castSucc * f j.succ.castSucc)
        = matProdFin k (fun j : Fin k => g j.castSucc.castSucc * f j.castSucc.succ) :=
      matProdFin_congr _ _ fun j => congrArg₂ (· * ·) rfl (congrArg f (Fin.ext rfl))
    rw [e1, e2, e3]
    noncomm_ring

set_option maxHeartbeats 1000000 in

/-- Splits an ordered matrix product at the boundary between its first `k` and last `l` factors. -/
private theorem matProdFin_add {k l : ℕ} (M : Fin (k + l) → Matrix R R ℂ) :
    matProdFin (k + l) M
      = matProdFin k (fun j => M (Fin.castAdd l j)) * matProdFin l (fun j => M (Fin.natAdd k j)) := by
  induction l with
  | zero =>
    rw [matProdFin_zero, mul_one]
    rfl
  | succ l ih =>
    show matProdFin (k + l + 1) M
      = matProdFin k (fun j => M (Fin.castAdd (l + 1) j)) *
        matProdFin (l + 1) (fun j => M (Fin.natAdd k j))
    rw [matProdFin_succ_right, ih (fun j : Fin (k + l) => M j.castSucc)]
    have e1 : matProdFin (l + 1) (fun j : Fin (l + 1) => M (Fin.natAdd k j))
        = matProdFin l (fun j : Fin l => M (Fin.natAdd k (j.castSucc))) * M (Fin.natAdd k (Fin.last l)) := by
      rw [matProdFin_succ_right]
    have e2 : matProdFin k (fun j : Fin k => M ((Fin.castAdd l j).castSucc))
        = matProdFin k (fun j : Fin k => M (Fin.castAdd (l + 1) j)) :=
      matProdFin_congr _ _ fun j => congrArg M (Fin.ext rfl)
    have e3 : matProdFin l (fun j : Fin l => M ((Fin.natAdd k j).castSucc))
        = matProdFin l (fun j : Fin l => M (Fin.natAdd k (j.castSucc))) :=
      matProdFin_congr _ _ fun j => congrArg M (Fin.ext rfl)
    have e4 : M (Fin.last (k + l)) = M (Fin.natAdd k (Fin.last l)) := congrArg M (Fin.ext rfl)
    rw [e1, e2, e3, e4, mul_assoc]

/-- The signed-variable diagonal oracle on the original register. -/
private noncomputable def figOR (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) : Matrix R R ℂ :=
  cbDelta δ (signVecC x)

/-- The signed-variable oracle evaluated on Boolean inputs is Hermitian. -/
private theorem figOR_hermitian (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) :
    (figOR δ x)ᴴ = figOR δ x := by
  show (Matrix.diagonal fun r => dzval δ (signVecC x) r)ᴴ = Matrix.diagonal fun r => dzval δ (signVecC x) r
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext r
  show star (dzval δ (signVecC x) r) = dzval δ (signVecC x) r
  rw [dzval_eq_dzO]
  cases h : δ r with
  | none => simp [dzO]
  | some k =>
    cases k with
    | inl i =>
      show star (signVecC x (Sum.inl i)) = signVecC x (Sum.inl i)
      cases hxi : x i <;> simp [signVecC, hxi]
    | inr i =>
      show star (signVecC x (Sum.inr i)) = signVecC x (Sum.inr i)
      simp [signVecC]

/-- The signed-variable oracle can be moved between arguments of the state inner product without
changing it. -/
private theorem inner_figOR_symm (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) (X w : QState R) :
    Qatlib.Foundations.PureStateMath.Inner (figOR δ x *ᵥ X) w = Qatlib.Foundations.PureStateMath.Inner X (figOR δ x *ᵥ w) := by
  rw [inner_mulVec_left, figOR_hermitian]

end Register

section Assembly

variable {R : Type} [Fintype R] [DecidableEq R] {n t : ℕ}

variable (δ : R → Option (Fin n ⊕ Fin n)) (W : Fin (2 * t + 1) → Matrix R R ℂ) (u v : QState R)
  (dU : Fin (2 * t + 1) → Bool → Matrix (R ⊕ R) (R ⊕ R) ℂ)
  (dS : Fin (2 * t + 1) → Bool → Matrix R R ℂ)

/-- The odd slot `2 * j + 1` when it lies in the position register, and slot one otherwise. -/
private def slotF (t j : ℕ) : Fin (2 * t + 2) :=
  ⟨if 2 * j + 1 < 2 * t + 2 then 2 * j + 1 else 1, by split <;> omega⟩

/-- The even slot `2 * j + 2` when it lies in the position register, and slot one otherwise. -/
private def slotT (t j : ℕ) : Fin (2 * t + 2) :=
  ⟨if 2 * j + 2 < 2 * t + 2 then 2 * j + 2 else 1, by split <;> omega⟩

/-- The final position slot, with index `2 * t + 1`. -/
private def slotM (t : ℕ) : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩

/-- The false-branch auxiliary slot is never slot zero. -/
private theorem slotF_ne_zero (t j : ℕ) : slotF t j ≠ 0 := by
  intro h
  have h2 : (slotF t j).val = 0 := congrArg Fin.val h
  have h3 : (slotF t j).val = if 2 * j + 1 < 2 * t + 2 then 2 * j + 1 else 1 := rfl
  rw [h3] at h2
  split at h2 <;> omega

/-- The true-branch auxiliary slot is never slot zero. -/
private theorem slotT_ne_zero (t j : ℕ) : slotT t j ≠ 0 := by
  intro h
  have h2 : (slotT t j).val = 0 := congrArg Fin.val h
  have h3 : (slotT t j).val = if 2 * j + 2 < 2 * t + 2 then 2 * j + 2 else 1 := rfl
  rw [h3] at h2
  split at h2 <;> omega

/-- The middle-gate auxiliary slot is never slot zero. -/
private theorem slotM_ne_zero (t : ℕ) : slotM t ≠ 0 := by
  intro h
  have h2 : (slotM t).val = 0 := congrArg Fin.val h
  have h3 : (slotM t).val = 2 * t + 1 := rfl
  omega

/-- For `j ≤ t`, the false-branch auxiliary slot has index `2 * j + 1`. -/
private theorem slotF_val {t j : ℕ} (hj : j ≤ t) : (slotF t j).val = 2 * j + 1 := by
  show (if 2 * j + 1 < 2 * t + 2 then 2 * j + 1 else 1) = 2 * j + 1
  rw [ite_eq_left (by omega)]

/-- For `j < t`, the true-branch auxiliary slot has index `2 * j + 2`. -/
private theorem slotT_val {t j : ℕ} (hj : j < t) : (slotT t j).val = 2 * j + 2 := by
  show (if 2 * j + 2 < 2 * t + 2 then 2 * j + 2 else 1) = 2 * j + 2
  rw [ite_eq_left (by omega)]

/-- The middle-gate auxiliary slot has index `2 * t + 1`. -/
private theorem slotM_val (t : ℕ) : (slotM t).val = 2 * t + 1 := rfl

/-- Lifts the false-branch dilation for round `j` to the main slot and its odd auxiliary slot. -/
private noncomputable def figGateF (j : ℕ) : Matrix (Pos t R) (Pos t R) ℂ :=
  liftP (slotF t j) (slotF_ne_zero t j) (dU ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ false)

/-- Lifts the true-branch dilation, with reversed factor index, to the main slot and its even
auxiliary slot. -/
private noncomputable def figGateT (j : ℕ) : Matrix (Pos t R) (Pos t R) ℂ :=
  liftP (slotT t j) (slotT_ne_zero t j) (dU ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true)

/-- Lifts the middle-factor dilation to the main slot and the final auxiliary slot. -/
private noncomputable def figGateM : Matrix (Pos t R) (Pos t R) ℂ :=
  liftP (slotM t) (slotM_ne_zero t) (dU ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true)

/-- Combines the false-branch and true-branch lifted gates for one query round. -/
private noncomputable def figRoundGate (j : ℕ) : Matrix (RegB t R) (RegB t R) ℂ :=
  branchMatrix (figGateF dU j) (figGateT dU j)

/-- Under the dilation action hypothesis, the false-branch gate applies the adjoint factor in
slot zero and places the defect component in its auxiliary slot. -/
private theorem figGateF_act (j : ℕ) (φ : QState R)
    (hact : ∀ m b x, dU m b *ᵥ Sum.elim x 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x) (dS m b *ᵥ x)) :
    figGateF dU j *ᵥ embSlot 0 φ
      = embSlot 0 ((W ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩)ᴴ *ᵥ φ) +
        embSlot (slotF t j) (dS ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ false *ᵥ φ) := by
  have h1 := liftP_act0 (slotF t j) (slotF_ne_zero t j)
    (dU ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ false) φ
  rw [hact] at h1
  rw [show figGateF dU j = liftP (slotF t j) (slotF_ne_zero t j)
      (dU ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ false) from rfl, h1]
  congr 1

/-- Under the dilation action hypothesis, the true-branch gate applies the reversed-index factor
in slot zero and places the defect component in its auxiliary slot. -/
private theorem figGateT_act (j : ℕ) (φ : QState R)
    (hact : ∀ m b x, dU m b *ᵥ Sum.elim x 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x) (dS m b *ᵥ x)) :
    figGateT dU j *ᵥ embSlot 0 φ
      = embSlot 0 (W ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ φ) +
        embSlot (slotT t j) (dS ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true *ᵥ φ) := by
  have h1 := liftP_act0 (slotT t j) (slotT_ne_zero t j)
    (dU ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true) φ
  rw [hact] at h1
  rw [show figGateT dU j = liftP (slotT t j) (slotT_ne_zero t j)
      (dU ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true) from rfl, h1]
  congr 1

/-- Under the dilation action hypothesis, the middle gate applies the middle factor in slot zero
and places the defect component in the final slot. -/
private theorem figGateM_act (φ : QState R)
    (hact : ∀ m b x, dU m b *ᵥ Sum.elim x 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x) (dS m b *ᵥ x)) :
    figGateM dU *ᵥ embSlot 0 φ
      = embSlot 0 (W ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ φ) +
        embSlot (slotM t) (dS ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true *ᵥ φ) := by
  have h1 := liftP_act0 (slotM t) (slotM_ne_zero t)
    (dU ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true) φ
  rw [hact] at h1
  rw [show figGateM dU = liftP (slotM t) (slotM_ne_zero t)
      (dU ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true) from rfl, h1]
  congr 1

/-- The false-branch gate fixes states supported outside its main and auxiliary slots. -/
private theorem figGateF_supported (j : ℕ) (z : QState (Pos t R))
    (hz : ∀ p, z p ≠ 0 → p.1 ≠ 0 ∧ p.1 ≠ slotF t j) :
    figGateF dU j *ᵥ z = z :=
  liftP_mulVec_of_support _ _ _ _ hz

/-- The true-branch gate fixes states supported outside its main and auxiliary slots. -/
private theorem figGateT_supported (j : ℕ) (z : QState (Pos t R))
    (hz : ∀ p, z p ≠ 0 → p.1 ≠ 0 ∧ p.1 ≠ slotT t j) :
    figGateT dU j *ᵥ z = z :=
  liftP_mulVec_of_support _ _ _ _ hz

/-- The middle gate fixes states supported outside its main and final slots. -/
private theorem figGateM_supported (z : QState (Pos t R))
    (hz : ∀ p, z p ≠ 0 → p.1 ≠ 0 ∧ p.1 ≠ slotM t) :
    figGateM dU *ᵥ z = z :=
  liftP_mulVec_of_support _ _ _ _ hz

/-- The false-branch state obtained by iterating its lifted gate followed by the position
oracle, starting from `u` in slot zero. -/
private noncomputable def figAstate (x : Fin n → Bool) : ℕ → QState (Pos t R)
  | 0 => embSlot 0 u
  | j + 1 => figOracleP δ x *ᵥ (figGateF dU j *ᵥ figAstate x j)

/-- The true-branch state obtained by iterating its lifted gate followed by the position oracle,
starting from `v` in slot zero. -/
private noncomputable def figBstate (x : Fin n → Bool) : ℕ → QState (Pos t R)
  | 0 => embSlot 0 v
  | j + 1 => figOracleP δ x *ᵥ (figGateT dU j *ᵥ figBstate x j)

/-- The main-register chain alternating adjoint factors and signed-variable oracles, starting
from `u`. -/
private noncomputable def figAchain (x : Fin n → Bool) : ℕ → QState R
  | 0 => u
  | j + 1 => figOR δ x *ᵥ ((W ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩)ᴴ *ᵥ figAchain x j)

/-- The main-register chain alternating reversed-index factors and signed-variable oracles,
starting from `v`. -/
private noncomputable def figBchain (x : Fin n → Bool) : ℕ → QState R
  | 0 => v
  | j + 1 => figOR δ x *ᵥ (W ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain x j)

set_option maxHeartbeats 1000000 in

/-- Expresses pairing with the false-branch main chain by an ordered product of factors and
oracles in the second argument. -/
private theorem figAchain_inner (x : Fin n → Bool) (j : ℕ) (hj : j ≤ t) (w : QState R) :
    Qatlib.Foundations.PureStateMath.Inner (figAchain δ W u x j) w
      = Qatlib.Foundations.PureStateMath.Inner u (matProdFin j (fun i : Fin j =>
          W ⟨i.val % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ * figOR δ x) *ᵥ w) := by
  induction j generalizing w with
  | zero =>
    show Qatlib.Foundations.PureStateMath.Inner u w = Qatlib.Foundations.PureStateMath.Inner u (matProdFin 0 _ *ᵥ w)
    rw [matProdFin_zero, Matrix.one_mulVec]
  | succ j ih =>
    have hstep : figAchain δ W u x (j + 1)
        = figOR δ x *ᵥ ((W ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩)ᴴ *ᵥ figAchain δ W u x j) := rfl
    rw [hstep, inner_figOR_symm, inner_mulVec_left, Matrix.conjTranspose_conjTranspose]
    rw [ih (by omega) _, matProdFin_succ_right]
    have hcs : (fun i : Fin j => (fun i' : Fin (j + 1) =>
          W ⟨i'.val % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ * figOR δ x) i.castSucc)
        = fun i : Fin j => W ⟨i.val % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ * figOR δ x := rfl
    have hlast : W ⟨(Fin.last j).val % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ * figOR δ x
        = W ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ * figOR δ x := rfl
    rw [hcs, hlast, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

set_option maxHeartbeats 1000000 in

/-- Expresses the true-branch main chain as an ordered product of oracles and factors applied to
`v`. -/
private theorem figBchain_eq (x : Fin n → Bool) (j : ℕ) (hj : j ≤ t) :
    figBchain δ W v x j
      = matProdFin j (fun i : Fin j => figOR δ x *
          W ⟨(2 * t - j + 1 + i.val) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩) *ᵥ v := by
  induction j with
  | zero =>
    show v = matProdFin 0 _ *ᵥ v
    rw [matProdFin_zero, Matrix.one_mulVec]
  | succ j ih =>
    have hstep : figBchain δ W v x (j + 1)
        = figOR δ x *ᵥ (W ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x j) := rfl
    rw [hstep, ih (by omega), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [matProdFin_succ_left]
    congr 1
    · congr 1
      have hv0 : (0 : Fin (j + 1)).val = 0 := by simp
      exact congrArg W (Fin.ext (congrArg (· % (2 * t + 1)) (by omega)))
    · exact matProdFin_congr _ _ fun i =>
        congrArg₂ (· * ·) rfl (congrArg W (Fin.ext (congrArg (· % (2 * t + 1)) (by
          have hs : (i.succ : Fin (j + 1)).val = i.val + 1 := by simp
          omega))))

/-- An index at most `2 * t` is unchanged by reduction modulo `2 * t + 1`. -/
private theorem figW_mod_eq (a : ℕ) (ha : a ≤ 2 * t) :
    (⟨a % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * t + 1)) = ⟨a, by omega⟩ :=
  Fin.ext (Nat.mod_eq_of_lt (by omega))

/-- Before the last factor, a constant-input sandwich slot equals its matrix factor followed by
the signed-variable oracle. -/
private theorem cbSlot_const_lt {k : ℕ} (W' : Fin (2 * k + 1) → Matrix R R ℂ) (i : Fin (2 * k + 1))
    (h : i.val < 2 * k) (z : Fin n → Bool) :
    cbSlot W' δ (fun _ => signVecC z) i = W' i * figOR δ z := by
  show (if h' : i.val < 2 * k then W' ⟨i.val, by omega⟩ * cbDelta δ (signVecC z)
    else W' ⟨i.val, by omega⟩) = _
  rw [dite_eq_left h]
  show W' ⟨i.val, by omega⟩ * cbDelta δ (signVecC z) = W' i * figOR δ z
  exact congrArg₂ (· * ·) (congrArg W' (Fin.ext rfl)) rfl

/-- At the last factor, a constant-input sandwich slot equals the matrix factor alone. -/
private theorem cbSlot_const_ge {k : ℕ} (W' : Fin (2 * k + 1) → Matrix R R ℂ) (i : Fin (2 * k + 1))
    (h : ¬ i.val < 2 * k) (z : Fin n → Bool) :
    cbSlot W' δ (fun _ => signVecC z) i = W' i := by
  show (if h' : i.val < 2 * k then W' ⟨i.val, by omega⟩ * cbDelta δ (signVecC z)
    else W' ⟨i.val, by omega⟩) = W' i
  rw [dite_eq_right h]

set_option maxHeartbeats 1000000 in

/-- Combines the two length-`k` chains and their middle factor into the full ordered product of
`cbSlot` factors. -/
private theorem fig_chain_sandwich (z : Fin n → Bool) :
    ∀ (k : ℕ) (W' : Fin (2 * k + 1) → Matrix R R ℂ),
      (matProdFin k (fun i : Fin k => W' ⟨i.val, by omega⟩ * figOR δ z)) *
        W' ⟨k, by omega⟩ *
        (matProdFin k (fun i : Fin k => figOR δ z * W' ⟨k + 1 + i.val, by omega⟩))
      = matProdFin (2 * k + 1) (cbSlot W' δ (fun _ => signVecC z)) := by
  intro k
  induction k with
  | zero =>
    intro W'
    rw [matProdFin_zero, matProdFin_zero, one_mul, mul_one]
    show W' ⟨0, by omega⟩ = matProdFin (0 + 1) (cbSlot W' δ (fun _ => signVecC z))
    rw [matProdFin_succ_left, matProdFin_zero, mul_one]
    show W' ⟨0, by omega⟩ = cbSlot W' δ (fun _ => signVecC z) 0
    rw [cbSlot_const_ge δ W' 0 (by show ¬ (0 : ℕ) < 2 * 0; omega) z]
    exact congrArg W' (Fin.ext rfl)
  | succ k ih =>
    intro W'

    have hP : matProdFin (k + 1) (fun i : Fin (k + 1) => W' ⟨i.val, by omega⟩ * figOR δ z)
        = (W' ⟨0, by omega⟩ * figOR δ z) *
          matProdFin k (fun i : Fin k => W' ⟨i.val + 1, by omega⟩ * figOR δ z) := by
      rw [matProdFin_succ_left]
      congr 1

    have hB : matProdFin (k + 1) (fun i : Fin (k + 1) => figOR δ z * W' ⟨k + 1 + 1 + i.val, by omega⟩)
        = matProdFin k (fun i : Fin k => figOR δ z * W' ⟨k + 1 + i.val + 1, by omega⟩) *
          (figOR δ z * W' ⟨2 * k + 2, by omega⟩) := by
      rw [matProdFin_succ_right]
      congr 1
      · exact matProdFin_congr _ _ fun i => congrArg₂ (· * ·) rfl (congrArg W' (Fin.ext (by
          show k + 1 + 1 + (i.castSucc : Fin (k + 1)).val = k + 1 + i.val + 1
          show k + 1 + 1 + i.val = k + 1 + i.val + 1
          omega)))
      · show figOR δ z * W' ⟨k + 1 + 1 + (Fin.last k).val, by omega⟩ = figOR δ z * W' ⟨2 * k + 2, by omega⟩
        exact congrArg₂ (· * ·) rfl (congrArg W' (Fin.ext (by
          show k + 1 + 1 + (Fin.last k).val = 2 * k + 2
          rw [Fin.val_last]
          omega)))

    have hS : matProdFin (2 * (k + 1) + 1) (cbSlot W' δ (fun _ => signVecC z))
        = (W' ⟨0, by omega⟩ * figOR δ z) *
          (matProdFin (2 * k + 1) (cbSlot (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩) δ
            (fun _ => signVecC z)) *
          (figOR δ z * W' ⟨2 * k + 2, by omega⟩)) := by
      rw [matProdFin_succ_left]
      have h0 : cbSlot W' δ (fun _ => signVecC z) (0 : Fin (2 * (k + 1) + 1)) = W' ⟨0, by omega⟩ * figOR δ z := by
        rw [cbSlot_const_lt δ W' (0 : Fin (2 * (k + 1) + 1)) (by show (0 : ℕ) < 2 * (k + 1); omega) z]
        exact congrArg₂ (· * ·) (congrArg W' (Fin.ext rfl)) rfl
      rw [h0]
      congr 1

      show matProdFin (2 * k + 1 + 1) (fun j : Fin (2 * k + 1 + 1) =>
          cbSlot W' δ (fun _ => signVecC z) j.succ) = _
      rw [matProdFin_succ_right]
      have hlast : cbSlot W' δ (fun _ => signVecC z) ((Fin.last (2 * k + 1)).succ)
          = W' ⟨2 * k + 2, by omega⟩ := by
        rw [cbSlot_const_ge δ W' ((Fin.last (2 * k + 1)).succ) (by
          show ¬ (2 * k + 1 + 1 : ℕ) < 2 * (k + 1)
          omega) z]
        exact congrArg W' (Fin.ext (by
          show 2 * k + 1 + 1 = 2 * k + 2
          omega))
      rw [hlast]

      have hmid : matProdFin (2 * k + 1) (fun j : Fin (2 * k + 1) =>
            cbSlot W' δ (fun _ => signVecC z) (j.castSucc).succ)
          = matProdFin (2 * k + 1) (fun j : Fin (2 * k + 1) =>
              W' ⟨j.val + 1, by omega⟩ * figOR δ z) := by
        refine matProdFin_congr _ _ fun j => ?_
        show cbSlot W' δ (fun _ => signVecC z)
            ((j.castSucc).succ) = W' ⟨j.val + 1, by omega⟩ * figOR δ z
        exact (cbSlot_const_lt δ W' ((j.castSucc : Fin (2 * k + 2)).succ) (by
          show j.val + 1 < 2 * (k + 1)
          have := j.isLt
          omega) z).trans (congrArg₂ (· * ·) (congrArg W' (Fin.ext rfl)) rfl)
      rw [hmid]

      have hsw : matProdFin (2 * k + 1) (cbSlot (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩) δ
              (fun _ => signVecC z)) * figOR δ z
          = matProdFin (2 * k + 1) (fun j : Fin (2 * k + 1) => W' ⟨j.val + 1, by omega⟩ * figOR δ z) := by
        rw [matProdFin_succ_right]
        rw [matProdFin_succ_right]
        rw [mul_assoc]
        congr 1
        · exact matProdFin_congr _ _ fun j =>
            cbSlot_const_lt δ (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩) j.castSucc
              (by
                show j.val < 2 * k
                have hjl := j.isLt
                omega)
              z
        · show cbSlot (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩) δ (fun _ => signVecC z)
                (Fin.last (2 * k)) * figOR δ z = _
          rw [cbSlot_const_ge δ (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩) (Fin.last (2 * k))
            (by show ¬ (2 * k : ℕ) < 2 * k; omega) z]
      rw [← hsw, mul_assoc]

    rw [hP, hB, hS]
    have hstep := ih (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩)
    show (W' ⟨0, by omega⟩ * figOR δ z) *
        matProdFin k (fun i : Fin k => W' ⟨i.val + 1, by omega⟩ * figOR δ z) *
        W' ⟨k + 1, by omega⟩ *
        (matProdFin k (fun i : Fin k => figOR δ z * W' ⟨k + 1 + i.val + 1, by omega⟩) *
          (figOR δ z * W' ⟨2 * k + 2, by omega⟩))
      = (W' ⟨0, by omega⟩ * figOR δ z) *
        (matProdFin (2 * k + 1) (cbSlot (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩) δ
          (fun _ => signVecC z)) *
        (figOR δ z * W' ⟨2 * k + 2, by omega⟩))
    rw [show W' ⟨k + 1, by omega⟩ = (fun i : Fin (2 * k + 1) => W' ⟨i.val + 1, by omega⟩) ⟨k, by omega⟩
        from rfl]
    rw [← hstep]
    noncomm_ring

set_option maxHeartbeats 1000000 in

/-- The product of the two query chains and their middle factor equals `cbSandwichMatrix` on
constant sign-vector inputs. -/
private theorem fig_sandwich_matrix (x : Fin n → Bool) :
    (matProdFin t (fun i : Fin t =>
        W ⟨i.val % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ * figOR δ x)) *
      W ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *
      (matProdFin t (fun i : Fin t => figOR δ x *
        W ⟨(2 * t - t + 1 + i.val) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩))
      = cbSandwichMatrix W δ (fun _ => signVecC x) := by
  have hP : matProdFin t (fun i : Fin t =>
        W ⟨i.val % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ * figOR δ x)
      = matProdFin t (fun i : Fin t => W ⟨i.val, by omega⟩ * figOR δ x) :=
    matProdFin_congr _ _ fun i => congrArg₂ (· * ·) (congrArg W (figW_mod_eq i.val (by omega))) rfl
  have hW : (⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * t + 1)) = ⟨t, by omega⟩ :=
    figW_mod_eq t (by omega)
  have hB : matProdFin t (fun i : Fin t => figOR δ x *
        W ⟨(2 * t - t + 1 + i.val) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩)
      = matProdFin t (fun i : Fin t => figOR δ x * W ⟨t + 1 + i.val, by omega⟩) := by
    refine matProdFin_congr _ _ fun i => congrArg₂ (· * ·) rfl (congrArg W ?_)
    have hv : 2 * t - t + 1 + i.val = t + 1 + i.val := by omega
    rw [hv]
    exact figW_mod_eq _ (by omega)
  rw [hP, hW, hB, cbSandwichMatrix_eq]
  exact fig_chain_sandwich δ x t W

set_option maxHeartbeats 1000000 in

/-- Under the dilation action hypothesis, the false-branch main slot equals `figAchain`, and all
other nonzero coordinates lie in previously used odd slots. -/
private theorem figAstate_supp (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0)) :
    ∀ (j : ℕ), j ≤ t →
      (∀ r, figAstate δ u dU x j (0, r) = figAchain δ W u x j r) ∧
      (∀ i r, figAstate δ u dU x j (i, r) ≠ 0 → i.val = 0 ∨ ∃ j', j' < j ∧ i.val = 2 * j' + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    constructor
    · intro r
      show embSlot 0 u (0, r) = u r
      rw [embSlot_apply, ite_eq_left rfl]
    · intro i r hne
      left
      have hi : i = 0 := by
        by_contra h0
        exact hne (by
          show embSlot 0 u (i, r) = 0
          rw [embSlot_apply, ite_eq_right h0])
      exact congrArg Fin.val hi
  | succ j ih =>
    intro hj
    obtain ⟨hmain, hsupp⟩ := ih (by omega)
    set Ra : QState (Pos t R) := figAstate δ u dU x j - embSlot 0 (figAchain δ W u x j) with hRa
    have hRa0 : ∀ r, Ra (0, r) = 0 := by
      intro r
      rw [hRa, Pi.sub_apply, hmain r, embSlot_apply, ite_eq_left rfl, sub_self]
    have hRa_supp : ∀ p, Ra p ≠ 0 → p.1 ≠ 0 ∧ p.1 ≠ slotF t j := by
      intro p hp
      have hpA : figAstate δ u dU x j p ≠ 0 := by
        intro hz
        apply hp
        rw [hRa, Pi.sub_apply, hz]
        by_cases h0 : p.1 = 0
        · have hp0 : p = (0, p.2) := Prod.ext h0 rfl
          rw [hp0, embSlot_apply, ite_eq_left rfl]
          rw [hp0] at hz
          rw [hmain p.2] at hz
          rw [hz, sub_self]
        · rw [embSlot_apply, ite_eq_right h0, sub_zero]
      obtain (h0 | ⟨j', hj1, hj2⟩) := hsupp p.1 p.2 hpA
      · exfalso
        have hp0 : p = (0, p.2) := Prod.ext (Fin.ext h0) rfl
        rw [hp0] at hp
        exact hp (hRa0 p.2)
      · constructor
        · intro hzero
          rw [hzero] at hj2
          simp at hj2
        · intro hk
          have hv : p.1.val = (slotF t j).val := congrArg Fin.val hk
          rw [slotF_val (by omega)] at hv
          omega
    have hgate : figGateF dU j *ᵥ figAstate δ u dU x j
        = embSlot 0 ((W ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩)ᴴ *ᵥ figAchain δ W u x j) +
          embSlot (slotF t j) (dS ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ false *ᵥ figAchain δ W u x j) +
          Ra := by
      have hdec : figAstate δ u dU x j = embSlot 0 (figAchain δ W u x j) + Ra :=
        (add_sub_cancel _ _).symm
      rw [hdec, Matrix.mulVec_add, figGateF_act W dU dS j _ hact,
          figGateF_supported dU j Ra hRa_supp]
    have hora : figOracleP δ x *ᵥ (figGateF dU j *ᵥ figAstate δ u dU x j)
        = embSlot 0 (figOR δ x *ᵥ ((W ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩)ᴴ *ᵥ figAchain δ W u x j)) +
          embSlot (slotF t j) (dS ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ false *ᵥ figAchain δ W u x j) +
          Ra := by
      rw [hgate, Matrix.mulVec_add, Matrix.mulVec_add, figOracleP_mulVec_main,
        figOracleP_mulVec_junk _ _ _ (slotF_ne_zero t j), figOracleP_mulVec_of_support]
      · rfl
      · intro p hp
        exact (hRa_supp p hp).1
    have hA : figAstate δ u dU x (j + 1)
        = figOracleP δ x *ᵥ (figGateF dU j *ᵥ figAstate δ u dU x j) := rfl
    have hC : figAchain δ W u x (j + 1)
        = figOR δ x *ᵥ ((W ⟨j % (2 * t + 1), Nat.mod_lt _ (by omega)⟩)ᴴ *ᵥ figAchain δ W u x j) := rfl
    constructor
    · intro r
      rw [hA, hora, hC]
      rw [Pi.add_apply, Pi.add_apply, embSlot_apply, embSlot_apply, hRa0]
      rw [ite_eq_left rfl,
          ite_eq_right (show ((0, r) : Pos t R).1 ≠ slotF t j from fun h => slotF_ne_zero t j h.symm)]
      simp
    · intro i r hne
      rw [hA, hora] at hne
      rw [Pi.add_apply, Pi.add_apply] at hne
      by_cases h0 : i = 0
      · left
        exact congrArg Fin.val h0
      · right
        by_cases hk : i = slotF t j
        · exact ⟨j, by omega, by rw [hk, slotF_val (by omega)]⟩
        · have hne3 : Ra (i, r) ≠ 0 := by
            intro hz
            apply hne
            rw [hz]
            rw [embSlot_apply, embSlot_apply, ite_eq_right h0, ite_eq_right hk]
            simp
          have hpA : figAstate δ u dU x j (i, r) ≠ 0 := by
            intro hz
            apply hne3
            rw [hRa, Pi.sub_apply, hz]
            rw [embSlot_apply, ite_eq_right h0, sub_zero]
          obtain (h0' | ⟨j', hj1, hj2⟩) := hsupp i r hpA
          · exact absurd (Fin.ext h0') h0
          · exact ⟨j', by omega, hj2⟩

set_option maxHeartbeats 1000000 in

/-- Under the dilation action hypothesis, the true-branch main slot equals `figBchain`, and all
other nonzero coordinates lie in previously used even slots. -/
private theorem figBstate_supp (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0)) :
    ∀ (j : ℕ), j ≤ t →
      (∀ r, figBstate δ v dU x j (0, r) = figBchain δ W v x j r) ∧
      (∀ i r, figBstate δ v dU x j (i, r) ≠ 0 → i.val = 0 ∨ ∃ j', j' < j ∧ i.val = 2 * j' + 2) := by
  intro j
  induction j with
  | zero =>
    intro _
    constructor
    · intro r
      show embSlot 0 v (0, r) = v r
      rw [embSlot_apply, ite_eq_left rfl]
    · intro i r hne
      left
      have hi : i = 0 := by
        by_contra h0
        exact hne (by
          show embSlot 0 v (i, r) = 0
          rw [embSlot_apply, ite_eq_right h0])
      exact congrArg Fin.val hi
  | succ j ih =>
    intro hj
    obtain ⟨hmain, hsupp⟩ := ih (by omega)
    set Rb : QState (Pos t R) := figBstate δ v dU x j - embSlot 0 (figBchain δ W v x j) with hRb
    have hRb0 : ∀ r, Rb (0, r) = 0 := by
      intro r
      rw [hRb, Pi.sub_apply, hmain r, embSlot_apply, ite_eq_left rfl, sub_self]
    have hRb_supp : ∀ p, Rb p ≠ 0 → p.1 ≠ 0 ∧ p.1 ≠ slotT t j := by
      intro p hp
      have hpA : figBstate δ v dU x j p ≠ 0 := by
        intro hz
        apply hp
        rw [hRb, Pi.sub_apply, hz]
        by_cases h0 : p.1 = 0
        · have hp0 : p = (0, p.2) := Prod.ext h0 rfl
          rw [hp0, embSlot_apply, ite_eq_left rfl]
          rw [hp0] at hz
          rw [hmain p.2] at hz
          rw [hz, sub_self]
        · rw [embSlot_apply, ite_eq_right h0, sub_zero]
      obtain (h0 | ⟨j', hj1, hj2⟩) := hsupp p.1 p.2 hpA
      · exfalso
        have hp0 : p = (0, p.2) := Prod.ext (Fin.ext h0) rfl
        rw [hp0] at hp
        exact hp (hRb0 p.2)
      · constructor
        · intro hzero
          rw [hzero] at hj2
          simp at hj2
        · intro hk
          have hv : p.1.val = (slotT t j).val := congrArg Fin.val hk
          rw [slotT_val (by omega)] at hv
          omega
    have hgate : figGateT dU j *ᵥ figBstate δ v dU x j
        = embSlot 0 (W ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x j) +
          embSlot (slotT t j) (dS ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true *ᵥ figBchain δ W v x j) +
          Rb := by
      have hdec : figBstate δ v dU x j = embSlot 0 (figBchain δ W v x j) + Rb :=
        (add_sub_cancel _ _).symm
      rw [hdec, Matrix.mulVec_add, figGateT_act W dU dS j _ hact,
          figGateT_supported dU j Rb hRb_supp]
    have hora : figOracleP δ x *ᵥ (figGateT dU j *ᵥ figBstate δ v dU x j)
        = embSlot 0 (figOR δ x *ᵥ (W ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x j)) +
          embSlot (slotT t j) (dS ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true *ᵥ figBchain δ W v x j) +
          Rb := by
      rw [hgate, Matrix.mulVec_add, Matrix.mulVec_add, figOracleP_mulVec_main,
        figOracleP_mulVec_junk _ _ _ (slotT_ne_zero t j), figOracleP_mulVec_of_support]
      · rfl
      · intro p hp
        exact (hRb_supp p hp).1
    have hB : figBstate δ v dU x (j + 1)
        = figOracleP δ x *ᵥ (figGateT dU j *ᵥ figBstate δ v dU x j) := rfl
    have hC : figBchain δ W v x (j + 1)
        = figOR δ x *ᵥ (W ⟨(2 * t - j) % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x j) := rfl
    constructor
    · intro r
      rw [hB, hora, hC]
      rw [Pi.add_apply, Pi.add_apply, embSlot_apply, embSlot_apply, hRb0]
      rw [ite_eq_left rfl,
          ite_eq_right (show ((0, r) : Pos t R).1 ≠ slotT t j from fun h => slotT_ne_zero t j h.symm)]
      simp
    · intro i r hne
      rw [hB, hora] at hne
      rw [Pi.add_apply, Pi.add_apply] at hne
      by_cases h0 : i = 0
      · left
        exact congrArg Fin.val h0
      · right
        by_cases hk : i = slotT t j
        · exact ⟨j, by omega, by rw [hk, slotT_val (by omega)]⟩
        · have hne3 : Rb (i, r) ≠ 0 := by
            intro hz
            apply hne
            rw [hz]
            rw [embSlot_apply, embSlot_apply, ite_eq_right h0, ite_eq_right hk]
            simp
          have hpA : figBstate δ v dU x j (i, r) ≠ 0 := by
            intro hz
            apply hne3
            rw [hRb, Pi.sub_apply, hz]
            rw [embSlot_apply, ite_eq_right h0, sub_zero]
          obtain (h0' | ⟨j', hj1, hj2⟩) := hsupp i r hpA
          · exact absurd (Fin.ext h0') h0
          · exact ⟨j', by omega, hj2⟩

/-- Subtracting the embedded false-branch main chain leaves a state that vanishes in slot zero. -/
private theorem figAstate_sub_main (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0)) :
    ∀ r, (figAstate δ u dU x t - embSlot 0 (figAchain δ W u x t) : QState (Pos t R)) (0, r) = 0 := by
  intro r
  obtain ⟨hmain, _⟩ := figAstate_supp δ W u dU dS x hact t (le_refl t)
  rw [Pi.sub_apply, hmain r, embSlot_apply, ite_eq_left rfl, sub_self]

/-- Every nonzero coordinate remaining after subtracting the false-branch main chain lies in an
odd auxiliary slot used before round `t`. -/
private theorem figAstate_sub_supp (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0))
    (p : Pos t R)
    (hp : (figAstate δ u dU x t - embSlot 0 (figAchain δ W u x t) : QState (Pos t R)) p ≠ 0) :
    ∃ j', j' < t ∧ p.1.val = 2 * j' + 1 := by
  obtain ⟨hmain, hsupp⟩ := figAstate_supp δ W u dU dS x hact t (le_refl t)
  have hpA : figAstate δ u dU x t p ≠ 0 := by
    intro hz
    apply hp
    rw [Pi.sub_apply, hz]
    by_cases h0 : p.1 = 0
    · have hp0 : p = (0, p.2) := Prod.ext h0 rfl
      rw [hp0, embSlot_apply, ite_eq_left rfl]
      rw [hp0] at hz
      rw [hmain p.2] at hz
      rw [hz, sub_self]
    · rw [embSlot_apply, ite_eq_right h0, sub_zero]
  obtain (h0 | ⟨j', hj1, hj2⟩) := hsupp p.1 p.2 hpA
  · exfalso
    have hp0 : p = (0, p.2) := Prod.ext (Fin.ext h0) rfl
    rw [hp0] at hp
    exact hp (figAstate_sub_main δ W u dU dS x hact p.2)
  · exact ⟨j', hj1, hj2⟩

/-- Subtracting the embedded true-branch main chain leaves a state that vanishes in slot zero. -/
private theorem figBstate_sub_main (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0)) :
    ∀ r, (figBstate δ v dU x t - embSlot 0 (figBchain δ W v x t) : QState (Pos t R)) (0, r) = 0 := by
  intro r
  obtain ⟨hmain, _⟩ := figBstate_supp δ W v dU dS x hact t (le_refl t)
  rw [Pi.sub_apply, hmain r, embSlot_apply, ite_eq_left rfl, sub_self]

/-- Every nonzero coordinate remaining after subtracting the true-branch main chain lies in an
even auxiliary slot used before round `t`. -/
private theorem figBstate_sub_supp (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0))
    (p : Pos t R)
    (hp : (figBstate δ v dU x t - embSlot 0 (figBchain δ W v x t) : QState (Pos t R)) p ≠ 0) :
    ∃ j', j' < t ∧ p.1.val = 2 * j' + 2 := by
  obtain ⟨hmain, hsupp⟩ := figBstate_supp δ W v dU dS x hact t (le_refl t)
  have hpA : figBstate δ v dU x t p ≠ 0 := by
    intro hz
    apply hp
    rw [Pi.sub_apply, hz]
    by_cases h0 : p.1 = 0
    · have hp0 : p = (0, p.2) := Prod.ext h0 rfl
      rw [hp0, embSlot_apply, ite_eq_left rfl]
      rw [hp0] at hz
      rw [hmain p.2] at hz
      rw [hz, sub_self]
    · rw [embSlot_apply, ite_eq_right h0, sub_zero]
  obtain (h0 | ⟨j', hj1, hj2⟩) := hsupp p.1 p.2 hpA
  · exfalso
    have hp0 : p = (0, p.2) := Prod.ext (Fin.ext h0) rfl
    rw [hp0] at hp
    exact hp (figBstate_sub_main δ W v dU dS x hact p.2)
  · exact ⟨j', hj1, hj2⟩

set_option maxHeartbeats 1000000 in

/-- The pairing of the false-branch state with the middle-gate image of the true-branch state
reduces to the pairing of their main chains through the middle factor. -/
private theorem fig_pairing (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0)) :
    Qatlib.Foundations.PureStateMath.Inner (figAstate δ u dU x t) (figGateM dU *ᵥ figBstate δ v dU x t)
      = Qatlib.Foundations.PureStateMath.Inner (figAchain δ W u x t)
          (W ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x t) := by
  set Ra : QState (Pos t R) := figAstate δ u dU x t - embSlot 0 (figAchain δ W u x t) with hRa
  set Rb : QState (Pos t R) := figBstate δ v dU x t - embSlot 0 (figBchain δ W v x t) with hRb
  have hdecA : figAstate δ u dU x t = embSlot 0 (figAchain δ W u x t) + Ra :=
    (add_sub_cancel _ _).symm
  have hdecB : figBstate δ v dU x t = embSlot 0 (figBchain δ W v x t) + Rb :=
    (add_sub_cancel _ _).symm
  have hRa0 : ∀ r, Ra (0, r) = 0 := by
    intro r
    rw [hRa]
    exact figAstate_sub_main δ W u dU dS x hact r
  have hRb0 : ∀ r, Rb (0, r) = 0 := by
    intro r
    rw [hRb]
    exact figBstate_sub_main δ W v dU dS x hact r
  have hRa_supp : ∀ p, Ra p ≠ 0 → ∃ j', j' < t ∧ p.1.val = 2 * j' + 1 := by
    intro p hp
    rw [hRa] at hp
    exact figAstate_sub_supp δ W u dU dS x hact p hp
  have hRb_supp : ∀ p, Rb p ≠ 0 → ∃ j', j' < t ∧ p.1.val = 2 * j' + 2 := by
    intro p hp
    rw [hRb] at hp
    exact figBstate_sub_supp δ W v dU dS x hact p hp
  have hGM : figGateM dU *ᵥ figBstate δ v dU x t
      = embSlot 0 (W ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x t) +
        embSlot (slotM t) (dS ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true *ᵥ figBchain δ W v x t) +
        Rb := by
    rw [hdecB, Matrix.mulVec_add, figGateM_act W dU dS _ hact, figGateM_supported dU Rb]
    intro p hp
    obtain ⟨j', hj1, hj2⟩ := hRb_supp p hp
    constructor
    · intro h0
      have h1 : (p.1).val = 0 := congrArg Fin.val h0
      omega
    · intro hk
      have hv : p.1.val = (slotM t).val := congrArg Fin.val hk
      rw [slotM_val] at hv
      omega
  rw [hdecA, hGM]
  simp only [inner_add_left, inner_add_right]

  have e1 : Qatlib.Foundations.PureStateMath.Inner (embSlot 0 (figAchain δ W u x t))
      (embSlot 0 (W ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x t))
      = Qatlib.Foundations.PureStateMath.Inner (figAchain δ W u x t)
        (W ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x t) :=
    inner_embSlot (t := t) 0 _ _
  have e2 : Qatlib.Foundations.PureStateMath.Inner (embSlot 0 (figAchain δ W u x t))
      (embSlot (slotM t) (dS ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true *ᵥ figBchain δ W v x t))
      = 0 :=
    inner_embSlot_disjoint (t := t) (fun h => slotM_ne_zero t h.symm) _ _
  have e3 : Qatlib.Foundations.PureStateMath.Inner (embSlot 0 (figAchain δ W u x t)) Rb = 0 :=
    inner_eq_zero_of_support_disjoint _ _ fun p hp => by
      rw [embSlot_apply] at hp
      by_cases h0 : p.1 = 0
      · have hp0 : p = (0, p.2) := Prod.ext h0 rfl
        rw [hp0]
        exact hRb0 p.2
      · rw [ite_eq_right h0] at hp
        exact absurd rfl hp
  have e4 : Qatlib.Foundations.PureStateMath.Inner Ra (embSlot 0 (W ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ *ᵥ figBchain δ W v x t))
      = 0 :=
    inner_eq_zero_of_support_disjoint _ _ fun p hp => by
      obtain ⟨j', hj1, hj2⟩ := hRa_supp p hp
      rw [embSlot_apply]
      rw [ite_eq_right (by
        intro h0
        rw [h0] at hj2
        simp at hj2)]
  have e5 : Qatlib.Foundations.PureStateMath.Inner Ra (embSlot (slotM t) (dS ⟨t % (2 * t + 1), Nat.mod_lt _ (by omega)⟩ true *ᵥ figBchain δ W v x t))
      = 0 :=
    inner_eq_zero_of_support_disjoint _ _ fun p hp => by
      obtain ⟨j', hj1, hj2⟩ := hRa_supp p hp
      rw [embSlot_apply]
      rw [ite_eq_right (by
        intro hk
        have hv : p.1.val = (slotM t).val := congrArg Fin.val hk
        rw [slotM_val] at hv
        omega)]
  have e6 : Qatlib.Foundations.PureStateMath.Inner Ra Rb = 0 :=
    inner_eq_zero_of_support_disjoint _ _ fun p hp => by
      obtain ⟨j', hj1, hj2⟩ := hRa_supp p hp
      by_cases hpb : Rb p = 0
      · exact hpb
      · obtain ⟨j'', hj1', hj2'⟩ := hRb_supp p hpb
        omega
  rw [e1, e2, e3, e4, e5, e6]
  simp

/-- The circuit consisting of successive branch gates, each followed by one oracle query. -/
private noncomputable def figRounds : ℕ → Circuit (RegB t R)
  | 0 => []
  | j + 1 => figRounds j ++ [Step.gate (figRoundGate dU j), Step.query]

/-- The equal superposition of `u` in the false branch and `v` in the true branch, both in slot
zero. -/
private noncomputable def figInit : QState (RegB t R) :=
  brF ((Real.sqrt 2 : ℂ)⁻¹ • embSlot 0 u) + brT ((Real.sqrt 2 : ℂ)⁻¹ • embSlot 0 v)

/-- The `t`-round query circuit followed by the true-branch middle gate and a branch Hadamard
gate. -/
private noncomputable def figCircuit : Circuit (RegB t R) :=
  figRounds dU t ++ [Step.gate (branchMatrix 1 (figGateM dU)), Step.gate hadGate]

omit [Fintype R] in

/-- One additional round appends its branch gate and a single oracle query. -/
private theorem figRounds_succ (dU : Fin (2 * t + 1) → Bool → Matrix (R ⊕ R) (R ⊕ R) ℂ) (j : ℕ) :
    figRounds dU (j + 1) = figRounds dU j ++ [Step.gate (figRoundGate dU j), Step.query] := rfl

/-- The circuit of `j` rounds contains exactly `j` queries. -/
private theorem figRounds_queryCount (dU : Fin (2 * t + 1) → Bool → Matrix (R ⊕ R) (R ⊕ R) ℂ) (j : ℕ) :
    QueryCount (figRounds dU j) = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [figRounds_succ, queryCount_append, ih]
    rfl

/-- Every gate in the round circuit is unitary when all supplied dilation matrices are unitary. -/
private theorem figRounds_unitary
    (hU : ∀ m b, dU m b ∈ Matrix.unitaryGroup (R ⊕ R) ℂ) :
    ∀ (j : ℕ) (U : Matrix (RegB t R) (RegB t R) ℂ),
      Step.gate U ∈ figRounds dU j → U ∈ Matrix.unitaryGroup (RegB t R) ℂ := by
  intro j
  induction j with
  | zero =>
    intro U hU'
    simp [figRounds] at hU'
  | succ j ih =>
    intro U hU'
    rw [figRounds_succ, List.mem_append] at hU'
    rcases hU' with hU' | hU'
    · exact ih U hU'
    · have h2 : Step.gate U = Step.gate (figRoundGate dU j) ∨ Step.gate U = Step.query := by
        simpa using hU'
      rcases h2 with h2 | h2
      · rw [Step.gate.injEq] at h2
        rw [h2]
        exact branchMatrix_unitary _ _
          (liftP_unitary _ _ _ (hU _ false)) (liftP_unitary _ _ _ (hU _ true))
      · cases h2

/-- The complete constructed circuit is unitary when all supplied dilation matrices are unitary. -/
private theorem figCircuit_unitary
    (hU : ∀ m b, dU m b ∈ Matrix.unitaryGroup (R ⊕ R) ℂ) :
    IsUnitaryCircuit (figCircuit (t := t) dU) := by
  intro U hU'
  rw [figCircuit, List.mem_append] at hU'
  rcases hU' with hU' | hU'
  · exact figRounds_unitary dU hU t U hU'
  · have h2 : Step.gate U = Step.gate (branchMatrix 1 (figGateM dU)) ∨ Step.gate U = Step.gate hadGate := by
      simpa using hU'
    rcases h2 with h2 | h2
    · rw [Step.gate.injEq] at h2
      rw [h2]
      exact branchMatrix_unitary _ _ (one_mem _) (liftP_unitary _ _ _ (hU _ true))
    · rw [Step.gate.injEq] at h2
      rw [h2]
      exact hadGate_unitary

/-- The complete constructed circuit contains exactly `t` queries. -/
private theorem figCircuit_queryCount (dU : Fin (2 * t + 1) → Bool → Matrix (R ⊕ R) (R ⊕ R) ℂ) :
    QueryCount (figCircuit (t := t) dU) = t := by
  rw [figCircuit, queryCount_append, figRounds_queryCount]
  rfl

/-- The initial equal-branch superposition is normalized when both input states are normalized. -/
private theorem figInit_normalized (hu : Normalized u) (hv : Normalized v) :
    Normalized (figInit (t := t) u v) := by
  show (∑ q : RegB t R, ‖figInit u v q‖ ^ 2) = 1
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have h1 : ∀ p : Pos t R, figInit u v (false, p) = (Real.sqrt 2 : ℂ)⁻¹ * embSlot 0 u p := by
    intro p
    simp [figInit, brF, brT, Pi.smul_apply, smul_eq_mul]
  have h2 : ∀ p : Pos t R, figInit u v (true, p) = (Real.sqrt 2 : ℂ)⁻¹ * embSlot 0 v p := by
    intro p
    simp [figInit, brF, brT, Pi.smul_apply, smul_eq_mul]
  have eT : (∑ p : Pos t R, ‖figInit u v (true, p)‖ ^ 2)
      = ∑ p : Pos t R, ‖(Real.sqrt 2 : ℂ)⁻¹ * embSlot 0 v p‖ ^ 2 :=
    Finset.sum_congr rfl fun p _ => by rw [h2 p]
  have eF : (∑ p : Pos t R, ‖figInit u v (false, p)‖ ^ 2)
      = ∑ p : Pos t R, ‖(Real.sqrt 2 : ℂ)⁻¹ * embSlot 0 u p‖ ^ 2 :=
    Finset.sum_congr rfl fun p _ => by rw [h1 p]
  rw [eT, eF]
  have hhalf : ∀ (w : QState R), Normalized w →
      (∑ p : Pos t R, ‖(Real.sqrt 2 : ℂ)⁻¹ * embSlot 0 w p‖ ^ 2) = (2 : ℝ)⁻¹ := by
    intro w hw
    rw [Finset.sum_congr rfl (fun p _ => by rw [norm_mul, mul_pow])]
    rw [← Finset.mul_sum]
    have h3 : (∑ p : Pos t R, ‖embSlot 0 w p‖ ^ 2) = ∑ r : R, ‖w r‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single 0]
      · exact Finset.sum_congr rfl fun r _ => by rw [embSlot_apply, ite_eq_left rfl]
      · intro i _ hi
        rw [Finset.sum_eq_zero]
        intro r _
        rw [embSlot_apply, ite_eq_right hi]
        simp
      · intro hmem
        exact absurd (Finset.mem_univ 0) hmem
    rw [h3, hw, norm_inv]
    rw [show ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 from by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hhalf v hv, hhalf u hu]
  norm_num

/-- The difference between the squared moduli of `a + b` and `a - b` is four times the real part
of `conj a * b`. -/
private theorem normSq_add_sub (a b : ℂ) :
    ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * ((starRingEnd ℂ) a * b).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  rw [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  rw [starRingEnd_apply]
  rw [Complex.mul_re]
  rw [show (star a).re = a.re from by simp, show (star a).im = -a.im from by simp]
  ring

/-- The sign bias of the two-branch interference state equals the real part of the inner product
of its two component states. -/
private theorem fig_signBias_form (A B : QState (Pos t R)) :
    signBias (fun q => ((2 : ℂ))⁻¹ * (A q.2 + (if q.1 then -1 else 1) * B q.2))
        ({false} ×ˢ Finset.univ)
      = (Qatlib.Foundations.PureStateMath.Inner A B).re := by
  have hE : (({false} ×ˢ Finset.univ : Finset (RegB t R))ᶜ) = {true} ×ˢ Finset.univ := by
    ext q
    simp only [Finset.mem_compl, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_singleton]
    cases hq : q.1 <;> simp
  show MeasureProb (fun q => ((2 : ℂ))⁻¹ * (A q.2 + (if q.1 then -1 else 1) * B q.2))
      ({false} ×ˢ Finset.univ)
      - MeasureProb (fun q => ((2 : ℂ))⁻¹ * (A q.2 + (if q.1 then -1 else 1) * B q.2))
        (({false} ×ˢ Finset.univ : Finset (RegB t R))ᶜ) = _
  rw [hE]
  have h1 : MeasureProb (fun q => ((2 : ℂ))⁻¹ * (A q.2 + (if q.1 then -1 else 1) * B q.2))
        ({false} ×ˢ Finset.univ)
      = (4 : ℝ)⁻¹ * ∑ p : Pos t R, ‖A p + B p‖ ^ 2 := by
    show (∑ i ∈ ({false} ×ˢ Finset.univ),
        ‖((2 : ℂ))⁻¹ * (A i.2 + (if i.1 then -1 else 1) * B i.2)‖ ^ 2) = _
    rw [Finset.sum_product, Finset.sum_singleton]
    rw [Finset.sum_congr rfl (fun p _ => by
      show ‖((2 : ℂ))⁻¹ * (A p + (if (false, p).1 then -1 else 1) * B p)‖ ^ 2
          = (4 : ℝ)⁻¹ * ‖A p + B p‖ ^ 2
      rw [ite_eq_right (by simp)]
      rw [one_mul, norm_mul, mul_pow]
      congr 1
      rw [norm_inv]
      rw [show ‖(2 : ℂ)‖ = 2 from by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]]
      rw [inv_pow]
      norm_num)]
    rw [Finset.mul_sum]
  have h2 : MeasureProb (fun q => ((2 : ℂ))⁻¹ * (A q.2 + (if q.1 then -1 else 1) * B q.2))
        ({true} ×ˢ Finset.univ)
      = (4 : ℝ)⁻¹ * ∑ p : Pos t R, ‖A p - B p‖ ^ 2 := by
    show (∑ i ∈ ({true} ×ˢ Finset.univ),
        ‖((2 : ℂ))⁻¹ * (A i.2 + (if i.1 then -1 else 1) * B i.2)‖ ^ 2) = _
    rw [Finset.sum_product, Finset.sum_singleton]
    rw [Finset.sum_congr rfl (fun p _ => by
      show ‖((2 : ℂ))⁻¹ * (A p + (if (true, p).1 then -1 else 1) * B p)‖ ^ 2
          = (4 : ℝ)⁻¹ * ‖A p - B p‖ ^ 2
      rw [ite_eq_left rfl]
      rw [show A p + -1 * B p = A p - B p from by ring]
      rw [norm_mul, mul_pow]
      congr 1
      rw [norm_inv]
      rw [show ‖(2 : ℂ)‖ = 2 from by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]]
      rw [inv_pow]
      norm_num)]
    rw [Finset.mul_sum]
  rw [h1, h2]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun p _ => normSq_add_sub (A p) (B p))]
  rw [← Finset.mul_sum]
  rw [← Complex.re_sum]
  rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
  rw [inner_apply]

set_option maxHeartbeats 1000000 in

/-- Running the round circuit yields the equally weighted false-branch and true-branch states
defined by the round recursions. -/
private theorem figRun (x : Fin n → Bool) (j : ℕ) :
    Run (cbPhaseOracle (figLabel δ) x) (figRounds dU j) (figInit u v)
      = brF ((Real.sqrt 2 : ℂ)⁻¹ • figAstate δ u dU x j) +
        brT ((Real.sqrt 2 : ℂ)⁻¹ • figBstate δ v dU x j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [figRounds_succ, run_append, ih]
    show Run (cbPhaseOracle (figLabel δ) x) [Step.gate (figRoundGate dU j), Step.query]
        (brF ((Real.sqrt 2 : ℂ)⁻¹ • figAstate δ u dU x j) +
         brT ((Real.sqrt 2 : ℂ)⁻¹ • figBstate δ v dU x j)) = _
    rw [run_gate, run_query, run_nil]
    show cbPhaseOracle (figLabel δ) x *ᵥ (figRoundGate dU j *ᵥ
        (brF ((Real.sqrt 2 : ℂ)⁻¹ • figAstate δ u dU x j) +
         brT ((Real.sqrt 2 : ℂ)⁻¹ • figBstate δ v dU x j))) = _
    rw [figOracle_eq]
    rw [show figRoundGate dU j = branchMatrix (figGateF dU j) (figGateT dU j) from rfl]
    rw [Matrix.mulVec_add, branchMatrix_mulVec_brF, branchMatrix_mulVec_brT]
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    rw [Matrix.mulVec_add, branchMatrix_mulVec_brF, branchMatrix_mulVec_brT]
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    rfl

set_option maxHeartbeats 1000000 in

/-- Under the dilation action hypothesis, the final sign bias is the real part of the
factorization sandwich paired with `u` and `v`. -/
private theorem fig_correct (x : Fin n → Bool)
    (hact : ∀ m b x0, dU m b *ᵥ Sum.elim x0 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x0) (dS m b *ᵥ x0)) :
    signBias (Run (cbPhaseOracle (figLabel δ) x) (figCircuit dU) (figInit u v))
        ({false} ×ˢ Finset.univ)
      = (Qatlib.Foundations.PureStateMath.Inner u (cbSandwichMatrix W δ (fun _ => signVecC x) *ᵥ v)).re := by
  have hrun : Run (cbPhaseOracle (figLabel δ) x) (figCircuit dU) (figInit u v)
      = hadGate *ᵥ (branchMatrix 1 (figGateM dU) *ᵥ
          (brF ((Real.sqrt 2 : ℂ)⁻¹ • figAstate δ u dU x t) +
           brT ((Real.sqrt 2 : ℂ)⁻¹ • figBstate δ v dU x t))) := by
    rw [figCircuit, run_append, figRun δ u v dU x t]
    rfl
  rw [hrun]
  rw [Matrix.mulVec_add, branchMatrix_mulVec_brF, branchMatrix_mulVec_brT]
  rw [Matrix.one_mulVec]
  rw [Matrix.mulVec_smul]
  rw [hadGate_mulVec]
  have hpsi : (fun q : RegB t R => Qatlib.Foundations.PureStateMath.Hadamard q.1 false *
        ((Real.sqrt 2 : ℂ)⁻¹ • figAstate δ u dU x t) q.2 +
        Qatlib.Foundations.PureStateMath.Hadamard q.1 true *
        ((Real.sqrt 2 : ℂ)⁻¹ • (figGateM dU *ᵥ figBstate δ v dU x t)) q.2)
      = fun q => ((2 : ℂ))⁻¹ * (figAstate δ u dU x t q.2 +
          (if q.1 then -1 else 1) * (figGateM dU *ᵥ figBstate δ v dU x t) q.2) := by
    funext q
    rw [hadamard_apply_false, hadamard_entry_true]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hc : ∀ X : ℂ, (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ * X) = ((2 : ℂ))⁻¹ * X :=
      fun X => by
        rw [← mul_assoc, inv_sqrt2_mul_self]
    rw [hc]
    rw [show ((if q.1 then -1 else 1) * (Real.sqrt 2 : ℂ)⁻¹) *
          ((Real.sqrt 2 : ℂ)⁻¹ * (figGateM dU *ᵥ figBstate δ v dU x t) q.2)
        = (if q.1 then -1 else 1) * (((2 : ℂ))⁻¹ * (figGateM dU *ᵥ figBstate δ v dU x t) q.2) from by
      rw [show ((if q.1 then -1 else 1) * (Real.sqrt 2 : ℂ)⁻¹) *
            ((Real.sqrt 2 : ℂ)⁻¹ * (figGateM dU *ᵥ figBstate δ v dU x t) q.2)
          = (if q.1 then -1 else 1) * ((Real.sqrt 2 : ℂ)⁻¹ *
              ((Real.sqrt 2 : ℂ)⁻¹ * (figGateM dU *ᵥ figBstate δ v dU x t) q.2)) from by ring]
      rw [hc]]
    ring
  rw [hpsi]
  rw [fig_signBias_form]
  rw [fig_pairing δ W u v dU dS x hact]
  rw [figAchain_inner δ W u x t (le_refl t), figBchain_eq δ W v x t (le_refl t)]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [fig_sandwich_matrix δ W x]

/-- A real tensor of order `2 * t` with a completely bounded factorization has a sign algorithm
realizing its tensor bias with `t` queries. -/
theorem lemma3_3FactorizationToAlgorithm : Lemma3_3FactorizationToAlgorithm := by
  intro n t T hfac
  obtain ⟨R, hRfin, hRdec, δ, u, v, W, hu, hv, hW, hcert⟩ := hfac
  classical
  let := hRfin
  let := hRdec
  have hdil : ∀ m : Fin (2 * t + 1), ∀ b : Bool,
      ∃ (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) (S : Matrix R R ℂ),
        U ∈ Matrix.unitaryGroup (R ⊕ R) ℂ ∧
          ∀ x : QState R, U *ᵥ Sum.elim x 0
            = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x) (S *ᵥ x) := by
    intro m b
    cases b
    · exact exists_unitary_dilation (W m)ᴴ (by
        rw [← Matrix.star_eq_conjTranspose, norm_star]
        exact hW m)
    · exact exists_unitary_dilation (W m) (hW m)
  choose dU dS hdil using hdil
  have hU : ∀ m b, dU m b ∈ Matrix.unitaryGroup (R ⊕ R) ℂ := fun m b => (hdil m b).1
  have hact : ∀ m b x, dU m b *ᵥ Sum.elim x 0
      = Sum.elim ((match b with | false => (W m)ᴴ | true => W m) *ᵥ x) (dS m b *ᵥ x) :=
    fun m b => (hdil m b).2
  refine ⟨RegB t R, inferInstance, inferInstance, figLabel δ, figCircuit dU, figInit u v,
    {false} ×ˢ Finset.univ, figCircuit_unitary dU hU, figInit_normalized u v hu hv, ?_, ?_⟩
  · rw [figCircuit_queryCount]
  · intro x
    rw [fig_correct δ W u v dU dS x hact]
    show (cbSandwich W δ u v (fun _ => signVecC x)).re = tensorBias T x
    rw [← hcert (fun _ => signVecC x)]
    rfl

end Assembly

end Qatlib.Concepts.QueryComplexity.NormObstruction
