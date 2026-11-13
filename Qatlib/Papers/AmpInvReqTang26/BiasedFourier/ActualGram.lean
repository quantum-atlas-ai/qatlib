/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.Fourier
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Qatlib.Foundations.MatrixAlgebra.FrameProject.AnalysisBound
import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.ActualOverlap

/-!
# Constructing the biased Fourier basis

Applies Gram–Schmidt to the weighted Fourier columns to define `biasedBasis` and their
coordinates `transformedColumn`. For `q > 1` and `0 < eps < 1/2`, lower synthesis bounds give
independence and prefix-span control, yielding a unitary transform with triangular support and
squared diagonal mass at least `1 - 4 * eps^2`. See [TangWright2025].

## Main statements

* `actual_prefix_projection`: the mass in earlier basis coordinates is at most `2 * eps^2 / (1 -
  eps)`.
* `actual_lemma33`: the biased Fourier unitary exists with the stated support and mass bounds.
* `actual_lemma37`: prefix projection mass is controlled by weighted-column overlaps.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The weighted Fourier column `fourierUnitVec eps q k` viewed as an element of complex
Euclidean space. -/
def weightedColumn (eps : ℝ) (q : ℕ) (k : Fin q) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 (fourierUnitVec eps q k)

/-- The orthonormal basis obtained by the Gram–Schmidt orthonormal-basis construction on the
weighted Fourier columns. -/
def biasedBasis (eps : ℝ) (q : ℕ) : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q)) :=
  InnerProductSpace.gramSchmidtOrthonormalBasis (by simp) (weightedColumn eps q)

/-- The family `biasedBasis eps q` is orthonormal. -/
theorem biasedBasis_orthonormal (eps : ℝ) (q : ℕ) :
    Orthonormal ℂ (biasedBasis eps q) := (biasedBasis eps q).orthonormal

/-- A basis vector with index `j > i` is orthogonal to the weighted Fourier column with index
`i`. -/
theorem biasedBasis_upper_zero (eps : ℝ) (q : ℕ) (i j : Fin q) (hij : i < j) :
    inner ℂ (biasedBasis eps q j) (weightedColumn eps q i) = 0 :=
  InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular (by simp)
    (weightedColumn eps q) hij

/-- Each weighted Fourier column equals the sum of its inner-product coordinates in
`biasedBasis` times the corresponding basis vectors. -/
theorem weightedColumn_expansion (eps : ℝ) (q : ℕ) (k : Fin q) :
    ∑ i, inner ℂ (biasedBasis eps q i) (weightedColumn eps q k) • biasedBasis eps q i =
      weightedColumn eps q k := (biasedBasis eps q).sum_repr' _

/-- The inner product with `weightedColumn eps q k` is the coordinate sum against
`fourierUnitVec eps q k`. -/
theorem weightedColumn_inner (eps : ℝ) (q : ℕ) (k : Fin q) (u : EuclideanSpace ℂ (Fin q)) :
    inner ℂ u (weightedColumn eps q k) =
      ∑ x, star (u x) * fourierUnitVec eps q k x := by
  simp [PiLp.inner_apply, RCLike.inner_apply, weightedColumn, mul_comm]

/-- For `q > 1` and `0 < eps < 1/2`, synthesis by the weighted columns has squared norm at least
`(1 - eps)` times the squared coefficient norm. -/
theorem weightedColumn_synthesis_bound (eps : ℝ) (q : ℕ) (hq : 1 < q)
    (he0 : 0 < eps) (he1 : eps < 1/2) (a : Fin q → ℂ) :
    (1-eps) * (∑ i, ‖a i‖^2) ≤ ‖∑ i, a i • weightedColumn eps q i‖^2 := by
  have h := (lemma36_singular_values q hq eps he0 he1 a).1
  simpa [EuclideanSpace.norm_sq_eq, weightedColumn, PiLp.smul_apply,
    Ftilde, fourierUnitVec, mul_comm] using! h

/-- For `q > 1` and `0 < eps < 1/2`, the weighted Fourier columns are linearly independent. -/
theorem weightedColumn_independent (eps : ℝ) (q : ℕ) (hq : 1 < q)
    (he0 : 0 < eps) (he1 : eps < 1/2) : LinearIndependent ℂ (weightedColumn eps q) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := weightedColumn_synthesis_bound eps q hq he0 he1 a
  rw [ha, norm_zero, zero_pow (by omega)] at h
  have hsum : ∑ j, ‖a j‖^2 = 0 := by
    have hnon : 0 ≤ ∑ j, ‖a j‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
    sq_nonneg ‖a j‖)).mp hsum i (Finset.mem_univ i)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

/-- For `q > 1` and `0 < eps < 1/2`, each basis vector with index less than `k` lies in the span
of the weighted columns with indices less than `k`. -/
theorem biasedBasis_mem_prefix (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (k i : Fin q) (hik : i<k) :
    biasedBasis eps q i ∈ Submodule.span ℂ
      (Set.range (fun j : {j : Fin q // j<k} => weightedColumn eps q j)) := by
  have hLi := weightedColumn_independent eps q hq he0 he1
  have hn : InnerProductSpace.gramSchmidtNormed ℂ (weightedColumn eps q) i ≠ 0 := by
    intro hz
    have h := InnerProductSpace.gramSchmidtNormed_unit_length i hLi
    rw [hz, norm_zero] at h
    norm_num at h
  rw [biasedBasis, InnerProductSpace.gramSchmidtOrthonormalBasis_apply (by simp) hn,
    InnerProductSpace.gramSchmidtNormed]
  apply Submodule.smul_mem
  apply Submodule.span_mono _ (InnerProductSpace.gramSchmidt_mem_span ℂ
    (weightedColumn eps q) (le_refl i))
  rintro x ⟨j,hj,rfl⟩
  exact ⟨⟨j,lt_of_le_of_lt hj hik⟩,rfl⟩

/-- A sum over the subtype satisfying `p` equals the sum over the full finite type with an
indicator for `p`. -/
private theorem sum_subtype_indicator {J : Type*} [Fintype J]
    (p : J → Prop) [DecidablePred p] (f : J → ℝ) :
    (∑ j : {j // p j}, f j) = ∑ j, if p j then f j else 0 := by
  have h1 (j : {j // p j}) : (if p j then f j else 0) = f j := if_pos j.property
  have h0 (j : {j // ¬p j}) : (if p j then f j else 0) = 0 := if_neg j.property
  have hs := Fintype.sum_subtype_add_sum_subtype p (fun j => if p j then f j else 0)
  simpa only [h1,h0,Finset.sum_const_zero,add_zero] using! hs

/-- For `q > 1` and `0 < eps < 1/2`, the squared projection mass of column `k` onto earlier
basis vectors is at most `2 * eps^2 / (1 - eps)` [Tang and Wright, Lemma
3.8][TangWright2025]. -/
theorem actual_prefix_projection (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (k : Fin q) :
    ∑ i : Fin q, (if i<k then
      ‖inner ℂ (biasedBasis eps q i) (weightedColumn eps q k)‖^2 else 0) ≤
      2*eps^2/(1-eps) := by
  let p : Fin q → Prop := fun j => j<k
  have hsyn := Qatlib.Foundations.MatrixAlgebra.FrameProject.synthesis_bound_subtype
    (weightedColumn eps q) (1-eps) (weightedColumn_synthesis_bound eps q hq he0 he1) p
  have hon : Orthonormal ℂ (fun i : {i // p i} => biasedBasis eps q i) :=
    (biasedBasis eps q).orthonormal.comp _ Subtype.coe_injective
  have hspan (i : {i // p i}) : biasedBasis eps q i ∈ Submodule.span ℂ
      (Set.range (fun j : {j // p j} => weightedColumn eps q j)) :=
    biasedBasis_mem_prefix eps q hq he0 he1 k i i.property
  have hb := Qatlib.Foundations.MatrixAlgebra.FrameProject.orthonormal_analysis_bound
    (fun j : {j // p j} => weightedColumn eps q j) (1-eps) (by linarith) hsyn
    (fun i : {i // p i} => biasedBasis eps q i) hon hspan (weightedColumn eps q k)
  rw [sum_subtype_indicator p (fun i => ‖inner ℂ (biasedBasis eps q i) (weightedColumn eps q k)‖^2),
    sum_subtype_indicator p (fun i => ‖inner ℂ (weightedColumn eps q i) (weightedColumn eps q k)‖^2)] at hb
  have hcomp : (∑ j : Fin q, if j<k then
      ‖inner ℂ (weightedColumn eps q j) (weightedColumn eps q k)‖^2 else 0) ≤
      ∑ j : Fin q, if j≠k then
        ‖inner ℂ (weightedColumn eps q j) (weightedColumn eps q k)‖^2 else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j<k
    · simp [hj,ne_of_lt hj]
    · simp only [if_neg hj]
      split_ifs <;> positivity
  have hoff := actual_offdiag_budget q hq eps he0.le (by linarith) k
  have hinner (j : Fin q) : inner ℂ (weightedColumn eps q j) (weightedColumn eps q k) =
      ∑ g, star (fourierUnitVec eps q j g) * fourierUnitVec eps q k g := by
    rw [weightedColumn_inner]
    rfl
  have hoff' : (∑ j : Fin q, if j≠k then
      ‖inner ℂ (weightedColumn eps q j) (weightedColumn eps q k)‖^2 else 0) ≤ 2*eps^2 := by
    simpa only [hinner] using! hoff
  dsimp only [p] at hb
  have hb' : (1-eps) * (∑ i : Fin q, if i<k then
      ‖inner ℂ (biasedBasis eps q i) (weightedColumn eps q k)‖^2 else 0) ≤ 2*eps^2 := by
    exact hb.trans (hcomp.trans hoff')
  exact (le_div_iff₀ (by linarith : 0<1-eps)).mpr (by nlinarith [hb'])

/-- For `q > 1` and `0 < eps < 1/2`, there is a unitary sending each weighted Fourier column `k`
to a normalized vector supported on indices at most `k`, with squared mass at `k` at least
`1 - 4 * eps^2` [Tang and Wright, Lemma 3.3][TangWright2025]. -/
theorem actual_lemma33 (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) :
    ∃ F : Matrix (Fin q) (Fin q) ℂ, Fᴴ*F=1 ∧
      ∀ k : Fin q, ∃ alpha : Fin q → ℂ,
        (∀ l : Fin q, (k:ℕ)<(l:ℕ) → alpha l=0) ∧
        (∑ l, ‖alpha l‖^2=1) ∧ (1-4*eps^2 ≤ ‖alpha k‖^2) ∧
        (∀ g, (F *ᵥ fourierUnitVec eps q k) g=alpha g) := by
  let u : Fin q → Fin q → ℂ := fun i x => biasedBasis eps q i x
  apply lemma33_biased_fourier_unitary q hq eps he0 he1 u
  · intro i j
    have h := orthonormal_iff_ite.mp (biasedBasis eps q).orthonormal i j
    simpa [PiLp.inner_apply, RCLike.inner_apply, u, mul_comm] using! h
  · intro k x
    have h := congrArg (fun v : EuclideanSpace ℂ (Fin q) => v x)
      (weightedColumn_expansion eps q k).symm
    simp only [weightedColumn_inner] at h
    simpa [weightedColumn, u] using! h
  · intro k i hki
    have h := biasedBasis_upper_zero eps q k i hki
    simpa only [weightedColumn_inner] using! h
  · intro k
    simpa only [weightedColumn_inner] using! actual_prefix_projection eps q hq he0 he1 k

/-- The coordinate at `y` of weighted column `k` in the orthonormal basis `biasedBasis eps q`. -/
def transformedColumn (eps : ℝ) (q : ℕ) (k y : Fin q) : ℂ :=
  (biasedBasis eps q).repr (weightedColumn eps q k) y

/-- The transformed-column coordinate equals the inner product with the corresponding
biased-basis vector. -/
theorem transformedColumn_inner (eps : ℝ) (q : ℕ) (k y : Fin q) :
    transformedColumn eps q k y = inner ℂ (biasedBasis eps q y) (weightedColumn eps q k) :=
  (biasedBasis eps q).repr_apply_apply _ _

/-- The transformed column `k` vanishes at every index `y > k`. -/
theorem transformedColumn_upper (eps : ℝ) (q : ℕ) (k y : Fin q) (hky : k<y) :
    transformedColumn eps q k y=0 := by
  rw [transformedColumn_inner]
  exact biasedBasis_upper_zero eps q k y hky

/-- For `q > 1` and `0 < eps < 1/2`, each transformed column has total squared mass one. -/
theorem transformedColumn_normalized (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (k : Fin q) :
    ∑y,‖transformedColumn eps q k y‖^2=1 := by
  calc
    _ = ‖(biasedBasis eps q).repr (weightedColumn eps q k)‖^2 :=
      (EuclideanSpace.norm_sq_eq _).symm
    _ = ‖weightedColumn eps q k‖^2 := by rw [(biasedBasis eps q).repr.norm_map]
    _ = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact actual_column_norm q hq eps he0.le (by linarith) k

/-- For `q > 1` and `0 < eps < 1/2`, transformed column `k` has squared mass at least `1 - 4 *
eps^2` at index `k`. -/
theorem transformedColumn_diagonal (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (k : Fin q) :
    1-4*eps^2 ≤ ‖transformedColumn eps q k k‖^2 := by
  have hsum := transformedColumn_normalized eps q hq he0 he1 k
  have hsplit : (∑y,‖transformedColumn eps q k y‖^2) =
      (∑y, if y<k then ‖transformedColumn eps q k y‖^2 else 0) +
        ‖transformedColumn eps q k k‖^2 := by
    have hp (y : Fin q) : ‖transformedColumn eps q k y‖^2 =
        (if y<k then ‖transformedColumn eps q k y‖^2 else 0) +
          (if y=k then ‖transformedColumn eps q k k‖^2 else 0) := by
      rcases lt_trichotomy y k with hy | hy | hy
      · simp [hy,ne_of_lt hy]
      · subst y; simp
      · rw [transformedColumn_upper eps q k y hy]
        simp [not_lt_of_gt hy,ne_of_gt hy]
    rw [Finset.sum_congr rfl (fun y _ => hp y),Finset.sum_add_distrib]
    simp
  have hp := actual_prefix_projection eps q hq he0 he1 k
  simp only [← transformedColumn_inner] at hp
  rw [hsplit] at hsum
  have hratio : 2*eps^2/(1-eps) ≤ 4*eps^2 := by
    apply (div_le_iff₀ (by linarith : 0<1-eps)).mpr
    nlinarith [sq_nonneg eps]
  linarith [hp.trans hratio]

/-- The transformed columns and the original weighted Fourier columns have the same pairwise
inner products. -/
theorem transformedColumn_gram (eps : ℝ) (q : ℕ) (j k : Fin q) :
    (∑y, star (transformedColumn eps q j y) * transformedColumn eps q k y) =
      ∑g, star (fourierUnitVec eps q j g) * fourierUnitVec eps q k g := by
  have h := (biasedBasis eps q).repr.inner_map_map (weightedColumn eps q j) (weightedColumn eps q k)
  simpa only [PiLp.inner_apply,RCLike.inner_apply',transformedColumn,weightedColumn] using! h

/-- For `q > 1` and `0 < eps < 1/2`, a biased-basis vector with natural index below `r` lies in
the span of the weighted columns with natural indices below `r`. -/
theorem biasedBasis_mem_cutoff (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (r : ℕ) (i : Fin q) (hir : (i:ℕ)<r) :
    biasedBasis eps q i ∈ Submodule.span ℂ
      (Set.range (fun j : {j : Fin q // (j:ℕ)<r} => weightedColumn eps q j)) := by
  have hLi := weightedColumn_independent eps q hq he0 he1
  have hn : InnerProductSpace.gramSchmidtNormed ℂ (weightedColumn eps q) i ≠ 0 := by
    intro hz
    have h := InnerProductSpace.gramSchmidtNormed_unit_length i hLi
    rw [hz,norm_zero] at h
    norm_num at h
  rw [biasedBasis,InnerProductSpace.gramSchmidtOrthonormalBasis_apply (by simp) hn,
    InnerProductSpace.gramSchmidtNormed]
  apply Submodule.smul_mem
  apply Submodule.span_mono _ (InnerProductSpace.gramSchmidt_mem_span ℂ
    (weightedColumn eps q) (le_refl i))
  rintro x ⟨j,hj,rfl⟩
  exact ⟨⟨j,lt_of_le_of_lt hj hir⟩,rfl⟩

/-- For `q > 1` and `0 < eps < 1/2`, the squared projection mass onto biased-basis indices below
`r` is at most `(1 - eps)⁻¹` times the sum of squared overlaps with weighted columns below
`r` [Tang and Wright, Lemma 3.7][TangWright2025]. -/
theorem actual_lemma37 (eps : ℝ) (q : ℕ) (hq : 1<q) (he0 : 0<eps) (he1 : eps<1/2)
    (r : ℕ) (v : EuclideanSpace ℂ (Fin q)) :
    (∑i : Fin q,if (i:ℕ)<r then ‖inner ℂ (biasedBasis eps q i) v‖^2 else 0) ≤
      (1-eps)⁻¹*(∑j : Fin q,if (j:ℕ)<r then ‖inner ℂ (weightedColumn eps q j) v‖^2 else 0) := by
  let p : Fin q → Prop := fun j => (j:ℕ)<r
  have hsyn := Qatlib.Foundations.MatrixAlgebra.FrameProject.synthesis_bound_subtype
    (weightedColumn eps q) (1-eps) (weightedColumn_synthesis_bound eps q hq he0 he1) p
  have hon : Orthonormal ℂ (fun i : {i // p i} => biasedBasis eps q i) :=
    (biasedBasis eps q).orthonormal.comp _ Subtype.coe_injective
  have hspan (i : {i // p i}) : biasedBasis eps q i ∈ Submodule.span ℂ
      (Set.range (fun j : {j // p j} => weightedColumn eps q j)) :=
    biasedBasis_mem_cutoff eps q hq he0 he1 r i i.property
  have hb := Qatlib.Foundations.MatrixAlgebra.FrameProject.orthonormal_analysis_bound
    (fun j : {j // p j} => weightedColumn eps q j) (1-eps) (by linarith) hsyn
    (fun i : {i // p i} => biasedBasis eps q i) hon hspan v
  rw [sum_subtype_indicator p (fun i => ‖inner ℂ (biasedBasis eps q i) v‖^2),
    sum_subtype_indicator p (fun i => ‖inner ℂ (weightedColumn eps q i) v‖^2)] at hb
  dsimp only [p] at hb
  rw [mul_comm ((1-eps)⁻¹),← div_eq_mul_inv]
  exact (le_div_iff₀ (by linarith : 0<1-eps)).mpr (by nlinarith [hb])

end Qatlib.Papers.AmpInvReqTang26.BiasedFourier
