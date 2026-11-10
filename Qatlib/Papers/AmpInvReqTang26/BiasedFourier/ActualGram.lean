/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.Fourier
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Qatlib.Foundations.MatrixAlgebra.FrameProject.AnalysisBound
import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.ActualOverlap
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Papers.AmpInvReqTang26.AccessModel
set_option warningAsError false

def weightedColumn (eps : ℝ) (q : ℕ) (k : Fin q) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 (fourierUnitVec eps q k)

def biasedBasis (eps : ℝ) (q : ℕ) : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q)) :=
  InnerProductSpace.gramSchmidtOrthonormalBasis (by simp) (weightedColumn eps q)

theorem biasedBasis_orthonormal (eps : ℝ) (q : ℕ) :
    Orthonormal ℂ (biasedBasis eps q) := (biasedBasis eps q).orthonormal

theorem biasedBasis_upper_zero (eps : ℝ) (q : ℕ) (i j : Fin q) (hij : i < j) :
    inner ℂ (biasedBasis eps q j) (weightedColumn eps q i) = 0 :=
  InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular (by simp)
    (weightedColumn eps q) hij

theorem weightedColumn_expansion (eps : ℝ) (q : ℕ) (k : Fin q) :
    ∑ i, inner ℂ (biasedBasis eps q i) (weightedColumn eps q k) • biasedBasis eps q i =
      weightedColumn eps q k := (biasedBasis eps q).sum_repr' _

theorem weightedColumn_inner (eps : ℝ) (q : ℕ) (k : Fin q) (u : EuclideanSpace ℂ (Fin q)) :
    inner ℂ u (weightedColumn eps q k) =
      ∑ x, star (u x) * fourierUnitVec eps q k x := by
  simp [PiLp.inner_apply, RCLike.inner_apply, weightedColumn, mul_comm]

theorem weightedColumn_synthesis_bound (eps : ℝ) (q : ℕ) (hq : 1 < q)
    (he0 : 0 < eps) (he1 : eps < 1/2) (a : Fin q → ℂ) :
    (1-eps) * (∑ i, ‖a i‖^2) ≤ ‖∑ i, a i • weightedColumn eps q i‖^2 := by
  have h := (lemma36_singular_values q hq eps he0 he1 a).1
  simpa [EuclideanSpace.norm_sq_eq, weightedColumn, PiLp.smul_apply,
    Ftilde, fourierUnitVec, mul_comm] using! h

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

private theorem sum_subtype_indicator {J : Type*} [Fintype J]
    (p : J → Prop) [DecidablePred p] (f : J → ℝ) :
    (∑ j : {j // p j}, f j) = ∑ j, if p j then f j else 0 := by
  have h1 (j : {j // p j}) : (if p j then f j else 0) = f j := if_pos j.property
  have h0 (j : {j // ¬p j}) : (if p j then f j else 0) = 0 := if_neg j.property
  have hs := Fintype.sum_subtype_add_sum_subtype p (fun j => if p j then f j else 0)
  simpa only [h1,h0,Finset.sum_const_zero,add_zero] using! hs

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

def transformedColumn (eps : ℝ) (q : ℕ) (k y : Fin q) : ℂ :=
  (biasedBasis eps q).repr (weightedColumn eps q k) y

theorem transformedColumn_inner (eps : ℝ) (q : ℕ) (k y : Fin q) :
    transformedColumn eps q k y = inner ℂ (biasedBasis eps q y) (weightedColumn eps q k) :=
  (biasedBasis eps q).repr_apply_apply _ _

theorem transformedColumn_upper (eps : ℝ) (q : ℕ) (k y : Fin q) (hky : k<y) :
    transformedColumn eps q k y=0 := by
  rw [transformedColumn_inner]
  exact biasedBasis_upper_zero eps q k y hky

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

theorem transformedColumn_gram (eps : ℝ) (q : ℕ) (j k : Fin q) :
    (∑y, star (transformedColumn eps q j y) * transformedColumn eps q k y) =
      ∑g, star (fourierUnitVec eps q j g) * fourierUnitVec eps q k g := by
  have h := (biasedBasis eps q).repr.inner_map_map (weightedColumn eps q j) (weightedColumn eps q k)
  simpa only [PiLp.inner_apply,RCLike.inner_apply',transformedColumn,weightedColumn] using! h

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
