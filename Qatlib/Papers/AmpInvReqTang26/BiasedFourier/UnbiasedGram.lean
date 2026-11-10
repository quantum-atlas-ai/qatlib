/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.ActualOverlap
import Qatlib.Papers.AmpInvReqTang26.RootLaws.Lemma23
import Qatlib.Foundations.MatrixAlgebra.TorusMoments.RootMoments
import Qatlib.Foundations.MatrixAlgebra.FrameProject.TensorErrors
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.RootLaws
open Qatlib.Foundations.MatrixAlgebra.TorusMoments
open Qatlib.Foundations.MatrixAlgebra.FrameProject.Tensor
set_option warningAsError false

theorem unbiased_column_gram (q : ℕ) (hq : 0<q) (j k : Fin q) :
    (∑g,star (fourierUnitVec 0 q j g)*fourierUnitVec 0 q k g) = if j=k then 1 else 0 := by
  have hq0 : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
  have hs : (Real.sqrt ((q:ℝ)⁻¹):ℂ)*(Real.sqrt ((q:ℝ)⁻¹):ℂ)=(q:ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul]
    have hr : Real.sqrt ((q:ℝ)⁻¹)*Real.sqrt ((q:ℝ)⁻¹)=(q:ℝ)⁻¹ := by
      nlinarith [Real.sq_sqrt (show 0≤(q:ℝ)⁻¹ by positivity)]
    rw [hr]
    simp
  have hterm (g : Fin q) : star (fourierUnitVec 0 q j g)*fourierUnitVec 0 q k g =
      (q:ℂ)⁻¹ * (phase q g ^ (k:ℕ) * star (phase q g ^ (j:ℕ))) := by
    simp only [fourierUnitVec,muEpsWeight,zero_mul,ite_self,add_zero,sub_zero,one_mul]
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
    calc
      _ = ((Real.sqrt ((q:ℝ)⁻¹):ℂ)*(Real.sqrt ((q:ℝ)⁻¹):ℂ)) *
          (phase q g ^ (k:ℕ) * star (phase q g ^ (j:ℕ))) := by
            simp only [Complex.star_def]; ring
      _ = _ := by rw [hs]; simp only [Complex.star_def]
  rw [Finset.sum_congr rfl (fun g _ => hterm g),← Finset.mul_sum]
  have hm := root_character_sum hq (omega q) (omega_isPrimitiveRoot q hq) k j
  change (∑g,phase q g ^ (k:ℕ) * star (phase q g ^ (j:ℕ))) = _ at hm
  rw [hm]
  by_cases he : j=k <;> simp [he,eq_comm, hq0]

theorem unbiased_histogram_gram {H : Type*} [DecidableEq H] {d q : ℕ}
    (hq : 0<q) (hist : H → Fin d → Fin q) (hinj : Function.Injective hist) :
    columns (fourierUnitVec 0 q) hist * (columns (fourierUnitVec 0 q) hist)ᴴ =
      histogramBasis hist * (histogramBasis hist)ᴴ := by
  ext h k
  have hb := histogramBasis_orthonormal hist hinj h k
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply] at hb ⊢
  rw [hb]
  simp only [columns,column,star_prod,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin d) (y : Fin q) =>
    fourierUnitVec 0 q (hist h i) y * star (fourierUnitVec 0 q (hist k i) y))]
  have hi (i : Fin d) : (∑y,fourierUnitVec 0 q (hist h i) y * star (fourierUnitVec 0 q (hist k i) y)) =
      if hist h i=hist k i then 1 else 0 := by
    simpa only [mul_comm,eq_comm] using! unbiased_column_gram q hq (hist k i) (hist h i)
  simp_rw [hi]
  by_cases he : h=k
  · subst k; simp
  · rw [if_neg he]
    have hex : ∃i,hist h i≠hist k i := by
      by_contra hn
      push Not at hn
      exact he (hinj (funext hn))
    obtain ⟨i,hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end Qatlib.Papers.AmpInvReqTang26.BiasedFourier
