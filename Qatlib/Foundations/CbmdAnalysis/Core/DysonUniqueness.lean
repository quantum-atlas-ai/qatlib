/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.DysonConstruction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Uniqueness for almost-everywhere matrix evolution

`orderedEvolutionUnit` packages continuous matrix evolution as a unit whose inverse reverses the
time endpoints. Differentiation in the starting time and closure of absolute continuity under
multiplication lead to uniqueness for matrix differential equations satisfied almost everywhere.

`ordered_matrix_ode_unique_ae` identifies absolutely continuous solutions with the same initial
value on an unordered compact interval. This supports the evolution constructions used in
[WangEtAl2026].

## Main statements

* `orderedEvolution_hasDerivAt_start`: differentiates the starting time.
* `ordered_matrix_ode_unique_ae`: proves uniqueness of absolutely continuous solutions.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CBMD
open Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator

/-- The unit given by continuous ordered matrix evolution, with inverse obtained by reversing
the start and end times. -/
noncomputable def orderedEvolutionUnit {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) : (Matrix I I ℂ)ˣ where
  val := orderedEvolution A s t
  inv := orderedEvolution A t s
  val_inv := by simpa using orderedEvolution_cocycle A hA t s t
  inv_val := by simpa using orderedEvolution_cocycle A hA s t s

/-- For a continuous matrix field, the ring inverse of ordered evolution is the evolution with
its endpoints reversed. -/
theorem orderedEvolution_ringInverse {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    Ring.inverse (orderedEvolution A s t) = orderedEvolution A t s :=
  Ring.inverse_unit (orderedEvolutionUnit A hA s t)

/-- For a continuous field, differentiating the starting time of evolution to a fixed endpoint
gives right multiplication by the field. -/
theorem orderedEvolution_hasDerivAt_start {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    HasDerivAt (fun u => orderedEvolution A u s) (orderedEvolution A t s * A t) t := by
  have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) (orderedEvolutionUnit A hA s t)).comp_hasDerivAt t
    (orderedEvolution_hasDerivAt A hA s t)
  have he : (fun u => Ring.inverse (orderedEvolution A s u)) =
      (fun u => orderedEvolution A u s) := funext (orderedEvolution_ringInverse A hA s)
  dsimp only [Function.comp_def] at hd
  rw [he] at hd
  convert! hd using 1
  change orderedEvolution A t s * A t =
    -(orderedEvolution A t s * -(A t * orderedEvolution A s t) * orderedEvolution A t s)
  have hi := (orderedEvolutionUnit A hA s t).val_inv
  change orderedEvolution A s t * orderedEvolution A t s = 1 at hi
  simp only [mul_neg, neg_mul, neg_neg]
  simp only [mul_assoc, hi, mul_one]

/-- The pointwise product of two absolutely continuous functions into a normed ring is
absolutely continuous on the same interval. -/
theorem absolutelyContinuous_mul {R : Type*} [NormedRing R]
    {f g : ℝ → R} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => f t * g t) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg
  apply squeeze_zero' ?_ ?_
    (by simpa using (hg.const_mul C).add (hf.const_mul D))
  · exact Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  rw [eventually_inf_principal]
  filter_upwards with (n, J) hnJ
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hJa := (hnJ.left i hi).left
  have hJb := (hnJ.left i hi).right
  calc
    _ ≤ dist (f (J i).1 * g (J i).1) (f (J i).1 * g (J i).2) +
        dist (f (J i).1 * g (J i).2) (f (J i).2 * g (J i).2) := dist_triangle _ _ _
    _ ≤ C * dist (g (J i).1) (g (J i).2) + D * dist (f (J i).1) (f (J i).2) := by
      apply add_le_add
      · rw [dist_eq_norm, ← mul_sub, dist_eq_norm]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hC _ hJa) (norm_nonneg _))
      · rw [dist_eq_norm, ← sub_mul, dist_eq_norm]
        exact (norm_mul_le _ _).trans (by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hD _ hJb) (norm_nonneg _))

/-- For a continuous matrix field and fixed starting time, ordered evolution is continuously
differentiable in the final time. -/
theorem orderedEvolution_contDiff_one {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℝ) :
    ContDiff ℝ 1 (orderedEvolution A s) := by
  have hd := orderedEvolution_hasDerivAt A hA s
  have hc : Continuous (orderedEvolution A s) :=
    continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (orderedEvolution A s) = fun t => -(A t * orderedEvolution A s t) :=
    funext fun t => (hd t).deriv
  rw [he]
  exact (hA.mul hc).neg

/-- For a continuous matrix field and fixed final time, ordered evolution is continuously
differentiable in the starting time. -/
theorem orderedEvolution_start_contDiff_one {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℝ) :
    ContDiff ℝ 1 (fun t => orderedEvolution A t s) := by
  have hd := orderedEvolution_hasDerivAt_start A hA s
  have hc : Continuous (fun t => orderedEvolution A t s) :=
    continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (fun t => orderedEvolution A t s) = fun t => orderedEvolution A t s * A t :=
    funext fun t => (hd t).deriv
  rw [he]
  exact hc.mul hA

/-- Two absolutely continuous solutions of `U' = -A U` that satisfy the equation almost
everywhere and share their value at `a` agree on `uIcc a b`, provided `A` is continuous. -/
theorem ordered_matrix_ode_unique_ae {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (f g : ℝ → Matrix I I ℂ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hinit : f a = g a)
    (hf' : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt f (-(A t * f t)) t)
    (hg' : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt g (-(A t * g t)) t) :
    EqOn f g (uIcc a b) := by
  let w := fun t => orderedEvolution A t a * (f t - g t)
  have hback : AbsolutelyContinuousOnInterval (fun t => orderedEvolution A t a) a b :=
    (orderedEvolution_start_contDiff_one A hA a).contDiffOn.absolutelyContinuousOnInterval
  have hw : AbsolutelyContinuousOnInterval w a b := absolutelyContinuous_mul hback (hf.sub hg)
  have hw' : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt w 0 t := by
    filter_upwards [hf', hg'] with t hft hgt ht
    convert! (orderedEvolution_hasDerivAt_start A hA a t).mul ((hft ht).sub (hgt ht)) using 1
    (try simp only [Pi.sub_apply])
    noncomm_ring
  obtain ⟨C, hC⟩ := hw.const_of_ae_hasDerivAt_zero hw'
  have hwa : w a = 0 := by simp [w, hinit]
  have hC₀ : C = 0 := by simpa only [hwa] using (hC a (left_mem_uIcc)).symm
  intro t ht
  have hwt : w t = 0 := (hC t ht).trans hC₀
  have hmul := congrArg (fun M => orderedEvolution A a t * M) hwt
  change orderedEvolution A a t *
      (orderedEvolution A t a * (f t - g t)) = orderedEvolution A a t * 0 at hmul
  rw [← mul_assoc, orderedEvolution_cocycle A hA t a t,
    orderedEvolution_self, one_mul, mul_zero] at hmul
  exact sub_eq_zero.mp hmul

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
