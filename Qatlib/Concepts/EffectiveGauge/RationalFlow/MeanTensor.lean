/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanQuadrature
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Normalized operators for the three-dimensional source-mean quadrature

Uniform errors survive both actual unit-interval integration and finite
normalized left sums. These are the contraction steps for the tensor estimate.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Unit-interval integration preserves a uniform difference bound. -/
theorem meanUnitIntegral_sub_bound (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (C : ℝ) (hfg : ∀ x ∈ Icc (0 : ℝ) 1, |f x-g x| ≤ C) :
    |(∫ x in (0 : ℝ)..1, f x)-(∫ x in (0 : ℝ)..1, g x)| ≤ C := by
  have hb : ∀ x ∈ Ι (0 : ℝ) 1, ‖f x-g x‖ ≤ C := by
    intro x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    simpa only [Real.norm_eq_abs] using hfg x ⟨hx.1.le,hx.2⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)] at hi
  simpa using hi

/-- All actual left-grid points are in the original unit interval. -/
theorem meanLeftNode_mem (N : ℕ) (hN : 0<N) (k : ℕ) (hk : k<N) :
    (k : ℝ)/(N : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  exact ⟨div_nonneg (Nat.cast_nonneg _) hn.le,(div_le_one hn).mpr (by exact_mod_cast Nat.le_of_lt hk)⟩

/-- Finite normalized left sums preserve a uniform difference bound. -/
theorem meanLeftSum_sub_bound (N : ℕ) (hN : 0<N) (f g : ℝ → ℝ)
    (C : ℝ) (hfg : ∀ x ∈ Icc (0 : ℝ) 1, |f x-g x| ≤ C) :
    |meanLeftSum N f-meanLeftSum N g| ≤ C := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  rw [meanLeftSum,meanLeftSum,← sub_div,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range N, |f ((k : ℝ)/(N : ℝ))-g ((k : ℝ)/(N : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, C := by
      apply Finset.sum_le_sum
      intro k hk
      exact hfg _ (meanLeftNode_mem N hN k (Finset.mem_range.mp hk))
    _ = C*(N : ℝ) := by simp [mul_comm]

/-- Original `continuous_meanLeftSum` guarantee for the `MeanTensor` construction; the complete source hypotheses are retained. -/
private theorem continuous_meanLeftSum {X : Type*} [TopologicalSpace X]
    (N : ℕ) (F : X → ℝ → ℝ) (hF : Continuous F.uncurry) :
    Continuous (fun x => meanLeftSum N (F x)) := by
  have hc (k : ℕ) : Continuous (fun x => F x ((k : ℝ)/(N : ℝ))) :=
    hF.comp (continuous_id.prodMk continuous_const)
  exact (continuous_finsetSum _ (fun k _ => hc k)).div_const _

/-- Original `continuous_meanUnitIntegral` guarantee for the `MeanTensor` construction; the complete source hypotheses are retained. -/
private theorem continuous_meanUnitIntegral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (F : X → ℝ → ℝ) (hF : Continuous F.uncurry) :
    Continuous (fun x => ∫ y in (0 : ℝ)..1, F x y) := by
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hF (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_Icc_eq_integral_Ioc] using hc


/-- Abbreviation for Mean Tensor Point in the Rational Flow construction. -/
abbrev MeanTensorPoint := ℝ × ℝ × ℝ

/-- The ordinary coordinate cube used for tensor quadrature. -/
def meanTensorInCube (p : MeanTensorPoint) : Prop :=
  p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2 ∈ Icc (0 : ℝ) 1

/-- Coordinatewise distance, retaining the constant needed by the source mesh. -/
def meanTensorDistance (p q : MeanTensorPoint) : ℝ :=
  |p.1-q.1|+|p.2.1-q.2.1|+|p.2.2-q.2.2|

/-- The genuine iterated unit-cube Lebesgue integral. -/
def meanTensorIntegral (f : MeanTensorPoint → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (x,y,z)

/-- The exact tensor left sum, before replacing its node values by rational packets. -/
def meanTensorLeftSum (N : ℕ) (f : MeanTensorPoint → ℝ) : ℝ :=
  meanLeftSum N (fun x => meanLeftSum N (fun y => meanLeftSum N (fun z => f (x,y,z))))

/-- Three applications of the actual one-dimensional integral estimate give
`3*D/N`; no Euclidean/operator-norm dimension factor is silently dropped. -/
theorem meanTensorLeftSum_error (N : ℕ) (hN : 0<N) (f : MeanTensorPoint → ℝ)
    (hf : Continuous f) (D : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ p q, meanTensorInCube p → meanTensorInCube q →
      |f p-f q| ≤ D*meanTensorDistance p q) :
    |meanTensorIntegral f-meanTensorLeftSum N f| ≤ 3*D/(N : ℝ) := by
  let Ixy := fun x y : ℝ => ∫ z in (0 : ℝ)..1, f (x,y,z)
  let Qxy := fun x y : ℝ => meanLeftSum N (fun z => f (x,y,z))
  let Iy := fun x : ℝ => ∫ y in (0 : ℝ)..1, Ixy x y
  let Ay := fun x : ℝ => ∫ y in (0 : ℝ)..1, Qxy x y
  let By := fun x : ℝ => meanLeftSum N (Qxy x)
  have h3 : Continuous (fun p : (ℝ × ℝ) × ℝ => f (p.1.1,p.1.2,p.2)) :=
    hf.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hIxy : Continuous (fun p : ℝ × ℝ => Ixy p.1 p.2) :=
    continuous_meanUnitIntegral (fun p : ℝ × ℝ => fun z => f (p.1,p.2,z)) h3
  have hQxy : Continuous (fun p : ℝ × ℝ => Qxy p.1 p.2) :=
    continuous_meanLeftSum N (fun p : ℝ × ℝ => fun z => f (p.1,p.2,z)) h3
  have hIy : Continuous Iy := continuous_meanUnitIntegral Ixy hIxy
  have hAy : Continuous Ay := continuous_meanUnitIntegral Qxy hQxy
  have hBy : Continuous By := continuous_meanLeftSum N Qxy hQxy
  have hinner (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      |Ixy x y-Qxy x y| ≤ D/(N : ℝ) := by
    have hc : Continuous (fun z : ℝ => f (x,y,z)) :=
      hf.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    apply meanLeftSum_error N hN (fun z => f (x,y,z)) hc D hD
    intro z hz w hw
    simpa [meanTensorDistance] using hLip (x,y,z) (x,y,w) ⟨hx,hy,hz⟩ ⟨hx,hy,hw⟩
  have hfirst : |(∫ x in (0 : ℝ)..1, Iy x)-(∫ x in (0 : ℝ)..1, Ay x)| ≤ D/(N : ℝ) := by
    apply meanUnitIntegral_sub_bound Iy Ay hIy hAy (D/(N : ℝ))
    intro x hx
    have hi : Continuous (Ixy x) := hIxy.comp (continuous_const.prodMk continuous_id)
    have hq : Continuous (Qxy x) := hQxy.comp (continuous_const.prodMk continuous_id)
    exact meanUnitIntegral_sub_bound (Ixy x) (Qxy x) hi hq (D/(N : ℝ)) (hinner x hx)
  have hmiddleLip (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1)
      (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) : |Qxy x y-Qxy x w| ≤ D*|y-w| := by
    apply meanLeftSum_sub_bound N hN
    intro z hz
    simpa [meanTensorDistance] using hLip (x,y,z) (x,w,z) ⟨hx,hy,hz⟩ ⟨hx,hw,hz⟩
  have hsecond : |(∫ x in (0 : ℝ)..1, Ay x)-(∫ x in (0 : ℝ)..1, By x)| ≤ D/(N : ℝ) := by
    apply meanUnitIntegral_sub_bound Ay By hAy hBy (D/(N : ℝ))
    intro x hx
    have hc : Continuous (Qxy x) := hQxy.comp (continuous_const.prodMk continuous_id)
    exact meanLeftSum_error N hN (Qxy x) hc D hD (hmiddleLip x hx)
  have houterLip (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      |By x-By w| ≤ D*|x-w| := by
    apply meanLeftSum_sub_bound N hN
    intro y hy
    apply meanLeftSum_sub_bound N hN
    intro z hz
    simpa [meanTensorDistance] using hLip (x,y,z) (w,y,z) ⟨hx,hy,hz⟩ ⟨hw,hy,hz⟩
  have hthird : |(∫ x in (0 : ℝ)..1, By x)-meanLeftSum N By| ≤ D/(N : ℝ) :=
    meanLeftSum_error N hN By hBy D hD houterLip
  change |(∫ x in (0 : ℝ)..1, Iy x)-meanLeftSum N By| ≤ 3*D/(N : ℝ)
  calc
    _ ≤ |(∫ x in (0 : ℝ)..1, Iy x)-(∫ x in (0 : ℝ)..1, Ay x)|+
        |(∫ x in (0 : ℝ)..1, Ay x)-(∫ x in (0 : ℝ)..1, By x)|+
        |(∫ x in (0 : ℝ)..1, By x)-meanLeftSum N By| := by
      have ha := abs_sub_le (∫ x in (0 : ℝ)..1, Iy x) (∫ x in (0 : ℝ)..1, Ay x) (meanLeftSum N By)
      have hb := abs_sub_le (∫ x in (0 : ℝ)..1, Ay x) (∫ x in (0 : ℝ)..1, By x) (meanLeftSum N By)
      linarith
    _ ≤ D/(N : ℝ)+D/(N : ℝ)+D/(N : ℝ) := add_le_add (add_le_add hfirst hsecond) hthird
    _ = 3*D/(N : ℝ) := by ring

/-- The nested normalized sum is precisely the full N-cubed average, with
one common denominator. This is the form consumed by the integer accumulator. -/
theorem meanTensorLeftSum_eq (N : ℕ) (f : MeanTensorPoint → ℝ) :
    meanTensorLeftSum N f=
      (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N,
        f ((k : ℝ)/(N : ℝ),(l : ℝ)/(N : ℝ),(m : ℝ)/(N : ℝ)))/(N : ℝ)^3 := by
  simp only [meanTensorLeftSum,meanLeftSum]
  simp_rw [← Finset.sum_div]
  simp [div_div,pow_succ,mul_assoc]

end Qatlib.Concepts.EffectiveGauge.RationalFlow
