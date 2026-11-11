/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.ComplexQuadrature
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanTensor

/-!
# Complex Tensor

Hopf Atlas constructions for Effective Gauge.
Defines `complexMeanTensorIntegral`, `complexMeanTensorLeftSum`.
Proves `complexMeanUnitIntegral_sub_bound`, `complexMeanLeftSum_sub_bound`, `continuous_complexMeanLeftSum`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Unit-interval integration preserves a uniform difference bound. -/
theorem complexMeanUnitIntegral_sub_bound (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (C : ℝ) (hfg : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x-g x‖ ≤ C) :
    ‖(∫ x in (0 : ℝ)..1, f x)-(∫ x in (0 : ℝ)..1, g x)‖ ≤ C := by
  have hb : ∀ x ∈ Ι (0 : ℝ) 1, ‖f x-g x‖ ≤ C := by
    intro x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hfg x ⟨hx.1.le,hx.2⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)] at hi
  simpa using hi

/-- Finite normalized left sums preserve a uniform difference bound. -/
theorem complexMeanLeftSum_sub_bound (N : ℕ) (hN : 0<N) (f g : ℝ → ℂ)
    (C : ℝ) (hfg : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x-g x‖ ≤ C) :
    ‖complexMeanLeftSum N f-complexMeanLeftSum N g‖ ≤ C := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hsum : ‖∑ k ∈ Finset.range N, (f ((k : ℝ)/(N : ℝ))-g ((k : ℝ)/(N : ℝ)))‖ ≤ (N : ℝ)*C := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, ‖f ((k : ℝ)/(N : ℝ))-g ((k : ℝ)/(N : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, C := by
        apply Finset.sum_le_sum
        intro k hk
        exact hfg _ (meanLeftNode_mem N hN k (Finset.mem_range.mp hk))
      _ = _ := by simp
  rw [complexMeanLeftSum,complexMeanLeftSum,← smul_sub,← Finset.sum_sub_distrib,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (N : ℝ)⁻¹*((N : ℝ)*C) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = C := by rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]

/-- Original `continuous_complexMeanLeftSum` guarantee for the `ComplexTensor` construction; the complete source hypotheses are retained. -/
private theorem continuous_complexMeanLeftSum {X : Type*} [TopologicalSpace X]
    (N : ℕ) (F : X → ℝ → ℂ) (hF : Continuous F.uncurry) :
    Continuous (fun x => complexMeanLeftSum N (F x)) := by
  have hc (k : ℕ) : Continuous (fun x => F x ((k : ℝ)/(N : ℝ))) :=
    hF.comp (continuous_id.prodMk continuous_const)
  exact (continuous_finsetSum _ (fun k _ => hc k)).const_smul ((N : ℝ)⁻¹)

/-- Original `continuous_complexMeanUnitIntegral` guarantee for the `ComplexTensor` construction; the complete source hypotheses are retained. -/
theorem continuous_complexMeanUnitIntegral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (F : X → ℝ → ℂ) (hF : Continuous F.uncurry) :
    Continuous (fun x => ∫ y in (0 : ℝ)..1, F x y) := by
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hF (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_Icc_eq_integral_Ioc] using hc


/-- The genuine iterated unit-cube Lebesgue integral. -/
def complexMeanTensorIntegral (f : MeanTensorPoint → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (x,y,z)

/-- The exact tensor left sum, before replacing its node values by rational packets. -/
def complexMeanTensorLeftSum (N : ℕ) (f : MeanTensorPoint → ℂ) : ℂ :=
  complexMeanLeftSum N (fun x => complexMeanLeftSum N (fun y => complexMeanLeftSum N (fun z => f (x,y,z))))

/-- Three applications of the actual one-dimensional integral estimate give
`3*D/N`; no Euclidean/operator-norm dimension factor is silently dropped. -/
theorem complexMeanTensorLeftSum_error (N : ℕ) (hN : 0<N) (f : MeanTensorPoint → ℂ)
    (hf : Continuous f) (D : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ p q, meanTensorInCube p → meanTensorInCube q →
      ‖f p-f q‖ ≤ D*meanTensorDistance p q) :
    ‖complexMeanTensorIntegral f-complexMeanTensorLeftSum N f‖ ≤ 3*D/(N : ℝ) := by
  let Ixy := fun x y : ℝ => ∫ z in (0 : ℝ)..1, f (x,y,z)
  let Qxy := fun x y : ℝ => complexMeanLeftSum N (fun z => f (x,y,z))
  let Iy := fun x : ℝ => ∫ y in (0 : ℝ)..1, Ixy x y
  let Ay := fun x : ℝ => ∫ y in (0 : ℝ)..1, Qxy x y
  let By := fun x : ℝ => complexMeanLeftSum N (Qxy x)
  have h3 : Continuous (fun p : (ℝ × ℝ) × ℝ => f (p.1.1,p.1.2,p.2)) :=
    hf.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hIxy : Continuous (fun p : ℝ × ℝ => Ixy p.1 p.2) :=
    continuous_complexMeanUnitIntegral (fun p : ℝ × ℝ => fun z => f (p.1,p.2,z)) h3
  have hQxy : Continuous (fun p : ℝ × ℝ => Qxy p.1 p.2) :=
    continuous_complexMeanLeftSum N (fun p : ℝ × ℝ => fun z => f (p.1,p.2,z)) h3
  have hIy : Continuous Iy := continuous_complexMeanUnitIntegral Ixy hIxy
  have hAy : Continuous Ay := continuous_complexMeanUnitIntegral Qxy hQxy
  have hBy : Continuous By := continuous_complexMeanLeftSum N Qxy hQxy
  have hinner (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      ‖Ixy x y-Qxy x y‖ ≤ D/(N : ℝ) := by
    have hc : Continuous (fun z : ℝ => f (x,y,z)) :=
      hf.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    apply complexMeanLeftSum_error N hN (fun z => f (x,y,z)) hc D hD
    intro z hz w hw
    simpa [meanTensorDistance] using hLip (x,y,z) (x,y,w) ⟨hx,hy,hz⟩ ⟨hx,hy,hw⟩
  have hfirst : ‖(∫ x in (0 : ℝ)..1, Iy x)-(∫ x in (0 : ℝ)..1, Ay x)‖ ≤ D/(N : ℝ) := by
    apply complexMeanUnitIntegral_sub_bound Iy Ay hIy hAy (D/(N : ℝ))
    intro x hx
    have hi : Continuous (Ixy x) := hIxy.comp (continuous_const.prodMk continuous_id)
    have hq : Continuous (Qxy x) := hQxy.comp (continuous_const.prodMk continuous_id)
    exact complexMeanUnitIntegral_sub_bound (Ixy x) (Qxy x) hi hq (D/(N : ℝ)) (hinner x hx)
  have hmiddleLip (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1)
      (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) : ‖Qxy x y-Qxy x w‖ ≤ D*|y-w| := by
    apply complexMeanLeftSum_sub_bound N hN
    intro z hz
    simpa [meanTensorDistance] using hLip (x,y,z) (x,w,z) ⟨hx,hy,hz⟩ ⟨hx,hw,hz⟩
  have hsecond : ‖(∫ x in (0 : ℝ)..1, Ay x)-(∫ x in (0 : ℝ)..1, By x)‖ ≤ D/(N : ℝ) := by
    apply complexMeanUnitIntegral_sub_bound Ay By hAy hBy (D/(N : ℝ))
    intro x hx
    have hc : Continuous (Qxy x) := hQxy.comp (continuous_const.prodMk continuous_id)
    exact complexMeanLeftSum_error N hN (Qxy x) hc D hD (hmiddleLip x hx)
  have houterLip (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      ‖By x-By w‖ ≤ D*|x-w| := by
    apply complexMeanLeftSum_sub_bound N hN
    intro y hy
    apply complexMeanLeftSum_sub_bound N hN
    intro z hz
    simpa [meanTensorDistance] using hLip (x,y,z) (w,y,z) ⟨hx,hy,hz⟩ ⟨hw,hy,hz⟩
  have hthird : ‖(∫ x in (0 : ℝ)..1, By x)-complexMeanLeftSum N By‖ ≤ D/(N : ℝ) :=
    complexMeanLeftSum_error N hN By hBy D hD houterLip
  change ‖(∫ x in (0 : ℝ)..1, Iy x)-complexMeanLeftSum N By‖ ≤ 3*D/(N : ℝ)
  calc
    _ ≤ ‖(∫ x in (0 : ℝ)..1, Iy x)-(∫ x in (0 : ℝ)..1, Ay x)‖+
        ‖(∫ x in (0 : ℝ)..1, Ay x)-(∫ x in (0 : ℝ)..1, By x)‖+
        ‖(∫ x in (0 : ℝ)..1, By x)-complexMeanLeftSum N By‖ := by
      have ha := dist_triangle (∫ x in (0 : ℝ)..1, Iy x) (∫ x in (0 : ℝ)..1, Ay x) (complexMeanLeftSum N By)
      have hb := dist_triangle (∫ x in (0 : ℝ)..1, Ay x) (∫ x in (0 : ℝ)..1, By x) (complexMeanLeftSum N By)
      simp only [dist_eq_norm] at ha hb
      linarith
    _ ≤ D/(N : ℝ)+D/(N : ℝ)+D/(N : ℝ) := add_le_add (add_le_add hfirst hsecond) hthird
    _ = 3*D/(N : ℝ) := by ring

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
