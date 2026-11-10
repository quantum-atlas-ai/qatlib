/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.EuclideanLayer
set_option warningAsError false

noncomputable section
open MeasureTheory
namespace Qatlib.Papers.LatentPQCTran26.MainResults.NoBiasBarrenPlateau
open EuclideanLayer LinearMetaGrad

def expectedLoss {K D : ℕ} {Z : Type*} [MeasurableSpace Z]
    (r : Measure Z) (h : Z → Fin D → ℝ)
    (L : EuclideanSpace ℝ (Fin K) → ℝ) (w : Parameters K D) : ℝ :=
  populationLoss r h (decoder K D) L w

theorem radius_arithmetic (g Lambda gamma : ℝ) (hLambda : 0 < Lambda)
    (hgamma : gamma ≤ g / (2 * Lambda)) : g / 2 ≤ g - Lambda * gamma := by
  have hm := (le_div_iff₀ (show 0 < 2 * Lambda by positivity)).mp hgamma
  linarith

theorem proposition10_actual {K D : ℕ} {Z : Type*} [MeasurableSpace Z]
    (r : Measure Z) [IsProbabilityMeasure r]
    (h : Z → Fin D → ℝ) (hh : AEStronglyMeasurable h r)
    (M : ℝ) (hM : ∀ z j, |h z j| ≤ M)
    (L : EuclideanSpace ℝ (Fin K) → ℝ) (hL : Differentiable ℝ L)
    (hD : Continuous (fderiv ℝ L))
    (B C : ℝ) (hB : ∀ x, ‖L x‖ ≤ B) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (w : Parameters K D) (theta : EuclideanSpace ℝ (Fin K))
    (Lambda gamma g : ℝ) (hLambda : 0 < Lambda)
    (hLip : ∀ x y, ‖fderiv ℝ L x - fderiv ℝ L y‖ ≤ Lambda * ‖x - y‖)
    (hnear : ∀ z, ‖decoder K D (h z) w - theta‖ ≤ gamma)
    (hg : g ≤ ‖gradient L theta‖) (hgamma : gamma ≤ g / (2 * Lambda)) :
    g / 2 ≤ ‖gradient (fun b : EuclideanSpace ℝ (Fin K) =>
        expectedLoss r h L (w + bias K D b)) 0‖ ∧
      ‖gradient (fun b : EuclideanSpace ℝ (Fin K) =>
        expectedLoss r h L (w + bias K D b)) 0‖ ≤
        ‖gradient (expectedLoss r h L) w‖ := by
  let N := ‖column K D none‖ + M * ∑ j, ‖column K D (some j)‖
  have hN : ∀ z, ‖decoder K D (h z)‖ ≤ N := fun z => decoder_norm_le K D _ M (hM z)
  have hg' : g ≤ ‖fderiv ℝ L theta‖ := by rwa [nativeGradient_norm] at hg
  obtain ⟨hlower,hfull⟩ := fullDerivative_lower_bound r h hh (decoder K D)
    (decoder_continuous K D) N hN L hL hD B C hB hC w (bias K D)
    (decoder_bias K D) (bias_norm_le K D) theta Lambda gamma g hLambda.le hLip hnear hg'
  obtain ⟨_,hd⟩ := populationLoss_hasFDerivAt r h hh (decoder K D)
    (decoder_continuous K D) N hN L hL hD B C hB hC w
  have hshift : HasFDerivAt (fun b : EuclideanSpace ℝ (Fin K) => w + bias K D b)
      (bias K D) 0 := by
    simpa using (bias K D).hasFDerivAt.const_add w (x := (0 : EuclideanSpace ℝ (Fin K)))
  have hbderiv : fderiv ℝ (fun b : EuclideanSpace ℝ (Fin K) =>
      expectedLoss r h L (w + bias K D b)) 0 =
        (fderiv ℝ (expectedLoss r h L) w).comp (bias K D) := by
    have hd' : HasFDerivAt (populationLoss r h (decoder K D) L)
        (∫ z, (fderiv ℝ L (decoder K D (h z) w)).comp (decoder K D (h z)) ∂r)
        (w + bias K D 0) := by simpa using hd
    have hc := hd'.comp 0 hshift
    change fderiv ℝ (fun b => populationLoss r h (decoder K D) L
      (w + bias K D b)) 0 =
      (fderiv ℝ (populationLoss r h (decoder K D) L) w).comp (bias K D)
    rw [hd.fderiv]
    simpa [Function.comp_def] using hc.fderiv
  simp only [nativeGradient_norm, hbderiv]
  exact ⟨(radius_arithmetic g Lambda gamma hLambda hgamma).trans hlower,hfull⟩

end Qatlib.Papers.LatentPQCTran26.MainResults.NoBiasBarrenPlateau
