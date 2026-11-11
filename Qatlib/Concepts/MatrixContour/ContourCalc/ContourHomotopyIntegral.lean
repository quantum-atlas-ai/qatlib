/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ResolventHomotopyCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! Compact-rectangle FTC/Fubini for scalar-anchor resolvent integration. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc
open MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

/-- The identity or estimate `rectangle_integral_difference` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem rectangle_integral_difference
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F G H : ℝ → ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hF0 : IntervalIntegrable (F 0) volume a b)
    (hF1 : IntervalIntegrable (F 1) volume a b)
    (hH : ContinuousOn (Function.uncurry H) (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hFs : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun v => F v t) (H s t) s)
    (hGt : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      HasDerivAt (G s) (H s t) t) :
    (∫ t in a..b, F 1 t)-(∫ t in a..b, F 0 t) =
      ∫ s in (0 : ℝ)..1, G s b-G s a := by
  have hH_s (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalIntegrable (fun s => H s t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact hH.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, ht⟩)
  have hH_t (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (H s) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact hH.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hs, ht⟩)
  have hprod : Integrable (Function.uncurry H)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict]
    exact (hH.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap : (∫ t in a..b, ∫ s in (0 : ℝ)..1, H s t) =
      ∫ s in (0 : ℝ)..1, ∫ t in a..b, H s t := by
    simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le zero_le_one]
    exact (MeasureTheory.integral_integral_swap hprod).symm
  rw [← intervalIntegral.integral_sub hF1 hF0]
  calc
    (∫ t in a..b, F 1 t-F 0 t) = ∫ t in a..b, ∫ s in (0 : ℝ)..1, H s t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hFs t ht' s (by simpa only [uIcc_of_le zero_le_one] using hs))
        (hH_s t ht')).symm
    _ = ∫ s in (0 : ℝ)..1, ∫ t in a..b, H s t := hswap
    _ = ∫ s in (0 : ℝ)..1, G s b-G s a := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hGt s hs' t (by simpa only [uIcc_of_le hab] using ht)) (hH_t s hs')

/-- The identity or estimate `panel_inverse_continuousOn` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem panel_inverse_continuousOn {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (c z₀ u : ℂ) (a h : ℝ)
    (hu : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a (a+h),
      IsUnit (matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t))) :
    ContinuousOn (fun st : ℝ × ℝ => homotopyPanelInverse A c z₀ u a h st.1 st.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc a (a+h)) := by
  have hm : Continuous (fun st : ℝ × ℝ =>
      matrixShift (scalarAnchorHomotopy A c st.1) (contourPanel z₀ u a h st.2)) := by
    unfold matrixShift scalarAnchorHomotopy contourPanel
    fun_prop
  intro st hst
  have hi : ContinuousAt (Ring.inverse : Matrix I I ℂ → Matrix I I ℂ)
      (matrixShift (scalarAnchorHomotopy A c st.1) (contourPanel z₀ u a h st.2)) :=
    (differentiableAt_inverse (𝕜 := ℝ) (hu st.1 hst.1 st.2 hst.2)).continuousAt
  have hcomp := hi.comp (x := st) hm.continuousAt
  exact hcomp.continuousWithinAt

noncomputable local instance {I : Type} [Fintype I] [DecidableEq I] :
    ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- Closed-panel resolvent integration is unchanged by a uniformly separated
scalar-anchor contraction, including anchors outside the original range. Neither a matrix Cauchy identity nor
a matrix-integral error bound is assumed. -/
theorem closed_panels_resolvent_homotopy_of_uniform_separation {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (c : ℂ)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ s ∈ Icc (0 : ℝ) 1, ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A c s), r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖) :
    (∑ j, ∫ t in (a j)..(a j+h j),
      u j • matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) =
    ∑ j, ∫ t in (a j)..(a j+h j),
      u j • matrixResolvent (c • (1 : Matrix I I ℂ))
        (contourPanel (z₀ j) (u j) (a j) (h j) t) := by
  let D := A-c • (1 : Matrix I I ℂ)
  let R (j : J) (s t : ℝ) := homotopyPanelInverse A c (z₀ j) (u j) (a j) (h j) s t
  let F (j : J) (s t : ℝ) := u j • R j s t
  let G (j : J) (s t : ℝ) := -D * R j s t
  let H (j : J) (s t : ℝ) := u j • (R j s t * D * R j s t)
  have hunit (j : J) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ)
      (ht : t ∈ Icc (a j) (a j+h j)) :
      IsUnit (matrixShift (scalarAnchorHomotopy A c s)
        (contourPanel (z₀ j) (u j) (a j) (h j) t)) := by
    obtain ⟨hl, hr', _⟩ := matrixResolvent_inverse_norm_of_separation _ _ r hr
      (hsep s hs j t ht)
    exact ⟨⟨_, _, hl, hr'⟩, rfl⟩
  have hR (j : J) : ContinuousOn (Function.uncurry (R j))
      (Icc (0 : ℝ) 1 ×ˢ Icc (a j) (a j+h j)) :=
    panel_inverse_continuousOn A c (z₀ j) (u j) (a j) (h j) (hunit j)
  have hEnd (j : J) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (F j s) volume (a j) (a j+h j) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [hh j])
    have hsR : ContinuousOn (fun t : ℝ => R j s t) (Icc (a j) (a j+h j)) :=
      (hR j).comp (f := fun t : ℝ => (s,t))
        (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
    exact (continuousOn_const (c := u j)).smul hsR
  have hH (j : J) : ContinuousOn (Function.uncurry (H j))
      (Icc (0 : ℝ) 1 ×ˢ Icc (a j) (a j+h j)) := by
    have hD : ContinuousOn (fun _ : ℝ × ℝ => D)
        (Icc (0 : ℝ) 1 ×ˢ Icc (a j) (a j+h j)) := continuousOn_const
    exact (continuousOn_const (c := u j)).smul (((hR j).mul hD).mul (hR j))
  have hG (j : J) : IntervalIntegrable
      (fun s => G j s (a j+h j)-G j s (a j)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hb := (hR j).comp (f := fun s : ℝ => (s,a j+h j))
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, show a j+h j ∈ Icc (a j) (a j+h j) from ⟨by linarith [hh j], le_rfl⟩⟩)
    have ha := (hR j).comp (f := fun s : ℝ => (s,a j))
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, show a j ∈ Icc (a j) (a j+h j) from ⟨le_rfl, by linarith [hh j]⟩⟩)
    exact ((continuousOn_const (c := -D)).mul hb).sub
      ((continuousOn_const (c := -D)).mul ha)
  have hPart (j : J) : (∫ t in (a j)..(a j+h j), F j 1 t)-
      (∫ t in (a j)..(a j+h j), F j 0 t) =
      ∫ s in (0 : ℝ)..1, G j s (a j+h j)-G j s (a j) := by
    apply rectangle_integral_difference (F j) (G j) (H j) (a j) (a j+h j)
      (by linarith [hh j]) (hEnd j 0 (by norm_num)) (hEnd j 1 (by norm_num)) (hH j)
    · intro t ht s hs
      exact (homotopyPanelInverse_closed_form A c (z₀ j) (u j) (a j) (h j) s t
        (hunit j s hs t ht)).1
    · intro s hs t ht
      exact (homotopyPanelInverse_closed_form A c (z₀ j) (u j) (a j) (h j) s t
        (hunit j s hs t ht)).2
  have hGsum (s : ℝ) : (∑ j, (G j s (a j+h j)-G j s (a j))) = 0 := by
    have he (j : J) : G j s (a j+h j) = G (next j) s (a (next j)) := by
      dsimp only [G, R, homotopyPanelInverse]
      rw [hclosed j]
    simp only [Finset.sum_sub_distrib, he]
    rw [Equiv.sum_comp next (fun j => G j s (a j)), sub_self]
  have hInt : (∑ j, ∫ t in (a j)..(a j+h j), F j 1 t) =
      ∑ j, ∫ t in (a j)..(a j+h j), F j 0 t := by
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    simp_rw [hPart]
    rw [← intervalIntegral.integral_finsetSum (fun j _ => hG j)]
    simp only [hGsum, intervalIntegral.integral_zero]
  have h0 : scalarAnchorHomotopy A c 0 = c • (1 : Matrix I I ℂ) := by
    simp [scalarAnchorHomotopy]
  have h1 : scalarAnchorHomotopy A c 1 = A := by
    simp [scalarAnchorHomotopy]
  have hEq (j : J) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (∫ t in (a j)..(a j+h j), F j s t) =
      ∫ t in (a j)..(a j+h j), u j • matrixResolvent (scalarAnchorHomotopy A c s)
        (contourPanel (z₀ j) (u j) (a j) (h j) t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (a j) (a j+h j) := by
      simpa only [uIcc_of_le (show a j ≤ a j+h j by linarith [hh j])] using ht
    exact congrArg (fun M : Matrix I I ℂ => u j • M)
      (matrixResolvent_eq_ringInverse_of_separation (scalarAnchorHomotopy A c s)
        (contourPanel (z₀ j) (u j) (a j) (h j) t) r hr (hsep s hs j t ht')).symm
  simpa only [hEq _ 1 (by norm_num), hEq _ 0 (by norm_num), h0, h1] using hInt

/-- The original actual-range-anchor interface is preserved. -/
theorem closed_panels_resolvent_homotopy {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (c : ℂ) (hc : c ∈ matrixNumericalRange A)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖) :
    (∑ j, ∫ t in (a j)..(a j+h j),
      u j • matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) =
    ∑ j, ∫ t in (a j)..(a j+h j),
      u j • matrixResolvent (c • (1 : Matrix I I ℂ))
        (contourPanel (z₀ j) (u j) (a j) (h j) t) := by
  apply closed_panels_resolvent_homotopy_of_uniform_separation A c z₀ u a h next hclosed r hr hh
  intro s hs j t ht
  exact scalarAnchorHomotopy_separation A c _ hc s hs r (hsep j t ht)

end Qatlib.Concepts.MatrixContour.ContourCalc
