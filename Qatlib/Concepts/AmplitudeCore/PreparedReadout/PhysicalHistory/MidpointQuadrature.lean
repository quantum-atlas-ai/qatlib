/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ClockDefinitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section
open MeasureTheory Set
open scoped Interval BigOperators

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.Clock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def midpointMean (N : ℕ) (f : ℝ → E) : E :=
  (N : ℝ)⁻¹ • ∑ j : Fin N, f (midpoint N j)

theorem integral_midpoint_distance (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, |t - (a+b)/2|) = (b-a)^2/4 := by
  let c := (a+b)/2
  have hac : a ≤ c := by dsimp [c]; linarith
  have hcb : c ≤ b := by dsimp [c]; linarith
  have hc : Continuous (fun t : ℝ => |t-c|) := (continuous_id.sub continuous_const).abs
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a c) (hc.intervalIntegrable c b)]
  have hleft : (∫ t in a..c, |t-c|) = ∫ t in a..c, c-t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hac] at ht
    change |t-c| = c-t
    rw [abs_of_nonpos (by linarith [ht.2] : t-c ≤ 0)]
    ring
  have hright : (∫ t in c..b, |t-c|) = ∫ t in c..b, t-c := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hcb] at ht
    exact abs_of_nonneg (by linarith [ht.1])
  change (∫ t in a..c, |t-c|) + (∫ t in c..b, |t-c|) = _
  rw [hleft, hright, intervalIntegral.integral_sub (f := fun _ : ℝ => c)
    (g := fun t : ℝ => t) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => c)
    (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
  dsimp [c]
  ring

theorem midpoint_cell_error (f : ℝ → E) (hf : Continuous f)
    (a b L : ℝ) (hab : a ≤ b)
    (hL : ∀ t ∈ Icc a b, ‖f t - f ((a+b)/2)‖ ≤ L * |t-(a+b)/2|) :
    ‖(∫ t in a..b, f t) - (b-a) • f ((a+b)/2)‖ ≤ L*(b-a)^2/4 := by
  rw [← intervalIntegral.integral_const,
    ← intervalIntegral.integral_sub (hf.intervalIntegrable a b) intervalIntegrable_const]
  have hbound : Continuous (fun t : ℝ => L * |t-(a+b)/2|) :=
    continuous_const.mul ((continuous_id.sub continuous_const).abs)
  calc
    _ ≤ ∫ t in a..b, L * |t-(a+b)/2| := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall (fun t ht => hL t ⟨le_of_lt ht.1, ht.2⟩))
        (hbound.intervalIntegrable a b)
    _ = L*(b-a)^2/4 := by
      rw [intervalIntegral.integral_const_mul, integral_midpoint_distance a b hab]
      ring

theorem midpointMean_error (f : ℝ → E) (hf : Continuous f)
    (N : ℕ) (hN : 0 < N) (L : ℝ)
    (hL : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f s-f t‖ ≤ L*|s-t|) :
    ‖(∫ t in (0 : ℝ)..1, f t) - midpointMean N f‖ ≤ L/(4*N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  let edge := fun j : ℕ => (j : ℝ)/N
  have hsum : (∑ j : Fin N, ∫ t in edge j..edge (j+1), f t) =
      ∫ t in (0 : ℝ)..1, f t := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫ t in edge j..edge (j+1), f t) N]
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := edge) (n := N)
      (fun j _ => hf.intervalIntegrable (edge j) (edge (j+1)))
    simpa [edge, hn0] using h
  have hmid (j : Fin N) : (edge j + edge (j+1))/2 = midpoint N j := by
    simp only [edge, Nat.cast_add, Nat.cast_one, midpoint]
    ring
  have hwidth (j : Fin N) : edge (j+1)-edge j = (N : ℝ)⁻¹ := by
    simp only [edge, Nat.cast_add, Nat.cast_one]
    ring
  have hcell (j : Fin N) :
      ‖(∫ t in edge j..edge (j+1), f t) - (N : ℝ)⁻¹ • f (midpoint N j)‖ ≤
        L * ((N : ℝ)⁻¹)^2/4 := by
    have he0 : 0 ≤ edge j := by dsimp [edge]; positivity
    have he1 : edge (j+1) ≤ 1 := by
      apply (div_le_one hn).mpr
      exact_mod_cast Nat.succ_le_iff.mpr j.isLt
    have he : edge j ≤ edge (j+1) := by
      have := inv_pos.mpr hn
      linarith [hwidth j]
    have hh := midpoint_cell_error f hf (edge j) (edge (j+1)) L he (fun t ht =>
      hL t ⟨he0.trans ht.1, ht.2.trans he1⟩ ((edge j+edge (j+1))/2)
        (by constructor <;> linarith))
    simpa only [hmid, hwidth] using hh
  rw [← hsum, midpointMean, Finset.smul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, ‖(∫ t in edge j..edge (j+1), f t) -
        (N : ℝ)⁻¹ • f (midpoint N j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin N, L * ((N : ℝ)⁻¹)^2/4 := Finset.sum_le_sum (fun j _ => hcell j)
    _ = L/(4*N) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

omit [CompleteSpace E] in

theorem uniformMean_error {C : Type*} [Fintype C] [Nonempty C]
    (f g : C → E) (δ : ℝ) (hδ : ∀ j, ‖f j-g j‖ ≤ δ) :
    ‖(Fintype.card C : ℝ)⁻¹ • ∑ j, f j -
      (Fintype.card C : ℝ)⁻¹ • ∑ j, g j‖ ≤ δ := by
  have hn : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (inv_pos.mpr hn))]
  calc
    _ ≤ (Fintype.card C : ℝ)⁻¹ * ∑ j, ‖f j-g j‖ := by
      gcongr; exact norm_sum_le _ _
    _ ≤ (Fintype.card C : ℝ)⁻¹ * ∑ _j : C, δ := by
      gcongr with j; exact hδ j
    _ = δ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

def midpointMean₂ (N : ℕ) (F : ℝ → ℝ → E) : E :=
  midpointMean N (fun u => midpointMean N (F u))

theorem midpointMean₂_error (F : ℝ → ℝ → E) (hF : Continuous F.uncurry)
    (N : ℕ) (hN : 0 < N) (Lu Lv : ℝ)
    (hu : ∀ u ∈ Icc (0 : ℝ) 1, ∀ u' ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ‖F u v-F u' v‖ ≤ Lu*|u-u'|)
    (hv : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ v' ∈ Icc (0 : ℝ) 1,
      ‖F u v-F u v'‖ ≤ Lv*|v-v'|) :
    ‖(∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, F u v) - midpointMean₂ N F‖ ≤
      (Lu+Lv)/(4*N) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hcont (u : ℝ) : Continuous (F u) := hF.comp (continuous_const.prodMk continuous_id)
  have hint : Continuous (fun u => ∫ v in (0 : ℝ)..1, F u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF 0 1
  have hu' : ∀ u ∈ Icc (0 : ℝ) 1, ∀ u' ∈ Icc (0 : ℝ) 1,
      ‖(∫ v in (0 : ℝ)..1, F u v) - (∫ v in (0 : ℝ)..1, F u' v)‖ ≤ Lu*|u-u'| := by
    intro u huc u' hu'c
    rw [← intervalIntegral.integral_sub ((hcont u).intervalIntegrable _ _)
      ((hcont u').intervalIntegrable _ _)]
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (fun v hvv => hu u huc u' hu'c v (by
        rw [uIoc_of_le (by norm_num)] at hvv
        exact ⟨le_of_lt hvv.1, hvv.2⟩))
  have houter := midpointMean_error _ hint N hN Lu hu'
  have hinner : ‖midpointMean N (fun u => ∫ v in (0 : ℝ)..1, F u v) -
      midpointMean₂ N F‖ ≤ Lv/(4*N) := by
    simpa only [midpointMean, midpointMean₂, Fintype.card_fin] using uniformMean_error
      (fun j : Fin N => ∫ v in (0 : ℝ)..1, F (midpoint N j) v)
      (fun j : Fin N => midpointMean N (F (midpoint N j))) _
      (fun j => midpointMean_error _ (hcont _) N hN Lv
        (hv _ (midpoint_bounds N hN j)))
  calc
    _ ≤ ‖(∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, F u v) -
          midpointMean N (fun u => ∫ v in (0 : ℝ)..1, F u v)‖ +
        ‖midpointMean N (fun u => ∫ v in (0 : ℝ)..1, F u v) - midpointMean₂ N F‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Lu/(4*N) + Lv/(4*N) := add_le_add houter hinner
    _ = (Lu+Lv)/(4*N) := by ring

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.Clock
