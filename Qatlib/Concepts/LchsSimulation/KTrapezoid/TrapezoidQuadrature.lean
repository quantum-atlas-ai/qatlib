/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureLine
import Qatlib.Concepts.LchsSimulation.KTrapezoid.InhomogeneousTrapezoidSourceQuadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section


open Qatlib.Concepts.LchsSimulation.InhomLeftGrid

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid
open MeasureTheory
open scoped Classical BigOperators
set_option warningAsError false

theorem inh_trapezoid_cell_error
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F F' F'' : ℝ → E) (a b C : ℝ) (hab : a ≤ b) (hF : Continuous F)
    (hd : ∀ u ∈ Set.Icc a b, HasDerivAt F (F' u) u)
    (hdd : ∀ u ∈ Set.Icc a b, HasDerivAt F' (F'' u) u)
    (hn : ∀ u ∈ Set.Icc a b, ‖F'' u‖ ≤ C) :
    ‖((b-a)/2) • (F a+F b) - ∫ u in a..b, F u‖ ≤ C*(b-a)^3/12 := by
  let m := (a+b)/2
  have hm : m ∈ Set.Icc a b := by dsimp [m]; constructor <;> linarith
  have hc : ContinuousOn F' (Set.uIcc a b) := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact (hdd u hu).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable F' volume a b := hc.intervalIntegrable
  have hLip (u : ℝ) (hu : u ∈ Set.Icc a b) : ‖F' u-F' m‖ ≤ C*|u-m| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hdd x hx).differentiableAt)
      (fun x hx => by rw [(hdd x hx).deriv]; exact hn x hx)
      (convex_Icc a b) hm hu
    simpa only [Real.norm_eq_abs] using! h
  have hip := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun x : ℝ => x-m) (u' := fun _ => (1 : ℝ)) (v := F) (v' := F')
    (continuous_id.sub continuous_const).continuousOn hF.continuousOn
    (fun u _ => (hasDerivAt_id u).sub_const m)
    (fun u hu => hd u (by rw [min_eq_left hab, max_eq_right hab] at hu; exact ⟨hu.1.le, hu.2.le⟩))
    intervalIntegrable_const hi
  simp only [one_smul] at hip
  have hpoly : (∫ u in a..b, u-m) = 0 := by
    rw [intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ : ℝ => m)
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, smul_eq_mul]
    dsimp [m]
    ring
  have hint : ((b-a)/2) • (F a+F b) - ∫ u in a..b, F u =
      ∫ u in a..b, (u-m) • (F' u-F' m) := by
    have hcst : IntervalIntegrable (fun u : ℝ => (u-m) • F' m) volume a b :=
      ((continuous_id.sub continuous_const).smul continuous_const).intervalIntegrable _ _
    have hpint : IntervalIntegrable (fun u : ℝ => (u-m) • F' u) volume a b :=
      hi.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub (f := fun u : ℝ => (u-m) • F' u)
      (g := fun u : ℝ => (u-m) • F' m) hpint hcst,
      intervalIntegral.integral_smul_const, hpoly, zero_smul, sub_zero, hip]
    dsimp [m]
    module
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
    (f := fun u => (u-m) • (F' u-F' m)) (g := fun u => C*(u-m)^2)
    (Filter.Eventually.of_forall (fun u hu => by
      have hl := hLip u ⟨hu.1.le, hu.2⟩
      rw [norm_smul, Real.norm_eq_abs]
      apply (mul_le_mul_of_nonneg_left hl (abs_nonneg _)).trans_eq
      change |u - m| * (C * |u - m|) = C*(u-m)^2
      rw [← sq_abs]
      ring))
    ((by fun_prop : Continuous (fun u : ℝ => C*(u-m)^2)).intervalIntegrable _ _)
  rw [hint]
  apply hbound.trans_eq
  rw [intervalIntegral.integral_const_mul]
  have he : (∫ u in a..b, (u-m)^2) = (b-m)^3/3-(a-m)^3/3 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => (u-m)^3/3)
    · intro u _
      convert! (((hasDerivAt_id u).sub_const m).pow 3).div_const 3 using 1
      norm_num
    · exact (by fun_prop : Continuous (fun u : ℝ => (u-m)^2)).intervalIntegrable _ _
  rw [he]
  dsimp [m]
  ring

theorem inh_trap_sum_correction
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (Mt : ℕ) (s t : ℝ) (hm : 0 < Mt) :
    (∑ l : Fin (Mt+1), inhTrapWeight Mt s t l • F (inhTrapNode Mt s t l)) =
      (∑ l : Fin Mt, inhStep Mt s t • F (inhNode Mt s t l)) +
        (inhStep Mt s t/2) • (F t-F s) := by
  let h := inhStep Mt s t
  let z : Fin Mt := ⟨0, hm⟩
  have hz : inhNode Mt s t z = s := by simp [inhNode, z]
  have hlast : inhTrapNode Mt s t (Fin.last Mt) = t := by
    have hn : (Mt : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    dsimp [inhTrapNode, inhStep]
    field_simp
    ring
  have hw (j : Fin Mt) :
      inhTrapWeight Mt s t j.castSucc • F (inhTrapNode Mt s t j.castSucc) =
        h • F (inhNode Mt s t j) - (if j=z then (h/2) • F s else 0) := by
    have hj : (j : ℕ) ≠ Mt := Nat.ne_of_lt j.isLt
    by_cases he : j=z
    · subst j
      simp [inhTrapWeight, inhTrapNode, inhNode, z, h]
      module
    · have hj0 : (j : ℕ) ≠ 0 := by
        intro hj0
        exact he (Fin.ext (by simpa [z] using! hj0))
      simp [inhTrapWeight, inhTrapNode, inhNode, hj, hj0, he, h]
  rw [Fin.sum_univ_castSucc]
  simp only [hw, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [inhTrapWeight, Fin.val_last, or_true, if_true, hlast]
  change (∑ l : Fin Mt, h • F (inhNode Mt s t l)) - (h/2) • F s + (h/2) • F t = _
  module

theorem inh_trap_grid_error
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F F' F'' : ℝ → E) (s t C : ℝ) (Mt : ℕ) (hst : s ≤ t) (hm : 0 < Mt)
    (hF : Continuous F)
    (hd : ∀ u ∈ Set.Icc s t, HasDerivAt F (F' u) u)
    (hdd : ∀ u ∈ Set.Icc s t, HasDerivAt F' (F'' u) u)
    (hn : ∀ u ∈ Set.Icc s t, ‖F'' u‖ ≤ C) :
    ‖(∑ l : Fin (Mt+1), inhTrapWeight Mt s t l • F (inhTrapNode Mt s t l)) -
      ∫ u in s..t, F u‖ ≤ (t-s)*(inhStep Mt s t)^2*C/12 := by
  let h := inhStep Mt s t
  let x := fun j : ℕ => s+(j : ℝ)*h
  have hmR : (Mt : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hh : 0 ≤ h := inh_step_nonneg Mt s t hst
  have hstep (j : ℕ) : x (j+1)-x j = h := by dsimp [x]; push_cast; ring
  have horder (j : ℕ) : x j ≤ x (j+1) := by linarith [hstep j]
  have hx0 : x 0 = s := by simp [x]
  have hxN : x Mt = t := by dsimp [x, h, inhStep]; field_simp; ring
  have hxmem (j : ℕ) (hj : j ≤ Mt) : x j ∈ Set.Icc s t := by
    have hjR : (j : ℝ) ≤ Mt := by exact_mod_cast hj
    have he : (Mt : ℝ)*h = t-s := by dsimp [h, inhStep]; field_simp
    constructor
    · dsimp [x]; linarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hh]
    · have := mul_le_mul_of_nonneg_right hjR hh
      dsimp [x]; linarith
  let P := fun j : ℕ => (h/2) • (F (x j)+F (x (j+1)))
  let D := fun j : ℕ => P j-(∫ u in x j..x (j+1), F u)
  have hcell (j : ℕ) (hj : j < Mt) : ‖D j‖ ≤ C*h^3/12 := by
    have ha := hxmem j hj.le
    have hb := hxmem (j+1) (by omega)
    have hsub (u : ℝ) (hu : u ∈ Set.Icc (x j) (x (j+1))) : u ∈ Set.Icc s t :=
      ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
    have hc := inh_trapezoid_cell_error F F' F'' (x j) (x (j+1)) C (horder j) hF
      (fun u hu => hd u (hsub u hu)) (fun u hu => hdd u (hsub u hu))
      (fun u hu => hn u (hsub u hu))
    simpa only [hstep] using! hc
  have htel : (∑ j ∈ Finset.range Mt, (F (x (j+1))-F (x j))) = F t-F s := by
    simpa only [hx0, hxN] using! (Finset.sum_range_sub (fun j => F (x j)) Mt)
  have hp : (∑ j ∈ Finset.range Mt, P j) =
      (∑ l : Fin Mt, h • F (inhNode Mt s t l))+(h/2) • (F t-F s) := by
    have he (j : ℕ) : P j = h • F (x j)+(h/2) • (F (x (j+1))-F (x j)) := by
      dsimp [P]
      module
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [← Finset.smul_sum]
    rw [htel]
    have hfsum : (∑ j ∈ Finset.range Mt, F (x j)) = ∑ l : Fin Mt, F (inhNode Mt s t l) := by
      rw [← Fin.sum_univ_eq_sum_range]
      rfl
    rw [hfsum]
  have he : (∑ l : Fin (Mt+1), inhTrapWeight Mt s t l • F (inhTrapNode Mt s t l)) -
      ∫ u in s..t, F u = ∑ j ∈ Finset.range Mt, D j := by
    dsimp only [D]
    rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => hF.intervalIntegrable _ _), hx0, hxN, hp, inh_trap_sum_correction F Mt s t hm]
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range Mt, ‖D j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range Mt, C*h^3/12 :=
      Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
    _ = (t-s)*h^2*C/12 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have he' : (Mt : ℝ)*h = t-s := by dsimp [h, inhStep]; field_simp
      rw [← he']
      ring

theorem inh_trap_node_mem (Mt : ℕ) (s t : ℝ) (hst : s ≤ t) (hm : 0 < Mt)
    (l : Fin (Mt+1)) : inhTrapNode Mt s t l ∈ Set.Icc s t := by
  have hn : (Mt : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hl : (l : ℝ) ≤ Mt := by exact_mod_cast (Nat.le_of_lt_succ l.isLt)
  have hh := inh_step_nonneg Mt s t hst
  have he : (Mt : ℝ)*inhStep Mt s t = t-s := by dsimp [inhStep]; field_simp
  constructor
  · dsimp [inhTrapNode]; linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ l) hh]
  · have := mul_le_mul_of_nonneg_right hl hh
    dsimp [inhTrapNode]; linarith

theorem inh_trap_weight_nonneg (Mt : ℕ) (s t : ℝ) (hst : s ≤ t) (l : Fin (Mt+1)) :
    0 ≤ inhTrapWeight Mt s t l := by
  unfold inhTrapWeight
  split_ifs
  · exact div_nonneg (inh_step_nonneg Mt s t hst) (by norm_num)
  · exact inh_step_nonneg Mt s t hst

theorem inh_trap_weight_sum (Mt : ℕ) (s t : ℝ) (hm : 0 < Mt) :
    (∑ l : Fin (Mt+1), inhTrapWeight Mt s t l) = t-s := by
  have he := inh_trap_sum_correction (fun _ : ℝ => (1 : ℝ)) Mt s t hm
  simp only [smul_eq_mul, mul_one, sub_self, mul_zero, add_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  apply he.trans
  have hn : (Mt : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  dsimp [inhStep]
  field_simp

end Qatlib.Concepts.LchsSimulation.KTrapezoid
