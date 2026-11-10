/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidQuadratureStat
import Qatlib.Concepts.LchsSimulation.KTrapezoid.TrapezoidQuadrature
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

theorem k_trap_node_eq (K M : ℕ) (j : Fin (M+1)) :
    kTrapNode K M j = inhTrapNode M (-(K : ℝ)) K j := by
  dsimp [kTrapNode, inhTrapNode, inhStep]
  ring

theorem k_trap_weight_eq (K M : ℕ) (j : Fin (M+1)) :
    kTrapWeight K M j = inhTrapWeight M (-(K : ℝ)) K j := by
  dsimp [kTrapWeight, inhTrapWeight, inhStep]
  split_ifs <;> ring

theorem k_trap_weight_nonneg (K M : ℕ) (j : Fin (M+1)) :
    0 ≤ kTrapWeight K M j := by
  rw [k_trap_weight_eq]
  apply inh_trap_weight_nonneg
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  linarith

theorem k_trap_weight_sum (K M : ℕ) (hM : 0 < M) :
    (∑ j : Fin (M+1), kTrapWeight K M j) = 2*(K : ℝ) := by
  simp_rw [k_trap_weight_eq]
  rw [inh_trap_weight_sum M (-(K : ℝ)) K hM]
  ring

theorem k_trap_duhamel {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (hL : Continuous L) (hH : Continuous H)
    (s t a b : ℝ) :
    orderedEvolution (fun u => Complex.I • (H u+a • L u)) s t -
      orderedEvolution (fun u => Complex.I • (H u+b • L u)) s t =
    (b-a) • (∫ u in s..t,
      orderedEvolution (fun v => Complex.I • (H v+a • L v)) u t *
        (Complex.I • L u) *
          orderedEvolution (fun v => Complex.I • (H v+b • L v)) s u) := by
  let A := fun u => Complex.I • (H u+a • L u)
  let B := fun u => Complex.I • (H u+b • L u)
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hB : Continuous B := by dsimp [B]; fun_prop
  let f := fun u => orderedEvolution A u t * orderedEvolution B s u
  let D := fun u => orderedEvolution A u t * (Complex.I • L u) * orderedEvolution B s u
  have hAc : Continuous (fun u => orderedEvolution A u t) :=
    continuous_iff_continuousAt.mpr (fun u =>
      (orderedEvolution_hasDerivAt_start A hA t u).continuousAt)
  have hBc : Continuous (orderedEvolution B s) :=
    continuous_iff_continuousAt.mpr (fun u =>
      (orderedEvolution_hasDerivAt B hB s u).continuousAt)
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hd (u : ℝ) : HasDerivAt f ((a-b) • D u) u := by
    convert! (orderedEvolution_hasDerivAt_start A hA t u).mul
      (orderedEvolution_hasDerivAt B hB s u) using 1
    have he : A u-B u = (a-b) • (Complex.I • L u) := by
      dsimp [A, B]
      rw [← smul_sub]
      module
    dsimp [D]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← he]
    noncomm_ring
  have hDc : Continuous (fun u => (a-b) • D u) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hDc.intervalIntegrable s t)
  rw [intervalIntegral.integral_smul] at he
  simp only [f, orderedEvolution_self, Matrix.one_mul, Matrix.mul_one] at he
  rw [show b-a = -(a-b) by ring, neg_smul, he]
  simp [A, B]

theorem k_trap_parameter_deriv_norm {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (s t k : ℝ)
    (hL : Continuous L) (hH : Continuous H)
    (hHermL : ∀ u, (L u).IsHermitian) (hHermH : ∀ u, (H u).IsHermitian)
    (hst : s ≤ t) :
    ‖deriv (fun a : ℝ => orderedEvolution
      (fun u => Complex.I • (H u+a • L u)) s t) k‖ ≤ ∫ u in s..t, ‖L u‖ := by
  apply norm_deriv_le_of_lip'
    (intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _))
  exact Filter.Eventually.of_forall (fun a => by
    simpa only [Real.norm_eq_abs, mul_comm] using!
      time_dependent_lchs_same_unitary_stability I L H s t a k
        hL hH hHermL hHermH hst)

theorem k_trap_duhamel_integral_norm {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (s t a b : ℝ)
    (hL : Continuous L) (hH : Continuous H)
    (hHermL : ∀ u, (L u).IsHermitian) (hHermH : ∀ u, (H u).IsHermitian)
    (hst : s ≤ t) :
    ‖∫ u in s..t, orderedEvolution (fun v => Complex.I • (H v+a • L v)) u t *
      (Complex.I • L u) * orderedEvolution (fun v => Complex.I • (H v+b • L v)) s u‖ ≤
        ∫ u in s..t, ‖L u‖ := by
  have hunit (r u c : ℝ) := ordered_evolution_hermitian_unitary I
    (fun x => H x+c • L x) (by fun_prop)
    (fun x => (hHermH x).add ((hHermL x).smul (R := ℝ) (IsSelfAdjoint.all c))) r u
  apply intervalIntegral.norm_integral_le_of_norm_le hst
    (Filter.Eventually.of_forall (fun u _ => ?_)) (hL.norm.intervalIntegrable s t)
  have ha := l2_norm_unitary_le_one (hunit u t a)
  have hb := l2_norm_unitary_le_one (hunit s u b)
  calc
    _ ≤ (‖orderedEvolution (fun v => Complex.I • (H v+a • L v)) u t‖ *
        ‖Complex.I • L u‖) *
          ‖orderedEvolution (fun v => Complex.I • (H v+b • L v)) s u‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖Complex.I • L u‖)*1 := by gcongr
    _ = ‖L u‖ := by rw [one_mul, mul_one, norm_smul, Complex.norm_I, one_mul]

def kTrapDuhamelIntegral {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (s t a b : ℝ) : Matrix I I ℂ :=
  ∫ u in s..t, orderedEvolution (fun v => Complex.I • (H v+a • L v)) u t *
    (Complex.I • L u) * orderedEvolution (fun v => Complex.I • (H v+b • L v)) s u

theorem k_trap_duhamel_integral_lipschitz {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (s t a b c d : ℝ)
    (hL : Continuous L) (hH : Continuous H)
    (hHermL : ∀ u, (L u).IsHermitian) (hHermH : ∀ u, (H u).IsHermitian)
    (hst : s ≤ t) :
    ‖kTrapDuhamelIntegral L H s t a b-kTrapDuhamelIntegral L H s t c d‖ ≤
      (|a-c|+|b-d|)*(∫ u in s..t, ‖L u‖)^2 := by
  let budget := ∫ u in s..t, ‖L u‖
  let V : ℝ → ℝ → ℝ → Matrix I I ℂ :=
      fun (k r u : ℝ) => orderedEvolution (fun v => Complex.I • (H v+k • L v)) r u
  have hbudget : 0 ≤ budget := intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
  have hn (k r u : ℝ) : ‖V k r u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I
      (fun v => H v+k • L v) (by fun_prop)
      (fun v => (hHermH v).add ((hHermL v).smul (R := ℝ) (IsSelfAdjoint.all k))) r u)
  have hi (k l : ℝ) : IntervalIntegrable
      (fun u => V k u t * (Complex.I • L u) * V l s u) volume s t := by
    have hA : Continuous (fun v => Complex.I • (H v+k • L v)) := by fun_prop
    have hB : Continuous (fun v => Complex.I • (H v+l • L v)) := by fun_prop
    have hVk : Continuous (fun u => V k u t) := continuous_iff_continuousAt.mpr (fun u =>
      (orderedEvolution_hasDerivAt_start _ hA t u).continuousAt)
    have hVl : Continuous (fun u => V l s u) := continuous_iff_continuousAt.mpr (fun u =>
      (orderedEvolution_hasDerivAt _ hB s u).continuousAt)
    have hprod : Continuous (fun u => V k u t * (Complex.I • L u) * V l s u) := by fun_prop
    exact hprod.intervalIntegrable s t
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc s t) :
      ‖V a u t * (Complex.I • L u) * V b s u -
        V c u t * (Complex.I • L u) * V d s u‖ ≤
          ((|a-c|+|b-d|)*budget)*‖L u‖ := by
    have hut : (∫ v in u..t, ‖L v‖) ≤ budget :=
      intervalIntegral.integral_mono_interval hu.1 hu.2 le_rfl
        (Filter.Eventually.of_forall (fun v => norm_nonneg (L v))) (hL.norm.intervalIntegrable s t)
    have hsu : (∫ v in s..u, ‖L v‖) ≤ budget :=
      intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
        (Filter.Eventually.of_forall (fun v => norm_nonneg (L v))) (hL.norm.intervalIntegrable s t)
    have hl : ‖V a u t-V c u t‖ ≤ |a-c| *budget :=
      (time_dependent_lchs_same_unitary_stability I L H u t a c hL hH hHermL hHermH hu.2).trans
        (mul_le_mul_of_nonneg_left hut (abs_nonneg _))
    have hr : ‖V b s u-V d s u‖ ≤ |b-d| *budget :=
      (time_dependent_lchs_same_unitary_stability I L H s u b d hL hH hHermL hHermH hu.1).trans
        (mul_le_mul_of_nonneg_left hsu (abs_nonneg _))
    have he : V a u t * (Complex.I • L u) * V b s u -
        V c u t * (Complex.I • L u) * V d s u =
        (V a u t-V c u t) * (Complex.I • L u) * V b s u +
          V c u t * (Complex.I • L u) * (V b s u-V d s u) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖(V a u t-V c u t) * (Complex.I • L u) * V b s u‖ +
          ‖V c u t * (Complex.I • L u) * (V b s u-V d s u)‖ := norm_add_le _ _
      _ ≤ (‖V a u t-V c u t‖ * ‖Complex.I • L u‖)*‖V b s u‖ +
          (‖V c u t‖ * ‖Complex.I • L u‖)*‖V b s u-V d s u‖ := by
        apply add_le_add <;> exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((|a-c| *budget)*‖Complex.I • L u‖)*1 +
          (1*‖Complex.I • L u‖)*(|b-d| *budget) := by gcongr <;> apply hn
      _ = _ := by rw [norm_smul, Complex.norm_I]; ring
  dsimp only [kTrapDuhamelIntegral]
  rw [← intervalIntegral.integral_sub (hi a b) (hi c d)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le hst
    (Filter.Eventually.of_forall (fun u hu => hpoint u ⟨hu.1.le, hu.2⟩))
    ((continuous_const.mul hL.norm).intervalIntegrable (μ := volume) s t)
  refine hb.trans_eq ?_
  rw [intervalIntegral.integral_const_mul]
  dsimp only [budget]
  ring

theorem k_trap_parameter_hasDerivAt {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (s t k : ℝ)
    (hL : Continuous L) (hH : Continuous H)
    (hHermL : ∀ u, (L u).IsHermitian) (hHermH : ∀ u, (H u).IsHermitian)
    (hst : s ≤ t) :
    HasDerivAt (fun a : ℝ => orderedEvolution
      (fun u => Complex.I • (H u+a • L u)) s t)
      (-kTrapDuhamelIntegral L H s t k k) k := by
  apply HasDerivAt.of_isLittleO
  apply (Asymptotics.IsBigO.of_bound ((∫ u in s..t, ‖L u‖)^2) ?_).trans_isLittleO
    (Asymptotics.isLittleO_pow_sub_sub k (by norm_num : 1 < (2 : ℕ)))
  apply Filter.Eventually.of_forall
  intro a
  have he := k_trap_duhamel L H hL hH s t a k
  change _ = (k-a) • kTrapDuhamelIntegral L H s t a k at he
  rw [he]
  have hr : (k-a) • kTrapDuhamelIntegral L H s t a k -
      (a-k) • (-kTrapDuhamelIntegral L H s t k k) =
      (k-a) • (kTrapDuhamelIntegral L H s t a k-kTrapDuhamelIntegral L H s t k k) := by
    module
  rw [hr, norm_smul, Real.norm_eq_abs]
  have hb := k_trap_duhamel_integral_lipschitz L H s t a k k k hL hH hHermL hHermH hst
  simp only [sub_self, abs_zero, add_zero] at hb
  calc
    _ ≤ |k-a| *(|a-k| *(∫ u in s..t, ‖L u‖)^2) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by
      rw [abs_sub_comm k a]
      simp only [Real.norm_eq_abs, abs_pow, abs_abs]
      ring

theorem k_trap_lipschitz_cell_error
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F F' : ℝ → E) (a b C : ℝ) (hab : a ≤ b) (hF : Continuous F)
    (hd : ∀ u ∈ Set.Icc a b, HasDerivAt F (F' u) u)
    (hc' : ContinuousOn F' (Set.Icc a b))
    (hlip : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, ‖F' u-F' v‖ ≤ C*|u-v|) :
    ‖((b-a)/2) • (F a+F b) - ∫ u in a..b, F u‖ ≤ C*(b-a)^3/12 := by
  let m := (a+b)/2
  have hm : m ∈ Set.Icc a b := by dsimp [m]; constructor <;> linarith
  have hi : IntervalIntegrable F' volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using! hc'
  have hLip (u : ℝ) (hu : u ∈ Set.Icc a b) : ‖F' u-F' m‖ ≤ C*|u-m| :=
    hlip u hu m hm
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

theorem k_trap_lipschitz_grid_error
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F F' : ℝ → E) (s t C : ℝ) (Mt : ℕ) (hst : s ≤ t) (hm : 0 < Mt)
    (hF : Continuous F)
    (hd : ∀ u ∈ Set.Icc s t, HasDerivAt F (F' u) u)
    (hc' : ContinuousOn F' (Set.Icc s t))
    (hlip : ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, ‖F' u-F' v‖ ≤ C*|u-v|) :
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
    have hc := k_trap_lipschitz_cell_error F F' (x j) (x (j+1)) C (horder j) hF
      (fun u hu => hd u (hsub u hu)) (hc'.mono hsub)
      (fun u hu v hv => hlip u (hsub u hu) v (hsub v hv))
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

private def kTrapDensity (k : ℝ) : ℝ := 1/(Real.pi*(1+k^2))
private def kTrapDensity' (k : ℝ) : ℝ := -2*k/(Real.pi*(1+k^2)^2)
private def kTrapDensity'' (k : ℝ) : ℝ := (6*k^2-2)/(Real.pi*(1+k^2)^3)

private theorem k_trap_density_hasDerivAt (k : ℝ) :
    HasDerivAt kTrapDensity (kTrapDensity' k) k := by
  have hn : Real.pi*(1+k^2) ≠ 0 := by positivity
  convert! (hasDerivAt_const k (1 : ℝ)).div
    (((hasDerivAt_const k (1 : ℝ)).add ((hasDerivAt_id k).pow 2)).const_mul Real.pi) hn using 1
  dsimp [kTrapDensity, kTrapDensity']
  field_simp
  ring

private theorem k_trap_density'_hasDerivAt (k : ℝ) :
    HasDerivAt kTrapDensity' (kTrapDensity'' k) k := by
  have hn : Real.pi*(1+k^2)^2 ≠ 0 := by positivity
  convert! ((hasDerivAt_id k).const_mul (-2)).div
    ((((hasDerivAt_const k (1 : ℝ)).add ((hasDerivAt_id k).pow 2)).pow 2).const_mul Real.pi) hn using 1
  dsimp [kTrapDensity', kTrapDensity'']
  field_simp
  ring

private theorem k_trap_density_norm (k : ℝ) : ‖kTrapDensity k‖ ≤ 1/Real.pi := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [kTrapDensity]; positivity)]
  dsimp [kTrapDensity]
  apply div_le_div_of_nonneg_left (by norm_num) Real.pi_pos
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg k)]

private theorem k_trap_density'_norm (k : ℝ) : ‖kTrapDensity' k‖ ≤ 1/Real.pi := by
  rw [Real.norm_eq_abs]
  dsimp [kTrapDensity']
  rw [abs_div, abs_of_pos (by positivity : 0 < Real.pi*(1+k^2)^2)]
  apply (div_le_iff₀ (by positivity : 0 < Real.pi*(1+k^2)^2)).2
  rw [div_mul_eq_mul_div]
  field_simp
  rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsq : |k|^2 = k^2 := sq_abs k
  have h : 2*|k| ≤ 1+k^2 := by nlinarith [sq_nonneg (|k|-1)]
  nlinarith [sq_nonneg (k^2), sq_nonneg k]

private theorem k_trap_density''_norm (k : ℝ) : ‖kTrapDensity'' k‖ ≤ 2/Real.pi := by
  rw [Real.norm_eq_abs]
  dsimp [kTrapDensity'']
  rw [abs_div, abs_of_pos (by positivity : 0 < Real.pi*(1+k^2)^3)]
  apply (div_le_iff₀ (by positivity : 0 < Real.pi*(1+k^2)^3)).2
  rw [div_mul_eq_mul_div]
  field_simp
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg k, sq_nonneg (k^2), pow_nonneg (sq_nonneg k) 3]

private theorem k_trap_density_lipschitz (a b : ℝ) :
    ‖kTrapDensity a-kTrapDensity b‖ ≤ (1/Real.pi)*|a-b| := by
  simpa only [Real.norm_eq_abs] using!
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (k_trap_density_hasDerivAt x).differentiableAt)
      (fun x _ => by rw [(k_trap_density_hasDerivAt x).deriv]; exact k_trap_density'_norm x)
      (Set.mem_univ b) (Set.mem_univ a)

private theorem k_trap_density'_lipschitz (a b : ℝ) :
    ‖kTrapDensity' a-kTrapDensity' b‖ ≤ (2/Real.pi)*|a-b| := by
  simpa only [Real.norm_eq_abs] using!
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (k_trap_density'_hasDerivAt x).differentiableAt)
      (fun x _ => by rw [(k_trap_density'_hasDerivAt x).deriv]; exact k_trap_density''_norm x)
      (Set.mem_univ b) (Set.mem_univ a)

private theorem kTrapDensity_nonneg (k : ℝ) : 0 ≤ kTrapDensity k := by
  dsimp [kTrapDensity]; positivity

private theorem kTrapTail_arctan_le (x : ℝ) (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := x) (f := Real.arctan) (f' := fun k : ℝ => (1+k^2)⁻¹) (C := 1)
    (fun k _ => (Real.hasDerivAt_arctan' k).hasDerivWithinAt)
    (fun k _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg k])) x ⟨hx, le_rfl⟩
  have hh : |Real.arctan x| ≤ x := by simpa using! hb
  exact (le_abs_self _).trans hh

private theorem kTrapDensity_integrable : Integrable kTrapDensity := by
  change Integrable (fun k : ℝ => 1/(Real.pi*(1+k^2)))
  simpa [kTrapDensity, div_eq_mul_inv, _root_.mul_inv_rev, mul_comm] using!
    integrable_inv_one_add_sq.const_mul Real.pi⁻¹

private theorem kTrapDensity_continuous : Continuous kTrapDensity := by
  apply Continuous.div continuous_const
  · fun_prop
  · intro k; positivity

private theorem kTrapDensity_tail (K : ℝ) (hK : 0 < K) :
    (∫ k : ℝ in (Set.Ioc (-K) K)ᶜ, kTrapDensity k) ≤ 2/(Real.pi*K) := by
  have he : (Set.Ioc (-K) K)ᶜ = Set.Iic (-K) ∪ Set.Ioi K := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
      not_and_or, not_lt, not_le]
  have hd : Disjoint (Set.Iic (-K)) (Set.Ioi K) := by
    rw [Set.disjoint_left]
    intro x hx hy; simp only [Set.mem_Iic, Set.mem_Ioi] at *; linarith
  rw [he, setIntegral_union hd measurableSet_Ioi kTrapDensity_integrable.integrableOn
    kTrapDensity_integrable.integrableOn]
  have hleft : (∫ k : ℝ in Set.Iic (-K), kTrapDensity k) =
      Real.pi⁻¹*(Real.pi/2-Real.arctan K) := by
    simp only [kTrapDensity, div_eq_mul_inv, _root_.mul_inv_rev, one_mul]
    rw [integral_mul_const, integral_Iic_inv_one_add_sq, Real.arctan_neg]
    ring
  have hright : (∫ k : ℝ in Set.Ioi K, kTrapDensity k) =
      Real.pi⁻¹*(Real.pi/2-Real.arctan K) := by
    simp only [kTrapDensity, div_eq_mul_inv, _root_.mul_inv_rev, one_mul]
    rw [integral_mul_const, integral_Ioi_inv_one_add_sq]
    ring
  rw [hleft, hright, ← Real.arctan_inv_of_pos hK]
  have ha := kTrapTail_arctan_le K⁻¹ (inv_nonneg.mpr hK.le)
  calc
    _ ≤ Real.pi⁻¹*K⁻¹+Real.pi⁻¹*K⁻¹ := by gcongr
    _ = _ := by ring

section Quadrature
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in

private theorem kTrapTail_weighted_integrable (V : ℝ → E) (hV : Continuous V)
    (hn : ∀ k, ‖V k‖ ≤ 1) : Integrable (fun k => kTrapDensity k • V k) :=
  kTrapDensity_integrable.smul_bdd 1 hV.aestronglyMeasurable (Filter.Eventually.of_forall hn)

omit [CompleteSpace E] in

private theorem kTrapTail_weighted_tail (V : ℝ → E) (hV : Continuous V)
    (hn : ∀ k, ‖V k‖ ≤ 1) (K : ℝ) (hK : 0 < K) :
    ‖(∫ k : ℝ, kTrapDensity k • V k) - (∫ k in (-K)..K, kTrapDensity k • V k)‖ ≤
      2/(Real.pi*K) := by
  have hf := kTrapTail_weighted_integrable V hV hn
  rw [intervalIntegral.integral_of_le (by linarith : -K ≤ K),
    ← integral_add_compl measurableSet_Ioc hf, add_sub_cancel_left]
  apply (MeasureTheory.norm_integral_le_of_norm_le kTrapDensity_integrable.integrableOn
    (Filter.Eventually.of_forall (fun k => ?_))).trans (kTrapDensity_tail K hK)
  rw [norm_smul, Real.norm_of_nonneg (kTrapDensity_nonneg k)]
  simpa using! mul_le_mul_of_nonneg_left (hn k) (kTrapDensity_nonneg k)

end Quadrature

theorem k_trap_weighted_derivative {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (s t : ℝ)
    (hL : Continuous L) (hH : Continuous H)
    (hHermL : ∀ u, (L u).IsHermitian) (hHermH : ∀ u, (H u).IsHermitian)
    (hst : s ≤ t) :
    ∃ F' : ℝ → Matrix I I ℂ,
      (∀ k, HasDerivAt (fun a : ℝ => (1/(Real.pi*(1+a^2))) •
        orderedEvolution (fun u => Complex.I • (H u+a • L u)) s t) (F' k) k) ∧
      Continuous F' ∧ ∀ a b, ‖F' a-F' b‖ ≤
        (2*(1+(∫ u in s..t, ‖L u‖)+(∫ u in s..t, ‖L u‖)^2)/Real.pi)*|a-b| := by
  let V := fun k : ℝ => orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t
  let D := fun k : ℝ => kTrapDuhamelIntegral L H s t k k
  let budget := ∫ u in s..t, ‖L u‖
  let C := 2*(1+budget+budget^2)/Real.pi
  let F' := fun k => kTrapDensity' k • V k - kTrapDensity k • D k
  have hbudget : 0 ≤ budget := intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnormV (k : ℝ) : ‖V k‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I
      (fun u => H u+k • L u) (by fun_prop)
      (fun u => (hHermH u).add ((hHermL u).smul (R := ℝ) (IsSelfAdjoint.all k))) s t)
  have hnormD (k : ℝ) : ‖D k‖ ≤ budget :=
    k_trap_duhamel_integral_norm L H s t k k hL hH hHermL hHermH hst
  have hlipV (a b : ℝ) : ‖V a-V b‖ ≤ |a-b| *budget :=
    time_dependent_lchs_same_unitary_stability I L H s t a b hL hH hHermL hHermH hst
  have hlipD (a b : ℝ) : ‖D a-D b‖ ≤ 2*budget^2*|a-b| := by
    have h := k_trap_duhamel_integral_lipschitz L H s t a a b b hL hH hHermL hHermH hst
    convert! h using 1
    dsimp [D, budget]
    ring
  have hdf (k : ℝ) : HasDerivAt (fun a : ℝ => kTrapDensity a • V a) (F' k) k := by
    convert! (k_trap_density_hasDerivAt k).smul
      (k_trap_parameter_hasDerivAt L H s t k hL hH hHermL hHermH hst) using 1
    dsimp [F', D]
    module
  have hlipF (a b : ℝ) : ‖F' a-F' b‖ ≤ C*|a-b| := by
    have he : F' a-F' b =
        (kTrapDensity' a-kTrapDensity' b) • V a + kTrapDensity' b • (V a-V b) -
        ((kTrapDensity a-kTrapDensity b) • D a + kTrapDensity b • (D a-D b)) := by
      dsimp [F']; module
    rw [he]
    calc
      _ ≤ (‖(kTrapDensity' a-kTrapDensity' b) • V a‖ +
          ‖kTrapDensity' b • (V a-V b)‖) +
          (‖(kTrapDensity a-kTrapDensity b) • D a‖ +
          ‖kTrapDensity b • (D a-D b)‖) :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ = (‖kTrapDensity' a-kTrapDensity' b‖*‖V a‖ +
          ‖kTrapDensity' b‖*‖V a-V b‖) +
          (‖kTrapDensity a-kTrapDensity b‖*‖D a‖ +
          ‖kTrapDensity b‖*‖D a-D b‖) := by simp only [norm_smul]
      _ ≤ ((2/Real.pi)*|a-b| *1 + (1/Real.pi)*(|a-b| *budget)) +
          ((1/Real.pi)*|a-b| *budget + (1/Real.pi)*(2*budget^2*|a-b|)) := by
        gcongr
        · exact k_trap_density'_lipschitz a b
        · exact hnormV a
        · exact k_trap_density'_norm b
        · exact hlipV a b
        · exact k_trap_density_lipschitz a b
        · exact hnormD a
        · exact k_trap_density_norm b
        · exact hlipD a b
      _ = _ := by dsimp [C]; ring
  refine ⟨F', hdf, ?_, hlipF⟩
  have hLip : LipschitzWith ⟨C, hC⟩ F' := LipschitzWith.of_dist_le_mul (fun a b => by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using! hlipF a b)
  exact hLip.continuous

theorem homogeneousKTrapezoidQuadrature : HomogeneousKTrapezoidQuadrature := by
  intro I _ _ L H s t K M hL hH hPSD hHerm hst hK hM
  let V := fun k : ℝ => orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t
  let F := fun k : ℝ => kTrapDensity k • V k
  let C := 2*(1+(∫ u in s..t, ‖L u‖)+(∫ u in s..t, ‖L u‖)^2)/Real.pi
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hHermL : ∀ u, (L u).IsHermitian := fun u => (hPSD u).isHermitian
  have hVc : Continuous V := continuous_iff_continuousAt.mpr (fun k =>
    (k_trap_parameter_hasDerivAt L H s t k hL hH hHermL hHerm hst).continuousAt)
  have hFc : Continuous F := by dsimp [F]; have := kTrapDensity_continuous; fun_prop
  have hVn (k : ℝ) : ‖V k‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I
      (fun u => H u+k • L u) (by fun_prop)
      (fun u => (hHerm u).add ((hHermL u).smul (R := ℝ) (IsSelfAdjoint.all k))) s t)
  obtain ⟨F', hd, hc, hlip⟩ := k_trap_weighted_derivative L H s t hL hH hHermL hHerm hst
  have hgrid := k_trap_lipschitz_grid_error F F' (-(K : ℝ)) K C M
    (by linarith) hM hFc (fun u _ => hd u) hc.continuousOn (fun u _ v _ => hlip u v)
  have hsum : kTrapSum L H s t K M =
      ∑ j : Fin (M+1), inhTrapWeight M (-(K : ℝ)) K j • F (inhTrapNode M (-(K : ℝ)) K j) := by
    unfold kTrapSum
    apply Finset.sum_congr rfl
    intro j _
    rw [← k_trap_node_eq, ← k_trap_weight_eq]
    dsimp only [kTrapCoeff, F, kTrapDensity, V]
    rw [Complex.coe_smul, smul_smul]
    congr 1
    ring
  rw [← hsum] at hgrid
  have hq : ‖kTrapSum L H s t K M - (∫ k in -(K : ℝ)..(K : ℝ), F k)‖ ≤
      (2*(K : ℝ))^3/(12*(M : ℝ)^2)*C := hgrid.trans_eq (by
        dsimp only [inhStep]
        field_simp
        ring)
  have htail := kTrapTail_weighted_tail V hVc hVn (K : ℝ) hKr
  have he := (time_dependent_lchs_cauchy_representation I L H s t hL hH hPSD hHerm hst).2
  change (∫ k : ℝ, F k) = _ at he
  rw [← he]
  have ht := norm_sub_le_norm_sub_add_norm_sub (kTrapSum L H s t K M)
    (∫ k in -(K : ℝ)..(K : ℝ), F k) (∫ k : ℝ, F k)
  rw [norm_sub_rev (∫ k in -(K : ℝ)..(K : ℝ), F k)] at ht
  exact ht.trans ((add_le_add hq htail).trans_eq (by dsimp [C]; ring))

end Qatlib.Concepts.LchsSimulation.KTrapezoid
