/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities
set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open Matrix
open scoped Classical BigOperators Kronecker

def aqGoodWindow (N P : ℕ) : Finset (Fin N) := {y | ∃ a : ℕ,
  a< P ∧ Nat.Coprime a P ∧ |(y.val:ℚ)/N-(a:ℚ)/P|≤1/(2*(N:ℚ))}
noncomputable def aqSuccessLower (N M P : ℕ) : ℝ :=
  4*(Nat.totient P:ℝ)*(M:ℝ)*aqGain N M/(Real.pi^2*(N-M:ℕ))

theorem aq_kernel_half_window (M : ℕ) (hM : 0 < M) (phi : ℝ)
    (hw : |(M:ℝ)*phi| ≤ 1/2) :
    4/Real.pi^2 ≤ ‖qpeKernel M phi (⟨0,hM⟩ : Fin M)‖^2 := by
  let delta := (M:ℝ)*phi
  have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  by_cases hd : delta=0
  · have hp : phi=0 := (mul_eq_zero.mp hd).resolve_left hMR
    rw [hp]
    have h0 : qpeKernel M 0 (⟨0,hM⟩ : Fin M) = 1 := by
      simpa [Ket] using!
          (offgrid_phase_geometric_and_periodic M 0 (⟨0,hM⟩ : Fin M) hM).2.2 (⟨0,hM⟩ : Fin M)
    rw [h0]
    simp only [norm_one, one_pow]
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [Real.two_le_pi]
  · have hn : (M:ℝ)*phi = (0:ℤ)+delta := by dsimp [delta]; simp
    have hr : phi-(0:ℝ)/(M:ℝ) = (0:ℤ)+delta/(M:ℝ) := by
      dsimp [delta]
      simp [hMR]
    have hk :=
        qpeKernel_neighbour_lower M phi ⟨0,hM⟩ hM 0 0 delta delta hn
        (by simpa only [Nat.cast_zero] using! hr) hd
    have hab : |Real.pi*delta| ≤ Real.pi/2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact (mul_le_mul_of_nonneg_left hw Real.pi_pos.le).trans_eq (by ring)
    have hj := Real.mul_abs_le_abs_sin hab
    have he : 2/Real.pi*|Real.pi*delta| = 2*|delta| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    rw [he] at hj
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*|delta|) hj 2
    simp only [mul_pow, sq_abs] at hs
    norm_num only [show (2:ℝ)^2 = 4 by norm_num] at hs
    calc
      _ = (4*delta^2)/(Real.pi^2*delta^2) := by field_simp
      _ ≤ (Real.sin (Real.pi*delta))^2/(Real.pi^2*delta^2) :=
        div_le_div_of_nonneg_right hs (by positivity)
      _ ≤ _ := hk

theorem aqPhase_normSq (N s y : ℕ) : Complex.normSq (aqPhase N s y) = 1 := by
  simp [Complex.normSq_eq_norm_sq, aqPhase, Complex.norm_exp]

theorem aq_progression_kernel (N s M P y : ℕ) (hM : 0 < M) :
    aqProgressionFourier N s M P y =
      aqPhase N s y*(M:ℂ)*qpeKernel M (-(P:ℝ)*(y:ℝ)/(N:ℝ)) (⟨0,hM⟩ : Fin M) := by
  have hk : qpeKernel M (-(P:ℝ)*(y:ℝ)/(N:ℝ)) (⟨0,hM⟩ : Fin M) = (M:ℂ)⁻¹ *
      ∑ r : Fin M, Complex.exp (2*Real.pi*Complex.I*((r.val:ℝ)*(-(P:ℝ)*(y:ℝ)/(N:ℝ)))) := by
    have h := (offgrid_phase_kernel_formula M (-(P:ℝ)*(y:ℝ)/(N:ℝ)) ⟨0,hM⟩ hM).2.1
    simpa only [Nat.cast_zero, Complex.ofReal_zero, zero_div, sub_zero,
      Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] using! h
  rw [hk, mul_assoc, mul_inv_cancel_left₀ (show (M:ℂ) ≠ 0 by exact_mod_cast hM.ne')]
  have hs : (∑ r : Fin M, Complex.exp (2*Real.pi*Complex.I*((r.val:ℝ)*(-(P:ℝ)*(y:ℝ)/(N:ℝ))))) =
      ∑ r ∈ Finset.range M, Complex.exp (2*Real.pi*Complex.I*((r:ℝ)*(-(P:ℝ)*(y:ℝ)/(N:ℝ)))) :=
    Fin.sum_univ_eq_sum_range (fun r : ℕ => Complex.exp
      (2*Real.pi*Complex.I*((r:ℝ)*(-(P:ℝ)*(y:ℝ)/(N:ℝ))))) M
  rw [hs]
  unfold aqProgressionFourier
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  unfold aqPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem aq_window_root_lower (N s M P : ℕ) (hN : 0 < N) (hM : 0 < M) (hP : 0 < P)
    (hMP : M*P ≤ N) (y : Fin N) (a : ℕ)
    (hw : |(y.val:ℚ)/N-(a:ℚ)/P| ≤ 1/(2*(N:ℚ))) :
    4*(M:ℝ)^2/Real.pi^2 ≤ Complex.normSq (aqProgressionFourier N s M P y.val) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hPR : (0:ℝ) < P := by exact_mod_cast hP
  have hwR : |(y.val:ℝ)/(N:ℝ)-(a:ℝ)/(P:ℝ)| ≤ 1/(2*(N:ℝ)) := by
    have h : ((|(y.val:ℚ)/N-(a:ℚ)/P| : ℚ):ℝ) ≤ ((1/(2*(N:ℚ)) : ℚ):ℝ) := Rat.cast_le.mpr hw
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
        Rat.cast_mul, Rat.cast_one] using! h
  let phi := (a:ℝ)-(P:ℝ)*(y.val:ℝ)/(N:ℝ)
  have he : phi = -(P:ℝ)*((y.val:ℝ)/(N:ℝ)-(a:ℝ)/(P:ℝ)) := by
    dsimp [phi]
    field_simp
    ring
  have hb : |(M:ℝ)*phi| ≤ 1/2 := by
    rw [abs_mul, abs_of_pos hMR, he, abs_mul, abs_neg, abs_of_pos hPR]
    have h := mul_le_mul_of_nonneg_left hwR (show 0 ≤ (M:ℝ)*(P:ℝ) by positivity)
    have hc : (M:ℝ)*(P:ℝ) ≤ N := by exact_mod_cast hMP
    calc
      _ = ((M:ℝ)*(P:ℝ))*|(y.val:ℝ)/(N:ℝ)-(a:ℝ)/(P:ℝ)| := by ring
      _ ≤ ((M:ℝ)*(P:ℝ))*(1/(2*(N:ℝ))) := h
      _ ≤ (N:ℝ)*(1/(2*(N:ℝ))) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 1/2 := by field_simp
  have hk := aq_kernel_half_window M hM phi hb
  have hperiod : qpeKernel M (-(P:ℝ)*(y.val:ℝ)/(N:ℝ)) (⟨0,hM⟩ : Fin M) =
      qpeKernel M phi (⟨0,hM⟩ : Fin M) := by
    have h := qpeKernel_int_add M (-(P:ℝ)*(y.val:ℝ)/(N:ℝ)) (⟨0,hM⟩ : Fin M) (a:ℤ)
    have he : (-(P:ℝ)*(y.val:ℝ)/(N:ℝ)) + ((a:ℤ):ℝ) = phi := by
      dsimp [phi]
      push_cast
      ring
    rw [he] at h
    exact h.symm
  rw [aq_progression_kernel N s M P y.val hM, Complex.normSq_mul, Complex.normSq_mul,
    aqPhase_normSq, Complex.normSq_natCast, one_mul, hperiod]
  rw [Complex.normSq_eq_norm_sq]
  have h := mul_le_mul_of_nonneg_left hk (show 0 ≤ (M:ℝ)^2 by positivity)
  convert! h using 1 <;> ring

def aqNearestNat (N P a : ℕ) : ℕ := Nat.floor ((N:ℚ)*(a:ℚ)/(P:ℚ)+1/2)

theorem aqNearest_bounds (N P a : ℕ) (hP : 0 < P) (hPN : P < N) (ha : a < P) :
    aqNearestNat N P a < N ∧
      |(aqNearestNat N P a:ℚ)/N-(a:ℚ)/P| ≤ 1/(2*(N:ℚ)) := by
  have hN : 0 < N := by omega
  have hNR : (0:ℚ) < N := by exact_mod_cast hN
  have hPR : (0:ℚ) < P := by exact_mod_cast hP
  have hNPR : (P:ℚ) < N := by exact_mod_cast hPN
  let x : ℚ := (N:ℚ)*(a:ℚ)/(P:ℚ)
  let y := aqNearestNat N P a
  have hxp : 0 ≤ x+1/2 := by dsimp [x]; positivity
  have hle : (y:ℚ) ≤ x+1/2 := Nat.floor_le hxp
  have hlt : x+1/2 < (y:ℚ)+1 := Nat.lt_floor_add_one _
  have hxN : x+1/2 < (N:ℚ) := by
    change (N:ℚ)*(a:ℚ)/(P:ℚ)+1/2 < N
    rw [← lt_sub_iff_add_lt, div_lt_iff₀ hPR]
    have haR : (a:ℚ)+1 ≤ P := by exact_mod_cast (show a+1 ≤ P by omega)
    have hm := mul_le_mul_of_nonneg_left haR hNR.le
    nlinarith
  have hy : y < N := by exact_mod_cast hle.trans_lt hxN
  have hw : |(y:ℚ)-x| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : (y:ℚ)/(N:ℚ)-(a:ℚ)/(P:ℚ) = ((y:ℚ)-x)/(N:ℚ) := by
    dsimp [x]
    field_simp
  refine ⟨hy, ?_⟩
  rw [he, abs_div, abs_of_pos hNR]
  exact (div_le_div_of_nonneg_right hw hNR.le).trans_eq (by ring)

theorem aqNearest_injective (N P : ℕ) (hP : 0 < P) (hPN : P < N) :
    Function.Injective (aqNearestNat N P) := by
  intro a b hab
  have hNR : (0:ℚ) < N := by exact_mod_cast (show 0 < N by omega)
  have hPR : (0:ℚ) < P := by exact_mod_cast hP
  have hNP : (P:ℚ) < N := by exact_mod_cast hPN
  have hlea : (aqNearestNat N P a:ℚ) ≤ (N:ℚ)*(a:ℚ)/(P:ℚ)+1/2 := Nat.floor_le (by positivity)
  have hlta : (N:ℚ)*(a:ℚ)/(P:ℚ)+1/2 < (aqNearestNat N P a:ℚ)+1 := Nat.lt_floor_add_one _
  have hleb : (aqNearestNat N P b:ℚ) ≤ (N:ℚ)*(b:ℚ)/(P:ℚ)+1/2 := Nat.floor_le (by positivity)
  have hltb : (N:ℚ)*(b:ℚ)/(P:ℚ)+1/2 < (aqNearestNat N P b:ℚ)+1 := Nat.lt_floor_add_one _
  rw [hab] at hlea hlta
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hR : (a:ℚ)+1 ≤ b := by exact_mod_cast (show a+1 ≤ b by omega)
    have hm := mul_le_mul_of_nonneg_left hR hNR.le
    have he : (N:ℚ)*(b:ℚ)/(P:ℚ)-(N:ℚ)*(a:ℚ)/(P:ℚ) < 1 := by linarith
    rw [← sub_div, div_lt_iff₀ hPR] at he
    nlinarith
  · have hR : (b:ℚ)+1 ≤ a := by exact_mod_cast (show b+1 ≤ a by omega)
    have hm := mul_le_mul_of_nonneg_left hR hNR.le
    have he : (N:ℚ)*(a:ℚ)/(P:ℚ)-(N:ℚ)*(b:ℚ)/(P:ℚ) < 1 := by linarith
    rw [← sub_div, div_lt_iff₀ hPR] at he
    nlinarith

theorem aq_good_window_card (N P : ℕ) (hP : 0 < P) (hPN : P < N) :
    Nat.totient P ≤ (aqGoodWindow N P).card := by
  let C : Finset (Fin P) := Finset.univ.filter (fun a => Nat.Coprime a.val P)
  have hc : C.card = Nat.totient P := by
    rw [Nat.totient_eq_card_coprime]
    apply Finset.card_bij (fun a ha => a.val)
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt,
        ((Finset.mem_filter.mp ha).2).symm⟩
    · intro a ha b hb he
      exact Fin.ext he
    · intro a ha
      obtain ⟨haP,hcop⟩ := Finset.mem_filter.mp ha
      exact ⟨⟨a,Finset.mem_range.mp haP⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcop.symm⟩,rfl⟩
  let e : Fin P → Fin N :=
      fun a => ⟨aqNearestNat N P a.val,(aqNearest_bounds N P a.val hP hPN a.isLt).1⟩
  have hinj : Function.Injective e := by
    intro a b h
    exact Fin.ext (aqNearest_injective N P hP hPN (congrArg Fin.val h))
  have hsub : C.image e ⊆ aqGoodWindow N P := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val,a.isLt,(Finset.mem_filter.mp ha).2,
      (aqNearest_bounds N P a.val hP hPN a.isLt).2⟩
  calc
    _ = C.card := hc.symm
    _ = (C.image e).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem aq_good_nonzero (N P : ℕ) (hP : 2 ≤ P) (hPN : P < N)
    (y : Fin N) (hy : y ∈ aqGoodWindow N P) : y.val ≠ 0 := by
  obtain ⟨a,ha,hcop,hw⟩ := (Finset.mem_filter.mp hy).2
  intro hz
  have hap : 0 < a := by
    by_contra h
    have ha0 : a = 0 := by omega
    subst a
    simp only [Nat.coprime_zero_left] at hcop
    omega
  have hNR : (0:ℚ) < N := by exact_mod_cast (show 0 < N by omega)
  have hPR : (0:ℚ) < P := by exact_mod_cast (show 0 < P by omega)
  rw [hz] at hw
  norm_num only [Nat.cast_zero, zero_div, zero_sub, abs_neg] at hw
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ hPR (by positivity)] at hw
  have haR : (1:ℚ) ≤ a := by exact_mod_cast hap
  have hPNR : (P:ℚ) < N := by exact_mod_cast hPN
  nlinarith

theorem amplified_progression_actual_rational_window_mass : ∀ (N : ℕ) (hN : 0< N) (s M P B : ℕ),
  2≤ M → 2≤ P → s+(M-1)*P< N → 2*M≤ N → M*P≤ N → P≤ B → 2*B^2< N →
  0< aqSuccessLower N M P ∧ aqSuccessLower N M P≤
    MeasureProb (aqState N hN M (aqProgressionSet N s M P)) (aqGoodWindow N P) ∧
  Nat.totient P≤(aqGoodWindow N P).card := by
  intro N hN s M P B hM hP hb hMN hMP hPB hsep
  have hPN : P < N := by nlinarith
  have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hDR : (0:ℝ) < (N-M:ℕ) := by exact_mod_cast (show 0 < N-M by omega)
  have hg :=
      (amplified_progression_zero_mode_and_corrected_floor_bounds N hN s M P hM (by omega) hb hMN).2.1
  have ht : (0:ℝ) < Nat.totient P := by exact_mod_cast (Nat.totient_pos.mpr (show 0 < P by omega))
  have hpi : (0:ℝ) < Real.pi^2 := pow_pos Real.pi_pos _
  let L : ℝ := 4*(M:ℝ)*aqGain N M/(Real.pi^2*(N-M:ℕ))
  have hL : 0 < L := by dsimp [L]; positivity
  have hcard := aq_good_window_card N P (by omega) hPN
  have hpoint : ∀ y ∈ aqGoodWindow N P, L ≤ BornProb (aqState N hN M (aqProgressionSet N s M P)) y := by
    intro y hy
    obtain ⟨a,ha,hcop,hw⟩ := (Finset.mem_filter.mp hy).2
    have hn := aq_good_nonzero N P hP hPN y hy
    have hp := (amplified_progression_actual_three_algorithm_probabilities N hN s M P
      (fun x => decide (x ∈ aqProgressionSet N s M P)) y hM (by omega) hb hMN (by intro x; rfl) hn).1
    rw [hp, aq_tan_density N M hN (by omega) hMN]
    have hr := aq_window_root_lower N s M P hN (by omega) (by omega) hMP y a hw
    have hm :=
        mul_le_mul_of_nonneg_left hr (show 0 ≤ (M:ℝ)/(N-M:ℕ)*aqGain N M/(M:ℝ)^2 by positivity)
    calc
      L = ((M:ℝ)/(N-M:ℕ)*aqGain N M/(M:ℝ)^2)*(4*(M:ℝ)^2/Real.pi^2) := by
        dsimp [L]; field_simp
      _ ≤ ((M:ℝ)/(N-M:ℕ)*aqGain N M/(M:ℝ)^2)*Complex.normSq (aqProgressionFourier N s M P y.val) := hm
      _ = _ := by ring
  refine ⟨by unfold aqSuccessLower; positivity, ?_, hcard⟩
  calc
    aqSuccessLower N M P = (Nat.totient P:ℝ)*L := by dsimp [aqSuccessLower,L]; ring
    _ ≤ ((aqGoodWindow N P).card:ℝ)*L := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hL.le
    _ = ∑ y ∈ aqGoodWindow N P, L := by simp
    _ ≤ _ := Finset.sum_le_sum hpoint

end Qatlib.Concepts.AmpTransform.ErrorStream
