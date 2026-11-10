/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments
import Mathlib.Analysis.SpecificLimits.Basic
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.AmpTransform.NoiseMoments

namespace Qatlib.Concepts.SpectralReadout.NoiseStatistics
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def noiseTupleDist (N L : ℕ) [NeZero N] : FinDist (Fin L→ZMod N) where
  prob _ := ((N : ℝ)^L)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const,Finset.card_univ,noise_tuple_card,nsmul_eq_mul,Nat.cast_pow]
    exact mul_inv_cancel₀ (pow_ne_zero L (by exact_mod_cast NeZero.ne N))

theorem noise_intensity_resonance_safe_bounds_vanish : ∀ (M : ℕ),
    Filter.Tendsto (fun L : ℕ => ((M : ℝ)^2+L)/((M+L : ℕ) : ℝ)^2)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun L : ℕ => (2*((L : ℝ)^2-L)+4*(M : ℝ)^2*L)/((M+L : ℕ) : ℝ)^4)
      Filter.atTop (nhds 0) := by
  intro M
  have hi : Filter.Tendsto (fun L : ℕ => (L : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmean : Filter.Tendsto (fun L : ℕ => (M : ℝ)^2*((L : ℝ)⁻¹)^2+(L : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using ((hi.pow 2).const_mul ((M : ℝ)^2)).add hi
  have hvar : Filter.Tendsto (fun L : ℕ => 2*((L : ℝ)⁻¹)^2+4*(M : ℝ)^2*((L : ℝ)⁻¹)^3)
      Filter.atTop (nhds 0) := by
    simpa using ((hi.pow 2).const_mul 2).add ((hi.pow 3).const_mul (4*(M : ℝ)^2))
  constructor
  · apply squeeze_zero' _ _ hmean
    · exact Filter.Eventually.of_forall (fun L => by positivity)
    · filter_upwards [Filter.eventually_ge_atTop 1] with L hL
      have hLp : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
      have hLT : (L : ℝ) ≤ ((M+L : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left L M
      calc
        _ ≤ ((M : ℝ)^2+L)/(L : ℝ)^2 := div_le_div_of_nonneg_left (by positivity)
          (pow_pos hLp 2) (pow_le_pow_left₀ hLp.le hLT 2)
        _ = _ := by field_simp
  · apply squeeze_zero' _ _ hvar
    · filter_upwards [Filter.eventually_ge_atTop 1] with L hL
      have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hs : 0 ≤ (L : ℝ)^2-L := by nlinarith
      exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) hs) (by positivity)) (by positivity)
    · filter_upwards [Filter.eventually_ge_atTop 1] with L hL
      have hLp : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
      have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hLT : (L : ℝ) ≤ ((M+L : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left L M
      have hs : 0 ≤ (L : ℝ)^2-L := by nlinarith
      calc
        _ ≤ (2*((L : ℝ)^2-L)+4*(M : ℝ)^2*L)/(L : ℝ)^4 :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos hLp 4)
            (pow_le_pow_left₀ hLp.le hLT 4)
        _ ≤ (2*(L : ℝ)^2+4*(M : ℝ)^2*L)/(L : ℝ)^4 :=
          div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by field_simp

theorem noise_order_two_variance_counterexample :
    let S := fun omega : Fin 2→ZMod 2 => ∑ i,ZMod.stdAddChar (omega i);
    ((2 : ℝ)^2)⁻¹*(∑ omega,‖S omega‖^2)=2 ∧
    ((2 : ℝ)^2)⁻¹*(∑ omega,(‖S omega‖^2-2)^2)=4 ∧
    (4 : ℝ) ≠ (2 : ℝ)^2-2 := by
  (try dsimp only)
  have h1 := (noise_sequence_second_moment 2 2 (1 : ZMod 2) 0 1 (by decide)).1
  have h2 := noise_sequence_variance_corrected 2 2 (1 : ZMod 2) 0 1 (by decide)
  have hr : (2 : ZMod 2)*(1 : ZMod 2)=0 := by decide
  dsimp only at h2
  rw [if_pos hr] at h2
  norm_num at h1 h2
  norm_num [Fin.sum_univ_two]
  exact ⟨h1,h2⟩

theorem noise_expect_uniform (N L : ℕ) [NeZero N] (p : FinDist (Fin L→ZMod N))
    (hp : ∀ omega,p.prob omega=((N : ℝ)^L)⁻¹) (f : (Fin L→ZMod N)→ℝ) :
    p.expect f=((N : ℝ)^L)⁻¹*∑ omega,f omega := by
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,hp,← Finset.mul_sum]

theorem noise_length_square_sub_nonneg (L : ℕ) : 0 ≤ (L : ℝ)^2-L := by
  cases L with
  | zero => norm_num
  | succ L =>
    have h : (1 : ℝ) ≤ (L+1 : ℕ) := by exact_mod_cast (show 1 ≤ L+1 by omega)
    nlinarith

theorem noise_shift_variance_upper (L M : ℕ) (c : ℂ) (hc : ‖c‖ ≤ M) (delta : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    ((L : ℝ)^2-L)+delta*((L : ℝ)^2-L)+2*(L : ℝ)*‖c‖^2+
      2*(L : ℝ)*(c^2).re*delta ≤ 2*((L : ℝ)^2-L)+4*(M : ℝ)^2*L := by
  have hbase := noise_length_square_sub_nonneg L
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hn : ‖c‖^2 ≤ (M : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hr : (c^2).re ≤ ‖c‖^2 := (Complex.re_le_norm (c^2)).trans_eq (Complex.norm_pow c 2)
  have hdeltaBase : delta*((L : ℝ)^2-L) ≤ (L : ℝ)^2-L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hbase
  have hrD : (c^2).re*delta ≤ ‖c‖^2 := by
    calc
      _ ≤ ‖c‖^2*delta := mul_le_mul_of_nonneg_right hr hd0
      _ ≤ ‖c‖^2*1 := mul_le_mul_of_nonneg_left hd1 (sq_nonneg _)
      _ = _ := mul_one _
  have hh1 := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*(L : ℝ) by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hrD (show 0 ≤ 2*(L : ℝ) by positivity)
  nlinarith

theorem noise_intensity_actual_fresh_mean_concentration :
    ∀ (N L M K : ℕ) [NeZero N] (y : ZMod N) (c : ℂ)
      (p : FinDist (Fin L→ZMod N)) (eps : ℝ),
    y≠0 → 0 < M+L → ‖c‖ ≤ M → 0 < K → 0 < eps →
    (∀ omega,p.prob omega=((N : ℝ)^L)⁻¹) →
    let F := fun omega : Fin L→ZMod N =>
      ‖c+∑ i,ZMod.stdAddChar (omega i*y)‖^2/((M+L : ℕ) : ℝ)^2;
    let mu := (‖c‖^2+(L : ℝ))/((M+L : ℕ) : ℝ)^2;
    p.expect F=mu ∧
    p.variance F ≤ (2*((L : ℝ)^2-L)+4*(M : ℝ)^2*L)/((M+L : ℕ) : ℝ)^4 ∧
    p.probEvent (fun omega : Fin K→(Fin L→ZMod N) =>
      eps < |(∑ j,F (omega j))/(K : ℝ)-mu|) ≤
      (2*((L : ℝ)^2-L)+4*(M : ℝ)^2*L)/(((M+L : ℕ) : ℝ)^4*(K : ℝ)*eps^2) ∧
    ∀ omega,0 ≤ F omega ∧ F omega ≤ 1 := by
  intro N L M K _ y c p eps hy hT hc hK heps hp
  (try dsimp only)
  let A := fun omega : Fin L→ZMod N => ‖c+∑ i,ZMod.stdAddChar (omega i*y)‖^2
  let T : ℝ := (M+L : ℕ)
  let mu0 : ℝ := ‖c‖^2+(L : ℝ)
  let F := fun omega => A omega/T^2
  have hTp : 0 < T := by
    change (0 : ℝ) < ((M+L : ℕ) : ℝ)
    exact_mod_cast hT
  have hmean0 : ((N : ℝ)^L)⁻¹*(∑ omega,A omega)=mu0 := by
    simpa only [Complex.ofReal_one,one_mul,one_pow] using
        (noise_sequence_second_moment N L y c 1 hy).2
  have hmean : p.expect F=mu0/T^2 := by
    rw [noise_expect_uniform N L p hp]
    dsimp only [F]
    rw [← Finset.sum_div]
    rw [← mul_div_assoc,hmean0]
  have hv0 := noise_sequence_variance_corrected N L y c 1 hy
  simp only [Complex.ofReal_one,one_mul,mul_one,one_pow] at hv0
  have hv : p.variance F ≤ (2*((L : ℝ)^2-L)+4*(M : ℝ)^2*L)/T^4 := by
    rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance,hmean,noise_expect_uniform N L p hp]
    have he (omega : Fin L→ZMod N) : (F omega-mu0/T^2)^2=(A omega-mu0)^2/T^4 := by
      dsimp only [F]
      rw [← sub_div,div_pow]
      ring
    simp_rw [he]
    rw [← Finset.sum_div,← mul_div_assoc,hv0]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact noise_shift_variance_upper L M c hc (if 2*y=0 then 1 else 0)
      (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
  refine ⟨hmean,hv,?_,?_⟩
  · have hcheb := p.chebyshev_avg F hK eps heps
    rw [hmean] at hcheb
    apply hcheb.trans
    exact (div_le_div_of_nonneg_right hv (by positivity)).trans_eq (by dsimp only [T];field_simp)
  · intro omega
    have hsum : ‖∑ i : Fin L,ZMod.stdAddChar (omega i*y)‖ ≤ (L : ℝ) := by
      simpa only [norm_stdAddChar,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
        norm_sum_le Finset.univ (fun i : Fin L => ZMod.stdAddChar (omega i*y))
    have hnorm : ‖c+∑ i,ZMod.stdAddChar (omega i*y)‖ ≤ T :=
      (norm_add_le _ _).trans ((add_le_add hc hsum).trans_eq (by dsimp [T];push_cast;rfl))
    refine ⟨by positivity,(div_le_one (pow_pos hTp 2)).mpr ?_⟩
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem noise_intensity_n3_actual_fresh_consumer (eps : ℝ) (heps : 0 < eps) :
    let p := noiseTupleDist 3 2;
    let F := fun omega : Fin 2→ZMod 3 => ‖(1 : ℂ)+∑ i,ZMod.stdAddChar (omega i)‖^2/9;
    p.expect F=1/3 ∧ p.variance F ≤ 4/27 ∧
    p.probEvent (fun omega : Fin 4→(Fin 2→ZMod 3) =>
      eps < |(∑ j,F (omega j))/4-1/3|) ≤ 1/(27*eps^2) := by
  (try dsimp only)
  simp only [Fin.sum_univ_two]
  have h := noise_intensity_actual_fresh_mean_concentration 3 2 1 4 (1 : ZMod 3)
    (1 : ℂ) (noiseTupleDist 3 2) eps (by decide) (by decide) (by norm_num) (by decide) heps (fun _ => rfl)
  norm_num at h
  refine ⟨h.1,h.2.1,?_⟩
  convert h.2.2.1 using 1
  field_simp
  ring

end Qatlib.Concepts.SpectralReadout.NoiseStatistics
