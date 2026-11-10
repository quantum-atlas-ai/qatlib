/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmStat
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascadeAux
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.NormNum.RealSqrt
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenWindowBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Papers.VarTimeAmpAmp10.StopModel

set_option autoImplicit false
set_option maxHeartbeats 900000
open Matrix
open scoped Classical BigOperators

variable {C : Type} [Fintype C] [DecidableEq C]

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
noncomputable section

theorem rdvt_odd_step (k : ℕ) (hk : 1 ≤ k) (r : ℝ) :
    (2*(k:ℕ)+1)*r = (2*(k-1:ℕ)+1)*r+2*r := by
  have hkc : ((k-1:ℕ):ℝ)+1 = ((k:ℕ):ℝ) := by
    have h : (k:ℕ)-1+1 = k := by omega
    exact_mod_cast h
  have h2 : (2*((k:ℕ):ℝ)+1)-(2*((k-1:ℕ):ℝ)+1)-2 = 0 := by linarith
  have h3 : (2*(k:ℕ)+1)*r-((2*(k-1:ℕ)+1)*r+2*r)
      = ((2*((k:ℕ):ℝ)+1)-(2*((k-1:ℕ):ℝ)+1)-2)*r := by ring
  have h4 : (2*(k:ℕ)+1)*r-((2*(k-1:ℕ)+1)*r+2*r) = 0 := by
    rw [h3, h2, zero_mul]
  linarith
end
noncomputable section

theorem rdvt_first_quarter (th : ℝ) (h0 : 0 < th) (h1 : th < Real.pi/2) :
    ∃ j : ℕ, Real.pi/4 ≤ (2*(j:ℕ)+1)*th ∧ (2*(j:ℕ)+1)*th ≤ 3*Real.pi/4 ∧
      ∀ j' : ℕ, j' < j → (2*(j' : ℕ)+1)*th < Real.pi/4 := by
  obtain ⟨n, hn⟩ := exists_nat_ge (Real.pi/(4*th))
  have hkey : Real.pi/4 ≤ (n : ℝ)*th := by
    have hm : Real.pi/(4*th)*th ≤ (n : ℝ)*th := mul_le_mul_of_nonneg_right hn h0.le
    have heq : Real.pi/(4*th)*th = Real.pi/4 := by field_simp
    rwa [heq] at hm
  have hexk : ∃ k ≤ n, Real.pi/4 ≤ (2*(k:ℕ)+1)*th := by
    refine ⟨n, le_rfl, ?_⟩
    have hstep : (n : ℝ)*th ≤ (2*(n:ℕ)+1)*th := by
      refine mul_le_mul_of_nonneg_right ?_ h0.le
      linarith
    exact hkey.trans hstep
  obtain ⟨k, hfind, hkN, hP, hmin⟩ :=
    bounded_first_crossing n (fun k => Real.pi/4 ≤ (2*(k:ℕ)+1)*th) hexk
  refine ⟨k, hP, ?_, fun j' hj' => lt_of_not_ge (hmin j' hj')⟩
  by_cases hth : Real.pi/4 ≤ th
  · have hk0 : k = 0 := by
      by_contra hk
      have hcontra : Real.pi/4 ≤ (2*(0:ℕ)+1)*th := by
        rw [show (2*(0:ℕ)+1)*th = th from by norm_num]
        exact hth
      exact hmin 0 (by omega) hcontra
    subst hk0
    have hc : (2*(0:ℕ)+1)*th = th := by norm_num
    rw [hc]
    have h34 : Real.pi/2 ≤ 3*Real.pi/4 := by linarith [Real.pi_pos]
    linarith
  · have hth4 : th < Real.pi/4 := lt_of_not_ge hth
    by_cases hk0 : k = 0
    · subst hk0
      have hc : (2*(0:ℕ)+1)*th = th := by norm_num
      rw [hc]
      have h34 : Real.pi/2 ≤ 3*Real.pi/4 := by linarith [Real.pi_pos]
      linarith
    · have hprev := lt_of_not_ge (hmin (k-1) (by omega))
      have hcalc : (2*(k:ℕ)+1)*th = (2*(k-1:ℕ)+1)*th+2*th := rdvt_odd_step k (by omega) th
      have h2th : 2*th ≤ 2*(Real.pi/4) := by nlinarith [Real.pi_pos]
      rw [hcalc]
      have hsum : (2*(k-1:ℕ)+1)*th+2*th ≤ Real.pi/4+2*(Real.pi/4) :=
        add_le_add (le_of_lt hprev) h2th
      have hsimp : Real.pi/4+2*(Real.pi/4) = 3*Real.pi/4 := by ring
      linarith
end
noncomputable section

theorem rdvt_final_crossing_exists {m : ℕ} (hm : 1 ≤ m) (est : ℝ)
    (h0 : 1/(2*10^12*(m : ℝ)^3) ≤ est) (h1 : est < 1) :
    ∃ k ≤ recordDrivenRoundCap m,
      1/2 ≤ (Real.sin ((2*(k:ℕ)+1)*Real.arcsin (Real.sqrt est)))^2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hest0 : 0 < est := lt_of_lt_of_le (by positivity) h0
  have hest1 : est ≤ 1 := le_of_lt h1
  set th : ℝ := Real.arcsin (Real.sqrt est) with hthd
  have hth0 : 0 < th := Real.arcsin_pos.2 (Real.sqrt_pos.mpr hest0)
  have hth1 : th < Real.pi/2 := Real.arcsin_lt_pi_div_two.2
    ((Real.sqrt_lt' (by norm_num)).2 (by linarith))
  have hthge : Real.sqrt est ≤ th := by
    have hsin := Real.sin_le ((Real.arcsin_nonneg).2 (Real.sqrt_nonneg est))
    rwa [Real.sin_arcsin (by linarith [Real.sqrt_nonneg est]) (by
      exact (Real.sqrt_le_sqrt hest1).trans (by norm_num))] at hsin
  obtain ⟨j, hj1, hj2, hj3⟩ := rdvt_first_quarter th hth0 hth1
  refine ⟨j, ?_, rdvt_sin_sq_ge_of_window hj1 hj2⟩
  by_cases hj : j = 0
  · subst hj
    exact Nat.zero_le _
  · have hprev : (2*(j-1:ℕ)+1)*th < Real.pi/4 := hj3 (j-1) (by omega)
    have hsq : Real.sqrt (2*10^12*(m : ℝ)^3) ≤ 2000000*(m : ℝ)^2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have hm4 : (m : ℝ)^3 ≤ (m : ℝ)^4 := pow_le_pow_right₀ hm' (by norm_num)
      have hmono : 2*10^12*(m : ℝ)^3 ≤ 4*10^12*(m : ℝ)^4 := by
        have hA : 2*10^12*(m : ℝ)^3 ≤ 2*10^12*(m : ℝ)^4 :=
          mul_le_mul_of_nonneg_left hm4 (by norm_num : (0:ℝ) ≤ 2*10^12)
        have hB : 2*10^12*(m : ℝ)^4 ≤ 4*10^12*(m : ℝ)^4 := by
          have heq : 4*10^12*(m : ℝ)^4 = 2*10^12*(m : ℝ)^4+2*10^12*(m : ℝ)^4 := by ring
          have hnn : (0:ℝ) ≤ 2*10^12*(m : ℝ)^4 := by positivity
          linarith
        exact hA.trans hB
      have he : (2000000*(m : ℝ)^2)^2 = 4*10^12*(m : ℝ)^4 := by
        norm_num
        ring
      rw [he]
      exact hmono
    have hinv : 1/th ≤ 2000000*(m : ℝ)^2 := by
      have h1a : (1:ℝ) ≤ th*Real.sqrt (2*10^12*(m : ℝ)^3) := by
        have hestmul : (1:ℝ) ≤ est*(2*10^12*(m : ℝ)^3) := (div_le_iff₀ (by positivity)).mp h0
        have hprod : Real.sqrt (est*(2*10^12*(m : ℝ)^3))
            = Real.sqrt est*Real.sqrt (2*10^12*(m : ℝ)^3) :=
          Real.sqrt_mul (le_of_lt hest0) _
        calc (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
          _ ≤ Real.sqrt (est*(2*10^12*(m : ℝ)^3)) := Real.sqrt_le_sqrt hestmul
          _ = Real.sqrt est*Real.sqrt (2*10^12*(m : ℝ)^3) := hprod
          _ ≤ th*Real.sqrt (2*10^12*(m : ℝ)^3) :=
              mul_le_mul_of_nonneg_right hthge (Real.sqrt_nonneg _)
      rw [div_le_iff₀ hth0]
      calc (1:ℝ) ≤ th*Real.sqrt (2*10^12*(m : ℝ)^3) := h1a
        _ ≤ th*(2000000*(m : ℝ)^2) := mul_le_mul_of_nonneg_left hsq (le_of_lt hth0)
        _ = 2000000*(m : ℝ)^2*th := by ring
    have hXle : (2*((j-1:ℕ):ℝ)+1) < (Real.pi/4)/th := (lt_div_iff₀ hth0).mpr hprev
    have hjc : ((j-1:ℕ):ℝ)+1 = ((j:ℕ):ℝ) := by
      have h : (j:ℕ)-1+1 = j := by omega
      exact_mod_cast h
    have hpre : ((j:ℕ):ℝ) < Real.pi/(8*th)+1 := by
      have htop : 2*((j:ℕ):ℝ) < (Real.pi/4)/th+2 := by linarith
      have heq : ((Real.pi/4)/th+2)/2 = Real.pi/(8*th)+1 := by
        field_simp
        ring
      have hhalf : ((j:ℕ):ℝ) < ((Real.pi/4)/th+2)/2 := by linarith
      rwa [heq] at hhalf
    have hpinv : Real.pi/(8*th) ≤ 1000000*(m : ℝ)^2 := by
      have hq : Real.pi/8 ≤ 1/2 := by linarith [Real.pi_lt_four.le]
      have hthpos : (0:ℝ) < 1/th := by positivity
      have hcalc : Real.pi/(8*th) = (Real.pi/8)*(1/th) := by
        field_simp
      rw [hcalc]
      have hhalf : (Real.pi/8)*(1/th) ≤ (1/2)*(1/th) :=
        mul_le_mul_of_nonneg_right hq hthpos.le
      refine hhalf.trans ?_
      linarith
    have hjle : ((j:ℕ):ℝ) ≤ 1000000*(m : ℝ)^2+1 := by linarith
    have hm0R : (0:ℝ) ≤ m := by linarith
    have hm21 : (1:ℝ) ≤ (m : ℝ)^2 := by
      nlinarith [hm', mul_nonneg hm0R (by linarith : (0:ℝ) ≤ m-1)]
    have hdiff : (1:ℝ) ≤ 999000000*(m : ℝ)^2 := by
      have h1 : (999000000:ℝ)*1 ≤ 999000000*(m : ℝ)^2 :=
        mul_le_mul_of_nonneg_left hm21 (by norm_num : (0:ℝ) ≤ 999000000)
      have h2 : (999000000:ℝ)*1 = 999000000 := by ring
      have h3 : (1:ℝ) ≤ 999000000 := by norm_num
      linarith
    have hcap : ((j:ℕ):ℝ) ≤ (recordDrivenRoundCap m : ℝ) := by
      have hfin : 1000000*(m : ℝ)^2+1 ≤ 1000000000*(m : ℝ)^2 := by
        have heq : 1000000*(m : ℝ)^2+999000000*(m : ℝ)^2 = 1000000000*(m : ℝ)^2 := by ring
        linarith
      calc ((j:ℕ):ℝ) ≤ 1000000*(m : ℝ)^2+1 := hjle
        _ ≤ 1000000000*(m : ℝ)^2 := hfin
        _ = (recordDrivenRoundCap m : ℝ) := by
            unfold recordDrivenRoundCap
            push_cast
            ring
    exact_mod_cast hcap
end
noncomputable section

theorem rdvt_final_mult_bound {est : ℝ} {k : ℕ} (h0 : 0 < est) (h1 : est < 1/2) (hk : 1 ≤ k)
    (hmin : ∀ j : ℕ, j < k →
      (Real.sin ((2*(j:ℕ)+1)*Real.arcsin (Real.sqrt est)))^2 < 1/2) :
    (2*(k:ℕ)+1)*Real.sqrt est ≤ 10/3 := by
  have hest1 : est ≤ 1 := by linarith
  set th : ℝ := Real.arcsin (Real.sqrt est) with hthd
  have hth0 : 0 < th := Real.arcsin_pos.2 (Real.sqrt_pos.mpr h0)
  have hthge : Real.sqrt est ≤ th := by
    have hsin := Real.sin_le ((Real.arcsin_nonneg).2 (Real.sqrt_nonneg est))
    rwa [Real.sin_arcsin (by linarith [Real.sqrt_nonneg est]) (by
      exact (Real.sqrt_le_sqrt hest1).trans (by norm_num))] at hsin
  have hth4 : th < Real.pi/4 := by
    have hlt : Real.sqrt est < Real.sin (Real.pi/4) := by
      rw [Real.sin_pi_div_four]
      have hlt2 : Real.sqrt est < Real.sqrt 2/2 := by
        apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < Real.sqrt 2/2)).2
        rw [show (Real.sqrt 2/2)^2 = 1/2 from by
          rw [div_pow, Real.sq_sqrt (by positivity)]
          norm_num]
        exact h1
      exact hlt2
    have hy1 : Real.sin (Real.pi/4) ≤ 1 := by
      rw [Real.sin_pi_div_four]
      have hs2 : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 4)).trans_eq
        (by norm_num)
      have h2 : Real.sqrt 2/2 ≤ 1 := by
        apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).2
        nlinarith [hs2]
      exact h2
    have harc := Real.arcsin_lt_arcsin (by linarith [Real.sqrt_nonneg est]) hlt hy1
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at harc
  obtain ⟨j, hj1, hj2, hj3⟩ := rdvt_first_quarter th hth0 (by linarith [Real.pi_pos])
  have hkj : k ≤ j := by
    by_contra hcon
    have hwin := rdvt_sin_sq_ge_of_window hj1 hj2
    have hcontra := hmin j (by omega)
    linarith
  have hprev : (2*(k-1:ℕ)+1)*th < Real.pi/4 := by
    have hjprev := hj3 (k-1) (by omega)
    exact hjprev
  have hsplit : (2*(k:ℕ)+1)*th = (2*(k-1:ℕ)+1)*th+2*th := rdvt_odd_step k hk th
  have h2th : 2*th ≤ 2*(Real.pi/4) := by nlinarith [Real.pi_pos]
  have htotal : (2*(k:ℕ)+1)*th ≤ 3*Real.pi/4 := by
    rw [hsplit]
    have hsum : (2*(k-1:ℕ)+1)*th+2*th ≤ Real.pi/4+2*(Real.pi/4) :=
      add_le_add (le_of_lt hprev) h2th
    have hsimp : Real.pi/4+2*(Real.pi/4) = 3*Real.pi/4 := by ring
    linarith
  calc (2*(k:ℕ)+1)*Real.sqrt est ≤ (2*(k:ℕ)+1)*th :=
        mul_le_mul_of_nonneg_left hthge (by positivity)
    _ ≤ 3*Real.pi/4 := htotal
    _ ≤ 3 := by linarith [Real.pi_lt_four.le]
    _ ≤ 10/3 := by norm_num
end
noncomputable section

theorem rdvt_cascade_time_unroll (sched : ℕ → ℕ) :
    ∀ j : ℕ, (dataVtWordTime (cascadeWord sched j) : ℝ) =
      ∑ i ∈ Finset.Ico 0 j, (2:ℝ)^i*∏ k ∈ Finset.Ico i j, ((2*(sched k)+1 : ℕ) : ℝ) := by
  intro j
  induction j with
  | zero => simp [cascadeWord, dataVtWordTime]
  | succ j ih =>
    have h1 : (dataVtWordTime (cascadeWord sched (j+1)) : ℝ)
        = ((2*(sched j)+1 : ℕ) : ℝ)*((dataVtWordTime (cascadeWord sched j) : ℝ)+(2:ℝ)^j) := by
      rw [cascadeWord_time sched j]
      push_cast
      ring
    rw [h1, ih, Finset.sum_Ico_succ_top (Nat.zero_le j)]
    have hprod : ∀ i ∈ Finset.Ico 0 j,
        ∏ k ∈ Finset.Ico i (j+1), ((2*(sched k)+1 : ℕ) : ℝ)
          = (∏ k ∈ Finset.Ico i j, ((2*(sched k)+1 : ℕ) : ℝ))*((2*(sched j)+1 : ℕ) : ℝ) :=
      fun i hi => Finset.prod_Ico_succ_top (Finset.mem_Ico.mp hi).2.le _
    have hsing : ∏ k ∈ Finset.Ico j (j+1), ((2*(sched k)+1 : ℕ) : ℝ)
        = ((2*(sched j)+1 : ℕ) : ℝ) := by
      rw [Finset.prod_Ico_succ_top (le_refl j), Finset.Ico_self, Finset.prod_empty, one_mul]
    have hrw : ∀ i ∈ Finset.Ico 0 j,
        (2:ℝ)^i*∏ k ∈ Finset.Ico i (j+1), ((2*(sched k)+1 : ℕ) : ℝ)
          = ((2:ℝ)^i*∏ k ∈ Finset.Ico i j, ((2*(sched k)+1 : ℕ) : ℝ))*((2*(sched j)+1 : ℕ) : ℝ) := by
      intro i hi
      rw [hprod i hi]
      ring
    rw [Finset.sum_congr rfl (fun i hi => hrw i hi), hsing, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · ring

end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
