/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineCoordinateReadoutStat
import Qatlib.Concepts.GradientOracle.ReadoutTools.ExceptionalPhaseGradientTransportOpti
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.UniformHHL

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Matrix
open scoped Classical BigOperators

namespace AlmostAffineCoordinateReadoutAux

theorem signed_decode_third (M : ℕ) (hM : 0 < M) (z : Fin M)
    (g w : ℝ) (hg : |g| ≤ 1/3) (hw : w ≤ 1/8)
    (hgood : phaseDistance ((z.val:ℝ)/(M:ℝ)) g ≤ w) :
    |signedGridValue M z-g| ≤ w := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  let a : ℝ := z.val/(M:ℝ)
  let n : ℤ := ⌊a-g+1/2⌋
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one hMr).mpr
    exact_mod_cast z.isLt
  have hg' := abs_le.mp hg
  have hnlo := Int.floor_le (a-g+1/2)
  have hnhi := Int.lt_floor_add_one (a-g+1/2)
  change |a-g-(n:ℝ)| ≤ w at hgood
  have hgood' := abs_le.mp hgood
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by
    have hn : (-1:ℝ) < (n:ℝ) := by dsimp [n]; linarith
    have hint : (-1:ℤ) < n := by exact_mod_cast hn
    exact_mod_cast (show 0 ≤ n by omega)
  have hn1 : (n:ℝ) ≤ 1 := by
    have hn : (n:ℝ) < 2 := by dsimp [n]; linarith
    have hi : n < 2 := by exact_mod_cast hn
    exact_mod_cast (show n ≤ 1 by omega)
  have hn : n = 0 ∨ n = 1 := by
    have h0 : 0 ≤ n := by exact_mod_cast hn0
    have h1 : n ≤ 1 := by exact_mod_cast hn1
    omega
  unfold signedGridValue
  split_ifs with hz
  · have ha : a ≤ 1/2 := by
      apply (div_le_iff₀ hMr).mpr
      have hz' : 2*(z.val:ℝ) ≤ (M:ℝ) := by exact_mod_cast hz
      linarith
    rcases hn with hn | hn
    · simpa [hn, a] using! hgood
    · rw [hn] at hgood'
      norm_num at hgood'
      linarith
  · have ha : 1/2 < a := by
      dsimp [a]
      apply (lt_div_iff₀ hMr).mpr
      have hz' : (M:ℝ) < 2*(z.val:ℝ) := by exact_mod_cast (show M < 2*z.val by omega)
      linarith
    rcases hn with hn | hn
    · rw [hn] at hgood'
      norm_num at hgood'
      linarith
    · simpa [hn, a, sub_sub, add_comm] using! hgood

theorem signedGridValue_abs_le (M : ℕ) (hM : 0 < M) (z : Fin M) :
    |signedGridValue M z| ≤ 1/2 := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hzlt : (z.val : ℝ)/(M : ℝ) < 1 := by
    apply (div_lt_one hMr).mpr
    exact_mod_cast z.isLt
  have hz0 : (0 : ℝ) ≤ (z.val : ℝ)/(M : ℝ) := by positivity
  unfold signedGridValue
  split_ifs with h
  · have hle : (z.val : ℝ)/(M : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ hMr).mpr
      have h' : 2*(z.val:ℝ) ≤ (M:ℝ) := by exact_mod_cast h
      linarith
    rw [abs_of_nonneg hz0]
    linarith
  · have hle : (1:ℝ)/2 ≤ (z.val : ℝ)/(M : ℝ) := by
      apply (le_div_iff₀ hMr).mpr
      have h' : (M:ℝ) < 2*(z.val:ℝ) := by exact_mod_cast (show M < 2*z.val by omega)
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem gridProductState_marginal {d M : ℕ} (v : Fin d → QState (Fin M))
    (hvn : ∀ k, ∑ y, ‖v k y‖^2 = 1) (j : Fin d) (P : Fin M → Prop) [DecidablePred P] :
    MeasureProb (gridProductState v) (Finset.univ.filter fun z => P (z j))
      = ∑ y ∈ Finset.univ.filter P, ‖v j y‖^2 := by
  classical
  set t : Fin d → Finset (Fin M) := fun k => if k = j then Finset.univ.filter P else Finset.univ with ht
  have he : (Finset.univ.filter fun z : Fin d → Fin M => P (z j)) = Fintype.piFinset t := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    by_cases hzj : P (z j)
    · refine ⟨fun _ k => ?_, fun _ => hzj⟩
      by_cases h : k = j
      · subst h
        simpa only [ht, if_pos rfl, Finset.mem_filter, Finset.mem_univ, true_and] using!
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj⟩
      · simpa only [ht, if_neg h] using! Finset.mem_univ (z k)
    · refine ⟨fun h k => ?_, fun h => ?_⟩
      · by_cases hkj : k = j
        · subst hkj
          simpa only [ht, if_pos rfl, Finset.mem_filter, Finset.mem_univ, true_and] using!
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        · simpa only [ht, if_neg hkj] using! Finset.mem_univ (z k)
      · have hj : z j ∈ t j := h j
        simp only [ht, if_pos rfl, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj
  rw [he]
  simp only [MeasureProb, BornProb, gridProductState, norm_prod, ← Finset.prod_pow]
  rw [← Finset.prod_univ_sum t fun k y => ‖v k y‖^2]
  have hsum : ∀ k : Fin d, ∑ y ∈ t k, ‖v k y‖^2
      = if k = j then ∑ y ∈ Finset.univ.filter P, ‖v k y‖^2 else 1 := by
    intro k
    by_cases hkj : k = j
    · subst hkj; simp [ht]
    · rw [if_neg hkj]
      simp only [ht, if_neg hkj]
      exact hvn k
  rw [Finset.prod_congr rfl fun k _ => hsum k]
  simp

end AlmostAffineCoordinateReadoutAux
open Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineCoordinateReadoutAux
set_option warningAsError false

theorem almostAffineCoordinateReadout : AlmostAffineCoordinateReadout := by
  intro d n hN φ g c S hg hbad hgood
  refine ⟨?_, (gradient_coordinate_qft_word_unitarity d (2^n) hN).1,
    (gradient_coordinate_qft_word_unitarity d (2^n) hN).2.1,
    (gradient_coordinate_qft_word_unitarity d (2^n) hN).2.2⟩
  intro j
  have hcast : (((2^n : ℕ) : ℝ)) = (2:ℝ)^n := by
    push_cast
    ring
  have hbad' : ((Finset.univ \ S).card : ℝ) ≤ (1/1000)*(((2^n : ℕ) : ℝ))^d := by
    rw [hcast]
    linarith
  have hG2 := exceptionalPhaseGradientTransport d (2^n) hN φ
    (fun x : GradientGrid d (2^n) => c+∑ k, g k*(x k).val) S (1/(42*Real.pi)) (1/1000)
    (by positivity) (by norm_num) hbad' hgood
  obtain ⟨hnormφ, hnormψ, hL2, hev⟩ := hG2
  have hvn : ∀ k, ∑ y, ‖qpeKernel (2^n) (g k) y‖^2 = 1 :=
    fun k => uniform_qpeKernel_normalized (2^n) (g k) hN
  have hmarg : MeasureProb (gradientReadout d (2^n) hN
      (fun x : GradientGrid d (2^n) => c+∑ k, g k*(x k).val))
      (Finset.univ.filter fun z : GradientGrid d (2^n) =>
        |signedGridValue (2^n) (z j) - g j| ≤ 4/(2:ℝ)^n)
      = ∑ y ∈ Finset.univ.filter
        (fun y : Fin (2^n) => |signedGridValue (2^n) y - g j| ≤ 4/(2:ℝ)^n),
        ‖qpeKernel (2^n) (g j) y‖^2 := by
    rw [gradient_offgrid_actual_readout d (2^n) hN g c]
    have hsmul : MeasureProb (Complex.exp (2*Real.pi*Complex.I*(c:ℂ)) •
        (gridProductState fun k => qpeKernel (2^n) (g k)))
        (Finset.univ.filter fun z : GradientGrid d (2^n) =>
          |signedGridValue (2^n) (z j) - g j| ≤ 4/(2:ℝ)^n)
        = MeasureProb (gridProductState fun k => qpeKernel (2^n) (g k))
          (Finset.univ.filter fun z : GradientGrid d (2^n) =>
            |signedGridValue (2^n) (z j) - g j| ≤ 4/(2:ℝ)^n) := by
      simp only [MeasureProb, BornProb, Pi.smul_apply, smul_eq_mul, norm_mul,
        norm_exp_two_pi_I, one_mul]
    rw [hsmul]
    exact gridProductState_marginal _ hvn j
      (fun y : Fin (2^n) => |signedGridValue (2^n) y - g j| ≤ 4/(2:ℝ)^n)
  have hloss : Real.sqrt ((2*Real.pi*(1/(42*Real.pi)))^2+4*(1/1000 : ℝ)) ≤ 1/12 := by
    have heq : (2*Real.pi*(1/(42*Real.pi)))^2 = 1/441 := by
      field_simp
      ring
    rw [heq]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have habs := (abs_le.mp (hev (Finset.univ.filter fun z : GradientGrid d (2^n) =>
    |signedGridValue (2^n) (z j) - g j| ≤ 4/(2:ℝ)^n))).1
  by_cases hn3 : 3 ≤ n
  · have hN8 : (8:ℝ) ≤ (2:ℝ)^n := by
      have h1 : ((2:ℕ)^3 : ℝ) ≤ ((2:ℕ)^n : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : (1:ℕ) ≤ 2) hn3
      have h2 : ((2:ℕ)^3 : ℝ) = 8 := by norm_num
      have h3 : ((2:ℕ)^n : ℝ) = (2:ℝ)^n := by push_cast; ring
      linarith
    have h2N : (2:ℕ) ≤ 2^n := Nat.pow_le_pow_right (by norm_num : (1:ℕ) ≤ 2) (show 1 ≤ n by omega)
    have h1le : (1:ℝ)/((2^n : ℕ) : ℝ) = 1/(2:ℝ)^n := by rw [hcast]
    have hwin : Finset.univ.filter
        (fun y : Fin (2^n) =>
          phaseDistance (g j) ((y.val : ℝ)/((2^n : ℕ) : ℝ)) ≤ 1/((2^n : ℕ) : ℝ))
        ⊆ Finset.univ.filter
        (fun y : Fin (2^n) => |signedGridValue (2^n) y - g j| ≤ 4/(2:ℝ)^n) := by
      intro z hz
      have hz2 : phaseDistance ((z.val : ℝ)/((2^n : ℕ) : ℝ)) (g j) ≤ 1/(2:ℝ)^n := by
        rw [gradient_phaseDistance_comm]
        exact ((Finset.mem_filter.mp hz).2).trans_eq h1le
      have hw : 1/(2:ℝ)^n ≤ 1/8 := by
        apply (div_le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^n) (by norm_num)).mpr
        linarith
      have h4 : 1/(2:ℝ)^n ≤ 4/(2:ℝ)^n := by
        apply (div_le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^n)
          (by positivity : (0:ℝ) < (2:ℝ)^n)).mpr
        norm_num
      have hd := signed_decode_third (2^n) hN z (g j) (1/(2:ℝ)^n) (hg j) hw hz2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.trans h4⟩
    have hkernel := offgrid_phase_window_probability (2^n) (g j) h2N
    have hmargLB : 8/Real.pi^2 ≤ ∑ y ∈ Finset.univ.filter
        (fun y : Fin (2^n) => |signedGridValue (2^n) y - g j| ≤ 4/(2:ℝ)^n),
        ‖qpeKernel (2^n) (g j) y‖^2 :=
      hkernel.ge.trans (Finset.sum_le_sum_of_subset_of_nonneg hwin fun _ _ _ => by positivity)
    have h83 : (3:ℝ)/4 ≤ 8/Real.pi^2 := by
      have hpi := Real.pi_lt_d4
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by positivity)]
      nlinarith [Real.pi_pos, hpi]
    linarith
  · have hN4 : (2:ℝ)^n ≤ 4 := by
      have h1 : ((2:ℕ)^n : ℝ) ≤ ((2:ℕ)^2 : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : (1:ℕ) ≤ 2) (by omega : n ≤ 2)
      have h3 : ((2:ℕ)^n : ℝ) = (2:ℝ)^n := by push_cast; ring
      have h4 : ((2:ℕ)^2 : ℝ) = 4 := by norm_num
      linarith
    have hmall : Finset.univ.filter
        (fun y : Fin (2^n) => |signedGridValue (2^n) y - g j| ≤ 4/(2:ℝ)^n)
        = Finset.univ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h12 : |signedGridValue (2^n) y - g j|
          ≤ |signedGridValue (2^n) y| + |g j| := by
        refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [le_abs_self (signedGridValue (2^n) y),
          le_abs_self (g j), (abs_le.mp (le_refl (|g j|))).1,
          (abs_le.mp (le_refl (|signedGridValue (2^n) y|))).1]
      have h12' : |signedGridValue (2^n) y - g j| ≤ 1/2 + 1/3 :=
        h12.trans (add_le_add (signedGridValue_abs_le (2^n) hN y) (hg j))
      have h43 : (1:ℝ) ≤ 4/(2:ℝ)^n := by
        apply (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^n)).mpr
        linarith
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      linarith
    have hmargLB : (1:ℝ) ≤ ∑ y ∈ Finset.univ.filter
        (fun y : Fin (2^n) => |signedGridValue (2^n) y - g j| ≤ 4/(2:ℝ)^n),
        ‖qpeKernel (2^n) (g j) y‖^2 := by
      rw [hmall]
      exact (hvn j).ge
    linarith

end Qatlib.Concepts.GradientOracle.ReadoutTools
