/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalReciprocal
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Qatlib.Concepts.WalshMoment.Forrelation.ThresholdApproximation
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Windowed reciprocal approximation with explicit bounds

`windowed_reciprocal_exists` constructs a bounded odd polynomial approximating `(δ/2)/x` on `[δ,
1]` for `0 < ε ≤ δ ≤ 1/2`. It records the degree bound and bounds on the reciprocal and window
truncation parameters.

`window_error_small` supplies the window residual estimate used in this construction, which
supports the pseudoinverse application of QSVT [GilyenSuLowWiebe2019].

## Main statements

* `window_error_small`: bounds the repeated window residual by the approximation budget.
* `windowed_reciprocal_exists`: constructs the bounded polynomial with explicit parameter
  bounds.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Polynomial
open scoped Classical

set_option maxHeartbeats 2000000

/-- Under 0 < ε ≤ δ ≤ 1/2 and the stated logarithmic choices of L and k, bounds the window
residual `(1 - (3 * δ * δ / 8) ^ 2) ^ (2 ^ k)` by twice the minimum of 1/(8J) and ε/(32J). -/
private theorem window_error_small {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hδ : δ ≤ 1/2)
    {J : ℕ} (hJ2 : 2 ≤ J) (hbudget : (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)))
    {L : ℝ} (hLdef : L = Real.log (64/(δ*ε))) {k : ℕ}
    (hkdef : k = Nat.ceil (Real.log (256*L/(9*δ^4))/Real.log 2)) :
    (1-(3*δ*δ/8)^2)^(2^k)
      ≤ 2*min (1/(8*(J:ℝ))) (ε/(32*(J:ℝ))) := by
  have hδpos : 0 < δ := by nlinarith
  have hJpos : (0:ℝ) < J := by exact_mod_cast (by omega : (0:ℕ) < J)
  have hA8 : (8:ℝ) ≤ 64/(δ*ε) := by
    rw [le_div_iff₀ (show (0:ℝ) < δ*ε by positivity)]
    nlinarith [hδpos, hε, hεδ, hδ]
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 8) hA8)
  have hL2 : (2:ℝ) ≤ L := by
    have he2 : Real.exp 2 ≤ 8 := by
      have he : Real.exp 2 = (Real.exp 1)*(Real.exp 1) := by
        rw [show (2:ℝ) = 1+1 from by norm_num, Real.exp_add]
      have hup : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
      have hE44 : Real.exp 1 ≤ 11/4 := hup.le.trans (by norm_num : (2.72:ℝ) ≤ 11/4)
      have hsq : (Real.exp 1)*(Real.exp 1) ≤ (11/4)*(11/4) :=
        mul_le_mul hE44 hE44 (by positivity) (by positivity)
      have h7 : (11/4:ℝ)*(11/4) ≤ 8 := by norm_num
      linarith
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    linarith

  have hln2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvpos : (0:ℝ) < 256*L/(9*δ^4) :=
    div_pos (mul_pos (by norm_num) hLpos) (mul_pos (by norm_num) (pow_pos hδpos 4))
  have h2v : 256*L/(9*δ^4) ≤ (2:ℝ)^((k:ℝ)) := by
    have h1 : Real.log (256*L/(9*δ^4))/Real.log 2 ≤ (k:ℝ) := by
      have h := Nat.le_ceil (Real.log (256*L/(9*δ^4))/Real.log 2)
      rw [← hkdef] at h
      exact_mod_cast h
    have h2 : (2:ℝ)^(Real.log (256*L/(9*δ^4))/Real.log 2) = 256*L/(9*δ^4) := by
      rw [Real.rpow_def_of_pos (show (0:ℝ) < 2 by norm_num)]
      have harg : Real.log 2*(Real.log (256*L/(9*δ^4))/Real.log 2)
          = Real.log (256*L/(9*δ^4)) := by
        field_simp
      rw [harg, Real.exp_log hvpos]
    calc 256*L/(9*δ^4) = (2:ℝ)^(Real.log (256*L/(9*δ^4))/Real.log 2) := h2.symm
      _ ≤ (2:ℝ)^((k:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hrw : ((2^k : ℕ):ℝ) = (2:ℝ)^((k:ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact (Real.rpow_natCast 2 k).symm
  have hγ2k : 4*L ≤ (3*δ*δ/8)^2*((2^k : ℕ):ℝ) := by
    have hle : 4*L ≤ (3*δ*δ/8)^2*(2:ℝ)^((k:ℝ)) := by
      have h1 : (3*δ*δ/8)^2*(256*L/(9*δ^4)) = 4*L := by
        field_simp
        norm_num
      calc 4*L = (3*δ*δ/8)^2*(256*L/(9*δ^4)) := h1.symm
        _ ≤ (3*δ*δ/8)^2*(2:ℝ)^((k:ℝ)) :=
            mul_le_mul_of_nonneg_left h2v (show (0:ℝ) ≤ (3*δ*δ/8)^2 by positivity)
    rw [hrw]
    exact hle

  have hη : min (1/(8*(J:ℝ))) (ε/(32*(J:ℝ))) = ε/(32*(J:ℝ)) := by
    refine min_eq_right ?_
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hJpos) (mul_pos (by norm_num) hJpos)]
    nlinarith [hε, hJpos, hεδ, hδ]

  have hL' : Real.log (16/(δ*ε)) ≤ L := by
    rw [hLdef]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hδpos, hε]
  have hJL : (J:ℝ)*δ ≤ 32*L := by
    have hb : (2*(J:ℝ)+1) ≤ (64/δ)*Real.log (16/(δ*ε)) := by
      have h := hbudget
      rwa [show 32*(2/δ) = 64/δ from by ring] at h
    have h1 : (2*(J:ℝ)+1)*δ ≤ 64*Real.log (16/(δ*ε)) := by
      calc (2*(J:ℝ)+1)*δ ≤ ((64/δ)*Real.log (16/(δ*ε)))*δ :=
            mul_le_mul_of_nonneg_right hb hδpos.le
        _ = 64*Real.log (16/(δ*ε)) := by
            rw [mul_assoc, mul_comm (Real.log (16/(δ*ε))) δ, ← mul_assoc,
              div_mul_cancel₀ _ hδpos.ne']
    nlinarith [h1, hL']
  have hlogη : Real.log (16*(J:ℝ)/ε) ≤ 4*L := by
    have hexpL : Real.exp L = 64/(δ*ε) := by
      rw [hLdef]
      exact Real.exp_log (by positivity)
    have h2 : 16*(J:ℝ)/ε ≤ 8*L*Real.exp L := by
      rw [hexpL, div_le_iff₀ hε,
        show 8*L*(64/(δ*ε))*ε = 512*L/δ from by field_simp; norm_num, le_div_iff₀ hδpos]
      nlinarith [hJL]
    have h3 : Real.log (8*L*Real.exp L) ≤ 4*L := by
      have hlogmul : Real.log (8*L*Real.exp L) = Real.log 8+Real.log L+L := by
        rw [Real.log_mul (mul_ne_zero (by norm_num) hLpos.ne') (Real.exp_ne_zero _),
          Real.log_mul (by norm_num) hLpos.ne', Real.log_exp L]
      have hln8 : Real.log 8 ≤ 3 := by
        have hE : (2.7:ℝ) ≤ Real.exp 1 :=
          ((by norm_num : (2.7:ℝ) ≤ 2.7182818283).trans_lt Real.exp_one_gt_d9).le
        have h1 : (2.7:ℝ)*(2.7:ℝ) ≤ (Real.exp 1)*(Real.exp 1) :=
          mul_le_mul hE hE (by positivity) (by positivity)
        have h2 : (2.7:ℝ)*(2.7:ℝ)*(2.7:ℝ)
            ≤ (Real.exp 1)*((Real.exp 1)*(Real.exp 1)) := by
          have t : (2.7:ℝ)*(2.7:ℝ)*(2.7:ℝ) ≤ ((Real.exp 1)*(Real.exp 1))*(Real.exp 1) :=
            mul_le_mul h1 hE (by positivity) (by positivity)
          rw [show ((Real.exp 1)*(Real.exp 1))*(Real.exp 1)
              = (Real.exp 1)*((Real.exp 1)*(Real.exp 1)) from by ring] at t
          exact t
        have he : Real.exp 3 = (Real.exp 1)*((Real.exp 1)*(Real.exp 1)) := by
          rw [show (3:ℝ) = 1+1+1 from by norm_num, Real.exp_add, Real.exp_add]
          ring
        have h8 : (8:ℝ) ≤ (2.7:ℝ)*(2.7:ℝ)*(2.7:ℝ) := by norm_num
        exact (Real.log_le_log (by norm_num) (by linarith)).trans (Real.log_exp 3).le
      have hlnL : Real.log L ≤ L-1 := Real.log_le_sub_one_of_pos hLpos
      rw [hlogmul]
      nlinarith
    exact (Real.log_le_log (div_pos (by nlinarith [hJpos]) hε) h2).trans h3

  have hδ2le : δ*δ ≤ 1/4 := by nlinarith [hδ, hδpos]
  have hγ1 : (3*δ*δ/8)^2 ≤ 1 := by
    have h4 : (δ*δ)*(δ*δ) ≤ 1/16 := by
      have t : (δ*δ)*(δ*δ) ≤ (1/4)*(1/4) :=
        mul_le_mul hδ2le hδ2le (by positivity) (by positivity)
      rw [show (1/4:ℝ)*(1/4) = 1/16 from by norm_num] at t
      exact t
    nlinarith [h4]
  have hbase : 1-(3*δ*δ/8)^2 ≤ Real.exp (-(3*δ*δ/8)^2) := by
    have h := Real.add_one_le_exp (-(3*δ*δ/8)^2)
    linarith
  rw [hη]
  refine le_trans (pow_le_pow_left₀ (by nlinarith [hγ1]) hbase (2^k)) ?_
  have hle : ((2^k : ℕ):ℝ)*(-(3*δ*δ/8)^2) ≤ Real.log (2*(ε/(32*(J:ℝ)))) := by
    have hlrw : Real.log (2*(ε/(32*(J:ℝ)))) = -(Real.log (16*(J:ℝ)/ε)) := by
      rw [show 2*(ε/(32*(J:ℝ))) = (16*(J:ℝ)/ε)⁻¹ from by field_simp; ring, Real.log_inv]
    rw [hlrw]
    nlinarith [hγ2k, hlogη]
  calc (Real.exp (-(3*δ*δ/8)^2))^(2^k)
      = Real.exp (((2^k : ℕ):ℝ)*(-(3*δ*δ/8)^2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log (2*(ε/(32*(J:ℝ))))) := Real.exp_le_exp.mpr hle
    _ = 2*(ε/(32*(J:ℝ))) :=
        Real.exp_log (mul_pos (by norm_num) (div_pos hε (by nlinarith [hJpos])))

/-- For 0 < ε ≤ δ ≤ 1/2, constructs a real polynomial bounded by one on [-1, 1], vanishing at
zero, and approximating (δ/2)/x within ε on [δ, 1]. It has odd parity and degree at most `2
* J + 1 + 2 * 3 ^ k`, with explicit bounds on J and 3^k [GilyenSuLowWiebe2019]. -/
theorem windowed_reciprocal_exists :
  ∀ (ε δ : ℝ), 0 < ε → ε ≤ δ → δ ≤ 1/2 →
    ∃ (Pw : Polynomial ℝ) (J k : ℕ),
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      Pw.natDegree ≤ 2*J+1+2*3^k ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (2*J+1+2*3^k) Pw ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) := by
  intro ε δ hε hεδ hδ
  have hδpos : 0 < δ := by nlinarith
  have hδε : δ*ε ≤ 1/4 := by nlinarith
  obtain ⟨hb1, hJ2, hgdeg, hgpar, hgeval0, hbudget⟩ :=
    nearOptimalReciprocal_family_degree_parity (2/δ) (ε/8)
      (by rw [lt_div_iff₀ hδpos]; nlinarith) (by positivity) (by nlinarith)
  obtain ⟨herr1, herr2, hsize, herr12, hscaled⟩ :=
    nearOptimalReciprocal_error_bounds (2/δ) (ε/8)
      (by rw [lt_div_iff₀ hδpos]; nlinarith) (by positivity) (by nlinarith)
  set J := nearOptimalReciprocalJ (2/δ) (ε/8) with hJdef
  set g := nearOptimalReciprocalPolynomial (2/δ) (ε/8) with hgdef
  set L := Real.log (64/(δ*ε)) with hLdef
  set k := Nat.ceil (Real.log (256*L/(9*δ^4))/Real.log 2) with hkdef
  set τ₀ := δ*Real.sqrt (5/8) with hτdef
  set γ := 3*δ*δ/8 with hγdef
  set η := min (1/(8*(J:ℝ))) (ε/(32*(J:ℝ))) with hηdef
  set w := thresholdPolynomial τ₀ k with hwdef
  set c' := (δ/2)*(1-ε/4) with hcdef
  have hJpos : (0:ℝ) < J := by exact_mod_cast (by omega : (0:ℕ) < J)
  have hLpos : 0 < L := by
    rw [hLdef]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ (show (0:ℝ) < δ*ε by positivity)]
    nlinarith [hδε, hδpos, hε]
  have hL2 : (2:ℝ) ≤ L := by
    have he2 : Real.exp 2 ≤ 8 := by
      have he : Real.exp 2 = (Real.exp 1)*(Real.exp 1) := by
        rw [show (2:ℝ) = 1+1 from by norm_num, Real.exp_add]
      have hup : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
      have hE44 : Real.exp 1 ≤ 11/4 := hup.le.trans (by norm_num : (2.72:ℝ) ≤ 11/4)
      have hsq : (Real.exp 1)*(Real.exp 1) ≤ (11/4)*(11/4) :=
        mul_le_mul hE44 hE44 (by positivity) (by positivity)
      have h7 : (11/4:ℝ)*(11/4) ≤ 8 := by norm_num
      linarith
    have hA8 : (8:ℝ) ≤ 64/(δ*ε) := by
      rw [le_div_iff₀ (show (0:ℝ) < δ*ε by positivity)]
      nlinarith [hδε, hδpos, hε]
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    linarith
  have hτ01 : τ₀ ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    calc τ₀ = δ*Real.sqrt (5/8) := hτdef
      _ ≤ δ*1 := by
          have h := Real.sqrt_le_sqrt (by norm_num : (5/8:ℝ) ≤ 1)
          rw [Real.sqrt_one] at h
          exact mul_le_mul_of_nonneg_left h hδpos.le
      _ ≤ 1 := by nlinarith
  have hτsq : τ₀*τ₀ = δ*δ*(5/8) := by
    rw [hτdef]
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5/8 by norm_num)
    nlinarith [Real.sqrt_nonneg (5/8 : ℝ)]
  have hγpos : 0 < γ := by positivity
  have hηε : η = ε/(32*(J:ℝ)) := by
    rw [hηdef]
    refine min_eq_right ?_
    rw [div_le_div_iff₀ (show (0:ℝ) < 32*(J:ℝ) by nlinarith)
      (show (0:ℝ) < 8*(J:ℝ) by nlinarith)]
    nlinarith [hε, hJpos, hεδ, hδ]
  rw [show (2/δ)/(ε/8) = 16/(δ*ε) from by field_simp; ring] at hbudget
  have hbudget2 : (2*(J:ℝ)+1) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using! hbudget
  have hwerr := window_error_small hε hεδ hδ hJ2 hbudget2 hLdef hkdef
  have herrη : signPolynomialError γ k/2 ≤ η := by
    have h2 := hwerr
    unfold signPolynomialError at h2 ⊢
    rw [← hγdef, ← hηdef] at h2
    nlinarith

  have hwlow : ∀ x : ℝ, |x| ≤ δ/2 → |w.eval x| ≤ η := by
    intro x hx
    have hx2 : x*x ≤ δ*δ/4 := by
      have hx' := mul_le_mul hx hx (abs_nonneg x) (by nlinarith : (0:ℝ) ≤ δ/2)
      rw [abs_mul_abs_self x] at hx'
      linarith
    have hind : thresholdIndicator τ₀ x = 0 := by
      unfold thresholdIndicator
      rw [if_neg]
      nlinarith
    have hgap : γ ≤ |x^2-τ₀^2| := by
      have hz : x^2-τ₀^2 ≤ -γ := by nlinarith
      rw [hγdef]
      rw [abs_of_nonpos (by nlinarith [hτsq, hx2])]
      nlinarith
    have herr := thresholdPolynomial_error_le k hτ01 hγpos hgap
      (le_trans hx (by nlinarith : δ/2 ≤ 1))
    rw [hind, zero_sub, abs_neg] at herr
    exact herr.trans herrη
  have hwhigh : ∀ x : ℝ, x ∈ Set.Icc δ 1 → 1-η ≤ w.eval x ∧ w.eval x ≤ 1 := by
    intro x hx
    have hxδ : δ ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hmem := thresholdPolynomial_eval_mem_Icc k hτ01 (abs_le.mpr ⟨by nlinarith, hx1⟩)
    have hind : thresholdIndicator τ₀ x = 1 := by
      unfold thresholdIndicator
      rw [if_pos]
      nlinarith
    have hgap : γ ≤ |x^2-τ₀^2| := by
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    have herr := thresholdPolynomial_error_le k hτ01 hγpos hgap
      (abs_le.mpr ⟨by nlinarith, hx1⟩)
    rw [hind] at herr
    constructor
    · have habs := abs_le.mp (herr.trans herrη)
      linarith [habs.1, habs.2]
    · exact hmem.2
  have hc'pos : 0 < c' := by
    have h4 : (0:ℝ) < 1-ε/4 := by nlinarith
    rw [hcdef]
    nlinarith [hδpos, h4]
  refine ⟨C c'*(g*w), J, k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using! hbudget
  · have hδ2 : (0:ℝ) ≤ δ*δ := by positivity
    have hδ2le : δ*δ ≤ 1/4 := by nlinarith [hδ, hδpos]
    have hln2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hln3le2 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 3)]
      have hE : (27/10:ℝ) ≤ Real.exp 1 :=
        ((by norm_num : (27/10:ℝ) ≤ 2.7182818283).trans_lt Real.exp_one_gt_d9).le
      have h1 : (27/10:ℝ)*(27/10:ℝ) ≤ (Real.exp 1)*(Real.exp 1) :=
        mul_le_mul hE hE (by positivity) (by positivity)
      have h3 : (3:ℝ) ≤ (27/10:ℝ)*(27/10:ℝ) := by norm_num
      have he : Real.exp 2 = (Real.exp 1)*(Real.exp 1) := by
        rw [show (2:ℝ) = 1+1 from by norm_num, Real.exp_add]
      linarith
    have hln256 : Real.log 256 ≤ 8 := by
      have hln2le1 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
        exact (lt_of_le_of_lt (by norm_num : (2:ℝ) ≤ 2.7182818283)
          Real.exp_one_gt_d9).le
      have h256 : Real.log 256 = 8*Real.log 2 := by
        rw [show (256:ℝ) = (2:ℝ)^(8:ℕ) from by norm_num, Real.log_pow]
        norm_num
      rw [h256]
      linarith
    have hinv' : Real.log ((δ:ℝ)⁻¹)*(δ*δ) ≤ 2 := by
      have h1 : Real.log ((δ:ℝ)⁻¹) ≤ (δ:ℝ)⁻¹ :=
        Real.log_le_self (inv_pos.2 hδpos).le
      have h2 : ((δ:ℝ)⁻¹)*(δ*δ) ≤ 2 := by
        rw [show ((δ:ℝ)⁻¹)*(δ*δ) = δ from by field_simp]
        nlinarith [hδpos]
      exact (mul_le_mul_of_nonneg_right h1 hδ2).trans h2

    have hlnv : (Real.log (256*L/(9*δ^4)))*(δ*δ) ≤ (8+L)*(δ*δ)+8 := by
      have hsplit : Real.log (256*L/(9*δ^4))*(δ*δ)
          = (Real.log 256+Real.log L-Real.log 9)*(δ*δ)
            +4*Real.log ((δ:ℝ)⁻¹)*(δ*δ) := by
        rw [Real.log_div (by positivity)
            (mul_ne_zero (by norm_num) (pow_ne_zero 4 hδpos.ne')),
            Real.log_mul (by norm_num) hLpos.ne',
            Real.log_mul (by norm_num) (pow_ne_zero 4 hδpos.ne'),
            Real.log_pow δ 4, Real.log_inv δ]
        ring
      rw [hsplit]
      have hlnL : Real.log L ≤ L := Real.log_le_self hLpos.le
      have hln9 : (0:ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
      have hp1 := mul_le_mul_of_nonneg_right hln256 hδ2
      have hp2 := mul_le_mul_of_nonneg_right hlnL hδ2
      have hp3 := mul_le_mul_of_nonneg_right hln9 hδ2
      nlinarith [hp1, hp2, hp3, hinv']
    have hvge1 : (1:ℝ) ≤ 256*L/(9*δ^4) := by
      have hδ4 : δ^4 ≤ 1/16 := by nlinarith [hδ2le, hδ2]
      rw [le_div_iff₀ (mul_pos (by norm_num) (pow_pos hδpos 4))]
      nlinarith [hL2, hδ4]
    have hlnvnn : (0:ℝ) ≤ Real.log (256*L/(9*δ^4)) := Real.log_nonneg hvge1
    have hln2 : Real.log 2 ≠ 0 := hln2pos.ne'
    have hkup : (k:ℝ) ≤ Real.log (256*L/(9*δ^4))/Real.log 2+1 := by
      have hnn : (0:ℝ) ≤ Real.log (256*L/(9*δ^4))/Real.log 2 :=
        div_nonneg hlnvnn hln2pos.le
      have hlt := Nat.ceil_lt_add_one hnn
      rw [← hkdef] at hlt
      linarith
    have hratio : Real.log 3/Real.log 2 ≤ 2 := by
      have hln4 : Real.log ((2:ℝ)^(2:ℕ)) = 2*Real.log 2 := by
        rw [Real.log_pow]
        norm_num
      rw [div_le_iff₀ hln2pos, ← hln4]
      exact Real.log_le_log (by norm_num) (by norm_num : (3:ℝ) ≤ (2:ℝ)^(2:ℕ))
    have hq : (Real.log (256*L/(9*δ^4))/Real.log 2)*Real.log 3
        ≤ 2*Real.log (256*L/(9*δ^4)) := by
      have hrw2 : (Real.log (256*L/(9*δ^4))/Real.log 2)*Real.log 3
          = (Real.log 3/Real.log 2)*Real.log (256*L/(9*δ^4)) := by ring
      rw [hrw2]
      exact mul_le_mul_of_nonneg_right hratio hlnvnn
    have hkln3 : (k:ℝ)*Real.log 3
        ≤ Real.log 3+2*Real.log (256*L/(9*δ^4)) := by
      have h1 := mul_le_mul_of_nonneg_right hkup (show (0:ℝ) ≤ Real.log 3 by positivity)
      have hrw3 : (Real.log (256*L/(9*δ^4))/Real.log 2+1)*Real.log 3
          = Real.log 3+(Real.log (256*L/(9*δ^4))/Real.log 2)*Real.log 3 := by ring
      rw [hrw3] at h1
      linarith [h1, hq]
    have hfinal1 : (k:ℝ)*Real.log 3*(δ*δ) ≤ 12*L := by
      have h1 : (k:ℝ)*Real.log 3*(δ*δ)
          ≤ (Real.log 3+2*Real.log (256*L/(9*δ^4)))*(δ*δ) :=
        mul_le_mul_of_nonneg_right hkln3 hδ2
      have hp5 : Real.log 3*(δ*δ) ≤ 2*(δ*δ) :=
        mul_le_mul_of_nonneg_right hln3le2 hδ2
      have hpL : (0:ℝ) ≤ L := le_trans (by norm_num) hL2
      have hLd := mul_le_mul_of_nonneg_left hδ2le hpL
      linarith
    have h3k : Real.exp ((k:ℝ)*Real.log 3) = (3:ℝ)^k := by
      rw [← Real.log_pow (3:ℝ) k, Real.exp_log (by norm_num : (0:ℝ) < (3:ℝ)^k)]
    have hArw : Real.exp (12*L/(δ*δ)) = (64/(δ*ε))^(12/(δ*δ)) := by
      rw [Real.rpow_def_of_pos (show (0:ℝ) < 64/(δ*ε) by positivity), ← hLdef]
      congr 1
      ring
    have hApos : (0:ℝ) < (64/(δ*ε))^(12/(δ*δ)) :=
      Real.rpow_pos_of_pos (show (0:ℝ) < 64/(δ*ε) by positivity) _
    calc (3:ℝ)^k = Real.exp ((k:ℝ)*Real.log 3) := h3k.symm
      _ ≤ Real.exp (12*L/(δ*δ)) := Real.exp_le_exp.mpr (by
        rw [le_div_iff₀ (show (0:ℝ) < δ*δ by positivity)]
        exact hfinal1)
      _ = (64/(δ*ε))^(12/(δ*δ)) := hArw
      _ ≤ 3*(64/(δ*ε))^(12/(δ*δ)) := le_mul_of_one_le_left hApos.le (by norm_num : (1:ℝ) ≤ 3)
  · have hgn := natDegree_le_of_degree_le hgdeg
    have hwn := thresholdPolynomial_natDegree_le τ₀ k
    calc (C c'*(g*w)).natDegree ≤ (C c').natDegree+(g*w).natDegree := natDegree_mul_le
      _ = (g*w).natDegree := by
          rw [natDegree_C, zero_add]
      _ ≤ g.natDegree+w.natDegree := natDegree_mul_le
      _ ≤ 2*J+1+2*3^k := add_le_add hgn hwn
  · change g.comp (-X) = C ((-1:ℝ)^(2*J+1))*g at hgpar
    unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
    rw [mul_comp, C_comp, mul_comp, hgpar, thresholdPolynomial_comp_neg_X]
    have hodd1 : Odd (2*J+1) := ⟨J, rfl⟩
    have hodd2 : Odd (2*J+1+2*3^k) := ⟨J+3^k, by ring⟩
    rw [hodd1.neg_one_pow, hodd2.neg_one_pow]
    ring
  · intro x hx
    rcases le_or_gt (abs x) (δ/2) with hlow | hhigh
    · have hw := hwlow x hlow
      have hg := hsize x hx
      have hη1 : η ≤ 1/(8*(J:ℝ)) := min_le_left _ _
      have hprod : (|g.eval x|)*(|w.eval x|) ≤ 4*(J:ℝ)*(1/(8*(J:ℝ))) :=
        mul_le_mul hg (hw.trans hη1) (abs_nonneg _) (by nlinarith [hJpos])
      have hval : 4*(J:ℝ)*(1/(8*(J:ℝ))) = 1/2 := by field_simp; ring
      rw [hval] at hprod
      have hc'le : c' ≤ δ/2 := by rw [hcdef]; nlinarith
      calc |(C c'*(g*w)).eval x| = c'*((|g.eval x|)*(|w.eval x|)) := by
            simp only [eval_mul, eval_C, abs_mul, abs_of_pos hc'pos]
        _ ≤ c'*(1/2) := mul_le_mul_of_nonneg_left hprod hc'pos.le
        _ ≤ (δ/2)*(1/2) := by nlinarith [hc'le]
        _ ≤ 1 := by nlinarith
    · have hax1 : |x| ≤ 1 := abs_le.mpr ⟨by nlinarith [hx.1, hx.2], hx.2⟩
      have hwm : w.eval x ∈ Set.Icc (0:ℝ) 1 := thresholdPolynomial_eval_mem_Icc k hτ01 hax1
      have hinvle : |(x:ℝ)⁻¹| ≤ 2/δ := by
        have hxinv : ((0:ℝ) < |x|) :=
          lt_trans (show (0:ℝ) < δ/2 by nlinarith [hδpos]) hhigh
        have h1 : (1:ℝ)/|x| ≤ 1/(δ/2) :=
          (one_div_le_one_div hxinv (by nlinarith [hδpos])).mpr hhigh.le
        rw [abs_inv, inv_eq_one_div, show 2/δ = 1/(δ/2) from by ring]
        exact h1
      have hginv : |g.eval x-(x:ℝ)⁻¹| ≤ 2*(ε/8) := by
        rcases lt_or_ge x 0 with hxneg | hxpos2
        · have hgev : g.eval (-x) = -(g.eval x) := by
            have h2 : g.comp (-X) = C ((-1:ℝ)^(2*J+1))*g := hgpar
            have h1 : (g.comp (-X)).eval x = ((C ((-1:ℝ)^(2*J+1))*g)).eval x := by
              rw [h2]
            rw [Polynomial.eval_comp, eval_neg, eval_X, eval_mul, eval_C] at h1
            rw [h1, show ((-1:ℝ)^(2*J+1)) = -1 from Odd.neg_one_pow ⟨J, rfl⟩]
            ring
          rw [abs_of_neg hxneg] at hhigh
          have hu : -x ∈ Set.Icc ((2:ℝ)/δ)⁻¹ 1 := by
            refine ⟨by rw [inv_div]; linarith, by linarith [hx.1]⟩
          have hg' := herr12 (-x) hu
          have hconv : (-g.eval x)-(-((x:ℝ)⁻¹)) = -(g.eval x-(x:ℝ)⁻¹) := by ring
          rw [hgev, inv_neg, hconv, abs_neg] at hg'
          exact hg'
        · rw [abs_of_nonneg hxpos2] at hhigh
          exact herr12 x ⟨by rw [inv_div]; linarith, (abs_le.mp hax1).2⟩
      have hwm1 : |w.eval x| ≤ 1 := abs_le.mpr ⟨by linarith [hwm.1], hwm.2⟩
      have htri : |g.eval x| ≤ |(x:ℝ)⁻¹|+|g.eval x-(x:ℝ)⁻¹| := by
        calc |g.eval x| = |(g.eval x-(x:ℝ)⁻¹)+(x:ℝ)⁻¹| := by ring
          _ ≤ |g.eval x-(x:ℝ)⁻¹|+|(x:ℝ)⁻¹| := abs_add_le _ _
          _ = |(x:ℝ)⁻¹|+|g.eval x-(x:ℝ)⁻¹| := by ring
      have hgle : |g.eval x| ≤ 2/δ+ε/4 := by
        have h2 : 2*(ε/8) = ε/4 := by ring
        linarith [htri, hginv, hinvle, h2]
      calc |(C c'*(g*w)).eval x| = c'*((|g.eval x|)*(|w.eval x|)) := by
            simp only [eval_mul, eval_C, abs_mul, abs_of_pos hc'pos]
        _ ≤ c'*((2/δ+ε/4)*1) := by
            refine mul_le_mul_of_nonneg_left ?_ hc'pos.le
            have hpp : (0:ℝ) < 2/δ+ε/4 :=
              add_pos (div_pos (by norm_num) hδpos) (by nlinarith [hε])
            exact mul_le_mul hgle hwm1 (abs_nonneg _) hpp.le
        _ = (δ/2)*(1-ε/4)*(2/δ+ε/4) := by rw [hcdef]; ring
        _ ≤ 1 := by
            have hkey : (δ/2)*(1-ε/4)*(2/δ+ε/4)
                = 1 - ε/4 + (δ*ε/8) - (δ*ε/8)*(ε/4) := by
              field_simp [hδpos.ne']; ring
            rw [hkey]
            have h1 : (δ*ε/8) ≤ (ε/4) := by
              rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
              nlinarith [hδpos, hδ]
            have hdεε : (0:ℝ) ≤ δ*ε*ε :=
              mul_nonneg (mul_nonneg hδpos.le hε.le) hε.le
            linarith [h1, hdεε]
  · simp only [eval_mul, eval_C, hgeval0]
    ring
  · intro x hx
    have hxδ : δ ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hxpos : 0 < x := by nlinarith
    have hax : |x| = x := abs_of_pos hxpos
    have hw1 : 1-η ≤ w.eval x := (hwhigh x hx).1
    have hw2 : w.eval x ≤ 1 := (hwhigh x hx).2
    have hg4 : |g.eval x| ≤ 4*(J:ℝ) := hsize x ⟨by nlinarith, hx1⟩
    have hginv := herr12 x ⟨by rw [inv_div]; linarith, hx1⟩
    have hwinv : |w.eval x-1| ≤ η := by
      have h1 : |1-w.eval x| ≤ η := abs_le.mpr ⟨by linarith [hw1], by nlinarith [hw2]⟩
      rw [abs_sub_comm]
      exact h1
    have hdecomp : c'*(g.eval x*(w.eval x))-(δ/2)/x
        = c'*(g.eval x)*(w.eval x-1)+c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹) := by
      rw [div_eq_inv_mul]
      ring
    have hδε0 : (0:ℝ) ≤ δ*ε := mul_nonneg hδpos.le hε.le
    have hsubq : (δ/2)*(1-ε/4) ≤ 1/4 := by nlinarith [hδ, hδε0]
    have t1 : |c'*(g.eval x)*(w.eval x-1)| ≤ ε/32 := by
      have hstep : |c'*(g.eval x)*(w.eval x-1)| ≤ c'*(4*(J:ℝ)*(ε/(32*(J:ℝ)))) := by
        calc |c'*(g.eval x)*(w.eval x-1)| = c'*((|g.eval x|)*(|w.eval x-1|)) := by
              simp only [abs_mul, abs_of_pos hc'pos, mul_assoc]
          _ ≤ c'*(4*(J:ℝ)*(ε/(32*(J:ℝ)))) := by
              refine mul_le_mul_of_nonneg_left ?_ hc'pos.le
              exact mul_le_mul hg4 (hwinv.trans_eq hηε) (abs_nonneg _)
                (by nlinarith [hJpos] : (0:ℝ) ≤ 4*(J:ℝ))
      have hval : 4*(J:ℝ)*(ε/(32*(J:ℝ))) = ε/8 := by field_simp; ring
      have hkey2 : (δ/2)*(1-ε/4)*(ε/8) ≤ ε/32 := by
        have hmul := mul_le_mul_of_nonneg_right hsubq
          (by nlinarith [hε] : (0:ℝ) ≤ ε/8)
        have hfin : (1/4:ℝ)*(ε/8) = ε/32 := by ring
        linarith [hmul, hfin]
      rw [hval, hcdef] at hstep
      linarith [hstep, hkey2]
    have t2 : |c'*(g.eval x-(x:ℝ)⁻¹)| ≤ ε/16 := by
      have habs : |c'*(g.eval x-(x:ℝ)⁻¹)| = c'*|g.eval x-(x:ℝ)⁻¹| := by
        rw [abs_mul, abs_of_pos hc'pos]
      rw [habs]
      have hstep : c'*|g.eval x-(x:ℝ)⁻¹| ≤ c'*(2*(ε/8)) :=
        mul_le_mul_of_nonneg_left hginv hc'pos.le
      have hkey3 : (δ/2)*(1-ε/4)*(2*(ε/8)) ≤ ε/16 := by
        have hmul := mul_le_mul_of_nonneg_right hsubq
          (by nlinarith [hε] : (0:ℝ) ≤ 2*(ε/8))
        have hfin : (1/4:ℝ)*(2*(ε/8)) = ε/16 := by ring
        linarith [hmul, hfin]
      rw [hcdef] at hstep ⊢
      linarith [hstep, hkey3]
    have t3 : |(c'-(δ/2))*((x:ℝ)⁻¹)| ≤ ε/8 := by
      have hc : c'-(δ/2) = -(δ/2)*(ε/4) := by rw [hcdef]; ring
      have hinvle : |((x:ℝ)⁻¹)| ≤ 1/δ := by
        rw [abs_inv, abs_of_pos hxpos, inv_eq_one_div]
        exact one_div_le_one_div_of_le hδpos hxδ
      rw [hc]
      calc |(-(δ/2)*(ε/4))*((x:ℝ)⁻¹)| = ((δ/2)*(ε/4))*|((x:ℝ)⁻¹)| := by
            rw [show (-(δ/2)*(ε/4))*((x:ℝ)⁻¹)
                  = -(((δ/2)*(ε/4))*((x:ℝ)⁻¹)) from by ring,
              abs_neg, abs_mul, abs_of_pos (by positivity)]
        _ ≤ ((δ/2)*(ε/4))*(1/δ) := mul_le_mul_of_nonneg_left hinvle (by positivity)
        _ = ε/8 := by field_simp; ring
    simp only [eval_mul, eval_C]
    rw [hdecomp]
    calc |c'*(g.eval x)*(w.eval x-1)+c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹)|
        ≤ |c'*(g.eval x)*(w.eval x-1)|
          +|c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹)| := by
            have hrw : c'*(g.eval x)*(w.eval x-1)
                +(c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹))
                = c'*(g.eval x)*(w.eval x-1)+c'*(g.eval x-(x:ℝ)⁻¹)
                  +(c'-(δ/2))*((x:ℝ)⁻¹) := by ring
            rw [← hrw]
            exact abs_add_le _ _
      _ ≤ |c'*(g.eval x)*(w.eval x-1)|
          +(|c'*(g.eval x-(x:ℝ)⁻¹)|+|(c'-(δ/2))*((x:ℝ)⁻¹)|) :=
          add_le_add (le_refl _) (abs_add_le _ _)
      _ ≤ ε/32+(ε/16+ε/8) := add_le_add t1 (add_le_add t2 t3)
      _ ≤ ε := by nlinarith [hε]

end Qatlib.Concepts.QsvtCore.LinearSystems
