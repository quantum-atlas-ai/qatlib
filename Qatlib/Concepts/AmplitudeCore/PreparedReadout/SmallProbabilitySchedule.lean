/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Ring
import Lean.Elab.Tactic.Omega

/-!
# Dyadic schedules for small-probability estimation

`request` combines variance and quadratic error requirements, and `counterBits` selects a dyadic
`grid` whose square meets them. `decoderBits` allocates a separate rational decoding precision.

The module proves upper and lower resource bounds and combines the scaled BHMT radius with
decoder error under a mass cap `T * p ≤ B`. The statistical radius is the amplitude-estimation
bound of [BrassardEtAl2002].

## Main statements

* `counter_square_lower`: shows that the squared grid meets the request.
* `counter_square_upper`: bounds the squared grid in terms of the request.
* `statistical_budget`: bounds the total statistical and decoder error by `5 * eps / 8`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule
open scoped BigOperators

/-- The base-two ceiling logarithm of the natural ceiling of a rational request. -/
def dyadicBits (x : ℚ) : ℕ := Nat.clog 2 ⌈x⌉₊

/-- The power of two selected by `dyadicBits` is at least the rational request. -/
theorem dyadicBits_bound (x : ℚ) : x ≤ (2:ℚ)^(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits x) := by
  calc
    _ ≤ (⌈x⌉₊:ℚ) := Nat.le_ceil x
    _ ≤ _ := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < (2:ℕ)) ⌈x⌉₊

/-- The BHMT amplitude-estimation error radius `2π sqrt(p(1-p)) / M + π² / M²`. -/
noncomputable def radius (M : ℕ) (p : ℝ) : ℝ :=
  2*Real.pi*Real.sqrt (p*(1-p))/(M:ℝ)+Real.pi^2/(M:ℝ)^2

/-- The guarded ceiling logarithm gives `2^(max 1 (Nat.clog 2 m)) ≤ 2 * (m + 1)`. -/
private theorem guarded_clog_power_bound (m : ℕ) :
    2^(max 1 (Nat.clog 2 m)) ≤ 2*(m+1) := by
  by_cases hm : m ≤ 1
  · have hlog : Nat.clog 2 m=0 := Nat.clog_of_right_le_one hm 2
    calc
      _ = 2 := by norm_num [hlog]
      _ ≤ _ := by omega
  · have hm' : 1 < m := by omega
    have hp : 0 < Nat.clog 2 m := Nat.clog_pos (by decide) hm'
    have ht := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hm'
    have he : Nat.clog 2 m=(Nat.clog 2 m).pred+1 := (Nat.succ_pred_eq_of_pos hp).symm
    calc
      _ = 2^(Nat.clog 2 m) := congrArg (fun k : ℕ => 2^k) (max_eq_right (by omega))
      _ = 2^((Nat.clog 2 m).pred+1) := congrArg (fun k : ℕ => 2^k) he
      _ = 2^(Nat.clog 2 m).pred*2 := pow_succ _ _
      _ ≤ 2*(m+1) := by omega

/-- For a nonnegative rational request, the guarded dyadic power is at most twice the request
plus four. -/
private theorem guarded_dyadic_power_bound (request : ℚ) (hr : 0 ≤ request) :
    (2 : ℚ)^(max 1 (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits request)) ≤ 2*request+4 := by
  have hn : (2 : ℚ)^(max 1 (Nat.clog 2 ⌈request⌉₊)) ≤
      2*((⌈request⌉₊ : ℚ)+1) := by
    exact_mod_cast guarded_clog_power_bound ⌈request⌉₊
  have hc : (⌈request⌉₊ : ℚ) ≤ request+1 := (Nat.ceil_lt_add_one hr).le
  change (2 : ℚ)^(max 1 (Nat.clog 2 ⌈request⌉₊)) ≤ _
  linarith

/-- The maximum of the rational variance and quadratic requests `1024 * B * T / eps²` and `64 *
T / eps`. -/
def request (T B eps : ℚ) : ℚ := max (1024*B*T/eps^2) (64*T/eps)

/-- The dyadic bit count for the squared-grid request. -/
def requestBits (T B eps : ℚ) : ℕ :=
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request T B eps)

/-- The counter bit count, at least one and otherwise the rounded-up half of `requestBits`. -/
def counterBits (T B eps : ℚ) : ℕ :=
    max 1 ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.requestBits T B eps+1)/2)

/-- The dyadic phase-counter grid determined by `counterBits`. -/
def grid (T B eps : ℚ) : ℕ :=
    2^(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits T B eps)

/-- The dyadic decoder precision chosen from `8 * T / eps`. -/
def decoderBits (T eps : ℚ) : ℕ :=
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits (8*T/eps)

/-- The counter uses at least one bit. -/
theorem counterBits_positive (T B eps : ℚ) :
    1≤Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits T B eps :=
    le_max_left _ _

/-- The selected grid has at least two labels. -/
theorem two_le_grid (T B eps : ℚ) : 2≤Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps :=
  calc
    2 = (2:ℕ)^1 := by norm_num
    _ ≤ 2^(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits T B eps) := pow_le_pow_right₀ (by decide) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits_positive T B eps)

/-- The selected grid size is positive. -/
theorem grid_pos (T B eps : ℚ) : 0<Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps :=
  lt_of_lt_of_le (by decide : 0<2) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.two_le_grid T B eps)

/-- The request bit count is at most twice the counter bit count. -/
theorem requestBits_le_twice (T B eps : ℚ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.requestBits T B eps≤2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits T B eps := by
  dsimp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits]
  omega

/-- Twice the counter bit count is at most the guarded request bit count plus one. -/
theorem twice_counterBits_le (T B eps : ℚ) :
    2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits T B eps ≤ max 1 (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.requestBits T B eps)+1 := by
  dsimp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits]
  omega

/-- The rational square of the grid equals two raised to twice the counter bit count. -/
theorem grid_sq_rat (T B eps : ℚ) :
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps : ℚ)^2=(2:ℚ)^(2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits T B eps) := by
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid,Nat.cast_pow,Nat.cast_ofNat,← pow_mul]
  rw [Nat.mul_comm]

/-- The grid squared is at least the rational request. -/
theorem counter_square_lower (T B eps : ℚ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request T B eps≤(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps : ℚ)^2 := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid_sq_rat]
  exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits_bound (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request T B eps)).trans
    (pow_le_pow_right₀ (by norm_num) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.requestBits_le_twice T B eps))

/-- For nonnegative `T` and `B`, the rational request is nonnegative. -/
theorem request_nonneg (T B eps : ℚ) (hT : 0≤T) (hB : 0≤B) :
    0≤Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request T B eps :=
  (div_nonneg (by positivity : 0≤1024*B*T) (sq_nonneg eps)).trans (le_max_left _ _)

/-- For nonnegative `T` and `B`, the grid squared is at most `8 + 4 * request`. -/
theorem counter_square_upper (T B eps : ℚ) (hT : 0≤T) (hB : 0≤B) :
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps : ℚ)^2≤8+4*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request T B eps := by
  have hr :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request_nonneg T B eps hT hB
  have hu : (2:ℚ)^(max 1 (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.requestBits T B eps))≤4+2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request T B eps :=
    (guarded_dyadic_power_bound _ hr).trans_eq (by ring)
  calc
    _ = (2:ℚ)^(2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counterBits T B eps) := Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid_sq_rat T B eps
    _ ≤ (2:ℚ)^(max 1 (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.requestBits T B eps)+1) :=
      pow_le_pow_right₀ (by norm_num) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.twice_counterBits_le T B eps)
    _ = (2:ℚ)^(max 1 (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.requestBits T B eps))*2 := pow_succ _ _
    _ ≤ (4+2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.request T B eps)*2 := mul_le_mul_of_nonneg_right hu (by norm_num)
    _ = _ := by ring

/-- For positive `eps`, the selected grid satisfies the rational variance budget `1024 * B * T ≤
eps² * grid²`. -/
theorem variance_budget_rat (T B eps : ℚ) (heps : 0<eps) :
    1024*B*T≤eps^2*(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps : ℚ)^2 := by
  have hh := (le_max_left (1024*B*T/eps^2) (64*T/eps)).trans
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counter_square_lower T B eps)
  have hc := (div_le_iff₀ (sq_pos_of_pos heps)).mp hh
  nlinarith

/-- For positive `eps`, the selected grid satisfies the rational quadratic budget `64 * T ≤ eps
* grid²`. -/
theorem quadratic_budget_rat (T B eps : ℚ) (heps : 0<eps) :
    64*T≤eps*(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps : ℚ)^2 := by
  have hh := (le_max_right (1024*B*T/eps^2) (64*T/eps)).trans
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.counter_square_lower T B eps)
  have hc := (div_le_iff₀ heps).mp hh
  nlinarith

/-- The selected decoder precision bounds the scaled rational rounding error by `eps / 8`. -/
theorem decoder_budget_rat (T eps : ℚ) (heps : 0<eps) :
    T/(2:ℚ)^(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoderBits T eps)≤eps/8 := by
  have hh :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits_bound
      (8*T/eps)
  change _≤(2:ℚ)^(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoderBits T eps) at hh
  have hc := (div_le_iff₀ heps).mp hh
  apply (div_le_iff₀ (by positivity : (0:ℚ)<2^(decoderBits T eps))).mpr
  nlinarith

/-- The selected decoder precision bounds the scaled real dyadic rounding error by `eps / 8`. -/
theorem decoder_budget (T eps : ℚ) (heps : 0<eps) :
    (T:ℝ)*((2:ℝ)⁻¹)^(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoderBits T eps)≤(eps:ℝ)/8 := by
  have hh :=
      (Rat.cast_le (K:=ℝ)).mpr
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoder_budget_rat T eps heps)
  push_cast at hh
  rw [inv_pow]
  simpa only [div_eq_mul_inv] using hh

/-- Under a scaled-mass cap `T * p ≤ B`, the selected grid bounds the scaled BHMT radius by `eps
/ 2`. -/
theorem bhmt_budget (T B eps : ℚ) (hT : 0<T) (heps : 0<eps)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (hpB : (T:ℝ)*p≤(B:ℝ)) :
    (T:ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.radius (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps) p≤(eps:ℝ)/2 := by
  have hTp : (0:ℝ)<T := by exact_mod_cast hT
  have hep : (0:ℝ)<eps := by exact_mod_cast heps
  have hm :
      (0:ℝ)<(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps:ℝ) := by exact_mod_cast Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid_pos T B eps
  have hv0 : 0≤p*(1-p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hs0 := Real.sqrt_nonneg (p*(1-p))
  have hs := Real.sq_sqrt hv0
  have hv : (Real.sqrt (p*(1-p)))^2≤p := by nlinarith [sq_nonneg p]
  have hsmall : ((T:ℝ)*Real.sqrt (p*(1-p)))^2≤(B:ℝ)*(T:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hv (sq_nonneg (T:ℝ))
    have h2 := mul_le_mul_of_nonneg_left hpB hTp.le
    nlinarith
  have hb :=
      (Rat.cast_le (K:=ℝ)).mpr
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.variance_budget_rat T B eps heps)
  have hq :=
      (Rat.cast_le (K:=ℝ)).mpr
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.quadratic_budget_rat T B eps heps)
  push_cast at hb hq
  have hroot : 8*(T:ℝ)*Real.sqrt (p*(1-p))≤(eps:ℝ)*(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps:ℝ)/4 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [hsmall,hb]
  have hpi : 2*Real.pi≤8 := by linarith [Real.pi_lt_four]
  have hnum : (T:ℝ)*(2*Real.pi*Real.sqrt (p*(1-p)))≤
      (eps:ℝ)*(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps:ℝ)/4 := by
    calc
      _ = ((T:ℝ)*Real.sqrt (p*(1-p)))*(2*Real.pi) := by ring
      _ ≤ ((T:ℝ)*Real.sqrt (p*(1-p)))*8 :=
        mul_le_mul_of_nonneg_left hpi (mul_nonneg hTp.le hs0)
      _ = 8*(T:ℝ)*Real.sqrt (p*(1-p)) := by ring
      _ ≤ _ := hroot
  have hfirst : (T:ℝ)*(2*Real.pi*Real.sqrt (p*(1-p)))/(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps:ℝ)≤(eps:ℝ)/4 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have hpisq : Real.pi^2≤16 := by
    nlinarith [mul_self_le_mul_self Real.pi_pos.le Real.pi_lt_four.le]
  have hsecond : (T:ℝ)*Real.pi^2/(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps:ℝ)^2≤(eps:ℝ)/4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    have hh := mul_le_mul_of_nonneg_left hpisq hTp.le
    nlinarith
  unfold Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.radius
  calc
    _ = (T:ℝ)*(2*Real.pi*Real.sqrt (p*(1-p)))/(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps:ℝ)+
        (T:ℝ)*Real.pi^2/(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps:ℝ)^2 := by ring
    _ ≤ (eps:ℝ)/4+(eps:ℝ)/4 := add_le_add hfirst hsecond
    _ = _ := by ring

/-- Under the scaled-mass cap, the combined BHMT and dyadic decoder errors are at most `5 * eps
/ 8`. -/
theorem statistical_budget (T B eps : ℚ) (hT : 0<T) (heps : 0<eps)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (hpB : (T:ℝ)*p≤(B:ℝ)) :
    (T:ℝ)*(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.radius (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps) p+
      ((2:ℝ)⁻¹)^(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoderBits T eps))≤5*(eps:ℝ)/8 := by
  rw [mul_add]
  linarith [Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.bhmt_budget T B eps hT heps p hp0 hp1 hpB,Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoder_budget T eps heps]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule
