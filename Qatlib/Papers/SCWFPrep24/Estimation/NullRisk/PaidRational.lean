/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Model.BornCurrentRecords

set_option backward.isDefEq.respectTransparency false

/-!
# Computed finite rational loss scale

The existing Machin enclosure supplies all endpoints. An actual doubling
prefix from eight bits checks absolute output error and relative variance
guards; termination and the returned coefficient are proved together.
-/

set_option autoImplicit false
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model

/-- Finite rational data obtained from the actual existing Machin enclosure, with no unknown-input query. -/
structure InverseSquareQ where
  /-- Lower rational enclosure for the original inverse-square grid spacing. -/
  lower : ℚ
  /-- Upper rational enclosure for the original inverse-square grid spacing. -/
  upper : ℚ
  /-- Actual rational midpoint returned to scalar postprocessing. -/
  value : ℚ
  /-- Certified half-width consumed by the explicit absolute-error guard. -/
  radius : ℚ
  /-- Actual requested Machin precision at the successful iteration. -/
  bits : ℕ
  deriving Repr

/-- Inverse-square midpoint and radius are computed using rational arithmetic on the existing Machin endpoints. -/
def inverseSquareCandidateQ (N bits : ℕ) : InverseSquareQ :=
  let p := piCandidateQ bits
  let lo := ((N : ℚ)/2/p.2)^2
  let hi := ((N : ℚ)/2/p.1)^2
  {lower:=lo, upper:=hi, value:=(lo+hi)/2, radius:=(hi-lo)/2, bits:=bits}

/-- Both the absolute output-error guard and the relative variance guard are actually checked. -/
def inverseSquareStepQ (N bits : ℕ) (A β : ℚ) : Option InverseSquareQ :=
  let c := inverseSquareCandidateQ N bits
  if 1≤bits ∧ c.radius≤β/A ∧ c.value≤2*c.lower then some c else none

/-- This finite precision threshold includes the true grid size N, not just the exponent's encoding length. -/
def inverseSquareBitsQ (N : ℕ) (A β : ℚ) : ℕ :=
  ceilLog2Q (max 1 ((N : ℚ)^2*A/(108*β)))

/-- The actual bounded doubling prefix reuses the existing rational precision loop and checks both stopping guards. -/
def inverseSquareGeneratedQ (N : ℕ) (A β : ℚ) : Option InverseSquareQ :=
  let k := ceilLog2Q (max 1 ((inverseSquareBitsQ N A β : ℚ)/16))
  doublingLoopQ (fun bits => inverseSquareStepQ N bits A β) (k+2) 8

noncomputable section

/-- Actual Machin endpoints enclose the reciprocal square of the original h=2π/N. -/
theorem inverseSquareCandidateQ_encloses (N bits : ℕ) (hb : 1≤bits) :
    ((inverseSquareCandidateQ N bits).lower : ℝ) ≤ 1/(2*Real.pi/(N : ℝ))^2 ∧
    1/(2*Real.pi/(N : ℝ))^2 ≤ ((inverseSquareCandidateQ N bits).upper : ℝ) := by
  have hp := pi_candidate_valid bits hb
  have hl : (0 : ℝ)<((piCandidateQ bits).1 : ℝ) := by linarith [hp.1]
  have hi : (0 : ℝ)<((piCandidateQ bits).2 : ℝ) := Real.pi_pos.trans_le hp.2.2.1
  have h := inverse_pi_interval N _ _ hl hp.2.1 hp.2.2.1
  have h0 : (0 : ℝ) ≤ (N : ℝ)/2/((piCandidateQ bits).2 : ℝ) := by positivity
  constructor
  · simpa only [inverseSquareCandidateQ, Rat.cast_pow, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, one_div_pow] using pow_le_pow_left₀ h0 h.1 2
  · have hx : (0 : ℝ) ≤ 1/(2*Real.pi/(N : ℝ)) := by positivity
    simpa only [inverseSquareCandidateQ, Rat.cast_pow, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, one_div_pow] using pow_le_pow_left₀ hx h.2 2

/-- The computed rational midpoint has its certified actual absolute error, before either stopping test is consumed. -/
theorem inverseSquareCandidateQ_error (N bits : ℕ) (hb : 1≤bits) :
    |((inverseSquareCandidateQ N bits).value : ℝ)-1/(2*Real.pi/(N : ℝ))^2| ≤
      ((inverseSquareCandidateQ N bits).radius : ℝ) := by
  have he := inverseSquareCandidateQ_encloses N bits hb
  have h := midpoint_error_bound _ _ _ he.1 he.2
  simpa only [inverseSquareCandidateQ, Rat.cast_div, Rat.cast_pow, Rat.cast_add,
    Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat] using h

/-- The actual finite Machin endpoint range already makes the separate relative guard true. -/
theorem inverseSquareCandidateQ_relative (N bits : ℕ) (hb : 1≤bits) :
    (inverseSquareCandidateQ N bits).value ≤ 2*(inverseSquareCandidateQ N bits).lower := by
  have hp := pi_candidate_valid bits hb
  let p : ℝ := (piCandidateQ bits).1
  let q : ℝ := (piCandidateQ bits).2
  have hp0 : 0<p := by dsimp [p]; linarith [hp.1]
  have hq0 : 0<q := Real.pi_pos.trans_le hp.2.2.1
  have hp9 : (9 : ℝ)<p^2 := by nlinarith [hp.1]
  have hq16 : q^2<16 := by nlinarith [hp.2.2.2]
  have hden : q^2≤3*p^2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg ((N : ℝ)/2))
  have hbound : ((N : ℝ)/2/p)^2 ≤ 3*((N : ℝ)/2/q)^2 := by
    simp only [div_pow]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos hp0) (sq_pos_of_pos hq0)).2
    nlinarith
  have he : (((inverseSquareCandidateQ N bits).value : ℚ) : ℝ) ≤
      ((2*(inverseSquareCandidateQ N bits).lower : ℚ) : ℝ) := by
    simp only [inverseSquareCandidateQ, Rat.cast_div, Rat.cast_pow, Rat.cast_add,
      Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
    change (((N : ℝ)/2/q)^2+((N : ℝ)/2/p)^2)/2 ≤ 2*((N : ℝ)/2/q)^2
    linarith
  exact Rat.cast_le.mp he

/-- Reusing the existing proved Machin rate bounds the newly computed inverse-square radius. -/
theorem inverseSquareCandidateQ_rate (N bits : ℕ) (hb : 1≤bits) :
    (inverseSquareCandidateQ N bits).radius ≤ (N : ℚ)^2/(108*(2 : ℚ)^bits) := by
  have hr := (coefficient_candidate_error_rates 1 N bits 1 1 0 1 hb).2
  have hc : ((inverseSquareCandidateQ N bits).radius : ℝ) =
      2*((coefficientCandidateQ 1 N bits 1 1 0 1).gammaError : ℝ) := by
    simp only [inverseSquareCandidateQ, coefficientCandidateQ, Rat.cast_div, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat]
    ring
  have he : ((inverseSquareCandidateQ N bits).radius : ℝ) ≤
      (((N : ℚ)^2/(108*(2 : ℚ)^bits) : ℚ) : ℝ) := by
    rw [hc]
    simp only [Rat.cast_one, one_pow, one_mul] at hr
    push_cast
    calc _ ≤ 2*((N : ℝ)^2/(216*(2 : ℝ)^bits)) :=
           mul_le_mul_of_nonneg_left hr (by norm_num)
         _ = _ := by ring
  exact Rat.cast_le.mp he

/-- A sufficient finite requested precision makes BOTH actual guards return the computed candidate. -/
theorem inverseSquareStepQ_ready (N bits : ℕ) (A β : ℚ) (hA : 0<A) (hβ : 0<β)
    (hb : 1≤bits) (hbits : inverseSquareBitsQ N A β≤bits) :
    inverseSquareStepQ N bits A β=some (inverseSquareCandidateQ N bits) := by
  have hp := ceil_log2_power (max 1 ((N : ℚ)^2*A/(108*β)))
  have hmono : (2 : ℚ)^(inverseSquareBitsQ N A β)≤(2 : ℚ)^bits :=
    pow_le_pow_right₀ (by norm_num) hbits
  have hpow : (N : ℚ)^2*A/(108*β) ≤ (2 : ℚ)^bits :=
    (le_max_right _ _).trans (hp.trans hmono)
  have hden : (0 : ℚ)<108*(2 : ℚ)^bits := by positivity
  have hc : (N : ℚ)^2/(108*(2 : ℚ)^bits) ≤ β/A := by
    apply (div_le_div_iff₀ hden hA).2
    have hm := (div_le_iff₀ (by positivity : (0 : ℚ)<108*β)).mp hpow
    nlinarith
  unfold inverseSquareStepQ
  rw [ite_eq_left ⟨hb,(inverseSquareCandidateQ_rate N bits hb).trans hc,
    inverseSquareCandidateQ_relative N bits hb⟩]

/-- The actual bounded doubling prefix terminates for every positive public error tolerance and output envelope. -/
theorem inverseSquareGeneratedQ_total (N : ℕ) (A β : ℚ) (hA : 0<A) (hβ : 0<β) :
    ∃ c, inverseSquareGeneratedQ N A β=some c := by
  let k := ceilLog2Q (max 1 ((inverseSquareBitsQ N A β : ℚ)/16))
  have hbits := (precision_doubling_bounds (inverseSquareBitsQ N A β)).1
  have hb : 1≤16*2^k := by
    have he : 0<16*2^k := by positivity
    omega
  have hready := inverseSquareStepQ_ready N (16*2^k) A β hA hβ hb hbits
  have he : 8*2^(k+1)=16*2^k := by rw [pow_succ]; ring
  have hlast : ∃ c, inverseSquareStepQ N (8*2^(k+1)) A β=some c := by
    rw [he]
    exact ⟨_,hready⟩
  simpa only [inverseSquareGeneratedQ, k, Nat.add_assoc] using doubling_loop_reaches
    (fun bits => inverseSquareStepQ N bits A β) (k+1) 8 hlast

/-- Every actual successful iteration exposes its own computed endpoints and both tested guards. -/
theorem inverseSquareStepQ_spec (N bits : ℕ) (A β : ℚ) (c : InverseSquareQ)
    (hc : inverseSquareStepQ N bits A β=some c) :
    c=inverseSquareCandidateQ N bits ∧ 1≤bits ∧ c.radius≤β/A ∧ c.value≤2*c.lower := by
  dsimp only [inverseSquareStepQ] at hc
  split_ifs at hc with hg
  · cases hc
    exact ⟨rfl,hg⟩

/-- The complete computed coefficient has absolute accuracy and the independently checked relative bound, without an externally supplied error certificate. -/
theorem inverseSquareGeneratedQ_spec (N : ℕ) (A β : ℚ) (c : InverseSquareQ)
    (hc : inverseSquareGeneratedQ N A β=some c) :
    |(c.value : ℝ)-1/(2*Real.pi/(N : ℝ))^2|≤(β : ℝ)/(A : ℝ) ∧
      (c.value : ℝ)≤2/(2*Real.pi/(N : ℝ))^2 := by
  unfold inverseSquareGeneratedQ at hc
  obtain ⟨i,hi,hstep⟩ := doubling_loop_trace _ _ 8 c hc
  obtain ⟨he,hb,ha,hr⟩ := inverseSquareStepQ_spec N (8*2^i) A β c hstep
  have herr := inverseSquareCandidateQ_error N (8*2^i) hb
  have hbox := (inverseSquareCandidateQ_encloses N (8*2^i) hb).1
  rw [← he] at herr hbox
  have har : (c.radius : ℝ)≤(β : ℝ)/(A : ℝ) := by exact_mod_cast ha
  have hrr : (c.value : ℝ)≤2*(c.lower : ℝ) := by exact_mod_cast hr
  refine ⟨herr.trans har,?_⟩
  calc (c.value : ℝ) ≤ 2*(c.lower : ℝ) := hrr
       _ ≤ 2*(1/(2*Real.pi/(N : ℝ))^2) :=
         mul_le_mul_of_nonneg_left hbox (by norm_num)
       _ = _ := by ring

/-- The computed midpoint is nonnegative for every finite grid size; this is needed before squaring the relative variance guard. -/
theorem inverseSquareCandidateQ_nonneg (N bits : ℕ) :
    0≤(inverseSquareCandidateQ N bits).value := by
  unfold inverseSquareCandidateQ
  positivity

/-- The actual returned coefficient retains the nonnegative sign of its computed midpoint. -/
theorem inverseSquareGeneratedQ_nonneg (N : ℕ) (A β : ℚ) (c : InverseSquareQ)
    (hc : inverseSquareGeneratedQ N A β=some c) : 0≤c.value := by
  unfold inverseSquareGeneratedQ at hc
  obtain ⟨i,hi,hstep⟩ := doubling_loop_trace _ _ 8 c hc
  have he := (inverseSquareStepQ_spec N (8*2^i) A β c hstep).1
  rw [he]
  exact inverseSquareCandidateQ_nonneg N (8*2^i)

/-- The actual computed rational coefficient gives pointwise output error at most the public tolerance on every bounded raw outcome. -/
theorem inverseSquareGeneratedQ_pointwise (N : ℕ) (A β : ℚ) (c : InverseSquareQ)
    (hc : inverseSquareGeneratedQ N A β=some c) (hA : 0<A) (hβ : 0≤β)
    (R : ℝ) (hR : |R|≤(A : ℝ)) :
    |(c.value : ℝ)*R-R/(2*Real.pi/(N : ℝ))^2|≤(β : ℝ) := by
  have he := (inverseSquareGeneratedQ_spec N A β c hc).1
  have hAr : (0 : ℝ)<(A : ℝ) := by exact_mod_cast hA
  have hβr : (0 : ℝ)≤(β : ℝ) := by exact_mod_cast hβ
  calc _ = |(c.value : ℝ)-1/(2*Real.pi/(N : ℝ))^2| * |R| := by
             rw [← abs_mul]
             congr 1
             ring
       _ ≤ ((β : ℝ)/(A : ℝ))*(A : ℝ) :=
         mul_le_mul he hR (abs_nonneg R) (div_nonneg hβr hAr.le)
       _ = _ := div_mul_cancel₀ _ (ne_of_gt hAr)

/-- Nonnegativity and the actually checked relative guard yield the null-variance coefficient bound without any added beta-squared term. -/
theorem inverseSquareGeneratedQ_null_coefficient (N d M : ℕ) (A β : ℚ) (c : InverseSquareQ)
    (hc : inverseSquareGeneratedQ N A β=some c) :
    8*(d : ℝ)*(M : ℝ)*(c.value : ℝ)^2≤32*(d : ℝ)*(M : ℝ)/(2*Real.pi/(N : ℝ))^4 := by
  have hq : (0 : ℝ)≤(c.value : ℝ) := by
    exact_mod_cast inverseSquareGeneratedQ_nonneg N A β c hc
  have hr := (inverseSquareGeneratedQ_spec N A β c hc).2
  have hs := pow_le_pow_left₀ hq hr 2
  calc _ ≤ 8*(d : ℝ)*(M : ℝ)*(2/(2*Real.pi/(N : ℝ))^2)^2 :=
           mul_le_mul_of_nonneg_left hs (by positivity)
       _ = _ := by rw [div_pow,← pow_mul]; norm_num; ring

/-- Every actual successful doubled precision stays within twice the required target bits, apart from the fixed initial scale. -/
theorem inverseSquareGeneratedQ_bits (N : ℕ) (A β : ℚ) (c : InverseSquareQ)
    (hc : inverseSquareGeneratedQ N A β=some c) :
    c.bits≤2*max 16 (inverseSquareBitsQ N A β) := by
  let k := ceilLog2Q (max 1 ((inverseSquareBitsQ N A β : ℚ)/16))
  unfold inverseSquareGeneratedQ at hc
  obtain ⟨i,hi,hstep⟩ := doubling_loop_trace _ _ 8 c hc
  have he := (inverseSquareStepQ_spec N (8*2^i) A β c hstep).1
  change i<k+2 at hi
  have hi' : i≤k+1 := by omega
  calc c.bits = 8*2^i := by rw [he]; rfl
       _ ≤ 8*2^(k+1) := Nat.mul_le_mul_left 8 (pow_le_pow_right₀ (by norm_num) hi')
       _ = 16*2^k := by rw [pow_succ]; ring
       _ ≤ _ := (precision_doubling_bounds (inverseSquareBitsQ N A β)).2


end
end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
