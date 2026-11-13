/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TuraevViro10.MainResults.HadamardTest
import Qatlib.Papers.TuraevViro10.MainResults.ApproximationGuarantee
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.BernoulliTail
import Mathlib.Tactic

/-!
# Finite-sample guarantees for Hadamard readout

This module bounds the sampling errors of two Boolean Hadamard-test readouts using indicator
variance, Chebyshev bounds, and a union bound. It converts simultaneous readout accuracy to WRT
and Turaev–Viro error bounds and proves a scaled invariant estimate with success probability at
least `1 - δ` for a supplied readout law. See [AlagicEtAl2010].

## Main statements

* `readout_success`: Simultaneous accuracy of the two empirical readout means.
* `wrt_error_le`: Complex invariant error from componentwise amplitude error.
* `algorithm_guarantee`: Finite-sample scaled Turaev–Viro estimate.

## References

* [Alagic et al., 2010][AlagicEtAl2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TuraevViro10.MainResults.ReadoutSampling

open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge.TuraevViroModel
open Qatlib.Papers.TuraevViro10.MainResults.HadamardTest
open Qatlib.Papers.TuraevViro10.MainResults.ApproximationGuarantee
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling

/-- The real-valued indicator of the first Boolean readout bit. -/
def reBit : Bool × Bool → ℝ := fun b => if b.1 then 1 else 0

/-- The real-valued indicator of the second Boolean readout bit. -/
def imBit : Bool × Bool → ℝ := fun b => if b.2 then 1 else 0

/-- Every function taking only values zero and one lies pointwise between zero and one. -/
theorem bit_mem_Icc {Ω : Type*} (f : Ω → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) (x : Ω) :
    0 ≤ f x ∧ f x ≤ 1 := by
  rcases hf x with h | h <;> simp [h]

/-- The variance of a zero-one-valued function under a finite distribution is at most `1/4`. -/
theorem variance_indicator_le {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p : FinDist Ω) (f : Ω → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    p.variance f ≤ 1 / 4 := by
  rw [FinDist.variance_eq_expect_sq_sub]
  have hsq : p.expect (fun x => f x ^ 2) = p.expect f := by
    unfold FinDist.expect
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases hf x with h | h <;> simp [h]
  rw [hsq]
  nlinarith [sq_nonneg (p.expect f - 1 / 2)]

/-- For `L > 0` and `ε > 0`, the probability that an indicator sample mean differs from its
expectation by more than `ε` is at most `1 / (4 L ε²)`. -/
theorem chebyshev_indicator {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p : FinDist Ω) (f : Ω → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) {L : ℕ} (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) :
    p.probEvent (L := L) (fun ω => ε < |FinDist.avg f ω - p.expect f|) ≤
      1 / (4 * (L : ℝ) * ε ^ 2) := by
  have hcheb := FinDist.chebyshev_avg p f hL ε hε
  have hvar := variance_indicator_le p f hf
  have hden : (0 : ℝ) < (L : ℝ) * ε ^ 2 := by positivity
  calc p.probEvent (fun ω : Fin L → Ω => ε < |FinDist.avg f ω - p.expect f|)
      ≤ p.variance f / ((L : ℝ) * ε ^ 2) := hcheb
    _ ≤ (1 / 4) / ((L : ℝ) * ε ^ 2) := by
        rw [div_le_div_iff_of_pos_right hden]
        exact hvar
    _ = 1 / (4 * (L : ℝ) * ε ^ 2) := by
        field_simp

/-- The probability of the union of two events is at most the sum of their probabilities under
the finite sample law. -/
theorem probEvent_or_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p : FinDist Ω) {L : ℕ}
    (E F : (Fin L → Ω) → Prop) [DecidablePred E] [DecidablePred F] :
    p.probEvent (L := L) (fun ω => E ω ∨ F ω) ≤
      p.probEvent (L := L) E + p.probEvent (L := L) F := by
  have hnn : ∀ ω : Fin L → Ω, 0 ≤ p.probOf ω :=
    fun ω => Finset.prod_nonneg fun i _ => p.nonneg _
  have hpoint : ∀ ω : Fin L → Ω,
      (if E ω ∨ F ω then p.probOf ω else (0 : ℝ)) ≤
        (if E ω then p.probOf ω else 0) + (if F ω then p.probOf ω else 0) := by
    intro ω
    by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF, hnn ω]
  simp only [FinDist.probEvent, Finset.sum_filter]
  calc ∑ ω : Fin L → Ω, (if E ω ∨ F ω then p.probOf ω else 0)
      ≤ ∑ ω : Fin L → Ω,
          ((if E ω then p.probOf ω else 0) + (if F ω then p.probOf ω else 0)) :=
        Finset.sum_le_sum fun ω _ => hpoint ω
    _ = (∑ ω : Fin L → Ω, (if E ω then p.probOf ω else 0)) +
        ∑ ω : Fin L → Ω, (if F ω then p.probOf ω else 0) := Finset.sum_add_distrib

/-- The sample count `max 1 ⌈1 / (2 ε² δ)⌉₊` used for simultaneous Hadamard readout. -/
noncomputable def hadamardShots (ε δ : ℝ) : ℕ := max 1 (Nat.ceil (1 / (2 * ε ^ 2 * δ)))

/-- The selected Hadamard sample count is positive. -/
theorem hadamardShots_pos (ε δ : ℝ) : 0 < hadamardShots ε δ :=
  lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (Nat.le_max_left 1 _)

/-- The selected Hadamard sample count, viewed as a real number, is at least `1 / (2 ε² δ)`. -/
theorem hadamardShots_lower (ε δ : ℝ) :
    1 / (2 * ε ^ 2 * δ) ≤ (hadamardShots ε δ : ℝ) := by
  have hc : 1 / (2 * ε ^ 2 * δ) ≤ (Nat.ceil (1 / (2 * ε ^ 2 * δ)) : ℝ) := Nat.le_ceil _
  have hm : Nat.ceil (1 / (2 * ε ^ 2 * δ)) ≤ hadamardShots ε δ := Nat.le_max_right 1 _
  exact hc.trans (Nat.cast_le.mpr hm)

/-- For positive `ε` and `δ`, the probability that either empirical bit mean differs from its
expectation by more than `ε` is at most `δ` at the selected sample count. -/
theorem readout_fail_le (p : FinDist (Bool × Bool)) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    p.probEvent (L := hadamardShots ε δ)
        (fun ω => ε < |FinDist.avg reBit ω - p.expect reBit| ∨
          ε < |FinDist.avg imBit ω - p.expect imBit|) ≤ δ := by
  classical
  have hL : 0 < hadamardShots ε δ := hadamardShots_pos ε δ
  have hre01 : ∀ x : Bool × Bool, reBit x = 0 ∨ reBit x = 1 := by
    intro x
    unfold reBit
    split <;> simp
  have him01 : ∀ x : Bool × Bool, imBit x = 0 ∨ imBit x = 1 := by
    intro x
    unfold imBit
    split <;> simp
  have hunion := probEvent_or_le p
    (fun ω : Fin (hadamardShots ε δ) → Bool × Bool =>
      ε < |FinDist.avg reBit ω - p.expect reBit|)
    (fun ω : Fin (hadamardShots ε δ) → Bool × Bool =>
      ε < |FinDist.avg imBit ω - p.expect imBit|)
  have hre := chebyshev_indicator p reBit hre01 hL ε hε
  have him := chebyshev_indicator p imBit him01 hL ε hε
  have hsum : 1 / (4 * (hadamardShots ε δ : ℝ) * ε ^ 2) +
      1 / (4 * (hadamardShots ε δ : ℝ) * ε ^ 2) ≤ δ := by
    have hlow := hadamardShots_lower ε δ
    have hpos : (0 : ℝ) < 2 * ε ^ 2 * δ := by positivity
    have hbase : 1 / (2 * ((hadamardShots ε δ : ℝ) * ε ^ 2)) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((hadamardShots ε δ : ℝ) * ε ^ 2))]
      rw [div_le_iff₀ hpos] at hlow
      nlinarith [hlow]
    have heq : 1 / (4 * (hadamardShots ε δ : ℝ) * ε ^ 2) +
        1 / (4 * (hadamardShots ε δ : ℝ) * ε ^ 2) =
        1 / (2 * ((hadamardShots ε δ : ℝ) * ε ^ 2)) := by
      field_simp
      ring
    rw [heq]
    exact hbase
  exact hunion.trans ((add_le_add hre him).trans hsum)

/-- For positive `ε` and `δ`, both empirical bit means are within `ε` of their expectations with
probability at least `1 - δ` at the selected sample count. See [AlagicEtAl2010]. -/
theorem readout_success (p : FinDist (Bool × Bool)) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    1 - δ ≤ p.probEvent (L := hadamardShots ε δ)
      (fun ω => |FinDist.avg reBit ω - p.expect reBit| ≤ ε ∧
        |FinDist.avg imBit ω - p.expect imBit| ≤ ε) := by
  classical
  have hfail := readout_fail_le p ε δ hε hδ
  have hcompl := probEvent_compl (L := hadamardShots ε δ) p
    (fun ω => |FinDist.avg reBit ω - p.expect reBit| ≤ ε ∧
      |FinDist.avg imBit ω - p.expect imBit| ≤ ε)
  have hbad : p.probEvent (L := hadamardShots ε δ)
      (fun ω => ¬(|FinDist.avg reBit ω - p.expect reBit| ≤ ε ∧
        |FinDist.avg imBit ω - p.expect imBit| ≤ ε)) ≤ δ := by
    refine le_trans (le_of_eq ?_) hfail
    refine probEvent_congr p _ _ (fun ω => ?_)
    constructor
    · intro h
      by_cases h1 : |FinDist.avg reBit ω - p.expect reBit| ≤ ε
      · by_cases h2 : |FinDist.avg imBit ω - p.expect imBit| ≤ ε
        · exact absurd ⟨h1, h2⟩ h
        · exact Or.inr (lt_of_not_ge h2)
      · exact Or.inl (lt_of_not_ge h1)
    · intro h hc
      rcases h with h | h
      · exact absurd hc.1 (not_le.mpr h)
      · exact absurd hc.2 (not_le.mpr h)
  linarith [hcompl]

/-- The mean of a nonempty finite sample of values in `[0, 1]` also lies in `[0, 1]`. -/
theorem avg_mem_Icc {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {L : ℕ} (hL : 0 < L)
    (f : Ω → ℝ) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (ω : Fin L → Ω) :
    FinDist.avg f ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hLR : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  have hsum0 : 0 ≤ ∑ k : Fin L, f (ω k) := Finset.sum_nonneg fun k _ => h0 _
  have hsum1 : (∑ k : Fin L, f (ω k)) ≤ (L : ℝ) := by
    have hb : (∑ k : Fin L, f (ω k)) ≤ ∑ _k : Fin L, (1 : ℝ) :=
      Finset.sum_le_sum fun k _ => h1 (ω k)
    simpa using hb
  unfold FinDist.avg
  constructor
  · exact div_nonneg hsum0 (le_of_lt hLR)
  · rw [div_le_iff₀ hLR]
    simpa using hsum1

/-- For an amplitude of norm at most one and component estimates bounded in absolute value by
one, componentwise error at most `ε` gives squared-modulus error at most `4 ε`. -/
theorem modulusSq_error_le {a : ℂ} {x y ε : ℝ}
    (hx : |x - a.re| ≤ ε) (hy : |y - a.im| ≤ ε) (ha : ‖a‖ ≤ 1)
    (hbx : |x| ≤ 1) (hby : |y| ≤ 1) :
    |x ^ 2 + y ^ 2 - ‖a‖ ^ 2| ≤ 4 * ε := by
  have hare : |a.re| ≤ 1 := le_trans (Complex.abs_re_le_norm a) ha
  have haim : |a.im| ≤ 1 := le_trans (Complex.abs_im_le_norm a) ha
  have hbx2 : |x + a.re| ≤ 2 := by
    have hx' := abs_le.mp hbx
    have ha' := abs_le.mp hare
    rw [abs_le]
    constructor <;> linarith
  have hby2 : |y + a.im| ≤ 2 := by
    have hy' := abs_le.mp hby
    have ha' := abs_le.mp haim
    rw [abs_le]
    constructor <;> linarith
  have hx' : |x ^ 2 - a.re ^ 2| ≤ 2 * ε := by
    rw [show x ^ 2 - a.re ^ 2 = (x - a.re) * (x + a.re) by ring, abs_mul]
    have hmul := mul_le_mul hx hbx2 (abs_nonneg (x + a.re))
      (le_trans (abs_nonneg (x - a.re)) hx)
    nlinarith [hmul]
  have hy' : |y ^ 2 - a.im ^ 2| ≤ 2 * ε := by
    rw [show y ^ 2 - a.im ^ 2 = (y - a.im) * (y + a.im) by ring, abs_mul]
    have hmul := mul_le_mul hy hby2 (abs_nonneg (y + a.im))
      (le_trans (abs_nonneg (y - a.im)) hy)
    nlinarith [hmul]
  have hsq : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hsq]
  have hsplit : x ^ 2 + y ^ 2 - (a.re ^ 2 + a.im ^ 2) =
      (x ^ 2 - a.re ^ 2) + (y ^ 2 - a.im ^ 2) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hx' hy').trans (by linarith))

/-- For genus at least one, normalized-invariant error at most `4 ε` scales to invariant error
at most `D ^ (2 * (g - 1)) * 4 ε`. -/
theorem tv_error_le {P ι : Type*} [Fintype P] (M : TuraevViroModel P ι) {g : ℕ}
    (hg : 1 ≤ g) (x : ι) {est ε : ℝ}
    (h : |est - M.normalizedTvInvariant g x| ≤ 4 * ε) :
    |M.D ^ (2 * (g - 1)) * est - M.tvInvariant g x| ≤ M.D ^ (2 * (g - 1)) * (4 * ε) :=
  tvEstimate_error_le M hg x est (4 * ε) h

/-- Componentwise amplitude errors at most `ε` give WRT error at most `D ^ (g - 1) * 2 ε` after
scaling. See [AlagicEtAl2010]. -/
theorem wrt_error_le {P ι : Type*} [Fintype P] (M : TuraevViroModel P ι) (g : ℕ) (x : ι)
    {xr yi ε : ℝ} (hxr : |xr - (M.amplitude g x).re| ≤ ε)
    (hyi : |yi - (M.amplitude g x).im| ≤ ε) :
    ‖((M.D : ℝ) : ℂ) ^ (g - 1) * (⟨xr, yi⟩ : ℂ) - M.wrtInvariant g x‖ ≤
      M.D ^ (g - 1) * (2 * ε) := by
  have hclose : ‖(⟨xr, yi⟩ : ℂ) - M.amplitude g x‖ ≤ 2 * ε := by
    have h := Complex.norm_le_abs_re_add_abs_im ((⟨xr, yi⟩ : ℂ) - M.amplitude g x)
    have hre : ((⟨xr, yi⟩ : ℂ) - M.amplitude g x).re = xr - (M.amplitude g x).re := by
      simp
    have him : ((⟨xr, yi⟩ : ℂ) - M.amplitude g x).im = yi - (M.amplitude g x).im := by
      simp
    rw [hre, him] at h
    linarith
  exact wrtScaled_error_le M g x (2 * ε) hclose

/-- For genus at least one and positive `ε` and `δ`, a readout law with the stated amplitude
means yields scaled Turaev–Viro error at most `D ^ (2 * (g - 1)) * 4 ε` with probability at
least `1 - δ` using `hadamardShots (ε / 2) δ` samples. See [AlagicEtAl2010]. -/
theorem algorithm_guarantee {P ι : Type*} [Fintype P] (M : TuraevViroModel P ι)
    {g : ℕ} (hg : 1 ≤ g) (x : ι) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (p : FinDist (Bool × Bool))
    (hre : p.expect reBit = (1 + (M.amplitude g x).re) / 2)
    (him : p.expect imBit = (1 + (M.amplitude g x).im) / 2) :
    1 - δ ≤ p.probEvent (L := hadamardShots (ε / 2) δ)
      (fun ω => |M.D ^ (2 * (g - 1)) *
          ((2 * FinDist.avg reBit ω - 1) ^ 2 + (2 * FinDist.avg imBit ω - 1) ^ 2) -
            M.tvInvariant g x| ≤
        M.D ^ (2 * (g - 1)) * (4 * ε)) := by
  classical
  have hL : 0 < hadamardShots (ε / 2) δ := hadamardShots_pos (ε / 2) δ
  have hgood := readout_success p (ε / 2) δ (by positivity) hδ
  refine hgood.trans (probEvent_mono p ?_)
  intro ω hω
  obtain ⟨h1, h2⟩ := hω
  rw [hre] at h1
  rw [him] at h2
  have hx' : |(2 * FinDist.avg reBit ω - 1) - (M.amplitude g x).re| ≤ ε := by
    have heq : 2 * FinDist.avg reBit ω - 1 - (M.amplitude g x).re =
        2 * (FinDist.avg reBit ω - (1 + (M.amplitude g x).re) / 2) := by ring
    rw [heq, abs_mul]
    have h2abs : |(2 : ℝ)| = 2 := by norm_num
    rw [h2abs]
    linarith
  have hy' : |(2 * FinDist.avg imBit ω - 1) - (M.amplitude g x).im| ≤ ε := by
    have heq : 2 * FinDist.avg imBit ω - 1 - (M.amplitude g x).im =
        2 * (FinDist.avg imBit ω - (1 + (M.amplitude g x).im) / 2) := by ring
    rw [heq, abs_mul]
    have h2abs : |(2 : ℝ)| = 2 := by norm_num
    rw [h2abs]
    linarith
  have hx1 : |2 * FinDist.avg reBit ω - 1| ≤ 1 := by
    have hb := avg_mem_Icc (hL := hL) reBit
      (fun b => (by unfold reBit; split <;> norm_num : 0 ≤ reBit b))
      (fun b => (by unfold reBit; split <;> norm_num : reBit b ≤ 1)) ω
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  have hy1 : |2 * FinDist.avg imBit ω - 1| ≤ 1 := by
    have hb := avg_mem_Icc (hL := hL) imBit
      (fun b => (by unfold imBit; split <;> norm_num : 0 ≤ imBit b))
      (fun b => (by unfold imBit; split <;> norm_num : imBit b ≤ 1)) ω
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  have ha : ‖M.amplitude g x‖ ≤ 1 := M.amplitude_le_one g x
  have hmod : |(2 * FinDist.avg reBit ω - 1) ^ 2 + (2 * FinDist.avg imBit ω - 1) ^ 2 -
      ‖M.amplitude g x‖ ^ 2| ≤ 4 * ε :=
    modulusSq_error_le hx' hy' ha hx1 hy1
  have hmod' : |(2 * FinDist.avg reBit ω - 1) ^ 2 + (2 * FinDist.avg imBit ω - 1) ^ 2 -
      M.normalizedTvInvariant g x| ≤ 4 * ε := by
    rwa [normalizedTvInvariant_eq_normSq M hg x]
  exact tv_error_le M hg x hmod'

end Qatlib.Papers.TuraevViro10.MainResults.ReadoutSampling
