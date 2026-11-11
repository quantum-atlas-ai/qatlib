/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellTail

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Unconditional

Retained Bell Unconditional constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

-- Partition only the finite image of a real observation, not all Nat vectors.
/-- Complete original `finite_image_expectation` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem finite_image_expectation {X Y : Type} [Fintype X] [DecidableEq Y]
    (p : FinDist X) (r : X → Y) (f : X → ℝ) :
    (∑ y ∈ Finset.univ.image r,p.expect (fun x => if r x=y then f x else 0))=
      p.expect f := by
  unfold FinDist.expect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  simp

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n m K : ℕ}

/-- Construction for possible Rvec in the retained bell unconditional model. -/
def possibleRvec (τ : S → S) (n m K : ℕ) : Finset (Fin K → ℕ) :=
  Finset.univ.image (observedRvec (n:=n) (m:=m) τ)

/-- Construction for rvec Total in the retained bell unconditional model. -/
def rvecTotal (ρ : Fin K → ℕ) : ℝ := ∑ j : Fin K,(ρ j : ℝ)

/-- Construction for rvec Mass in the retained bell unconditional model. -/
def rvecMass (τ : Equiv.Perm S) (n m : ℕ) (ρ : Fin K → ℕ) : ℝ :=
  ∏ j : Fin K,matchedCardEventMass τ n m (ρ j)

omit [Fintype S] [Nonempty S] in
/-- Complete original `pooled_matches_cast` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem pooled_matches_cast (τ : S → S) (ω : Fin K → CohortObservation n m τ) :
    (pooledMatches τ ω : ℝ)=rvecTotal (observedRvec τ ω) := by
  simp only [pooledMatches,rvecTotal,Nat.cast_sum]

/-- Complete original `rvec_mass_as_event` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem rvec_mass_as_event (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (ρ : Fin K → ℕ) :
    (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect
      (fun ω => if observedRvec τ ω=ρ then 1 else 0)=rvecMass τ n m ρ := by
  simpa only [pooledStratumPGF,one_pow,rvecMass] using
    pooled_stratum_at_one (n:=n) (m:=m) a b c k hz τ ρ

/-- Complete original `rvec_mass_sum` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem rvec_mass_sum (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) :
    (∑ ρ ∈ possibleRvec τ n m K,rvecMass τ n m ρ)=1 := by
  simp_rw [← rvec_mass_as_event a b c k hz τ]
  rw [possibleRvec,finite_image_expectation]
  exact finite_expect_const _ _

/-- Construction for pooled Bad Mass in the retained bell unconditional model. -/
def pooledBadMass (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (ε : ℝ) : ℝ :=
  (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect
    (fun ω => if ε< |(pooledMeanQ τ ω : ℝ)-bellMean a b c k τ| then 1 else 0)

/-- Complete original `pooled_bad_strata_sum` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem pooled_bad_strata_sum (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (ε : ℝ) :
    (∑ ρ ∈ possibleRvec τ n m K,
      pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε)=
        pooledBadMass (n:=n) (m:=m) (K:=K) a b c k hz τ ε := by
  unfold pooledStratumBadMass
  have hh (ρ : Fin K → ℕ) :
      (fun ω : Fin K → CohortObservation n m τ =>
        if observedRvec τ ω=ρ ∧ ε< |(pooledMeanQ τ ω : ℝ)-bellMean a b c k τ|
        then (1 : ℝ) else 0)=
      (fun ω => if observedRvec τ ω=ρ then
        if ε< |(pooledMeanQ τ ω : ℝ)-bellMean a b c k τ| then 1 else 0 else 0) := by
    funext ω
    split_ifs <;> simp_all
  simp_rw [hh]
  exact finite_image_expectation _ _ _

/-- Construction for pooled Small Mass in the retained bell unconditional model. -/
def pooledSmallMass (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (r₀ : ℝ) : ℝ :=
  (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect
    (fun ω => if (pooledMatches τ ω : ℝ)<r₀ then 1 else 0)

/-- Complete original `pooled_small_strata_sum` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem pooled_small_strata_sum (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (r₀ : ℝ) :
    (∑ ρ ∈ possibleRvec τ n m K,
      if rvecTotal ρ<r₀ then rvecMass τ n m ρ else 0)=
        pooledSmallMass (n:=n) (m:=m) (K:=K) a b c k hz τ r₀ := by
  let p := freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K
  have hfiber (ρ : Fin K → ℕ) :
      (if rvecTotal ρ<r₀ then rvecMass τ n m ρ else 0)=
        p.expect (fun ω => if observedRvec τ ω=ρ then
          if (pooledMatches τ ω : ℝ)<r₀ then 1 else 0 else 0) := by
    rw [← rvec_mass_as_event a b c k hz τ ρ]
    by_cases h : rvecTotal ρ<r₀
    · rw [ite_eq_left h]
      apply congrArg p.expect
      funext ω
      by_cases hρ : observedRvec τ ω=ρ
      · simp [hρ,pooled_matches_cast,h]
      · simp [hρ]
    · rw [ite_eq_right h]
      symm
      calc
        _ = p.expect (fun _ => 0) := by
          apply congrArg p.expect
          funext ω
          by_cases hρ : observedRvec τ ω=ρ
          · simp [hρ,pooled_matches_cast,h]
          · simp [hρ]
        _ = 0 := finite_expect_const _ _
  simp_rw [hfiber]
  exact finite_image_expectation _ _ _

-- The public mean bound replaces the unknown mean only in the denominator.
/-- Complete original `pooled_stratum_public_tail` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem pooled_stratum_public_tail (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (p₀ ε : ℝ) (hmean : bellMean a b c k τ≤p₀) (hε : 0<ε) :
    pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε≤
      2*rvecMass τ n m ρ*Real.exp (-rvecTotal ρ*ε^2/(4*(p₀+ε))) := by
  have hμ := bell_mean_nonneg a b c k hz τ
  have hv : 0<4*(bellMean a b c k τ+ε) := by linarith
  have hnum : 0≤rvecTotal ρ*ε^2 := mul_nonneg
    (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _) (sq_nonneg ε)
  have hrate : -rvecTotal ρ*ε^2/(4*(bellMean a b c k τ+ε))≤
      -rvecTotal ρ*ε^2/(4*(p₀+ε)) := by
    simpa only [neg_mul,neg_div] using
      neg_le_neg (div_le_div_of_nonneg_left hnum hv (by linarith))
  exact (pooled_stratum_low_mean_tail a b c k hz τ ρ ε hε).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate)
      (mul_nonneg (by norm_num) (Finset.prod_nonneg fun j _ =>
        matched_card_mass_nonneg (n:=n) (m:=m) τ (ρ j))))

/-- Complete original `pooled_unconditional_tail` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem pooled_unconditional_tail (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (p₀ ε r₀ : ℝ) (hmean : bellMean a b c k τ≤p₀) (hε : 0<ε) :
    pooledBadMass (n:=n) (m:=m) (K:=K) a b c k hz τ ε≤
      pooledSmallMass (n:=n) (m:=m) (K:=K) a b c k hz τ r₀+
        2*Real.exp (-r₀*ε^2/(4*(p₀+ε))) := by
  let C := 2*Real.exp (-r₀*ε^2/(4*(p₀+ε)))
  have hC : 0≤C := by dsimp [C]; positivity
  have hv : 0<4*(p₀+ε) := by linarith [bell_mean_nonneg a b c k hz τ]
  have hrow (ρ : Fin K → ℕ) :
      pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε≤
        (if rvecTotal ρ<r₀ then rvecMass τ n m ρ else 0)+C*rvecMass τ n m ρ := by
    have hD : 0≤rvecMass τ n m ρ :=
      Finset.prod_nonneg fun j _ => matched_card_mass_nonneg (n:=n) (m:=m) τ (ρ j)
    by_cases h : rvecTotal ρ<r₀
    · rw [ite_eq_left h]
      exact (pooled_stratum_bad_le_mass a b c k hz τ ρ ε).trans
        (le_add_of_nonneg_right (mul_nonneg hC hD))
    · rw [ite_eq_right h,zero_add]
      have he : Real.exp (-rvecTotal ρ*ε^2/(4*(p₀+ε)))≤
          Real.exp (-r₀*ε^2/(4*(p₀+ε))) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ hv.le
        nlinarith [mul_le_mul_of_nonneg_right (le_of_not_gt h) (sq_nonneg ε)]
      calc
        _ ≤ 2*rvecMass τ n m ρ*Real.exp (-rvecTotal ρ*ε^2/(4*(p₀+ε))) :=
          pooled_stratum_public_tail a b c k hz τ ρ p₀ ε hmean hε
        _ ≤ 2*rvecMass τ n m ρ*Real.exp (-r₀*ε^2/(4*(p₀+ε))) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num) hD)
        _ = C*rvecMass τ n m ρ := by dsimp [C]; ring
  calc
    _ = ∑ ρ ∈ possibleRvec τ n m K,
        pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε :=
      (pooled_bad_strata_sum a b c k hz τ ε).symm
    _ ≤ ∑ ρ ∈ possibleRvec τ n m K,
        ((if rvecTotal ρ<r₀ then rvecMass τ n m ρ else 0)+C*rvecMass τ n m ρ) :=
      Finset.sum_le_sum fun ρ _ => hrow ρ
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,
        pooled_small_strata_sum a b c k hz τ r₀,
        rvec_mass_sum a b c k hz τ,mul_one]

/-- Construction for clipped Pooled Mean Q in the retained bell unconditional model. -/
def clippedPooledMeanQ (p₀ : ℚ) (τ : S → S) (ω : Fin K → CohortObservation n m τ) : ℚ :=
  intervalClipQ 0 p₀ (pooledMeanQ τ ω)

/-- Complete original `clipped_pooled_unconditional_tail` guarantee for `RetainedBellUnconditional`; all source hypotheses and output obligations are retained. -/
theorem clipped_pooled_unconditional_tail (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (p₀ : ℚ) (ε r₀ : ℝ) (hmean : bellMean a b c k τ≤(p₀ : ℝ)) (hε : 0<ε) :
    (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect
      (fun ω => if ε< |(clippedPooledMeanQ p₀ τ ω : ℝ)-bellMean a b c k τ| then 1 else 0)≤
        pooledSmallMass (n:=n) (m:=m) (K:=K) a b c k hz τ r₀+
          2*Real.exp (-r₀*ε^2/(4*((p₀ : ℝ)+ε))) := by
  have hpoint (ω : Fin K → CohortObservation n m τ) :
      |(clippedPooledMeanQ p₀ τ ω : ℝ)-bellMean a b c k τ|≤
        |(pooledMeanQ τ ω : ℝ)-bellMean a b c k τ| := by
    simpa only [clippedPooledMeanQ,interval_clip_cast,Rat.cast_zero] using
      interval_clip_contract 0 (p₀ : ℝ) (pooledMeanQ τ ω : ℝ) (bellMean a b c k τ)
        (bell_mean_nonneg a b c k hz τ) hmean
  apply le_trans _ (pooled_unconditional_tail a b c k hz τ (p₀ : ℝ) ε r₀ hmean hε)
  apply finite_expect_mono
  intro ω
  by_cases h : ε< |(clippedPooledMeanQ p₀ τ ω : ℝ)-bellMean a b c k τ|
  · simp only [ite_eq_left h,ite_eq_left (h.trans_le (hpoint ω)),le_refl]
  · simp only [ite_eq_right h]
    split_ifs <;> norm_num

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.rvec_mass_sum
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_small_strata_sum
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_stratum_public_tail
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_unconditional_tail
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.clipped_pooled_unconditional_tail
