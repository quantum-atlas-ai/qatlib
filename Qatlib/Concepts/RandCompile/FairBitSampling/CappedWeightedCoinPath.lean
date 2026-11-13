/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalRejectionConsumers
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

/-!
# Capped fair-bit weighted sampling for qDRIFT

This module implements capped weighted rejection sampling from finite fair-bit records, with
explicit bit and comparison counters. It proves that the pathwise implementation has the
rational rejection-run law and derives the mixture of the normalized weight law with a fallback
point mass, for use in qDRIFT [Campbell2019].

For positive weight mass, the one-trial rejection probability is at most one half. The final
cost theorem gives both worst-case path costs and expected bit and comparison bounds.

## Main statements

* `fairQdriftPick`: returns a sampled label and its bit and comparison costs.
* `fair_bit_qdrift_actual_sampler_law`: computes the capped sampler probability law.
* `fair_bit_qdrift_actual_coin_path_cost`: bounds pathwise and expected sampling costs.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.RandCompile.FairBitSampling

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal
set_option autoImplicit false

/-- Performs one counted weighted-decoding trial from a `b`-bit record, updating bit and
comparison counters and returning either an accepted label or a pending configuration. -/
def fairQdriftTrial {L : ℕ} (w : Fin L → ℕ) (b : ℕ) (BD : ℕ × ℕ)
    (bits : Reg b) : Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ) :=
  let decoded := weightDecodeCounted w (bitVecEquiv b bits).val
  match decoded.1 with
  | some j => .inl (j, BD.1 + b, BD.2 + decoded.2)
  | none => .inr (BD.1 + b, BD.2 + decoded.2)

/-- Executes at most `R` counted sampling trials from a finite bit record, stopping at
acceptance and returning the final configuration and number of trials performed. -/
def fairQdriftRawRun {L : ℕ} (w : Fin L → ℕ) (b : ℕ) :
    (R : ℕ) → (Fin R → Reg b) → Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ) →
      Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ) × ℕ
  | 0, _, c => (c, 0)
  | _ + 1, _, .inl out => (.inl out, 0)
  | R + 1, ω, .inr BD =>
    let result := fairQdriftRawRun w b R (Fin.tail ω) (fairQdriftTrial w b BD (ω 0))
    (result.1, 1 + result.2)

/-- Extracts an accepted label or substitutes `j0` for a pending configuration, preserving its
bit and comparison counters. -/
def fairQdriftFallback {L : ℕ} (j0 : Fin L)
    (c : Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ)) : Fin L × ℕ × ℕ :=
  match c with
  | .inl out => out
  | .inr BD => (j0, BD.1, BD.2)

/-- The capped fair-bit weighted sampler with fallback label `j0` and counted costs; zero total
weight returns the fallback with zero costs. -/
def fairQdriftPick {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (ω : Fin R → Reg (Nat.clog 2 (weightTotal w))) : Fin L × ℕ × ℕ :=
  if weightTotal w = 0 then (j0, 0, 0) else
    fairQdriftFallback j0 (fairQdriftRawRun w _ R ω (.inr (0, 0))).1

/-- The uniform finite distribution on a nonempty finite type. -/
noncomputable def fairQdriftUniform (A : Type) [Fintype A] [Nonempty A] : FinDist A where
  prob _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- The finite distribution obtained by summing source probabilities over the fibers of a
function. -/
noncomputable def fairQdriftPushforward {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq B] (d : FinDist A) (f : A → B) : FinDist B where
  prob y := ∑ a, if f a = y then d.prob a else 0
  nonneg y := Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact d.nonneg a
    · exact le_rfl
  sum_one := by
    rw [Finset.sum_comm]
    simpa [eq_comm] using d.sum_one

/-- The output-label law obtained by running the capped sampler on a uniformly distributed
finite bit record. -/
noncomputable def fairQdriftLaw {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ) :
    FinDist (Fin L) :=
  fairQdriftPushforward (fairQdriftUniform (Fin R → Reg (Nat.clog 2 (weightTotal w))))
    (fun ω => (fairQdriftPick w j0 R ω).1)

/-- A uniform record of length `R + 1` can be sampled as a uniform head followed by an
independent uniform tail, before applying any function. -/
private theorem uniform_record_split {A B : Type} [Fintype A] [Nonempty A]
    (R : ℕ) (f : (Fin (R + 1) → A) → B) :
    (PMF.uniformOfFintype' (Fin (R + 1) → A)).map f =
      (PMF.uniformOfFintype' A).bind (fun a =>
        (PMF.uniformOfFintype' (Fin R → A)).map (fun ω => f (Fin.cons a ω))) := by
  classical
  ext y
  simp only [PMF.map_apply, PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype'_apply]
  rw [← (Fin.consEquiv (fun _ : Fin (R + 1) => A)).sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, pow_succ]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  change (if y = f (Fin.cons a ω) then _ else 0) = _
  split_ifs <;> simp_all [ENNReal.mul_inv, mul_comm]

/-- The costed fair-bit law is the uniform `b`-bit record law with deterministic cost `b`. -/
private theorem fairBitsCosted_eq_uniform (b : ℕ) :
    fairBitsCosted b = (PMF.uniformOfFintype' (Reg b)).map (fun ω => (ω,b)) := by
  ext z
  rcases z with ⟨ω,k⟩
  rw [fair_bit_program_joint_distribution, PMF.map_apply, tsum_fintype]
  by_cases hk : k = b
  · subst k
    simp
  · simp [hk]

/-- A uniform bit record passed through the counted trial gives the rational counted next-step
law. -/
theorem fairQdriftTrial_law {L : ℕ} (w : Fin L → ℕ) (b : ℕ) (BD : ℕ × ℕ) :
    (PMF.uniformOfFintype' (Reg b)).map (fairQdriftTrial w b BD) =
      rationalCountedNext w b BD := by
  rw [rationalCountedNext, fairBitsCosted_eq_uniform, PMF.map_comp]
  congr 1

/-- Running the deterministic sampler on a uniform finite bit record gives the same costed law
as the bounded probabilistic rejection run. -/
theorem fairQdriftRawRun_law {L : ℕ} (w : Fin L → ℕ) (b R : ℕ)
    (c : Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ)) :
    (PMF.uniformOfFintype' (Fin R → Reg b)).map (fun ω => fairQdriftRawRun w b R ω c) =
      runFor (rationalCountedNext w b) R c := by
  induction R generalizing c with
  | zero =>
    change (PMF.uniformOfFintype' (Fin 0 → Reg b)).map (Function.const _ (c,0)) = PMF.pure (c,0)
    exact PMF.map_const _ _
  | succ R ih =>
    cases c with
    | inl out =>
      rw [runFor_halted]
      change (PMF.uniformOfFintype' (Fin (R+1) → Reg b)).map
          (Function.const _ (Sum.inl out,0)) = PMF.pure (Sum.inl out,0)
      exact PMF.map_const _ _
    | inr BD =>
      rw [uniform_record_split]
      simp only [fairQdriftRawRun, Fin.tail_cons, Fin.cons_zero]
      have hm (bits : Reg b) :
          (PMF.uniformOfFintype' (Fin R → Reg b)).map
            (fun ω => ((fairQdriftRawRun w b R ω (fairQdriftTrial w b BD bits)).1,
              1 + (fairQdriftRawRun w b R ω (fairQdriftTrial w b BD bits)).2)) =
          CostedLaw.charge 1 (runFor (rationalCountedNext w b) R (fairQdriftTrial w b BD bits)) := by
        rw [CostedLaw.charge, ← ih, PMF.map_comp]
        rfl
      simp_rw [hm]
      rw [runFor, tick, CostedLaw.bind, PMF.bind_map, ← fairQdriftTrial_law, PMF.bind_map]
      rfl

/-- For positive weight mass, the sampler's joint output-label and cost law equals the
rejection-run law followed by the fallback operation. -/
theorem fairQdriftPick_law {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (hW : 0 < weightTotal w) :
    (PMF.uniformOfFintype' (Fin R → Reg (Nat.clog 2 (weightTotal w)))).map
        (fairQdriftPick w j0 R) =
      (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R).map
        (fun z => fairQdriftFallback j0 z.1) := by
  rw [rationalRejectionRun, ← fairQdriftRawRun_law, PMF.map_comp]
  congr 1
  funext ω
  simp [fairQdriftPick, ne_of_gt hW]

/-- The real probability of an event under a uniform finite law is the sum of
reciprocal-cardinality weights over its satisfying elements. -/
private theorem uniform_event_real {A : Type} [Fintype A] [Nonempty A]
    (E : A → Prop) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (PMF.uniformOfFintype' A) E).toReal =
      ∑ a, if E a then (Fintype.card A : ℝ)⁻¹ else 0 := by
  classical
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype, ENNReal.toReal_sum (fun a _ => by
    dsimp
    split_ifs <;> simp [PMF.uniformOfFintype'_apply])]
  apply Finset.sum_congr rfl
  intro a _
  dsimp
  by_cases h : E a <;> simp [h, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv]

/-- Event probability under a mapped probability law equals the probability of the event's
preimage under the original law. -/
private theorem event_map {A B : Type} (p : PMF A) (f : A → B) (E : B → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (p.map f) E = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun a => E (f a)) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map p f _

/-- For positive weight mass, a sampler label probability equals the real probability that the
rejection run followed by fallback returns that label. -/
theorem fairQdriftLaw_prob_event {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (hW : 0 < weightTotal w) (j : Fin L) :
    (fairQdriftLaw w j0 R).prob j =
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
        (fun z => (fairQdriftFallback j0 z.1).1 = j)).toReal := by
  have he := event_map (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
    (fun z => fairQdriftFallback j0 z.1) (fun out => out.1 = j)
  rw [← he, ← fairQdriftPick_law w j0 R hW, event_map, uniform_event_real]
  simp [fairQdriftLaw, fairQdriftPushforward, fairQdriftUniform]

/-- A fallback-label event splits into the accepted-label event and, when the label equals the
fallback, the pending event. -/
private theorem fallback_event_split {L : ℕ} (j0 j : Fin L)
    (p : PMF (Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ) × ℕ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => (fairQdriftFallback j0 z.1).1 = j) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => rejectionOutcome z.1 = Sum.inl j) +
        (if j = j0 then 1 else 0) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => rejectionOutcome z.1 = Sum.inr ()) := by
  classical
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply tsum_congr
  intro z
  rcases z with ⟨c,k⟩
  rcases c with ⟨i,B,D⟩ | ⟨B,D⟩ <;>
    simp [fairQdriftFallback, rejectionOutcome, eq_comm]

/-- For positive total weight `W` and width `b = Nat.clog 2 W`, the real one-trial rejection
mass is `1 - W / 2^b` and lies between zero and one half. -/
theorem fairQdriftReject_real {L : ℕ} (w : Fin L → ℕ) (hW : 0 < weightTotal w) :
    let b := Nat.clog 2 (weightTotal w)
    (rationalRejectMass w b).toReal = 1 - (weightTotal w : ℝ) / (2 ^ b : ℝ) ∧
      0 ≤ 1 - (weightTotal w : ℝ) / (2 ^ b : ℝ) ∧
      1 - (weightTotal w : ℝ) / (2 ^ b : ℝ) ≤ 1/2 := by
  let b := Nat.clog 2 (weightTotal w)
  have hc := rational_effective_truncation_consumer L w 0 hW
  have he : (rationalRejectMass w b).toReal = 1 - (weightTotal w : ℝ) / (2 ^ b : ℝ) := by
    change (((2^b - weightTotal w : ℕ) : ℝ≥0∞) / ((2^b : ℕ) : ℝ≥0∞)).toReal = _
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
    rw [Nat.cast_sub hc.1, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [b]
    field_simp
  refine ⟨he, he ▸ ENNReal.toReal_nonneg, ?_⟩
  have hh := ENNReal.toReal_mono (by finiteness : (1/2 : ℝ≥0∞) ≠ ⊤) hc.2.1
  rw [← he]
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hh

/-- For positive total weight, the capped sampler law is `(1 - q^R)` times the normalized weight
law plus `q^R` times the fallback point mass, where `q` is the one-trial rejection
probability. See [Campbell2019]. -/
theorem fair_bit_qdrift_actual_sampler_law (L R : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (hW : 0 < weightTotal w) :
    let b := Nat.clog 2 (weightTotal w)
    let q := 1 - (weightTotal w : ℝ) / (2 ^ b : ℝ)
    ∀ j : Fin L, (fairQdriftLaw w j0 R).prob j =
      (1-q^R)*(w j : ℝ)/(weightTotal w : ℝ) + q^R*(if j=j0 then 1 else 0) := by
  (try dsimp only)
  intro j
  let b := Nat.clog 2 (weightTotal w)
  have hc := rational_effective_truncation_consumer L w R hW
  have hf := rational_finite_return_pending_and_first_stop L w b R hW hc.1
  have hq := (fairQdriftReject_real w hW).1
  have hq1 : (rationalRejectMass w b)^R ≤ 1 :=
    pow_le_one₀ (by positivity) (hc.2.1.trans (by norm_num))
  have hqt : (rationalRejectMass w b)^R ≠ ⊤ := ne_top_of_le_ne_top (by simp) hq1
  have hp : (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by positivity)
  have hs : 1 - (rationalRejectMass w b)^R ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  rw [fairQdriftLaw_prob_event w j0 R hW, fallback_event_split, hf.1, hf.2.1]
  split_ifs with hj <;> simp only [one_mul, zero_mul, add_zero]
  all_goals
    try rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp hs) hqt]
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, ENNReal.toReal_sub_of_le hq1 (by simp),
      ENNReal.toReal_one, ENNReal.toReal_pow]
    simp only [b] at *
    rw [hq]
    ring

/-- The real expectation of a natural-valued function under a uniform finite law is its
uniformly weighted finite sum. -/
private theorem uniform_nat_expect_real {A : Type} [Fintype A] [Nonempty A] (f : A → ℕ) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.uniformOfFintype' A) (fun a => (f a : ℝ≥0∞))).toReal =
      ∑ a, (Fintype.card A : ℝ)⁻¹ * (f a : ℝ) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype, ENNReal.toReal_sum (fun a _ =>
    ENNReal.mul_ne_top ((PMF.uniformOfFintype' A).apply_ne_top a) (by simp))]
  simp [PMF.uniformOfFintype'_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- Every length-`R` record of `b` bits has uniform mass `(1/2)^(b * R)`. -/
private theorem raw_uniform_mass (b R : ℕ) :
    (Fintype.card (Fin R → Reg b) : ℝ)⁻¹ = ((2 : ℝ)⁻¹)^(b*R) := by
  rw [Fintype.card_fun, card_reg, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat]
  simp only [← inv_pow, pow_mul]

/-- Applying fallback preserves the configuration's counted bit usage. -/
private theorem fallback_bits {L : ℕ} (j0 : Fin L)
    (c : Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ)) :
    (fairQdriftFallback j0 c).2.1 = rejectionBits c := by cases c <;> rfl

/-- Applying fallback preserves the configuration's counted comparison usage. -/
private theorem fallback_comparisons {L : ℕ} (j0 : Fin L)
    (c : Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ)) :
    (fairQdriftFallback j0 c).2.2 = rejectionComparisons c := by cases c <;> rfl

/-- For positive weight mass, every sampler path uses at most `b * R` bits and `L * R`
comparisons, where `b` is the sampling width. The corresponding uniform expectations are at
most `2 * b` and `2 * L`. See [Campbell2019]. -/
theorem fair_bit_qdrift_actual_coin_path_cost (L R : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (hW : 0 < weightTotal w) :
    let b := Nat.clog 2 (weightTotal w)
    (∀ ω : Fin R → Reg b, (fairQdriftPick w j0 R ω).2.1 ≤ b*R ∧
      (fairQdriftPick w j0 R ω).2.2 ≤ L*R) ∧
    (∑ ω : Fin R → Reg b, ((2 : ℝ)⁻¹)^(b*R)*((fairQdriftPick w j0 R ω).2.1 : ℝ)) ≤ 2*b ∧
    (∑ ω : Fin R → Reg b, ((2 : ℝ)⁻¹)^(b*R)*((fairQdriftPick w j0 R ω).2.2 : ℝ)) ≤ 2*L := by
  let b := Nat.clog 2 (weightTotal w)
  have hc := rational_effective_truncation_consumer L w R hW
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    have hz : fairQdriftRawRun w b R ω (.inr (0,0)) ∈ (rationalRejectionRun w b R).support := by
      rw [rationalRejectionRun, ← fairQdriftRawRun_law]
      exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨ω, PMF.mem_support_uniformOfFintype' ω, rfl⟩
    simpa only [fairQdriftPick, if_neg (ne_of_gt hW), fallback_bits, fallback_comparisons] using
      hc.2.2.2.2.2.2 _ hz
  · have he := congrArg (fun p => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => (z.2.1 : ℝ≥0∞)))
      (fairQdriftPick_law w j0 R hW)
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
        fallback_bits] at he
    have ht := congrArg ENNReal.toReal he
    rw [uniform_nat_expect_real, raw_uniform_mass] at ht
    rw [ht]
    have h := ENNReal.toReal_mono (ENNReal.natCast_ne_top (2*b)) hc.2.2.2.2.1
    simpa using h
  · have he := congrArg (fun p => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => (z.2.2 : ℝ≥0∞)))
      (fairQdriftPick_law w j0 R hW)
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
        fallback_comparisons] at he
    have ht := congrArg ENNReal.toReal he
    rw [uniform_nat_expect_real, raw_uniform_mass] at ht
    rw [ht]
    have h := ENNReal.toReal_mono (ENNReal.natCast_ne_top (2*L)) hc.2.2.2.2.2.1
    simpa using h

end Qatlib.Concepts.RandCompile.FairBitSampling
