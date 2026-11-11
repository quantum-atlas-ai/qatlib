/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.EffectiveFourierRecoveryDefs

/-!
# Effective Fourier recovery and modular exponentiation

This module proves the three specifications for effective Fourier recovery, combining
presentation normalization, arithmetic and Fourier circuit results, and sampling and decoding
guarantees. It also verifies the semantics, length, control count, and bijectivity properties of
the modular multiplication word `modeExpWord`. [Kitaev1995]

## Main statements

* `stageA_fourier_recovery_clause1`: establishes the presentation and exact phase readout
  specification.
* `stageA_fourier_recovery_clause2`: establishes the arithmetic and Fourier circuit
  specification.
* `stageA_fourier_recovery_clause3`: establishes the sampling, generation, and decoding
  specification.
* `stageA_fourier_recovery_clause2_modexp`: establishes the modular exponentiation word
  specification.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open Qatlib
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Concepts.HspRecovery.AbelianSampling
set_option warningAsError false

/-- Establishes the conjunction of presentation invariance, normalized coordinate and word
equality laws, Smith computation bounds, and exact phase readout in
`stageA_fourier_recovery_clause1_spec`. -/
theorem stageA_fourier_recovery_clause1 : stageA_fourier_recovery_clause1_spec := by
  refine ⟨@compactRecovery_factors_canonical,
          @compactRecoveryEquiv_word,
          @compactRecovery_wordEq,
          @compactRecovery_generator,
          @smithRunBinaryEuclid_factors_invariant,
          @smithRunBinaryEuclid_control_bound,
          @smithRunBinaryEuclid_division_bound,
          fun hM => qpe_exact_readout hM⟩

/-- Establishes the arithmetic circuit, finite gate, local Fourier transform, approximation
error, and exact phase readout guarantees in `stageA_fourier_recovery_clause2_spec`. -/
theorem stageA_fourier_recovery_clause2 : stageA_fourier_recovery_clause2_spec := by
  refine ⟨boolean_word_adder_resources,
          boolean_word_adder_coherent,
          boolean_word_mul_basis,
          boolean_word_mul_coherent,
          boolean_word_div_value,
          @subsetActiveWorks_length,
          finiteCodeMatrix_unitary,
          fun n => ⟨(localQFT_exact_gate_counts_and_wires n).2.2.2.1,
                    (localQFT_exact_gate_counts_and_wires n).2.2.2.2.1⟩,
          fun n b => (approxLocalQFT_actual_filter_and_cost n b).2.2.2.1,
          approxLocalQFT_forward_inverse_born_error,
          fun hM => qpe_exact_readout hM⟩

/-- Establishes the cyclic and hidden subgroup sampling laws, oracle perturbation bound,
stabilizer generation guarantee, rational scan properties, and exact phase readout in
`stageA_fourier_recovery_clause3_spec`. -/
theorem stageA_fourier_recovery_clause3 : stageA_fourier_recovery_clause3_spec := by
  refine ⟨cyclic_actual_sampling_semantics_cost,
          cyclic_period_born_uniform_multiples,
          hiddenSubgroupSamplingCircuit_resources,
          marginalProbLeft_hiddenSubgroupSampling_oracle_error,
          abelianStabilizerGenerationSubgoal,
          boundedRationalScan_count,
          boundedRationalScan_sound,
          fun hM => qpe_exact_readout hM⟩

/-- Applying a modular word with head `g` first applies `g` and then the tail word. -/
theorem applyModWord_cons {n : ℕ} (g : ZMod n → ZMod n) (w : List (ZMod n → ZMod n))
    (x : ZMod n) :
    applyModWord (g :: w) x = applyModWord w (g x) := rfl

/-- The modular multiplication schedule beginning at bit position `k` sends `x` to `x * (a ^ (2
^ k)) ^ bitsValue bs`. -/
theorem applyModWord_schedule {n : ℕ} (a : ZMod n) :
    ∀ (k : ℕ) (bs : List Bool) (x : ZMod n),
      applyModWord ((modeExpSchedule a bs k).map (fun p => modMulGate p.1 p.2)) x
        = x * (a ^ 2 ^ k) ^ bitsValue bs := by
  intro k bs
  induction bs generalizing k with
  | nil =>
      intro x
      simp [applyModWord, modeExpSchedule, bitsValue]
  | cons b bs ih =>
      intro x
      rw [modeExpSchedule, List.map_cons, applyModWord_cons]
      rw [ih (k + 1)]
      simp only [modMulGate, bitsValue]
      have hpow : a ^ 2 ^ (k + 1) = (a ^ 2 ^ k) ^ 2 := by
        have h1 : 2 ^ (k + 1) = 2 ^ k * 2 := by
          rw [pow_succ]
        rw [h1, pow_mul]
      cases b with
      | true =>
        calc (a ^ 2 ^ k * x) * (a ^ 2 ^ (k + 1)) ^ bitsValue bs
            = x * ((a ^ 2 ^ k) ^ 1 * (a ^ 2 ^ k) ^ (2 * bitsValue bs)) := by
                rw [hpow, ← pow_mul]
                ring
          _ = x * (a ^ 2 ^ k) ^ (1 + 2 * bitsValue bs) := by
                rw [← pow_add]
      | false =>
        calc x * (a ^ 2 ^ (k + 1)) ^ bitsValue bs
            = x * ((a ^ 2 ^ k) ^ 0 * (a ^ 2 ^ k) ^ (2 * bitsValue bs)) := by
                rw [hpow, ← pow_mul]
                ring
          _ = x * (a ^ 2 ^ k) ^ (0 + 2 * bitsValue bs) := by
                rw [← pow_add]

/-- The modular exponentiation word for exponent `e` sends `x` to `x * a ^ e`. -/
theorem modeExpWord_semantics {n : ℕ} (a : ZMod n) (e : ℕ) (x : ZMod n) :
    applyModWord (modeExpWord a e) x = x * a ^ e := by
  rw [modeExpWord, applyModWord_schedule]
  have h1 : a ^ 2 ^ 0 = a := by simp
  rw [h1, modExpBits_value]

/-- The modular exponentiation schedule has one entry for each input bit. -/
theorem modeExpSchedule_length {n : ℕ} (a : ZMod n) :
    ∀ (bs : List Bool) (k : ℕ), (modeExpSchedule a bs k).length = bs.length := by
  intro bs k
  induction bs generalizing k with
  | nil => simp [modeExpSchedule]
  | cons b bs ih => simp [modeExpSchedule, ih (k + 1)]

/-- The modular exponentiation word has the same length as the bit list encoding its exponent. -/
theorem modeExpWord_length {n : ℕ} (a : ZMod n) (e : ℕ) :
    (modeExpWord a e).length = (modExpBits e).length := by
  rw [modeExpWord, List.length_map]
  exact modeExpSchedule_length a (modExpBits e) 0

/-- The schedule preserves the number of true control bits. -/
theorem modeExpSchedule_count {n : ℕ} (a : ZMod n) :
    ∀ (bs : List Bool) (k : ℕ),
      ((modeExpSchedule a bs k).map (fun p => p.2)).count true = bs.count true := by
  intro bs k
  induction bs generalizing k with
  | nil => simp [modeExpSchedule]
  | cons b bs ih =>
      rw [modeExpSchedule, List.map_cons]
      have hc : ∀ (c : Bool) (l : List Bool),
          (c :: l).count true = (if c then 1 else 0) + l.count true := by
        intro c l
        cases c with
        | true => simp [Nat.add_comm]
        | false => simp
      rw [hc, ih (k + 1)]
      by_cases hb : b = true
      · simp [hb, Nat.add_comm]
      · simp [hb]

/-- A controlled modular multiplication map is bijective whenever its multiplier is a unit. -/
theorem modMulGate_bijective {n : ℕ} {c : ZMod n} (hc : IsUnit c) (b : Bool) :
    Function.Bijective (modMulGate c b) := by
  have hunit : (↑hc.unit : ZMod n) * ↑(hc.unit⁻¹) = 1 := by
    rw [← Units.val_mul]
    exact Units.mul_inv _
  have hunit' : ↑(hc.unit⁻¹) * (↑hc.unit : ZMod n) = 1 := by
    rw [← Units.val_mul]
    exact Units.inv_mul _
  have hkey : Function.Bijective (modMulGate (↑hc.unit : ZMod n) b) := by
    constructor
    · intro x y hxy
      cases b with
      | true =>
          simp only [modMulGate, if_pos True.intro] at hxy
          calc x = ↑(hc.unit⁻¹) * ((↑hc.unit : ZMod n) * x) := by
                rw [← mul_assoc, hunit', one_mul]
            _ = ↑(hc.unit⁻¹) * ((↑hc.unit : ZMod n) * y) := by rw [hxy]
            _ = y := by rw [← mul_assoc, hunit', one_mul]
      | false =>
          simp only [modMulGate, if_neg (by simp : ¬ ((false : Bool) = true))] at hxy
          exact hxy
    · intro x
      cases b with
      | true =>
          refine ⟨↑(hc.unit⁻¹) * x, ?_⟩
          simp only [modMulGate, if_pos True.intro]
          rw [← mul_assoc, hunit, one_mul]
      | false =>
          refine ⟨x, ?_⟩
          simp only [modMulGate, if_neg (by simp : ¬ ((false : Bool) = true))]
  have hspec : (↑hc.unit : ZMod n) = c := IsUnit.unit_spec hc
  have hgate : modMulGate c b = modMulGate (↑hc.unit : ZMod n) b := by
    funext x
    simp only [modMulGate]
    rw [hspec]
  rw [hgate]
  exact hkey

/-- A modular word acts bijectively if every map in the word is bijective. -/
theorem applyModWord_bijective {n : ℕ} {w : List (ZMod n → ZMod n)} :
    (∀ g ∈ w, Function.Bijective g) → Function.Bijective (applyModWord w) := by
  intro h
  have key : ∀ (w : List (ZMod n → ZMod n)),
      (∀ g ∈ w, Function.Bijective g) →
      Function.Injective (applyModWord w) ∧ Function.Surjective (applyModWord w) := by
    intro w
    induction w with
    | nil =>
        intro _
        refine ⟨?_, ?_⟩
        · intro a b hab
          simpa [applyModWord] using! hab
        · intro x
          exact ⟨x, rfl⟩
    | cons g w ih =>
        intro hg
        obtain ⟨hinj, hsurj⟩ := ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg'))
        have hgbi : Function.Bijective g := hg g (List.mem_cons_self)
        constructor
        · intro x y hxy
          have h1 : applyModWord w (g x) = applyModWord w (g y) := by
            simpa [applyModWord, applyModWord_cons] using! hxy
          exact hgbi.injective (hinj h1)
        · intro x
          obtain ⟨z, hz⟩ := hsurj x
          obtain ⟨y, hy⟩ := hgbi.surjective z
          refine ⟨y, ?_⟩
          rw [applyModWord_cons, hy, hz]
  exact ⟨(key w h).1, (key w h).2⟩

/-- Each multiplier in the schedule is a repeated square `a ^ (2 ^ (k + j))` for some natural
`j`. -/
theorem modeExpSchedule_mem {n : ℕ} (a : ZMod n) :
    ∀ (bs : List Bool) (k : ℕ) (p : ZMod n × Bool), p ∈ modeExpSchedule a bs k →
      ∃ j : ℕ, p.1 = a ^ 2 ^ (k + j) := by
  intro bs k
  induction bs generalizing k with
  | nil =>
      intro p hp
      simp [modeExpSchedule] at hp
  | cons b bs ih =>
      intro p hp
      rw [modeExpSchedule] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨0, by simp⟩
      · obtain ⟨j, hj⟩ := ih (k + 1) p hp'
        refine ⟨j + 1, ?_⟩
        have h1 : k + (j + 1) = (k + 1) + j := by omega
        rw [h1, hj]

/-- Every map in the modular exponentiation word is a controlled multiplication by `a ^ (2 ^ k)`
for some `k` and Boolean control. -/
theorem modeExpWord_mem {n : ℕ} (a : ZMod n) (e : ℕ) {g : ZMod n → ZMod n}
    (hg : g ∈ modeExpWord a e) :
    ∃ k : ℕ, ∃ b : Bool, g = modMulGate (a ^ 2 ^ k) b := by
  rw [modeExpWord] at hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j, hj⟩ := modeExpSchedule_mem a (modExpBits e) 0 p hp
  exact ⟨j, p.2, by simp [hj]⟩

/-- The modular exponentiation word acts bijectively whenever its base is a unit. -/
theorem modeExpWord_bijective {n : ℕ} {a : ZMod n} (ha : IsUnit a) (e : ℕ) :
    Function.Bijective (applyModWord (modeExpWord a e)) := by
  refine applyModWord_bijective (fun g hg => ?_)
  obtain ⟨k, b, rfl⟩ := modeExpWord_mem a e hg
  exact modMulGate_bijective (ha.pow _) b

/-- For positive modulus `n`, evaluating the modular exponentiation word at one agrees with
`modExpResult n a e` in `ZMod n`. -/
theorem modeExpWord_realizes_modExpResult {n : ℕ} (hn : 0 < n) (a e : ℕ) :
    applyModWord (modeExpWord (a : ZMod n) e) 1 = (modExpResult n a e : ZMod n) := by
  rw [modeExpWord_semantics]
  rw [modExpResult_eq n a e hn]
  rw [one_mul, ZMod.natCast_mod, ← Nat.cast_pow]

/-- The modular exponentiation word satisfies its semantics, unit base bijectivity, bit length,
true control count, and numerical result specification. -/
theorem stageA_fourier_recovery_clause2_modexp : StageAFourierRecoveryClause2ModeExpEndpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n a e x
    exact modeExpWord_semantics (a : ZMod n) e x
  · intro n a e ha
    exact modeExpWord_bijective ha e
  · intro n a e
    exact modeExpWord_length (a : ZMod n) e
  · intro n a e
    exact modeExpSchedule_count (a : ZMod n) (modExpBits e) 0
  · intro n a e hn
    exact modeExpWord_realizes_modExpResult hn a e

end Qatlib.Concepts.HspRecovery.AbelianSampling
