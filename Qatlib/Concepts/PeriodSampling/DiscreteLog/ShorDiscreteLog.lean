/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.PeriodSampling.DiscreteLog.ShorDiscreteLogDefs
public import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.BernoulliTail
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling Qatlib.Concepts.MatrixAccess.RitzPipeline Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.CircuitImpl.ReflectionCompile Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling
open Qatlib.Concepts.PeriodSampling.DiscreteLog Qatlib.Concepts.MatrixAccess.RitzPipeline
open Qatlib.Concepts.PeriodSampling.DiscreteLog Qatlib.Concepts.MatrixAccess.RitzPipeline

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section

namespace Qatlib.Concepts.PeriodSampling.DiscreteLog

open Qatlib
open scoped Classical BigOperators

/-- Shows that distinct base primes of the modulus are coprime. -/
theorem dlogBasePrimes_pairwise_coprime (m : ℕ) :
    Set.Pairwise (dlogBasePrimes m) fun a b => Nat.Coprime a b := by
  intro a ha b hb hab
  have hpa : a.Prime := Nat.prime_of_mem_primeFactors ha
  have hpb : b.Prime := Nat.prime_of_mem_primeFactors hb
  exact (Nat.coprime_primes hpa hpb).2 hab

/-- Shows that each maximal prime power associated with a base prime divides the modulus. -/
theorem dlogMaxPrimePower_dvd (m ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) :
    dlogMaxPrimePower m ℓ ∣ m := by
  have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hne : m ≠ 0 := (Nat.mem_primeFactors.mp hℓ).2.2
  exact (Nat.Prime.pow_dvd_iff_le_factorization hprime hne).2 le_rfl

/-- Shows that the maximal prime power of a base prime is positive. -/
theorem dlogMaxPrimePower_pos (m ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) :
    0 < dlogMaxPrimePower m ℓ := by
  have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hne : m ≠ 0 := (Nat.mem_primeFactors.mp hℓ).2.2
  have hdiv : ℓ ∣ m := (Nat.mem_primeFactors.mp hℓ).2.1
  have hexp : 0 < m.factorization ℓ := by
    have hne' : m.factorization ℓ ≠ 0 := by
      intro hz
      have h1 : ¬ℓ.Prime ∨ ¬(ℓ ∣ m) ∨ m = 0 :=
        (Nat.factorization_eq_zero_iff m ℓ).mp hz
      rcases h1 with h1 | h1 | h1
      · exact absurd hprime h1
      · exact absurd hdiv h1
      · exact hne h1
    exact Nat.pos_of_ne_zero hne'
  rw [dlogMaxPrimePower]
  have htwo : (2 : ℕ) ≤ ℓ := hprime.two_le
  have hexp' : 0 ≤ m.factorization ℓ := hexp.le
  positivity

/-- Decomposes a nonzero modulus as the product of its maximal prime powers. -/
theorem dlogPrimePower_decomposition (m : ℕ) (hm : m ≠ 0) :
    ∏ ℓ ∈ dlogBasePrimes m, dlogMaxPrimePower m ℓ = m := by
  unfold dlogMaxPrimePower dlogBasePrimes
  calc
    ∏ ℓ ∈ m.primeFactors, ℓ ^ m.factorization ℓ
        = m.factorization.prod (fun a b => a ^ b) :=
      (Nat.prod_factorization_eq_prod_primeFactors _).symm
    _ = m.factorization.prod (· ^ ·) := rfl
    _ = m := Nat.prod_factorization_pow_eq_self hm

/-- Reduces sample congruences modulo the modulus to congruences modulo each maximal prime
power. -/
theorem dlogSampleCongruent_mod_prime_power (m : ℕ) (r : ℤ) {t : ℕ}
    (rec : DlogSampleRecord m t) (hcong : dlogSampleCongruent m r rec)
    (ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) (i : Fin t) :
    rec.dprime i + r * rec.cprime i ≡ 0 [ZMOD (dlogMaxPrimePower m ℓ : ℤ)] := by
  have hw : (dlogMaxPrimePower m ℓ : ℤ) ∣ (m : ℤ) :=
    Int.natCast_dvd.mpr (dlogMaxPrimePower_dvd m ℓ hℓ)
  exact (hcong i).of_dvd hw

/-- Shows that the true exponent residue belongs to each prime candidate set for congruent
samples. -/
theorem dlogPrimeCandidates_contains (m : ℕ) (r : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (hcong : dlogSampleCongruent m (r : ℤ) rec)
    (ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) :
    r % dlogMaxPrimePower m ℓ ∈ dlogPrimeCandidates m rec ℓ := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (dlogMaxPrimePower_pos m ℓ hℓ)), ?_⟩
  intro i
  have hmod : ((r % dlogMaxPrimePower m ℓ : ℕ) : ℤ) ≡ (r : ℤ)
      [ZMOD (dlogMaxPrimePower m ℓ : ℤ)] := by
    rw [Int.natCast_emod]
    exact Int.mod_modEq _ _
  have hmul : ((r % dlogMaxPrimePower m ℓ : ℕ) : ℤ) * rec.cprime i
      ≡ (r : ℤ) * rec.cprime i [ZMOD (dlogMaxPrimePower m ℓ : ℤ)] :=
    hmod.mul_right _
  have hadd : rec.dprime i + ((r % dlogMaxPrimePower m ℓ : ℕ) : ℤ) * rec.cprime i
      ≡ rec.dprime i + (r : ℤ) * rec.cprime i [ZMOD (dlogMaxPrimePower m ℓ : ℤ)] :=
    hmul.add_left _
  exact hadd.trans (dlogSampleCongruent_mod_prime_power m (r : ℤ) rec hcong ℓ hℓ i)

/-- Bounds a prime candidate set by one element when a sample multiplier is coprime to the
prime-power modulus. -/
theorem dlogPrimeCandidates_card_le_one_of_coprime (m : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) (i : Fin t)
    (hc : Nat.Coprime (dlogMaxPrimePower m ℓ) (rec.cprime i).natAbs) :
    (dlogPrimeCandidates m rec ℓ).card ≤ 1 := by
  have hcop : Nat.Coprime (dlogMaxPrimePower m ℓ) (rec.cprime i).natAbs := hc
  have hkey : ∀ ρ ρ' : ℕ, ρ ∈ dlogPrimeCandidates m rec ℓ →
      ρ' ∈ dlogPrimeCandidates m rec ℓ → ρ = ρ' := by
    intro ρ ρ' hρ hρ'
    have hρc := (Finset.mem_filter.mp hρ).2 i
    have hρ'c := (Finset.mem_filter.mp hρ').2 i
    have hsub : ((ρ : ℤ) - (ρ' : ℤ)) * rec.cprime i ≡ 0
        [ZMOD (dlogMaxPrimePower m ℓ : ℤ)] := by
      have h := hρc.sub hρ'c
      convert! h using 1; ring
    have hcancel : ((ρ : ℤ) - (ρ' : ℤ)) ≡ 0
        [ZMOD ((dlogMaxPrimePower m ℓ : ℤ) /
          ↑(Int.gcd (dlogMaxPrimePower m ℓ : ℤ) (rec.cprime i)))] := by
      refine Int.ModEq.cancel_right_div_gcd (m := (dlogMaxPrimePower m ℓ : ℤ))
        (a := (ρ : ℤ) - (ρ' : ℤ)) (b := 0) (c := rec.cprime i) (by
        exact_mod_cast dlogMaxPrimePower_pos m ℓ hℓ) ?_
      convert! hsub using 1; ring
    have hmod : ((ρ : ℤ) - (ρ' : ℤ)) ≡ 0
        [ZMOD (dlogMaxPrimePower m ℓ : ℤ)] := by
      have h1 : ((dlogMaxPrimePower m ℓ : ℤ).natAbs : ℕ) = dlogMaxPrimePower m ℓ := by
        have h2 : ((dlogMaxPrimePower m ℓ : ℤ).natAbs : ℤ)
            = (dlogMaxPrimePower m ℓ : ℤ) :=
          Int.natAbs_of_nonneg (by
            exact_mod_cast (Nat.zero_le (dlogMaxPrimePower m ℓ)))
        exact_mod_cast h2
      have hg : Int.gcd (dlogMaxPrimePower m ℓ : ℤ) (rec.cprime i) = 1 := by
        rw [Int.gcd_eq_natAbs, h1]
        exact Nat.coprime_iff_gcd_eq_one.mp hcop
      rw [hg] at hcancel
      simpa using! hcancel
    have hadd : (ρ : ℤ) ≡ (ρ' : ℤ) [ZMOD (dlogMaxPrimePower m ℓ : ℤ)] := by
      simpa only [sub_add_cancel, zero_add] using! hmod.add_right (ρ' : ℤ)
    rw [Int.natCast_modEq_iff] at hadd
    exact Nat.ModEq.eq_of_lt_of_lt hadd
      (Finset.mem_range.mp (Finset.mem_filter.mp hρ).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hρ').1)
  by_cases hne : (dlogPrimeCandidates m rec ℓ).Nonempty
  · obtain ⟨ρ₀, hρ₀⟩ := hne
    have hsub : (dlogPrimeCandidates m rec ℓ) ⊆ {ρ₀} := by
      intro ρ hρ
      have hρ' : ρ = ρ₀ := hkey ρ ρ₀ hρ hρ₀
      simp [hρ']
    calc
      (dlogPrimeCandidates m rec ℓ).card ≤ ({ρ₀} : Finset ℕ).card :=
        Finset.card_le_card hsub
      _ = 1 := by simp
  · have hz : (dlogPrimeCandidates m rec ℓ).card = 0 := by
      rw [Finset.card_eq_zero]
      simpa [Finset.not_nonempty_iff_eq_empty] using! hne
    omega

/-- Computes the full candidate count for a single zero multiplier with a divisible offset. -/
theorem dlogPrimeCandidates_card_of_zero_multiplier (m : ℕ)
    (rec : DlogSampleRecord m 1) (ℓ : ℕ)
    (hzero : rec.cprime 0 = 0)
    (hd : (dlogMaxPrimePower m ℓ : ℤ) ∣ rec.dprime 0) :
    (dlogPrimeCandidates m rec ℓ).card = dlogMaxPrimePower m ℓ := by
  have hsup : Finset.range (dlogMaxPrimePower m ℓ) ⊆
      dlogPrimeCandidates m rec ℓ := by
    intro ρ hρ
    apply Finset.mem_filter.mpr
    refine ⟨hρ, ?_⟩
    intro i
    have hi : (i : Fin 1) = 0 := Fin.eq_zero i
    subst hi
    have hzero' : rec.dprime 0 + (ρ : ℤ) * rec.cprime 0 = rec.dprime 0 := by
      rw [hzero]
      ring
    rw [hzero']
    exact Int.modEq_zero_iff_dvd.mpr hd
  have hsub : dlogPrimeCandidates m rec ℓ ⊆ Finset.range (dlogMaxPrimePower m ℓ) :=
    Finset.filter_subset _ _
  have h1 : (dlogPrimeCandidates m rec ℓ).card
      ≤ (Finset.range (dlogMaxPrimePower m ℓ)).card := Finset.card_le_card hsub
  have h2 : (Finset.range (dlogMaxPrimePower m ℓ)).card
      ≤ (dlogPrimeCandidates m rec ℓ).card := Finset.card_le_card hsup
  have heq : (dlogPrimeCandidates m rec ℓ).card
      = (Finset.range (dlogMaxPrimePower m ℓ)).card := le_antisymm h1 h2
  rwa [Finset.card_range] at heq

/-- Exhibits a small-prime candidate set with more than eighteen elements, refuting the stated
uniform bound. -/
theorem dlogPaperAtMost18False :
    ∃ (m : ℕ) (rec : DlogSampleRecord m 1) (ℓ : ℕ),
      ℓ ∈ dlogSmallBasePrimes m ∧
      (dlogPrimeCandidates m rec ℓ).card > 18 := by
  refine ⟨2 ^ 8, (⟨fun _ => 0, fun _ => 0⟩ : DlogSampleRecord (2 ^ 8) 1), 2, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, by norm_num⟩
    refine (Nat.mem_primeFactors).2 ⟨by norm_num, ?_, by norm_num⟩
    simp [Nat.pow_succ]
  · have hcard : (dlogPrimeCandidates (2 ^ 8)
        (⟨fun _ => 0, fun _ => 0⟩ : DlogSampleRecord (2 ^ 8) 1) 2).card
        = dlogMaxPrimePower (2 ^ 8) 2 := by
      refine dlogPrimeCandidates_card_of_zero_multiplier (2 ^ 8) _ 2 rfl ?_
      simp
    rw [hcard]
    have hfac : (2 ^ 8 : ℕ).factorization 2 = 8 :=
      Nat.factorization_pow_self (by norm_num)
    rw [dlogMaxPrimePower, hfac]
    norm_num

/-- Shows that the CRT merge lies below the nonzero modulus and has the chosen prime-power
residues. -/
theorem dlogCrtMerge_spec (m : ℕ) (hm : m ≠ 0) (choice : ℕ → ℕ) :
    dlogCrtMerge m choice < m ∧
      ∀ ℓ ∈ dlogBasePrimes m,
        Nat.ModEq (dlogMaxPrimePower m ℓ) (dlogCrtMerge m choice) (choice ℓ) := by
  have hne : ∀ ℓ ∈ dlogBasePrimes m, dlogMaxPrimePower m ℓ ≠ 0 := by
    intro ℓ hℓ
    have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
    have hne0 : m ≠ 0 := (Nat.mem_primeFactors.mp hℓ).2.2
    have h := dlogMaxPrimePower_dvd m ℓ hℓ
    rw [dlogMaxPrimePower] at h
    exact pow_ne_zero _ hprime.ne_zero
  have hpair : Set.Pairwise (dlogBasePrimes m)
      fun a b => Nat.Coprime (dlogMaxPrimePower m a) (dlogMaxPrimePower m b) := by
    intro a ha b hb hab
    have hpa : a.Prime := Nat.prime_of_mem_primeFactors ha
    have hpb : b.Prime := Nat.prime_of_mem_primeFactors hb
    have hcop : Nat.Coprime a b := (Nat.coprime_primes hpa hpb).2 hab
    exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _ hcop)
  refine ⟨?_, ?_⟩
  · have hlt := Nat.chineseRemainderOfFinset_lt_prod (t := dlogBasePrimes m) choice
      (fun ℓ => dlogMaxPrimePower m ℓ) hne hpair
    have hprod : ∏ ℓ ∈ dlogBasePrimes m, dlogMaxPrimePower m ℓ = m :=
      dlogPrimePower_decomposition m hm
    rw [hprod] at hlt
    exact hlt
  · intro ℓ hℓ
    exact (Nat.chineseRemainderOfFinset choice (fun ℓ => dlogMaxPrimePower m ℓ)
      (dlogBasePrimes m) hne hpair).prop ℓ hℓ

/-- Shows that the verified merged candidate set is the singleton containing the true discrete
logarithm. -/
theorem dlogMergedCandidates_singleton (p : ℕ) [NeZero p] (g x : ZMod p)
    (hg : orderOf g = p - 1) (r : ℕ) (hr : r < p - 1) (hx : x = g ^ r) {t : ℕ}
    (rec : DlogSampleRecord (p - 1) t)
    (hcong : dlogSampleCongruent (p - 1) (r : ℤ) rec) :
    dlogMergedCandidates p g x rec = {r} := by
  ext r'
  constructor
  · intro hr'mem
    have hver := (Finset.mem_filter.mp hr'mem).2.2
    have hr'lt : r' < p - 1 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr'mem).1
    have hxpow : g ^ r' = g ^ r := by
      rw [← hx]
      exact hver
    by_cases hle : r ≤ r'
    · have hmul : g ^ (r' + (p - 1 - r)) = 1 := by
        calc
          g ^ (r' + (p - 1 - r)) = g ^ r' * g ^ (p - 1 - r) := pow_add _ _ _
          _ = g ^ r * g ^ (p - 1 - r) := by rw [hxpow]
          _ = g ^ (r + (p - 1 - r)) := (pow_add _ _ _).symm
          _ = g ^ (p - 1) := by congr 1; omega
          _ = 1 := by rw [← hg, pow_orderOf_eq_one]
      have hdiv : p - 1 ∣ r' + (p - 1 - r) := by
        have h2 : orderOf g ∣ r' + (p - 1 - r) := orderOf_dvd_of_pow_eq_one hmul
        rwa [hg] at h2
      have hdiv' : p - 1 ∣ r' - r := by
        have h3 : p - 1 ∣ (r' + (p - 1 - r)) - (p - 1) :=
          Nat.dvd_sub hdiv (Nat.dvd_refl _)
        rwa [show r' + (p - 1 - r) - (p - 1) = r' - r by omega] at h3
      have hbound : r' - r < p - 1 := by omega
      have hz : r' - r = 0 := Nat.eq_zero_of_dvd_of_lt hdiv' hbound
      have hr'r : r' = r := by omega
      subst hr'r
      exact Finset.mem_singleton_self _
    · have hmul : g ^ (r + (p - 1 - r')) = 1 := by
        calc
          g ^ (r + (p - 1 - r')) = g ^ r * g ^ (p - 1 - r') := pow_add _ _ _
          _ = g ^ r' * g ^ (p - 1 - r') := by rw [hxpow]
          _ = g ^ (r' + (p - 1 - r')) := (pow_add _ _ _).symm
          _ = g ^ (p - 1) := by congr 1; omega
          _ = 1 := by rw [← hg, pow_orderOf_eq_one]
      have hdiv : p - 1 ∣ r + (p - 1 - r') := by
        have h2 : orderOf g ∣ r + (p - 1 - r') := orderOf_dvd_of_pow_eq_one hmul
        rwa [hg] at h2
      have hdiv' : p - 1 ∣ r - r' := by
        have h3 : p - 1 ∣ (r + (p - 1 - r')) - (p - 1) :=
          Nat.dvd_sub hdiv (Nat.dvd_refl _)
        rwa [show r + (p - 1 - r') - (p - 1) = r - r' by omega] at h3
      have hbound : r - r' < p - 1 := by omega
      have hz : r - r' = 0 := Nat.eq_zero_of_dvd_of_lt hdiv' hbound
      exact False.elim (absurd hz (by omega))
  · intro hr'
    simp only [Finset.mem_singleton] at hr'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    constructor
    · intro ℓ hℓ
      rw [hr']
      exact dlogPrimeCandidates_contains (p - 1) r rec hcong ℓ hℓ
    · rw [hr']
      exact hx.symm

/-- Shows that a CRT merge of valid local choices appears in the recursively enumerated
combinations. -/
theorem dlogCrtCombinations_contains (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (primes : List ℕ) :
    ∀ (choice : ℕ → ℕ), (∀ ℓ ∈ primes, choice ℓ ∈ dlogPrimeCandidates m rec ℓ) →
      dlogCrtMerge m choice ∈ dlogCrtCombinations m rec primes choice := by
  induction primes with
  | nil =>
      intro choice _
      simp [dlogCrtCombinations]
  | cons ℓ rest ih =>
      intro choice hcand
      have hmem : choice ℓ ∈ (dlogPrimeCandidates m rec ℓ).toList := by
        rw [Finset.mem_toList]
        exact hcand ℓ List.mem_cons_self
      have hsame : (fun l => if l = ℓ then choice ℓ else choice l) = choice := by
        funext l
        by_cases h : l = ℓ <;> simp [h]
      have hbranch : dlogCrtMerge m choice ∈
          (dlogPrimeCandidates m rec ℓ).toList.flatMap fun ρ =>
            dlogCrtCombinations m rec rest (fun l => if l = ℓ then ρ else choice l) := by
        rw [List.mem_flatMap]
        refine ⟨choice ℓ, hmem, ?_⟩
        have hmerge : dlogCrtMerge m choice
            = dlogCrtMerge m (fun l => if l = ℓ then choice ℓ else choice l) := by
          rw [hsame]
        rw [hmerge]
        refine ih (fun l => if l = ℓ then choice ℓ else choice l) ?_
        intro l hl
        by_cases h : l = ℓ <;> simp [h] <;> exact hcand _ (by simp [hl])
      rw [dlogCrtCombinations]
      exact hbranch

/-- Shows that the CRT merge of the true exponent residues appears in the candidate list
initialized with those residues. -/
theorem dlogCrtCandidateList_contains (m : ℕ) (r : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (hcong : dlogSampleCongruent m (r : ℤ) rec) :
    dlogCrtMerge m (fun ℓ => r % dlogMaxPrimePower m ℓ)
      ∈ dlogCrtCandidateList m rec (fun ℓ => r % dlogMaxPrimePower m ℓ) := by
  have hcand : ∀ ℓ ∈ dlogBasePrimeList m,
      (fun l' => r % dlogMaxPrimePower m l') ℓ ∈ dlogPrimeCandidates m rec ℓ := by
    intro ℓ hℓ
    have hmem : ℓ ∈ dlogBasePrimes m := (Finset.mem_sort (fun a b => a ≤ b)).mp hℓ
    exact dlogPrimeCandidates_contains m r rec hcong ℓ hmem
  exact dlogCrtCombinations_contains m rec (dlogBasePrimeList m)
    (fun ℓ => r % dlogMaxPrimePower m ℓ) hcand

/-- Shows that the product of maximal prime powers in the base prime list equals the nonzero
modulus. -/
theorem dlogBasePrimeList_maxPrimePower_prod (m : ℕ) (hm : m ≠ 0) :
    ((dlogBasePrimeList m).map (fun ℓ => dlogMaxPrimePower m ℓ)).prod = m := by
  have hperm : (dlogBasePrimes m).toList.Perm (dlogBasePrimeList m) := by
    have h := List.toFinset_toList (Finset.sort_nodup (dlogBasePrimes m) (fun a b => a ≤ b))
    rw [Finset.sort_toFinset] at h
    simpa [dlogBasePrimeList] using! h
  have h2 : ((List.map (fun ℓ => dlogMaxPrimePower m ℓ) (dlogBasePrimes m).toList)).prod
      = (dlogBasePrimes m).prod (fun ℓ => dlogMaxPrimePower m ℓ) :=
    Finset.prod_map_toList _ _
  have h3 : (dlogBasePrimes m).prod (fun ℓ => dlogMaxPrimePower m ℓ) = m :=
    dlogPrimePower_decomposition m hm
  calc
    ((dlogBasePrimeList m).map (fun ℓ => dlogMaxPrimePower m ℓ)).prod
        = ((List.map (fun ℓ => dlogMaxPrimePower m ℓ) (dlogBasePrimes m).toList)).prod :=
      ((hperm.map _).prod_eq).symm
    _ = (dlogBasePrimes m).prod (fun ℓ => dlogMaxPrimePower m ℓ) := h2
    _ = m := h3

/-- Shows that maximal prime powers in the base prime list are pairwise coprime. -/
theorem dlogBasePrimeList_pairwise (m : ℕ) :
    (dlogBasePrimeList m).Pairwise
      (Function.onFun Nat.Coprime (fun ℓ => dlogMaxPrimePower m ℓ)) := by
  have hset : Set.Pairwise {x | x ∈ dlogBasePrimeList m}
      (fun a b => Nat.Coprime (dlogMaxPrimePower m a) (dlogMaxPrimePower m b)) := by
    intro a ha b hb hab
    have ha' : a ∈ dlogBasePrimes m :=
      (Finset.mem_sort (fun a b => a ≤ b)).mp ha
    have hb' : b ∈ dlogBasePrimes m :=
      (Finset.mem_sort (fun a b => a ≤ b)).mp hb
    have hcop : Nat.Coprime a b := dlogBasePrimes_pairwise_coprime m ha' hb' hab
    exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _ hcop)
  exact List.Nodup.pairwise_of_forall_ne (Finset.sort_nodup _ _) hset

/-- Shows that two residues below a nonzero modulus are equal if they agree modulo every maximal
prime power. -/
theorem dlogCrtMerge_unique (m : ℕ) (hm : m ≠ 0) {x y : ℕ} (hx : x < m) (hy : y < m)
    (h : ∀ ℓ ∈ dlogBasePrimes m, Nat.ModEq (dlogMaxPrimePower m ℓ) x y) : x = y := by
  have hlist : x ≡ y [MOD ((dlogBasePrimeList m).map (fun ℓ => dlogMaxPrimePower m ℓ)).prod] :=
    (Nat.modEq_list_map_prod_iff (dlogBasePrimeList_pairwise m)).2
      (fun i hi => h i ((Finset.mem_sort (fun a b => a ≤ b)).mp hi))
  rw [dlogBasePrimeList_maxPrimePower_prod m hm] at hlist
  exact hlist.eq_of_lt_of_lt hx hy

/-- Describes the range and prime-power residue constraints satisfied by every enumerated CRT
combination. -/
theorem dlogCrtCombinations_elem (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (hm : m ≠ 0) :
    ∀ (primes : List ℕ) (seed : ℕ → ℕ), primes.Nodup →
      ∀ x ∈ dlogCrtCombinations m rec primes seed,
        x < m ∧
        (∀ ℓ ∈ dlogBasePrimes m, ℓ ∉ primes →
          Nat.ModEq (dlogMaxPrimePower m ℓ) x (seed ℓ)) ∧
        (∀ ℓ ∈ primes, ℓ ∈ dlogBasePrimes m →
          ∃ ρ ∈ dlogPrimeCandidates m rec ℓ,
            Nat.ModEq (dlogMaxPrimePower m ℓ) x ρ) := by
  intro primes
  induction primes with
  | nil =>
      intro seed _ x hx
      have hmerge : x = dlogCrtMerge m seed := by
        simpa [dlogCrtCombinations] using! hx
      obtain ⟨hlt, hmod⟩ := dlogCrtMerge_spec m hm seed
      refine ⟨?_, ?_, ?_⟩
      · rw [hmerge]
        exact hlt
      · intro ℓ hℓ hnot
        rw [hmerge]
        exact hmod ℓ hℓ
      · intro ℓ hℓ hmem
        exact absurd hℓ (by simp)
  | cons ℓ₀ rest ih =>
      intro seed hnodup x hx
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hnotmem : ℓ₀ ∉ rest := (List.nodup_cons.mp hnodup).1
      rw [dlogCrtCombinations] at hx
      rw [List.mem_flatMap] at hx
      obtain ⟨ρ, hρ, hx'⟩ := hx
      have hρ' : ρ ∈ dlogPrimeCandidates m rec ℓ₀ := (Finset.mem_toList).mp hρ
      obtain ⟨hlt, hout, hin⟩ :=
        ih (fun l => if l = ℓ₀ then ρ else seed l) hrest x hx'
      refine ⟨hlt, ?_, ?_⟩
      · intro ℓ hℓ hnot
        have hne : ℓ ≠ ℓ₀ := by
          intro h
          exact hnot (h ▸ List.mem_cons_self)
        have h1 := hout ℓ hℓ (by
          intro hr
          exact hnot (by simp [hr]))
        simpa [hne] using! h1
      · intro ℓ hprim hbase
        by_cases heq : ℓ = ℓ₀
        · have hbase₀ : ℓ₀ ∈ dlogBasePrimes m := heq ▸ hbase
          have h1 := hout ℓ₀ hbase₀ hnotmem
          rw [heq]
          exact ⟨ρ, hρ', by simpa using! h1⟩
        · have hlrest : ℓ ∈ rest := by
            have hmem' : ℓ ∈ ℓ₀ :: rest := hprim
            simp only [List.mem_cons] at hmem'
            exact hmem'.resolve_left (fun hh => heq hh)
          obtain ⟨ρl, hρl, hmod⟩ := hin ℓ hlrest hbase
          exact ⟨ρl, hρl, hmod⟩

/-- Computes the CRT combination list length as the product of local candidate counts. -/
theorem dlogCrtCombinations_length (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) :
    ∀ (primes : List ℕ) (seed : ℕ → ℕ),
      (dlogCrtCombinations m rec primes seed).length =
        ((primes.map fun ℓ => (dlogPrimeCandidates m rec ℓ).card)).prod := by
  intro primes
  induction primes with
  | nil =>
      intro seed
      simp [dlogCrtCombinations]
  | cons ℓ rest ih =>
      intro seed
      have hinner : ∀ ρ : ℕ, (dlogCrtCombinations m rec rest
          (fun l => if l = ℓ then ρ else seed l)).length =
          ((rest.map fun l' => (dlogPrimeCandidates m rec l').card)).prod :=
        fun ρ => ih (fun l => if l = ℓ then ρ else seed l)
      have hflat : (((dlogPrimeCandidates m rec ℓ).toList.flatMap fun ρ =>
          dlogCrtCombinations m rec rest (fun l => if l = ℓ then ρ else seed l)).length)
          = (dlogPrimeCandidates m rec ℓ).toList.length *
            ((rest.map fun l' => (dlogPrimeCandidates m rec l').card)).prod := by
        rw [List.length_flatMap]
        simp_rw [hinner]
        have hconst : ∀ (l : List ℕ) (K : ℕ), (l.map (fun _ => K)).sum = l.length * K := by
          intro l K
          induction l with
          | nil => simp
          | cons a l ih =>
              simp only [List.map_cons, List.sum_cons, List.length_cons]
              rw [ih]
              ring
        exact hconst _ _
      show (dlogCrtCombinations m rec (ℓ :: rest) seed).length = _
      rw [dlogCrtCombinations]
      rw [hflat]
      simp only [List.prod_cons, List.map_cons]
      rw [Finset.length_toList]

/-- Shows that every valid assignment of local candidates extending the seed is realized by an
enumerated CRT combination. -/
theorem dlogCrtCombinations_exists (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (hm : m ≠ 0) :
    ∀ (primes : List ℕ) (seed ch : ℕ → ℕ), primes.Nodup →
      (∀ ℓ ∈ primes, ℓ ∈ dlogBasePrimes m) →
      (∀ ℓ ∈ primes, ch ℓ ∈ dlogPrimeCandidates m rec ℓ) →
      (∀ ℓ ∈ dlogBasePrimes m, ℓ ∉ primes → ch ℓ = seed ℓ) →
      ∃ x ∈ dlogCrtCombinations m rec primes seed,
        ∀ ℓ ∈ dlogBasePrimes m, Nat.ModEq (dlogMaxPrimePower m ℓ) x (ch ℓ) := by
  intro primes
  induction primes with
  | nil =>
      intro seed ch _ _ _ h2
      refine ⟨dlogCrtMerge m seed, by simp [dlogCrtCombinations], ?_⟩
      intro ℓ hℓ
      have h := (dlogCrtMerge_spec m hm seed).2 ℓ hℓ
      rwa [← h2 ℓ hℓ (by simp)] at h
  | cons ℓ₀ rest ih =>
      intro seed ch hnodup hbase hch h2
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hnotmem : ℓ₀ ∉ rest := (List.nodup_cons.mp hnodup).1
      have hbase' : ∀ ℓ ∈ rest, ℓ ∈ dlogBasePrimes m := by
        intro ℓ hℓ
        exact hbase ℓ (List.mem_cons_of_mem (y := ℓ₀) hℓ)
      have hch' : ∀ ℓ ∈ rest, ch ℓ ∈ dlogPrimeCandidates m rec ℓ := by
        intro ℓ hℓ
        exact hch ℓ (List.mem_cons_of_mem (y := ℓ₀) hℓ)
      have h2' : ∀ ℓ ∈ dlogBasePrimes m, ℓ ∉ rest →
          ch ℓ = (fun l => if l = ℓ₀ then ch ℓ₀ else seed l) ℓ := by
        intro ℓ hℓ hnot
        by_cases heq : ℓ = ℓ₀
        · subst heq
          simp
        · have hne : ℓ ≠ ℓ₀ := heq
          have h1 := h2 ℓ hℓ (by
            intro hr
            simp only [List.mem_cons] at hr
            rcases hr with hEq | hr
            · exact heq hEq
            · exact hnot hr)
          have h3 : (fun l => if l = ℓ₀ then ch ℓ₀ else seed l) ℓ = seed ℓ := by
            simp [hne]
          rw [h3]
          exact h1
      obtain ⟨x, hx, hmod⟩ :=
        ih (fun l => if l = ℓ₀ then ch ℓ₀ else seed l) ch hrest hbase' hch' h2'
      refine ⟨x, ?_, hmod⟩
      rw [dlogCrtCombinations, List.mem_flatMap]
      refine ⟨ch ℓ₀, ?_, hx⟩
      rw [Finset.mem_toList]
      exact hch ℓ₀ (List.mem_cons_self)

/-- Converts disjointness for unequal indices in a duplicate-free list into pairwise
disjointness of the associated lists. -/
private theorem pairwise_disjoint_of_neq : ∀ (l : List ℕ) (f : ℕ → List ℕ), l.Nodup →
    (∀ ρ₁ ∈ l, ∀ ρ₂ ∈ l, ρ₁ ≠ ρ₂ → List.Disjoint (f ρ₁) (f ρ₂)) →
    List.Pairwise (Function.onFun List.Disjoint f) l := by
  intro l
  induction l with
  | nil =>
      intro f _ _
      simp
  | cons a l ih =>
      intro f hnodup h
      rw [List.pairwise_cons]
      constructor
      · intro b hb
        exact h a (List.mem_cons_self) b (List.mem_cons_of_mem a hb) (by
          intro hab
          subst hab
          exact (List.nodup_cons.mp hnodup).1 hb)
      · exact ih f (List.nodup_cons.mp hnodup).2 (fun ρ₁ hρ₁ ρ₂ hρ₂ hne =>
          h ρ₁ (List.mem_cons_of_mem a hρ₁) ρ₂ (List.mem_cons_of_mem a hρ₂) hne)

/-- Shows that CRT combinations contain no duplicates for a duplicate-free list of base primes. -/
theorem dlogCrtCombinations_nodup (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (hm : m ≠ 0) :
    ∀ (primes : List ℕ) (seed : ℕ → ℕ), primes.Nodup →
      (∀ ℓ ∈ primes, ℓ ∈ dlogBasePrimes m) →
      (dlogCrtCombinations m rec primes seed).Nodup := by
  intro primes
  induction primes with
  | nil =>
      intro seed _ _
      simp [dlogCrtCombinations]
  | cons ℓ₀ rest ih =>
      intro seed hnodup hbase
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hnotmem : ℓ₀ ∉ rest := (List.nodup_cons.mp hnodup).1
      have hbase₀ : ℓ₀ ∈ dlogBasePrimes m := hbase ℓ₀ (List.mem_cons_self)
      have hinner : ∀ ρ : ℕ,
          (dlogCrtCombinations m rec rest (fun l => if l = ℓ₀ then ρ else seed l)).Nodup :=
        fun ρ => ih (fun l => if l = ℓ₀ then ρ else seed l) hrest
          (fun l hl => hbase l (List.mem_cons_of_mem ℓ₀ hl))
      have hdisj : ∀ ρ₁ ∈ (dlogPrimeCandidates m rec ℓ₀).toList,
          ∀ ρ₂ ∈ (dlogPrimeCandidates m rec ℓ₀).toList, ρ₁ ≠ ρ₂ →
            List.Disjoint
              (dlogCrtCombinations m rec rest (fun l => if l = ℓ₀ then ρ₁ else seed l))
              (dlogCrtCombinations m rec rest (fun l => if l = ℓ₀ then ρ₂ else seed l)) := by
        intro ρ₁ hρ₁ ρ₂ hρ₂ hne
        have hρ₁' : ρ₁ ∈ dlogPrimeCandidates m rec ℓ₀ := (Finset.mem_toList).mp hρ₁
        have hρ₂' : ρ₂ ∈ dlogPrimeCandidates m rec ℓ₀ := (Finset.mem_toList).mp hρ₂
        have hlt₁ : ρ₁ < dlogMaxPrimePower m ℓ₀ :=
          Finset.mem_range.mp (Finset.mem_filter.mp hρ₁').1
        have hlt₂ : ρ₂ < dlogMaxPrimePower m ℓ₀ :=
          Finset.mem_range.mp (Finset.mem_filter.mp hρ₂').1
        intro a ha
        have h₁out : ∀ ℓ ∈ dlogBasePrimes m, ℓ ∉ rest →
            Nat.ModEq (dlogMaxPrimePower m ℓ) a
              ((fun l => if l = ℓ₀ then ρ₁ else seed l) ℓ) := by
          intro ℓ hℓ hnot
          exact (dlogCrtCombinations_elem m rec hm rest
            (fun l => if l = ℓ₀ then ρ₁ else seed l) hrest a ha).2.1 ℓ hℓ hnot
        intro h₂mem
        have h₂out : ∀ ℓ ∈ dlogBasePrimes m, ℓ ∉ rest →
            Nat.ModEq (dlogMaxPrimePower m ℓ) a
              ((fun l => if l = ℓ₀ then ρ₂ else seed l) ℓ) := by
          intro ℓ hℓ hnot
          exact (dlogCrtCombinations_elem m rec hm rest
            (fun l => if l = ℓ₀ then ρ₂ else seed l) hrest a h₂mem).2.1 ℓ hℓ hnot
        have hmod₁ : Nat.ModEq (dlogMaxPrimePower m ℓ₀) a ρ₁ := by
          have h := h₁out ℓ₀ hbase₀ hnotmem
          simpa using! h
        have hmod₂ : Nat.ModEq (dlogMaxPrimePower m ℓ₀) a ρ₂ := by
          have h := h₂out ℓ₀ hbase₀ hnotmem
          simpa using! h
        have hmod : Nat.ModEq (dlogMaxPrimePower m ℓ₀) ρ₁ ρ₂ := hmod₁.symm.trans hmod₂
        exact absurd (Nat.ModEq.eq_of_lt_of_lt hmod hlt₁ hlt₂) hne
      rw [dlogCrtCombinations, List.nodup_flatMap]
      refine ⟨fun ρ hρ => hinner ρ, ?_⟩
      exact pairwise_disjoint_of_neq _ _ (Finset.nodup_toList _)
        (fun ρ₁ hρ₁ ρ₂ hρ₂ hne => hdisj ρ₁ hρ₁ ρ₂ hρ₂ hne)

/-- Shows that the CRT merge of true exponent residues appears in the candidate list with the
zero seed. -/
theorem dlogCrtCandidateList_contains_seed (m : ℕ) (r : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (hm : m ≠ 0)
    (hcong : dlogSampleCongruent m (r : ℤ) rec) :
    dlogCrtMerge m (fun ℓ => r % dlogMaxPrimePower m ℓ)
      ∈ dlogCrtCandidateList m rec (fun _ => 0) := by
  obtain ⟨x, hx, hmod⟩ :=
    dlogCrtCombinations_exists m rec hm (dlogBasePrimeList m) (fun _ => 0)
      (fun ℓ => r % dlogMaxPrimePower m ℓ)
      (Finset.sort_nodup (dlogBasePrimes m) (fun a b => a ≤ b))
      (fun ℓ hℓ => (Finset.mem_sort (fun a b => a ≤ b)).mp hℓ)
      (fun ℓ hℓ => dlogPrimeCandidates_contains m r rec hcong ℓ
        ((Finset.mem_sort (fun a b => a ≤ b)).mp hℓ))
      (fun ℓ hℓ hnot =>
        (hnot ((Finset.mem_sort (fun a b => a ≤ b)).mpr hℓ)).elim)
  have hxl : x < m :=
    (dlogCrtCombinations_elem m rec hm (dlogBasePrimeList m) (fun _ => 0)
      (Finset.sort_nodup (dlogBasePrimes m) (fun a b => a ≤ b)) x hx).1
  have hmerge := (dlogCrtMerge_spec m hm (fun ℓ => r % dlogMaxPrimePower m ℓ))
  have hmod' : ∀ ℓ ∈ dlogBasePrimes m,
      Nat.ModEq (dlogMaxPrimePower m ℓ) x (dlogCrtMerge m (fun ℓ' => r % dlogMaxPrimePower m ℓ')) := by
    intro ℓ hℓ
    have h1 := hmod ℓ hℓ
    have h2 := hmerge.2 ℓ hℓ
    exact h1.trans h2.symm
  have heq : x = dlogCrtMerge m (fun ℓ => r % dlogMaxPrimePower m ℓ) :=
    dlogCrtMerge_unique m hm hxl hmerge.1 hmod'
  rw [heq] at hx
  exact hx

/-- Identifies the CRT candidate list length with the enumeration cost. -/
theorem dlogCrtCandidateList_length (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) :
    (dlogCrtCandidateList m rec (fun _ => 0)).length = dlogEnumerationCost m rec := by
  have h1 := dlogCrtCombinations_length m rec (dlogBasePrimeList m) (fun _ => 0)
  have hperm : (dlogBasePrimes m).toList.Perm (dlogBasePrimeList m) := by
    have h := List.toFinset_toList (Finset.sort_nodup (dlogBasePrimes m) (fun a b => a ≤ b))
    rw [Finset.sort_toFinset] at h
    simpa [dlogBasePrimeList] using! h
  have hperm' :
      (List.map (fun ℓ => (dlogPrimeCandidates m rec ℓ).card) (dlogBasePrimes m).toList).Perm
        (List.map (fun ℓ => (dlogPrimeCandidates m rec ℓ).card) (dlogBasePrimeList m)) :=
    hperm.map _
  have h2 : (dlogBasePrimes m).prod (fun ℓ => (dlogPrimeCandidates m rec ℓ).card)
      = ((List.map (fun ℓ => (dlogPrimeCandidates m rec ℓ).card) (dlogBasePrimes m).toList)).prod :=
    (Finset.prod_map_toList _ _).symm
  unfold dlogCrtCandidateList dlogEnumerationCost
  rw [h1]
  rw [← hperm'.prod_eq]
  exact h2.symm

/-- Shows that verification leaves exactly the true discrete logarithm in the candidate list. -/
theorem dlogVerifiedCandidates_eq_singleton (p : ℕ) [NeZero p] (g x : ZMod p)
    (hg : orderOf g = p - 1) (r : ℕ) (hr : r < p - 1) (hx : x = g ^ r) {t : ℕ}
    (rec : DlogSampleRecord (p - 1) t)
    (hcong : dlogSampleCongruent (p - 1) (r : ℤ) rec) :
    dlogVerifiedCandidates p g x rec = [r] := by
  have hhm : p - 1 ≠ 0 := by omega
  have hbase : ∀ ℓ ∈ dlogBasePrimes (p - 1), ℓ ∈ dlogBasePrimeList (p - 1) := by
    intro ℓ hℓ
    rw [dlogBasePrimeList]
    exact (Finset.mem_sort (fun a b => a ≤ b)).mpr hℓ
  have hnod : (dlogBasePrimeList (p - 1)).Nodup :=
    Finset.sort_nodup (dlogBasePrimes (p - 1)) (fun a b => a ≤ b)
  have hbase' : ∀ ℓ ∈ dlogBasePrimeList (p - 1), ℓ ∈ dlogBasePrimes (p - 1) := by
    intro ℓ hℓ
    exact (Finset.mem_sort (fun a b => a ≤ b)).mp hℓ
  have hmerge : dlogCrtMerge (p - 1) (fun ℓ => r % dlogMaxPrimePower (p - 1) ℓ) = r := by
    have hspec :=
      (dlogCrtMerge_spec (p - 1) hhm (fun ℓ => r % dlogMaxPrimePower (p - 1) ℓ))
    refine dlogCrtMerge_unique (p - 1) hhm hspec.1 hr ?_
    intro ℓ hℓ
    have h1 := hspec.2 ℓ hℓ
    have h2 : Nat.ModEq (dlogMaxPrimePower (p - 1) ℓ) (r % dlogMaxPrimePower (p - 1) ℓ) r :=
      Nat.mod_modEq r _
    exact h1.trans h2
  have hmemcand : r ∈ dlogCrtCandidateList (p - 1) rec (fun _ => 0) := by
    have h := dlogCrtCandidateList_contains_seed (p - 1) r rec hhm hcong
    rw [hmerge] at h
    exact h
  have hver : r ∈ dlogVerifiedCandidates p g x rec := by
    unfold dlogVerifiedCandidates
    rw [List.mem_filter]
    refine ⟨hmemcand, ?_⟩
    simp [hx.symm]
  have hall : ∀ y ∈ dlogVerifiedCandidates p g x rec, y = r := by
    intro y hy
    unfold dlogVerifiedCandidates at hy
    rw [List.mem_filter] at hy
    obtain ⟨hycand, hgy⟩ := hy
    have hgy' : g ^ y = x := by simpa using! hgy
    obtain ⟨hlt, hout, hin⟩ :=
      (dlogCrtCombinations_elem (p - 1) rec hhm (dlogBasePrimeList (p - 1)) (fun _ => 0)
        hnod y hycand)
    have hcongr : ∀ ℓ ∈ dlogBasePrimes (p - 1),
        y % dlogMaxPrimePower (p - 1) ℓ ∈ dlogPrimeCandidates (p - 1) rec ℓ := by
      intro ℓ hℓ
      obtain ⟨ρ, hρ, hmod⟩ := hin ℓ (hbase ℓ hℓ) hℓ
      have hρlt : ρ < dlogMaxPrimePower (p - 1) ℓ :=
        Finset.mem_range.mp (Finset.mem_filter.mp hρ).1
      have hmod' : y % dlogMaxPrimePower (p - 1) ℓ = ρ := by
        rw [hmod]
        exact Nat.mod_eq_of_lt hρlt
      rw [hmod']
      exact hρ
    have hmemmerged : y ∈ dlogMergedCandidates p g x rec := by
      rw [dlogMergedCandidates, Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr hlt, ⟨hcongr, hgy'⟩⟩
    have hsingle := dlogMergedCandidates_singleton p g x hg r hr hx rec hcong
    rw [hsingle] at hmemmerged
    simpa using! hmemmerged
  have hnodup : (dlogVerifiedCandidates p g x rec).Nodup := by
    have h := dlogCrtCombinations_nodup (p - 1) rec hhm (dlogBasePrimeList (p - 1))
      (fun _ => 0) hnod (fun ℓ hℓ => hbase' ℓ hℓ)
    unfold dlogVerifiedCandidates
    exact List.Nodup.filter _ h
  have hlen : (dlogVerifiedCandidates p g x rec).length = 1 := by
    have htoFinset : (dlogVerifiedCandidates p g x rec).toFinset = {r} := by
      ext y
      constructor
      · intro hy
        exact Finset.mem_singleton.mpr (hall y (List.mem_toFinset.mp hy))
      · intro hy
        simp only [Finset.mem_singleton] at hy
        subst hy
        exact List.mem_toFinset.mpr hver
    have h1 : (dlogVerifiedCandidates p g x rec).toFinset.card = 1 :=
      Finset.card_eq_one.mpr ⟨r, htoFinset⟩
    have h2 : (dlogVerifiedCandidates p g x rec).toFinset.card
        = (dlogVerifiedCandidates p g x rec).length :=
      List.toFinset_card_of_nodup hnodup
    omega
  obtain ⟨n, hn⟩ := List.get_of_mem hver
  have hn0 : (n : ℕ) = 0 := by
    have hln : (dlogVerifiedCandidates p g x rec).length = 1 := hlen
    simp at hn
    omega
  have hnfin : n = ⟨0, by omega⟩ := Fin.ext hn0
  refine List.ext_get (hlen.trans (by simp)) ?_
  intro k hk1 hk2
  have hk0 : k = 0 := by
    have hln : (dlogVerifiedCandidates p g x rec).length = 1 := hlen
    omega
  subst hk0
  rw [hnfin] at hn
  have hR : ([r] : List ℕ).get ⟨0, hk2⟩ = r := by simp
  rw [hR]
  exact hn

/-- Computes the gate count of a local program circuit as its list length and its query count as
zero. -/
theorem dlogLocalProgramCircuit_counts {n : ℕ} (gs : List (LocalQFTGate n)) :
    GateCount (localProgramCircuit gs) = gs.length ∧ QueryCount (localProgramCircuit gs) = 0 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp [ih]

/-- Computes the length of the local QFT gate list. -/
theorem dlogLocalQFT_length (n : ℕ) :
    (localQFT n).length = n + n * (n - 1) / 2 + n / 2 := by
  have h := localQFT_exact_gate_counts_and_wires n
  have hgc := (dlogLocalProgramCircuit_counts (localQFT n)).1
  rw [hgc] at h
  exact h.2.2.2.1

/-- Computes the readout program length and gate count, and shows that it makes no queries. -/
theorem dlogReadoutProgram_counts (n : ℕ) :
    (dlogReadoutProgram n).length = 2 * (n + n * (n - 1) / 2 + n / 2) ∧
      GateCount (localProgramCircuit (dlogReadoutProgram n))
        = 2 * (n + n * (n - 1) / 2 + n / 2) ∧
      QueryCount (localProgramCircuit (dlogReadoutProgram n)) = 0 := by
  have h1 : (dlogReadoutProgram n).length = 2 * (n + n * (n - 1) / 2 + n / 2) := by
    simp only [dlogReadoutProgram, List.length_append, List.length_map, dlogLocalQFT_length]
    ring
  have h2 := (dlogLocalProgramCircuit_counts (dlogReadoutProgram n))
  exact ⟨h1, by rw [h2.1, h1], h2.2⟩

/-- Shows that the readout width accommodates `q` under the stated encoding and modulus bounds. -/
theorem dlogReadoutWidth_sufficient (p x q : ℕ) (enc : DlogGroupEncoding p x q)
    (hq2p : q < 2 * p) : q ≤ 2 ^ (enc.pBits + 1) := by
  have h1 : q ≤ 2 * 2 ^ enc.pBits := by
    have hmul : 2 * p ≤ 2 * 2 ^ enc.pBits := by
      have hle := Nat.mul_le_mul_left 2 (le_of_lt enc.hp)
      omega
    exact hq2p.le.trans hmul
  have h2 : 2 * 2 ^ enc.pBits = 2 ^ (enc.pBits + 1) := by
    rw [Nat.pow_succ]
    ring
  omega

/-- Bounds the readout circuit gate count by a quadratic expression in its width. -/
theorem dlogReadoutGateCount_le (p x q : ℕ) (enc : DlogGroupEncoding p x q) :
    GateCount (localProgramCircuit (dlogReadoutProgram (enc.pBits + 1)))
      ≤ 2 * ((enc.pBits + 1) ^ 2 + (enc.pBits + 1)) := by
  have h1 (n : ℕ) : n + n * (n - 1) / 2 ≤ n * n := by
    calc n + n * (n - 1) / 2 ≤ n + n * (n - 1) :=
        Nat.add_le_add_left (Nat.div_le_self _ _) n
      _ = n * n := by
        cases n with
        | zero => rfl
        | succ m =>
            calc (m + 1) + (m + 1) * m = m * (m + 1) + (m + 1) := by ring
              _ = (m + 1) * (m + 1) := by rw [← Nat.succ_mul]
  have h2 (n : ℕ) : n + n * (n - 1) / 2 + n / 2 ≤ n * n + n := by
    calc n + n * (n - 1) / 2 + n / 2
        = (n + n * (n - 1) / 2) + n / 2 := rfl
      _ ≤ (n * n) + n / 2 := Nat.add_le_add_right (h1 n) (n / 2)
      _ ≤ (n * n) + n := Nat.add_le_add_left (Nat.div_le_self n 2) (n * n)
      _ = n * n + n := by ring
  rw [(dlogReadoutProgram_counts (enc.pBits + 1)).2.1]
  have h4 := h2 (enc.pBits + 1)
  calc 2 * ((enc.pBits + 1) + (enc.pBits + 1) * (enc.pBits + 1 - 1) / 2
        + (enc.pBits + 1) / 2)
      ≤ 2 * ((enc.pBits + 1) * (enc.pBits + 1) + (enc.pBits + 1)) := by
        exact Nat.mul_le_mul_left 2 h4
    _ = 2 * ((enc.pBits + 1) ^ 2 + (enc.pBits + 1)) := by ring

/-- Shows that a conditional marginal vanishes when its fiber contains no good outcomes. -/
theorem dlogConditionalMarginal_eq_zero {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (G : X → Prop) [DecidablePred G] (π : X → Y)
    (y : Y) (h : ∀ x, π x = y → ¬ G x) :
    dlogConditionalMarginal law G π y = 0 := by
  unfold dlogConditionalMarginal
  have hz : (∑ x, if π x = y ∧ G x then law.prob x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxy : π x = y
    · have hxg := h x hxy
      simp [hxg]
    · simp [hxy]
  rw [hz]
  simp

/-- Shows that the conditional law assigns zero probability outside the image of the
conditioning event. -/
theorem dlogConditionalLaw_eq_zero_of_not_image {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (G : X → Prop) [DecidablePred G] (π : X → Y)
    (hmass : 0 < dlogEventMass law G) (y : Y) (hy : ∀ x, G x → π x ≠ y) :
    (dlogConditionalLaw law G π hmass).prob y = 0 := by
  have hz : (∑ x, if π x = y ∧ G x then law.prob x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxy : π x = y
    · have hn : ¬G x := fun h => hy x h hxy
      simp [hn]
    · simp [hxy]
  show (∑ x, if π x = y ∧ G x then law.prob x else 0) / dlogEventMass law G = 0
  rw [hz]
  simp

/-- Expresses a one-sample event probability as the sum of its point probabilities. -/
theorem dlogProbEvent_one_eq {X : Type} [Fintype X] [DecidableEq X] (μ : FinDist X)
    (E : X → Prop) [DecidablePred E] :
    μ.probEvent (L := 1) (fun ω : Fin 1 → X => E (ω 0)) =
      ∑ x, if E x then μ.prob x else 0 := by
  classical
  have h := μ.expect_coord (L := 1) 0 (fun x => if E x then (1 : ℝ) else 0)
  simpa only [FinDist.probEvent, Finset.sum_filter, mul_ite, mul_one, mul_zero] using! h

/-- Expresses the probability that all independent samples satisfy an event as a power of its
single-sample mass. -/
theorem dlogProbEvent_all {X : Type} [Fintype X] [DecidableEq X] (μ : FinDist X)
    (E : X → Prop) [DecidablePred E] {t : ℕ} :
    μ.probEvent (L := t) (fun ω : Fin t → X => ∀ i, E (ω i)) =
      (∑ x, if E x then μ.prob x else 0) ^ t := by
  classical
  have h := μ.expect_prod (L := t) (fun _ x => if E x then (1 : ℝ) else 0)
  simpa only [Fintype.prod_ite_zero, Finset.prod_const_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_ite, mul_one, mul_zero,
    FinDist.probEvent, Finset.sum_filter] using! h

/-- Shows that pointwise probability domination implies domination of one-sample event
probabilities. -/
theorem dlogProbEvent_one_mono {X : Type} [Fintype X] [DecidableEq X]
    {μ ν : FinDist X} (hdom : ∀ x, μ.prob x ≤ ν.prob x) (E : X → Prop)
    [DecidablePred E] :
    μ.probEvent (L := 1) (fun ω : Fin 1 → X => E (ω 0)) ≤
      ν.probEvent (L := 1) (fun ω : Fin 1 → X => E (ω 0)) := by
  rw [dlogProbEvent_one_eq μ E, dlogProbEvent_one_eq ν E]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hE : E x
  · simp only [hE, ite_true]
    exact hdom x
  · simp only [hE, ite_false]
    exact le_rfl

/-- Shows that pointwise probability domination implies domination of all-samples event
probabilities. -/
theorem dlogProbEvent_all_mono {X : Type} [Fintype X] [DecidableEq X]
    {μ ν : FinDist X} (hdom : ∀ x, μ.prob x ≤ ν.prob x) {t : ℕ} (E : X → Prop)
    [DecidablePred E] :
    μ.probEvent (L := t) (fun ω : Fin t → X => ∀ i, E (ω i)) ≤
      ν.probEvent (L := t) (fun ω : Fin t → X => ∀ i, E (ω i)) := by
  rw [dlogProbEvent_all μ E, dlogProbEvent_all ν E]
  have hnonneg : 0 ≤ ∑ x, if E x then μ.prob x else 0 := by
    refine Finset.sum_nonneg fun x _ => ?_
    by_cases hE : E x
    · simp only [hE, ite_true]; exact μ.nonneg x
    · simp only [hE, ite_false]; exact le_rfl
  have hle : (∑ x, if E x then μ.prob x else 0) ≤ ∑ x, if E x then ν.prob x else 0 := by
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hE : E x
    · simp only [hE, ite_true]
      exact hdom x
    · simp only [hE, ite_false]
      exact le_rfl
  exact pow_le_pow_left₀ hnonneg hle t

/-- Derives uniform-good divisibility transport from pointwise transport. -/
theorem dlogUniformGoodDivisibilityTransport_of_pointwise {X : Type} [Fintype X]
    [DecidableEq X] {μ ν : FinDist X} (hdom : dlogUniformGoodPointwiseTransport μ ν)
    (E : X → Prop) [DecidablePred E] :
    dlogUniformGoodDivisibilityTransport μ ν E := by
  unfold dlogUniformGoodDivisibilityTransport
  have hμ : μ.expect (fun x => if E x then (1 : ℝ) else 0)
      = ∑ x, if E x then μ.prob x else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hE : E x
    · simp [hE]
    · simp [hE]
  have hν : ν.expect (fun x => if E x then (1 : ℝ) else 0)
      = ∑ x, if E x then ν.prob x else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hE : E x
    · simp [hE]
    · simp [hE]
  rw [hμ, hν]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hE : E x
  · simp only [hE, ite_true]
    exact hdom x
  · simp only [hE, ite_false]
    exact le_rfl

/-- Shows that the encoded group element is a unit modulo `p`. -/
theorem dlogEncoding_isUnit (p x q : ℕ) [NeZero p] (enc : DlogGroupEncoding p x q) :
    IsUnit (x : ZMod p) :=
  (ZMod.isUnit_iff_coprime x p).2 enc.hinvert

/-- Produces an inverse of the encoded group element with representative below `p`. -/
theorem dlogEncoding_inverse (p x q : ℕ) [NeZero p] (enc : DlogGroupEncoding p x q) :
    ∃ y : ZMod p, y.val < p ∧ (x : ZMod p) * y = 1 := by
  obtain ⟨u, hu⟩ := dlogEncoding_isUnit p x q enc
  have hinv : (u : (ZMod p)ˣ) * (u⁻¹ : (ZMod p)ˣ) = 1 := mul_inv_cancel _
  have h1 := congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hinv
  refine ⟨(u⁻¹ : (ZMod p)ˣ).val, ZMod.val_lt _, ?_⟩
  rw [← hu, ← Units.val_mul]
  simpa only [Units.val_one] using! h1

/-- Bounds the variance of an event indicator by its expectation. -/
private theorem dlog_indicator_variance_le {X : Type} [Fintype X] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] :
    law.variance (fun x => if E x then (1 : ℝ) else 0) ≤
      law.expect (fun x => if E x then (1 : ℝ) else 0) := by
  let f := fun x => if E x then (1 : ℝ) else 0
  let μ := law.expect f
  have hsq (x : X) : f x ^ 2 = f x := by dsimp [f]; split_ifs <;> norm_num
  have he (x : X) : law.prob x * (f x - μ)^2 =
      law.prob x * f x - 2*μ*(law.prob x * f x) + μ^2*law.prob x := by
    calc
      _ = law.prob x * f x^2 - 2*μ*(law.prob x*f x) + μ^2*law.prob x := by ring
      _ = _ := by rw [hsq]
  have hv : law.variance f = μ-μ^2 := by
    change (∑ x, law.prob x * (f x-μ)^2) = _
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, law.sum_one]
    change μ - 2*μ*μ + μ^2*1 = μ-μ^2
    ring
  change law.variance f ≤ μ
  rw [hv]
  nlinarith [sq_nonneg μ]

/-- Shows that the ratio of a positive variable to its squared distance above `c` decreases on
the stated domain. -/
private theorem dlog_ratio_mono {μ u c : ℝ} (hμu : u ≤ μ) (hc0 : 0 ≤ c) (hc : c < u) :
    μ / (μ - c) ^ 2 ≤ u / (u - c) ^ 2 := by
  have hden : 0 < (μ - c) ^ 2 := by
    have : c < μ := lt_of_lt_of_le hc hμu
    positivity
  have hden2 : 0 < (u - c) ^ 2 := by positivity
  have hmain : μ * (u - c) ^ 2 ≤ u * (μ - c) ^ 2 := by
    have hkey : μ * (u - c)^2 - u * (μ - c)^2 = (μ - u) * (c^2 - μ * u) := by ring
    have hc2 : c ^ 2 ≤ μ * u := by
      have h1 : c ^ 2 ≤ u ^ 2 := by
        have hnonneg : 0 ≤ (u - c) * (u + c) := by
          apply mul_nonneg
          · linarith
          · linarith
        nlinarith
      have h2 : u ^ 2 ≤ u * μ := by
        have hu : 0 ≤ u := by linarith
        simpa only [pow_two, mul_comm] using! mul_le_mul_of_nonneg_right hμu hu
      linarith
    have h3 : 0 ≤ μ - u := by linarith
    have h4 : 0 ≤ μ * u - c ^ 2 := by linarith
    have h5 : 0 ≤ (μ - u) * (μ * u - c ^ 2) := mul_nonneg h3 h4
    have hnonpos : (μ - u) * (c ^ 2 - μ * u) ≤ 0 := by linarith
    linarith [hkey]
  rw [div_le_div_iff₀ hden hden2]
  exact hmain

/-- Rewrites the gap between the baseline success rate and the required sample fraction. -/
private theorem dlog_budget_epsilon (t n : ℕ) :
    1 / 480 - (t : ℝ) / (480 * (t : ℝ) + 960 * ((n : ℝ) + 1))
      = 2 * ((n : ℝ) + 1) / (480 * (t : ℝ) + 960 * ((n : ℝ) + 1)) := by
  have h1 : (0 : ℝ) < 480 * (t : ℝ) + 960 * ((n : ℝ) + 1) := by positivity
  field_simp
  ring

/-- Simplifies the tail-bound expression for the discrete logarithm sampling budget. -/
private theorem dlog_budget_tail (t n : ℕ) :
    (1 / 480 : ℝ) / ((480 * (t : ℝ) + 960 * ((n : ℝ) + 1)) *
        (2 * ((n : ℝ) + 1) / (480 * (t : ℝ) + 960 * ((n : ℝ) + 1))) ^ 2)
      = (480 * (t : ℝ) + 960 * ((n : ℝ) + 1)) / (1920 * ((n : ℝ) + 1) ^ 2) := by
  have h1 : (0 : ℝ) < 480 * (t : ℝ) + 960 * ((n : ℝ) + 1) := by positivity
  have h2 : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  field_simp
  ring

/-- Bounds the sampling budget by a quadratic expression when `n` squared dominates `t`. -/
private theorem dlog_budget_bound (t n : ℕ) (hn : n ^ 2 ≥ t) :
    480 * (t : ℝ) + 960 * ((n : ℝ) + 1) ≤ 960 * ((n : ℝ) + 1) ^ 2 := by
  have htn2 : t ≤ n ^ 2 := hn
  have htR : (t : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h3 : (t : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast htn2
    have h4 : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by exact_mod_cast (Nat.cast_pow n 2)
    linarith
  nlinarith

/-- Shows that the target fraction is strictly below the baseline success rate. -/
private theorem dlog_budget_mean (t n : ℕ) (ht : 0 < t) :
    (t : ℝ) / (480 * (t : ℝ) + 960 * ((n : ℝ) + 1)) < 1 / 480 := by
  have hpos : (0 : ℝ) < 480 * (t : ℝ) + 960 * ((n : ℝ) + 1) := by positivity
  rw [div_lt_iff₀ hpos]
  have h1 : 480 * (t : ℝ) < 480 * (t : ℝ) + 960 * ((n : ℝ) + 1) := by
    have : (0 : ℝ) < 960 * ((n : ℝ) + 1) := by positivity
    linarith
  linarith

/-- Shows that the prescribed sampling budget yields at least `t` good samples with probability
at least one half. -/
theorem dlogGoodCountBudget {X : Type} [Fintype X] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E]
    (hmass : 1 / 480 ≤ law.expect (fun x => if E x then (1 : ℝ) else 0))
    (t n : ℕ) (ht : 0 < t) (hn : n ^ 2 ≥ t) :
    law.probEvent (L := 480 * t + 960 * (n + 1))
      (fun ω : Fin (480 * t + 960 * (n + 1)) → X =>
        (t : ℝ) ≤ ∑ j, if E (ω j) then (1 : ℝ) else 0) ≥ 1 / 2 := by
  classical
  let L : ℕ := 480 * t + 960 * (n + 1)
  have hL : 0 < L := by
    dsimp [L]
    have hpos : 0 < 960 * (n + 1) := by positivity
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hcast : (L : ℝ) = 480 * (t : ℝ) + 960 * ((n : ℝ) + 1) := by
    show ((480 * t + 960 * (n + 1) : ℕ) : ℝ) = _
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
    norm_num
  let f : X → ℝ := fun x => if E x then 1 else 0
  have hμ1 : (1 : ℝ) / 480 ≤ law.expect f := by simpa [f] using! hmass
  have hμ : 0 < law.expect f := lt_of_lt_of_le (by norm_num) hμ1
  have hc : (t : ℝ) / (L : ℝ) < 1 / 480 := by
    rw [hcast]
    exact dlog_budget_mean t n ht
  have hε : 0 < law.expect f - (t : ℝ) / (L : ℝ) := by linarith
  have hcheb := law.chebyshev_avg f hL (law.expect f - (t : ℝ) / (L : ℝ)) hε
  have hbad (ω : Fin L → X) (h : ¬((t : ℝ) ≤ ∑ j, f (ω j))) :
      law.expect f - (t : ℝ) / (L : ℝ) < |FinDist.avg f ω - law.expect f| := by
    have hsum : (∑ j, f (ω j)) < (t : ℝ) := lt_of_not_ge h
    have havg : FinDist.avg f ω < (t : ℝ) / (L : ℝ) := by
      have hstep : ((∑ j, f (ω j)) : ℝ) / (L : ℝ) < (t : ℝ) / (L : ℝ) := by
        have hmul : (t : ℝ) / (L : ℝ) * (L : ℝ) = (t : ℝ) := by
          field_simp
        rw [div_lt_iff₀ hLr, hmul]
        exact hsum
      simpa [FinDist.avg] using! hstep
    have hnonpos : FinDist.avg f ω - law.expect f ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  have hmono : law.probEvent (L := L) (fun ω : Fin L → X => ¬((t : ℝ) ≤ ∑ j, f (ω j)))
      ≤ law.probEvent (L := L) (fun ω : Fin L → X =>
          law.expect f - (t : ℝ) / (L : ℝ) < |FinDist.avg f ω - law.expect f|) := by
    simp only [FinDist.probEvent, Finset.sum_filter]
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases h : ¬((t : ℝ) ≤ ∑ j, f (ω j))
    · simp only [ite_eq_left h, ite_eq_left (hbad ω h)]
      exact le_rfl
    · rw [ite_eq_right h]
      split_ifs
      · exact Finset.prod_nonneg fun i _ => law.nonneg (ω i)
      · exact le_rfl
  have hvar : law.variance f ≤ law.expect f := by
    have h := dlog_indicator_variance_le law E
    simpa [f] using! h
  have hratio : law.expect f / (law.expect f - (t : ℝ) / (L : ℝ)) ^ 2
      ≤ (1 / 480) / (1 / 480 - (t : ℝ) / (L : ℝ)) ^ 2 :=
    dlog_ratio_mono hμ1 (by positivity) hc
  have hmul := mul_le_mul_of_nonneg_left hratio
    (by positivity : 0 ≤ (1 : ℝ) / (L : ℝ))
  have hstep : law.expect f / ((L : ℝ) * (law.expect f - (t : ℝ) / (L : ℝ)) ^ 2)
      ≤ (1 / 480) / ((L : ℝ) * (1 / 480 - (t : ℝ) / (L : ℝ)) ^ 2) := by
    have hl1 : (1 : ℝ) / (L : ℝ) *
        (law.expect f / (law.expect f - (t : ℝ) / (L : ℝ)) ^ 2)
        = law.expect f / ((L : ℝ) * (law.expect f - (t : ℝ) / (L : ℝ)) ^ 2) := by
      field_simp
    have hl2 : (1 : ℝ) / (L : ℝ) *
        ((1 / 480) / (1 / 480 - (t : ℝ) / (L : ℝ)) ^ 2)
        = (1 / 480) / ((L : ℝ) * (1 / 480 - (t : ℝ) / (L : ℝ)) ^ 2) := by
      field_simp
    rw [← hl1, ← hl2]
    exact hmul
  have hkey : 1 / 480 - (t : ℝ) / (L : ℝ) = 2 * ((n : ℝ) + 1) / (L : ℝ) := by
    rw [hcast]
    exact dlog_budget_epsilon t n
  have hfinal : (1 / 480) / ((L : ℝ) * (1 / 480 - (t : ℝ) / (L : ℝ)) ^ 2) ≤ 1 / 2 := by
    rw [hkey, hcast, dlog_budget_tail t n]
    have hpos2 : (0 : ℝ) < 1920 * ((n : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hpos2]
    have hid : (1 / 2 : ℝ) * (1920 * ((n : ℝ) + 1) ^ 2) = 960 * ((n : ℝ) + 1) ^ 2 := by ring
    rw [hid]
    exact dlog_budget_bound t n hn
  have hchain : law.probEvent (L := L) (fun ω : Fin L → X => ¬((t : ℝ) ≤ ∑ j, f (ω j)))
      ≤ 1 / 2 := by
    have h1 := hmono.trans hcheb
    have h1' : law.variance f / ((L : ℝ) * (law.expect f - (t : ℝ) / (L : ℝ)) ^ 2)
        ≤ law.expect f / ((L : ℝ) * (law.expect f - (t : ℝ) / (L : ℝ)) ^ 2) := by
      exact div_le_div_of_nonneg_right hvar
        (mul_nonneg (le_of_lt hLr) (sq_nonneg _))
    exact h1.trans (h1'.trans (hstep.trans hfinal))
  have hcompl := probEvent_compl law (fun ω : Fin L → X => (t : ℝ) ≤ ∑ j, f (ω j))
  have hgoal : law.probEvent (L := L) (fun ω : Fin L → X => (t : ℝ) ≤ ∑ j, f (ω j))
      ≥ 1 / 2 := by
    linarith [hcompl, hchain]
  exact hgoal

/-- Expresses a conditional point probability as its joint event mass divided by the
conditioning mass. -/
theorem dlogConditionalLaw_prob_eq_joint {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (G : X → Prop) [DecidablePred G] (π : X → Y)
    (hmass : 0 < dlogEventMass law G) (y : Y) :
    (dlogConditionalLaw law G π hmass).prob y
      = (∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x)
        / dlogEventMass law G := by
  show (∑ x, if π x = y ∧ G x then law.prob x else 0) / dlogEventMass law G
      = (∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x)
        / dlogEventMass law G
  rw [Finset.sum_filter]

/-- Bounds a joint event mass by the corresponding conditional point probability. -/
theorem dlogConditionalLaw_prob_ge_joint {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (G : X → Prop) [DecidablePred G] (π : X → Y)
    (hmass : 0 < dlogEventMass law G) (y : Y) :
    (∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x)
      ≤ (dlogConditionalLaw law G π hmass).prob y := by
  rw [dlogConditionalLaw_prob_eq_joint law G π hmass y]
  have hle : dlogEventMass law G ≤ 1 := by
    unfold dlogEventMass
    have hle' : (∑ x, if G x then law.prob x else 0) ≤ ∑ x, law.prob x := by
      refine Finset.sum_le_sum fun x _ => ?_
      by_cases hG : G x
      · simp only [hG, ite_true]; exact le_rfl
      · simp only [hG, ite_false]; exact law.nonneg x
    rw [← law.sum_one]
    exact hle'
  have hnonneg : 0 ≤ ∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x := by
    refine Finset.sum_nonneg fun x _ => ?_
    exact law.nonneg x
  rw [le_div_iff₀ hmass]
  have hprod : (∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x)
      * dlogEventMass law G
      ≤ ∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x := by
    calc
      (∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x)
          * dlogEventMass law G
          ≤ (∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x) * 1 :=
            mul_le_mul_of_nonneg_left hle hnonneg
      _ = ∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x := by ring
  linarith

/-- Bounds the mass of any finite subset of a good fiber by the corresponding conditional point
probability. -/
theorem dlogConditionalLaw_prob_ge_finset {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (G : X → Prop) [DecidablePred G] (π : X → Y)
    (hmass : 0 < dlogEventMass law G) (y : Y) (S : Finset X)
    (hS : ∀ x ∈ S, π x = y ∧ G x) :
    (∑ x ∈ S, law.prob x) ≤ (dlogConditionalLaw law G π hmass).prob y := by
  have hnum : (dlogConditionalLaw law G π hmass).prob y
      = (∑ x ∈ (Finset.univ.filter (fun x => π x = y ∧ G x)), law.prob x)
        / dlogEventMass law G := by
    show (∑ x, if π x = y ∧ G x then law.prob x else 0) / dlogEventMass law G = _
    rw [Finset.sum_filter]
  rw [hnum]
  have hS' : S ⊆ Finset.univ.filter (fun x => π x = y ∧ G x) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS x hx⟩
  have hle : (∑ x ∈ S, law.prob x)
      ≤ ∑ x ∈ Finset.univ.filter (fun x => π x = y ∧ G x), law.prob x :=
    Finset.sum_le_sum_of_subset_of_nonneg hS' (fun x _ _ => law.nonneg x)
  have hle1 : dlogEventMass law G ≤ 1 := by
    unfold dlogEventMass
    have hle' : (∑ x, if G x then law.prob x else 0) ≤ ∑ x, law.prob x := by
      refine Finset.sum_le_sum fun x _ => ?_
      by_cases hG : G x
      · simp only [hG, ite_true]; exact le_rfl
      · simp only [hG, ite_false]; exact law.nonneg x
    rw [← law.sum_one]
    exact hle'
  have hnonneg : 0 ≤ ∑ x ∈ S, law.prob x := by
    refine Finset.sum_nonneg fun x _ => ?_
    exact law.nonneg x
  rw [le_div_iff₀ hmass]
  calc
    (∑ x ∈ S, law.prob x) * dlogEventMass law G
        ≤ (∑ x ∈ S, law.prob x) * 1 := mul_le_mul_of_nonneg_left hle1 hnonneg
    _ = ∑ x ∈ S, law.prob x := by ring
  linarith [hle]

/-- Bounds a finite set's probability mass below by its cardinality times a uniform pointwise
lower bound. -/
theorem dlogMass_ge_card_mul {X : Type} [Fintype X] (law : FinDist X)
    (S : Finset X) (m : ℝ) (hpoint : ∀ x ∈ S, m ≤ law.prob x) :
    (S.card : ℝ) * m ≤ ∑ x ∈ S, law.prob x := by
  have hle : (∑ x ∈ S, m) ≤ ∑ x ∈ S, law.prob x :=
    Finset.sum_le_sum fun x hx => hpoint x hx
  have heq : (∑ x ∈ S, m) = (S.card : ℝ) * m := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [heq] at hle
  exact hle

/-- Bounds the conditional mass of good outcomes avoiding a bad event using cardinality and
pointwise probability bounds. -/
theorem dlogAvoidMass_lower {X : Type} [Fintype X] (law : FinDist X) (G : X → Prop)
    [DecidablePred G] (B : X → Prop) [DecidablePred B] (N k m : ℝ)
    (hm : 0 ≤ m) (hmass : 0 < dlogEventMass law G)
    (hN : N ≤ (dlogGoodIndexCard G : ℝ))
    (hk : ((Finset.univ.filter (fun x => G x ∧ B x)).card : ℝ) ≤ k)
    (hpoint : ∀ x, G x → ¬ B x → m ≤ law.prob x) :
    (N - k) * m ≤ (∑ x ∈ (Finset.univ.filter (fun x => G x ∧ ¬ B x)), law.prob x)
        / dlogEventMass law G := by
  classical
  set S : Finset X := Finset.univ.filter (fun x => G x ∧ ¬ B x) with hSdef
  set T : Finset X := Finset.univ.filter (fun x => G x ∧ B x) with hTdef
  have hcard : (S.card : ℝ) + (T.card : ℝ) = (dlogGoodIndexCard G : ℝ) := by
    have hunion : S ∪ T = Finset.univ.filter G := by
      ext x
      constructor
      · intro h
        simp only [Finset.mem_union] at h
        rcases h with hS | hT
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2.1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT).2.1⟩
      · intro h
        have hG := Finset.mem_filter.mp h
        rw [Finset.mem_union]
        by_cases hB : B x
        · refine Or.inr ?_
          rw [hTdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG.2, hB⟩
        · refine Or.inl ?_
          rw [hSdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG.2, hB⟩
    have hinter : S ∩ T = (∅ : Finset X) := by
      ext x
      simp only [hSdef, hTdef, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact (h.1.2 h.2.2).elim
      · intro h
        simp at h
    have h := Finset.card_union_add_card_inter S T
    rw [hunion, hinter] at h
    have hn : dlogGoodIndexCard G = S.card + T.card := by
      simpa [dlogGoodIndexCard] using! h
    exact_mod_cast hn.symm
  have hS : N - k ≤ (S.card : ℝ) := by linarith [hN, hk, hcard]
  have hmassS : (N - k) * m ≤ ∑ x ∈ S, law.prob x := by
    have h1 : (S.card : ℝ) * m ≤ ∑ x ∈ S, law.prob x := by
      refine dlogMass_ge_card_mul law S m (fun x hx => ?_)
      have hx' := Finset.mem_filter.mp hx
      exact hpoint x hx'.2.1 hx'.2.2
    nlinarith [hm]
  have hle1 : dlogEventMass law G ≤ 1 := by
    unfold dlogEventMass
    have hle : (∑ x, if G x then law.prob x else 0) ≤ ∑ x, law.prob x := by
      refine Finset.sum_le_sum fun x _ => ?_
      by_cases hG : G x
      · simp only [hG, ite_true]; exact le_rfl
      · simp only [hG, ite_false]; exact law.nonneg x
    rw [← law.sum_one]
    exact hle
  have hnonneg : 0 ≤ ∑ x ∈ S, law.prob x := by
    refine Finset.sum_nonneg fun x _ => ?_
    exact law.nonneg x
  have hdiv : ∑ x ∈ S, law.prob x
      ≤ (∑ x ∈ S, law.prob x) / dlogEventMass law G := by
    rw [le_div_iff₀ hmass]
    have hnonneg' : 0 ≤ ∑ x ∈ S, law.prob x := hnonneg
    calc
      (∑ x ∈ S, law.prob x) * dlogEventMass law G
          ≤ (∑ x ∈ S, law.prob x) * 1 :=
            mul_le_mul_of_nonneg_left hle1 hnonneg'
      _ = ∑ x ∈ S, law.prob x := by ring
  linarith [hmassS, hdiv, hle1]

/-- Bounds the probability that all samples satisfy an event below by a power of a lower bound
on its mass. -/
theorem dlogProbEvent_all_ge {X : Type} [Fintype X] [DecidableEq X] (μ : FinDist X)
    (E : X → Prop) [DecidablePred E] {t : ℕ} (p : ℝ) (hp : 0 ≤ p)
    (h : p ≤ ∑ x, if E x then μ.prob x else 0) :
    p ^ t ≤ μ.probEvent (L := t) (fun ω : Fin t → X => ∀ i, E (ω i)) := by
  rw [dlogProbEvent_all μ E]
  have hnonneg : 0 ≤ ∑ x, if E x then μ.prob x else 0 := by
    refine Finset.sum_nonneg fun x _ => ?_
    by_cases hE : E x
    · simp only [hE, ite_true]; exact μ.nonneg x
    · simp only [hE, ite_false]; exact le_rfl
  exact pow_le_pow_left₀ hp h t

/-- Bounds the probability that some indexed event holds for all samples by the number of
indices times the single-event power bound. -/
theorem dlogUnionBound_pinned {X : Type} [Fintype X] [DecidableEq X] (μ : FinDist X)
    (W : Finset ℕ) (E : ℕ → X → Prop) [Einst : ∀ n, DecidablePred (E n)] {t : ℕ}
    (δ : ℝ)
    (hpin : ∀ w ∈ W, (∑ x, if E w x then μ.prob x else 0) ≤ 1 - δ)
    [DecidablePred (fun ω : Fin t → X => ∃ w ∈ W, ∀ i, E w (ω i))] :
    μ.probEvent (L := t) (fun ω : Fin t → X => ∃ w ∈ W, ∀ i, E w (ω i))
      ≤ (W.card : ℝ) * (1 - δ) ^ t := by
  classical
  have hprobOf_nonneg : ∀ ω : Fin t → X, 0 ≤ μ.probOf ω := by
    intro ω
    exact Finset.prod_nonneg fun i _ => μ.nonneg (ω i)
  have hmain : μ.probEvent (L := t) (fun ω : Fin t → X => ∃ w ∈ W, ∀ i, E w (ω i))
      ≤ ∑ w ∈ W, μ.probEvent (L := t) (fun ω : Fin t → X => ∀ i, E w (ω i)) := by
    unfold FinDist.probEvent
    have hinner (w : ℕ) :
        (∑ ψ ∈ (Finset.univ : Finset (Fin t → X)).filter
            (fun ψ => ∀ i, E w (ψ i)), μ.probOf ψ)
        = ∑ ψ : Fin t → X, if ∀ i, E w (ψ i) then μ.probOf ψ else 0 := by
      rw [Finset.sum_filter]
    rw [Finset.sum_filter]
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases he : ∃ w ∈ W, ∀ i, E w (ω i)
    · rw [ite_eq_left he]
      obtain ⟨w, hw, hew⟩ := he
      calc
        μ.probOf ω = (if ∀ i, E w (ω i) then μ.probOf ω else 0) := by rw [ite_eq_left hew]
        _ ≤ ∑ w' ∈ W, if ∀ i, E w' (ω i) then μ.probOf ω else 0 :=
          Finset.single_le_sum
            (s := W) (a := w)
            (f := fun w' => if ∀ i, E w' (ω i) then μ.probOf ω else 0)
            (fun w' _ => by
              by_cases hc : ∀ i, E w' (ω i)
              · simp [hc]
                exact hprobOf_nonneg ω
              · simp [hc])
            hw
    · rw [ite_eq_right he]
      exact Finset.sum_nonneg fun w _ => by
        split_ifs
        · exact hprobOf_nonneg ω
        · exact le_rfl
  calc
    μ.probEvent (L := t) (fun ω : Fin t → X => ∃ w ∈ W, ∀ i, E w (ω i))
      ≤ ∑ w ∈ W, μ.probEvent (L := t) (fun ω : Fin t → X => ∀ i, E w (ω i)) := hmain
    _ = ∑ w ∈ W, (∑ x, if E w x then μ.prob x else 0) ^ t := by
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [dlogProbEvent_all μ (E w)]
    _ ≤ ∑ w ∈ W, (1 - δ) ^ t := by
      refine Finset.sum_le_sum fun w hw => ?_
      have hnonneg : 0 ≤ ∑ x, if E w x then μ.prob x else 0 := by
        refine Finset.sum_nonneg fun x _ => ?_
        by_cases hE : E w x
        · simp only [hE, ite_true]; exact μ.nonneg x
        · simp only [hE, ite_false]; exact le_rfl
      exact pow_le_pow_left₀ hnonneg (hpin w hw) t
    _ = (W.card : ℝ) * (1 - δ) ^ t := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Shows that the escape probability is strictly less than one under the stated modulus bounds. -/
theorem dlogEscapeProbability_lt_one (p q w : ℕ) (hp : 1 ≤ p) (hq : 0 < q)
    (hpq : p < q) :
    dlogEscapeProbability p q w < 1 := by
  have hnonneg : (0 : ℝ) ≤ (p - 1 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hden : (0 : ℝ) < 20 * (q : ℝ)^2 := by positivity
  have hfac : (0 : ℝ) ≤ (p - 1 : ℝ) / (20 * (q : ℝ)^2) :=
    div_nonneg hnonneg (le_of_lt hden)
  have hbr : ((q / 12 : ℕ) : ℝ) - (((p - 1) / w + 1 : ℕ) : ℝ)
      ≤ ((q / 12 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (((p - 1) / w + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hq12 : ((q / 12 : ℕ) : ℝ) ≤ (q : ℝ) := by
    have : (q / 12 : ℕ) ≤ q := by omega
    exact_mod_cast this
  have hfac' : (p - 1 : ℝ) / (20 * (q : ℝ)^2) ≤ 1 / (20 * (q : ℝ)) := by
    apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 20 * (q : ℝ))).mpr
    calc
      (p - 1 : ℝ) * (20 * (q : ℝ)) ≤ (q : ℝ) * (20 * (q : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (by
            have hlt : (p - 1 : ℕ) ≤ q := by omega
            exact_mod_cast hlt)
          (by positivity)
      _ = 1 * (20 * (q : ℝ)^2) := by ring
  unfold dlogEscapeProbability
  calc
    (((q / 12 : ℕ) : ℝ) - (((p - 1) / w + 1 : ℕ) : ℝ)) *
        ((p - 1 : ℝ) / (20 * (q : ℝ)^2))
      ≤ ((q / 12 : ℕ) : ℝ) * (1 / (20 * (q : ℝ))) := by
        have h1 : (((q / 12 : ℕ) : ℝ) - (((p - 1) / w + 1 : ℕ) : ℝ)) *
              ((p - 1 : ℝ) / (20 * (q : ℝ)^2))
            ≤ ((q / 12 : ℕ) : ℝ) *
              ((p - 1 : ℝ) / (20 * (q : ℝ)^2)) :=
          mul_le_mul_of_nonneg_right hbr hfac
        have h2 : ((q / 12 : ℕ) : ℝ) *
              ((p - 1 : ℝ) / (20 * (q : ℝ)^2))
            ≤ ((q / 12 : ℕ) : ℝ) * (1 / (20 * (q : ℝ))) :=
          mul_le_mul_of_nonneg_left hfac' (Nat.cast_nonneg _)
        linarith
    _ ≤ (q : ℝ) * (1 / (20 * (q : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hq12 (by positivity)
    _ = 1 / 20 := by field_simp
    _ < 1 := by norm_num

/-- Shows that a base prime's maximal prime power is at least two. -/
theorem dlogMaxPrimePower_ge_two (m ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) :
    2 ≤ dlogMaxPrimePower m ℓ := by
  have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hne : m ≠ 0 := (Nat.mem_primeFactors.mp hℓ).2.2
  have hpos := dlogMaxPrimePower_pos m ℓ hℓ
  have hexp : 1 ≤ m.factorization ℓ := by
    have h1 : m.factorization ℓ ≠ 0 := by
      intro hz
      have h2 : ¬ℓ.Prime ∨ ¬(ℓ ∣ m) ∨ m = 0 :=
        (Nat.factorization_eq_zero_iff m ℓ).mp hz
      rcases h2 with h2 | h2 | h2
      · exact absurd hprime h2
      · exact absurd ((Nat.mem_primeFactors.mp hℓ).2.1) h2
      · exact hne h2
    omega
  have hdvd : ℓ ∣ dlogMaxPrimePower m ℓ := dvd_pow_self ℓ (by omega)
  have hpow : ℓ ≤ dlogMaxPrimePower m ℓ := Nat.le_of_dvd hpos hdvd
  have htwo : (2 : ℕ) ≤ ℓ := hprime.two_le
  omega

/-- Bounds two raised to the number of base primes by the nonzero modulus. -/
theorem dlogBasePrimes_two_pow_card_le (m : ℕ) (hm : m ≠ 0) :
    2 ^ (dlogBasePrimes m).card ≤ m := by
  have hprod := dlogPrimePower_decomposition m hm
  have hge : ∀ ℓ ∈ dlogBasePrimes m, 2 ≤ dlogMaxPrimePower m ℓ := by
    intro ℓ hℓ
    exact dlogMaxPrimePower_ge_two m ℓ hℓ
  calc
    2 ^ (dlogBasePrimes m).card = ∏ _x ∈ dlogBasePrimes m, (2 : ℕ) :=
      (Finset.prod_const 2).symm
    _ ≤ ∏ ℓ ∈ dlogBasePrimes m, dlogMaxPrimePower m ℓ :=
      Finset.prod_le_prod fun ℓ hℓ => hge ℓ hℓ
    _ = m := hprod

/-- Bounds the number of base primes by the binary logarithm of the modulus. -/
theorem dlogBasePrimes_card_le_log2 (m : ℕ) (hm : 2 ≤ m) :
    (dlogBasePrimes m).card ≤ Nat.log2 m := by
  have h := dlogBasePrimes_two_pow_card_le m (by omega : m ≠ 0)
  rw [Nat.log2_eq_log_two]
  exact (Nat.le_log_iff_pow_le Nat.one_lt_two (by omega : m ≠ 0)).mpr h

/-- Bounds the number of large base primes by the binary logarithm of the modulus. -/
theorem dlogLargeBasePrimes_card_le_log2 (m : ℕ) (hm : 2 ≤ m) :
    (dlogLargeBasePrimes m).card ≤ Nat.log2 m := by
  have hsub : dlogLargeBasePrimes m ⊆ dlogBasePrimes m :=
    Finset.filter_subset _ _
  calc
    (dlogLargeBasePrimes m).card ≤ (dlogBasePrimes m).card := Finset.card_le_card hsub
    _ ≤ Nat.log2 m := dlogBasePrimes_card_le_log2 m hm

/-- Shows that natural-number division decreases when a positive divisor increases. -/
theorem dlogDiv_le_div_of_le {a b c : ℕ} (h : c ≤ b) (hc : 0 < c) (hb : 0 < b) :
    a / b ≤ a / c := by
  have hmod : a % c < c := Nat.mod_lt _ hc
  have hadd : c * (a / c) + a % c = a := Nat.div_add_mod _ _
  have hmul : c * (a / c) ≤ b * (a / c) := Nat.mul_le_mul_right _ h
  have hmul' : a / c * c ≤ b * (a / c) := by simpa [Nat.mul_comm] using! hmul
  apply (Nat.div_le_iff_le_mul_add_pred hb).mpr
  omega

/-- Shows that the escape probability at nineteen is bounded by that at any larger parameter. -/
theorem dlogEscapeProbability_mono (p q w : ℕ) (hp : 1 ≤ p) (hq : 0 < q) (hw : 19 ≤ w) :
    dlogEscapeProbability p q 19 ≤ dlogEscapeProbability p q w := by
  have hdiv : (p - 1) / w ≤ (p - 1) / 19 :=
    dlogDiv_le_div_of_le hw (by norm_num) (by omega)
  have hstep : (((p - 1) / w + 1 : ℕ) : ℝ) ≤ (((p - 1) / 19 + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hdiv
  have hnonneg : (0 : ℝ) ≤ (p - 1 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hden : (0 : ℝ) < 20 * (q : ℝ)^2 := by positivity
  have hfac : (0 : ℝ) ≤ (p - 1 : ℝ) / (20 * (q : ℝ)^2) :=
    div_nonneg hnonneg (le_of_lt hden)
  unfold dlogEscapeProbability
  have hbr : ((q / 12 : ℕ) : ℝ) - (((p - 1) / 19 + 1 : ℕ) : ℝ)
      ≤ ((q / 12 : ℕ) : ℝ) - (((p - 1) / w + 1 : ℕ) : ℝ) := by linarith
  exact mul_le_mul_of_nonneg_right hbr hfac

/-- Bounds a power of one minus a unit-interval parameter by the reciprocal of one plus its
linear accumulation. -/
theorem dlogOneSubPow_le_inv (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (t : ℕ) :
    (1 - δ) ^ t ≤ 1 / (1 + (t : ℝ) * δ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hcast : (((t + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by exact_mod_cast (Nat.cast_succ t)
    have hpos : (0 : ℝ) < 1 + (t : ℝ) * δ := by positivity
    have hpos' : (0 : ℝ) < 1 + (((t + 1 : ℕ) : ℝ) * δ) := by
      rw [hcast]
      positivity
    have hnonneg : (0 : ℝ) ≤ 1 - δ := by linarith
    have hsq : (0 : ℝ) ≤ δ ^ 2 := sq_nonneg δ
    calc
      (1 - δ) ^ (t + 1) = (1 - δ) ^ t * (1 - δ) := pow_succ _ _
      _ ≤ (1 / (1 + (t : ℝ) * δ)) * (1 - δ) :=
        mul_le_mul_of_nonneg_right ih hnonneg
      _ = (1 - δ) / (1 + (t : ℝ) * δ) := by ring
      _ ≤ 1 / (1 + (((t + 1 : ℕ) : ℝ) * δ)) := by
        rw [div_le_div_iff₀ hpos hpos']
        have hmain : (1 - δ) * (1 + (((t + 1 : ℕ) : ℝ) * δ))
            ≤ 1 + (t : ℝ) * δ := by
          rw [hcast]
          nlinarith [hsq]
        linarith

/-- Shows that the stated pinning sample condition reduces the union-bound estimate to at most
one half. -/
theorem dlogPinningBudget_le (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (t : ℕ)
    (ht : (2 * k - 1 : ℝ) ≤ (t : ℝ) * δ) :
    (k : ℝ) * (1 - δ) ^ t ≤ 1 / 2 := by
  have h1 := dlogOneSubPow_le_inv δ hδ.le hδ1.le t
  have hpos : (0 : ℝ) < 1 + (t : ℝ) * δ := by positivity
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  calc
    (k : ℝ) * (1 - δ) ^ t ≤ (k : ℝ) * (1 / (1 + (t : ℝ) * δ)) :=
      mul_le_mul_of_nonneg_left h1 hk
    _ = (k : ℝ) / (1 + (t : ℝ) * δ) := by ring
    _ ≤ 1 / 2 := by
      rw [div_le_iff₀ hpos]
      linarith

/-- Shows that the defined pinning budget satisfies the required linear sample inequality. -/
theorem dlogPinningBudget_suffices (W : Finset ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (2 * (W.card : ℝ) - 1) ≤ (dlogPinningBudget W δ : ℝ) * δ := by
  have hceil : (2 * (W.card : ℝ) - 1) / δ ≤ (dlogPinningBudget W δ : ℝ) := by
    have h1 : ((2 * (W.card : ℝ) - 1) / δ)
        < (Nat.floor ((2 * (W.card : ℝ) - 1) / δ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [dlogPinningBudget]
    push_cast
    linarith
  rw [div_le_iff₀ hδ] at hceil
  exact hceil

/-- Bounds the pinning budget by six thousand times the number of indices plus one for a
nonempty index set and the stated escape bound. -/
theorem dlogPinningBudget_le_mul_log2 (W : Finset ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hconst : (1 / 3000 : ℝ) ≤ δ) (hW : W.Nonempty) :
    dlogPinningBudget W δ ≤ 6000 * (W.card : ℕ) + 1 := by
  have hcard : (1 : ℝ) ≤ (W.card : ℝ) := by
    have hpos : 0 < W.card := Finset.card_pos.mpr hW
    have h1 : (1 : ℕ) ≤ W.card := by omega
    exact_mod_cast h1
  have hnum : (0 : ℝ) ≤ 2 * (W.card : ℝ) - 1 := by linarith
  have hx0 : (0 : ℝ) ≤ (2 * (W.card : ℝ) - 1) / δ := by
    exact div_nonneg hnum (le_of_lt hδ)
  have hfloor : ((Nat.floor ((2 * (W.card : ℝ) - 1) / δ) : ℝ))
      ≤ (2 * (W.card : ℝ) - 1) / δ := Nat.floor_le hx0
  have hbudget : (dlogPinningBudget W δ : ℝ)
      ≤ (2 * (W.card : ℝ) - 1) / δ + 1 := by
    rw [dlogPinningBudget]
    push_cast
    linarith
  have hstep : (1 : ℝ) ≤ 3000 * δ := by
    have h1 : (1 / 3000 : ℝ) * 3000 ≤ δ * 3000 := by
      have := mul_le_mul_of_nonneg_right hconst (by positivity : (0 : ℝ) ≤ 3000)
      linarith
    linarith
  have h1 : (2 * (W.card : ℝ) - 1) / δ ≤ (2 * (W.card : ℝ) - 1) * 3000 := by
    rw [div_le_iff₀ hδ]
    calc
      2 * (W.card : ℝ) - 1 ≤ (2 * (W.card : ℝ) - 1) * (3000 * δ) := by
        nlinarith [hnum]
      _ = ((2 * (W.card : ℝ) - 1) * 3000) * δ := by ring
  have h2 : (2 * (W.card : ℝ) - 1) * 3000 ≤ 6000 * (W.card : ℝ) := by nlinarith [hnum]
  have h3 : (dlogPinningBudget W δ : ℝ) ≤ 6000 * (W.card : ℝ) + 1 := by
    linarith
  have h4 : dlogPinningBudget W δ ≤ 6000 * (W.card : ℕ) + 1 := by
    have h5 : (dlogPinningBudget W δ : ℝ) ≤ ((6000 * (W.card : ℕ) + 1 : ℕ) : ℝ) := by
      exact_mod_cast h3
    exact_mod_cast h5
  exact h4

/-- Shows that the natural floor of a nonpositive real number is zero. -/
private theorem dlogFloor_nonpos (x : ℝ) (hx : x ≤ 0) : Nat.floor x = 0 := by
  rw [Nat.floor_of_nonpos hx]

/-- Shows that the natural binary logarithm is monotone. -/
private theorem dlogLog2_mono (a b : ℕ) (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases ha2 : 2 ≤ a
    · have hb2 : 2 ≤ b := by omega
      have h1 : a / 2 ≤ b / 2 := by omega
      have h2 : b / 2 < b := by omega
      have hrec : Nat.log2 (a / 2) ≤ Nat.log2 (b / 2) := ih (b / 2) h2 (a / 2) h1
      have hA : Nat.log2 a = (a / 2).log2 + 1 := by rw [Nat.log2_def]; simp [ha2]
      have hB : Nat.log2 b = (b / 2).log2 + 1 := by rw [Nat.log2_def]; simp [hb2]
      rw [hA, hB]
      omega
    · have hA : Nat.log2 a = 0 := by rw [Nat.log2_def]; simp [ha2]
      rw [hA]
      omega

/-- Bounds the uniform escape probability below by one over three thousand in the stated modulus
range. -/
theorem dlogUniformEscapeProbability_ge_const (p q : ℕ) (hp : 1000 ≤ p) (hq : p < q)
    (hq2 : q < 2 * p) :
    (1 / 3000 : ℝ) ≤ dlogUniformEscapeProbability p q := by
  have hpr0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpr1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hpr1000 : (1000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hqr : (p : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq2r : (q : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hq2
  have hnat : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    have h1 : (p - 1 : ℕ) + 1 = p := by omega
    have h2 : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
      have h3 : ((p - 1 : ℕ) : ℝ) + 1 = (((p - 1 : ℕ) + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
      have h4 : (((p - 1 : ℕ) + 1 : ℕ) : ℝ) = (p : ℝ) := by exact_mod_cast h1
      rw [h3, h4]
    linarith
  have hq12 : ((q / 12 : ℕ) : ℝ) ≥ (q : ℝ) / 12 - 1 := by
    have hdiv : (12 : ℝ) * ((q / 12 : ℕ) : ℝ) + ((q % 12 : ℕ) : ℝ) = (q : ℝ) := by
      exact_mod_cast Nat.div_add_mod q 12
    have hmod : ((q % 12 : ℕ) : ℝ) ≤ 11 := by
      have h1 := Nat.mod_lt q (by norm_num : 0 < 12)
      have h2 : q % 12 ≤ 11 := by omega
      exact_mod_cast h2
    have hpos : (0 : ℝ) < 12 := by norm_num
    have hmul : (12 : ℝ) * ((q / 12 : ℕ) : ℝ)
        = (q : ℝ) - ((q % 12 : ℕ) : ℝ) := by linarith
    have hA : ((q / 12 : ℕ) : ℝ) = ((q : ℝ) - ((q % 12 : ℕ) : ℝ)) / 12 := by
      rw [eq_div_iff (by norm_num : (12 : ℝ) ≠ 0)]
      linarith
    have hstep : ((q : ℝ) - 11) / 12 ≤ ((q : ℝ) - ((q % 12 : ℕ) : ℝ)) / 12 := by
      apply (div_le_div_iff₀ hpos hpos).2
      linarith
    have hsmall : (11 : ℝ) / 12 ≤ 1 := by norm_num
    rw [hA]
    have hident : ((q : ℝ) - 11) / 12 = (q : ℝ) / 12 - 11 / 12 := by ring
    linarith
  have hA : 12 * ((q / 12 : ℕ) : ℝ) ≥ (q : ℝ) - 12 := by
    have hdiv : (12 : ℝ) * ((q / 12 : ℕ) : ℝ) + ((q % 12 : ℕ) : ℝ) = (q : ℝ) := by
      exact_mod_cast Nat.div_add_mod q 12
    have hmod : ((q % 12 : ℕ) : ℝ) ≤ 11 := by
      have h1 := Nat.mod_lt q (by norm_num : 0 < 12)
      have h2 : q % 12 ≤ 11 := by omega
      exact_mod_cast h2
    linarith
  have hB : 19 * (((p - 1) / 19 : ℕ) : ℝ) ≤ (p - 1 : ℝ) := by
    have hdiv : (19 : ℝ) * (((p - 1) / 19 : ℕ) : ℝ) + (((p - 1) % 19 : ℕ) : ℝ)
        = ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_add_mod (p - 1) 19
    have hmod : (0 : ℝ) ≤ (((p - 1) % 19 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hnat] at hdiv
    linarith
  have hbracket : ((q / 12 : ℕ) : ℝ) - (((p - 1) / 19 + 1 : ℕ) : ℝ)
      ≥ (7 * (p : ℝ) - 425) / 228 := by
    have hgoal : 7 * (p : ℝ) - 425
        ≤ (((q / 12 : ℕ) : ℝ) - (((p - 1) / 19 + 1 : ℕ) : ℝ)) * 228 := by
      have hA228 : 228 * ((q / 12 : ℕ) : ℝ) ≥ 19 * (q : ℝ) - 228 := by
        have hs : 19 * ((q : ℝ) - 12) ≤ 19 * (12 * ((q / 12 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hA (by norm_num)
        calc 228 * ((q / 12 : ℕ) : ℝ) = 19 * (12 * ((q / 12 : ℕ) : ℝ)) := by ring
          _ ≥ 19 * ((q : ℝ) - 12) := by linarith
          _ = 19 * (q : ℝ) - 228 := by ring
      have hB' : 19 * (((p - 1) / 19 + 1 : ℕ) : ℝ) ≤ (p - 1 : ℝ) + 19 := by
        have hcast : (((p - 1) / 19 + 1 : ℕ) : ℝ) = (((p - 1) / 19 : ℕ) : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [hcast]
        linarith [hB]
      have hB228 : 228 * (((p - 1) / 19 + 1 : ℕ) : ℝ) ≤ 12 * (p - 1 : ℝ) + 228 := by
        calc 228 * (((p - 1) / 19 + 1 : ℕ) : ℝ)
            = 12 * (19 * (((p - 1) / 19 + 1 : ℕ) : ℝ)) := by ring
          _ ≤ 12 * ((p - 1 : ℝ) + 19) := mul_le_mul_of_nonneg_left hB' (by norm_num)
          _ = 12 * (p - 1 : ℝ) + 228 := by ring
      have hq1 : (q : ℝ) ≥ (p : ℝ) + 1 := by
        have h3 : (p + 1 : ℕ) ≤ q := by omega
        exact_mod_cast h3
      have hq1' : 19 * (q : ℝ) ≥ 19 * (p : ℝ) + 19 := by linarith
      have hcomb : 228 * ((q / 12 : ℕ) : ℝ) ≥ 19 * (p : ℝ) + 19 - 228 := by
        linarith
      have hcomb2 : 228 * ((q / 12 : ℕ) : ℝ) - 228 * (((p - 1) / 19 + 1 : ℕ) : ℝ)
          ≥ 19 * (p : ℝ) + 19 - 228 - (12 * (p - 1 : ℝ) + 228) := by
        linarith
      have hexpanded : 7 * (p : ℝ) - 425
          ≤ 228 * ((q / 12 : ℕ) : ℝ) - 228 * (((p - 1) / 19 + 1 : ℕ) : ℝ) := by
        linarith
      calc 7 * (p : ℝ) - 425
          ≤ 228 * ((q / 12 : ℕ) : ℝ) - 228 * (((p - 1) / 19 + 1 : ℕ) : ℝ) := hexpanded
        _ = (((q / 12 : ℕ) : ℝ) - (((p - 1) / 19 + 1 : ℕ) : ℝ)) * 228 := by ring
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 228)).2
    exact hgoal
  have hfactor : (p - 1 : ℝ) / (80 * (p : ℝ)^2)
      ≤ (p - 1 : ℝ) / (20 * (q : ℝ)^2) := by
    have hprod : (0 : ℝ) ≤ (2 * (p : ℝ) - q) * (2 * (p : ℝ) + q) := by
      have h1 : (0 : ℝ) ≤ 2 * (p : ℝ) - q := by linarith
      have h2 : (0 : ℝ) ≤ 2 * (p : ℝ) + q := by linarith
      exact mul_nonneg h1 h2
    have hid : 4 * (p : ℝ)^2 - q ^ 2 = (2 * (p : ℝ) - q) * (2 * (p : ℝ) + q) := by ring
    have hsq : (q : ℝ)^2 ≤ 4 * (p : ℝ)^2 := by linarith
    have hle : 20 * (q : ℝ)^2 ≤ 80 * (p : ℝ)^2 := by linarith
    have hnum : (0 : ℝ) ≤ (p - 1 : ℝ) := by linarith
    have hd1 : (0 : ℝ) < 20 * (q : ℝ)^2 := by
      have h1 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      exact mul_pos (by norm_num) (sq_pos_of_pos h1)
    have hd2 : (0 : ℝ) < 80 * (p : ℝ)^2 := by
      exact mul_pos (by norm_num) (sq_pos_of_pos hpr0)
    apply (div_le_div_iff₀ hd2 hd1).2
    exact mul_le_mul_of_nonneg_left hle hnum
  have hnonnegA : (0 : ℝ) ≤ (7 * (p : ℝ) - 425) / 228 := by
    have h1 : (0 : ℝ) < 228 := by norm_num
    apply (div_nonneg (by linarith) h1.le)
  have hnonnegB : (0 : ℝ) ≤ (p - 1 : ℝ) / (80 * (p : ℝ)^2) := by
    apply div_nonneg
    · linarith
    · have h1 : (0 : ℝ) < 80 * (p : ℝ)^2 := by
        exact mul_pos (by norm_num) (sq_pos_of_pos hpr0)
      exact h1.le
  have hnonnegC : (0 : ℝ) ≤ (p - 1 : ℝ) / (20 * (q : ℝ)^2) := by
    apply div_nonneg
    · linarith
    · have h1 : (0 : ℝ) < 20 * (q : ℝ)^2 := by
        have h2 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        exact mul_pos (by norm_num) (sq_pos_of_pos h2)
      exact h1.le
  have hmain : (7 * (p : ℝ) - 425) / 228 * ((p - 1 : ℝ) / (80 * (p : ℝ)^2)) ≥ 1 / 3000 := by
    have hnum : ((7 * (p : ℝ) - 425) * (p - 1 : ℝ)) * 3000
        ≥ 18240 * (p : ℝ)^2 := by
      have hcert : (0 : ℝ) ≤ 2760 * (p - 1000) ^ 2 + 4224000 * (p - 1000) + 1465275000 := by
        have h1 : (0 : ℝ) ≤ 2760 * (p - 1000) ^ 2 := by positivity
        have h2 : (0 : ℝ) ≤ 4224000 * (p - 1000) := by
          have h3 : (0 : ℝ) ≤ p - 1000 := by linarith
          exact mul_nonneg (by norm_num) h3
        linarith
      have hid : ((7 * (p : ℝ) - 425) * (p - 1 : ℝ)) * 3000 - 18240 * (p : ℝ)^2
          = 2760 * (p - 1000) ^ 2 + 4224000 * (p - 1000) + 1465275000 := by
        ring
      have hdiff : (0 : ℝ) ≤
          ((7 * (p : ℝ) - 425) * (p - 1 : ℝ)) * 3000 - 18240 * (p : ℝ)^2 := by
        rw [hid]
        linarith
      linarith
    have hrewrite : (7 * (p : ℝ) - 425) / 228 * ((p - 1 : ℝ) / (80 * (p : ℝ)^2))
        = ((7 * (p : ℝ) - 425) * (p - 1 : ℝ)) / (18240 * (p : ℝ)^2) := by
      field_simp
      ring
    have hd1 : (0 : ℝ) < 18240 * (p : ℝ)^2 := by
      exact mul_pos (by norm_num) (sq_pos_of_pos hpr0)
    have hd2 : (0 : ℝ) < 3000 := by norm_num
    rw [hrewrite]
    apply (div_le_div_iff₀ hd2 hd1).2
    linarith
  unfold dlogUniformEscapeProbability dlogEscapeProbability
  have hA : (((q / 12 : ℕ) : ℝ) - (((p - 1) / 19 + 1 : ℕ) : ℝ))
      ≥ (7 * (p : ℝ) - 425) / 228 := hbracket
  have hB : (p - 1 : ℝ) / (20 * (q : ℝ)^2)
      ≥ (p - 1 : ℝ) / (80 * (p : ℝ)^2) := by linarith [hfactor]
  have hnonnegBracket : (0 : ℝ)
      ≤ (((q / 12 : ℕ) : ℝ) - (((p - 1) / 19 + 1 : ℕ) : ℝ)) := by linarith
  have hprod := mul_le_mul hA hB hnonnegB hnonnegBracket
  linarith

/-- Bounds the pinning budget by six thousand times the number of indices plus one, including
the empty case. -/
theorem dlogPinningBudget_le_mul_log2' (W : Finset ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hconst : (1 / 3000 : ℝ) ≤ δ) :
    dlogPinningBudget W δ ≤ 6000 * (W.card : ℕ) + 1 := by
  by_cases hW : W.Nonempty
  · exact dlogPinningBudget_le_mul_log2 W δ hδ hconst hW
  · have hempty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    have hcard : W.card = 0 := by simp [hempty]
    have hneg : (-1 : ℝ) / δ < 0 := by
      have h1 : (0 : ℝ) < δ := hδ
      have h3 : (-1 : ℝ) / δ = -(1 / δ) := by field_simp
      rw [h3]
      have h2 : (0 : ℝ) < 1 / δ := one_div_pos.mpr h1
      linarith
    have hfloor : Nat.floor (-1 / δ) = 0 := dlogFloor_nonpos _ hneg.le
    rw [dlogPinningBudget, hcard]
    have hzero : (2 * (0 : ℝ) - 1) = -1 := by ring
    simp only [Nat.cast_zero, hzero, hfloor]
    norm_num

/-- Bounds the large-prime pinning budget by a linear function of the number of large base
primes. -/
theorem dlogPinningBudget_modulus_le (p q : ℕ) (hp : 1000 ≤ p) (hq : p < q)
    (hq2 : q < 2 * p) :
    dlogPinningBudget (dlogLargeBasePrimes (p - 1)) (dlogUniformEscapeProbability p q)
      ≤ 6000 * (dlogLargeBasePrimes (p - 1)).card + 1 := by
  have hconst : (1 / 3000 : ℝ) ≤ dlogUniformEscapeProbability p q :=
    dlogUniformEscapeProbability_ge_const p q hp hq hq2
  have hδ : (0 : ℝ) < dlogUniformEscapeProbability p q := by linarith
  exact dlogPinningBudget_le_mul_log2' _ _ hδ hconst

/-- Bounds the large-prime pinning budget by six thousand times the binary logarithm of `p - 1`
plus one. -/
theorem dlogPinningBudget_log2_le (p q : ℕ) (hp : 1000 ≤ p) (hq : p < q)
    (hq2 : q < 2 * p) :
    dlogPinningBudget (dlogLargeBasePrimes (p - 1)) (dlogUniformEscapeProbability p q)
      ≤ 6000 * Nat.log2 (p - 1) + 1 := by
  have h1 := dlogPinningBudget_modulus_le p q hp hq hq2
  have h2 : (dlogLargeBasePrimes (p - 1)).card ≤ Nat.log2 (p - 1) :=
    dlogLargeBasePrimes_card_le_log2 (p - 1) (by omega)
  have h3 : ((dlogLargeBasePrimes (p - 1)).card : ℕ) ≤ Nat.log2 (p - 1) := by
    exact_mod_cast h2
  omega

/-- Shows that the modular multiplication remainder circuit computes the product modulo the
encoded modulus. -/
theorem dlogModMulRemainder_value (w : ℕ) (a b : Reg w) (mReg : Reg (2 * w)) (m : ℕ)
    (hm : booleanWordLSBValue (2 * w) mReg = m) :
    booleanWordLSBValue (2 * (2 * w)) (dlogModMulRemainder w a b mReg)
      = (booleanWordLSBValue w a * booleanWordLSBValue w b) % m := by
  have hdiv := boolean_word_div_value (2 * w) (booleanWordMulResult w a b) mReg
  have hmul := boolean_word_mul_value w a b
  rw [dlogModMulRemainder]
  rw [hdiv.2, hmul, hm]

/-- Bounds the multiplication and division step counts by `dlogModMulGateCount`. -/
theorem dlogModMulGateCount_ge (w : ℕ) :
    (booleanDAGSteps (booleanWordMulProgram w).graph (booleanWordMulSelect w)).length
      + (booleanDAGSteps (booleanWordDivDAG (2 * w)) (booleanWordDivSelect (2 * w))).length
      ≤ dlogModMulGateCount w := by
  have h1 := boolean_word_mul_resources w
  simp only [booleanWordMulProgram] at h1
  have h2 := boolean_word_div_resources (2 * w)
  simp only [booleanWordDivProgram, booleanWordDivDAG] at h2
  have hlen1 : (booleanDAGSteps (booleanWordMulProgram w).graph
      (booleanWordMulSelect w)).length ≤ 330 * w ^ 2 + 32 * w + 30 := h1.2.2.1
  have hlen2 : (booleanDAGSteps (booleanWordDivDAG (2 * w))
      (booleanWordDivSelect (2 * w))).length
      ≤ 600 * (2 * w) ^ 2 + 183 * (2 * w) + 30 := h2.2.2.1
  simp only [dlogModMulGateCount]
  nlinarith

/-- Bounds the specified multiplication and division workspace expression by
`dlogModMulSpaceCount`. -/
theorem dlogModMulSpaceCount_ge (w : ℕ) :
    (2 * w + (booleanWordMulProgram w).nodes + 2 * w)
      + (2 * (2 * w) + ((booleanWordDivProgram (2 * w)).nodes + (2 * w)) + 3 * (2 * w))
      ≤ dlogModMulSpaceCount w := by
  have h1 := boolean_word_mul_resources w
  simp only [booleanWordMulProgram] at h1
  have h2 := boolean_word_div_resources (2 * w)
  simp only [booleanWordDivProgram, booleanWordDivDAG] at h2
  have hwid1 : 2 * w + (booleanWordMulProgram w).nodes + 2 * w ≤ 11 * w ^ 2 + 5 * w + 1 :=
    h1.2.2.2.2.2
  have hwid2 : 2 * (2 * w) + ((booleanWordDivProgram (2 * w)).nodes + (2 * w)) + 3 * (2 * w)
      ≤ 20 * (2 * w) ^ 2 + 11 * (2 * w) + 1 := h2.2.2.2.2.2
  simp only [dlogModMulSpaceCount]
  nlinarith

/-- Shows that reducing before squaring leaves the final modular square unchanged. -/
private theorem dlogSqMod (x m : ℕ) : (x % m) ^ 2 % m = x ^ 2 % m := by
  rw [pow_two, pow_two]
  exact (Nat.mul_mod x x m).symm

/-- Shows that reducing before squaring and multiplying leaves the final modular result
unchanged. -/
private theorem dlogSqMulMod (x y m : ℕ) : ((x % m) ^ 2 * y) % m = (x ^ 2 * y) % m := by
  have h1 : ((x % m) ^ 2 * y) % m = ((x % m) ^ 2) % m * (y % m) % m := Nat.mul_mod _ _ _
  have h2 : ((x % m) ^ 2) % m = (x ^ 2) % m := dlogSqMod x m
  have h3 : ((x ^ 2) % m) * (y % m) % m = (x ^ 2 * y) % m := (Nat.mul_mod _ _ _).symm
  rw [h1, h2, h3]

/-- Shows that `dlogModexpValue` computes modular exponentiation. -/
theorem dlogModexpValue_eq (base m e : ℕ) : dlogModexpValue base m e = base ^ e % m := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [dlogModexpValue]
    split
    · next he =>
      subst he
      simp
    · next he =>
      have hpos : 0 < e := Nat.pos_of_ne_zero he
      have hhalf : e / 2 < e := by omega
      have hval := ih (e / 2) hhalf
      have hsplit : 2 * (e / 2) + e % 2 = e := Nat.div_add_mod e 2
      by_cases hodd : e % 2 = 1
      · rw [ite_eq_left hodd, hval]
        have hsq : ((base ^ (e / 2) % m) ^ 2 * base) % m
            = ((base ^ (e / 2)) ^ 2 * base) % m := dlogSqMulMod (base ^ (e / 2)) base m
        rw [hsq, pow_two]
        rw [← pow_add, ← pow_succ]
        rw [show e / 2 + e / 2 + 1 = e by omega]
      · rw [ite_eq_right hodd, hval, Nat.mul_one]
        have hsq : ((base ^ (e / 2) % m) ^ 2) % m = ((base ^ (e / 2)) ^ 2) % m :=
          dlogSqMod (base ^ (e / 2)) m
        rw [hsq, pow_two]
        rw [← pow_add]
        rw [show e / 2 + e / 2 = e by omega]

/-- Gives the explicit polynomial formula for the modular exponentiation gate count. -/
theorem dlogModexpGateCount_eq (w e : ℕ) :
    dlogModexpGateCount w e = 2 * (Nat.log2 e + 1) * (2730 * w ^ 2 + 398 * w + 60) := rfl

/-- Bounds the modular exponentiation gate count by a cubic expression in the bit width of `p`. -/
theorem dlogModexpGateCount_cube_le (p : ℕ) (hp : 2 ≤ p) :
    dlogModexpGateCount (Nat.log2 p + 1) (p - 1) ≤ 6400 * (Nat.log2 p + 1) ^ 3 := by
  have hlog : Nat.log2 (p - 1) ≤ Nat.log2 p := dlogLog2_mono (p - 1) p (by omega)
  have hw : (1 : ℕ) ≤ Nat.log2 p + 1 := by omega
  rw [dlogModexpGateCount_eq]
  have hbits : Nat.log2 (p - 1) + 1 ≤ Nat.log2 p + 1 := by omega
  have hbits2 : 2 * (Nat.log2 (p - 1) + 1) ≤ 2 * (Nat.log2 p + 1) := by omega
  have hmul : 2 * (Nat.log2 (p - 1) + 1) * (2730 * (Nat.log2 p + 1) ^ 2
      + 398 * (Nat.log2 p + 1) + 60) ≤ 6400 * (Nat.log2 p + 1) ^ 3 := by
    have h2 : 1 ≤ Nat.log2 p + 1 := by omega
    have h3 : 2730 * (Nat.log2 p + 1) ^ 2 + 398 * (Nat.log2 p + 1) + 60
        ≤ 3200 * (Nat.log2 p + 1) ^ 2 := by
      nlinarith [sq_nonneg (Nat.log2 p + 1)]
    calc
      2 * (Nat.log2 (p - 1) + 1) * (2730 * (Nat.log2 p + 1) ^ 2
            + 398 * (Nat.log2 p + 1) + 60)
          ≤ 2 * (Nat.log2 p + 1) * (2730 * (Nat.log2 p + 1) ^ 2
            + 398 * (Nat.log2 p + 1) + 60) := by
              exact mul_le_mul_of_nonneg_right hbits2 (by positivity)
        _ ≤ 2 * (Nat.log2 p + 1) * (3200 * (Nat.log2 p + 1) ^ 2) := by
              exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 6400 * (Nat.log2 p + 1) ^ 3 := by ring
  exact hmul

/-- Shows that multiplying the third register value by the compensating power of `x` yields the
corresponding power of `g`. -/
theorem dlogThirdRegisterValue_mul (p : ℕ) (g x : ZMod p) (a b : ℕ)
    (hx : x ^ (p - 1) = 1) (hb : b ≤ p - 1) :
    dlogThirdRegisterValue p g x a b * x ^ b = g ^ a := by
  have hsplit : (p - 1 - b) + b = p - 1 := by omega
  have hmul : x ^ (p - 1) = x ^ (p - 1 - b) * x ^ b := by
    have h1 : x ^ ((p - 1 - b) + b) = x ^ (p - 1 - b) * x ^ b := by
      rw [pow_add]
    calc x ^ (p - 1) = x ^ ((p - 1 - b) + b) := by rw [hsplit]
      _ = x ^ (p - 1 - b) * x ^ b := h1
  have hone : x ^ (p - 1 - b) * x ^ b = 1 := by rw [← hmul, hx]
  rw [dlogThirdRegisterValue, mul_assoc, hone, mul_one]

/-- Expresses the third register value entirely in powers of `g` when `x` is a power of `g`. -/
theorem dlogThirdRegisterValue_eq_pow (p : ℕ) (g x : ZMod p) (a b r : ℕ)
    (hr : x = g ^ r) :
    dlogThirdRegisterValue p g x a b = g ^ a * g ^ ((p - 1 - b) * r) := by
  rw [dlogThirdRegisterValue, hr, ← pow_mul]
  simp [Nat.mul_comm]

/-- Identifies the two modular exponentiation factors and their product with the third register
value. -/
theorem dlogModexpFactors_spec (p : ℕ) (g x : ZMod p) (a b : ℕ) :
    (dlogModexpFactors p g x a b).1 = g ^ a ∧
      (dlogModexpFactors p g x a b).2 = x ^ (p - 1 - b) ∧
      (dlogModexpFactors p g x a b).1 * (dlogModexpFactors p g x a b).2
        = dlogThirdRegisterValue p g x a b := by
  refine ⟨rfl, rfl, rfl⟩

/-- Shows that the factorization exponent of a base prime is positive. -/
theorem dlogFactorization_pos (m ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) :
    0 < m.factorization ℓ := by
  have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hne : m ≠ 0 := (Nat.mem_primeFactors.mp hℓ).2.2
  have hdiv : ℓ ∣ m := (Nat.mem_primeFactors.mp hℓ).2.1
  have hne' : m.factorization ℓ ≠ 0 := by
    intro hz
    have h1 : ¬ℓ.Prime ∨ ¬(ℓ ∣ m) ∨ m = 0 :=
      (Nat.factorization_eq_zero_iff m ℓ).mp hz
    rcases h1 with h1 | h1 | h1
    · exact absurd hprime h1
    · exact absurd hdiv h1
    · exact hne h1
  exact Nat.pos_of_ne_zero hne'

/-- Identifies prime candidates with prime-power candidates at the modulus's factorization
exponent. -/
theorem dlogPrimeCandidates_eq_prime_power (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (ℓ : ℕ) :
    dlogPrimeCandidates m rec ℓ = dlogPrimePowerCandidates ℓ (m.factorization ℓ) rec := rfl

/-- Expresses the common valuation using the multiplier gcd, with the cap used when the gcd is
zero. -/
theorem dlogCommonValuation_eq (ℓ cap : ℕ) {t m : ℕ} (rec : DlogSampleRecord m t) :
    dlogCommonValuation ℓ cap rec = if dlogMultiplierGcd rec = 0 then cap
      else min cap ((dlogMultiplierGcd rec).factorization ℓ) := rfl

/-- Bounds the common valuation by its cap. -/
theorem dlogCommonValuation_le (ℓ cap : ℕ) {t m : ℕ} (rec : DlogSampleRecord m t) :
    dlogCommonValuation ℓ cap rec ≤ cap := by
  rw [dlogCommonValuation_eq]
  split_ifs
  · exact le_rfl
  · exact Nat.min_le_left _ _

/-- Shows that the prime raised to the common valuation divides every sample multiplier's
absolute value. -/
theorem dlogCommonValuation_dvd (ℓ cap : ℕ) {t m : ℕ} (rec : DlogSampleRecord m t)
    (hℓ : ℓ.Prime) (i : Fin t) :
    ℓ ^ dlogCommonValuation ℓ cap rec ∣ (rec.cprime i).natAbs := by
  have hG : dlogMultiplierGcd rec ∣ (rec.cprime i).natAbs :=
    Finset.gcd_dvd (Finset.mem_univ i)
  rw [dlogCommonValuation_eq]
  split_ifs with hG0
  · obtain ⟨k, hk⟩ := hG
    rw [hG0, zero_mul] at hk
    rw [hk]
    exact Nat.dvd_zero _
  · have hGne : dlogMultiplierGcd rec ≠ 0 := hG0
    have hle : min cap ((dlogMultiplierGcd rec).factorization ℓ)
        ≤ (dlogMultiplierGcd rec).factorization ℓ := Nat.min_le_right _ _
    have hdvd : ℓ ^ min cap ((dlogMultiplierGcd rec).factorization ℓ) ∣ dlogMultiplierGcd rec := by
      rw [Nat.Prime.pow_dvd_iff_le_factorization hℓ hGne]
      exact hle
    exact hdvd.trans hG

/-- Shows that the common valuation reaches its cap or some multiplier fails divisibility at the
next exponent. -/
theorem dlogCommonValuation_max (ℓ cap : ℕ) {t m : ℕ} (rec : DlogSampleRecord m t)
    (hℓ : ℓ.Prime) :
    dlogCommonValuation ℓ cap rec = cap ∨
      ∃ i, ¬ ℓ ^ (dlogCommonValuation ℓ cap rec + 1) ∣ (rec.cprime i).natAbs := by
  rw [dlogCommonValuation_eq]
  split_ifs with hG0
  · exact Or.inl rfl
  · have hGne : dlogMultiplierGcd rec ≠ 0 := hG0
    by_cases hk : min cap ((dlogMultiplierGcd rec).factorization ℓ) = cap
    · exact Or.inl hk
    · right
      have hklt : min cap ((dlogMultiplierGcd rec).factorization ℓ) < cap := by omega
      have hfac : min cap ((dlogMultiplierGcd rec).factorization ℓ)
          = (dlogMultiplierGcd rec).factorization ℓ := Nat.min_eq_right (by omega)
      have hnot : ¬ ℓ ^ (min cap ((dlogMultiplierGcd rec).factorization ℓ) + 1)
          ∣ dlogMultiplierGcd rec := by
        rw [hfac, Nat.Prime.pow_dvd_iff_le_factorization hℓ hGne]
        omega
      by_contra hcon
      push Not at hcon
      exact hnot (Finset.dvd_gcd fun b _ => hcon b)

/-- Cancels the exact prime-power valuation of a factor from a divisibility relation. -/
theorem dlogValuationStep (ℓ α k a b : ℕ) (hℓ : ℓ.Prime) (hk : k ≤ α)
    (hb : ℓ ^ k ∣ b) (hb' : ¬ ℓ ^ (k + 1) ∣ b) (hdvd : ℓ ^ α ∣ a * b) :
    ℓ ^ (α - k) ∣ a := by
  by_cases ha : a = 0
  · subst ha
    exact Nat.dvd_zero _
  · have hbne : b ≠ 0 := by
      intro hb0
      subst hb0
      exact hb' (Nat.dvd_zero _)
    have hbfac : b.factorization ℓ = k := by
      have h1 : ¬ (k + 1 ≤ b.factorization ℓ) := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization hℓ hbne]
        exact hb'
      have h2 : k ≤ b.factorization ℓ := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization hℓ hbne]
        exact hb
      omega
    have habne : a * b ≠ 0 := by
      intro h0
      exact hbne ((Nat.mul_eq_zero.mp h0).resolve_left ha)
    have hfac : (a * b).factorization ℓ = a.factorization ℓ + b.factorization ℓ := by
      rw [Nat.factorization_mul (by omega) (by omega)]
      exact Finsupp.add_apply _ _ _
    have hα : α ≤ (a * b).factorization ℓ := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hℓ habne]
      exact hdvd
    have hle : α - k ≤ a.factorization ℓ := by omega
    rw [Nat.Prime.pow_dvd_iff_le_factorization hℓ ha]
    exact hle

/-- Relates integer divisibility of a product to natural divisibility of the product of absolute
values. -/
theorem dlogIntDvd_iff {n a b : ℤ} :
    n ∣ a * b ↔ n.natAbs ∣ a.natAbs * b.natAbs := by
  rw [← Int.natAbs_dvd_natAbs]
  simp [Int.natAbs_mul]

/-- Characterizes prime-power candidates by their range and divisibility of differences from a
fixed candidate. -/
theorem dlogPrimePowerCandidates_iff_diff (ℓ α : ℕ) {t m : ℕ}
    (rec : DlogSampleRecord m t) {ρ ρ₀ : ℕ}
    (hρ₀ : ρ₀ ∈ dlogPrimePowerCandidates ℓ α rec) :
    ρ ∈ dlogPrimePowerCandidates ℓ α rec ↔
      (ρ < ℓ ^ α ∧ ∀ i, (ℓ ^ α : ℤ) ∣ ((ρ : ℤ) - (ρ₀ : ℤ)) * rec.cprime i) := by
  constructor
  · intro hρ
    refine ⟨Finset.mem_range.mp (Finset.mem_filter.mp hρ).1, ?_⟩
    intro i
    have h1 := (Finset.mem_filter.mp hρ).2 i
    have h2 := (Finset.mem_filter.mp hρ₀).2 i
    have h3 : (ℓ ^ α : ℤ) ∣ (rec.dprime i + (ρ : ℤ) * rec.cprime i) :=
      Int.modEq_zero_iff_dvd.mp h1
    have h4 : (ℓ ^ α : ℤ) ∣ (rec.dprime i + (ρ₀ : ℤ) * rec.cprime i) :=
      Int.modEq_zero_iff_dvd.mp h2
    have h5 : (ℓ ^ α : ℤ) ∣
        (rec.dprime i + (ρ : ℤ) * rec.cprime i) - (rec.dprime i + (ρ₀ : ℤ) * rec.cprime i) :=
      Int.dvd_sub h3 h4
    convert! h5 using 1
    ring
  · rintro ⟨hρlt, hρ⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hρlt, ?_⟩
    intro i
    have h3 := (Finset.mem_filter.mp hρ₀).2 i
    have h4 : (ℓ ^ α : ℤ) ∣ (rec.dprime i + (ρ₀ : ℤ) * rec.cprime i) :=
      Int.modEq_zero_iff_dvd.mp h3
    have h6 : (ℓ ^ α : ℤ) ∣
        (rec.dprime i + (ρ₀ : ℤ) * rec.cprime i) + ((ρ : ℤ) - (ρ₀ : ℤ)) * rec.cprime i :=
      Int.dvd_add h4 (hρ i)
    refine Int.modEq_zero_iff_dvd.mpr ?_
    convert! h6 using 1
    ring

/-- Shows that candidate differences are divisible by the prime power remaining after the common
valuation. -/
theorem dlogDifference_dvd (ℓ α : ℕ) (hℓ : ℓ.Prime) {t m : ℕ}
    (rec : DlogSampleRecord m t) {ρ ρ₀ : ℕ}
    (hcond : ∀ i, (ℓ ^ α : ℤ) ∣ ((ρ : ℤ) - (ρ₀ : ℤ)) * rec.cprime i) :
    (ℓ ^ (α - dlogCommonValuation ℓ α rec) : ℤ) ∣ (ρ : ℤ) - (ρ₀ : ℤ) := by
  have hk : dlogCommonValuation ℓ α rec ≤ α := dlogCommonValuation_le ℓ α rec
  by_cases hka : dlogCommonValuation ℓ α rec = α
  · rw [hka]
    simp
  · obtain ⟨i, hi⟩ :=
      (dlogCommonValuation_max ℓ α rec hℓ).resolve_left hka
    have hcond' := hcond i
    have hdvd : ℓ ^ α ∣ ((ρ : ℤ) - (ρ₀ : ℤ)).natAbs * (rec.cprime i).natAbs := by
      have h := (dlogIntDvd_iff (n := (ℓ ^ α : ℤ)) (a := (ρ : ℤ) - (ρ₀ : ℤ))
        (b := rec.cprime i)).1 hcond'
      simpa using! h
    have hstep : ℓ ^ (α - dlogCommonValuation ℓ α rec) ∣ ((ρ : ℤ) - (ρ₀ : ℤ)).natAbs := by
      refine dlogValuationStep ℓ α (dlogCommonValuation ℓ α rec) _
        (rec.cprime i).natAbs hℓ hk ?_ ?_ hdvd
      · exact dlogCommonValuation_dvd ℓ α rec hℓ i
      · exact hi
    rw [← Int.natAbs_dvd_natAbs]
    simpa using! hstep

/-- Shows that a natural number congruent to a progression element has a natural progression
index when the residue is below the step. -/
theorem dlogDifference_eq_progression (d ρ ρ₀ r w : ℕ) (hd : 0 < d) (hrlt : r < d)
    (hdiv : (d : ℤ) ∣ (ρ : ℤ) - (ρ₀ : ℤ)) (hw : ρ₀ = r + d * w) :
    ∃ j : ℕ, ρ = r + d * j := by
  obtain ⟨z, hz⟩ := hdiv
  have hrw : (ρ₀ : ℤ) = (r : ℤ) + (d : ℤ) * (w : ℤ) := by
    rw [hw, Int.natCast_add, Int.natCast_mul]
  have hr : (ρ : ℤ) = (r : ℤ) + (d : ℤ) * ((w : ℤ) + z) := by linarith
  have hz' : 0 ≤ (w : ℤ) + z := by
    have hdpos' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    have hrlt' : (r : ℤ) < (d : ℤ) := by exact_mod_cast hrlt
    have h1 : 0 ≤ (ρ : ℤ) := by exact_mod_cast (Nat.zero_le ρ)
    rcases lt_or_ge ((w : ℤ) + z) 0 with hneg | hpos
    · exfalso
      have hmul : (d : ℤ) * ((w : ℤ) + z) ≤ (d : ℤ) * (-1) := by
        have h := Int.mul_le_mul_of_nonneg_right (a := ((w : ℤ) + z)) (b := -1) (c := (d : ℤ))
          (by omega) (by exact_mod_cast (Nat.zero_le d))
        simpa [Int.mul_comm] using! h
      have hle : (ρ : ℤ) ≤ (r : ℤ) + (d : ℤ) * (-1) := by rw [hr]; linarith
      linarith
    · exact hpos
  set j := ((w : ℤ) + z).natAbs with hj
  have hj' : (j : ℤ) = (w : ℤ) + z := by
    rw [hj]
    exact Int.natAbs_of_nonneg hz'
  have hr2 : (ρ : ℤ) = (r : ℤ) + (d : ℤ) * (j : ℤ) := by
    rw [hr, hj']
  refine ⟨j, ?_⟩
  have hfinal : (ρ : ℤ) = ((r + d * j : ℕ) : ℤ) := by
    rw [hr2, Int.natCast_add, Int.natCast_mul]
  exact_mod_cast hfinal

/-- Computes the size of a nonempty prime-power candidate set as the prime raised to the common
valuation. -/
theorem dlogPrimePowerCandidates_card (ℓ α : ℕ) (hℓ : ℓ.Prime)
    {t m : ℕ} (rec : DlogSampleRecord m t)
    (hne : (dlogPrimePowerCandidates ℓ α rec).Nonempty) :
    (dlogPrimePowerCandidates ℓ α rec).card = ℓ ^ dlogCommonValuation ℓ α rec := by
  obtain ⟨ρ₀, hρ₀⟩ := hne
  have hρ₀lt : ρ₀ < ℓ ^ α := Finset.mem_range.mp (Finset.mem_filter.mp hρ₀).1
  have hk : dlogCommonValuation ℓ α rec ≤ α := dlogCommonValuation_le ℓ α rec
  have hℓpos : 0 < ℓ := hℓ.pos
  set d := ℓ ^ (α - dlogCommonValuation ℓ α rec) with hd
  have hdpos : 0 < d := by
    rw [hd]
    positivity
  have hdn : d ∣ ℓ ^ α := by
    rw [hd]
    refine ⟨ℓ ^ (α - (α - dlogCommonValuation ℓ α rec)), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  have hq : (ℓ ^ α) / d = ℓ ^ dlogCommonValuation ℓ α rec := by
    have h1 : d * ((ℓ ^ α) / d) = ℓ ^ α := Nat.mul_div_cancel' hdn
    have h2 : ℓ ^ α = d * ℓ ^ dlogCommonValuation ℓ α rec := by
      rw [hd, ← pow_add]
      congr 1
      omega
    have h3 : d * ((ℓ ^ α) / d) = d * ℓ ^ dlogCommonValuation ℓ α rec := by rw [h1, h2]
    exact Nat.mul_left_cancel (by rw [hd]; positivity) h3
  set r := ρ₀ % d with hr
  have hrlt : r < d := Nat.mod_lt _ hdpos
  have hrw : ρ₀ = r + d * (ρ₀ / d) := by
    have h := Nat.mod_add_div ρ₀ d
    rw [← hr] at h
    exact h.symm

  have hdc : ∀ i, (ℓ ^ α : ℤ) ∣ (d : ℤ) * rec.cprime i := by
    intro i
    obtain ⟨w, hw⟩ := dlogCommonValuation_dvd ℓ α rec hℓ i
    have hmul : d * (rec.cprime i).natAbs = ℓ ^ α * w := by
      rw [hd, hw]
      calc ℓ ^ (α - dlogCommonValuation ℓ α rec) * (ℓ ^ dlogCommonValuation ℓ α rec * w)
          = (ℓ ^ (α - dlogCommonValuation ℓ α rec) * ℓ ^ dlogCommonValuation ℓ α rec) * w := by ring
        _ = ℓ ^ ((α - dlogCommonValuation ℓ α rec) + dlogCommonValuation ℓ α rec) * w := by
          rw [← pow_add]
        _ = ℓ ^ α * w := by
          have heq : (α - dlogCommonValuation ℓ α rec) + dlogCommonValuation ℓ α rec = α := by
            omega
          rw [heq]
    have hshow : ((ℓ ^ α : ℤ)).natAbs ∣ ((d : ℤ)).natAbs * (rec.cprime i).natAbs := by
      have h1 : ((ℓ ^ α : ℤ)).natAbs = ℓ ^ α := by simp
      have h2 : ((d : ℤ)).natAbs = d := by simp
      rw [h1, h2, hmul]
      exact ⟨w, by ring⟩
    exact (dlogIntDvd_iff (n := (ℓ ^ α : ℤ)) (a := (d : ℤ)) (b := rec.cprime i)).2 hshow

  have hbound : ∀ j : ℕ, j < (ℓ ^ α) / d → r + d * j < ℓ ^ α := by
    intro j hj
    have h3 : d * ((ℓ ^ α) / d) = ℓ ^ α := Nat.mul_div_cancel' hdn
    have hj1 : j + 1 ≤ (ℓ ^ α) / d := by omega
    have hle : d * j + d ≤ d * ((ℓ ^ α) / d) := by
      have h := Nat.mul_le_mul_left d hj1
      simpa [Nat.mul_add] using! h
    rw [h3] at hle
    omega
  have hchar : ∀ ρ : ℕ, ρ < ℓ ^ α →
      (ρ ∈ dlogPrimePowerCandidates ℓ α rec ↔
        ∃ j : ℕ, j < (ℓ ^ α) / d ∧ ρ = r + d * j) := by
    intro ρ hρ
    constructor
    · intro hmem
      have hcond := (dlogPrimePowerCandidates_iff_diff ℓ α rec hρ₀).mp hmem
      have hdiv : (d : ℤ) ∣ (ρ : ℤ) - (ρ₀ : ℤ) := by
        rw [hd]
        exact dlogDifference_dvd ℓ α hℓ rec hcond.2
      obtain ⟨j, hj⟩ := dlogDifference_eq_progression d ρ ρ₀ r (ρ₀ / d) hdpos hrlt hdiv hrw
      refine ⟨j, ?_, hj⟩
      have h3 : d * ((ℓ ^ α) / d) = ℓ ^ α := Nat.mul_div_cancel' hdn
      have hsub : d * j = ρ - r := by
        rw [hj]
        exact (Nat.add_sub_cancel_left r (d * j)).symm
      have hlt : d * j < d * ((ℓ ^ α) / d) := by omega
      have hlt' : j * d < ((ℓ ^ α) / d) * d := by
        calc j * d = d * j := Nat.mul_comm _ _
          _ < d * ((ℓ ^ α) / d) := hlt
          _ = ((ℓ ^ α) / d) * d := Nat.mul_comm _ _
      exact (Nat.mul_lt_mul_right hdpos).mp hlt'
    · rintro ⟨j, hj, hρeq⟩
      subst hρeq
      refine (dlogPrimePowerCandidates_iff_diff ℓ α rec hρ₀).mpr ⟨hbound j hj, ?_⟩
      intro i
      have hrw' : (ρ₀ : ℤ) = (r : ℤ) + (d : ℤ) * ((ρ₀ / d : ℕ) : ℤ) := by
        have h := Nat.mod_add_div ρ₀ d
        rw [← hr] at h
        calc
          (ρ₀ : ℤ) = ((r + d * (ρ₀ / d) : ℕ) : ℤ) := by exact_mod_cast h.symm
          _ = (r : ℤ) + (d : ℤ) * ((ρ₀ / d : ℕ) : ℤ) := by
            rw [Int.natCast_add, Int.natCast_mul]
      have hsub : ((r + d * j : ℕ) : ℤ) - (ρ₀ : ℤ)
          = (d : ℤ) * (((j : ℕ) : ℤ) - ((ρ₀ / d : ℕ) : ℤ)) := by
        have h1 : ((r + d * j : ℕ) : ℤ) = (r : ℤ) + (d : ℤ) * ((j : ℕ) : ℤ) := by
          rw [Int.natCast_add, Int.natCast_mul]
        rw [h1, hrw']
        ring
      obtain ⟨k, hk⟩ := hdc i
      refine ⟨k * (((j : ℕ) : ℤ) - ((ρ₀ / d : ℕ) : ℤ)), ?_⟩
      rw [hsub]
      have hre : (d : ℤ) * (((j : ℕ) : ℤ) - ((ρ₀ / d : ℕ) : ℤ)) * rec.cprime i
          = ((d : ℤ) * rec.cprime i) * (((j : ℕ) : ℤ) - ((ρ₀ / d : ℕ) : ℤ)) := by ring
      rw [hre, hk]
      ring

  have hcard' : (Finset.range ((ℓ ^ α) / d)).card
      = (dlogPrimePowerCandidates ℓ α rec).card := by
    apply Finset.card_bij (s := Finset.range ((ℓ ^ α) / d))
      (t := dlogPrimePowerCandidates ℓ α rec) (fun j _ => r + d * j)
    · intro j hj
      have hjlt : j < (ℓ ^ α) / d := Finset.mem_range.mp hj
      exact (hchar (r + d * j) (hbound j hjlt)).mpr ⟨j, hjlt, rfl⟩
    · intro j hj j' hj' heq
      have hcancel : d * j = d * j' := by omega
      exact Nat.mul_left_cancel hdpos hcancel
    · intro ρ hρ
      obtain ⟨j, hj, hρeq⟩ :=
        (hchar ρ (Finset.mem_range.mp (Finset.mem_filter.mp hρ).1)).mp hρ
      exact ⟨j, Finset.mem_range.mpr hj, hρeq.symm⟩
  have hcard : (dlogPrimePowerCandidates ℓ α rec).card = (ℓ ^ α) / d := by
    rw [← hcard', Finset.card_range]
  rw [hcard, hq]

/-- Computes the size of a nonempty prime candidate set as a power determined by the common
valuation. -/
theorem dlogPrimeCandidates_card_eq_pow (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m)
    (hne : (dlogPrimeCandidates m rec ℓ).Nonempty) :
    (dlogPrimeCandidates m rec ℓ).card = ℓ ^ dlogCommonValuation ℓ (m.factorization ℓ) rec := by
  have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hα : 0 < m.factorization ℓ := dlogFactorization_pos m ℓ hℓ
  have hcard : (dlogPrimePowerCandidates ℓ (m.factorization ℓ) rec).card
      = ℓ ^ dlogCommonValuation ℓ (m.factorization ℓ) rec := by
    refine dlogPrimePowerCandidates_card ℓ (m.factorization ℓ) hprime rec ?_
    rw [← dlogPrimeCandidates_eq_prime_power]
    exact hne
  rw [dlogPrimeCandidates_eq_prime_power]
  exact hcard

/-- Shows that a nonempty prime candidate set is a singleton when some multiplier is not
divisible by the prime. -/
theorem dlogPrimeCandidates_card_eq_one_of_coprime (m : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) (i : Fin t)
    (hc : ¬ ℓ ∣ (rec.cprime i).natAbs)
    (hne : (dlogPrimeCandidates m rec ℓ).Nonempty) :
    (dlogPrimeCandidates m rec ℓ).card = 1 := by
  have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hα : 0 < m.factorization ℓ := dlogFactorization_pos m ℓ hℓ
  have hcne : (rec.cprime i).natAbs ≠ 0 := by
    intro hz
    rw [hz] at hc
    exact hc (Nat.dvd_zero _)
  have hcfac : (rec.cprime i).natAbs.factorization ℓ = 0 := by
    have h1 : ¬ (1 ≤ (rec.cprime i).natAbs.factorization ℓ) := by
      intro hcon
      exact hc ((Nat.Prime.dvd_iff_one_le_factorization hprime hcne).mpr hcon)
    omega
  have hG : dlogMultiplierGcd rec ∣ (rec.cprime i).natAbs :=
    Finset.gcd_dvd (Finset.mem_univ i)
  have hGne : dlogMultiplierGcd rec ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := hG
    rw [h0, zero_mul] at hk
    rw [hk] at hc
    exact hc (Nat.dvd_zero _)
  have hGfac : (dlogMultiplierGcd rec).factorization ℓ = 0 := by
    have h2 : ℓ ^ (dlogMultiplierGcd rec).factorization ℓ ∣ dlogMultiplierGcd rec := by
      rw [Nat.Prime.pow_dvd_iff_le_factorization hprime hGne]
    have h3 : (dlogMultiplierGcd rec).factorization ℓ
        ≤ (rec.cprime i).natAbs.factorization ℓ := by
      have h2' : ℓ ^ (dlogMultiplierGcd rec).factorization ℓ ∣ (rec.cprime i).natAbs :=
        h2.trans hG
      exact (Nat.Prime.pow_dvd_iff_le_factorization hprime hcne).mp h2'
    omega
  have hle : (dlogMultiplierGcd rec).factorization ℓ ≤ m.factorization ℓ := by
    rw [hGfac]
    omega
  have hle0 : (0 : ℕ) ≤ m.factorization ℓ := by omega
  have hk : dlogCommonValuation ℓ (m.factorization ℓ) rec = 0 := by
    rw [dlogCommonValuation_eq, ite_eq_right hGne, hGfac]
    exact Nat.min_eq_right hle0
  rw [dlogPrimeCandidates_card_eq_pow m rec ℓ hℓ hne, hk]
  simp

/-- Computes the full prime-power candidate count when all sample multipliers are zero. -/
theorem dlogPrimeCandidates_card_eq_pow_of_zero (m : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m)
    (hz : ∀ i, rec.cprime i = 0)
    (hne : (dlogPrimeCandidates m rec ℓ).Nonempty) :
    (dlogPrimeCandidates m rec ℓ).card = ℓ ^ (m.factorization ℓ) := by
  have hα : 0 < m.factorization ℓ := dlogFactorization_pos m ℓ hℓ
  have hne' : (dlogPrimePowerCandidates ℓ (m.factorization ℓ) rec).Nonempty := by
    rw [← dlogPrimeCandidates_eq_prime_power]
    exact hne
  obtain ⟨ρ₀, hρ₀⟩ := hne'
  have hdiv : ∀ i, (ℓ ^ m.factorization ℓ : ℤ) ∣ rec.dprime i := by
    intro i
    have h1 := (Finset.mem_filter.mp hρ₀).2 i
    have h2 : (ℓ ^ m.factorization ℓ : ℤ) ∣
        (rec.dprime i + (ρ₀ : ℤ) * rec.cprime i) := Int.modEq_zero_iff_dvd.mp h1
    rw [hz i] at h2
    convert! h2 using 1
    ring
  have heq : dlogPrimePowerCandidates ℓ (m.factorization ℓ) rec
      = Finset.range (ℓ ^ m.factorization ℓ) := by
    ext ρ
    constructor
    · intro hρ
      exact (Finset.mem_filter.mp hρ).1
    · intro hρ
      refine Finset.mem_filter.mpr ⟨hρ, ?_⟩
      intro i
      have h1 : rec.dprime i + (ρ : ℤ) * rec.cprime i = rec.dprime i := by
        rw [hz i]
        ring
      rw [h1]
      exact Int.modEq_zero_iff_dvd.mpr (hdiv i)
  rw [dlogPrimeCandidates_eq_prime_power, heq, Finset.card_range]

/-- Expresses the enumeration cost as a product of prime powers determined by common valuations. -/
theorem dlogEnumerationCost_eq_pow (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (hne : ∀ ℓ ∈ dlogBasePrimes m, (dlogPrimeCandidates m rec ℓ).Nonempty) :
    dlogEnumerationCost m rec =
      ∏ ℓ ∈ dlogBasePrimes m, ℓ ^ dlogCommonValuation ℓ (m.factorization ℓ) rec := by
  unfold dlogEnumerationCost
  rw [Finset.prod_congr rfl]
  intro ℓ hℓ
  rw [dlogPrimeCandidates_card_eq_pow m rec ℓ hℓ (hne ℓ hℓ)]

/-- Expresses the small-prime enumeration cost as a product of prime powers determined by common
valuations. -/
theorem dlogSmallEnumerationCost_eq_pow (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (hne : ∀ ℓ ∈ dlogSmallBasePrimes m, (dlogPrimeCandidates m rec ℓ).Nonempty) :
    dlogSmallEnumerationCost m rec =
      ∏ ℓ ∈ dlogSmallBasePrimes m, ℓ ^ dlogCommonValuation ℓ (m.factorization ℓ) rec := by
  unfold dlogSmallEnumerationCost
  rw [Finset.prod_congr rfl]
  intro ℓ hℓ
  have hℓ' : ℓ ∈ dlogBasePrimes m := (Finset.mem_filter.mp hℓ).1
  rw [dlogPrimeCandidates_card_eq_pow m rec ℓ hℓ' (hne ℓ hℓ)]

/-- Decomposes the base primes into the union of the small and large base primes. -/
theorem dlogBasePrimes_eq_small_union_large (m : ℕ) :
    dlogBasePrimes m = dlogSmallBasePrimes m ∪ dlogLargeBasePrimes m := by
  apply Finset.ext
  intro ℓ
  simp only [dlogSmallBasePrimes, dlogLargeBasePrimes, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · intro h
    by_cases h1 : ℓ ≤ 18
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h, by omega⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

/-- Shows that the small and large base prime sets are disjoint. -/
theorem dlogSmallLarge_disjoint (m : ℕ) :
    Disjoint (dlogSmallBasePrimes m) (dlogLargeBasePrimes m) := by
  refine Finset.disjoint_right.mpr ?_
  intro ℓ hℓ' hℓ
  have hmem : ℓ ∈ dlogBasePrimes m ∧ 18 < ℓ := by
    rw [dlogLargeBasePrimes] at hℓ'
    exact Finset.mem_filter.mp hℓ'
  have hle : ℓ ≤ 18 := by
    have h' : ℓ ∈ (dlogBasePrimes m).filter (fun ℓ => ℓ ≤ 18) := hℓ
    exact (Finset.mem_filter.mp h').2
  omega

/-- Shows that a nonempty prime candidate set has one element when some integer sample
multiplier is not divisible by the prime. -/
theorem dlogPrimeCandidates_card_eq_one_of_not_dvd (m : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (ℓ : ℕ) (hℓ : ℓ ∈ dlogBasePrimes m) (i : Fin t)
    (hc : ¬ ((ℓ : ℤ) ∣ rec.cprime i))
    (hne : (dlogPrimeCandidates m rec ℓ).Nonempty) :
    (dlogPrimeCandidates m rec ℓ).card = 1 := by
  refine dlogPrimeCandidates_card_eq_one_of_coprime m rec ℓ hℓ i ?_ hne
  intro h
  exact hc (Int.natCast_dvd.mpr h)

/-- Shows that full pinning reduces the enumeration cost to one when all local candidate sets
are nonempty. -/
theorem dlogEnumerationCost_eq_one_of_pinned (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (hp : dlogPinningHypothesis m rec)
    (hne : ∀ ℓ ∈ dlogBasePrimes m, (dlogPrimeCandidates m rec ℓ).Nonempty) :
    dlogEnumerationCost m rec = 1 := by
  have hcard : ∀ ℓ ∈ dlogBasePrimes m, (dlogPrimeCandidates m rec ℓ).card = 1 := by
    intro ℓ hℓ
    obtain ⟨i, hi⟩ := hp ℓ hℓ
    exact dlogPrimeCandidates_card_eq_one_of_not_dvd m rec ℓ hℓ i hi (hne ℓ hℓ)
  unfold dlogEnumerationCost
  exact Finset.prod_eq_one hcard

/-- Shows that small-prime pinning reduces the small-prime enumeration cost to one. -/
theorem dlogSmallEnumerationCost_eq_one_of_pinned (m : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (hp : dlogSmallPinningHypothesis m rec)
    (hne : ∀ ℓ ∈ dlogSmallBasePrimes m, (dlogPrimeCandidates m rec ℓ).Nonempty) :
    dlogSmallEnumerationCost m rec = 1 := by
  have hcard : ∀ ℓ ∈ dlogSmallBasePrimes m, (dlogPrimeCandidates m rec ℓ).card = 1 := by
    intro ℓ hℓ
    obtain ⟨i, hi⟩ := hp ℓ hℓ
    have hmem : ℓ ∈ dlogBasePrimes m := (Finset.mem_filter.mp hℓ).1
    exact dlogPrimeCandidates_card_eq_one_of_not_dvd m rec ℓ hmem i hi (hne ℓ hℓ)
  unfold dlogSmallEnumerationCost
  exact Finset.prod_eq_one hcard

/-- Shows that large-prime pinning reduces the total enumeration cost to the small-prime cost. -/
theorem dlogEnumerationCost_eq_small_of_large_pinned (m : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (hp : dlogLargePinningHypothesis m rec)
    (hne : ∀ ℓ ∈ dlogBasePrimes m, (dlogPrimeCandidates m rec ℓ).Nonempty) :
    dlogEnumerationCost m rec = dlogSmallEnumerationCost m rec := by
  have hcard : ∀ ℓ ∈ dlogLargeBasePrimes m, (dlogPrimeCandidates m rec ℓ).card = 1 := by
    intro ℓ hℓ
    obtain ⟨i, hi⟩ := hp ℓ hℓ
    have hmem : ℓ ∈ dlogBasePrimes m := (Finset.mem_filter.mp hℓ).1
    exact dlogPrimeCandidates_card_eq_one_of_not_dvd m rec ℓ hmem i hi (hne ℓ hmem)
  have hlarge : ∏ ℓ ∈ dlogLargeBasePrimes m, (dlogPrimeCandidates m rec ℓ).card = 1 :=
    Finset.prod_eq_one hcard
  unfold dlogEnumerationCost dlogSmallEnumerationCost
  rw [dlogBasePrimes_eq_small_union_large]
  rw [Finset.prod_union (dlogSmallLarge_disjoint m)]
  rw [hlarge, mul_one]

/-- Shows that the CRT candidate list is exactly the true exponent singleton under congruence
and pinning assumptions. -/
theorem dlogCrtCandidateList_eq_singleton_of_pinned (m : ℕ) {t : ℕ}
    (rec : DlogSampleRecord m t) (r : ℕ) (hr : r < m)
    (hcong : dlogSampleCongruent m (r : ℤ) rec)
    (hp : dlogPinningHypothesis m rec)
    (hne : ∀ ℓ ∈ dlogBasePrimes m, (dlogPrimeCandidates m rec ℓ).Nonempty) :
    dlogCrtCandidateList m rec (fun _ => 0) = [r] := by
  have hm : m ≠ 0 := by omega
  have hlen : (dlogCrtCandidateList m rec (fun _ => 0)).length = 1 := by
    rw [dlogCrtCandidateList_length]
    exact dlogEnumerationCost_eq_one_of_pinned m rec hp hne
  have hmerge : dlogCrtMerge m (fun ℓ => r % dlogMaxPrimePower m ℓ) = r := by
    have hspec := dlogCrtMerge_spec m hm (fun ℓ => r % dlogMaxPrimePower m ℓ)
    refine dlogCrtMerge_unique m hm hspec.1 hr ?_
    intro ℓ hℓ
    have h1 := hspec.2 ℓ hℓ
    have h2 : Nat.ModEq (dlogMaxPrimePower m ℓ) (r % dlogMaxPrimePower m ℓ) r :=
      Nat.mod_modEq r _
    exact h1.trans h2
  have hmem : r ∈ dlogCrtCandidateList m rec (fun _ => 0) := by
    have h := dlogCrtCandidateList_contains_seed m r rec hm hcong
    rw [hmerge] at h
    exact h
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  have hmem' : r ∈ [a] := by rw [← ha]; exact hmem
  have hra : r = a := by simpa using! hmem'
  rw [ha, hra]

/-- Bounds the combined readout and modular exponentiation gate count by the total gate budget. -/
theorem dlogTotalGateCount_le (p x q : ℕ) (enc : DlogGroupEncoding p x q) (hp : 2 ≤ p) :
    GateCount (localProgramCircuit (dlogReadoutProgram (enc.pBits + 1)))
      + dlogModexpGateCount (Nat.log2 p + 1) (p - 1)
      ≤ dlogTotalGateCount p x q enc := by
  have h1 := dlogReadoutGateCount_le p x q enc
  have h2 := dlogModexpGateCount_cube_le p hp
  unfold dlogTotalGateCount
  omega

/-- Bounds the readout and modular multiplication space requirement by the total space budget. -/
theorem dlogTotalSpaceCount_le (p x q : ℕ) (enc : DlogGroupEncoding p x q) :
    3 * (enc.pBits + 1) + dlogModMulSpaceCount (Nat.log2 p + 1)
      ≤ dlogTotalSpaceCount p x q enc := by
  simp [dlogModMulSpaceCount, dlogTotalSpaceCount]

/-- Bounds the size of a linear congruence fiber by the gcd of its coefficient and modulus. -/
theorem dlogCongrFiber_card_le (A q v : ℕ) (hq : 0 < q) :
    ((Finset.univ : Finset (Fin q)).filter
      fun i : Fin q => A * i.val ≡ v [MOD q]).card ≤ Nat.gcd A q := by
  classical
  have hg0 : 0 < Nat.gcd A q := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left A hq
  have hgq : Nat.gcd A q ∣ q := Nat.gcd_dvd_right A q
  have hgdvd : Nat.gcd A q ∣ A := Nat.gcd_dvd_left A q
  have hqeq : Nat.gcd A q * (q / Nat.gcd A q) = q := Nat.mul_div_cancel' hgq
  have hAeq : Nat.gcd A q * (A / Nat.gcd A q) = A := Nat.mul_div_cancel' hgdvd
  have hle : Nat.gcd A q ≤ q := Nat.le_of_dvd hq hgq
  have hqpos : 0 < q / Nat.gcd A q := Nat.div_pos hle hg0
  have hcop : Nat.Coprime (q / Nat.gcd A q) (A / Nat.gcd A q) := by
    have h := Nat.coprime_div_gcd_div_gcd (m := q) (n := A) (by rw [Nat.gcd_comm]; exact hg0)
    simpa only [Nat.gcd_comm] using! h

  have hmulmod (g x y z : ℕ) (hg : 0 < g) (hz : g * z = y) :
      (g * x) % y = g * (x % z) := by
    subst hz
    exact Nat.mul_mod_mul_left g x z

  have hdiff : ∀ i j : Fin q, A * i.val ≡ v [MOD q] → A * j.val ≡ v [MOD q] →
      i.val % (q / Nat.gcd A q) = j.val % (q / Nat.gcd A q) := by
    intro i j hi hj
    have hmod : (A * i.val) % q = (A * j.val) % q := hi.trans hj.symm
    have hmul : A * i.val = Nat.gcd A q * ((A / Nat.gcd A q) * i.val) := by
      calc A * i.val = (Nat.gcd A q * (A / Nat.gcd A q)) * i.val := by rw [hAeq]
        _ = Nat.gcd A q * ((A / Nat.gcd A q) * i.val) := by ring
    have hmulj : A * j.val = Nat.gcd A q * ((A / Nat.gcd A q) * j.val) := by
      calc A * j.val = (Nat.gcd A q * (A / Nat.gcd A q)) * j.val := by rw [hAeq]
        _ = Nat.gcd A q * ((A / Nat.gcd A q) * j.val) := by ring
    rw [hmul, hmulj] at hmod
    have hmod' : (Nat.gcd A q * ((A / Nat.gcd A q) * i.val)) % q
        = Nat.gcd A q * ((A / Nat.gcd A q) * i.val % (q / Nat.gcd A q)) :=
      hmulmod (Nat.gcd A q) ((A / Nat.gcd A q) * i.val) q (q / Nat.gcd A q) hg0 hqeq
    have hmod'' : (Nat.gcd A q * ((A / Nat.gcd A q) * j.val)) % q
        = Nat.gcd A q * ((A / Nat.gcd A q) * j.val % (q / Nat.gcd A q)) :=
      hmulmod (Nat.gcd A q) ((A / Nat.gcd A q) * j.val) q (q / Nat.gcd A q) hg0 hqeq
    rw [hmod', hmod''] at hmod
    have hmod' : (A / Nat.gcd A q) * i.val % (q / Nat.gcd A q) * Nat.gcd A q
        = (A / Nat.gcd A q) * j.val % (q / Nat.gcd A q) * Nat.gcd A q := by
      simpa [Nat.mul_comm] using! hmod
    have hcancel : (A / Nat.gcd A q) * i.val % (q / Nat.gcd A q)
        = (A / Nat.gcd A q) * j.val % (q / Nat.gcd A q) :=
      Nat.mul_right_cancel hg0 hmod'
    have h5 : i.val ≡ j.val [MOD q / Nat.gcd A q / Nat.gcd (q / Nat.gcd A q)
      (A / Nat.gcd A q)] :=
      Nat.ModEq.cancel_right_div_gcd hqpos (by
        simpa [Nat.mul_comm] using! hcancel)
    have h6 : Nat.gcd (q / Nat.gcd A q) (A / Nat.gcd A q) = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hcop
    rw [h6, Nat.div_one] at h5
    exact h5
  have hlt : ∀ i : Fin q, i.val / (q / Nat.gcd A q) < Nat.gcd A q := by
    intro i
    rw [Nat.div_lt_iff_lt_mul hqpos, hqeq]
    exact i.isLt
  let S : Finset (Fin q) :=
    (Finset.univ : Finset (Fin q)).filter fun i : Fin q => A * i.val ≡ v [MOD q]
  have hSmem : ∀ i : Fin q, i ∈ S ↔ A * i.val ≡ v [MOD q] := by
    intro i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hinj : ∀ i ∈ S, ∀ j ∈ S,
      i.val / (q / Nat.gcd A q) = j.val / (q / Nat.gcd A q) → i = j := by
    intro i hi j hj hij
    have h1 : A * i.val ≡ v [MOD q] := (hSmem i).mp hi
    have h2 : A * j.val ≡ v [MOD q] := (hSmem j).mp hj
    have hmod : i.val % (q / Nat.gcd A q) = j.val % (q / Nat.gcd A q) := hdiff i j h1 h2
    have h1' := Nat.div_add_mod i.val (q / Nat.gcd A q)
    have h2' := Nat.div_add_mod j.val (q / Nat.gcd A q)
    rw [hij] at h1'
    have h3 : i.val = j.val := by omega
    exact Fin.ext h3
  let f : Fin q → Fin (Nat.gcd A q) :=
    fun i => ⟨i.val / (q / Nat.gcd A q), by exact hlt i⟩
  have hinjOn : Set.InjOn f ↑S := by
    intro i hi j hj h
    exact hinj i hi j hj (congrArg Fin.val h)
  have himg : S.image f ⊆ (Finset.univ : Finset (Fin (Nat.gcd A q))) := by
    intro y hy
    exact Finset.mem_univ _
  have hcard' : S.card = (S.image f).card := (Finset.card_image_of_injOn hinjOn).symm
  have hle : (S.image f).card ≤ Finset.card (Finset.univ : Finset (Fin (Nat.gcd A q))) :=
    Finset.card_le_card himg
  have hcard : S.card ≤ Finset.card (Finset.univ : Finset (Fin (Nat.gcd A q))) := hcard' ▸ hle
  simpa [S] using! hcard

/-- Shows that a linear congruence fiber is empty when the gcd does not divide the target
residue. -/
theorem dlogCongrFiber_eq_zero_of_not_dvd (A q v : ℕ) (_hq : 0 < q)
    (h : ¬ Nat.gcd A q ∣ v) :
    ((Finset.univ : Finset (Fin q)).filter
      fun i : Fin q => A * i.val ≡ v [MOD q]).card = 0 := by
  classical
  have hne : ∀ i : Fin q, ¬ (A * i.val ≡ v [MOD q]) := by
    intro i hi
    have hdvd : (q : ℤ) ∣ (v : ℤ) - (A * i.val : ℤ) := (Nat.modEq_iff_dvd).mp hi
    have hgA : (Nat.gcd A q : ℤ) ∣ (A * i.val : ℤ) :=
      (Int.natCast_dvd_natCast).mpr (Nat.dvd_trans (Nat.gcd_dvd_left A q)
        (Nat.dvd_mul_right A i.val))
    have hgq : (Nat.gcd A q : ℤ) ∣ (q : ℤ) :=
      (Int.natCast_dvd_natCast).mpr (Nat.gcd_dvd_right A q)
    have hgc : (Nat.gcd A q : ℤ) ∣ (v : ℤ) - (A * i.val : ℤ) := Int.dvd_trans hgq hdvd
    have hgv : (Nat.gcd A q : ℤ) ∣ (v : ℤ) := by
      have heq : (v : ℤ) = (A * i.val : ℤ) + ((v : ℤ) - (A * i.val : ℤ)) := by ring
      rw [heq]
      exact Int.dvd_add hgA hgc
    exact h ((Int.natCast_dvd_natCast).mp hgv)
  rw [Finset.card_eq_zero]
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  exact hne x ((Finset.mem_filter.mp hx).2)

/-- Converts an integer congruence into an equality of natural modular remainders. -/
theorem dlogCongr_eq_mod (A q : ℕ) (hq : 0 < q) (v : ℤ) (i : Fin q)
    (h : (A : ℤ) * (i : ℤ) ≡ v [ZMOD q]) :
    A * i.val % q = (v % (q : ℤ)).toNat := by
  have h1 : (A : ℤ) * (i : ℤ) % (q : ℤ) = v % (q : ℤ) := h
  have h2 : (A : ℤ) * (i : ℤ) = (A * i.val : ℤ) := by
    ring
  rw [h2] at h1
  have h3 : (A * i.val : ℤ) % (q : ℤ) = ((A * i.val) % q : ℤ) := (Int.natCast_emod _ _).symm
  rw [h3] at h1
  have h4 : (0 : ℤ) ≤ v % (q : ℤ) :=
    @Int.emod_nonneg v (q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hq))
  have h6 : (v % (q : ℤ)) = ((v % (q : ℤ)).toNat : ℤ) := (Int.toNat_of_nonneg h4).symm
  have h7 : ((A * i.val) % q : ℤ) = ((v % (q : ℤ)).toNat : ℤ) := h1.trans h6
  exact Int.ofNat_inj.mp h7

/-- Bounds the number of divisible reads with a fixed residue by the read fiber divisor. -/
theorem dlogDivisibleReadCount_le_of_residue
    (m q w : ℕ) (hm : 0 < m) (hq : 0 < q) (hw : 2 ≤ w) (hwm : w ∣ m)
    (s : ℤ) (reads : Fin q → DlogResidueRead)
    (hrel : ∀ i, DlogReadRelation m q i (reads i)) :
    ((Finset.univ : Finset (Fin q)).filter fun i : Fin q =>
        (reads i).residue = s ∧ (w : ℤ) ∣ (reads i).cprime).card
      ≤ dlogReadFiberDivisor m q w := by
  classical
  set gA := dlogReadFiberDivisor m q w with hgAdef
  set A := m / w with hAdef
  have hgA0 : 0 < gA := by
    unfold gA dlogReadFiberDivisor
    have hmw : 0 < m / w := Nat.div_pos (Nat.le_of_dvd hm hwm) (by omega)
    exact Nat.gcd_pos_of_pos_left q hmw
  have hw0 : (w : ℤ) ≠ 0 := by omega
  have hwmZ : (w : ℤ) ∣ (m : ℤ) := (Int.natCast_dvd_natCast).mpr hwm
  have hmA : (m : ℤ) = (w : ℤ) * (A : ℤ) := by
    have h : m = w * (m / w) := (Nat.mul_div_cancel' hwm).symm
    have h2 : (m : ℤ) = ((w * (m / w) : ℕ) : ℤ) := by exact_mod_cast h
    have h3 : ((w * (m / w) : ℕ) : ℤ) = (w : ℤ) * ((m / w : ℕ) : ℤ) := by
      exact_mod_cast rfl
    rw [h2, h3, hAdef]
  let T : Finset (Fin q) := (Finset.univ : Finset (Fin q)).filter fun i : Fin q =>
      (reads i).residue = s ∧ (w : ℤ) ∣ (reads i).cprime
  by_cases hne : T.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hne
    obtain ⟨hi0res, hi0div⟩ := (Finset.mem_filter.mp hi₀).2

    have hmi₀ : (w : ℤ) ∣ (m : ℤ) * (i₀ : ℤ) :=
      Int.dvd_mul_of_dvd_left (c := (i₀ : ℤ)) hwmZ
    have hqc' : (w : ℤ) ∣ (reads i₀).cprime * (q : ℤ) :=
      Int.dvd_mul_of_dvd_left (c := (q : ℤ)) hi0div
    have hdiff : s = (m : ℤ) * (i₀ : ℤ) - (reads i₀).cprime * (q : ℤ) := by
      have h := hrel i₀
      unfold DlogReadRelation at h
      rw [hi0res] at h
      rw [h]
      ring
    have hsvD : (w : ℤ) ∣ s := by
      rw [hdiff]
      exact Int.dvd_sub hmi₀ hqc'
    obtain ⟨v, hv⟩ := hsvD

    have hcong : ∀ i : Fin q,
        (reads i).residue = s ∧ (w : ℤ) ∣ (reads i).cprime →
        (A : ℤ) * (i : ℤ) ≡ v [ZMOD q] := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨c'', hc''⟩ := hi2
      have hrel' := hrel i
      unfold DlogReadRelation at hrel'
      have h1 : (w : ℤ) * ((A : ℤ) * (i : ℤ)) = (w : ℤ) * ((q : ℤ) * c'' + v) := by
        rw [hi1, hv, hc'', hmA] at hrel'
        calc (w : ℤ) * ((A : ℤ) * (i : ℤ)) = (w : ℤ) * (A : ℤ) * (i : ℤ) := by ring
          _ = (q : ℤ) * ((w : ℤ) * c'') + (w : ℤ) * v := hrel'
          _ = (w : ℤ) * ((q : ℤ) * c'' + v) := by ring
      have h2 : (A : ℤ) * (i : ℤ) = (q : ℤ) * c'' + v := Int.eq_of_mul_eq_mul_left hw0 h1
      rw [Int.modEq_iff_dvd]
      exact ⟨-c'', by rw [h2]; ring⟩

    have hsub : T ⊆ ((Finset.univ : Finset (Fin q)).filter fun i : Fin q =>
        A * i.val ≡ (v % (q : ℤ)).toNat [MOD q]) := by
      intro i hi
      have hmem := Finset.mem_filter.mp hi
      have h1 := dlogCongr_eq_mod A q hq v i (hcong i hmem.2)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hlt : (v % (q : ℤ)).toNat < q := by
        have hlt' : v % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos v (by omega)
        have hnonneg : (0 : ℤ) ≤ v % (q : ℤ) :=
          @Int.emod_nonneg v (q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hq))
        rw [← Int.toNat_of_nonneg hnonneg] at hlt'
        exact_mod_cast hlt'
      show A * i.val % q = (v % (q : ℤ)).toNat % q
      rw [Nat.mod_eq_of_lt hlt]
      exact h1
    have hcard : T.card ≤ ((Finset.univ : Finset (Fin q)).filter fun i : Fin q =>
        A * i.val ≡ (v % (q : ℤ)).toNat [MOD q]).card := Finset.card_le_card hsub
    calc T.card ≤ ((Finset.univ : Finset (Fin q)).filter fun i : Fin q =>
          A * i.val ≡ (v % (q : ℤ)).toNat [MOD q]).card := hcard
      _ ≤ Nat.gcd A q := dlogCongrFiber_card_le A q _ hq
      _ = gA := by rw [hgAdef, dlogReadFiberDivisor]
  · have hcard0 : T.card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.not_nonempty_iff_eq_empty.mp ?_
      rintro ⟨x, hx⟩
      exact hne ⟨x, hx⟩
    rw [hcard0]
    exact Nat.zero_le _

/-- Shows that the residue index encoding distinguishes integers within its prescribed symmetric
range. -/
theorem dlogResidueIndexVal_injective (K : ℕ) (k k' : ℤ)
    (hk : -((K : ℤ)) ≤ k ∧ k ≤ (K : ℤ))
    (hk' : -((K : ℤ)) ≤ k' ∧ k' ≤ (K : ℤ))
    (h : dlogResidueIndexVal K k = dlogResidueIndexVal K k') : k = k' := by
  have h0 : 0 ≤ k + (K : ℤ) := by omega
  have h0' : 0 ≤ k' + (K : ℤ) := by omega
  have hcast : ((k + (K : ℤ)).toNat : ℤ) = k + (K : ℤ) := by rw [Int.toNat_of_nonneg h0]
  have hcast' : ((k' + (K : ℤ)).toNat : ℤ) = k' + (K : ℤ) := by rw [Int.toNat_of_nonneg h0']
  simp only [dlogResidueIndexVal] at h
  have hcast'' : (k + (K : ℤ)) = (k' + (K : ℤ)) := by
    have hz : ((k + (K : ℤ)).toNat : ℤ) = ((k' + (K : ℤ)).toNat : ℤ) := by
      exact_mod_cast h
    rw [hcast, hcast'] at hz
    exact hz
  omega

/-- Converts an absolute-value bound on an integer into upper and lower bounds. -/
theorem dlogNatAbs_le_bounds (k : ℤ) (K : ℕ) (hk : k.natAbs ≤ K) :
    -((K : ℤ)) ≤ k ∧ k ≤ (K : ℤ) := by
  by_cases hk0 : 0 ≤ k
  · have hcast : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hk0
    have hle : (k.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hk
    constructor <;> omega
  · have hcast : (k.natAbs : ℤ) = -k := by
      have hne : k ≠ 0 := by omega
      have hpos : 0 ≤ -k := by omega
      have h1 := Int.natAbs_neg k
      have h2 := Int.natAbs_of_nonneg hpos
      rw [← h1]
      exact h2
    have hle : (k.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hk
    constructor <;> omega

/-- Shows that the natural absolute value of a natural number cast to an integer is the original
number. -/
theorem dlog_natCast_natAbs (n : ℕ) : ((n : ℤ)).natAbs = n := by
  have h := Int.natAbs_of_nonneg (a := (n : ℤ)) (by exact_mod_cast (Nat.zero_le n))
  exact Nat.cast_injective h

/-- Derives a reduced read relation and a divisible residue when the multiplier is divisible by
`w`. -/
theorem dlogDivisibleRead_reduced (m q w : ℕ)
    (hw : 2 ≤ w) (hwm : w ∣ m) (reads : Fin q → DlogResidueRead)
    (hrel : ∀ i, DlogReadRelation m q i (reads i))
    (i : Fin q) (hdiv : (w : ℤ) ∣ (reads i).cprime) :
    ∃ v : ℤ,
      ((m / w : ℕ) : ℤ) * (i : ℤ) = (q : ℤ) * ((reads i).cprime / (w : ℤ)) + v ∧
      (reads i).residue = (w : ℤ) * v := by
  classical
  have hwmZ : (w : ℤ) ∣ (m : ℤ) := (Int.natCast_dvd_natCast).mpr hwm
  have hw0 : (w : ℤ) ≠ 0 := by omega
  have hrel' := hrel i
  unfold DlogReadRelation at hrel'

  have hmi : (w : ℤ) ∣ (m : ℤ) * (i : ℤ) := Int.dvd_mul_of_dvd_left (c := (i : ℤ)) hwmZ
  have hqc : (w : ℤ) ∣ (q : ℤ) * (reads i).cprime :=
    Int.dvd_mul_of_dvd_right hdiv
  have hws : (w : ℤ) ∣ (reads i).residue := by
    have h2 : (reads i).residue = (m : ℤ) * (i : ℤ) - (q : ℤ) * (reads i).cprime := by
      linarith [hrel']
    rw [h2]
    exact Int.dvd_sub hmi hqc

  obtain ⟨v, hv⟩ := hws
  have hcp : (reads i).cprime = (w : ℤ) * ((reads i).cprime / (w : ℤ)) := by
    simpa [Int.mul_comm] using! (Int.ediv_mul_cancel hdiv).symm

  have hmA : (m : ℤ) = (w : ℤ) * ((m / w : ℕ) : ℤ) := by
    have h : m = w * (m / w) := (Nat.mul_div_cancel' hwm).symm
    have h2 : (m : ℤ) = ((w * (m / w) : ℕ) : ℤ) := by exact_mod_cast h
    have h3 : ((w * (m / w) : ℕ) : ℤ) = (w : ℤ) * ((m / w : ℕ) : ℤ) := by
      exact_mod_cast rfl
    rw [h2, h3]

  refine ⟨v, ?_, ?_⟩
  · have h := hrel'
    rw [hmA, hcp, hv] at h
    have h2 : (w : ℤ) * (((m / w : ℕ) : ℤ) * (i : ℤ))
        = (w : ℤ) * ((q : ℤ) * ((reads i).cprime / (w : ℤ)) + v) := by
      calc (w : ℤ) * (((m / w : ℕ) : ℤ) * (i : ℤ))
          = (w : ℤ) * ((m / w : ℕ) : ℤ) * (i : ℤ) := by ring
        _ = (q : ℤ) * ((w : ℤ) * ((reads i).cprime / (w : ℤ))) + (w : ℤ) * v := h
        _ = (w : ℤ) * ((q : ℤ) * ((reads i).cprime / (w : ℤ)) + v) := by ring
    have h3 : ((m / w : ℕ) : ℤ) * (i : ℤ)
        = (q : ℤ) * ((reads i).cprime / (w : ℤ)) + v :=
      Int.eq_of_mul_eq_mul_left hw0 h2
    exact h3
  · exact hv

/-- Shows that solutions of the same linear congruence agree modulo the modulus divided by the
coefficient gcd. -/
theorem dlogCongrFiber_quot_eq (A q v : ℕ) (hq : 0 < q) (i j : Fin q)
    (hi : A * i.val ≡ v [MOD q]) (hj : A * j.val ≡ v [MOD q]) :
    i.val % (q / Nat.gcd A q) = j.val % (q / Nat.gcd A q) := by
  classical
  have hg0 : 0 < Nat.gcd A q := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left A hq
  have hgq : Nat.gcd A q ∣ q := Nat.gcd_dvd_right A q
  have hgdvd : Nat.gcd A q ∣ A := Nat.gcd_dvd_left A q
  have hqeq : Nat.gcd A q * (q / Nat.gcd A q) = q := Nat.mul_div_cancel' hgq
  have hAeq : Nat.gcd A q * (A / Nat.gcd A q) = A := Nat.mul_div_cancel' hgdvd
  have hle : Nat.gcd A q ≤ q := Nat.le_of_dvd hq hgq
  have hqpos : 0 < q / Nat.gcd A q := Nat.div_pos hle hg0
  have hcop : Nat.Coprime (q / Nat.gcd A q) (A / Nat.gcd A q) := by
    have h := Nat.coprime_div_gcd_div_gcd (m := q) (n := A) (by rw [Nat.gcd_comm]; exact hg0)
    simpa only [Nat.gcd_comm] using! h
  have hmulmod (g x y z : ℕ) (hg : 0 < g) (hz : g * z = y) :
      (g * x) % y = g * (x % z) := by
    subst hz
    exact Nat.mul_mod_mul_left g x z
  have hmod : (A * i.val) % q = (A * j.val) % q := hi.trans hj.symm
  have hmul : A * i.val = Nat.gcd A q * ((A / Nat.gcd A q) * i.val) := by
    calc A * i.val = (Nat.gcd A q * (A / Nat.gcd A q)) * i.val := by rw [hAeq]
      _ = Nat.gcd A q * ((A / Nat.gcd A q) * i.val) := by ring
  have hmulj : A * j.val = Nat.gcd A q * ((A / Nat.gcd A q) * j.val) := by
    calc A * j.val = (Nat.gcd A q * (A / Nat.gcd A q)) * j.val := by rw [hAeq]
      _ = Nat.gcd A q * ((A / Nat.gcd A q) * j.val) := by ring
  rw [hmul, hmulj] at hmod
  have hmod' : (Nat.gcd A q * ((A / Nat.gcd A q) * i.val)) % q
      = Nat.gcd A q * ((A / Nat.gcd A q) * i.val % (q / Nat.gcd A q)) :=
    hmulmod (Nat.gcd A q) ((A / Nat.gcd A q) * i.val) q (q / Nat.gcd A q) hg0 hqeq
  have hmod'' : (Nat.gcd A q * ((A / Nat.gcd A q) * j.val)) % q
      = Nat.gcd A q * ((A / Nat.gcd A q) * j.val % (q / Nat.gcd A q)) :=
    hmulmod (Nat.gcd A q) ((A / Nat.gcd A q) * j.val) q (q / Nat.gcd A q) hg0 hqeq
  rw [hmod', hmod''] at hmod
  have hmod' : (A / Nat.gcd A q) * i.val % (q / Nat.gcd A q) * Nat.gcd A q
      = (A / Nat.gcd A q) * j.val % (q / Nat.gcd A q) * Nat.gcd A q := by
    simpa [Nat.mul_comm] using! hmod
  have hcancel : (A / Nat.gcd A q) * i.val % (q / Nat.gcd A q)
      = (A / Nat.gcd A q) * j.val % (q / Nat.gcd A q) :=
    Nat.mul_right_cancel hg0 hmod'
  have h5 : i.val ≡ j.val [MOD q / Nat.gcd A q / Nat.gcd (q / Nat.gcd A q)
    (A / Nat.gcd A q)] :=
    Nat.ModEq.cancel_right_div_gcd hqpos (by
      simpa [Nat.mul_comm] using! hcancel)
  have h6 : Nat.gcd (q / Nat.gcd A q) (A / Nat.gcd A q) = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp hcop
  rw [h6, Nat.div_one] at h5
  exact h5

/-- Represents a divisible good read residue as a bounded integer multiple of the read fiber
divisor times `w`. -/
theorem dlogDivisibleRead_index (m q w : ℕ) (hm : 0 < m) (hq : 0 < q)
    (hw : 2 ≤ w) (hwm : w ∣ m) (reads : Fin q → DlogResidueRead)
    (hrel : ∀ i, DlogReadRelation m q i (reads i))
    (i : Fin q) (hgood : DlogGoodRead q (reads i)) (hdiv : (w : ℤ) ∣ (reads i).cprime) :
    ∃ k : ℤ,
      (reads i).residue / ((dlogReadFiberDivisor m q w : ℤ) * (w : ℤ)) = k ∧
      (reads i).residue = k * ((dlogReadFiberDivisor m q w : ℤ) * (w : ℤ)) ∧
      -(((q / 12) / (w * dlogReadFiberDivisor m q w) : ℕ) : ℤ) ≤ k ∧
      k ≤ ((q / 12) / (w * dlogReadFiberDivisor m q w) : ℕ) := by
  classical
  set gA := dlogReadFiberDivisor m q w with hgAdef
  set A := m / w with hAdef
  set K := (q / 12) / (w * gA) with hKdef
  have hgAeq : Nat.gcd A q = gA := by
    rw [hAdef, hgAdef]
    rfl
  have hgA0 : 0 < gA := by
    rw [← hgAeq]
    have hmw : 0 < m / w := Nat.div_pos (Nat.le_of_dvd hm hwm) (by omega)
    exact Nat.gcd_pos_of_pos_left q hmw

  obtain ⟨v, hvrel, hvs⟩ := dlogDivisibleRead_reduced m q w hw hwm reads hrel i hdiv

  have hcong : (A : ℤ) * (i : ℤ) ≡ v [ZMOD q] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-((reads i).cprime / (w : ℤ)), ?_⟩
    rw [hAdef]
    rw [hvrel]
    ring

  have hlt : (v % (q : ℤ)).toNat < q := by
    have hlt' : v % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos v (by omega)
    have hnonneg : (0 : ℤ) ≤ v % (q : ℤ) :=
      @Int.emod_nonneg v (q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hq))
    rw [← Int.toNat_of_nonneg hnonneg] at hlt'
    exact_mod_cast hlt'
  have hnat : A * i.val ≡ (v % (q : ℤ)).toNat [MOD q] := by
    have h1 := dlogCongr_eq_mod A q hq v i hcong
    show A * i.val % q = (v % (q : ℤ)).toNat % q
    rw [Nat.mod_eq_of_lt hlt]
    exact h1

  have hgAvnat : Nat.gcd A q ∣ (v % (q : ℤ)).toNat := by
    by_contra hn
    have hz := dlogCongrFiber_eq_zero_of_not_dvd A q ((v % (q : ℤ)).toNat) hq hn
    have hmem : i ∈ (Finset.univ : Finset (Fin q)).filter fun j : Fin q =>
        A * j.val ≡ (v % (q : ℤ)).toNat [MOD q] := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnat⟩
    have hcard : 0 < ((Finset.univ : Finset (Fin q)).filter fun j : Fin q =>
        A * j.val ≡ (v % (q : ℤ)).toNat [MOD q]).card := by
      rw [Finset.card_pos]
      exact ⟨i, hmem⟩
    omega
  have hgAv : (Nat.gcd A q : ℤ) ∣ v := by
    have h1 : (Nat.gcd A q : ℤ) ∣ ((v % (q : ℤ)).toNat : ℤ) :=
      (Int.natCast_dvd_natCast).mpr hgAvnat
    have hqdiv : (q : ℤ) ∣ v - ((v % (q : ℤ)).toNat : ℤ) := by
      have hnonneg : (0 : ℤ) ≤ v % (q : ℤ) :=
        @Int.emod_nonneg v (q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hq))
      have hcast : ((v % (q : ℤ)).toNat : ℤ) = v % (q : ℤ) := by
        rw [Int.toNat_of_nonneg hnonneg]
      rw [hcast]
      have hc := Int.mul_ediv_add_emod v (q : ℤ)
      refine ⟨v / (q : ℤ), ?_⟩
      linarith
    have hgq : (Nat.gcd A q : ℤ) ∣ (q : ℤ) :=
      (Int.natCast_dvd_natCast).mpr (Nat.gcd_dvd_right A q)
    have h4 : (Nat.gcd A q : ℤ) ∣ v - ((v % (q : ℤ)).toNat : ℤ) := Int.dvd_trans hgq hqdiv
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨c2, hc2⟩ := h4
    refine ⟨c1 + c2, ?_⟩
    have h5 : v = ((v % (q : ℤ)).toNat : ℤ) + (v - ((v % (q : ℤ)).toNat : ℤ)) := by ring
    rw [h5, hc2, hc1]
    ring

  obtain ⟨k0, hk0⟩ := hgAv
  have hDne : (Nat.gcd A q : ℤ) * (w : ℤ) ≠ 0 := by
    have h1 : (Nat.gcd A q : ℤ) ≠ 0 := by
      have h2 : 0 < Nat.gcd A q := by rw [hgAeq]; exact hgA0
      have h3 : (0 : ℤ) < (Nat.gcd A q : ℤ) := by exact_mod_cast h2
      omega
    have h2 : (w : ℤ) ≠ 0 := by omega
    exact mul_ne_zero h1 h2
  have hsk : (reads i).residue = k0 * ((Nat.gcd A q : ℤ) * (w : ℤ)) := by
    rw [hvs, hk0]
    ring

  have hDvd : (Nat.gcd A q : ℤ) * (w : ℤ) ∣ (reads i).residue := by
    refine ⟨k0, ?_⟩
    rw [hsk]
    ring
  have hediv : (reads i).residue / ((Nat.gcd A q : ℤ) * (w : ℤ))
      * ((Nat.gcd A q : ℤ) * (w : ℤ)) = (reads i).residue :=
    Int.ediv_mul_cancel hDvd
  have hk0eq : (reads i).residue / ((Nat.gcd A q : ℤ) * (w : ℤ)) = k0 := by
    have h2 : (Nat.gcd A q : ℤ) * (w : ℤ) * ((reads i).residue
          / ((Nat.gcd A q : ℤ) * (w : ℤ)))
        = (Nat.gcd A q : ℤ) * (w : ℤ) * k0 := by
      calc
        (Nat.gcd A q : ℤ) * (w : ℤ) * ((reads i).residue
              / ((Nat.gcd A q : ℤ) * (w : ℤ)))
            = ((reads i).residue / ((Nat.gcd A q : ℤ) * (w : ℤ)))
                * ((Nat.gcd A q : ℤ) * (w : ℤ)) := by rw [Int.mul_comm]
        _ = (reads i).residue := hediv
        _ = k0 * ((Nat.gcd A q : ℤ) * (w : ℤ)) := hsk
        _ = (Nat.gcd A q : ℤ) * (w : ℤ) * k0 := by rw [Int.mul_comm]
    exact Int.eq_of_mul_eq_mul_left hDne h2

  have hnatabs : (reads i).residue.natAbs = k0.natAbs * (gA * w) := by
    have h1 : (reads i).residue.natAbs
        = (k0 * ((gA : ℤ) * (w : ℤ))).natAbs := by rw [hsk, hgAeq]
    have h2 : (k0 * ((gA : ℤ) * (w : ℤ))).natAbs
        = k0.natAbs * (((gA : ℤ) * (w : ℤ)).natAbs) :=
      Int.natAbs_mul k0 ((gA : ℤ) * (w : ℤ))
    have h3 : ((gA : ℤ) * (w : ℤ)).natAbs = gA * w := by
      have h4 := Int.natAbs_mul (gA : ℤ) (w : ℤ)
      rw [dlog_natCast_natAbs, dlog_natCast_natAbs] at h4
      exact h4
    rw [h1, h2, h3]
  have hle : k0.natAbs * (gA * w) ≤ q / 12 := by
    have h1 : (reads i).residue.natAbs ≤ q / 12 := hgood
    rw [hnatabs] at h1
    exact h1
  have hk0le : k0.natAbs ≤ (q / 12) / (w * gA) := by
    have h1 : 0 < w * gA := Nat.mul_pos (by omega) hgA0
    have h2 : k0.natAbs * (w * gA) ≤ q / 12 := by
      calc k0.natAbs * (w * gA) = k0.natAbs * (gA * w) := by ac_rfl
        _ ≤ q / 12 := hle
    exact (Nat.le_div_iff_mul_le h1).2 h2
  have hbounds : -((K : ℤ)) ≤ k0 ∧ k0 ≤ (K : ℤ) := by
    have h1 := dlogNatAbs_le_bounds k0 ((q / 12) / (w * gA)) hk0le
    simpa [hKdef] using! h1
  have hgAfull : dlogReadFiberDivisor m q w = Nat.gcd A q := by
    rw [hAdef]
    rfl
  have hgAD : (dlogReadFiberDivisor m q w : ℤ) * (w : ℤ)
      = (Nat.gcd A q : ℤ) * (w : ℤ) := by
    rw [hgAfull]
  refine ⟨k0, ?_, ?_, hbounds.1, hbounds.2⟩
  · rw [hgAdef, hgAD]
    exact hk0eq
  · rw [hgAdef, hgAD]
    exact hsk

/-- Bounds the number of divisible good reads by `dlogDivisibleReadBudget`. -/
theorem dlogDivisibleGoodReadCount_le (m q w : ℕ) (hm : 0 < m) (hq : 0 < q)
    (hw : 2 ≤ w) (hwm : w ∣ m) (reads : Fin q → DlogResidueRead)
    (hrel : ∀ i, DlogReadRelation m q i (reads i)) :
    ((Finset.univ : Finset (Fin q)).filter fun i : Fin q =>
        DlogGoodRead q (reads i) ∧ (w : ℤ) ∣ (reads i).cprime).card
      ≤ dlogDivisibleReadBudget m q w := by
  classical
  set gA := dlogReadFiberDivisor m q w with hgAdef
  set A := m / w with hAdef
  set K := (q / 12) / (w * gA) with hKdef
  have hgAeq : Nat.gcd A q = gA := by
    rw [hAdef, hgAdef]
    rfl
  have hgA0 : 0 < gA := by
    rw [← hgAeq]
    have hmw : 0 < m / w := Nat.div_pos (Nat.le_of_dvd hm hwm) (by omega)
    exact Nat.gcd_pos_of_pos_left q hmw

  let kidx : Fin q → ℤ := fun i => (reads i).residue / ((gA : ℤ) * (w : ℤ))
  have hbound : ∀ (i : Fin q),
      DlogGoodRead q (reads i) ∧ (w : ℤ) ∣ (reads i).cprime →
        -((K : ℤ)) ≤ kidx i ∧ kidx i ≤ (K : ℤ) := by
    intro i hi
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
      dlogDivisibleRead_index m q w hm hq hw hwm reads hrel i hi.1 hi.2
    have hki : kidx i = k := by
      simp only [kidx]
      have hconv : (gA : ℤ) * (w : ℤ) = ((dlogReadFiberDivisor m q w : ℤ) * (w : ℤ)) := by
        rw [hgAdef]
      rw [hconv]
      exact hk1
    rw [hki]
    exact ⟨hk3, hk4⟩

  have hqdiv0 : 0 < q / gA := by
    have hle : gA ≤ q := by
      rw [← hgAeq]
      exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right A q)
    exact Nat.div_pos hle hgA0
  have hqeq : gA * (q / gA) = q := by
    have hdvd : gA ∣ q := by
      rw [← hgAeq]
      exact Nat.gcd_dvd_right A q
    exact Nat.mul_div_cancel' hdvd
  have hlt : ∀ i : Fin q, i.val / (q / gA) < gA := by
    intro i
    rw [Nat.div_lt_iff_lt_mul hqdiv0, hqeq]
    exact i.isLt

  let f : Fin q → Fin (2 * K + 1) × Fin gA := fun i =>
    if hi : DlogGoodRead q (reads i) ∧ (w : ℤ) ∣ (reads i).cprime then
      ⟨dlogResidueIndex K (kidx i) (hbound i hi), ⟨i.val / (q / gA), hlt i⟩⟩
    else
      ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩
  let T : Finset (Fin q) := (Finset.univ : Finset (Fin q)).filter fun i : Fin q =>
      DlogGoodRead q (reads i) ∧ (w : ℤ) ∣ (reads i).cprime

  have hinj : ∀ i ∈ T, ∀ j ∈ T, f i = f j → i = j := by
    intro i hi j hj h
    have hcond_i : DlogGoodRead q (reads i) ∧ (w : ℤ) ∣ (reads i).cprime :=
      (Finset.mem_filter.mp hi).2
    have hcond_j : DlogGoodRead q (reads j) ∧ (w : ℤ) ∣ (reads j).cprime :=
      (Finset.mem_filter.mp hj).2

    have hfval := congrArg Prod.fst h
    have hidx : dlogResidueIndexVal K (kidx i) = dlogResidueIndexVal K (kidx j) := by
      have hfin : dlogResidueIndex K (kidx i) (hbound i hcond_i)
          = dlogResidueIndex K (kidx j) (hbound j hcond_j) := by
        have h2 := hfval
        simp only [f] at h2
        rw [dite_eq_left hcond_i, dite_eq_left hcond_j] at h2
        exact h2
      have hval := congrArg Fin.val hfin
      simpa only [dlogResidueIndex, dlogResidueIndexVal] using! hval
    have hki : kidx i = kidx j :=
      dlogResidueIndexVal_injective K (kidx i) (kidx j)
        (hbound i hcond_i) (hbound j hcond_j) hidx

    obtain ⟨ki, hki1, hki2, _, _⟩ :=
      dlogDivisibleRead_index m q w hm hq hw hwm reads hrel i hcond_i.1 hcond_i.2
    obtain ⟨kj, hkj1, hkj2, _, _⟩ :=
      dlogDivisibleRead_index m q w hm hq hw hwm reads hrel j hcond_j.1 hcond_j.2
    have hki_eq : kidx i = ki := by
      simp only [kidx]
      have hconv : (gA : ℤ) * (w : ℤ) = ((dlogReadFiberDivisor m q w : ℤ) * (w : ℤ)) := by
        rw [hgAdef]
      rw [hconv]
      exact hki1
    have hkj_eq : kidx j = kj := by
      simp only [kidx]
      have hconv : (gA : ℤ) * (w : ℤ) = ((dlogReadFiberDivisor m q w : ℤ) * (w : ℤ)) := by
        rw [hgAdef]
      rw [hconv]
      exact hkj1
    have hki' : ki = kj := by
      rw [hki_eq, hkj_eq] at hki
      exact hki

    have hres : (reads i).residue = (reads j).residue := by
      have hconv : (gA : ℤ) * (w : ℤ) = ((dlogReadFiberDivisor m q w : ℤ) * (w : ℤ)) := by
        rw [hgAdef]
      have h1 : (reads i).residue = ki * ((gA : ℤ) * (w : ℤ)) := by
        rw [← hconv]
        exact hki2
      have h2 : (reads j).residue = kj * ((gA : ℤ) * (w : ℤ)) := by
        rw [← hconv]
        exact hkj2
      rw [h1, h2, hki']

    obtain ⟨vi, hvi1, hvi2⟩ :=
      dlogDivisibleRead_reduced m q w hw hwm reads hrel i hcond_i.2
    obtain ⟨vj, hvj1, hvj2⟩ :=
      dlogDivisibleRead_reduced m q w hw hwm reads hrel j hcond_j.2
    have hvw : vi = vj := by
      have h1 : (reads i).residue = (w : ℤ) * vi := hvi2
      have h2 : (reads j).residue = (w : ℤ) * vj := hvj2
      have hw0 : (w : ℤ) ≠ 0 := by omega
      have h3 : (w : ℤ) * vi = (w : ℤ) * vj := by rw [← h1, ← h2]; exact hres
      exact Int.eq_of_mul_eq_mul_left hw0 h3
    have hnat_i : A * i.val ≡ (vi % (q : ℤ)).toNat [MOD q] := by
      have hcong : (A : ℤ) * (i : ℤ) ≡ vi [ZMOD q] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-((reads i).cprime / (w : ℤ)), ?_⟩
        rw [hAdef]
        rw [hvi1]
        ring
      have hlt' : (vi % (q : ℤ)).toNat < q := by
        have hlt'' : vi % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos vi (by omega)
        have hnonneg : (0 : ℤ) ≤ vi % (q : ℤ) :=
          @Int.emod_nonneg vi (q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hq))
        rw [← Int.toNat_of_nonneg hnonneg] at hlt''
        exact_mod_cast hlt''
      have h1 := dlogCongr_eq_mod A q hq vi i hcong
      show A * i.val % q = (vi % (q : ℤ)).toNat % q
      rw [Nat.mod_eq_of_lt hlt']
      exact h1
    have hnat_j : A * j.val ≡ (vi % (q : ℤ)).toNat [MOD q] := by
      have hcong : (A : ℤ) * (j : ℤ) ≡ vi [ZMOD q] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-((reads j).cprime / (w : ℤ)), ?_⟩
        rw [hAdef]
        rw [hvj1]
        rw [hvw]
        ring
      have hlt' : (vi % (q : ℤ)).toNat < q := by
        have hlt'' : vi % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos vi (by omega)
        have hnonneg : (0 : ℤ) ≤ vi % (q : ℤ) :=
          @Int.emod_nonneg vi (q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hq))
        rw [← Int.toNat_of_nonneg hnonneg] at hlt''
        exact_mod_cast hlt''
      have h1 := dlogCongr_eq_mod A q hq vi j hcong
      show A * j.val % q = (vi % (q : ℤ)).toNat % q
      rw [Nat.mod_eq_of_lt hlt']
      exact h1
    have hquot : i.val % (q / gA) = j.val % (q / gA) := by
      have h1 := dlogCongrFiber_quot_eq A q ((vi % (q : ℤ)).toNat) hq i j hnat_i hnat_j
      rw [hgAeq] at h1
      exact h1

    have hfst2 := congrArg Prod.snd h
    have hdiv : i.val / (q / gA) = j.val / (q / gA) := by
      have h2 := hfst2
      simp only [f] at h2
      rw [dite_eq_left hcond_i, dite_eq_left hcond_j] at h2
      exact congrArg Fin.val h2
    have h1 := Nat.div_add_mod i.val (q / gA)
    have h2 := Nat.div_add_mod j.val (q / gA)
    rw [hdiv] at h1
    have h3 : i.val = j.val := by omega
    exact Fin.ext h3

  have hcard : (T.image f).card = T.card :=
    Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h)
  have himg : T.image f ⊆ (Finset.univ : Finset (Fin (2 * K + 1) × Fin gA)) := by
    intro y hy
    exact Finset.mem_univ _
  have hle : (T.image f).card ≤ (Finset.univ : Finset (Fin (2 * K + 1) × Fin gA)).card :=
    Finset.card_le_card himg
  have huniv : (Finset.univ : Finset (Fin (2 * K + 1) × Fin gA)).card = (2 * K + 1) * gA := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have hmain : T.card ≤ dlogDivisibleReadBudget m q w := by
    calc
      T.card = (T.image f).card := hcard.symm
      _ ≤ (2 * K + 1) * gA := hle.trans huniv.le
      _ = dlogDivisibleReadBudget m q w := by
        unfold dlogDivisibleReadBudget
        rw [hKdef, hgAdef]
  show T.card ≤ dlogDivisibleReadBudget m q w
  exact hmain

/-- Bounds the divisible read budget by the modulus divided by `w` under the stated parameter
bounds. -/
theorem dlogDivisibleReadBudget_le_frac (m q w : ℕ) (hm : 0 < m)
    (hw : 2 ≤ w) (hwm : w ∣ m) (hq2m : q ≤ 2 * m + 1) :
    dlogDivisibleReadBudget m q w ≤ m / w := by
  classical
  unfold dlogDivisibleReadBudget
  set gA := dlogReadFiberDivisor m q w with hgAdef
  set K := (q / 12) / (w * gA) with hKdef
  have hgApos : 0 < gA := by
    unfold gA dlogReadFiberDivisor
    have hmw : 0 < m / w := Nat.div_pos (Nat.le_of_dvd hm hwm) (by omega)
    exact Nat.gcd_pos_of_pos_left q hmw
  have hgAle : gA ≤ m / w := by
    unfold gA dlogReadFiberDivisor
    have hmw : 0 < m / w := Nat.div_pos (Nat.le_of_dvd hm hwm) (by omega)
    exact Nat.le_of_dvd hmw (Nat.gcd_dvd_left (m / w) q)
  have hwpos : 0 < w := by omega
  have hKmul : K * (w * gA) ≤ q / 12 := by
    have h1 : (q / 12) / (w * gA) * (w * gA) ≤ q / 12 := Nat.div_mul_le_self _ _
    simpa [hKdef] using! h1
  have hdiv12 : 3 * (q / 12) ≤ m := by
    have h1 : ((q / 12 : ℕ) : ℝ) ≤ (q : ℝ) / 12 := by
      have h2 : (12 : ℝ) * ((q / 12 : ℕ) : ℝ) + ((q % 12 : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast Nat.div_add_mod q 12
      have h3 : (0 : ℝ) ≤ ((q % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 12)).2
      linarith
    have h2 : (3 * (q / 12 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have h3 : (q : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hq2m
      have h5 : (3 * (q / 12 : ℕ) : ℝ) < (m : ℝ) := by
        calc
          (3 * (q / 12 : ℕ) : ℝ) = 3 * ((q / 12 : ℕ) : ℝ) := by norm_cast
          _ ≤ 3 * ((q : ℝ) / 12) := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = (q : ℝ) / 4 := by ring
          _ ≤ (2 * (m : ℝ) + 1) / 4 := by
            exact div_le_div_of_nonneg_right h3 (by norm_num)
          _ = (m : ℝ) / 2 + 1 / 4 := by ring
          _ < (m : ℝ) := by
            have h4 : (1 : ℝ) ≤ (m : ℝ) := by
              exact_mod_cast (show 1 ≤ m by omega)
            linarith
      exact h5.le
    exact_mod_cast h2
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · rw [hK0]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul]
    exact hgAle
  · have hwgA : w * gA ≤ q / 12 := by
      have h : 1 * (w * gA) ≤ K * (w * gA) := Nat.mul_le_mul_right (w * gA) hK1
      have h' : w * gA ≤ 1 * (w * gA) := by simp
      exact le_trans h' (le_trans h hKmul)
    have hKgA : (K * gA) * w ≤ q / 12 := by
      have h1 : K * gA * w = K * (w * gA) := by ring
      rw [h1]
      exact hKmul
    have hmain : (2 * K + 1) * gA * w ≤ m := by
      have h1 : (2 * K + 1) * gA * w = 2 * ((K * gA) * w) + gA * w := by ring
      rw [h1]
      have h3 : gA * w ≤ q / 12 := by simpa [Nat.mul_comm] using! hwgA
      have h4 : 2 * ((K * gA) * w) + gA * w ≤ 2 * (q / 12) + (q / 12) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hKgA) h3
      have h2 : 2 * ((K * gA) * w) + gA * w ≤ 3 * (q / 12) := by
        rw [show 2 * (q / 12) + (q / 12) = 3 * (q / 12) by ring] at h4
        exact h4
      omega
    have h6 : (2 * K + 1) * gA ≤ m / w := (Nat.le_div_iff_mul_le hwpos).2 hmain
    exact h6

/-- Shows that the marginal probabilities sum to one. -/
theorem dlogMarginal_sum_one {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (π : X → Y) : (∑ y, dlogMarginal law π y) = 1 := by
  unfold dlogMarginal
  rw [Finset.sum_comm]
  calc
    (∑ x, ∑ y, if π x = y then law.prob x else 0) = ∑ x, law.prob x := by
      apply Finset.sum_congr rfl
      intro x _
      have hsingle : (∑ y ∈ (Finset.univ : Finset Y),
            (if π x = y then law.prob x else 0))
          = (if π x = π x then law.prob x else 0) :=
        Finset.sum_eq_single (π x) (fun b _ hb => by
          have hne : ¬(π x = b) := fun h => hb h.symm
          simp [hne])
          (fun h => absurd (Finset.mem_univ _) h)
      rw [hsingle]
      simp
    _ = 1 := law.sum_one

/-- Shows that summing joint masses over marginal outcomes recovers the event mass. -/
theorem dlogJointMass_sum {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] (π : X → Y) :
    (∑ y, dlogJointMass law E π y) = dlogEventMass law E := by
  unfold dlogJointMass dlogEventMass
  rw [Finset.sum_comm]
  calc
    (∑ x, ∑ y, if π x = y ∧ E x then law.prob x else 0)
        = ∑ x, if E x then law.prob x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have hsingle : (∑ y ∈ (Finset.univ : Finset Y),
            (if π x = y ∧ E x then law.prob x else 0))
          = (if π x = π x ∧ E x then law.prob x else 0) :=
        Finset.sum_eq_single (π x) (fun b _ hb => by
          have hne : ¬(π x = b) := fun h => hb h.symm
          simp [hne])
          (fun h => absurd (Finset.mem_univ _) h)
      rw [hsingle]
      simp
    _ = _ := rfl

/-- Shows that joint mass vanishes outside any predicate containing the event's image. -/
theorem dlogJointMass_eq_zero_of_not_good {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (E : X → Prop) [DecidablePred E] (π : X → Y)
    (G : Y → Prop) [DecidablePred G]
    (hsub : ∀ x, E x → G (π x)) (y : Y) (hGy : ¬ G y) :
    dlogJointMass law E π y = 0 := by
  unfold dlogJointMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases h : π x = y ∧ E x
  · have hgy : G y := by
      rw [← h.1]
      exact hsub x h.2
    exact absurd hgy hGy
  · simp [h]

/-- Shows that a uniform marginal has a nonzero codomain cardinality. -/
theorem dlogUniformMarginal_card_ne_zero {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (π : X → Y)
    (hmarg : dlogUniformMarginal law π) : (Fintype.card Y : ℝ) ≠ 0 := by
  intro hzero
  have h1 : ∀ y, dlogMarginal law π y = 0 := by
    intro y
    rw [hmarg y, hzero]
    simp
  have h2 : (∑ y, dlogMarginal law π y) = 0 := by
    calc
      (∑ y, dlogMarginal law π y) = ∑ y, 0 :=
        Finset.sum_congr rfl (fun y _ => by rw [h1 y])
      _ = 0 := by simp
  have h3 := dlogMarginal_sum_one law π
  rw [h2] at h3
  linarith

/-- Expresses the goodness weight as joint mass times the codomain cardinality under a uniform
marginal. -/
theorem dlogGoodnessWeight_eq {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] (π : X → Y)
    (hmarg : dlogUniformMarginal law π) (y : Y) :
    dlogGoodnessWeight law E π y
      = dlogJointMass law E π y * (Fintype.card Y : ℝ) := by
  have hcard := dlogUniformMarginal_card_ne_zero law π hmarg
  unfold dlogGoodnessWeight
  rw [hmarg y]
  field_simp

/-- Computes the total goodness weight as event mass times the codomain cardinality. -/
theorem dlogGoodnessWeight_sum {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] (π : X → Y)
    (hmarg : dlogUniformMarginal law π) :
    (∑ y, dlogGoodnessWeight law E π y)
      = dlogEventMass law E * (Fintype.card Y : ℝ) := by
  calc
    (∑ y, dlogGoodnessWeight law E π y)
        = ∑ y, dlogJointMass law E π y * (Fintype.card Y : ℝ) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [dlogGoodnessWeight_eq law E π hmarg y]
    _ = (∑ y, dlogJointMass law E π y) * (Fintype.card Y : ℝ) := by
          rw [Finset.sum_mul]
    _ = dlogEventMass law E * (Fintype.card Y : ℝ) := by
          rw [dlogJointMass_sum]

/-- Expresses the conditional law as normalized goodness weights under a uniform marginal. -/
theorem dlogConditionalLaw_eq_reweightedUniform {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] (law : FinDist X) (E : X → Prop) [DecidablePred E] (π : X → Y)
    (hmass : 0 < dlogEventMass law E) (hmarg : dlogUniformMarginal law π) :
    ∀ y, (dlogConditionalLaw law E π hmass).prob y
      = dlogGoodnessWeight law E π y
        / (∑ y', dlogGoodnessWeight law E π y') := by
  intro y
  have hcard := dlogUniformMarginal_card_ne_zero law π hmarg
  have hμ : (dlogConditionalLaw law E π hmass).prob y
      = dlogJointMass law E π y
          / dlogEventMass law E := by
    rw [dlogConditionalLaw_prob_eq_joint law E π hmass y]
    unfold dlogJointMass
    rw [Finset.sum_filter]
  rw [hμ, dlogGoodnessWeight_eq law E π hmarg y,
    dlogGoodnessWeight_sum law E π hmarg]
  have hne : dlogEventMass law E ≠ 0 := hmass.ne'
  field_simp

/-- Computes the uniform good-index law as reciprocal cardinality on good indices and zero
elsewhere. -/
theorem dlogUniformGoodIndexLaw_apply {Y : Type} [Fintype Y] [DecidableEq Y]
    (G : Y → Prop) [DecidablePred G] (hG : 0 < dlogGoodIndexCard G) (y : Y) :
    (dlogUniformGoodIndexLaw G hG).prob y = if G y then (dlogGoodIndexCard G : ℝ)⁻¹ else 0 := rfl

/-- Computes event mass under the uniform good-index law as the fraction of good indices
satisfying the event. -/
theorem dlogUniformGoodIndexLaw_event_mass {Y : Type} [Fintype Y] [DecidableEq Y]
    (G : Y → Prop) [DecidablePred G] (hG : 0 < dlogGoodIndexCard G)
    (E : Y → Prop) [DecidablePred E] :
    (∑ y, if E y then (dlogUniformGoodIndexLaw G hG).prob y else 0)
      = ((Finset.univ.filter fun y => G y ∧ E y).card : ℝ)
          / (dlogGoodIndexCard G : ℝ) := by
  classical
  have hmain : (∑ y, if E y then (dlogUniformGoodIndexLaw G hG).prob y else 0)
      = (∑ y ∈ (Finset.univ.filter (fun y => G y ∧ E y)),
          (dlogGoodIndexCard G : ℝ)⁻¹) := by
    have hflatten : (fun y => if E y then (dlogUniformGoodIndexLaw G hG).prob y else 0)
        = (fun y => if G y ∧ E y then (dlogGoodIndexCard G : ℝ)⁻¹ else 0) := by
      funext y
      by_cases hE : E y
      · by_cases hS : G y
        · rw [dlogUniformGoodIndexLaw_apply G hG y]
          simp [hE, hS]
        · rw [dlogUniformGoodIndexLaw_apply G hG y]
          simp [hE, hS]
      · rw [dlogUniformGoodIndexLaw_apply G hG y]
        simp [hE]
    rw [hflatten, ← Finset.sum_filter]
  have hcard : ((dlogGoodIndexCard G : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hG)
  calc
    (∑ y, if E y then (dlogUniformGoodIndexLaw G hG).prob y else 0)
        = (∑ y ∈ (Finset.univ.filter (fun y => G y ∧ E y)),
            (dlogGoodIndexCard G : ℝ)⁻¹) := hmain
    _ = ((Finset.univ.filter (fun y => G y ∧ E y)).card : ℝ)
          * (dlogGoodIndexCard G : ℝ)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Finset.univ.filter (fun y => G y ∧ E y)).card : ℝ)
          / (dlogGoodIndexCard G : ℝ) := by rw [div_eq_mul_inv]

/-- Characterizes pointwise transport to the uniform good-index law by bounding each good-index
weight by the total goodness weight divided by the number of good indices. -/
theorem dlogUniformGoodPointwiseTransport_iff {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (law : FinDist X) (E : X → Prop) [DecidablePred E]
    (G : Y → Prop) [DecidablePred G] (π : X → Y)
    (hsub : ∀ x, E x → G (π x))
    (hG : 0 < dlogGoodIndexCard G)
    (hmass : 0 < dlogEventMass law E)
    (hmarg : dlogUniformMarginal law π) :
    dlogUniformGoodPointwiseTransport (dlogConditionalLaw law E π hmass)
        (dlogUniformGoodIndexLaw G hG) ↔
      ∀ y, G y → dlogGoodnessWeight law E π y
        ≤ (∑ y', dlogGoodnessWeight law E π y') / (dlogGoodIndexCard G : ℝ) := by
  classical
  have hgoodpos : (0 : ℝ) < (dlogGoodIndexCard G : ℝ) := by
    have h1 : (1 : ℕ) ≤ dlogGoodIndexCard G := by omega
    have h2 : (1 : ℝ) ≤ (dlogGoodIndexCard G : ℝ) := by exact_mod_cast h1
    linarith
  have hgoodne : ((dlogGoodIndexCard G : ℕ) : ℝ) ≠ 0 := ne_of_gt hgoodpos
  have hsumwpos : (0 : ℝ) < ∑ y, dlogGoodnessWeight law E π y := by
    rw [dlogGoodnessWeight_sum law E π hmarg]
    have hcardne := dlogUniformMarginal_card_ne_zero law π hmarg
    have hcardpos : (0 : ℝ) < (Fintype.card Y : ℝ) := by
      have h1 : (0 : ℕ) ≤ Fintype.card Y := Nat.zero_le _
      have h2 : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast h1
      exact lt_of_le_of_ne h2 (Ne.symm hcardne)
    exact mul_pos hmass hcardpos
  have hsumwne : (∑ y, dlogGoodnessWeight law E π y) ≠ 0 := ne_of_gt hsumwpos
  constructor
  · intro hdom y hGy
    have hμ := dlogConditionalLaw_eq_reweightedUniform law E π hmass hmarg y
    have hν : (dlogUniformGoodIndexLaw G hG).prob y = (dlogGoodIndexCard G : ℝ)⁻¹ := by
      rw [dlogUniformGoodIndexLaw_apply G hG y]
      simp [hGy]
    have hle := hdom y
    rw [hμ, hν] at hle
    rw [div_le_iff₀ hsumwpos] at hle
    have hmul := mul_le_mul_of_nonneg_right hle (by
      positivity : (0 : ℝ) ≤ (dlogGoodIndexCard G : ℝ))
    rw [le_div_iff₀ hgoodpos]
    calc
      dlogGoodnessWeight law E π y * (dlogGoodIndexCard G : ℝ)
          ≤ ((dlogGoodIndexCard G : ℝ)⁻¹
              * (∑ y', dlogGoodnessWeight law E π y'))
              * (dlogGoodIndexCard G : ℝ) := hmul
      _ = ∑ y', dlogGoodnessWeight law E π y' := by field_simp
  · intro hw y
    by_cases hGy : G y
    · have hstep : dlogGoodnessWeight law E π y * (dlogGoodIndexCard G : ℝ)
          ≤ ∑ y', dlogGoodnessWeight law E π y' := by
        have h' := hw y hGy
        rw [le_div_iff₀ hgoodpos] at h'
        exact h'
      have hmul := mul_le_mul_of_nonneg_right hstep (by
        positivity : (0 : ℝ) ≤ (dlogGoodIndexCard G : ℝ)⁻¹)
      have htarget : dlogGoodnessWeight law E π y
          ≤ (dlogGoodIndexCard G : ℝ)⁻¹
              * (∑ y', dlogGoodnessWeight law E π y') := by
        calc
          dlogGoodnessWeight law E π y
              = (dlogGoodnessWeight law E π y * (dlogGoodIndexCard G : ℝ))
                  * (dlogGoodIndexCard G : ℝ)⁻¹ := by field_simp
          _ ≤ (∑ y', dlogGoodnessWeight law E π y')
                * (dlogGoodIndexCard G : ℝ)⁻¹ := hmul
          _ = (dlogGoodIndexCard G : ℝ)⁻¹
                * (∑ y', dlogGoodnessWeight law E π y') := by ring
      have hμ := dlogConditionalLaw_eq_reweightedUniform law E π hmass hmarg y
      have hν : (dlogUniformGoodIndexLaw G hG).prob y = (dlogGoodIndexCard G : ℝ)⁻¹ := by
        rw [dlogUniformGoodIndexLaw_apply G hG y]
        simp [hGy]
      rw [hμ, hν]
      rw [div_le_iff₀ hsumwpos]
      exact htarget
    · have hμzero : (dlogConditionalLaw law E π hmass).prob y = 0 := by
        rw [dlogConditionalLaw_eq_reweightedUniform law E π hmass hmarg y]
        have hz : dlogGoodnessWeight law E π y = 0 := by
          unfold dlogGoodnessWeight
          rw [dlogJointMass_eq_zero_of_not_good law E π G hsub y hGy]
          simp
        rw [hz]
        simp
      have hνzero : (dlogUniformGoodIndexLaw G hG).prob y = 0 := by
        rw [dlogUniformGoodIndexLaw_apply G hG y]
        simp [hGy]
      rw [hμzero, hνzero]

/-- Bounds the modular exponentiation width by the encoding width plus one. -/
theorem dlogModexpWidth_le (p x q : ℕ) (enc : DlogGroupEncoding p x q) (hp : 1 ≤ p) :
    Nat.log2 p + 1 ≤ enc.pBits + 1 := by
  have hne : p ≠ 0 := by omega
  have henc := enc.hp
  have h1 : ¬ (enc.pBits + 1 ≤ Nat.log2 p) := by
    intro h
    have h2 : 2 ^ (enc.pBits + 1) ≤ p := (Nat.le_log2 hne).mp h
    have h3 : 2 ^ (enc.pBits + 1) = 2 ^ enc.pBits * 2 := by rw [Nat.pow_succ]
    rw [h3] at h2
    have h4 : 2 ^ enc.pBits * 2 > 2 ^ enc.pBits := by
      have hpos : (0 : ℕ) < 2 ^ enc.pBits := by positivity
      omega
    omega
  omega

/-- Bounds the total gate budget by the stated cubic polynomial in the encoding width plus one. -/
theorem dlogTotalGateCount_pow (p x q : ℕ) (enc : DlogGroupEncoding p x q) (hp : 1 ≤ p) :
    dlogTotalGateCount p x q enc
      ≤ 2 * ((enc.pBits + 1) ^ 2 + (enc.pBits + 1)) + 6400 * ((enc.pBits + 1) ^ 3) := by
  have h := dlogModexpWidth_le p x q enc hp
  have hsq : (Nat.log2 p + 1) ^ 3 ≤ (enc.pBits + 1) ^ 3 := by
    have h1 : Nat.log2 p + 1 ≤ enc.pBits + 1 := h
    have h2 : (0 : ℕ) ≤ Nat.log2 p + 1 := Nat.zero_le _
    exact pow_le_pow_left₀ h2 h1 3
  have hmul : 6400 * (Nat.log2 p + 1) ^ 3 ≤ 6400 * ((enc.pBits + 1) ^ 3) := by
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  unfold dlogTotalGateCount
  omega

/-- Bounds the total space budget by the stated quadratic polynomial in the encoding width plus
one. -/
theorem dlogTotalSpaceCount_pow (p x q : ℕ) (enc : DlogGroupEncoding p x q) (hp : 1 ≤ p) :
    dlogTotalSpaceCount p x q enc
      ≤ 3 * (enc.pBits + 1) + 91 * ((enc.pBits + 1) ^ 2) + 27 * (enc.pBits + 1) + 2 := by
  have h := dlogModexpWidth_le p x q enc hp
  have hsq : (Nat.log2 p + 1) ^ 2 ≤ (enc.pBits + 1) ^ 2 := by
    have h1 : Nat.log2 p + 1 ≤ enc.pBits + 1 := h
    have h2 : (0 : ℕ) ≤ Nat.log2 p + 1 := Nat.zero_le _
    exact pow_le_pow_left₀ h2 h1 2
  have h91 : 91 * (Nat.log2 p + 1) ^ 2 ≤ 91 * ((enc.pBits + 1) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have h27 : 27 * (Nat.log2 p + 1) ≤ 27 * (enc.pBits + 1) := by
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  unfold dlogTotalSpaceCount
  omega

/-- Establishes the conditional-law and uniform-good transport conclusions collected in clause
six. -/
theorem clause6_endpoint {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] (G : Y → Prop) [DecidablePred G]
    (π : X → Y) (hsub : ∀ x, E x → G (π x))
    (hG : 0 < dlogGoodIndexCard G)
    (hmass : 0 < dlogEventMass law E)
    (hmarg : dlogUniformMarginal law π) :
    (∀ y, (dlogConditionalLaw law E π hmass).prob y
        = dlogGoodnessWeight law E π y
          / (∑ y', dlogGoodnessWeight law E π y')) ∧
    (∀ y, ¬ G y → (dlogConditionalLaw law E π hmass).prob y = 0) ∧
    (∀ y, (dlogUniformGoodIndexLaw G hG).prob y
        = if G y then (dlogGoodIndexCard G : ℝ)⁻¹ else 0) ∧
    (dlogUniformGoodPointwiseTransport
        (dlogConditionalLaw law E π hmass)
        (dlogUniformGoodIndexLaw G hG) ↔
      ∀ y, G y → dlogGoodnessWeight law E π y
        ≤ (∑ y', dlogGoodnessWeight law E π y') / (dlogGoodIndexCard G : ℝ)) := by
  refine ⟨dlogConditionalLaw_eq_reweightedUniform law E π hmass hmarg, ?_,
    fun _ => dlogUniformGoodIndexLaw_apply G hG _,
    dlogUniformGoodPointwiseTransport_iff law E G π hsub hG hmass hmarg⟩
  intro y hGy
  rw [dlogConditionalLaw_eq_reweightedUniform law E π hmass hmarg y]
  have hz : dlogGoodnessWeight law E π y = 0 := by
    unfold dlogGoodnessWeight
    rw [dlogJointMass_eq_zero_of_not_good law E π G hsub y hGy]
    simp
  rw [hz]
  simp

/-- Establishes the sampling, pinned enumeration, and verified recovery conclusions collected in
clause seven. -/
theorem clause7_endpoint {X : Type} [Fintype X] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E]
    (hmass : 1 / 480 ≤ law.expect (fun x => if E x then (1 : ℝ) else 0))
    (t n : ℕ) (ht : 0 < t) (hn : n ^ 2 ≥ t)
    (p : ℕ) [NeZero p] (g x : ZMod p) (r : ℕ) (hr : r < p - 1)
    (hx : x = g ^ r) (hg : orderOf g = p - 1) {s : ℕ} (rec : DlogSampleRecord (p - 1) s)
    (hcong : dlogSampleCongruent (p - 1) (r : ℤ) rec)
    (hpinned : dlogPinningHypothesis (p - 1) rec) :
    (dlogSmallEnumerationCost (p - 1) rec
        = ∏ ℓ ∈ dlogSmallBasePrimes (p - 1),
            ℓ ^ dlogCommonValuation ℓ ((p - 1).factorization ℓ) rec) ∧
    ((dlogCrtCandidateList (p - 1) rec (fun _ => 0)).length
        = dlogEnumerationCost (p - 1) rec) ∧
    (dlogVerifiedCandidates p g x rec = [r]) ∧
    (dlogEnumerationCost (p - 1) rec = 1) ∧
    (law.probEvent (L := 480 * t + 960 * (n + 1))
      (fun ω : Fin (480 * t + 960 * (n + 1)) → X =>
        (t : ℝ) ≤ ∑ j, if E (ω j) then (1 : ℝ) else 0) ≥ 1 / 2) := by
  have hne : ∀ ℓ ∈ dlogBasePrimes (p - 1),
      (dlogPrimeCandidates (p - 1) rec ℓ).Nonempty := by
    intro ℓ hℓ
    exact ⟨r % dlogMaxPrimePower (p - 1) ℓ,
      dlogPrimeCandidates_contains (p - 1) r rec hcong ℓ hℓ⟩
  have hnes : ∀ ℓ ∈ dlogSmallBasePrimes (p - 1),
      (dlogPrimeCandidates (p - 1) rec ℓ).Nonempty := by
    intro ℓ hℓ
    exact hne ℓ ((Finset.mem_filter.mp hℓ).1)
  refine ⟨dlogSmallEnumerationCost_eq_pow (p - 1) rec hnes, ?_,
    dlogVerifiedCandidates_eq_singleton p g x hg r hr hx rec hcong,
    dlogEnumerationCost_eq_one_of_pinned (p - 1) rec hpinned hne,
    dlogGoodCountBudget law E hmass t n ht hn⟩
  exact dlogCrtCandidateList_length (p - 1) rec

/-- Establishes the inverse, gate, space, and query resource conclusions collected in clause
eight. -/
theorem clause8_endpoint (p x q : ℕ) [NeZero p] (enc : DlogGroupEncoding p x q)
    (hp : 2 ≤ p) (hq2p : q < 2 * p) :
    (IsUnit (x : ZMod p)) ∧
    (∃ y : ZMod p, y.val < p ∧ (x : ZMod p) * y = 1) ∧
    (GateCount (localProgramCircuit (dlogReadoutProgram (enc.pBits + 1)))
      + dlogModexpGateCount (Nat.log2 p + 1) (p - 1) ≤ dlogTotalGateCount p x q enc) ∧
    (3 * (enc.pBits + 1) + dlogModMulSpaceCount (Nat.log2 p + 1)
      ≤ dlogTotalSpaceCount p x q enc) ∧
    (QueryCount (localProgramCircuit (dlogReadoutProgram (enc.pBits + 1))) = 0) ∧
    (q ≤ 2 ^ (enc.pBits + 1)) ∧
    (∀ base m e, dlogModexpValue base m e = base ^ e % m) ∧
    (dlogTotalGateCount p x q enc
      ≤ 2 * ((enc.pBits + 1) ^ 2 + (enc.pBits + 1)) + 6400 * ((enc.pBits + 1) ^ 3)) ∧
    (dlogTotalSpaceCount p x q enc
      ≤ 3 * (enc.pBits + 1) + 91 * ((enc.pBits + 1) ^ 2) + 27 * (enc.pBits + 1) + 2) := by
  refine ⟨dlogEncoding_isUnit p x q enc, dlogEncoding_inverse p x q enc,
    dlogTotalGateCount_le p x q enc hp, dlogTotalSpaceCount_le p x q enc,
    (dlogReadoutProgram_counts (enc.pBits + 1)).2.2,
    dlogReadoutWidth_sufficient p x q enc hq2p,
    fun base m e => dlogModexpValue_eq base m e,
    dlogTotalGateCount_pow p x q enc (by omega),
    dlogTotalSpaceCount_pow p x q enc (by omega)⟩

end Qatlib.Concepts.PeriodSampling.DiscreteLog
