/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.ShorOrderDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PeriodSampling.OrderRecovery

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder

open Qatlib
open Matrix
open scoped Classical BigOperators ComplexConjugate
set_option warningAsError false

theorem pow_lt_pow_of_lt_base (a b n : ℕ) (h : a < b) (hb : 0 < b) (hn : 0 < n) :
    a ^ n < b ^ n := by
  induction n with
  | zero => exact absurd hn (by omega)
  | succ n ih =>
    by_cases hz : n = 0
    · subst hz
      simpa [pow_succ, pow_zero, one_mul] using! h
    · rw [pow_succ, pow_succ]
      have hpos : 0 < n := by omega
      calc a ^ n * a ≤ b ^ n * a := Nat.mul_le_mul (le_of_lt (ih hpos)) (le_refl _)
        _ < b ^ n * b := by
          have h2 := Nat.mul_lt_mul_of_pos_right h (by positivity : 0 < b ^ n)
          simpa [mul_comm] using! h2

theorem pow_le_pow_same (a m n : ℕ) (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := by
  induction n generalizing m with
  | zero =>
    have hz : m = 0 := by omega
    subst hz
    simp
  | succ n ih =>
    by_cases hm : m ≤ n
    · rw [pow_succ]
      exact Nat.le_trans (by rw [Nat.mul_one]; exact ih m hm)
        (Nat.mul_le_mul (le_refl _) (by omega : 1 ≤ a))
    · have hz : m = n + 1 := by omega
      subst hz
      simp only [pow_succ]
      exact le_rfl

theorem pow_mul4 (x : ℕ) : (x ^ 2) ^ 2 = x ^ 4 := by
  calc (x ^ 2) ^ 2 = x ^ 2 * x ^ 2 := by rw [pow_succ, pow_one]
    _ = x ^ (2 + 2) := by rw [Nat.pow_add]
    _ = x ^ 4 := by norm_num

theorem pow_mul5 (x : ℕ) : x * x ^ 4 = x ^ 5 := by
  calc x * x ^ 4 = x ^ 1 * x ^ 4 := by rw [pow_one]
    _ = x ^ (1 + 4) := by rw [Nat.pow_add]
    _ = x ^ 5 := by norm_num

theorem lt_two_pow_orderBitLength (N : ℕ) : N < 2 ^ orderBitLength N := by
  unfold orderBitLength
  by_cases hN : N = 0
  · simp [hN]
  · exact (Nat.log_lt_iff_lt_pow Nat.one_lt_two hN).mp (by omega)

theorem two_pow_le_of_log2 (N : ℕ) (hN : N ≠ 0) : 2 ^ (Nat.log 2 N) ≤ N := by
  exact (Nat.le_log_iff_pow_le Nat.one_lt_two hN).mp (le_refl (Nat.log 2 N))

theorem find_congr {p : ℕ → Prop} [DecidablePred p] {H1 H2 : ∃ n, p n} :
    Nat.find H1 = Nat.find H2 := by
  apply (Nat.find_eq_iff H1).mpr
  refine ⟨Nat.find_spec H2, ?_⟩
  intro n hn
  exact Nat.find_min H2 hn

theorem intRoot_eq_find (e N : ℕ) (he : 1 ≤ e) :
    intRoot e N = Nat.find (powExceedWitness e N he) - 1 := by
  unfold intRoot
  rw [dif_neg (by omega : e ≠ 0)]

theorem find_pow_exceeds_pos (e N : ℕ) (he : 1 ≤ e) :
    0 < Nat.find (powExceedWitness e N he) := by
  by_contra hc
  have hz : Nat.find (powExceedWitness e N he) = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hc)
  have h0 := (Nat.find_eq_iff (powExceedWitness e N he)).mp hz |>.1
  rw [Nat.zero_pow (by omega : 0 < e)] at h0
  omega

theorem find_pow_exceeds (e N : ℕ) (he : 1 ≤ e) :
    (Nat.find (powExceedWitness e N he)) ^ e > N ∧
      (Nat.find (powExceedWitness e N he) - 1) ^ e ≤ N := by
  have hpos := find_pow_exceeds_pos e N he
  have hspec := Nat.find_spec (powExceedWitness e N he)
  have hmin : ∀ m, m < Nat.find (powExceedWitness e N he) → ¬ (m ^ e > N) :=
    fun m hlt => Nat.find_min (powExceedWitness e N he) hlt
  refine ⟨hspec, ?_⟩
  by_contra hcon
  have hgt : (Nat.find (powExceedWitness e N he) - 1) ^ e > N := Nat.not_le.mp hcon
  have hlt : Nat.find (powExceedWitness e N he) - 1 < Nat.find (powExceedWitness e N he) := by
    have h1 : Nat.find (powExceedWitness e N he) - 1 + 1 = Nat.find (powExceedWitness e N he) :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    rw [← h1]
    exact Nat.lt_add_one _
  exact hmin _ hlt hgt

theorem intRoot_pow_le (e N : ℕ) (he : 1 ≤ e) : intRoot e N ^ e ≤ N := by
  rw [intRoot_eq_find e N he]
  exact (find_pow_exceeds e N he).2

theorem intRoot_succ_pow_gt (e N : ℕ) (he : 1 ≤ e) : (intRoot e N + 1) ^ e > N := by
  rw [intRoot_eq_find e N he]
  have h := (find_pow_exceeds e N he).1
  have hstep : Nat.find (powExceedWitness e N he) - 1 + 1 = Nat.find (powExceedWitness e N he) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (find_pow_exceeds_pos e N he))
  rw [hstep]
  exact h

theorem mem_perfectPowerDivisors (N m e : ℕ) (hm : 2 ≤ m) (he : 2 ≤ e) (hN : m ^ e = N) :
    m ∈ perfectPowerDivisors N := by
  have h2e : 2 ^ e ≤ N := by
    rw [← hN]
    exact pow_le_pow_of_le_base 2 m e (by omega)
  have hN0 : N ≠ 0 := by
    rw [← hN]
    intro hz
    have hge : m ^ e ≥ m := pow_ge_self m e (by omega) (by omega)
    omega
  have hlog : e ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le Nat.one_lt_two hN0).mpr h2e
  have hle : e ≤ orderBitLength N := by unfold orderBitLength; omega
  have hroot : intRoot e N = m := by
    have h1 : m ≤ intRoot e N := by
      by_contra hc
      have hlt : intRoot e N < m := Nat.lt_of_not_ge hc
      have hstep : intRoot e N + 1 ≤ m := by omega
      have hle : (intRoot e N + 1) ^ e ≤ m ^ e := pow_le_pow_of_le_base _ _ _ hstep
      have hgt : (intRoot e N + 1) ^ e > N := intRoot_succ_pow_gt e N (by omega)
      rw [hN] at hle
      have hcontra : (intRoot e N + 1) ^ e < (intRoot e N + 1) ^ e :=
        Nat.lt_of_le_of_lt hle hgt
      exact (Nat.lt_irrefl _ hcontra)
    have h2 : intRoot e N < m + 1 := by
      by_contra hc
      have hge : m + 1 ≤ intRoot e N := Nat.le_of_not_gt hc
      have hle : (m + 1) ^ e ≤ (intRoot e N) ^ e := pow_le_pow_of_le_base _ _ _ hge
      have hle2 : (intRoot e N) ^ e ≤ N := intRoot_pow_le e N (by omega)
      have hstrict : m ^ e < (m + 1) ^ e :=
        pow_lt_pow_of_lt_base m (m + 1) e (by omega) (by omega) (by omega)
      have h3 : N < (m + 1) ^ e := by rw [← hN]; exact hstrict
      have h5 : (intRoot e N) ^ e < (m + 1) ^ e := Nat.lt_of_le_of_lt hle2 h3
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle h5)
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp h2) h1
  refine Finset.mem_image.mpr ⟨e, ?_, hroot⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [Finset.mem_range]
    omega
  · rw [hroot]
    exact ⟨he, hm, hN⟩

theorem perfectPowerDivisors_sound (N : ℕ) (d : ℕ) (hd : d ∈ perfectPowerDivisors N) :
    1 < d ∧ d < N ∧ d ∣ N := by
  obtain ⟨e, he, hroot⟩ := Finset.mem_image.mp hd
  have hprops := (Finset.mem_filter.mp he).2
  have h2 : 2 ≤ d := by rw [← hroot]; exact hprops.2.1
  have hpow : d ^ e = N := by rw [← hroot]; exact hprops.2.2
  have he2 : 2 ≤ e := hprops.1
  refine ⟨h2, ?_, ?_⟩
  · rw [← hpow]
    have hge : d ^ 2 ≤ d ^ e := pow_le_pow_same d 2 e (by omega) (by omega)
    calc d ^ e ≥ d ^ 2 := hge
      _ = d * d := by ring
      _ > d := by
        simpa using! Nat.mul_lt_mul_of_pos_left (show 1 < d by omega) (by omega : 0 < d)
  · rw [← hpow]
    refine ⟨d ^ (e - 1), ?_⟩
    have hde : d ^ e = d * d ^ (e - 1) := by
      have hp := pow_succ d (e - 1)
      rw [show e = e - 1 + 1 by omega, hp]
      exact mul_comm _ _
    exact hde

theorem evenDivisor_sound (N : ℕ) (d : ℕ) (hd : evenDivisor N = some d) :
    1 < d ∧ d < N ∧ d ∣ N := by
  rw [evenDivisor] at hd
  split at hd
  · have h2 : 2 = d := Option.some.inj hd
    subst h2
    exact ⟨by omega, by omega, by omega⟩
  · simp at hd

theorem perfectPowerDivisor_sound (N : ℕ) (d : ℕ) (hd : perfectPowerDivisor N = some d) :
    1 < d ∧ d < N ∧ d ∣ N := by
  rw [perfectPowerDivisor] at hd
  cases hex : perfectPowerExponent N with
  | none => simp [hex] at hd
  | some e =>
    have hmap : intRoot e N = d := by
      simp [hex] at hd
      exact hd
    have hdef : perfectPowerExponent N = some e := hex
    simp only [perfectPowerExponent] at hdef
    split at hdef
    · simp at hdef
    · rename_i hcard
      have hmin : (perfectPowerCandidates N).min'
          (Finset.card_ne_zero.mp (by omega)) = e := Option.some.inj hdef
      have hmem : e ∈ perfectPowerCandidates N := by
        rw [← hmin]
        exact Finset.min'_mem _ _
      have hmem2 : intRoot e N ∈ perfectPowerDivisors N :=
        Finset.mem_image.mpr ⟨e, hmem, rfl⟩
      rw [hmap] at hmem2
      exact perfectPowerDivisors_sound N d hmem2

theorem preprocessBitCost_le (N : ℕ) : preprocessBitCost N ≤ polyLogBound 1 4 N := by
  have hb : 1 ≤ orderBitLength N := by unfold orderBitLength; omega
  have h1 : orderBitLength N ≤ orderBitLength N + 1 := Nat.le_add_right _ _
  have h2 : orderBitLength N * (orderBitLength N + 1) * (orderBitLength N + 1)
      ≤ (orderBitLength N + 1) * (orderBitLength N + 1) * (orderBitLength N + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 (le_refl _)) (le_refl _)
  have h3 : (orderBitLength N + 1) * (orderBitLength N + 1) * (orderBitLength N + 1)
      = (orderBitLength N + 1) ^ 3 := by ring
  have h4 : (orderBitLength N + 1) ^ 3 ≤ (orderBitLength N + 1) ^ 4 :=
    pow_le_pow_same (orderBitLength N + 1) 3 4 (by omega) (by omega)
  have h5 : (orderBitLength N + 1) ^ 4 = 1 * (orderBitLength N + 1) ^ 4 := by ring
  unfold preprocessBitCost polyLogBound
  omega

theorem polyLogDominates (c d N : ℕ) (hc : 0 < c) (hd : 0 < d) :
    PolyLogDominates c d N := by
  refine ⟨hc, hd, ?_⟩
  have h1 : orderBitLength N ≤ orderBitLength N + 1 := Nat.le_add_right _ _
  have h2 : orderBitLength N + 1 ≤ (orderBitLength N + 1) ^ d := by
    have : (orderBitLength N + 1) ^ 1 ≤ (orderBitLength N + 1) ^ d :=
      pow_le_pow_same (orderBitLength N + 1) 1 d (by omega) hd
    simpa using! this
  have h3 : (orderBitLength N + 1) ^ d ≤ c * (orderBitLength N + 1) ^ d := by
    have h : (orderBitLength N + 1) ^ d * 1 ≤ (orderBitLength N + 1) ^ d * c :=
      Nat.mul_le_mul (le_refl _) hc
    simpa [mul_comm] using! h
  unfold polyLogBound
  omega

theorem primeDirectionWitness_of_prime (N : ℕ) [NeZero N] (hp : Nat.Prime N)
    (a : (ZMod N)ˣ) : PrimeDirectionWitness N a := by
  have hcard : Fintype.card (ZMod N)ˣ = N - 1 := by
    rw [ZMod.card_units_eq_totient]
    exact (Nat.totient_eq_iff_prime (by have := hp.two_le; omega)).mpr hp
  have hstep : a ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact orderOf_dvd_card
  unfold PrimeDirectionWitness
  rw [← hcard]
  exact hstep

theorem compositeCertificate_imp_notPrime (N d : ℕ) (h : CompositeCertificate N d) :
    ¬ Nat.Prime N := by
  intro hp
  obtain ⟨h1, h2, h3⟩ := h
  rcases hp.eq_one_or_self_of_dvd d h3 with h0 | h4
  · omega
  · omega

theorem localQft_ledger (n : ℕ) :
    GateCount (localProgramCircuit (localQFT n)) = localQftGateCount n ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 ∧
      localQftSpaceCost n = n := by
  have h := localQFT_exact_gate_counts_and_wires n
  refine ⟨h.2.2.2.1, h.2.2.2.2.1, rfl⟩

theorem modularOrder_ledger (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) :
    QueryCount (modularOrderCircuit N M a) = M * (M - 1) / 2 ∧
      GateCount (modularOrderCircuit N M a) = M * (M - 1) + 2 :=
  (modular_order_exact_query_macro_ledger N M a hM).2

theorem orderVerification_is_power (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (q : ℕ) :
    orderVerificationProduct N a q = a ^ q := orderVerificationProduct_eq_pow N a q

theorem euclidCounted_ledger (a b : ℕ) :
    (euclidCounted a b).1 = Nat.gcd a b ∧ (euclidCounted a b).2 ≤ b :=
  ⟨euclidCounted_gcd a b, euclidCounted_count a b⟩

theorem euclidBitCost_le_polyLog (N : ℕ) :
    euclidBitCost (orderBitLength N) ≤ polyLogBound 1 5 N := by
  have hb : 1 ≤ orderBitLength N := by unfold orderBitLength; omega
  have hsq : 2 * orderBitLength N + 1 ≤ (orderBitLength N + 1) ^ 2 := by
    have : (orderBitLength N + 1) ^ 2 = orderBitLength N * orderBitLength N
        + 2 * orderBitLength N + 1 := by ring
    omega
  unfold euclidBitCost euclidStepBound euclidStepCost schoolbookMulModCost polyLogBound
  have hfactor : (2 * orderBitLength N + 1) * (2 * orderBitLength N * orderBitLength N
      + orderBitLength N) = orderBitLength N * (2 * orderBitLength N + 1) ^ 2 := by ring
  rw [hfactor, one_mul]
  have h1 : orderBitLength N ≤ orderBitLength N + 1 := Nat.le_add_right _ _
  have h2 : (2 * orderBitLength N + 1) ^ 2 ≤ (orderBitLength N + 1) ^ 4 := by
    have h3 : (2 * orderBitLength N + 1) ^ 2 ≤ ((orderBitLength N + 1) ^ 2) ^ 2 := by
      simpa [pow_two] using! Nat.mul_self_le_mul_self hsq
    rwa [pow_mul4] at h3
  have hmain : orderBitLength N * (2 * orderBitLength N + 1) ^ 2
      ≤ (orderBitLength N + 1) ^ 5 := by
    calc orderBitLength N * (2 * orderBitLength N + 1) ^ 2
        ≤ orderBitLength N * (orderBitLength N + 1) ^ 4 := Nat.mul_le_mul (le_refl _) h2
      _ ≤ (orderBitLength N + 1) * (orderBitLength N + 1) ^ 4 := by
          gcongr
      _ = (orderBitLength N + 1) ^ 5 := pow_mul5 _
  exact hmain

theorem attemptLedgerBound_ge_rejected (N M k : ℕ) :
    (rejectedLedger k).bits ≤ (attemptLedgerBound N M k).bits ∧
      (rejectedLedger k).queries ≤ (attemptLedgerBound N M k).queries ∧
      (rejectedLedger k).gates ≤ (attemptLedgerBound N M k).gates ∧
      (rejectedLedger k).space ≤ (attemptLedgerBound N M k).space := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rejectedLedger, attemptLedgerBound]
    omega
  · simp only [rejectedLedger, attemptLedgerBound]
    omega
  · simp only [rejectedLedger, attemptLedgerBound]
    omega
  · simp only [rejectedLedger, attemptLedgerBound]
    omega

theorem attemptOutcomeFactor_classical_sound (N M : ℕ) [NeZero N] (y : ZMod N)
    (d : ℕ) (h : attemptOutcomeFactor N M (.classicalGcd y) = some d) :
    1 < d ∧ d < N ∧ d ∣ N := by
  simp only [attemptOutcomeFactor] at h
  split at h
  · cases h
    exact ⟨by omega, by omega, (Nat.gcd_dvd _ _).1⟩
  · simp at h

theorem attemptOutcomeFactor_quantum_sound (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (yz : Fin M × Fin M) (d : ℕ)
    (h : attemptOutcomeFactor N M (.quantumOrder a yz) = some d) :
    1 < d ∧ d < N ∧ d ∣ N := by
  simp only [attemptOutcomeFactor] at h
  cases hq : (cfPairLCMOrderDecode N M a yz).1 with
  | none => simp [hq] at h
  | some q =>
    have hbind : (cfPairLCMOrderDecode N M a yz).1.bind (orderFactor N a) = some d := h
    rw [hq, Option.bind_some] at hbind
    exact orderFactor_sound N a q d hbind

theorem attemptOutcomeFactor_sound (N M : ℕ) [NeZero N] (t : AttemptOutcome N M)
    (d : ℕ) (h : attemptOutcomeFactor N M t = some d) :
    1 < d ∧ d < N ∧ d ∣ N := by
  cases t with
  | rejected => simp [attemptOutcomeFactor] at h
  | classicalGcd y => exact attemptOutcomeFactor_classical_sound N M y d h
  | quantumOrder a yz => exact attemptOutcomeFactor_quantum_sound N M a yz d h

theorem firstSuccessAt_sound (N M R : ℕ) [NeZero N] (ω : Fin R → AttemptOutcome N M)
    (j : Fin R) (h : firstSuccessAt (N := N) (M := M) (R := R) ω j) :
    (attemptOutcomeFactor N M (ω j)).isSome ∧
      ∀ d : ℕ, attemptOutcomeFactor N M (ω j) = some d → 1 < d ∧ d < N ∧ d ∣ N := by
  refine ⟨h.1, ?_⟩
  intro d hd
  exact attemptOutcomeFactor_sound N M (ω j) d hd

theorem factorTreeOfFuel_spec (split : ∀ n, Option (ProperDivisor n)) :
    ∀ fuel n, n ≤ fuel →
      (∀ m, 2 ≤ m → m ≤ n → ∀ h : ¬Nat.Prime m, split m ≠ none) →
      (factorTreeOfFuel split fuel n).leavesProduct = n ∧
        (factorTreeOfFuel split fuel n).root = n ∧
        (∀ p ∈ (factorTreeOfFuel split fuel n).leaves, p ≤ 1 ∨ Nat.Prime p) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hne
    have hz : n = 0 := by omega
    subst hz
    simp [factorTreeOfFuel, FactorTree.leavesProduct, FactorTree.leaves, FactorTree.root]
  | succ fuel ih =>
    intro n hfuel hne
    cases n with
    | zero =>
      simp [factorTreeOfFuel, FactorTree.leavesProduct, FactorTree.leaves, FactorTree.root]
    | succ n =>
      rw [factorTreeOfFuel]
      cases hsplit : split (n + 1) with
      | none =>
        refine ⟨?_, ?_, ?_⟩
        · simp [FactorTree.leavesProduct, FactorTree.root]
        · simp [FactorTree.root]
        · intro p hp
          have hp' : p = n + 1 := by simpa [FactorTree.leaves] using! hp
          subst hp'
          by_cases hle : n + 1 ≤ 1
          · exact Or.inl hle
          · refine Or.inr ?_
            have h2le : 2 ≤ n + 1 := by omega
            by_contra hnp
            have h1 : split (n + 1) = none := hsplit
            have h2 : split (n + 1) ≠ none := hne (n + 1) h2le (by omega) hnp
            exact absurd h1 h2
      | some pd =>
        have hlt : pd.d < n + 1 := pd.proof.2.1
        have hneD : ∀ m, 2 ≤ m → m ≤ pd.d → ∀ h : ¬Nat.Prime m, split m ≠ none :=
          fun m hm2 hm h => hne m hm2 (by omega) h
        have hdiv : pd.d ∣ n + 1 := pd.proof.2.2
        have hcoef : (n + 1) / pd.d < n + 1 := by
          have hd2 : 2 ≤ pd.d := pd.proof.1
          exact Nat.div_lt_self (by omega) (by omega)
        have hneC : ∀ m, 2 ≤ m → m ≤ (n + 1) / pd.d → ∀ h : ¬Nat.Prime m, split m ≠ none :=
          fun m hm2 hm h => hne m hm2 (by omega) h
        have hfuelD : pd.d ≤ fuel := by omega
        have hfuelC : (n + 1) / pd.d ≤ fuel := by omega
        have hL := ih pd.d hfuelD hneD
        have hR := ih ((n + 1) / pd.d) hfuelC hneC
        refine ⟨?_, ?_, ?_⟩
        · simp only [FactorTree.leavesProduct]
          rw [hL.1, hR.1]
          exact ((Nat.div_mul_cancel hdiv).symm.trans (Nat.mul_comm _ _)).symm
        · simp [FactorTree.root]
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hL.2.2 p hp
          · exact hR.2.2 p hp

theorem factorTreeOf_complete (split : ∀ n, Option (ProperDivisor n)) :
    ∀ n, (∀ m, 2 ≤ m → m ≤ n → ∀ h : ¬Nat.Prime m, split m ≠ none) →
      (factorTreeOf split n).complete := by
  intro n hne
  have h := factorTreeOfFuel_spec split n n (by omega) hne
  unfold factorTreeOf
  refine ⟨?_, ?_⟩
  · rw [h.1, h.2.1]
  · exact h.2.2

theorem compiledMeasurement_matrix_eq {Ω H : Type} [Fintype Ω] [Fintype H]
    (V : Matrix H Ω ℂ) (T : Matrix Ω Ω ℂ) (hV : ComputationIsometry V) :
    (V * T * Vᴴ) * V = V * T := by
  rw [Matrix.mul_assoc, hV, Matrix.mul_one]

theorem compiledMeasurement_action_eq {Ω H : Type} [Fintype Ω] [Fintype H]
    (V : Matrix H Ω ℂ) (T : Matrix Ω Ω ℂ) (φ : QState H) :
    (V * T * Vᴴ) *ᵥ φ = V *ᵥ (T *ᵥ (Vᴴ *ᵥ φ)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem orbitFourier_isometry (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] :
    (orbitFourierMatrix G)ᴴ * orbitFourierMatrix G = (1 : Matrix G G ℂ) :=
  Qatlib.Concepts.WalshMoment.Forrelation.fourierMatrix_conjTranspose_mul

theorem compactRecordWidth_bound (m : ℕ) (hm : m ≠ 0) : m ≤ 2 ^ compactRecordWidth m := by
  unfold compactRecordWidth
  have h2 := (Nat.log_lt_iff_lt_pow Nat.one_lt_two hm).mp
    (by omega : Nat.log 2 m < Nat.log 2 m + 1)
  omega

theorem pow_two_mul (x b : ℕ) : (x ^ b) ^ 2 = x ^ (2 * b) := by
  calc (x ^ b) ^ 2 = x ^ b * x ^ b := by rw [pow_succ, pow_one]
    _ = x ^ (b + b) := by rw [Nat.pow_add]
    _ = x ^ (2 * b) := by congr 1; omega

theorem originalClockWindow_exists (N : ℕ) (hN : 1 < N) :
    ∃ q, OriginalClockWindow N q := by
  have hex : ∃ t, N ^ 2 ≤ 2 ^ t := by
    refine ⟨2 * orderBitLength N, ?_⟩
    have h1 : N < 2 ^ orderBitLength N := lt_two_pow_orderBitLength N
    have h2 : N ^ 2 < (2 ^ orderBitLength N) ^ 2 :=
      pow_lt_pow_of_lt_base N (2 ^ orderBitLength N) 2 h1 (by norm_num) (by omega)
    have h3 : (2 ^ orderBitLength N) ^ 2 = 2 ^ (2 * orderBitLength N) :=
      pow_two_mul _ _
    omega
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ¬ (N ^ 2 ≤ 2 ^ m) := fun m hm => Nat.find_min hex hm
  refine ⟨2 ^ Nat.find hex, Nat.find hex, rfl, hspec, ?_⟩
  have ht1 : 1 ≤ Nat.find hex := by
    by_contra hc
    have hz : Nat.find hex = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hc)
    have hp0 := (Nat.find_eq_iff hex).mp hz |>.1
    simp at hp0
    omega
  have hprev : 2 ^ (Nat.find hex - 1) < N ^ 2 := by
    have hcontra := hmin (Nat.find hex - 1) (by omega)
    omega
  have h2t : 2 ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
    have hp := pow_succ 2 (Nat.find hex - 1)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hp
    exact ((mul_comm _ _).trans hp.symm).symm
  rw [h2t]
  have hlt : 2 * 2 ^ (Nat.find hex - 1) < 2 * N ^ 2 :=
    (Nat.mul_lt_mul_left (by omega : (0:ℕ) < 2)).mpr hprev
  omega

theorem orderGoodMass_pos (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (hN : 1 < N) (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M) :
    0 < orderGoodMass N M a hM := by
  have h := modular_order_actual_verified_success_lower_bound N M a hM hN hr hsize
  have hpos0 : (0:ℕ) < orderOf a := by
    have := orderOf_pos a
    omega
  have hφ : 0 < (Nat.totient (orderOf a) : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hpos0)
  have hr' : (0:ℝ) < (orderOf a : ℝ) := by
    exact_mod_cast hpos0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : 0 < (8 / Real.pi ^ 2) * (Nat.totient (orderOf a) : ℝ) / (orderOf a : ℝ) := by
    positivity
  have hbound : orderGoodMass N M a hM
      ≥ 8 / Real.pi ^ 2 * (Nat.totient (orderOf a) : ℝ) / (orderOf a : ℝ) := by
    simpa [orderGoodMass, OrderGoodEvent] using! h
  exact lt_of_lt_of_le hpos hbound

noncomputable def orderConditionalLaw (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (hpos : 0 < orderGoodMass N M a hM) : FinDist (Fin M) where
  prob := fun y =>
    if OrderGoodEvent N M a y then
      (modularOrderLaw N M a hM).prob y / orderGoodMass N M a hM
    else 0
  nonneg := by
    intro y
    by_cases h : OrderGoodEvent N M a y
    · simp only [h, if_pos]
      exact div_nonneg ((modularOrderLaw N M a hM).nonneg y) (le_of_lt hpos)
    · simp only [h, if_neg]
      exact le_rfl
  sum_one := by
    classical
    have hsum : (∑ y : Fin M, (if OrderGoodEvent N M a y then
        (modularOrderLaw N M a hM).prob y / orderGoodMass N M a hM else 0)) = 1 := by
      rw [← Finset.sum_filter, ← Finset.sum_div]
      have hdef : Finset.sum (Finset.univ.filter (fun y : Fin M => OrderGoodEvent N M a y))
          (fun y => (modularOrderLaw N M a hM).prob y) = orderGoodMass N M a hM := rfl
      rw [hdef]
      exact div_self (ne_of_gt hpos)
    exact hsum

theorem orderConditionalLaw_prob_eq_zero (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (hpos : 0 < orderGoodMass N M a hM) (y : Fin M)
    (hy : ¬ OrderGoodEvent N M a y) :
    (orderConditionalLaw N M a hM hpos).prob y = 0 := by
  simp [orderConditionalLaw, hy]

theorem orderConditionalLaw_prob_eq (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (hpos : 0 < orderGoodMass N M a hM) (y : Fin M)
    (hy : OrderGoodEvent N M a y) :
    (orderConditionalLaw N M a hM hpos).prob y
      = (modularOrderLaw N M a hM).prob y / orderGoodMass N M a hM := by
  simp [orderConditionalLaw, hy]

theorem smallPrimePowers_dvd (m : ℕ) (w : ℕ) (hw : w ∈ smallPrimePowers m) : w ∣ m := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
  exact (Finset.mem_filter.mp hp).2.2.1

def clause2_endpoint : Prop :=
  (∀ (c d N : ℕ), 0 < c → 0 < d → PolyLogDominates c d N) ∧
  (∀ (N d : ℕ), evenDivisor N = some d → 1 < d ∧ d < N ∧ d ∣ N) ∧
  (∀ (N d : ℕ), d ∈ perfectPowerDivisors N → 1 < d ∧ d < N ∧ d ∣ N) ∧
  (∀ (N d : ℕ), perfectPowerDivisor N = some d → 1 < d ∧ d < N ∧ d ∣ N) ∧
  (∀ N : ℕ, preprocessBitCost N ≤ polyLogBound 1 4 N) ∧
  (∀ (N : ℕ) [NeZero N] (hp : Nat.Prime N) (a : (ZMod N)ˣ), PrimeDirectionWitness N a) ∧
  (∀ (N d : ℕ), CompositeCertificate N d → ¬ Nat.Prime N)

theorem clause2_endpoint_holds : clause2_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d N hc hd
    exact polyLogDominates c d N hc hd
  · exact evenDivisor_sound
  · exact perfectPowerDivisors_sound
  · exact perfectPowerDivisor_sound
  · exact preprocessBitCost_le
  · intro N _ hp a
    exact primeDirectionWitness_of_prime N hp a
  · exact compositeCertificate_imp_notPrime

def clause3_endpoint : Prop :=
  (∀ n : ℕ, GateCount (localProgramCircuit (localQFT n)) = localQftGateCount n ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 ∧
      localQftSpaceCost n = n) ∧
  (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M),
      QueryCount (modularOrderCircuit N M a) = M * (M - 1) / 2 ∧
        GateCount (modularOrderCircuit N M a) = M * (M - 1) + 2) ∧
  (∀ (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (q : ℕ),
      orderVerificationProduct N a q = a ^ q) ∧
  (∀ (a b : ℕ), (euclidCounted a b).1 = Nat.gcd a b ∧ (euclidCounted a b).2 ≤ b) ∧
  (∀ N : ℕ, euclidBitCost (orderBitLength N) ≤ polyLogBound 1 5 N) ∧
  (∀ (N M k : ℕ), (rejectedLedger k).bits ≤ (attemptLedgerBound N M k).bits ∧
      (rejectedLedger k).queries ≤ (attemptLedgerBound N M k).queries ∧
      (rejectedLedger k).gates ≤ (attemptLedgerBound N M k).gates ∧
      (rejectedLedger k).space ≤ (attemptLedgerBound N M k).space)

theorem clause3_endpoint_holds : clause3_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact localQft_ledger
  · exact modularOrder_ledger
  · intro N _ a q
    exact orderVerification_is_power N a q
  · exact euclidCounted_ledger
  · exact euclidBitCost_le_polyLog
  · exact attemptLedgerBound_ge_rejected

def clause4_endpoint : Prop :=
  (∀ (N M : ℕ) [NeZero N] (t : AttemptOutcome N M) (d : ℕ),
      attemptOutcomeFactor N M t = some d → 1 < d ∧ d < N ∧ d ∣ N) ∧
  (∀ (N M R : ℕ) [NeZero N] (ω : Fin R → AttemptOutcome N M) (j : Fin R),
      firstSuccessAt (N := N) (M := M) (R := R) ω j →
        (attemptOutcomeFactor N M (ω j)).isSome ∧
          ∀ d : ℕ, attemptOutcomeFactor N M (ω j) = some d →
            1 < d ∧ d < N ∧ d ∣ N) ∧
  (∀ (split : ∀ n, Option (ProperDivisor n)) (n : ℕ),
      (∀ m, 2 ≤ m → m ≤ n → ∀ h : ¬Nat.Prime m, split m ≠ none) →
        (factorTreeOf split n).complete)

theorem clause4_endpoint_holds : clause4_endpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro N M _ t d h
    exact attemptOutcomeFactor_sound N M t d h
  · intro N M R _ ω j h
    exact firstSuccessAt_sound N M R ω j h
  · intro split n hne
    exact factorTreeOf_complete split n hne

def clause5_endpoint : Prop :=
  (∀ (Ω H : Type) [Fintype Ω] [Fintype H] (V : Matrix H Ω ℂ) (T : Matrix Ω Ω ℂ),
      ComputationIsometry V → (V * T * Vᴴ) * V = V * T) ∧
  (∀ (Ω H : Type) [Fintype Ω] [Fintype H] (V : Matrix H Ω ℂ) (T : Matrix Ω Ω ℂ)
      (φ : QState H),
      (V * T * Vᴴ) *ᵥ φ = V *ᵥ (T *ᵥ (Vᴴ *ᵥ φ))) ∧
  (∀ (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G],
      (orbitFourierMatrix G)ᴴ * orbitFourierMatrix G = (1 : Matrix G G ℂ)) ∧
  (∀ m : ℕ, m ≠ 0 → m ≤ 2 ^ compactRecordWidth m)

theorem clause5_endpoint_holds : clause5_endpoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Ω H _ _ V T hV
    exact compiledMeasurement_matrix_eq V T hV
  · intro Ω H _ _ V T φ
    exact compiledMeasurement_action_eq V T φ
  · intro G
    exact orbitFourier_isometry G
  · intro m hm
    exact compactRecordWidth_bound m hm

def clause6_endpoint : Prop :=
  (∀ N : ℕ, 1 < N → ∃ q, OriginalClockWindow N q) ∧
  (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) (hN : 1 < N)
      (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M),
      0 < orderGoodMass N M a hM) ∧
  (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) (hN : 1 < N)
      (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M) (y : Fin M),
      (orderConditionalLaw N M a hM (orderGoodMass_pos N M a hM hN hr hsize)).prob y
        = if OrderGoodEvent N M a y then
            (modularOrderLaw N M a hM).prob y / orderGoodMass N M a hM else 0) ∧
  (∀ m w : ℕ, w ∈ smallPrimePowers m → w ∣ m)

theorem clause6_endpoint_holds : clause6_endpoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N hN
    exact originalClockWindow_exists N hN
  · intro N M _ a hM hN hr hsize
    exact orderGoodMass_pos N M a hM hN hr hsize
  · intro N M _ a hM hN hr hsize y
    by_cases hy : OrderGoodEvent N M a y
    · rw [orderConditionalLaw_prob_eq N M a hM _ y hy]
      simp [hy]
    · rw [orderConditionalLaw_prob_eq_zero N M a hM _ y hy]
      simp [hy]
  · intro m w hw
    exact smallPrimePowers_dvd m w hw

end Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder
