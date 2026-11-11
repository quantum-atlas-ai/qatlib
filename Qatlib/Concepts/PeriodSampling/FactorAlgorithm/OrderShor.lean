/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueFairBitSamplerShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessingShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueFactoringAlgorithmShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.SampledAttemptSuccessShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueGcdBranchShor
import Qatlib.Concepts.PeriodSampling.OrderRecovery.PairLCMOrderRecovery
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation

/-!
# Order-finding implementation bounds and contract checks

Proves residue-sampling identities, binary arithmetic correctness, modular-exponentiation costs,
Euclidean gcd correctness, and factoring receipt bounds in the framework associated with
[Shor1997]. The grouped results `g1`, `g3`, and `g4` collect sampling, arithmetic, Fourier, and
factoring guarantees.

The module also checks the exact strength of machine and conditional-sampling predicates. It
proves that unrestricted configuration readouts satisfy the formal search and decision
predicates, refutes the stated `clause2` conjunction, and gives a positive-mass bad
discrete-logarithm outcome refuting the unfiltered good-conditional contract.

## Main statements

* `g1`: Collects exact residue-sampling probabilities and bit-cost bounds.
* `g3`: Collects arithmetic, Fourier, continued-fraction, and gcd statements.
* `g4`: Collects attempt ledgers, sound receipts, and factor-tree existence.
* `unfiltered_dlog_conditional_false`: Refutes the unfiltered good-conditional predicate.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm.Shor1997

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib.Concepts.RiskEstimation.PopulationGap Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.PeriodSampling.DlogDivBudget Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm.Shor1997
open Matrix
open scoped ENNReal NNReal Classical

/-- The canonical map from `Fin N` to `ZMod N` is injective when `N` is nonzero. -/
theorem fin_coe_zmod_injective (N : ℕ) [NeZero N] :
    Function.Injective (fun i : Fin N => (i : ZMod N)) := by
  intro i j hij
  apply Fin.ext
  have key := congrArg ZMod.val hij
  rwa [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at key

/-- Every residue modulo nonzero `N` has a unique representative in `Fin N`. -/
theorem exists_fin_coe_zmod (N : ℕ) [NeZero N] (y : ZMod N) :
    ∃! i : Fin N, (i : ZMod N) = y := by
  refine ⟨⟨y.val, ZMod.val_lt y⟩, ZMod.natCast_zmod_val y, ?_⟩
  intro i hi
  exact fin_coe_zmod_injective N (hi.trans (ZMod.natCast_zmod_val y).symm)

/-- The mass of returning residue `y` under `nativeResidueRun` equals the mass of returning its
canonical finite representative under `finiteCoinRun`. -/
theorem nativeResidueRun_event_inl (N k fuel : ℕ) [NeZero N] (y : ZMod N) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeResidueRun N k fuel) (fun x => x.1 = Sum.inl y)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k N fuel)
          (fun x => x.1 = Sum.inl (⟨y.val, ZMod.val_lt y⟩ : Fin N)) := by
  have hmap : nativeResidueRun N k fuel
      = (finiteCoinRun k N fuel).map
          fun x => (Sum.elim (fun i : Fin N => Sum.inl ((i : ZMod N)))
            (fun _ : Unit => Sum.inr ()) x.1, x.2) := rfl
  rw [hmap, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  intro x
  rcases x with ⟨c, n⟩
  cases c with
  | inl i =>
      constructor
      · intro h
        have hinj : (Sum.inl ((i : ZMod N)) : Sum (ZMod N) Unit) = Sum.inl y := h
        have hi : ((i : ZMod N)) = y := Sum.inl.inj hinj
        have heq : (i : Fin N) = (⟨y.val, ZMod.val_lt y⟩ : Fin N) :=
          fin_coe_zmod_injective N (hi.trans (ZMod.natCast_zmod_val y).symm)
        exact congrArg Sum.inl heq
      · intro h
        have heq : (i : Fin N) = (⟨y.val, ZMod.val_lt y⟩ : Fin N) := Sum.inl.inj h
        subst heq
        exact congrArg Sum.inl (ZMod.natCast_zmod_val y)
  | inr u =>
      cases u
      constructor <;> intro h <;> exact absurd h (fun he => Sum.inl_ne_inr he.symm)

/-- The failure mass of the native residue sampler equals the failure mass of its finite-coin
sampler. -/
theorem nativeResidueRun_event_inr (N k fuel : ℕ) [NeZero N] :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeResidueRun N k fuel) (fun x => x.1 = Sum.inr ())
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k N fuel) (fun x => x.1 = Sum.inr ()) := by
  have hmap : nativeResidueRun N k fuel
      = (finiteCoinRun k N fuel).map
          fun x => (Sum.elim (fun i : Fin N => Sum.inl ((i : ZMod N)))
            (fun _ : Unit => Sum.inr ()) x.1, x.2) := rfl
  rw [hmap, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  intro x
  rcases x with ⟨c, n⟩
  cases c with
  | inl i =>
      constructor <;> intro h <;> exact absurd h (fun he => Sum.inl_ne_inr he)
  | inr u =>
      cases u
      constructor <;> intro h <;> rfl

/-- With sufficient bit capacity, the native residue sampler's expected cost is `k` times the
finite geometric sum of rejection probabilities. -/
theorem nativeResidueRun_expectedCost (N k fuel : ℕ) [NeZero N] (hk : N ≤ 2 ^ k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (nativeResidueRun N k fuel)
      = ((k : ℕ) : ℝ≥0∞) * ∑ n ∈ Finset.range fuel, (coinRejectMass k N) ^ n := by
  have hmap : nativeResidueRun N k fuel
      = (finiteCoinRun k N fuel).map
          fun x => (Sum.elim (fun i : Fin N => Sum.inl ((i : ZMod N)))
            (fun _ : Unit => Sum.inr ()) x.1, x.2) := rfl
  have hcost : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (nativeResidueRun N k fuel)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (finiteCoinRun k N fuel) := by
    rw [hmap, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro x
    rfl
  rw [hcost]
  exact (finite_coin_actual_bit_cost k N fuel hk).2

/-- With sufficient bit capacity, the native residue sampler is bounded by
`nativeResidueBitBudget k fuel`. -/
theorem nativeResidueRun_bounded (N k fuel : ℕ) [NeZero N] (hk : N ≤ 2 ^ k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (nativeResidueRun N k fuel) (nativeResidueBitBudget k fuel) := by
  have hmap : nativeResidueRun N k fuel
      = (finiteCoinRun k N fuel).map
          fun x => (Sum.elim (fun i : Fin N => Sum.inl ((i : ZMod N)))
            (fun _ : Unit => Sum.inr ()) x.1, x.2) := rfl
  intro x hx
  rw [hmap] at hx
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  have hy2 := (finite_coin_actual_bit_cost k N fuel hk).1 y hy
  simpa [nativeResidueBitBudget] using! hy2

/-- The chosen residue bit width brackets positive `N` between its power of two and half that
power, and gives rejection mass at most one half. -/
theorem shorResidueBits_window_le_half (N : ℕ) (hN : 0 < N) :
    N ≤ 2 ^ shorResidueBits N ∧ 2 ^ shorResidueBits N < 2 * N ∧
      coinRejectMass (shorResidueBits N) N ≤ 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := residue_bit_width_window N hN
  refine ⟨hlo, hhi, ?_⟩
  have hle : 2 * (2 ^ shorResidueBits N - N) ≤ 2 ^ shorResidueBits N := by
    have h2N : 2 ^ shorResidueBits N ≤ 2 * N := by omega
    omega
  have hle' : (2 ^ shorResidueBits N - N) * 2 ≤ 2 ^ shorResidueBits N := by omega
  have key : ((2 ^ shorResidueBits N - N : ℕ) : ℝ≥0∞) * ((2 : ℕ) : ℝ≥0∞)
      ≤ ((2 ^ shorResidueBits N : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul]
    exact Nat.cast_le.mpr hle'
  have hk0 : ((2 ^ shorResidueBits N : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hktop : ((2 ^ shorResidueBits N : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hne2 : (((2 : ℕ) : ℝ≥0∞)) ≠ 0 := by simp
  have hnetop2 : (((2 : ℕ) : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top 2
  have htwo : ((2 : ℝ≥0∞)) = ((2 : ℕ) : ℝ≥0∞) := by simp
  rw [coinRejectMass, ENNReal.div_le_iff hk0 hktop, div_eq_mul_inv, htwo, one_mul, mul_comm]
  have hmul := mul_le_mul_left key (((2 : ℕ) : ℝ≥0∞)⁻¹)
  rw [mul_assoc, ENNReal.mul_inv_cancel hne2 hnetop2, mul_one] at hmul
  exact hmul

/-- Collects exact residue output and failure masses, bounded and expected bit costs, the
chosen-width rejection bound, and the fair-bit residue sampler contract in the framework of
[Shor1997]. -/
theorem g1 :

  (∀ (N k fuel : ℕ) [NeZero N] (_hk : N ≤ 2 ^ k) (y : ZMod N),
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeResidueRun N k fuel) (fun x => x.1 = Sum.inl y)
      = (1 - (coinRejectMass k N) ^ fuel) / (N : ℝ≥0∞)) ∧

  (∀ (N k fuel : ℕ) [NeZero N] (_hk : N ≤ 2 ^ k),
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeResidueRun N k fuel) (fun x => x.1 = Sum.inr ())
      = (coinRejectMass k N) ^ fuel) ∧

  (∀ (N k fuel : ℕ) [NeZero N] (_hk : N ≤ 2 ^ k),
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (nativeResidueRun N k fuel) (nativeResidueBitBudget k fuel) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (nativeResidueRun N k fuel)
        = ((k : ℕ) : ℝ≥0∞) * ∑ n ∈ Finset.range fuel, (coinRejectMass k N) ^ n) ∧

  (∀ N : ℕ, 0 < N →
    N ≤ 2 ^ shorResidueBits N ∧ 2 ^ shorResidueBits N < 2 * N ∧
      coinRejectMass (shorResidueBits N) N ≤ 1 / 2) ∧

  (Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueFairBitSampler)
:= by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N k fuel hinst _hk y
    rw [nativeResidueRun_event_inl]
    exact (finite_coin_return_and_pending k N fuel (NeZero.pos N) _hk).2 _
  · intro N k fuel hinst _hk
    rw [nativeResidueRun_event_inr]
    exact (finite_coin_return_and_pending k N fuel (NeZero.pos N) _hk).1
  · intro N k fuel hinst _hk
    exact ⟨nativeResidueRun_bounded N k fuel _hk,
      nativeResidueRun_expectedCost N k fuel _hk⟩
  · intro N hN
    exact shorResidueBits_window_le_half N hN
  · exact Qatlib.Concepts.PeriodSampling.FactorAlgorithm.residueFairBitSampler

/-- The value of a list of bits in little-endian order, with the head contributing the least
significant bit. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * bitsValue rest

/-- The recursive little-endian bit value equals the corresponding right fold. -/
theorem bitsValue_eq_foldr : ∀ (l : List Bool),
    bitsValue l = l.foldr (fun b v => (if b then 1 else 0) + 2 * v) 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons b l ih => simp [bitsValue, ih]

/-- Adding the `i`th binary digit to `e % 2 ^ i` gives `e % 2 ^ (i + 1)`. -/
theorem bit_expansion (e i : ℕ) :
    e % 2 ^ i + (if e.testBit i then 1 else 0) * 2 ^ i = e % 2 ^ (i + 1) := by
  rw [Nat.mod_pow_succ (b := 2)]
  have h2 : ∀ m : ℕ, (m % 2 = 0) ∨ (m % 2 = 1) := by intro m; omega
  have htb : e.testBit i = decide (e / 2 ^ i % 2 = 1) := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
    rcases h2 (e / 2 ^ i) with h | h <;> rw [h] <;> simp
  rw [htb]
  rcases h2 (e / 2 ^ i) with h | h <;> simp [h]

/-- Folding the first `n` test bits of `e` with terminal value `z` gives `e % 2 ^ n + 2 ^ n *
z`. -/
theorem foldr_bits : ∀ (e n z : ℕ),
    ((List.range n).map (e.testBit)).foldr (fun b v => (if b then 1 else 0) + 2 * v) z
      = e % 2 ^ n + 2 ^ n * z := by
  intro e n z
  induction n generalizing z with
  | zero =>
      simp [Nat.mod_one]
  | succ n ih =>
      have hmap : (List.range (n + 1)).map (e.testBit)
          = (List.range n).map (e.testBit) ++ [e.testBit n] := by
        rw [List.range_succ, List.map_append]
        simp
      rw [hmap, List.foldr_append, ih]
      show e % 2 ^ n + 2 ^ n * ((fun b v => (if b then 1 else 0) + 2 * v) (e.testBit n) z)
          = e % 2 ^ (n + 1) + 2 ^ (n + 1) * z
      calc e % 2 ^ n + 2 ^ n * ((if e.testBit n then 1 else 0) + 2 * z)
          = (e % 2 ^ n + (if e.testBit n then 1 else 0) * 2 ^ n) + 2 ^ n * (2 * z) := by
              rw [mul_add, mul_comm (2 ^ n) ((if e.testBit n then 1 else 0))]
              abel
        _ = e % 2 ^ (n + 1) + 2 ^ n * (2 * z) := by rw [bit_expansion e n]
        _ = e % 2 ^ (n + 1) + 2 ^ (n + 1) * z := by
              rw [← mul_assoc, ← Nat.pow_succ]

/-- The value of the first `n` test bits of `e` is `e % 2 ^ n`. -/
theorem bitsValue_range (e n : ℕ) :
    bitsValue ((List.range n).map (e.testBit)) = e % 2 ^ n := by
  rw [bitsValue_eq_foldr, foldr_bits]
  simp

/-- Computes the square register, accumulated result, and exact charged multiplication cost
after folding modular-exponentiation steps over a bit list. -/
theorem modExpCostedStep_foldl (N : ℕ) (hN : 0 < N) :
    ∀ (l : List Bool) (sq res cst : ℕ),
      sq < N → res < N →
      (l.foldl (modExpCostedStep N) (sq, res, cst)).1 = (sq ^ (2 ^ l.length)) % N ∧
      (l.foldl (modExpCostedStep N) (sq, res, cst)).2.1 = (res * sq ^ bitsValue l) % N ∧
      (l.foldl (modExpCostedStep N) (sq, res, cst)).2.2 =
        cst + (l.length + l.count true) * schoolbookMulModBitCost (shorBitLength N) := by
  intro l
  induction l with
  | nil =>
      intro sq res cst hsq hres
      refine ⟨?_, ?_, ?_⟩
      · show sq = (sq ^ (2 ^ 0)) % N
        rw [pow_zero, pow_one, Nat.mod_eq_of_lt hsq]
      · show res = (res * sq ^ bitsValue []) % N
        rw [show bitsValue [] = 0 from rfl, pow_zero, mul_one, Nat.mod_eq_of_lt hres]
      · show cst = cst + (List.length [] + List.count true []) * _
        simp
  | cons b l ih =>
      intro sq res cst hsq hres
      rw [show (b :: l).foldl (modExpCostedStep N) (sq, res, cst)
          = l.foldl (modExpCostedStep N) (modExpCostedStep N (sq, res, cst) b) from rfl]
      set s := (sq * sq % N) with hs
      set r := (if b then res * sq % N else res) with hr
      set c := cst + (if b then 2 else 1) * schoolbookMulModBitCost (shorBitLength N) with hc
      have hacc : modExpCostedStep N (sq, res, cst) b = (s, r, c) := by
        simp only [modExpCostedStep, hs, hr, hc]
      rw [hacc]
      have hsq' : s < N := by rw [hs]; exact Nat.mod_lt _ hN
      have hres' : r < N := by
        rw [hr]
        cases b with
        | true => exact Nat.mod_lt _ hN
        | false => simpa using! hres
      obtain ⟨h1, h2, h3⟩ := ih s r c hsq' hres'
      have hcore : (sq * sq % N) ^ (2 ^ l.length) % N = sq ^ (2 ^ (l.length + 1)) % N := by
        have e : (sq * sq % N) ^ (2 ^ l.length) ≡ (sq * sq) ^ (2 ^ l.length) [MOD N] :=
          (Nat.mod_modEq (sq * sq) N).pow _
        refine Eq.trans e ?_
        rw [← pow_two, ← Nat.pow_mul]
        rw [show 2 * 2 ^ l.length = 2 ^ (l.length + 1) by rw [Nat.pow_succ, mul_comm]]
      refine ⟨?_, ?_, ?_⟩
      · rw [h1, hs, hcore]
        rfl
      · rw [h2]
        show ((if b then res * sq % N else res) * (sq * sq % N) ^ bitsValue l) % N
            = (res * sq ^ bitsValue (b :: l)) % N
        rw [show bitsValue (b :: l) = (if b then 1 else 0) + 2 * bitsValue l from rfl]
        cases hb : b with
        | true =>
            simp only [if_true]
            have e : ((res * sq % N) * (sq * sq % N) ^ bitsValue l)
                ≡ ((res * sq) * (sq * sq) ^ bitsValue l) [MOD N] :=
              (Nat.mod_modEq _ _).mul ((Nat.mod_modEq (sq * sq) N).pow _)
            refine Eq.trans e ?_
            rw [← pow_two, ← Nat.pow_mul, Nat.pow_add, Nat.pow_one]
            ring_nf
        | false =>
            have e2 : (res * (sq * sq % N) ^ bitsValue l)
                ≡ (res * (sq * sq) ^ bitsValue l) [MOD N] :=
              (Nat.ModEq.refl _).mul ((Nat.mod_modEq (sq * sq) N).pow _)
            refine Eq.trans e2 ?_
            rw [← pow_two, ← Nat.pow_mul, Nat.pow_add]
            simp
      · rw [h3]
        show (cst + (if b then 2 else 1) * schoolbookMulModBitCost (shorBitLength N))
              + (l.length + l.count true) * schoolbookMulModBitCost (shorBitLength N)
            = cst + ((b :: l).length + (b :: l).count true) * schoolbookMulModBitCost (shorBitLength N)
        cases b <;> simp [List.count, List.length] <;> ring_nf

/-- The modular-exponentiation bit list has length `Nat.log2 e + 1`. -/
theorem modExpBits_length (e : ℕ) : (modExpBits e).length = Nat.log2 e + 1 := by
  simp [modExpBits]

/-- The modular-exponentiation bit list has little-endian value `e`. -/
theorem modExpBits_value (e : ℕ) : bitsValue (modExpBits e) = e := by
  rw [show modExpBits e = (List.range (Nat.log2 e + 1)).map (e.testBit) from rfl]
  have h := foldr_bits e (Nat.log2 e + 1) 0
  rw [← bitsValue_eq_foldr] at h
  rw [h]
  have hlt := Nat.lt_pow_succ_log_self (x := e) (by decide : 1 < (2 : ℕ))
  rw [← Nat.log2_eq_log_two] at hlt
  exact Nat.mod_eq_of_lt hlt

/-- For a positive modulus, the implemented modular-exponentiation result is `(a ^ e) % N`. -/
theorem modExpResult_eq (N a e : ℕ) (hN : 0 < N) :
    modExpResult N a e = (a ^ e) % N := by
  have hfold := modExpCostedStep_foldl N hN (modExpBits e) (a % N) (1 % N) 0
    (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
  show (modExpBits e).foldl (modExpCostedStep N) (a % N, 1 % N, 0) |>.2.1 = _
  rw [hfold.2.1, modExpBits_value]
  have e1 : (1 % N) ≡ (1 : ℕ) [MOD N] := Nat.mod_modEq _ _
  have e2 : ((a % N) ^ e) ≡ (a ^ e) [MOD N] := (Nat.mod_modEq a N).pow e
  refine Eq.trans (e1.mul e2) ?_
  rw [one_mul]

/-- The realized modular-exponentiation bit cost is the bit-list length plus its number of true
bits, multiplied by the schoolbook multiplication cost at the modulus bit width. -/
theorem modExpCost_eq (N a e : ℕ) (hN : 0 < N) :
    modExpRealizedBitCost N a e
      = ((Nat.log2 e + 1) + (modExpBits e).count true) * schoolbookMulModBitCost (shorBitLength N) := by
  have hfold := modExpCostedStep_foldl N hN (modExpBits e) (a % N) (1 % N) 0
    (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
  show (modExpBits e).foldl (modExpCostedStep N) (a % N, 1 % N, 0) |>.2.2 = _
  rw [hfold.2.2, modExpBits_length]
  simp

/-- The natural-number polynomial inequality `s * (2 * s + 1) ^ 2 ≤ (s + 1) ^ 5` holds. -/
theorem poly5 (s : ℕ) : s * (2 * s + 1) ^ 2 ≤ (s + 1) ^ 5 := by
  have h : (s : ℤ) * (2 * s + 1) ^ 2 ≤ (s + 1) ^ 5 := by
    have hs : (0 : ℤ) ≤ s := by exact_mod_cast s.zero_le
    nlinarith [sq_nonneg ((s : ℤ) - 1), sq_nonneg ((s : ℤ) - 2),
      mul_nonneg hs (sq_nonneg ((s : ℤ) - 1)),
      mul_nonneg hs (sq_nonneg ((s : ℤ) - 2)),
      mul_nonneg (sq_nonneg ((s : ℤ) - 2)) (sq_nonneg ((s : ℤ) - 2)),
      mul_nonneg hs (sq_nonneg (s : ℤ))]
  exact_mod_cast h

/-- The chosen natural-number bit length is always at least one. -/
theorem shorBitLength_pos (n : ℕ) : 1 ≤ shorBitLength n := by
  simp only [shorBitLength]; omega

/-- The chosen bit-length function is monotone. -/
theorem shorBitLength_mono {m n : ℕ} (h : m ≤ n) : shorBitLength m ≤ shorBitLength n := by
  simp only [shorBitLength, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- For positive `n`, the power `2 ^ (shorBitLength n - 1)` is at most `n`. -/
theorem eq_pow_le_bitlen (n : ℕ) (hn : 0 < n) : 2 ^ (shorBitLength n - 1) ≤ n := by
  have h := Nat.pow_log_le_self (x := n) (b := 2) (by omega)
  rw [← Nat.log2_eq_log_two] at h
  have hexp : shorBitLength n - 1 = Nat.log2 n := by
    simp only [shorBitLength]; omega
  rw [hexp]; exact h

/-- Every natural number is strictly less than two raised to its chosen bit length. -/
theorem lt_pow_bitlen (n : ℕ) : n < 2 ^ shorBitLength n := by
  have h := Nat.lt_pow_succ_log_self (x := n) (by decide : 1 < (2 : ℕ))
  rw [← Nat.log2_eq_log_two] at h
  have hexp : shorBitLength n = Nat.log2 n + 1 := rfl
  rw [hexp] at *
  omega

/-- A positive natural number has chosen bit length one exactly when it is one. -/
theorem bitlen_eq_one_iff (n : ℕ) (hn : 0 < n) : shorBitLength n = 1 ↔ n = 1 := by
  simp only [shorBitLength]
  constructor
  · intro h
    have hlog : Nat.log2 n = 0 := by omega
    rw [Nat.log2_eq_log_two, Nat.log_eq_zero_iff] at hlog
    omega
  · intro h
    subst h
    rfl

/-- If `0 < r < b` and `r` has the same bit length as `b`, the remainder `b % r` has bit length
at most `shorBitLength b - 1` in the stated inequality form. -/
theorem bitlen_two_step_drop (b r s : ℕ) (hr : 0 < r)
    (hrb : r < b) (heq : shorBitLength r = shorBitLength b) (hsdef : s = b % r) :
    shorBitLength s + 1 ≤ shorBitLength b := by
  have hpowb := eq_pow_le_bitlen b (by omega)
  have hltb := lt_pow_bitlen b
  have hpowr := eq_pow_le_bitlen r hr
  have hltr := lt_pow_bitlen r
  rw [heq] at hpowr hltr
  have hpowsum : 2 ^ (shorBitLength b - 1) * 2 = 2 ^ shorBitLength b := by
    conv_rhs => rw [show shorBitLength b = (shorBitLength b - 1) + 1 from by
      simp only [shorBitLength]; omega]
    rw [Nat.pow_succ]
  have hL2 : 2 ≤ shorBitLength b := by
    by_contra hc
    have hL1 : shorBitLength b = 1 := by
      have := shorBitLength_pos b
      omega
    have hb1 : b = 1 := (bitlen_eq_one_iff b (by omega)).mp hL1
    omega
  have hq : b / r = 1 := by
    by_contra hc
    have hpos : 0 < b / r := Nat.div_pos hrb.le hr
    have hge : 2 ≤ b / r := by omega
    have hprod := Nat.mul_le_mul_right r hge
    have hle : (b / r) * r ≤ b := Nat.div_mul_le_self b r
    omega
  have hmod : s = b - r := by
    have h1 : b % r = b - r := by
      have hlt2 : b - r < r := by
        have hdiv := Nat.div_add_mod b r
        rw [hq] at hdiv
        have hmod := Nat.mod_lt b hr
        omega
      rw [Nat.mod_eq_sub_mod hrb.le, Nat.mod_eq_of_lt hlt2]
    exact hsdef.trans h1
  have hlt : s < 2 ^ (shorBitLength b - 1) := by
    have hsub : b - r < 2 ^ (shorBitLength b - 1) := by omega
    rw [hmod]; exact hsub
  have hsm : Nat.log2 s + 1 ≤ shorBitLength b - 1 := by
    have hlog := Nat.log_lt_of_lt_pow' (x := shorBitLength b - 1) (y := s)
      (by omega : shorBitLength b - 1 ≠ 0) hlt
    rw [← Nat.log2_eq_log_two] at hlog
    simp only [shorBitLength] at *
    omega
  simp only [shorBitLength] at *
  omega

/-- The fuel-bounded Euclidean algorithm returns `b` immediately when its second argument is
zero. -/
theorem euclidGcd_zero_right (fuel b : ℕ) : euclidGcd fuel b 0 = b := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [euclidGcd]

/-- The gcd of `a` and `b` equals the gcd of `b` and `a % b`. -/
theorem gcd_swap (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]

/-- With positive second argument and fuel at least `euclidStepBound b`, the fuel-bounded
Euclidean algorithm returns `Nat.gcd a b`. -/
theorem euclidGcd_eq_gcd :
    ∀ (fuel a b : ℕ), 0 < b → euclidStepBound b ≤ fuel → euclidGcd fuel a b = Nat.gcd a b := by
  intro fuel
  refine Nat.strongRecOn fuel ?_
  intro f ih a b hb hf
  have hbf : 2 * shorBitLength b + 1 ≤ f := by
    simpa [euclidStepBound] using! hf
  cases f with
  | zero =>
      exfalso
      have := shorBitLength_pos b
      omega
  | succ f0 =>
      have hb0 : ¬ b = 0 := by omega
      rw [show euclidGcd (f0 + 1) a b = euclidGcd f0 b (a % b) from by
        show (if b = 0 then a else euclidGcd f0 b (a % b)) = _
        rw [if_neg hb0]]
      by_cases hr : a % b = 0
      · rw [hr, euclidGcd_zero_right]
        have h1 : Nat.gcd b (a % b) = b := by rw [hr, Nat.gcd_zero_right]
        rw [gcd_swap]
        exact h1.symm
      · have hrb : 0 < a % b := by omega
        have hmono := shorBitLength_mono (Nat.mod_lt a hb).le
        by_cases hlt : shorBitLength (a % b) < shorBitLength b
        · have hfe : euclidStepBound (a % b) ≤ f0 := by
            have h1 : shorBitLength (a % b) + 1 ≤ shorBitLength b := by omega
            show 2 * shorBitLength (a % b) + 1 ≤ f0
            omega
          rw [ih f0 (by omega) b (a % b) hrb hfe]
          exact (gcd_swap a b).symm
        · have heq : shorBitLength (a % b) = shorBitLength b := by omega
          rw [show euclidGcd f0 b (a % b)
              = euclidGcd (f0 - 1) (a % b) (b % (a % b)) from by
            conv_lhs => rw [show f0 = (f0 - 1) + 1 from by
              have := shorBitLength_pos b
              omega]
            show (if a % b = 0 then b else euclidGcd (f0 - 1) (a % b) (b % (a % b))) = _
            rw [if_neg hr]]
          by_cases hs : b % (a % b) = 0
          · rw [hs, euclidGcd_zero_right]
            have h1 : Nat.gcd b (a % b) = a % b := by
              rw [gcd_swap b (a % b), hs, Nat.gcd_zero_right]
            rw [gcd_swap]
            exact h1.symm
          · have hsb : 0 < b % (a % b) := by omega
            have hdrop := bitlen_two_step_drop b (a % b) (b % (a % b)) hrb
              (Nat.mod_lt a hb) heq rfl
            have hfe : euclidStepBound (b % (a % b)) ≤ f0 - 1 := by
              have : shorBitLength (b % (a % b)) + 1 ≤ shorBitLength b := hdrop
              show 2 * shorBitLength (b % (a % b)) + 1 ≤ f0 - 1
              omega
            rw [ih (f0 - 1) (by omega) (a % b) (b % (a % b)) hsb hfe]
            exact ((gcd_swap b (a % b)).symm).trans (gcd_swap a b).symm

/-- The initial binary-tape machine configuration containing the encoding `natToBinaryList N`. -/
def initCfg (N : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin 2) :=
  Turing.TM0.init (natToBinaryList N)

/-- The `n`th cell of the tape initialized from a list is the list's defaulted `n`th entry. -/
theorem tape_mk₁_nth_getI (l : List (Option Bool)) (n : ℕ) :
    (Turing.Tape.mk₁ l).nth n = l.getI n := by
  rw [← Turing.Tape.right₀_nth (Turing.Tape.mk₁ l) n]
  show (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk l)).right₀.nth n = l.getI n
  rw [Turing.Tape.mk'_right₀, Turing.ListBlank.nth_mk]

/-- Every blank-extended list of optional bits has a position containing the blank symbol. -/
theorem exists_listBlank_blank (L : Turing.ListBlank (Option Bool)) : ∃ n, L.nth n = none :=
  Turing.ListBlank.induction_on L fun l =>
    ⟨l.length, by
      rw [Turing.ListBlank.nth_mk, List.getI_eq_default l (le_refl _)]
      rfl⟩

/-- Every configuration over the optional-bit tape alphabet has a blank tape position at a
natural-number index. -/
theorem exists_tape_blank (c : Turing.TM0.Cfg (Option Bool) (Fin 2)) :
    ∃ n : ℕ, c.Tape.nth n = none := by
  obtain ⟨n, hn⟩ := exists_listBlank_blank c.Tape.right₀
  exact ⟨n, (Turing.Tape.right₀_nth c.Tape n).symm.trans hn⟩

/-- The least natural-number tape index containing a blank symbol. -/
noncomputable def tapeBlankAt (c : Turing.TM0.Cfg (Option Bool) (Fin 2)) : ℕ :=
  Nat.find (exists_tape_blank c)

/-- The tape cell at `tapeBlankAt c` is blank. -/
theorem tapeBlankAt_spec (c : Turing.TM0.Cfg (Option Bool) (Fin 2)) :
    c.Tape.nth (tapeBlankAt c) = none :=
  Nat.find_spec (exists_tape_blank c)

/-- Every natural-number tape index below `tapeBlankAt c` contains a nonblank symbol. -/
theorem tapeBlankAt_min (c : Turing.TM0.Cfg (Option Bool) (Fin 2)) {m : ℕ}
    (hm : m < tapeBlankAt c) : c.Tape.nth m ≠ none :=
  Nat.find_min (exists_tape_blank c) hm

/-- The binary input list for `N` has length `shorBitLength N`. -/
theorem length_natToBinaryList (N : ℕ) :
    (natToBinaryList N).length = shorBitLength N := by
  simp [natToBinaryList]

/-- At an index below the chosen bit length, the encoded input list contains `some (N.testBit
i)`. -/
theorem getI_natToBinaryList (N i : ℕ) (hi : i < shorBitLength N) :
    (natToBinaryList N).getI i = some (N.testBit i) := by
  have hlen : i < (natToBinaryList N).length := by rw [length_natToBinaryList N]; exact hi
  rw [List.getI_eq_getElem (natToBinaryList N) hlen]
  simp [natToBinaryList]

/-- The defaulted input-list entry at its chosen bit length is blank. -/
theorem getI_natToBinaryList_end (N : ℕ) :
    (natToBinaryList N).getI (shorBitLength N) = none := by
  have hlen : (natToBinaryList N).length ≤ shorBitLength N := by rw [length_natToBinaryList N]
  rw [List.getI_eq_default (natToBinaryList N) hlen]
  rfl

/-- The natural-indexed tape cells of `initCfg N` are the defaulted entries of `natToBinaryList
N`. -/
theorem tape_nth_init_getI (N : ℕ) :
    ∀ n : ℕ, (initCfg N).Tape.nth n = (natToBinaryList N).getI n :=
  fun n => tape_mk₁_nth_getI _ n

/-- The first blank in the initialized input tape occurs at `shorBitLength N`. -/
theorem tapeBlankAt_init (N : ℕ) : tapeBlankAt (initCfg N) = shorBitLength N := by
  have hne : ∀ i < shorBitLength N, (initCfg N).Tape.nth i ≠ none := by
    intro i hi
    rw [tape_nth_init_getI, getI_natToBinaryList N i hi]
    simp
  have hblank : (initCfg N).Tape.nth (shorBitLength N) = none := by
    rw [tape_nth_init_getI, getI_natToBinaryList_end N]
  refine le_antisymm ?_ ?_
  · by_contra hc
    have hlt : shorBitLength N < tapeBlankAt (initCfg N) := by omega
    exact tapeBlankAt_min _ hlt hblank
  · by_contra hc
    have hlt : tapeBlankAt (initCfg N) < shorBitLength N := by omega
    exact hne _ hlt (tapeBlankAt_spec _)

/-- The list of tape bits at natural-number positions strictly before the first blank,
extracting each optional bit with default false. -/
noncomputable def tapeBits (c : Turing.TM0.Cfg (Option Bool) (Fin 2)) : List Bool :=
  (List.range (tapeBlankAt c)).map fun (i : ℕ) => (c.Tape.nth i).getD false

/-- The natural number obtained by applying `binaryListValue` to the tape prefix before its
first blank. -/
noncomputable def tapeValue (c : Turing.TM0.Cfg (Option Bool) (Fin 2)) : ℕ :=
  binaryListValue (tapeBits c)

/-- The binary-list decoder `binaryListValue` equals the recursive little-endian decoder
`bitsValue`. -/
theorem binaryListValue_eq_bitsValue : ∀ (l : List Bool), binaryListValue l = bitsValue l
  | [] => rfl
  | b :: l => by
    show (if b then 1 else 0) + 2 * binaryListValue l = (if b then 1 else 0) + 2 * bitsValue l
    rw [binaryListValue_eq_bitsValue l]

/-- Decoding the optional-bit input encoding after replacing blanks by false returns the encoded
natural number. -/
theorem binaryListValue_map_getD (N : ℕ) :
    binaryListValue ((natToBinaryList N).map fun b => b.getD false) = N := by
  have h : (natToBinaryList N).map (fun b => b.getD false) = modExpBits N := by
    simp only [natToBinaryList, List.map_map]
    show (List.range (shorBitLength N)).map N.testBit = modExpBits N
    rfl
  rw [h, binaryListValue_eq_bitsValue, modExpBits_value]

/-- The tape prefix extracted from the initial configuration equals `modExpBits N`. -/
theorem tapeBits_init (N : ℕ) : tapeBits (initCfg N) = modExpBits N := by
  show (List.range (tapeBlankAt (initCfg N))).map
      (fun (i : ℕ) => ((initCfg N).Tape.nth i).getD false) = modExpBits N
  rw [tapeBlankAt_init]
  have hmap : (List.range (shorBitLength N)).map
      (fun (i : ℕ) => ((initCfg N).Tape.nth i).getD false)
      = (List.range (shorBitLength N)).map N.testBit := by
    apply List.map_congr_left
    intro i hi
    rw [tape_nth_init_getI, getI_natToBinaryList N i (List.mem_range.mp hi)]
    rfl
  rw [hmap]
  rfl

/-- Reading the natural-number value of the initialized input tape returns `N`. -/
theorem tapeValue_init (N : ℕ) : tapeValue (initCfg N) = N := by
  show binaryListValue (tapeBits (initCfg N)) = N
  rw [tapeBits_init, binaryListValue_eq_bitsValue, modExpBits_value]

/-- The machine that halts immediately for every state and tape symbol. -/
def haltOnStart : Turing.TM0.Machine (Option Bool) (Fin 2) := fun _ _ => none

/-- The immediately halting machine satisfies the polynomial-time machine predicate. -/
theorem bitMachinePolynomialTime_haltOnStart :
    BitMachinePolynomialTime haltOnStart := by
  refine ⟨1, 1, fun input => ⟨0, Nat.zero_le _, Turing.TM0.init input, rfl, rfl⟩⟩

/-- For positive inputs, the binary encoding has the chosen bit length, fits below the
corresponding power of two, and decodes to the original input. -/
theorem clause81_binary_encoding : ∀ N : ℕ, 0 < N →
    (natToBinaryList N).length = shorBitLength N ∧
      N < 2 ^ shorBitLength N ∧
        binaryListValue ((natToBinaryList N).map fun b => b.getD false) = N := by
  intro N _hN
  exact ⟨length_natToBinaryList N, lt_pow_bitlen N, binaryListValue_map_getD N⟩

/-- The preprocessing-factor function satisfies the formal `ClassicalPolySearch` predicate,
whose configuration readout is unrestricted. -/
theorem clause81_poly_search : ClassicalPolySearch shorPreprocessFactor := by
  simp only [ClassicalPolySearch]
  refine ⟨haltOnStart, fun c => shorPreprocessFactor (tapeValue c),
    bitMachinePolynomialTime_haltOnStart, ?_⟩
  intro N
  refine ⟨0, initCfg N, rfl, rfl, ?_⟩
  show shorPreprocessFactor (tapeValue (initCfg N)) = shorPreprocessFactor N
  rw [tapeValue_init]

/-- The primality decision function satisfies the formal `ClassicalPolyDecision` predicate,
whose configuration readout is unrestricted. -/
theorem clause81_poly_decision : ClassicalPolyDecision fun N => decide (Nat.Prime N) := by
  simp only [ClassicalPolyDecision]
  refine ⟨haltOnStart, fun c => decide (Nat.Prime (tapeValue c)),
    bitMachinePolynomialTime_haltOnStart, ?_⟩
  intro N
  refine ⟨0, initCfg N, rfl, rfl, ?_⟩
  show decide (Nat.Prime (tapeValue (initCfg N))) = decide (Nat.Prime N)
  rw [tapeValue_init]

/-- The polynomial bit-length bound `polyLogBound c d` is monotone in its input. -/
theorem clause81_polyLogBound_monotone (c d N N' : ℕ) :
    N ≤ N' → polyLogBound c d N ≤ polyLogBound c d N' := by
  intro h
  simp only [polyLogBound]
  exact Nat.mul_le_mul (le_refl c)
    (pow_le_pow_left' (Nat.add_le_add_right (shorBitLength_mono h) 1) d)

/-- Re-exports the factoring preprocessing contract for the source-bridge clause. -/
theorem clause81_source_bridge :
    Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessing :=
  Qatlib.Concepts.PeriodSampling.FactorAlgorithm.factoringPreprocessing

/-- The displayed conjunction of binary-encoding, search, decision, universal bit-bound, and
preprocessing clauses is false. -/
theorem not_clause2 : ¬ (

  (∀ N : ℕ, 0 < N →
    (natToBinaryList N).length = shorBitLength N ∧
      N < 2 ^ shorBitLength N ∧
        binaryListValue ((natToBinaryList N).map fun b => b.getD false) = N) ∧

  (ClassicalPolySearch shorPreprocessFactor) ∧

  (ClassicalPolyDecision fun N => decide (Nat.Prime N)) ∧

  (∀ (c d N : ℕ), 0 < c →
    shorBitLength N ≤ polyLogBound c d N ∧
      ∀ N', N ≤ N' → polyLogBound c d N ≤ polyLogBound c d N') ∧

  (Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessing)
) := by
  intro h
  have := (h.2.2.2.1 1 0 2 (by decide)).1
  simp [shorBitLength, polyLogBound] at this

/-- Collects modular-exponentiation correctness and costs, local Fourier formulas and counts,
continued-fraction bounds, pair-decoder soundness, and Euclidean gcd bounds in the framework
of [Shor1997]. -/
theorem g3 :

  (∀ (N a e : ℕ), 0 < N →
    modExpResult N a e = (a ^ e) % N ∧
      modExpRealizedBitCost N a e =
        ((Nat.log2 e + 1) + (modExpBits e).count true) *
          schoolbookMulModBitCost (shorBitLength N) ∧
        modExpSpaceCost N e = 3 * shorBitLength N + shorBitLength e) ∧

  (∀ n : ℕ,
    qftGateCount n = n + n * (n - 1) / 2 + n / 2 ∧
      qftSpaceCost n = n ∧
        GateCount (localProgramCircuit (localQFT n)) = qftGateCount n ∧
          QueryCount (localProgramCircuit (localQFT n)) = 0) ∧

  (∀ n : ℕ,
    localProgramMatrix (localQFT n) = relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) ∧
      localProgramMatrix (localProgramAdjoint (localQFT n)) =
        (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ) ∧
  (∀ n : ℕ,
    (∀ (a : Fin n) (x y : Reg n), localGateMatrix (.h a) x y =
        if ∀ k : Fin n, k ≠ a → x k = y k then Hadamard (x a) (y a) else 0) ∧
      (∀ (a c : Fin n) (k : ℕ) (neg : Bool) (x y : Reg n),
          localGateMatrix (.cp a c k neg) x y = if x = y then
            (if x a && x c then Complex.exp
              (((if neg then -(2 * Real.pi / (2 ^ k : ℝ)) else 2 * Real.pi / (2 ^ k : ℝ)) : ℝ)
                * Complex.I)
            else 1) else 0) ∧
      (∀ (a c : Fin n) (x y : Reg n), localGateMatrix (.swap a c) x y =
          if x = (fun k => y (Equiv.swap a c k)) then 1 else 0) ∧
      (∀ g : LocalQFTGate n, localGateMatrix g ∈ Matrix.unitaryGroup (Reg n) ℂ)) ∧
  (∀ (m : ℕ) (x : Reg m),
      (bitVecEquiv m x).val = ∑ i : Fin m, (if x i then 1 else 0) * 2 ^ (m - 1 - i.val)) ∧

  (∀ M : ℕ,
    cfDepth M = 2 * (Nat.log 2 M + 1) + 2 ∧
      cfBitCost M ≤
        (2 * (shorBitLength M + 1) + 3) * schoolbookMulModBitCost (shorBitLength M) ∧
        cfSpaceCost M = 3 * shorBitLength M) ∧

  (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y z : Fin M),
    (pairLCMOrderDecode N M a (y, z)).2.1 ≤ N * (N + 1) ∧
      (pairLCMOrderDecode N M a (y, z)).2.2 ≤ N ^ 2 ∧
      (∀ q, (pairLCMOrderDecode N M a (y, z)).1 = some q → 0 < q ∧ a ^ q = 1) ∧
      (∀ d, pairLCMFactor N M a (y, z) = some d → 1 < d ∧ d < N ∧ d ∣ N)) ∧

  (∀ (a b fuel : ℕ), 0 < b → euclidStepBound b ≤ fuel →
      euclidGcd fuel a b = Nat.gcd a b) ∧
  (∀ N : ℕ, 0 < N →
    gcdBitCost N ≤ polyLogBound 1 5 N ∧ gcdSpaceCost N = 2 * shorBitLength N)
:= by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N a e hN
    exact ⟨modExpResult_eq N a e hN, modExpCost_eq N a e hN, rfl⟩
  · intro n
    have hgc := localQFT_exact_gate_counts_and_wires n
    refine ⟨rfl, rfl, hgc.2.2.2.1, hgc.2.2.2.2.1⟩
  · intro n
    exact localQFT_exact_positive_matrix n
  · intro n
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a x y
      exact localGateMatrix_h n a x y
    · intro a c k neg x y
      exact localGateMatrix_cp n a c k neg x y
    · intro a c x y
      exact localGateMatrix_swap n a c x y
    · intro g
      exact localGateMatrix_unitary g
  · intro m x
    exact bitVecEquiv_binary_msb_expansion m x
  · intro M
    refine ⟨rfl, ?_, rfl⟩
    have hle : cfDepth M + 1 ≤ 2 * (shorBitLength M + 1) + 3 := by
      rw [cfDepth, shorBitLength, Nat.log2_eq_log_two]
      omega
    exact Nat.mul_le_mul hle (le_refl _)
  · exact pair_lcm_order_soundness_and_actual_work
  · intro a b fuel hb hf
    exact euclidGcd_eq_gcd fuel a b hb hf
  · intro N hN
    refine ⟨?_, rfl⟩
    have hpoly := poly5 (shorBitLength N)
    simp only [gcdBitCost, euclidStepBound, euclidStepBitCost, schoolbookMulModBitCost,
      polyLogBound]
    have hfactor : (2 * shorBitLength N + 1) * (2 * shorBitLength N * shorBitLength N + shorBitLength N)
        = shorBitLength N * (2 * shorBitLength N + 1) ^ 2 := by ring_nf
    rw [hfactor, one_mul]
    exact hpoly

/-- Each of the four components of an attempt's resource ledger is bounded by the corresponding
component of `attemptLedgerBound`. -/
theorem ledger_le (N M k : ℕ) [NeZero N] (t : residueAttemptOutcome N M k) :
    (attemptOutcomeLedger N M k t).1 ≤ (attemptLedgerBound N M k).1 ∧
      (attemptOutcomeLedger N M k t).2.1 ≤ (attemptLedgerBound N M k).2.1 ∧
        (attemptOutcomeLedger N M k t).2.2.1 ≤ (attemptLedgerBound N M k).2.2.1 ∧
          (attemptOutcomeLedger N M k t).2.2.2 ≤ (attemptLedgerBound N M k).2.2.2 := by
  rcases t with b | y | ayz <;>
    simp only [attemptOutcomeLedger, attemptLedgerBound, gcdSpaceCost] <;> omega

/-- The first component of every attempt resource ledger is at least the sampled bit width `k`. -/
theorem ledger_bit_ge (N M k : ℕ) [NeZero N] (t : residueAttemptOutcome N M k) :
    k ≤ (attemptOutcomeLedger N M k t).1 := by
  rcases t with b | y | ayz <;> simp only [attemptOutcomeLedger] <;> omega

/-- A recorded first-success position yields a factor, and every factor returned at that
position is a proper nontrivial divisor of `N`. -/
theorem receipt_sound (N M k R : ℕ) [NeZero N]
    (ω : Fin R → residueAttemptOutcome N M k) (j : Fin R)
    (h : firstSuccessAt N M k R ω j) :
    (attemptOutcomeFactor N M k (ω j)).isSome ∧
      ∀ d : ℕ, attemptOutcomeFactor N M k (ω j) = some d → 1 < d ∧ d < N ∧ d ∣ N := by
  have hsucc := h.1
  rcases hj : ω j with b | y | ayz
  · rw [hj] at hsucc
    simp only [residueAttemptSuccessEvent] at hsucc
  · rw [hj] at hsucc
    simp only [residueAttemptSuccessEvent] at hsucc
    show (residueClassicalFactor N y).isSome = true ∧
      ∀ d : ℕ, residueClassicalFactor N y = some d → 1 < d ∧ d < N ∧ d ∣ N
    exact ⟨hsucc, residue_classical_factor_sound N y⟩
  · obtain ⟨a, y, z⟩ := ayz
    rw [hj] at hsucc
    simp only [residueAttemptSuccessEvent] at hsucc
    show (attemptFactor N M a (y, z)).isSome = true ∧
      ∀ d : ℕ, attemptFactor N M a (y, z) = some d → 1 < d ∧ d < N ∧ d ∣ N
    exact ⟨hsucc, attemptFactor_sound N M a y z⟩

/-- A proper nontrivial divisor `d` of `N`, viewed as a residue, makes the classical residue
factor routine return `some d`. -/
theorem residueClassicalFactor_minFac (N : ℕ) [NeZero N] (d : ℕ) (hd1 : 1 < d) (hdlt : d < N)
    (hdvd : d ∣ N) : residueClassicalFactor N ((d : ZMod N)) = some d := by
  have hval : ((d : ZMod N)).val = d := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hdlt
  have hgcd : Nat.gcd ((d : ZMod N)).val N = d := by
    rw [hval]
    exact Nat.gcd_eq_left hdvd
  unfold residueClassicalFactor
  show (if 1 < Nat.gcd ((d : ZMod N)).val N ∧ Nat.gcd ((d : ZMod N)).val N < N
      then some (Nat.gcd ((d : ZMod N)).val N) else none) = some d
  rw [hgcd]
  simp [hd1, hdlt]

/-- Every natural number at least two is the root of a complete factor tree satisfying
`FactorTree.splitSound M` for every `M`. -/
theorem factorTree_exists :
    ∀ (n : ℕ), 2 ≤ n →
      ∃ t : FactorTree, FactorTree.root t = n ∧ FactorTree.complete t ∧
        ∀ M, FactorTree.splitSound M t := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih hn
  by_cases hp : Nat.Prime n
  · refine ⟨FactorTree.leaf n, rfl, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · show (List.prod [n]) = n
        simp
      · intro p
        show List.count p [n] = n.factorization p
        rw [List.count_singleton, hp.factorization, Finsupp.single_apply]
        by_cases hpn : n = p
        · subst hpn; simp
        · simp [hpn, beq_iff_eq]
    · intro M
      show Nat.Prime n
      exact hp
  · have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hdprime : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
    have hdlt : n.minFac < n := (Nat.not_prime_iff_minFac_lt hn).mp hp
    have hd1 : 1 < n.minFac := hdprime.one_lt
    have hdpos : 0 < n.minFac := by omega
    have hcopos : 0 < n / n.minFac := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
    have hco : 2 ≤ n / n.minFac := by
      by_contra hc
      have hq : n / n.minFac = 1 := by omega
      have hmul := Nat.div_mul_cancel hdvd
      rw [hq] at hmul
      omega
    haveI : NeZero n.minFac := NeZero.of_pos hdpos
    haveI : NeZero (n / n.minFac) := NeZero.of_pos hcopos
    obtain ⟨t1, h1r, h1c, h1s⟩ := ih n.minFac (by omega) hd1
    obtain ⟨t2, h2r, h2c, h2s⟩ := ih (n / n.minFac)
      (Nat.div_lt_self (by omega) (by omega : 1 < n.minFac)) hco
    refine ⟨FactorTree.node n n.minFac t1 t2, rfl, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · show List.prod (FactorTree.leaves t1 ++ FactorTree.leaves t2) = n
        rw [List.prod_append, h1c.1, h2c.1, h1r, h2r]
        exact Nat.mul_div_cancel' hdvd
      · intro p
        show List.count p (FactorTree.leaves t1 ++ FactorTree.leaves t2) = n.factorization p
        rw [List.count_append]
        have e1 : (FactorTree.leaves t1).count p = n.minFac.factorization p := by
          rw [h1c.2 p, h1r]
        have e2 : (FactorTree.leaves t2).count p = (n / n.minFac).factorization p := by
          rw [h2c.2 p, h2r]
        rw [e1, e2, ← Finsupp.add_apply,
          ← Nat.factorization_mul (by omega : n.minFac ≠ 0) (by omega : n / n.minFac ≠ 0),
          Nat.mul_div_cancel' hdvd]
    · intro M h
      haveI : NeZero n := NeZero.of_pos (by omega)
      refine ⟨?_, h1r, h2r, h1s M, h2s M⟩
      show ShorPreResult.factor n.minFac = shorPreprocess n ∨
        (∃ y : ZMod n, residueClassicalFactor n y = some n.minFac) ∨
        (∃ a : (ZMod n)ˣ, ∃ yz : Fin M × Fin M, attemptFactor n M a yz = some n.minFac)
      exact Or.inr (Or.inl ⟨(n.minFac : ZMod n),
        residueClassicalFactor_minFac n n.minFac hd1 hdlt hdvd⟩)

/-- Up to a receipt's first success, the first ledger sum lies between the number of attempts
times `k` and the corresponding uniform bound; the stated third-component sum also satisfies
its uniform bound. -/
theorem trajectory_ledger_sandwich (N M k R : ℕ) [NeZero N]
    (rec : FirstSuccessReceipt N M k R) :
    (rec.first.val + 1) * k ≤
      trajectoryLedgerSum N M k R rec.trajectory
        (fun t => (attemptOutcomeLedger N M k t).1) (rec.first.val + 1) ∧
      trajectoryLedgerSum N M k R rec.trajectory
          (fun t => (attemptOutcomeLedger N M k t).1) (rec.first.val + 1)
        ≤ (rec.first.val + 1) * (attemptLedgerBound N M k).1 ∧
      trajectoryLedgerSum N M k R rec.trajectory
          (fun t => (attemptOutcomeLedger N M k t).2.2.1) (rec.first.val + 1)
        ≤ (rec.first.val + 1) * (attemptLedgerBound N M k).2.2.1 := by
  have hfirst : rec.first.val < R := rec.first.isLt
  set ω := rec.trajectory
  set n := rec.first.val + 1
  have hnle : n ≤ R := by omega
  have hcard : (Finset.range n).card = n := Finset.card_range n
  refine ⟨?_, ?_, ?_⟩
  · unfold trajectoryLedgerSum
    have hconst : ∑ _j ∈ Finset.range n, k = n * k := by
      rw [Finset.sum_const, hcard, Nat.nsmul_eq_mul]
    rw [← hconst]
    apply Finset.sum_le_sum
    intro j hj
    have hjR : j < R := by
      have := Finset.mem_range.mp hj
      omega
    show k ≤ (if h : j < R then (attemptOutcomeLedger N M k (ω ⟨j, h⟩)).1 else 0)
    rw [dif_pos hjR]
    exact ledger_bit_ge N M k _
  · unfold trajectoryLedgerSum
    have hle : ∀ j ∈ Finset.range n,
        (if h : j < R then (attemptOutcomeLedger N M k (ω ⟨j, h⟩)).1 else 0)
          ≤ (attemptLedgerBound N M k).1 := by
      intro j hj
      have hjR : j < R := by
        have := Finset.mem_range.mp hj
        omega
      rw [dif_pos hjR]
      exact (ledger_le N M k _).1
    have := Finset.sum_le_card_nsmul (Finset.range n) _ (attemptLedgerBound N M k).1 hle
    rw [hcard, Nat.nsmul_eq_mul] at this
    exact this
  · unfold trajectoryLedgerSum
    have hle : ∀ j ∈ Finset.range n,
        (if h : j < R then (attemptOutcomeLedger N M k (ω ⟨j, h⟩)).2.2.1 else 0)
          ≤ (attemptLedgerBound N M k).2.2.1 := by
      intro j hj
      have hjR : j < R := by
        have := Finset.mem_range.mp hj
        omega
      rw [dif_pos hjR]
      exact (ledger_le N M k _).2.2.1
    have := Finset.sum_le_card_nsmul (Finset.range n) _ (attemptLedgerBound N M k).2.2.1 hle
    rw [hcard, Nat.nsmul_eq_mul] at this
    exact this

/-- Collects uniform attempt-ledger bounds, sound first-success receipts, cumulative cost
bounds, the residue factoring contract, and complete sound factor-tree existence in the
framework of [Shor1997]. -/
theorem g4 :

  (∀ (N M k : ℕ) [NeZero N] (t : residueAttemptOutcome N M k),
    (attemptOutcomeLedger N M k t).1 ≤ (attemptLedgerBound N M k).1 ∧
      (attemptOutcomeLedger N M k t).2.1 ≤ (attemptLedgerBound N M k).2.1 ∧
        (attemptOutcomeLedger N M k t).2.2.1 ≤ (attemptLedgerBound N M k).2.2.1 ∧
          (attemptOutcomeLedger N M k t).2.2.2 ≤ (attemptLedgerBound N M k).2.2.2) ∧

  (∀ (N M k R : ℕ) [NeZero N]
      (ω : Fin R → residueAttemptOutcome N M k) (j : Fin R),
    firstSuccessAt N M k R ω j →
      (attemptOutcomeFactor N M k (ω j)).isSome ∧
        ∀ d : ℕ, attemptOutcomeFactor N M k (ω j) = some d →
          1 < d ∧ d < N ∧ d ∣ N) ∧

  (∀ (N M k R : ℕ) [NeZero N] (rec : FirstSuccessReceipt N M k R),
    (rec.first.val + 1) * k ≤
      trajectoryLedgerSum N M k R rec.trajectory
        (fun t => (attemptOutcomeLedger N M k t).1) (rec.first.val + 1) ∧
      trajectoryLedgerSum N M k R rec.trajectory
          (fun t => (attemptOutcomeLedger N M k t).1) (rec.first.val + 1)
        ≤ (rec.first.val + 1) * (attemptLedgerBound N M k).1 ∧
      trajectoryLedgerSum N M k R rec.trajectory
          (fun t => (attemptOutcomeLedger N M k t).2.2.1) (rec.first.val + 1)
        ≤ (rec.first.val + 1) * (attemptLedgerBound N M k).2.2.1) ∧

  (Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueFactoringAlgorithm) ∧

  (∀ (N M : ℕ) [NeZero N] (_hM : 2 * N ^ 2 < M), 2 ≤ N →
    ∃ t : FactorTree, FactorTree.root t = N ∧
      FactorTree.splitSound M t ∧ FactorTree.complete t)
:= by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N M k hinst t
    exact ledger_le N M k t
  · intro N M k R hinst ω j h
    exact receipt_sound N M k R ω j h
  · intro N M k R hinst rec
    exact trajectory_ledger_sandwich N M k R rec
  · exact Qatlib.Concepts.PeriodSampling.FactorAlgorithm.residueFactoringAlgorithm
  · intro N M hinst hM hN
    obtain ⟨t, hr, hc, hs⟩ := factorTree_exists N hN
    exact ⟨t, hr, hs M, hc⟩

/-- Every natural-valued function satisfies the stated `ClassicalPolySearch` predicate because
its configuration readout is unrestricted. -/
lemma classicalPolySearch_arbitrary_readout (f : ℕ → ℕ) : ClassicalPolySearch f := by
  refine ⟨haltOnStart, fun c => f (tapeValue c), bitMachinePolynomialTime_haltOnStart, ?_⟩
  intro N
  exact ⟨0, initCfg N, rfl, rfl, by simp only [tapeValue_init]⟩

/-- Every Boolean-valued function satisfies the stated `ClassicalPolyDecision` predicate because
its configuration readout is unrestricted. -/
lemma classicalPolyDecision_arbitrary_readout (f : ℕ → Bool) : ClassicalPolyDecision f := by
  refine ⟨haltOnStart, fun c => f (tapeValue c), bitMachinePolynomialTime_haltOnStart, ?_⟩
  intro N
  exact ⟨0, initCfg N, rfl, rfl, by simp only [tapeValue_init]⟩

open scoped BigOperators

/-- The discrete-logarithm record `(1, 0, 1)` is not good for parameters `p = 3`, `q = 4`, and
`r = 0`. -/
theorem bad_dlog_record : ¬ dlogGoodOutcome 3 4 0 (1,0,1) := by
  intro h
  have hs := h.2
  norm_num [dlogSmallResidue,centeredResidue] at hs

/-- The bad record `(1, 0, 1)` has Born probability `1 / 16` in the state with `p = 3`, `q = 4`,
`g = 2`, and `x = 1`. -/
theorem bad_dlog_record_mass : BornProb (dlogTwoDimState 3 4 (2 : ZMod 3) 1) (1,0,1) = (1/16:ℝ) := by
  have hs : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  unfold BornProb dlogTwoDimState
  rw [show (3:ℕ)-1=2 by decide]
  simp only [Fin.sum_univ_two]
  norm_num [offGridPhase,hs,show (2:ZMod 3) ≠ 1 by decide]

/-- The unfiltered good-conditional predicate fails for `p = 3`, `q = 4`, `r = 0`, `g = 2`, and
`x = 1`. -/
theorem unfiltered_dlog_conditional_false : ¬ HasDlogGoodConditional 3 4 0 (2 : ZMod 3) 1 := by
  intro h
  obtain ⟨hnorm,D,hp,hformula,hzero⟩ := h
  have hz := hzero (1,0,1) bad_dlog_record
  rw [hformula] at hz
  change BornProb (dlogTwoDimState 3 4 (2 : ZMod 3) 1) (1,0,1) / _ = 0 at hz
  rw [bad_dlog_record_mass] at hz
  have hpos : 0 < (1/16:ℝ) / (dlogBornLaw 3 4 2 1 hnorm).probEvent (L := 1)
      (fun ω => dlogGoodOutcome 3 4 0 (ω 0)) := div_pos (by norm_num) hp
  linarith

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
