/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCoreDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Quan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Quan

/-!
# Rational readout witnesses and effective counting bounds

This module constructs a legal readout witness whose decoder returns the rational payoff mean
directly, and proves its table, error, and ledger specifications. It also establishes half-up
rational rounding bounds and transfers the counting guarantees of [BrassardEtAl2002] to
finite-precision scalar decoding with explicit slack.

## Main statements

* `clause23`: collects the readout witness and scalar and payoff precision specifications.
* `aeEffCount_error`: bounds the combined decoding and nearest-integer error.
* `clause90`: collects rounding properties, effective counting success bounds, and budget
  inequalities.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Classical BigOperators
set_option warningAsError false

/-- The rational arithmetic mean of the request payoff values, using rational division also when
the basis size is zero. -/
def requestMean (r : ReadoutRequest) : ℚ :=
  (∑ i : Fin r.basisSize, r.payoff i) / r.basisSize

/-- The real coercion of the rational request mean equals the request target. -/
theorem requestMean_eq_target (r : ReadoutRequest) : (requestMean r : ℝ) = r.target := by
  unfold ReadoutRequest.target
  by_cases h : r.basisSize = 0
  · rw [if_pos h, requestMean]
    simp [h]
  · rw [if_neg h, requestMean]
    push_cast
    rfl

/-- The zero-wire readout program with empty gate words, a single payoff-table layer, and
constant decoder equal to `requestMean`. -/
def readoutProgram (r : ReadoutRequest) : ReadoutProgram :=
  ⟨0, r.prec, [], [], ⟨1, r.basisSize, fun _ z => r.payoff z⟩, [], [],
    fun _ => requestMean r, 0⟩

/-- The readout ledger with zero bit, arithmetic, space, and gate entries and one forward and
one inverse access. -/
def readoutLedger : ReadoutLedger := ⟨0, 0, 0, 0, 0, 1, 1⟩

/-- The constructed readout program satisfies the finite-word legality and inverse-word
conditions. -/
theorem readoutProgram_legal (r : ReadoutRequest) : (readoutProgram r).Legal := by
  show
    finiteWordLegal _ ([] ++ [] ++ []) = true ∧
      ([] : List FiniteGateCode) = finiteWordAdjoint []
  simp [finiteWordLegal, finiteWordAdjoint]

/-- For a legal request, the constructed readout table is well formed and faithful to its payoff
values. -/
theorem readoutProgram_tableFaithful (r : ReadoutRequest) (hr : r.Legal) :
    (readoutProgram r).TableFaithful r := by
  have hpos : 0 < r.basisSize := hr.1
  have hpay : ∀ i, 0 ≤ r.payoff i ∧ r.payoff i ≤ 1 := hr.2.1
  have hpe : 0 ≤ r.payoffErr := hr.2.2.1
  have hph : 0 ≤ r.phaseErr := hr.2.2.2.2.1
  refine ⟨rfl, ⟨?_, hpos, ?_⟩, ?_⟩
  · show (0 : ℕ) < 1
    norm_num
  · intro l z
    exact hpay z
  · intro l z i hzi
    have hzi' : z = i := Fin.eq_of_val_eq hzi
    rw [hzi']
    show |(r.payoff i : ℝ) - (r.payoff i : ℝ)| ≤ r.payoffErr + r.phaseErr
    rw [sub_self, abs_zero]
    exact add_nonneg hpe hph

/-- The error record assigning the request input budget to input approximation and zero to all
program errors. -/
def readoutError (r : ReadoutRequest) : JointErrorRecord :=
  ⟨r.inputBudget, 0, 0, 0⟩

/-- For a legal request, the constructed total error is at most its tolerance. -/
theorem readoutError_total (r : ReadoutRequest) (hr : r.Legal) :
    (readoutError r).total ≤ r.tol := by
  have htol : r.inputBudget < r.tol := hr.2.2.2.2.2.2.1
  show (r.inputBudget + (0 + 0 + 0) : ℝ) ≤ _
  simpa using! htol.le

/-- The constructed readout error has zero program error. -/
theorem readoutError_programErr (r : ReadoutRequest) :
    (readoutError r).programErr = 0 := by
  show (0 + 0 + 0 : ℝ) = 0
  simp

/-- The constructed program returns the exact request target with probability one at its
specified program error. -/
theorem readoutProgram_successProb (r : ReadoutRequest) :
    (readoutProgram r).successProb r ((readoutError r).programErr) = 1 := by
  have hq : (requestMean r : ℝ) = r.target := requestMean_eq_target r
  rw [readoutError_programErr]
  show
    MeasureProb
        (Run (1 : Matrix (Reg 0) (Reg 0) ℂ) (finiteCodeCircuit 0 ([] ++ [] ++ []))
          (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0)))
        (Finset.univ.filter fun z : Reg 0 => |((requestMean r : ℚ) : ℝ) - r.target| ≤ 0) = 1
  have hev :
      (Finset.univ.filter fun z : Reg 0 => |((requestMean r : ℚ) : ℝ) - r.target| ≤ 0) =
        Finset.univ := by
    apply Finset.filter_true_of_mem
    intro z _
    rw [hq]
    simp
  have hrun :
      (Run (1 : Matrix (Reg 0) (Reg 0) ℂ) (finiteCodeCircuit 0 ([] ++ [] ++ []))
          (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0))) =
        Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0) := rfl
  rw [hev, hrun, measureProb_univ (normalized_ket _)]

/-- For a legal request, the constructed program satisfies `ReadoutProgram.SolvesAt`. -/
theorem readoutProgram_solves (r : ReadoutRequest) (hr : r.Legal) :
    (readoutProgram r).SolvesAt r := by
  refine ⟨readoutError r, rfl, readoutError_total r hr, ?_, readoutProgram_tableFaithful r hr⟩
  have h := readoutProgram_successProb r
  have hep : (readoutError r).programErr = 0 := readoutError_programErr r
  rw [hep] at h
  rw [hep]
  rw [h]
  norm_num

/-- The constructed ledger covers the constructed readout program for every request. -/
theorem readoutLedger_covers (r : ReadoutRequest) :
    readoutLedger.Covers (readoutProgram r) r := by
  refine ⟨rfl, rfl, rfl, rfl, 1, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℕ) ≤ 1 * readoutBitShape _ _
    exact Nat.zero_le _
  · show (0 : ℕ) ≤ 1 * readoutGcdShape _ _
    exact Nat.zero_le _
  · show (0 : ℕ) ≤ 1 * readoutPersistentShape _ _
    exact Nat.zero_le _
  · show (0 : ℕ) ≤ 1 * readoutPeakShape _ _
    exact Nat.zero_le _
  · show (0 : ℕ) ≤ 1 * readoutGateShape _ _ _
    exact Nat.zero_le _

/-- Collects the error decompositions, existence of legal readout witnesses with covering
ledgers, resource shape identities, and rational payoff and native scalar precision bounds. -/
theorem clause23 :

  (∀ e : JointErrorRecord,
    e.total = e.inputApprox + e.forwardAccess + e.inverseAccess + e.decoderErr ∧
      e.total = e.inputApprox + e.programErr ∧
      e.programErr = e.forwardAccess + e.inverseAccess + e.decoderErr) ∧

  (∀ r : ReadoutRequest, r.inputBudget = r.payoffErr + r.normErr + r.phaseErr + r.frameErr) ∧

  (∀ r : ReadoutRequest, r.Legal →
    ∃ (P : ReadoutProgram) (led : ReadoutLedger),
      P.Legal ∧ P.SolvesAt r ∧ led.Covers P r) ∧

  (∀ (basisSize layers prec : ℕ),
    readoutBitShape basisSize prec = (basisSize + 1) * (prec + 1) ∧
      readoutGcdShape basisSize prec = basisSize + prec + 1 ∧
      readoutPersistentShape basisSize prec = 2 * readoutBitShape basisSize prec ∧
      readoutPeakShape basisSize prec = 3 * readoutBitShape basisSize prec ∧
      readoutGateShape basisSize layers prec =
        (basisSize + 1) * (layers + 1) * (prec + 1)) ∧
  (∀ P : ReadoutProgram,
    P.Legal →
      finiteWordLegal P.wires P.synthWord = true ∧
        P.prepareInvWord = finiteWordAdjoint P.prepareWord ∧
        P.synthWord = P.prepareWord ++ P.tableSelectWord ++ P.phaseInversion) ∧

  (RationalPayoffTablePrecise ∧ NativeScalarPrecision)
 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    refine ⟨?_, rfl, rfl⟩
    show e.inputApprox + e.programErr = _
    simp only [JointErrorRecord.programErr]
    abel
  · intro r
    rfl
  · intro r hr
    exact ⟨readoutProgram r, readoutLedger, readoutProgram_legal r,
      readoutProgram_solves r hr, readoutLedger_covers r⟩
  · intro basisSize layers prec
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro P hP
    exact ⟨hP.1, hP.2, rfl⟩
  · exact ⟨rational_payoff_unitary_value_and_operator_error,
      native_ae_computed_scalar_precision⟩

/-- Rational numerator-denominator floor division agrees with the real floor. -/
theorem ratFloor_eq_floor (x : ℚ) : ratFloor x = Int.floor (x : ℝ) := by
  unfold ratFloor
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg x.den)]
  rw [Rat.floor_cast x, Rat.floor_def']

/-- Effective rational rounding equals the floor after adding one half. -/
theorem aeEffRound_eq_intFloor (x : ℚ) : aeEffRound x = Int.floor ((x : ℝ) + 1 / 2) := by
  unfold aeEffRound
  rw [ratFloor_eq_floor]
  congr 1
  push_cast
  rfl

/-- Effective rational rounding has absolute error at most one half. -/
theorem aeEffRound_error (x : ℚ) : |(x : ℝ) - (aeEffRound x : ℝ)| ≤ 1 / 2 := by
  rw [aeEffRound_eq_intFloor]
  have h1 : (Int.floor ((x : ℝ) + 1 / 2) : ℝ) ≤ (x : ℝ) + 1 / 2 := Int.floor_le _
  have h2 : (x : ℝ) + 1 / 2 < (Int.floor ((x : ℝ) + 1 / 2) : ℝ) + 1 := Int.lt_floor_add_one _
  apply abs_le.mpr
  constructor <;> linarith

/-- Effective rational rounding fixes every integer. -/
theorem aeEffRound_intCast (n : ℤ) : aeEffRound n = n := by
  rw [aeEffRound_eq_intFloor]
  apply Int.floor_eq_iff.mpr
  constructor <;> push_cast <;> linarith

/-- A half-integer is rounded to the larger integer. -/
theorem aeEffRound_half_up (n : ℤ) : aeEffRound (n + 1 / 2) = n + 1 := by
  rw [aeEffRound_eq_intFloor]
  apply Int.floor_eq_iff.mpr
  constructor <;> push_cast <;> linarith

/-- A rational strictly below `n+1/2` rounds to an integer at most `n`. -/
theorem aeEffRound_le_of_lt (n : ℤ) (x : ℚ) (h : (x : ℝ) < (n : ℝ) + 1 / 2) :
    aeEffRound x ≤ n := by
  rw [aeEffRound_eq_intFloor]
  apply Int.floor_le_iff.mpr
  linarith

/-- A rational at least `n+1/2` rounds to an integer at least `n+1`. -/
theorem le_aeEffRound_of_le (n : ℤ) (x : ℚ) (h : (n : ℝ) + 1 / 2 ≤ (x : ℝ)) :
    n + 1 ≤ aeEffRound x := by
  rw [aeEffRound_eq_intFloor]
  apply Int.le_floor.mpr
  push_cast
  linarith

/-- Arbitrarily close to each half-integer, there are rationals rounding to each of its two
neighboring integers. -/
theorem aeEffRound_boundary_dense (n : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x y : ℚ,
      |(x : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound x = n ∧
        |(y : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound y = n + 1 := by
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn (lt_min hε one_pos : (0 : ℝ) < min ε 1)
  have hδ1 : (δ : ℝ) < 1 := lt_of_lt_of_le hδε (min_le_right ε 1)
  have hδe : (δ : ℝ) < ε := lt_of_lt_of_le hδε (min_le_left ε 1)
  have hδ : 0 < δ := Rat.cast_pos.mp hδ0
  refine ⟨(n : ℚ) + 1 / 2 - δ, (n : ℚ) + 1 / 2, ?_, ?_, ?_, ?_⟩
  · have h : (((n : ℚ) + 1 / 2 - δ : ℚ) : ℝ) - ((n : ℝ) + 1 / 2) = -(δ : ℝ) := by
      push_cast
      ring
    rw [h, abs_neg, abs_of_nonneg (le_of_lt hδ0)]
    exact hδe
  · rw [aeEffRound_eq_intFloor]
    apply Int.floor_eq_iff.mpr
    constructor
    · push_cast
      nlinarith
    · push_cast
      nlinarith
  · have h : (((n : ℚ) + 1 / 2 : ℚ) : ℝ) = ((n : ℝ) + 1 / 2) := by
      push_cast
      ring
    rw [h, sub_self, abs_zero]
    exact hε
  · rw [aeEffRound_eq_intFloor]
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith

/-- Effective counting rounds the native rational scalar estimate after multiplication by `N`. -/
theorem aeEffCount_eq (N M k : ℕ) (z : Fin M) :
    aeEffCount N M k z =
      aeEffRound (((N : ℚ) * nativeAEDecode M k z : ℚ)) := rfl

/-- Scaling native scalar decoding by `N` gives error at most `N*2^(-k)` relative to the scaled
ideal amplitude estimate. -/
theorem nativeScaled_error (N M k : ℕ) (z : Fin M) :
    |((((N : ℚ) * nativeAEDecode M k z : ℚ)) : ℝ) - (N : ℝ) * aeEstimate M z| ≤
      (N : ℝ) * ((2 : ℝ)⁻¹) ^ k := by
  have h := (native_ae_computed_scalar_precision M k z).2.2
  have hcast : (((((N : ℚ) * nativeAEDecode M k z : ℚ)) : ℝ)) =
      (N : ℝ) * (nativeAEDecode M k z : ℝ) := by
    push_cast
    rfl
  rw [hcast, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)

/-- The effective integer count differs from the scaled ideal amplitude estimate by at most
`N*2^(-k)+1/2`. -/
theorem aeEffCount_error (N M k : ℕ) (z : Fin M) :
    |(aeEffCount N M k z : ℝ) - (N : ℝ) * aeEstimate M z| ≤
      (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2 := by
  have h1 := aeEffRound_error ((((N : ℚ) * nativeAEDecode M k z : ℚ)))
  have h2 := nativeScaled_error N M k z
  have htri := abs_sub_le
    (((aeEffRound ((((N : ℚ) * nativeAEDecode M k z : ℚ))) : ℤ) : ℝ))
    ((((((N : ℚ) * nativeAEDecode M k z : ℚ))) : ℝ)) ((N : ℝ) * aeEstimate M z)
  have hgoal : ((aeEffCount N M k z : ℤ) : ℝ) =
      (((aeEffRound ((((N : ℚ) * nativeAEDecode M k z : ℚ))) : ℤ) : ℝ)) := rfl
  rw [hgoal]
  have hswap := abs_sub_comm (((((N : ℚ) * nativeAEDecode M k z : ℚ))) : ℝ)
    (((aeEffRound ((((N : ℚ) * nativeAEDecode M k z : ℚ))) : ℤ) : ℝ))
  rw [hswap] at h1
  linarith

/-- The effective integer count differs from half-up rounding of the ideal scaled estimate by at
most `effRoundSlack N k`. -/
theorem aeEffCount_near_floor (N M k : ℕ) (z : Fin M) :
    |(aeEffCount N M k z : ℝ) - ((⌊(N : ℝ) * aeEstimate M z + 1 / 2⌋ : ℤ) : ℝ)| ≤
      effRoundSlack N k := by
  set a : ℝ := (((((N : ℚ) * nativeAEDecode M k z : ℚ))) : ℝ) with ha
  set b : ℝ := ((N : ℝ) * aeEstimate M z) with hb
  have hAB : |a - b| ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k := by
    rw [ha, hb]
    exact nativeScaled_error N M k z
  have hL : ((aeEffCount N M k z : ℤ) : ℝ) = ((Int.floor (a + 1 / 2) : ℤ) : ℝ) := by
    rw [ha]
    have h1 : aeEffCount N M k z = aeEffRound ((((N : ℚ) * nativeAEDecode M k z : ℚ))) := rfl
    rw [h1, aeEffRound_eq_intFloor]
  have hR : ((⌊(N : ℝ) * aeEstimate M z + 1 / 2⌋ : ℤ) : ℝ) =
      ((Int.floor (b + 1 / 2) : ℤ) : ℝ) := by
    rw [hb]
  rw [hL, hR]
  have hu : (Int.floor (a + 1 / 2) : ℝ) ≤ a + 1 / 2 := Int.floor_le _
  have hv : (b + 1 / 2) < (Int.floor (b + 1 / 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hw : (Int.floor (b + 1 / 2) : ℝ) ≤ b + 1 / 2 := Int.floor_le _
  have hz : (a + 1 / 2) < (Int.floor (a + 1 / 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hpos : (0 : ℝ) ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k := by positivity
  have hab : a - b ≤ |a - b| := le_abs_self _
  have hba : b - a ≤ |a - b| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hss : effRoundSlack N k = 1 + (N : ℝ) * ((2 : ℝ)⁻¹) ^ k := rfl
  rw [hss]
  apply abs_le.mpr
  constructor <;> linarith

/-- The effective count on the Corollary 14 grid differs from its ideal rounded output by at
most `effRoundSlack N k`. -/
theorem aeEffCount_near_cor14Output (N k : ℕ) (z : Fin (approxCountCor14Grid N)) :
    |(aeEffCount N (approxCountCor14Grid N) k z : ℝ) -
        (approxCountCor14Output N z : ℝ)| ≤ effRoundSlack N k := by
  have h : approxCountCor14Output N z =
      ⌊(N : ℝ) * aeEstimate (approxCountCor14Grid N) z + 1 / 2⌋ := rfl
  rw [h]
  exact aeEffCount_near_floor N (approxCountCor14Grid N) k z

/-- The effective basic approximate counting output differs from its ideal rounded output by at
most `effRoundSlack N k`. -/
theorem aeEffCount_near_basicOutput (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) (k : ℕ) :
    |(basicApproxCountEffOutput N ε ω y k : ℝ) -
        (basicApproxCountOutput N ε ω y : ℝ)| ≤ effRoundSlack N k := by
  have h1 : basicApproxCountEffOutput N ε ω y k =
      aeEffCount N (basicApproxCountFinalM ε (basicApproxCountStop N ω)) k y := rfl
  have h2 : basicApproxCountOutput N ε ω y =
      ⌊(N : ℝ) * aeEstimate (basicApproxCountFinalM ε (basicApproxCountStop N ω)) y + 1 / 2⌋ := rfl
  rw [h1, h2]
  exact aeEffCount_near_floor N (basicApproxCountFinalM ε (basicApproxCountStop N ω)) k y

/-- The effective count differs from the exact counting procedure's ideal rounded output by at
most `effRoundSlack N k`. -/
theorem aeEffCount_near_exactOutput (N M k : ℕ) (y : Fin M) :
    |(aeEffCount N M k y : ℝ) - (BHMTTh17.exactCountOutput N y : ℝ)| ≤
      effRoundSlack N k := by
  have h : BHMTTh17.exactCountOutput N y =
      ⌊(N : ℝ) * aeEstimate M y + 1 / 2⌋ := rfl
  rw [h]
  exact aeEffCount_near_floor N M k y

/-- Collects half-up rounding laws and finite-precision counting guarantees, including Corollary
14, basic approximate counting, and the exact counting procedure with rounding slack
[BrassardEtAl2002]. It also records the corresponding cost and budget inequalities. -/
theorem clause90 :

  (∀ x : ℚ, |(x : ℝ) - (aeEffRound x : ℝ)| ≤ 1 / 2) ∧
    ((1 : ℝ) / 2 ≤ 2 / 3) ∧
    (∀ n : ℤ, aeEffRound n = n) ∧
    (∀ n : ℤ, aeEffRound (n + 1 / 2) = n + 1) ∧
    (∀ (n : ℤ) (x : ℚ), (x : ℝ) < (n : ℝ) + 1 / 2 → aeEffRound x ≤ n) ∧
    (∀ (n : ℤ) (x : ℚ), (n : ℝ) + 1 / 2 ≤ (x : ℝ) → n + 1 ≤ aeEffRound x) ∧
    (∀ (n : ℤ) (ε : ℝ), 0 < ε →
      ∃ x y : ℚ,
        |(x : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound x = n ∧
          |(y : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound y = n + 1) ∧

  (NativeScalarPrecision ∧
    (∀ (N M k : ℕ) (z : Fin M),
      |(aeEffCount N M k z : ℝ) - (N : ℝ) * aeEstimate M z| ≤
        (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2)) ∧

  ((∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N), 2 ≤ N →
      ∀ (hM : 2 ≤ approxCountCor14Grid N),
      let t : ℝ := (S.card : ℝ)
      (8 : ℝ) / Real.pi ^ 2 ≤
        ∑ z ∈ Finset.univ.filter (fun z : Fin (approxCountCor14Grid N) =>
          |(approxCountCor14Output N z : ℝ) - t| < cor14Width N t),
          (aeLaw (approxCountCor14Grid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM).prob z) ∧
    (∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N), 2 ≤ N →
      ∀ (k : ℕ) (hM : 2 ≤ approxCountCor14Grid N),
      let t : ℝ := (S.card : ℝ)
      (8 : ℝ) / Real.pi ^ 2 ≤
        ∑ z ∈ Finset.univ.filter (fun z : Fin (approxCountCor14Grid N) =>
          |(aeEffCount N (approxCountCor14Grid N) k z : ℝ) - t| < cor14EffWidth N k t),
          (aeLaw (approxCountCor14Grid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM).prob z) ∧
    (∀ S : Finset (Fin 1),
      cor14N1Output S = (S.card : ℤ) ∧
        |(cor14N1Output S : ℝ) - (S.card : ℝ)| < cor14Width 1 (S.card : ℝ) ∧
        (8 : ℝ) / Real.pi ^ 2 ≤ 1)) ∧

  (∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) (k : ℕ),
      (S.card = 0 →
        (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            basicApproxCountEffZero hN S ε ω (hω ω) k) = 1) ∧
      (0 < S.card →
        (2 : ℝ) / 3 ≤
          ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
            basicApproxCountPrefixWeight hN S ω *
              basicApproxCountEffGood hN S ε ω (hω ω) k)) ∧

  (∀ (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
      (hM₀ : 2 ≤ BHMTTh17.exactCountM₀ N)
      (hM : ∀ z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N),
        2 ≤ BHMTTh17.exactCountGrid N
          ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
          ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) (k : ℕ),
    (2 : ℝ) / 3 ≤ exactCountEffSuccessMass hN S hM₀ hM k ∧
      BHMTTh17.exactCountCostMass hN S hM₀ hM ≤
        1000 * Real.sqrt (((S.card : ℝ) + 1) * ((N : ℝ) - (S.card : ℝ) + 1))) ∧

  (∀ N k : ℕ,
    Nat.clog 2 (N + 1) + k ≤ effCountBitBudget N k ∧
      2 * effCountBitBudget N k ≤ effCountSpaceBudget N k)
 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact aeEffRound_error
  · norm_num
  · exact aeEffRound_intCast
  · exact aeEffRound_half_up
  · exact aeEffRound_le_of_lt
  · exact le_aeEffRound_of_le
  · exact aeEffRound_boundary_dense
  · refine ⟨native_ae_computed_scalar_precision, ?_⟩
    intro N M k z
    exact aeEffCount_error N M k z
  · refine ⟨?_, ?_, ?_⟩
    · intro N S hN hN2 hM
      exact bhmt_corollary14_rounded_count N S hN hN2 hM
    · intro N S hN hN2 k hM
      have hbase := bhmt_corollary14_rounded_count N S hN hN2 hM
      have hsub : (Finset.univ.filter
            (fun z : Fin (approxCountCor14Grid N) =>
              |(approxCountCor14Output N z : ℝ) - (S.card : ℝ)| <
                cor14Width N (S.card : ℝ)))
          ⊆ Finset.univ.filter
            (fun z : Fin (approxCountCor14Grid N) =>
              |(aeEffCount N (approxCountCor14Grid N) k z : ℝ) - (S.card : ℝ)| <
                cor14EffWidth N k (S.card : ℝ)) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        have hbridge := aeEffCount_near_cor14Output N k z
        have htri := abs_sub_le ((aeEffCount N (approxCountCor14Grid N) k z : ℝ))
          ((approxCountCor14Output N z : ℝ)) ((S.card : ℝ))
        have h0 : (0 : ℝ) ≤ effRoundSlack N k := by
          unfold effRoundSlack
          positivity
        show |(aeEffCount N (approxCountCor14Grid N) k z : ℝ) - (S.card : ℝ)| <
          cor14Width N (S.card : ℝ) + effRoundSlack N k
        linarith
      exact le_trans hbase
        (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => (aeLaw (approxCountCor14Grid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM).nonneg i))
    · intro S
      have hout : cor14N1Output S = (S.card : ℤ) := by
        by_cases h : (0 : Fin 1) ∈ S
        · have hS : S = Finset.univ := Finset.eq_univ_of_forall (fun x => by
            have : x = 0 := Fin.fin_one_eq_zero x
            rw [this]
            exact h)
          simp [cor14N1Output, hS]
        · have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by
            have : x = 0 := Fin.fin_one_eq_zero x
            rw [this] at hx
            exact h hx)
          simp [cor14N1Output, hS]
      refine ⟨hout, ?_, ?_⟩
      · rw [hout]
        push_cast
        rw [sub_self, abs_zero]
        show (0 : ℝ) < cor14Width 1 (S.card : ℝ)
        unfold cor14Width
        positivity
      · have hpi : (8 : ℝ) ≤ Real.pi ^ 2 := by
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        exact (div_le_one (sq_pos_of_pos Real.pi_pos)).mpr hpi
  · intro N S hN ε hε hε1 hω k
    have hz : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountFinalZero hN S ε ω (hω ω) ≤
          basicApproxCountEffZero hN S ε ω (hω ω) k := by
      intro ω
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        have hbridge := aeEffCount_near_basicOutput N ε ω y k
        have hy0 : (basicApproxCountOutput N ε ω y : ℝ) = 0 := by
          exact_mod_cast hy
        have h0 : (0 : ℝ) ≤ effRoundSlack N k := by
          unfold effRoundSlack
          positivity
        show |(basicApproxCountEffOutput N ε ω y k : ℝ)| ≤ effRoundSlack N k
        have h : |(basicApproxCountEffOutput N ε ω y k : ℝ)| =
            |(basicApproxCountEffOutput N ε ω y k : ℝ) -
              (basicApproxCountOutput N ε ω y : ℝ)| := by
          rw [hy0, sub_zero]
        rw [h]
        exact hbridge
      · intro y _ _
        exact (basicApproxCountFinalLaw hN S ε ω (hω ω)).nonneg y
    have hzle : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountEffZero hN S ε ω (hω ω) k ≤ 1 := by
      intro ω
      have h1 : basicApproxCountEffZero hN S ε ω (hω ω) k =
          ∑ y ∈ Finset.univ.filter
              (fun y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω)) =>
                |(basicApproxCountEffOutput N ε ω y k : ℝ)| ≤ effRoundSlack N k),
            (basicApproxCountFinalLaw hN S ε ω (hω ω)).prob y := rfl
      rw [h1]
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun y _ _ => (basicApproxCountFinalLaw hN S ε ω (hω ω)).nonneg y)).trans_eq
        (basicApproxCountFinalLaw hN S ε ω (hω ω)).sum_one
    have hg : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountFinalGood hN S ε ω (hω ω) ≤
          basicApproxCountEffGood hN S ε ω (hω ω) k := by
      intro ω
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        have hbridge := aeEffCount_near_basicOutput N ε ω y k
        have htri := abs_sub_le ((basicApproxCountEffOutput N ε ω y k : ℝ))
          ((basicApproxCountOutput N ε ω y : ℝ)) ((S.card : ℝ))
        have h0 : (0 : ℝ) ≤ effRoundSlack N k := by
          unfold effRoundSlack
          positivity
        show |(basicApproxCountEffOutput N ε ω y k : ℝ) - (S.card : ℝ)| ≤
          ε * (S.card : ℝ) + effRoundSlack N k
        linarith
      · intro y _ _
        exact (basicApproxCountFinalLaw hN S ε ω (hω ω)).nonneg y
    refine ⟨?_, ?_⟩
    · intro hS
      have hbase := bhmt_basic_approx_count_zero hN S hS ε hω
      have hp0 : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          0 ≤ basicApproxCountPrefixWeight hN S ω := by
        intro ω
        exact Finset.prod_nonneg (fun l _ =>
          (basicApproxCountLoopLaw hN S l).nonneg (ω l))
      have hge : (1 : ℝ) ≤
          ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
            basicApproxCountPrefixWeight hN S ω *
              basicApproxCountEffZero hN S ε ω (hω ω) k := by
        rw [← hbase]
        exact Finset.sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left (hz ω) (hp0 ω))
      have hle : (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            basicApproxCountEffZero hN S ε ω (hω ω) k) ≤ 1 := by
        calc
          (∑ ω, basicApproxCountPrefixWeight hN S ω *
              basicApproxCountEffZero hN S ε ω (hω ω) k) ≤
              ∑ ω, basicApproxCountPrefixWeight hN S ω * 1 :=
            Finset.sum_le_sum (fun ω _ =>
              mul_le_mul_of_nonneg_left (hzle ω) (hp0 ω))
          _ = ∑ ω, basicApproxCountPrefixWeight hN S ω := by simp only [mul_one]
          _ = 1 := basicApproxCountPrefixWeight_sum hN S
      exact le_antisymm hle hge
    · intro hS
      have hbase := bhmt_basic_approx_count_positive hN S hS ε hε hε1 hω
      have hp0 : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          0 ≤ basicApproxCountPrefixWeight hN S ω := by
        intro ω
        exact Finset.prod_nonneg (fun l _ =>
          (basicApproxCountLoopLaw hN S l).nonneg (ω l))
      refine le_trans hbase ?_
      exact Finset.sum_le_sum (fun ω _ =>
        mul_le_mul_of_nonneg_left (hg ω) (hp0 ω))
  · intro N hN S hM₀ hM k
    have hbase := bhmt_theorem17_exact_count N hN S hM₀ hM
    refine ⟨?_, hbase.2⟩
    have hinner : ∀ z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N),
        (∑ y ∈ Finset.univ.filter
            (fun y : Fin (BHMTTh17.exactCountGrid N
                ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
                ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) =>
              BHMTTh17.exactCountOutput N y = ((S.card : ℕ) : ℤ)),
          (aeLaw (BHMTTh17.exactCountGrid N
              ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
              ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂))
            (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) (hM z₁ z₂)).prob y) ≤
          exactCountEffFinalMass hN S (hM z₁ z₂) k := by
      intro z₁ z₂
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        have hbridge := aeEffCount_near_exactOutput N
          (BHMTTh17.exactCountGrid N
            ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
            ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) k y
        have hy' : (BHMTTh17.exactCountOutput N y : ℝ) = (S.card : ℝ) := by
          exact_mod_cast hy
        show |(aeEffCount N
            (BHMTTh17.exactCountGrid N
              ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
              ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) k y : ℝ) -
            (S.card : ℝ)| ≤ effRoundSlack N k
        have h : |(aeEffCount N
              (BHMTTh17.exactCountGrid N
                ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
                ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) k y : ℝ) -
            (S.card : ℝ)| =
            |(aeEffCount N
                (BHMTTh17.exactCountGrid N
                  ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
                  ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) k y : ℝ) -
              (BHMTTh17.exactCountOutput N y : ℝ)| := by
          rw [hy']
        rw [h]
        exact hbridge
      · intro y _ _
        exact (aeLaw (BHMTTh17.exactCountGrid N
          ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
          ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂))
          (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) (hM z₁ z₂)).nonneg y
    have hle : BHMTTh17.exactCountSuccessMass hN S hM₀ hM ≤
        exactCountEffSuccessMass hN S hM₀ hM k := by
      simp only [BHMTTh17.exactCountSuccessMass, exactCountEffSuccessMass]
      apply Finset.sum_le_sum
      intro z₁ _
      apply Finset.sum_le_sum
      intro z₂ _
      apply mul_le_mul_of_nonneg_left (hinner z₁ z₂)
      exact mul_nonneg
        ((aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM₀).nonneg z₁)
        ((aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM₀).nonneg z₂)
    exact le_trans hbase.1 hle
  · intro N k
    show Nat.clog 2 (N + 1) + k ≤ effCountBitBudget N k ∧
      2 * effCountBitBudget N k ≤ effCountSpaceBudget N k
    refine ⟨?_, ?_⟩
    · show Nat.clog 2 (N + 1) + k ≤ Nat.clog 2 (N + 1) + k + 8
      exact Nat.le_add_right _ 8
    · show 2 * (Nat.clog 2 (N + 1) + k + 8) ≤ 2 * (Nat.clog 2 (N + 1) + k + 8) + 4
      exact Nat.le_add_right _ 4

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
