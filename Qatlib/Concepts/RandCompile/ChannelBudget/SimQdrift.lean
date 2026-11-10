/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.SimQdriftDefs
import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.RandCompile.EffectiveInput
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift
open Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined
open Qatlib.Concepts.RandCompile.ChannelBudget.QdriftSimulation
open Qatlib.Concepts.RandCompile.ChannelBudget.SimQdriftDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.RandCompile.ChannelBudget.SimQdrift

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

theorem dyadicRead_relParamRead {x : ℝ} {q : ℕ → ℚ} (h : DyadicRead x q) :
    ∀ k, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k := fun k => h.accuracy k

theorem dyadicLowerRead_relLowerParamRead {x : ℝ} {q : ℕ → ℚ} (h : DyadicLowerRead x q) :
    ∀ k, (q k : ℝ) ≤ x ∧ |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k := by
  intro k
  refine ⟨h.lower k, ?_⟩
  rw [abs_of_nonneg (by linarith [h.lower k])]
  exact h.deficit k

theorem simDigitProgram_eval {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) :
    ratEval (simDigitProgram b (a j)) * (2 : ℚ) ^ b = (simDigit b a j : ℚ) := by
  have hfloor : (⌊(a j) * (2 : ℚ) ^ b + 1 / 2⌋ : ℤ) = dyadicCoefficient b (a j) := by
    unfold dyadicCoefficient
    rw [show (a j) * (2 : ℚ) ^ b + 1 / 2 = (2 : ℚ) ^ b * (a j) + 1 / 2 by ring]
  have harg : (a j + (1 / 2 : ℚ) / (2 : ℚ) ^ b) * (2 : ℚ) ^ b
      = (a j) * (2 : ℚ) ^ b + 1 / 2 := by
    field_simp
  unfold simDigitProgram ratDigits ratAdd ratLit ratEval
  rw [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_digits,
      Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_add]
  simp only [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval]
  rw [harg, hfloor]
  unfold simDigit
  field_simp

theorem simDigit_roundtrip {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) :
    |(simDigitValue b (simDigit b a j) : ℝ) - (a j : ℝ)| ≤ (1 / 2 : ℝ) ^ (b + 1) := by
  have h := dyadicCoefficient_error b (a j)
  have h' : |((dyadicCoefficient b (a j) : ℤ) : ℝ) / (2 : ℝ) ^ b - (a j : ℝ)|
      ≤ (1 / 2 : ℝ) ^ (b + 1) := by
    convert! h using 1 <;> simp only [one_div, inv_pow]
  have hcast : ((dyadicCoefficient b (a j) : ℤ) : ℝ) / (2 : ℝ) ^ b
      = ((simDigitValue b (simDigit b a j) : ℝ)) := by
    unfold simDigitValue simDigit
    push_cast
    ring
  rw [← hcast]
  exact h'

theorem simDigit_le_weightTotal {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) :
    SimQdriftDefs.simWeights b a j ≤ weightTotal (SimQdriftDefs.simWeights b a) := by
  have h2 : SimQdriftDefs.simWeights b a j ≤ ∑ j' : Fin L, SimQdriftDefs.simWeights b a j' :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa [weightTotal] using! h2

theorem simDigit_abs_eq_weight {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) :
    |simDigit b a j| = (SimQdriftDefs.simWeights b a j : ℤ) := by
  have hz := Int.abs_eq_natAbs (dyadicCoefficient b (a j))
  have hz' : (SimQdriftDefs.simWeights b a j : ℤ) = ((dyadicCoefficient b (a j)).natAbs : ℤ) :=
      rfl
  unfold simDigit
  rw [hz, hz']

theorem simDigit_fits_width {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) :
    |simDigit b a j| < (2 ^ (simDigitWidth b a) : ℤ) := by
  have hlt : SimQdriftDefs.simWeights b a j < 2 ^ (simDigitWidth b a) := by
    have hw := simDigit_le_weightTotal b a j
    have hclog : weightTotal (SimQdriftDefs.simWeights b a) + 1
        ≤ 2 ^ (Nat.clog 2 (weightTotal (SimQdriftDefs.simWeights b a) + 1)) := by
      have h := (Nat.clog_le_iff_le_pow (by omega : (1 : ℕ) < 2)
        (x := weightTotal (SimQdriftDefs.simWeights b a) + 1)
        (y := Nat.clog 2 (weightTotal (SimQdriftDefs.simWeights b a) + 1))).mp (le_refl _)
      simpa using! h
    have h1 : SimQdriftDefs.simWeights b a j < 2 ^ (Nat.clog 2 (weightTotal (SimQdriftDefs.simWeights b a) + 1)) := by
      omega
    have h2 : 2 ^ (Nat.clog 2 (weightTotal (SimQdriftDefs.simWeights b a) + 1))
        ≤ 2 ^ (simDigitWidth b a) := by
      unfold simDigitWidth
      rw [pow_succ]
      omega
    exact lt_of_lt_of_le h1 h2
  rw [simDigit_abs_eq_weight b a j]
  exact_mod_cast hlt

theorem simDigitTableSpace_eq {L : ℕ} (b : ℕ) (a : Fin L → ℚ) :
    simDigitTableSpace b a = L * simDigitWidth b a := rfl

theorem simCountProgram_eval (W T : ℕ) (eQ : ℚ) :
    ratEval (simCountProgram W T eQ)
      = ↑(Rat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)) := by
  unfold simCountProgram ratCeil ratDiv ratMul ratLit ratEval
  rw [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_ceil, Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_div,
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_mul, Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_mul,
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_mul, Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_mul]
  simp only [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval]
  congr 1
  ring

theorem simFuelProgram_eval (n s : ℕ) :
    ratEval (simFuelProgram n s) = (s + Nat.clog 2 n + 2 : ℚ) := by
  have hnum : ((n : ℚ)).num.natAbs = n := by simp
  unfold simFuelProgram ratAdd ratLog2 ratLit ratEval
  rw [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_add, Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_add,
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_eval_log2]
  simp only [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval]
  rw [hnum]
  push_cast
  ring

theorem simRunLedger_ledger (L : ℕ) (k : ℕ) (prog : RatProgram) (digitSpace B : ℕ) :
    (simRunLedger L k prog digitSpace B).ops = (ratCost prog).total ∧
    (simRunLedger L k prog digitSpace B).digitReads = L * (k + 1) ∧
    (simRunLedger L k prog digitSpace B).paramReads = 2 * (k + 1) ∧
    (simRunLedger L k prog digitSpace B).scanned = k + 1 ∧
    (simRunLedger L k prog digitSpace B).bitTime =
      ((simRunLedger L k prog digitSpace B).ops
          + (simRunLedger L k prog digitSpace B).digitReads) * (B + 2) * (B + 2) ∧
    (simRunLedger L k prog digitSpace B).bitSpace = B + digitSpace + 16 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
  rfl

theorem simRunBitLength_digit (k : ℕ) (tq eq : ℕ → ℚ) (digitSpace : ℕ) :
    digitSpace ≤ simRunBitLength k tq eq digitSpace := by
  unfold simRunBitLength
  omega

theorem simRunBitLength_read (k : ℕ) (tq eq : ℕ → ℚ) (digitSpace : ℕ) (k' : ℕ)
    (hk' : k' ≤ k) :
    simRatBits (tq k') ≤ simRunBitLength k tq eq digitSpace := by
  have hsup : max (simRatBits (tq k')) (simRatBits (eq k'))
      ≤ Finset.sup' (Finset.range (k + 1)) (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩)
        (fun k'' => max (simRatBits (tq k'')) (simRatBits (eq k''))) := by
    refine Finset.le_sup'
      (fun k'' => max (simRatBits (tq k'')) (simRatBits (eq k''))) (b := k')
      (Finset.mem_range.mpr (by omega))
  have hle : simRatBits (tq k') ≤ max (simRatBits (tq k')) (simRatBits (eq k')) := by
    exact le_max_left _ _
  unfold simRunBitLength
  omega

theorem simScanReachesSimulation : ∀ (L D : ℕ) (a : Fin L → ℚ) (b : ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t ε : ℝ) (tq eq : ℕ → ℚ) (fuel T : ℕ),
    DyadicRead t tq → DyadicLowerRead ε eq →
    0 < weightTotal (SimQdriftDefs.simWeights b a) → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    (∃ k, k ≤ fuel ∧ scanCert (tq k) (eq k) T k = true) →
    ∃ (T' s : ℕ),
      |t| ≤ T' ∧
      (2 : ℝ)⁻¹ ^ s / 2 ≤ ε ∧
      finiteDiamondDistance
          (fairQdriftActualMap (SimQdriftDefs.simWeights b a) j0
            (fairQdriftSteps (weightTotal (SimQdriftDefs.simWeights b a)) T' s)
            (fairQdriftFuel (fairQdriftSteps (weightTotal (SimQdriftDefs.simWeights b a)) T' s) s) K t)
          (conjBranch (HamiltonianEvolution (∑ j, ((SimQdriftDefs.simWeights b a) j : ℂ) • K j) t))
        ≤ ENNReal.ofReal ε := by
  intro L D a b j0 K t ε tq eq fuel T htq heq hW hK hex
  obtain ⟨k, hk, hc⟩ := hex
  have hc' : Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsCertified eq k
      = true := by
    have h1 : 0 < eq k - (1 / 2 : ℚ) ^ k := by
      have h :=
          (Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.scanCert_iff).mp hc
      rw [← _root_.one_div_pow] at h
      exact h.1
    simp only [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsCertified,
      decide_eq_true_eq]
    exact h1
  obtain ⟨T', s, h1, h2, h3⟩ :=
    Qatlib.Concepts.RandCompile.ChannelBudget.QdriftSimulation.clause27_endpoint
      L D a b j0 K t ε tq eq fuel
      (dyadicRead_relParamRead htq) (dyadicLowerRead_relLowerParamRead heq)
      hW hK ⟨k, hk, hc'⟩
  exact ⟨T', s, h1, h2, h3⟩

theorem simTightCount_eq_source (W T : ℕ) (eQ : ℚ) :
    simTightCount W T eQ = SimQdriftDefs.sourceTightCount W T eQ := rfl

theorem simGateBudget_eq (m n : ℕ) :
    simGateBudget m n = n * SimQdriftDefs.synthGateBudget m := rfl

theorem simQuantumSpace_eq (m : ℕ) :
    simQuantumSpace m = m + (m + 1) := rfl

theorem simClassicalSpace_eq (n L : ℕ) :
    simClassicalSpace n L = Nat.clog 2 (max 1 n) + Nat.clog 2 (max 1 L) := rfl

theorem simStep_synthesis (m : ℕ) (K : Matrix (Reg m) (Reg m) ℂ) (θ : ℝ)
    (hK : K.IsHermitian) :
    ∃ gs : List (ReflectionGate (m + (m + 1))),
      reflectionLegal gs ∧
      gs.length ≤ SimQdriftDefs.synthGateBudget m ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg m),
        Run 1 (reflectionCompile gs) (knownFrameEmbed m ψ) =
          knownFrameEmbed m (HamiltonianEvolution K θ *ᵥ ψ) :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.hermitian_exponential_circuit_synthesis
    m K θ hK

theorem simSourceCount_le_budget (W T : ℕ) (eQ : ℚ) (he : 0 < eQ) :
    (SimQdriftDefs.sourceTightCount W T eQ : ℝ) ≤ 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (eQ : ℝ) + 1 := by
  have h1 := Nat.ceil_lt_add_one (a := 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)
    (by positivity)
  have h1' : ((Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) : ℚ) : ℝ)
      < ((2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ : ℚ) : ℝ) + 1 := by
    exact_mod_cast h1
  have h2 : (SimQdriftDefs.sourceTightCount W T eQ : ℝ)
      = ((Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) : ℚ) : ℝ) := by
    unfold SimQdriftDefs.sourceTightCount
    exact (Rat.cast_natCast (Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ))).symm
  rw [h2]
  have h3 : ((2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ : ℚ) : ℝ)
      = 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (eQ : ℝ) := by
    push_cast
    ring
  rw [h3] at h1'
  linarith

theorem simActualCount_oversize (W T : ℕ) (eQ : ℚ) (s : ℕ)
    (hW : 0 < W) (hT : 0 < T) (he : 0 < eQ) :
    (simActualCount W T s : ℝ) ≥
      simOversizeFactor eQ s * (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (eQ : ℝ)) := by
  have hcnt : (simActualCount W T s : ℝ)
      ≥ 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ s) := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ s := by exact_mod_cast (Nat.one_le_two_pow (n := s))
    have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hW0 : (0 : ℝ) ≤ (W : ℝ) := by positivity
    have hT0 : (0 : ℝ) ≤ (T : ℝ) := by positivity
    have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hW1 hW0
      nlinarith
    have hT2 : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hT1 hT0
      nlinarith
    have h1 : (1 : ℝ) ≤ 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ s) := by
      calc (1 : ℝ) ≤ 8 * (W : ℝ) ^ 2 := by nlinarith
        _ ≤ 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 := by
          have hh := mul_le_mul_of_nonneg_left hT2 (by positivity : (0 : ℝ) ≤ 8 * (W : ℝ) ^ 2)
          nlinarith
        _ ≤ 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ s) := by
          have hh := mul_le_mul_of_nonneg_left hp
            (by positivity : (0 : ℝ) ≤ 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2)
          nlinarith
    have h3 : (simActualCount W T s : ℝ)
        = max (1 : ℝ) (8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ s)) := by
      unfold simActualCount
      push_cast
      congr 1
    rw [h3]
    exact le_max_right _ _
  have hmul : simOversizeFactor eQ s * (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (eQ : ℝ))
      = 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ s) := by
    unfold simOversizeFactor
    field_simp
    ring
  rw [hmul]
  exact hcnt

theorem simPostSelect_no_free_lunch (L : ℕ) (w : Fin L → ℕ) (hW : 0 < weightTotal w)
    (K : Fin L → Operator 2) (n : ℕ) (t : ℝ) :
    SimQdriftDefs.ctrlCrossBlock
        (SimQdriftDefs.ctrlBlockMapIdx (SimQdriftDefs.postSelectedQdriftMap w hW n K t) SimQdriftDefs.coherentWitness) = 0 ∧
    SimQdriftDefs.ctrlCrossBlock SimQdriftDefs.coherentWitness ≠ 0 := by
  have hne : SimQdriftDefs.ctrlCrossBlock SimQdriftDefs.coherentWitness ≠ 0 := by
    intro hh
    have hh' := congrFun (congrFun hh 0) 0
    simp [SimQdriftDefs.ctrlCrossBlock, SimQdriftDefs.coherentWitness,
      Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlCrossBlock,
      Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.coherentWitness] at hh'
  exact ⟨Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.ctrlBlockMapIdx_cross_zero
      (SimQdriftDefs.postSelectedQdriftMap w hW n K t) SimQdriftDefs.coherentWitness, hne⟩

theorem simPostSelect_tight_count (L D : ℕ) (w : Fin L → ℕ)
    (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ)
    (hW : 0 < weightTotal w) (ht : |t| ≤ T)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) (hT : 0 < T) (he : 0 < eQ) :
    ∃ n : ℕ, 0 < n ∧
      finiteDiamondDistance (SimQdriftDefs.postSelectedQdriftMap w hW n K t)
        (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
        ≤ ENNReal.ofReal eQ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.QdriftSimulation.clause28_post_select_tight_count
    L D w K t T eQ hW ht hK hT he

theorem simPostSelect_fuel (n : ℕ) (eQ : ℚ) (he : 0 < eQ) :
    (n : ℝ) * ((2 : ℝ)⁻¹) ^ (simPostSelectFuel n eQ) ≤ (eQ : ℝ) := by
  have hclog : Nat.ceil ((n : ℚ) / eQ) ≤ 2 ^ (Nat.clog 2 (Nat.ceil ((n : ℚ) / eQ))) := by
    have h := (Nat.clog_le_iff_le_pow (by omega : (1 : ℕ) < 2)
      (x := Nat.ceil ((n : ℚ) / eQ))
      (y := Nat.clog 2 (Nat.ceil ((n : ℚ) / eQ)))).mp (le_refl _)
    simpa using! h
  have h1 : (Nat.ceil ((n : ℚ) / eQ) : ℝ) ≤ (2 : ℝ) ^ (simPostSelectFuel n eQ) := by
    have h2 : (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil ((n : ℚ) / eQ)))
        = (2 : ℝ) ^ (simPostSelectFuel n eQ) := by
      unfold simPostSelectFuel
      rfl
    rw [← h2]
    have h3 : ((Nat.ceil ((n : ℚ) / eQ) : ℚ) : ℝ)
        ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil ((n : ℚ) / eQ))) := by
      exact_mod_cast hclog
    exact h3
  have h2 : (n : ℝ) / (eQ : ℝ) ≤ (Nat.ceil ((n : ℚ) / eQ) : ℝ) := by
    have hceil' : ((n : ℚ) / eQ : ℚ) ≤ (Nat.ceil ((n : ℚ) / eQ) : ℚ) := Nat.le_ceil _
    have hceil'' : (((n : ℚ) / eQ : ℚ) : ℝ) ≤ ((Nat.ceil ((n : ℚ) / eQ) : ℚ) : ℝ) := by
      exact_mod_cast hceil'
    have hcast : (((n : ℚ) / eQ : ℚ) : ℝ) = (n : ℝ) / (eQ : ℝ) := by
      push_cast
      ring
    rw [hcast] at hceil''
    exact hceil''
  have h3 : (n : ℝ) / (eQ : ℝ) ≤ (2 : ℝ) ^ (simPostSelectFuel n eQ) := by
    exact h2.trans h1
  have h4 : (n : ℝ) * ((2 : ℝ)⁻¹) ^ (simPostSelectFuel n eQ)
      ≤ (n : ℝ) / (2 : ℝ) ^ (simPostSelectFuel n eQ) := by
    rw [div_eq_mul_inv, ← inv_pow]
  calc (n : ℝ) * ((2 : ℝ)⁻¹) ^ (simPostSelectFuel n eQ)
      ≤ (n : ℝ) / (2 : ℝ) ^ (simPostSelectFuel n eQ) := h4
    _ ≤ (eQ : ℝ) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (simPostSelectFuel n eQ) := by positivity
      apply (div_le_iff₀ hpos).mpr
      have h8 : (0 : ℝ) ≤ (eQ : ℝ) := by positivity
      have hh := mul_le_mul_of_nonneg_left h3 h8
      have h9 : (eQ : ℝ) * ((n : ℝ) / (eQ : ℝ)) = n := by field_simp
      linarith

theorem simTableI_gate_comparison (m : ℕ) (lam t eps deltaE pf : ℝ)
    (hlam : 0 < lam) (hdelta : 0 < deltaE) (hpf : 0 < pf)
    (hbudget : eps = deltaE ^ 2 * pf ^ 2) (hcmp : 2 * t ^ 2 * pf ≤ 133)
    (hB : 1 ≤ 133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3)) :
    simTableIGateCount m lam t eps ≤ simPeGateCount m lam deltaE pf := by
  have h1 := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.tableIQdriftCount_le_peCount
    lam t eps deltaE pf hlam hdelta hpf hbudget hcmp hB
  unfold simTableIGateCount simPeGateCount
  unfold simGateBudget
  exact Nat.mul_le_mul_right (SimQdriftDefs.synthGateBudget m) h1

theorem clause27_endpoint :
    (∀ (x : ℝ) (q : ℕ → ℚ), DyadicRead x q →
      ∀ k, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k) ∧
    (∀ (x : ℝ) (q : ℕ → ℚ), DyadicLowerRead x q →
      ∀ k, (q k : ℝ) ≤ x ∧ |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k) ∧
    (∀ (L : ℕ) (b : ℕ) (a : Fin L → ℚ) (j : Fin L),
      ratEval (simDigitProgram b (a j)) * (2 : ℚ) ^ b = (simDigit b a j : ℚ) ∧
      |(simDigitValue b (simDigit b a j) : ℝ) - (a j : ℝ)| ≤ (1 / 2 : ℝ) ^ (b + 1)) ∧
    (∀ (L : ℕ) (b : ℕ) (a : Fin L → ℚ),
      simDigitTableSpace b a = L * simDigitWidth b a ∧
      (∀ j, |simDigit b a j| < (2 ^ (simDigitWidth b a) : ℤ)) ∧
      (∀ j, SimQdriftDefs.simWeights b a j ≤ weightTotal (SimQdriftDefs.simWeights b a))) ∧
    (∀ (W T : ℕ) (eQ : ℚ),
      ratEval (simCountProgram W T eQ)
        = ↑(Rat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ))) ∧
    (∀ (n s : ℕ), ratEval (simFuelProgram n s) = (s + Nat.clog 2 n + 2 : ℚ)) ∧
    (∀ (p : RatProgram), ratNodes p = (ratCost p).total) ∧
    (∀ (L : ℕ) (k : ℕ) (prog : RatProgram) (digitSpace B : ℕ),
      (simRunLedger L k prog digitSpace B).ops = (ratCost prog).total ∧
      (simRunLedger L k prog digitSpace B).digitReads = L * (k + 1) ∧
      (simRunLedger L k prog digitSpace B).paramReads = 2 * (k + 1) ∧
      (simRunLedger L k prog digitSpace B).scanned = k + 1 ∧
      (simRunLedger L k prog digitSpace B).bitTime =
        ((simRunLedger L k prog digitSpace B).ops
            + (simRunLedger L k prog digitSpace B).digitReads) * (B + 2) * (B + 2) ∧
      (simRunLedger L k prog digitSpace B).bitSpace = B + digitSpace + 16) ∧
    (∀ (k : ℕ) (tq eq : ℕ → ℚ) (digitSpace : ℕ),
      digitSpace ≤ simRunBitLength k tq eq digitSpace ∧
      (∀ k' ≤ k, simRatBits (tq k') ≤ simRunBitLength k tq eq digitSpace)) ∧
    (∀ (L D : ℕ) (a : Fin L → ℚ) (b : ℕ) (j0 : Fin L) (K : Fin L → Operator D)
      (t ε : ℝ) (tq eq : ℕ → ℚ) (fuel T : ℕ),
      DyadicRead t tq → DyadicLowerRead ε eq →
      0 < weightTotal (SimQdriftDefs.simWeights b a) → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
      (∃ k, k ≤ fuel ∧ scanCert (tq k) (eq k) T k = true) →
      ∃ (T' s : ℕ),
        |t| ≤ T' ∧ (2 : ℝ)⁻¹ ^ s / 2 ≤ ε ∧
        finiteDiamondDistance
            (fairQdriftActualMap (SimQdriftDefs.simWeights b a) j0
              (fairQdriftSteps (weightTotal (SimQdriftDefs.simWeights b a)) T' s)
              (fairQdriftFuel (fairQdriftSteps (weightTotal (SimQdriftDefs.simWeights b a)) T' s) s) K t)
            (conjBranch (HamiltonianEvolution (∑ j, ((SimQdriftDefs.simWeights b a) j : ℂ) • K j) t))
          ≤ ENNReal.ofReal ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x q h
    exact dyadicRead_relParamRead h
  · intro x q h
    exact dyadicLowerRead_relLowerParamRead h
  · intro L b a j
    exact ⟨simDigitProgram_eval b a j, simDigit_roundtrip b a j⟩
  · intro L b a
    refine ⟨simDigitTableSpace_eq b a, fun j => simDigit_fits_width b a j, fun j =>
      simDigit_le_weightTotal b a j⟩
  · intro W T eQ
    exact simCountProgram_eval W T eQ
  · intro n s
    exact simFuelProgram_eval n s
  · intro p
    exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined.ratProgram_nodes_cost p
  · intro L k prog digitSpace B
    exact simRunLedger_ledger L k prog digitSpace B
  · intro k tq eq digitSpace
    exact ⟨simRunBitLength_digit k tq eq digitSpace,
      fun k' hk' => simRunBitLength_read k tq eq digitSpace k' hk'⟩
  · intro L D a b j0 K t ε tq eq fuel T htq heq hW hK hex
    exact simScanReachesSimulation L D a b j0 K t ε tq eq fuel T htq heq hW hK hex

theorem clause28_endpoint : ∀ (m : ℕ) (K : Matrix (Reg m) (Reg m) ℂ) (θ : ℝ), K.IsHermitian →
    (∃ gs : List (ReflectionGate (m + (m + 1))),
      reflectionLegal gs ∧
      gs.length ≤ SimQdriftDefs.synthGateBudget m ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg m),
        Run 1 (reflectionCompile gs) (knownFrameEmbed m ψ) =
          knownFrameEmbed m (HamiltonianEvolution K θ *ᵥ ψ)) ∧
    (∀ (W T : ℕ) (eQ : ℚ), simTightCount W T eQ = SimQdriftDefs.sourceTightCount W T eQ) ∧
    (∀ (W T : ℕ) (eQ : ℚ) (s : ℕ), 0 < W → 0 < T → 0 < eQ →
      (SimQdriftDefs.sourceTightCount W T eQ : ℝ) ≤ 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (eQ : ℝ) + 1 ∧
      (simActualCount W T s : ℝ) ≥
        simOversizeFactor eQ s * (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (eQ : ℝ))) ∧
    (∀ (m n : ℕ),
      simGateBudget m n = n * SimQdriftDefs.synthGateBudget m ∧
      simQuantumSpace m = m + (m + 1) ∧
      simClassicalSpace n m = Nat.clog 2 (max 1 n) + Nat.clog 2 (max 1 m)) := by
  intro m K θ hK
  refine ⟨simStep_synthesis m K θ hK, ?_, ?_, ?_⟩
  · intro W T eQ
    exact simTightCount_eq_source W T eQ
  · intro W T eQ s hW hT he
    exact ⟨simSourceCount_le_budget W T eQ he,
      simActualCount_oversize W T eQ s hW hT he⟩
  · intro m n
    exact ⟨simGateBudget_eq m n, simQuantumSpace_eq m, simClassicalSpace_eq n m⟩

theorem clause29_endpoint : ∀ (L : ℕ) (w : Fin L → ℕ) (hW : 0 < weightTotal w)
    (K : Fin L → Operator 2) (n : ℕ) (t : ℝ),
    SimQdriftDefs.ctrlCrossBlock
        (SimQdriftDefs.ctrlBlockMapIdx (SimQdriftDefs.postSelectedQdriftMap w hW n K t) SimQdriftDefs.coherentWitness) = 0 ∧
    SimQdriftDefs.ctrlCrossBlock SimQdriftDefs.coherentWitness ≠ 0 ∧
    (∀ (L D : ℕ) (w : Fin L → ℕ) (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ)
      (hW : 0 < weightTotal w) (ht : |t| ≤ T)
      (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) (hT : 0 < T) (he : 0 < eQ),
      ∃ n : ℕ, 0 < n ∧
        finiteDiamondDistance (SimQdriftDefs.postSelectedQdriftMap w hW n K t)
          (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
          ≤ ENNReal.ofReal eQ) ∧
    (∀ (n : ℕ) (eQ : ℚ), 0 < eQ →
      (n : ℝ) * ((2 : ℝ)⁻¹) ^ (simPostSelectFuel n eQ) ≤ (eQ : ℝ)) ∧
    (∀ (m : ℕ) (lam t eps deltaE pf : ℝ),
      0 < lam → 0 < deltaE → 0 < pf → eps = deltaE ^ 2 * pf ^ 2 → 2 * t ^ 2 * pf ≤ 133 →
      1 ≤ 133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3) →
      simTableIGateCount m lam t eps ≤ simPeGateCount m lam deltaE pf) := by
  intro L w hW K n t
  have h1 := simPostSelect_no_free_lunch L w hW K n t
  refine ⟨h1.1, h1.2, ?_, ?_, ?_⟩
  · intro L D w K t T eQ hW ht hK hT he
    exact simPostSelect_tight_count L D w K t T eQ hW ht hK hT he
  · intro n eQ he
    exact simPostSelect_fuel n eQ he
  · intro m lam t eps deltaE pf hlam hdelta hpf hbudget hcmp hB
    exact simTableI_gate_comparison m lam t eps deltaE pf hlam hdelta hpf hbudget hcmp hB

end Qatlib.Concepts.RandCompile.ChannelBudget.SimQdrift
