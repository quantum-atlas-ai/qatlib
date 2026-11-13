/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.QdriftSimulation
import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs

/-!
# Definitions for explicit qDRIFT simulation costs

This module exposes the rational-program and dyadic-read interfaces used to account for qDRIFT
preprocessing and simulation costs. It defines signed coefficient digits, finite arithmetic
programs, run ledgers, and gate and space budgets for the randomized simulation setting of
[Campbell2019].

## Main statements

* `simDigitProgram`: encodes rounded dyadic coefficient extraction as a rational program.
* `SimRunLedger`: records scan, read, operation, and bit-resource counts.
* `simActualCount`: chooses the positive actual simulation step count.
* `simPostSelectFuel`: sets the rejection-fuel budget from the step count and tolerance.

## References

* [Campbell, 2019][Campbell2019]
-/

open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.RandCompile.EffectiveInput

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.RandCompile.ChannelBudget.SimQdriftDefs

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- Alias for the dyadic parameter-read interface used by refined finite-diamond qDRIFT. -/
abbrev DyadicRead :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.DyadicRead

/-- Alias for the dyadic lower parameter-read interface used by refined finite-diamond qDRIFT. -/
abbrev DyadicLowerRead :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.DyadicLowerRead

/-- Alias for the syntax of finite rational arithmetic programs. -/
abbrev RatProgram :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram

/-- Alias for the rational-program resource-cost record. -/
abbrev RatCost := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatCost

/-- The rational-program constructor for a literal rational value. -/
abbrev ratLit : ℚ → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.lit

/-- The rational-program constructor for addition. -/
abbrev ratAdd : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.add

/-- The rational-program constructor for multiplication. -/
abbrev ratMul : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.mul

/-- The rational-program constructor for division. -/
abbrev ratDiv : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.div

/-- The rational-program constructor for an integer ceiling. -/
abbrev ratCeil : RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.ceil

/-- The rational-program constructor for the binary ceiling-logarithm operation. -/
abbrev ratLog2 : RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.log2

/-- The rational-program constructor for extracting a dyadic approximation at a specified
precision. -/
abbrev ratDigits : RatProgram → ℕ → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.digits

/-- The number of nodes in a rational arithmetic program. -/
abbrev ratNodes : RatProgram → ℕ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.nodes

/-- The resource-cost record assigned to a rational arithmetic program. -/
abbrev ratCost : RatProgram → RatCost :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.cost

/-- The rational value obtained by evaluating a rational arithmetic program. -/
abbrev ratEval : RatProgram → ℚ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval

/-- Alias for the rational time-and-accuracy scan certificate. -/
abbrev scanCert :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.scanCert

/-- Alias for the corrected rational qDRIFT error budget. -/
abbrev correctedBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.correctedBudget

/-- Alias for the fair-bit qDRIFT error-budget function. -/
noncomputable abbrev fairBitBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.fairBitBudget

/-- Alias for the minimum fair-bit qDRIFT error-budget function. -/
noncomputable abbrev fairBitBudgetMin :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.fairBitBudgetMin

/-- Alias for the tight fair-bit qDRIFT sample-count function. -/
noncomputable abbrev tightFairBitCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tightFairBitCount

/-- Alias for the per-step Hamiltonian synthesis gate budget. -/
abbrev synthGateBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.synthGateBudget

/-- Alias for the Hamiltonian synthesis space budget. -/
abbrev synthSpaceBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.synthSpaceBudget

/-- Alias for the Table I qDRIFT simulation count. -/
noncomputable abbrev tableIQdriftCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tableIQdriftCount

/-- Alias for the Table I qDRIFT phase-estimation count. -/
noncomputable abbrev tableIQdriftPeCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tableIQdriftPeCount

/-- Alias for the Table I qDRIFT error budget. -/
abbrev tableIBudget :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tableIBudget

/-- Alias for the phase-estimation chain's bit-count parameter. -/
noncomputable abbrev peChainBits :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainBits

/-- Alias for the phase-estimation chain's evolution-time schedule. -/
noncomputable abbrev peChainTimes :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainTimes

/-- Alias for the phase-estimation chain's per-query error allocation. -/
noncomputable abbrev peChainErrorShare :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainErrorShare

/-- Alias for the phase-estimation chain's per-query qDRIFT step count. -/
noncomputable abbrev peChainQuerySteps :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainQuerySteps

/-- Alias for the phase-estimation chain's total qDRIFT count. -/
noncomputable abbrev peChainTotalCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainTotalCount

/-- The natural sampling weights obtained from precision-`b` quantized rational coefficients. -/
abbrev simWeights {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) : ℕ :=
  Qatlib.Concepts.RandCompile.EffectiveInput.simWeights b a j

/-- The coefficient-digit read budget for `L` terms at precision `b`. -/
abbrev simDigitReads (L b : ℕ) : ℕ :=
  Qatlib.Concepts.RandCompile.EffectiveInput.simDigitReads L b

/-- Extracts the off-diagonal control block of a matrix with a two-dimensional control register. -/
noncomputable abbrev ctrlCrossBlock {D : ℕ} :
    Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlCrossBlock

/-- Lifts an operator map to the controlled matrix space using the blockwise construction. -/
noncomputable abbrev ctrlBlockMapIdx {D : ℕ} :
    (Operator D →ₗ[ℂ] Operator D) → Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ →
      Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlBlockMapIdx

/-- The fixed control-data matrix witnessing the nonzero cross block used in the
coherent-control obstruction. -/
noncomputable abbrev coherentWitness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.coherentWitness

/-- The postselected qDRIFT operator map for positive total weight and the prescribed number of
steps. -/
noncomputable abbrev postSelectedQdriftMap {L D : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) (n : ℕ) (K : Fin L → Operator D) (t : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectedQdriftMap w hW n K t

/-- Alias for the source qDRIFT tight sample-count function. -/
abbrev sourceTightCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.sourceTightCount

/-- Alias for the decidable certificate relating rejection fuel and a proposed tight sample
count. -/
abbrev tightCountCertified :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.tightCountCertified

/-- The signed integer obtained by rounding a rational coefficient at dyadic precision `b`. -/
def simDigit {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) : ℤ :=
  dyadicCoefficient b (a j)

/-- The rational value `d / 2^b` represented by a signed dyadic digit. -/
def simDigitValue (b : ℕ) (d : ℤ) : ℚ := (d : ℚ) / (2 : ℚ) ^ b

/-- The digit width `Nat.clog 2 (weightTotal (simWeights b a) + 1) + 1` assigned to the
coefficient table. -/
def simDigitWidth {L : ℕ} (b : ℕ) (a : Fin L → ℚ) : ℕ :=
  Nat.clog 2 (weightTotal (simWeights b a) + 1) + 1

/-- The total coefficient-table space, equal to `L` times the assigned digit width. -/
def simDigitTableSpace {L : ℕ} (b : ℕ) (a : Fin L → ℚ) : ℕ :=
  L * simDigitWidth b a

/-- A rational bit-size measure given by the binary ceiling logarithm of the absolute numerator
plus the denominator. -/
def simRatBits (r : ℚ) : ℕ := Nat.clog 2 (r.num.natAbs + r.den)

/-- A rational program for dyadic coefficient rounding, using a half-unit offset before digit
extraction. -/
def simDigitProgram (b : ℕ) (a : ℚ) : RatProgram :=
  ratDigits (ratAdd (ratLit a) (ratLit ((1 / 2 : ℚ) / (2 : ℚ) ^ b))) b

/-- A rational program computing the ceiling of `2 * W^2 * T^2 / eQ`. -/
def simCountProgram (W T : ℕ) (eQ : ℚ) : RatProgram :=
  ratCeil
    (ratDiv
      (ratMul (ratLit 2)
        (ratMul (ratLit (W : ℚ))
          (ratMul (ratLit (W : ℚ))
            (ratMul (ratLit (T : ℚ)) (ratLit (T : ℚ))))))
      (ratLit eQ))

/-- A rational program computing `s + Nat.clog 2 n + 2`. -/
def simFuelProgram (n s : ℕ) : RatProgram :=
  ratAdd (ratLit s) (ratAdd (ratLog2 (ratLit n)) (ratLit 2))

/-- A bit-length bound combining digit-table space, twice the maximum parameter-read bit size
through precision `k`, and a constant margin of sixty-four. -/
noncomputable def simRunBitLength (k : ℕ) (tq eq : ℕ → ℚ)
    (digitSpace : ℕ) : ℕ :=
  digitSpace
    + 2 * (Finset.sup' (Finset.range (k + 1)) (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩)
        (fun k' => max (simRatBits (tq k')) (simRatBits (eq k'))))
    + 64

/-- A simulation-run resource record containing scan, parameter-read, digit-read, operation,
bit-time, and bit-space counts. -/
structure SimRunLedger where

  scanned : ℕ

  paramReads : ℕ

  digitReads : ℕ

  ops : ℕ

  bitTime : ℕ

  bitSpace : ℕ
  deriving Repr, DecidableEq

/-- Constructs the run ledger from the rational-program cost, `k + 1` scan levels, digit-table
space, and bit-length bound `B`. -/
noncomputable def simRunLedger (L : ℕ) (k : ℕ) (prog : RatProgram)
    (digitSpace : ℕ) (B : ℕ) : SimRunLedger :=
  let ops := (ratCost prog).total
  { scanned := k + 1
    paramReads := 2 * (k + 1)
    digitReads := L * (k + 1)
    ops := ops
    bitTime := (ops + L * (k + 1)) * (B + 2) * (B + 2)
    bitSpace := B + digitSpace + 16 }

/-- The total synthesis gate budget for `n` steps on an `m`-bit register. -/
def simGateBudget (m n : ℕ) : ℕ := n * synthGateBudget m

/-- The Hamiltonian synthesis space budget for an `m`-bit register. -/
def simQuantumSpace (m : ℕ) : ℕ := synthSpaceBudget m

/-- The sum of binary ceiling logarithms needed for positive-clamped step and label counts. -/
def simClassicalSpace (n L : ℕ) : ℕ :=
  Nat.clog 2 (max 1 n) + Nat.clog 2 (max 1 L)

/-- The natural ceiling of `2 * W^2 * T^2 / eQ`. -/
def simTightCount (W T : ℕ) (eQ : ℚ) : ℕ :=
  Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)

/-- The real factor `4 * eQ * 2^s` used to compare actual and source sample counts. -/
noncomputable def simOversizeFactor (eQ : ℚ) (s : ℕ) : ℝ := 4 * (eQ : ℝ) * ((2 : ℝ) ^ s)

/-- The positive-clamped simulation count `max 1 (8 * W^2 * T^2 * 2^s)`. -/
def simActualCount (W T : ℕ) (s : ℕ) : ℕ := max 1 (8 * W ^ 2 * T ^ 2 * 2 ^ s)

/-- The postselected simulation count, defined to be `simTightCount W T eQ`. -/
def simPostSelectCount (W T : ℕ) (eQ : ℚ) : ℕ := simTightCount W T eQ

/-- The binary ceiling logarithm of the natural ceiling of `n / eQ`. -/
noncomputable def simPostSelectFuel (n : ℕ) (eQ : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil ((n : ℚ) / eQ))

/-- The total synthesis gate budget at the Table I qDRIFT simulation count. -/
noncomputable def simTableIGateCount (m : ℕ) (lam t eps : ℝ) : ℕ :=
  simGateBudget m (tableIQdriftCount lam t eps)

/-- The total synthesis gate budget at the Table I qDRIFT phase-estimation count. -/
noncomputable def simPeGateCount (m : ℕ) (lam deltaE pf : ℝ) : ℕ :=
  simGateBudget m (tableIQdriftPeCount lam deltaE pf)

end Qatlib.Concepts.RandCompile.ChannelBudget.SimQdriftDefs
