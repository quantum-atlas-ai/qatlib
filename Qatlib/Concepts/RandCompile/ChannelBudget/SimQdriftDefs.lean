/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.QdriftSimulation
import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.RandCompile.EffectiveInput

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.RandCompile.ChannelBudget.SimQdriftDefs

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

abbrev DyadicRead :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.DyadicRead

abbrev DyadicLowerRead :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.DyadicLowerRead

abbrev RatProgram :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram

abbrev RatCost := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatCost

abbrev ratLit : ℚ → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.lit

abbrev ratAdd : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.add

abbrev ratMul : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.mul

abbrev ratDiv : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.div

abbrev ratCeil : RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.ceil

abbrev ratLog2 : RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.log2

abbrev ratDigits : RatProgram → ℕ → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.digits

abbrev ratNodes : RatProgram → ℕ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.nodes

abbrev ratCost : RatProgram → RatCost :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.cost

abbrev ratEval : RatProgram → ℚ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval

abbrev scanCert :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.scanCert

abbrev correctedBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.correctedBudget

noncomputable abbrev fairBitBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.fairBitBudget

noncomputable abbrev fairBitBudgetMin :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.fairBitBudgetMin

noncomputable abbrev tightFairBitCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tightFairBitCount

abbrev synthGateBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.synthGateBudget

abbrev synthSpaceBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.synthSpaceBudget

noncomputable abbrev tableIQdriftCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tableIQdriftCount

noncomputable abbrev tableIQdriftPeCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tableIQdriftPeCount

abbrev tableIBudget :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.tableIBudget

noncomputable abbrev peChainBits :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainBits

noncomputable abbrev peChainTimes :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainTimes

noncomputable abbrev peChainErrorShare :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainErrorShare

noncomputable abbrev peChainQuerySteps :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainQuerySteps

noncomputable abbrev peChainTotalCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.peChainTotalCount

abbrev simWeights {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) : ℕ :=
  Qatlib.Concepts.RandCompile.EffectiveInput.simWeights b a j

abbrev simDigitReads (L b : ℕ) : ℕ :=
  Qatlib.Concepts.RandCompile.EffectiveInput.simDigitReads L b

noncomputable abbrev ctrlCrossBlock {D : ℕ} :
    Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlCrossBlock

noncomputable abbrev ctrlBlockMapIdx {D : ℕ} :
    (Operator D →ₗ[ℂ] Operator D) → Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ →
      Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlBlockMapIdx

noncomputable abbrev coherentWitness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.coherentWitness

noncomputable abbrev postSelectedQdriftMap {L D : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) (n : ℕ) (K : Fin L → Operator D) (t : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectedQdriftMap w hW n K t

abbrev sourceTightCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.sourceTightCount

abbrev tightCountCertified :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.tightCountCertified

def simDigit {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) : ℤ :=
  dyadicCoefficient b (a j)

def simDigitValue (b : ℕ) (d : ℤ) : ℚ := (d : ℚ) / (2 : ℚ) ^ b

def simDigitWidth {L : ℕ} (b : ℕ) (a : Fin L → ℚ) : ℕ :=
  Nat.clog 2 (weightTotal (simWeights b a) + 1) + 1

def simDigitTableSpace {L : ℕ} (b : ℕ) (a : Fin L → ℚ) : ℕ :=
  L * simDigitWidth b a

def simRatBits (r : ℚ) : ℕ := Nat.clog 2 (r.num.natAbs + r.den)

def simDigitProgram (b : ℕ) (a : ℚ) : RatProgram :=
  ratDigits (ratAdd (ratLit a) (ratLit ((1 / 2 : ℚ) / (2 : ℚ) ^ b))) b

def simCountProgram (W T : ℕ) (eQ : ℚ) : RatProgram :=
  ratCeil
    (ratDiv
      (ratMul (ratLit 2)
        (ratMul (ratLit (W : ℚ))
          (ratMul (ratLit (W : ℚ))
            (ratMul (ratLit (T : ℚ)) (ratLit (T : ℚ))))))
      (ratLit eQ))

def simFuelProgram (n s : ℕ) : RatProgram :=
  ratAdd (ratLit s) (ratAdd (ratLog2 (ratLit n)) (ratLit 2))

noncomputable def simRunBitLength (k : ℕ) (tq eq : ℕ → ℚ)
    (digitSpace : ℕ) : ℕ :=
  digitSpace
    + 2 * (Finset.sup' (Finset.range (k + 1)) (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩)
        (fun k' => max (simRatBits (tq k')) (simRatBits (eq k'))))
    + 64

structure SimRunLedger where

  scanned : ℕ

  paramReads : ℕ

  digitReads : ℕ

  ops : ℕ

  bitTime : ℕ

  bitSpace : ℕ
  deriving Repr, DecidableEq

noncomputable def simRunLedger (L : ℕ) (k : ℕ) (prog : RatProgram)
    (digitSpace : ℕ) (B : ℕ) : SimRunLedger :=
  let ops := (ratCost prog).total
  { scanned := k + 1
    paramReads := 2 * (k + 1)
    digitReads := L * (k + 1)
    ops := ops
    bitTime := (ops + L * (k + 1)) * (B + 2) * (B + 2)
    bitSpace := B + digitSpace + 16 }

def simGateBudget (m n : ℕ) : ℕ := n * synthGateBudget m

def simQuantumSpace (m : ℕ) : ℕ := synthSpaceBudget m

def simClassicalSpace (n L : ℕ) : ℕ :=
  Nat.clog 2 (max 1 n) + Nat.clog 2 (max 1 L)

def simTightCount (W T : ℕ) (eQ : ℚ) : ℕ :=
  Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)

noncomputable def simOversizeFactor (eQ : ℚ) (s : ℕ) : ℝ := 4 * (eQ : ℝ) * ((2 : ℝ) ^ s)

def simActualCount (W T : ℕ) (s : ℕ) : ℕ := max 1 (8 * W ^ 2 * T ^ 2 * 2 ^ s)

def simPostSelectCount (W T : ℕ) (eQ : ℚ) : ℕ := simTightCount W T eQ

noncomputable def simPostSelectFuel (n : ℕ) (eQ : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil ((n : ℚ) / eQ))

noncomputable def simTableIGateCount (m : ℕ) (lam t eps : ℝ) : ℕ :=
  simGateBudget m (tableIQdriftCount lam t eps)

noncomputable def simPeGateCount (m : ℕ) (lam deltaE pf : ℝ) : ℕ :=
  simGateBudget m (tableIQdriftPeCount lam deltaE pf)

end Qatlib.Concepts.RandCompile.ChannelBudget.SimQdriftDefs
