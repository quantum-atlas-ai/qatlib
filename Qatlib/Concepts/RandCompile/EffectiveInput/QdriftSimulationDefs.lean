/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs
import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.RandCompile.EffectiveInput

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.EffectiveInput

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

abbrev RelParamRead :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelParamRead

abbrev RelLowerParamRead :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelLowerParamRead

abbrev RelBracket := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelBracket

abbrev RelBracketStream :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelBracketStream

abbrev bracketRead := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.bracketRead

noncomputable abbrev bracketError :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.bracketError

abbrev epsBudgetBracket :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsBudgetBracket

abbrev epsCertifiedBracket :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsCertifiedBracket

noncomputable abbrev bracketTimeBound :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.bracketTimeBound

abbrev majorityFailure :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.majorityFailure

noncomputable abbrev peRounds :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peRounds

abbrev epsBudget := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsBudget

abbrev epsCertified :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsCertified

abbrev scanPrecision :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.scanPrecision

abbrev timeBound := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.timeBound

abbrev successLevel :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.successLevel

abbrev successCertified :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.successCertified

abbrev successFuel := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.successFuel

abbrev QdriftRunCost :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.QdriftRunCost

abbrev QdriftInputRun :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.QdriftInputRun

abbrev qdriftInputRun :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.qdriftInputRun

abbrev inputRunCost :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.inputRunCost

abbrev runBitLength :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.runBitLength

abbrev qdRatBits := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.qdRatBits

abbrev tightCountCertified :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.tightCountCertified

abbrev sourceTightCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.sourceTightCount

abbrev synthGateBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.synthGateBudget

abbrev synthSpaceBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.synthSpaceBudget

noncomputable def ctrlCrossBlock :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlCrossBlock

noncomputable def ctrlBlockMapIdx :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlBlockMapIdx

noncomputable def coherentWitness :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.coherentWitness

noncomputable def tableQdriftCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.tableQdriftCount

noncomputable def peBits :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peBits

noncomputable def peErrorShare :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peErrorShare

noncomputable def peQuerySteps :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peQuerySteps

noncomputable def peTimes :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peTimes

abbrev fairQdriftPickReport {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (ω : Fin R → Reg (Nat.clog 2 (weightTotal w))) : Bool :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.fairQdriftPickReport w j0 R ω

noncomputable abbrev fairBitCleanProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.fairBitCleanProb w R

noncomputable abbrev fairBitExhaustProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.fairBitExhaustProb w R

noncomputable abbrev postSelectSuccessMass {L : ℕ} (w : Fin L → ℕ) (R n : ℕ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectSuccessMass w R n

noncomputable abbrev postSelectedQdriftMap {L D : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) (n : ℕ) (K : Fin L → Operator D) (t : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectedQdriftMap w hW n K t

noncomputable abbrev postSelectDiamondBudget {L : ℕ} (w : Fin L → ℕ) (n : ℕ) (t : ℝ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectDiamondBudget w n t

noncomputable abbrev selectiveOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.selectiveOutput Φ P X

noncomputable abbrev selectiveMass {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.selectiveMass Φ P X

noncomputable abbrev conditionalOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.conditionalOutput Φ P X

def simDigitReads (L b : ℕ) : ℕ := L * (b + 1)

def simWeights {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) : ℕ := dyadicWeights b a j

def simInputCost (fuel b L : ℕ) (tq eq : ℕ → ℚ) : QdriftRunCost :=
  let run := qdriftInputRun fuel L tq eq
  { run.cost with digitReads := run.cost.digitReads + simDigitReads L b }

end Qatlib.Concepts.RandCompile.EffectiveInput
