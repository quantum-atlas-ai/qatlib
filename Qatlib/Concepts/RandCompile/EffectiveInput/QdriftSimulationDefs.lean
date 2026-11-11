/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs
import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift

/-!
# Effective input interfaces for qDRIFT simulation

This module exposes parameter-read, rational-bracket, precision-search, postselection, and
resource-ledger interfaces for effective qDRIFT input processing. It also defines `simWeights`
and the additional coefficient-digit cost in `simInputCost`, supporting simulation bounds in the
setting of [Campbell2019].

## Main statements

* `RelBracketStream`: provides the rational-bracket parameter interface.
* `simWeights`: uses dyadically rounded coefficient magnitudes as natural weights.
* `simInputCost`: adds coefficient reads to the parameter-processing ledger.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.RandCompile.EffectiveInput

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.EffectiveInput

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- Alias for the rational parameter-read relation used by finite-diamond qDRIFT. -/
abbrev RelParamRead :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelParamRead

/-- Alias for the rational lower parameter-read relation used by finite-diamond qDRIFT. -/
abbrev RelLowerParamRead :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelLowerParamRead

/-- Alias for the rational-bracket relation for a real parameter. -/
abbrev RelBracket := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelBracket

/-- Alias for a stream of rational brackets approximating a real parameter. -/
abbrev RelBracketStream :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.RelBracketStream

/-- Alias for extracting a rational parameter read from a bracket. -/
abbrev bracketRead := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.bracketRead

/-- Alias for the real error bound associated with a rational bracket. -/
noncomputable abbrev bracketError :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.bracketError

/-- Alias for the error budget computed from rational bracket data. -/
abbrev epsBudgetBracket :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsBudgetBracket

/-- Alias for the Boolean error-budget certificate computed from rational bracket data. -/
abbrev epsCertifiedBracket :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsCertifiedBracket

/-- Alias for the natural time bound extracted from a rational bracket. -/
noncomputable abbrev bracketTimeBound :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.bracketTimeBound

/-- Alias for the majority-vote failure expression. -/
abbrev majorityFailure :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.majorityFailure

/-- Alias for the phase-estimation repetition count. -/
noncomputable abbrev peRounds :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peRounds

/-- Alias for the error budget extracted from a rational accuracy read at a precision level. -/
abbrev epsBudget := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsBudget

/-- Alias for the Boolean positivity certificate for the accuracy budget at a precision level. -/
abbrev epsCertified :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.epsCertified

/-- Alias for the bounded search selecting a certified precision level. -/
abbrev scanPrecision :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.scanPrecision

/-- Alias for the natural time bound extracted from a rational time read. -/
abbrev timeBound := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.timeBound

/-- Alias for the accuracy level selected from an error budget. -/
abbrev successLevel :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.successLevel

/-- Alias for the Boolean certificate for a proposed success level. -/
abbrev successCertified :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.successCertified

/-- Alias for the fuel assigned to the success-level search. -/
abbrev successFuel := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.successFuel

/-- Alias for the qDRIFT input-processing resource-cost record. -/
abbrev QdriftRunCost :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.QdriftRunCost

/-- Alias for the record of a qDRIFT input-processing run. -/
abbrev QdriftInputRun :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.QdriftInputRun

/-- Alias for the bounded qDRIFT parameter-processing run. -/
abbrev qdriftInputRun :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.qdriftInputRun

/-- Alias for the cost of a qDRIFT parameter-processing run. -/
abbrev inputRunCost :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.inputRunCost

/-- Alias for the bit-length bound assigned to the parameter reads of an input run. -/
abbrev runBitLength :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.runBitLength

/-- Alias for the rational bit-size measure used in qDRIFT input accounting. -/
abbrev qdRatBits := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.qdRatBits

/-- Alias for the Boolean certificate for rejection fuel and a proposed tight simulation count. -/
abbrev tightCountCertified :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.tightCountCertified

/-- Alias for the source qDRIFT tight sample-count function. -/
abbrev sourceTightCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.sourceTightCount

/-- Alias for the per-step Hamiltonian synthesis gate budget. -/
abbrev synthGateBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.synthGateBudget

/-- Alias for the Hamiltonian synthesis space budget. -/
abbrev synthSpaceBudget :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.synthSpaceBudget

/-- The control cross-block extraction function used in the coherent-control witness. -/
noncomputable def ctrlCrossBlock :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlCrossBlock

/-- The blockwise lift of an operator map to matrices with a two-dimensional control register. -/
noncomputable def ctrlBlockMapIdx :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.ctrlBlockMapIdx

/-- The fixed control-data witness with a nonzero control cross block. -/
noncomputable def coherentWitness :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.coherentWitness

/-- The qDRIFT step-count function associated with the simulation table bound. -/
noncomputable def tableQdriftCount :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.tableQdriftCount

/-- The bit-count parameter used by the phase-estimation schedule. -/
noncomputable def peBits :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peBits

/-- The per-query error share in the phase-estimation schedule. -/
noncomputable def peErrorShare :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peErrorShare

/-- The qDRIFT step count assigned to a query in the phase-estimation schedule. -/
noncomputable def peQuerySteps :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peQuerySteps

/-- The evolution-time schedule used in phase estimation. -/
noncomputable def peTimes :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.peTimes

/-- The Boolean report returned by the capped fair-bit weighted sampler. -/
abbrev fairQdriftPickReport {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (ω : Fin R → Reg (Nat.clog 2 (weightTotal w))) : Bool :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.fairQdriftPickReport w j0 R ω

/-- The clean-sampling probability assigned to the fair-bit sampler at rejection fuel `R`. -/
noncomputable abbrev fairBitCleanProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.fairBitCleanProb w R

/-- The fuel-exhaustion probability assigned to the fair-bit sampler at rejection fuel `R`. -/
noncomputable abbrev fairBitExhaustProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.fairBitExhaustProb w R

/-- The postselection success mass for `n` capped sampling steps with rejection fuel `R`. -/
noncomputable abbrev postSelectSuccessMass {L : ℕ} (w : Fin L → ℕ) (R n : ℕ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectSuccessMass w R n

/-- The postselected qDRIFT operator map for positive total weight. -/
noncomputable abbrev postSelectedQdriftMap {L D : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) (n : ℕ) (K : Fin L → Operator D) (t : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectedQdriftMap w hW n K t

/-- The finite diamond error budget assigned to the postselected qDRIFT map. -/
noncomputable abbrev postSelectDiamondBudget {L : ℕ} (w : Fin L → ℕ) (n : ℕ) (t : ℝ) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.postSelectDiamondBudget w n t

/-- The selected operator output obtained from the map, selection operator, and input operator. -/
noncomputable abbrev selectiveOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.selectiveOutput Φ P X

/-- The real selected-output mass associated with the map, selection operator, and input
operator. -/
noncomputable abbrev selectiveMass {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : ℝ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.selectiveMass Φ P X

/-- The conditional output associated with the map, selection operator, and input operator. -/
noncomputable abbrev conditionalOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.conditionalOutput Φ P X

/-- The coefficient-digit read budget `L * (b + 1)`. -/
def simDigitReads (L b : ℕ) : ℕ := L * (b + 1)

/-- The natural weights given by the magnitudes of the precision-`b` rounded dyadic
coefficients. -/
def simWeights {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) : ℕ := dyadicWeights b a j

/-- The qDRIFT parameter-run cost with `simDigitReads L b` added to its digit-read field. -/
def simInputCost (fuel b L : ℕ) (tq eq : ℕ → ℚ) : QdriftRunCost :=
  let run := qdriftInputRun fuel L tq eq
  { run.cost with digitReads := run.cost.digitReads + simDigitReads L b }

end Qatlib.Concepts.RandCompile.EffectiveInput
