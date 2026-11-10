/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardFourierBridge
import Qatlib.Concepts.HspRecovery.Distinguisher.HiddenSubgroupSampling
set_option warningAsError false

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical

theorem hadamardN_eq_booleanFourierGate_submatrix (n : ℕ) :
    Qatlib.Foundations.PureStateMath.HadamardN n =
      (fourierGate (booleanCharacterEquiv n).toEquiv).submatrix
        (regBooleanEquiv n) (regBooleanEquiv n) := by
  ext y z
  simpa [fourierGate, booleanCharacterEquiv_apply] using
    congrArg (fun M => M y z) (hadamardN_eq_booleanFourier_submatrix n)

theorem hiddenSubgroupSamplingCircuit_boolean_resources
    (n : ℕ) {R : Type*}
    [AddCommGroup R] [Fintype R] [DecidableEq R] :
    QueryCount
        (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv) = 1 ∧
      GateCount
          (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv) = 1 ∧
        Size
          (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv) = 2 := by
  exact hiddenSubgroupSamplingCircuit_resources
    (R := R) (booleanCharacterEquiv n).toEquiv

theorem marginalProbLeft_hiddenSubgroupSampling_booleanReg_singleton
    {n : ℕ} {R : Type*}
    [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (y : Qatlib.Foundations.PureStateMath.Reg n) :
    MarginalProbLeft
        (Run (AddOracle f)
          (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv)
          (TensorState (Uniform (BooleanVec n)) (Ket 0)))
        {regBooleanEquiv n y} =
      if regBooleanEquiv n y ∈ booleanOrthogonal H then
        1 / (Fintype.card (characterAnnihilator H) : ℝ)
      else 0 := by
  have h := marginalProbLeft_hiddenSubgroupSampling_singleton
    f H hf (booleanCharacterEquiv n).toEquiv
      (booleanCharacterEquiv n (regBooleanEquiv n y))
  have hlabel : (booleanCharacterEquiv n).toEquiv.symm
      (booleanCharacterEquiv n (regBooleanEquiv n y)) = regBooleanEquiv n y :=
    (booleanCharacterEquiv n).symm_apply_apply _
  rw [hlabel, booleanCharacterEquiv_mem_characterAnnihilator_iff] at h
  exact h

end Qatlib.Concepts.HspRecovery.ReductionCore
