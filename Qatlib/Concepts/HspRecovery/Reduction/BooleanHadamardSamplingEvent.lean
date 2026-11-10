/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardSampling
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

theorem marginalProbLeft_hiddenSubgroupSampling_booleanReg
    {n : ℕ} {R : Type*}
    [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (S : Finset (Qatlib.Foundations.PureStateMath.Reg n)) :
    MarginalProbLeft
        (Run (AddOracle f)
          (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv)
          (TensorState (Uniform (BooleanVec n)) (Ket 0)))
        (S.map (regBooleanEquiv n).toEmbedding) =
      ∑ y ∈ S,
        if regBooleanEquiv n y ∈ booleanOrthogonal H then
          1 / (Fintype.card (characterAnnihilator H) : ℝ)
        else 0 := by
  unfold MarginalProbLeft MeasureProb
  simp only [Finset.sum_product, Finset.sum_map, Equiv.toEmbedding_apply]
  apply Finset.sum_congr rfl
  intro y _hy
  have hsingle := marginalProbLeft_hiddenSubgroupSampling_booleanReg_singleton
    f H hf y
  unfold MarginalProbLeft MeasureProb at hsingle
  simp only [Finset.sum_product, Finset.sum_singleton] at hsingle
  exact hsingle

end Qatlib.Concepts.HspRecovery.ReductionCore
