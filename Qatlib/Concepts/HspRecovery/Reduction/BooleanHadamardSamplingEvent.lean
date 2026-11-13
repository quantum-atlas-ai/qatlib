/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardSampling

/-!
# Finite events in Boolean subgroup sampling

The theorem `marginalProbLeft_hiddenSubgroupSampling_booleanReg` gives the probability of an
arbitrary finite set of Boolean register outcomes. It sums the uniform annihilator masses of the
encoded outcomes that belong to `booleanOrthogonal H`. See [Simon1997] for the mathematical
background.

## Main statements

* `marginalProbLeft_hiddenSubgroupSampling_booleanReg`: sum the singleton outcome formula over a
  finite register event.

## References

* [Simon, 1997][Simon1997]
-/

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

/-- For a hiding oracle, the probability of an encoded finite register event is the sum of
reciprocal annihilator cardinalities over its outcomes orthogonal to `H`. -/
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
