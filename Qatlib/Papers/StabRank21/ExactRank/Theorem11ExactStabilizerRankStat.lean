/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank
public import Qatlib.Papers.StabRank21.ExactRank.MagicStateAmplitudeDefs

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false


namespace Qatlib.Papers.StabRank21.ExactRank

open Qatlib.Papers.StabRank21.ExactRank Qatlib.Concepts.PauliClifford.ExactRank
def Theorem11ExactStabilizerRank : Prop :=
  ∀ n : ℕ, n / 100 < stabilizerRank (magicH n) ∧ n / 100 < stabilizerRank (magicR n)

end Qatlib.Papers.StabRank21.ExactRank
