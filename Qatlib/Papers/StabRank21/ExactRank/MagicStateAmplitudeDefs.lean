/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false

open Qatlib.Concepts.PauliClifford.ExactRank
namespace Qatlib.Papers.StabRank21.ExactRank

noncomputable def magicH (n : ℕ) : BooleanVec n → ℂ :=
  fun x => (Complex.ofReal (Real.cos (Real.pi / 8))) ^ (n - cubeWeight x) *
    (Complex.ofReal (Real.sin (Real.pi / 8))) ^ (cubeWeight x)

noncomputable def magicRbeta : ℝ := Real.arccos ((1 : ℝ) / Real.sqrt 3) / 2

noncomputable def expPiQuarterI : ℂ := Complex.exp (Complex.ofReal Real.pi / 4 * Complex.I)

noncomputable def magicR (n : ℕ) : BooleanVec n → ℂ :=
  fun x => (Complex.ofReal (Real.cos magicRbeta)) ^ (n - cubeWeight x) *
    (expPiQuarterI * Complex.ofReal (Real.sin magicRbeta)) ^ (cubeWeight x)
end Qatlib.Papers.StabRank21.ExactRank
