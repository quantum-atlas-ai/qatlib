/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchAuxiliary

/-!
# Finite quantum search specification

`Theorem3QSearchSpec.expected` describes the finite-horizon quantum search loop with unknown
marked mass from [BrassardEtAl2002]. It specifies correctness of successful labels, failure for
zero marked mass, and inverse-square-root expected bounds for both cost counters.

## Main statements

* `Theorem3QSearchSpec.expected`: the finite-horizon support and expected-cost contract.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchSpec
/-- Specifies marked-output correctness, certain failure for zero initial marked mass, and
expected cost at most `400 / sqrt a` for each counter when the initial marked mass `a` is
positive. -/
def expected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ),
    let a : ℝ :=
        Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState A j₀) S
    let p := BHMTQSearch.qSearchLoop A hA j₀ S T 0
    (∀ out ∈ PMF.support p, ∀ y, out.1 = some y → y ∈ S) ∧
    (a = 0 → ∀ out ∈ PMF.support p, out.1 = none) ∧
    (0 < a →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt a) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt a))
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchSpec
