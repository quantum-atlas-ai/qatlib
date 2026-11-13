/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Grover circuits from a source preparation gate

`SourceGateCircuit` repeats a phase query followed by the signed conjugate of a source
reflection; `SourceGatePlainCircuit` uses the unsigned conjugate. `Section6SourceGateSubgoal`
specifies unitary validity, exact query count, equivalence with `GroverState`, the global phase
of the unsigned circuit, and its success formula.

For the mathematical background, see [Grover1997].

## Main statements

* `Section6SourceGateSubgoal`: The contract stating that unitary preparation of the uniform
  state gives a valid j-query Grover circuit, with the unsigned variant differing by (−1)^j and
  success given by the stated sine-square formula.

## References

* [Grover, 1997][Grover1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.GateCore

open Qatlib.Concepts.SearchStopping.KnownCount Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The source reflection I − 2|v⟩⟨v|. -/
noncomputable def SourceZeroReflect (v : QState I) : Matrix I I ℂ :=
  1 - (2 : ℂ) • outerProduct v

/-- A phase query followed by the negative conjugate of `SourceZeroReflect v` by `T'`. -/
noncomputable def SourceGateBlock (T' : Matrix I I ℂ) (v : QState I) : Circuit I :=
  [Step.query, Step.gate (-(T' * SourceZeroReflect v * star T'))]

/-- The circuit repeating `SourceGateBlock` exactly j times. -/
noncomputable def SourceGateCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit I :=
  RepeatCircuit (SourceGateBlock T' v) j

/-- A phase query followed by the conjugate of `SourceZeroReflect v` by `T'`, without the
leading minus sign. -/
noncomputable def SourceGatePlainBlock (T' : Matrix I I ℂ) (v : QState I) : Circuit I :=
  [Step.query, Step.gate (T' * SourceZeroReflect v * star T')]

/-- The circuit repeating `SourceGatePlainBlock` exactly j times. -/
noncomputable def SourceGatePlainCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit I :=
  RepeatCircuit (SourceGatePlainBlock T' v) j

/-- The contract stating that unitary preparation of the uniform state gives a valid j-query
Grover circuit, with the unsigned variant differing by (−1)^j and success given by the
stated sine-square formula. -/
def Section6SourceGateSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (T' : Matrix I I ℂ) (v : QState I),
      T' ∈ Matrix.unitaryGroup I ℂ → Normalized v → T' *ᵥ v = Uniform I →
      ∀ (A : Finset I) (j : ℕ),
        IsUnitaryCircuit (SourceGateCircuit T' v j) ∧
        QueryCount (SourceGateCircuit T' v j) = j ∧
        Run (SetOracle A) (SourceGateCircuit T' v j) (Uniform I) = GroverState A j ∧
        Run (SetOracle A) (SourceGatePlainCircuit T' v j) (Uniform I) =
          (-1 : ℂ) ^ j • GroverState A j ∧
        ∀ θ : ℝ, (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ) →
          Real.sin θ ≠ 0 → Real.cos θ ≠ 0 →
          MeasureProb (Run (SetOracle A) (SourceGateCircuit T' v j) (Uniform I)) A
            = (Real.sin ((2 * j + 1) * θ)) ^ 2

end Qatlib.Concepts.SearchStopping.GateCore
