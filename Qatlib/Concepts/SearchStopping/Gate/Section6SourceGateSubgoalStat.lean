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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.GateCore

open Qatlib.Concepts.SearchStopping.KnownCount Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def SourceZeroReflect (v : QState I) : Matrix I I ℂ :=
  1 - (2 : ℂ) • outerProduct v

noncomputable def SourceGateBlock (T' : Matrix I I ℂ) (v : QState I) : Circuit I :=
  [Step.query, Step.gate (-(T' * SourceZeroReflect v * star T'))]

noncomputable def SourceGateCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit I :=
  RepeatCircuit (SourceGateBlock T' v) j

noncomputable def SourceGatePlainBlock (T' : Matrix I I ℂ) (v : QState I) : Circuit I :=
  [Step.query, Step.gate (T' * SourceZeroReflect v * star T')]

noncomputable def SourceGatePlainCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit I :=
  RepeatCircuit (SourceGatePlainBlock T' v) j

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
