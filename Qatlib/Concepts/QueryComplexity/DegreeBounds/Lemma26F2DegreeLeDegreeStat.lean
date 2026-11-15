/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.Support

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeBounds

def Lemma26F2DegreeLeDegree : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool),
    gf2Degree f ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f

end Qatlib.Concepts.QueryComplexity.DegreeBounds
