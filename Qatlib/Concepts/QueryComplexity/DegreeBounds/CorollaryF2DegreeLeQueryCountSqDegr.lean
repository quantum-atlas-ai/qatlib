/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.CorollaryF2DegreeLeQueryCountSqStat
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem3DegreeLeQueryCountSqDegr
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Lemma26F2DegreeLeDegreeDegr

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeBounds

/-- A unitary circuit computing a Boolean function with success probability at least two thirds
bounds its degree over the field with two elements by the stated constant times the squared
query count. -/
theorem corollaryF2DegreeLeQueryCountSq : CorollaryF2DegreeLeQueryCountSq := by
  classical
  intro N W _ _ C ψ E f hC hψ hs
  have hd : (gf2Degree f : ℝ) ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f :=
    Nat.cast_le.mpr (lemma26F2DegreeLeDegree (Fin N) f)
  exact hd.trans (theorem3DegreeLeQueryCountSq N W C ψ E f hC hψ hs)

end Qatlib.Concepts.QueryComplexity.DegreeBounds
