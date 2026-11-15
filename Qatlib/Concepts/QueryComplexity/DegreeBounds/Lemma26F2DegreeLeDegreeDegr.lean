/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Lemma26F2DegreeLeDegreeStat
public import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.BooleanPolynomial

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeBounds

/-- The degree of a Boolean function over the field with two elements is at most its exact real
polynomial degree. -/
theorem lemma26F2DegreeLeDegree : Lemma26F2DegreeLeDegree := by
  classical
  intro I _ _ f
  obtain ⟨p,hp,hd⟩ := boolean_mod_two_representation f
  exact (csInf_le' (show p.totalDegree ∈
    (fun q : MvPolynomial I (ZMod 2) => q.totalDegree) ''
      {q | ∀ x, MvPolynomial.eval (fun i => if x i then 1 else 0) q=
        if f x then 1 else 0} from ⟨p,hp,rfl⟩)).trans hd

end Qatlib.Concepts.QueryComplexity.DegreeBounds
