/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem3DegreeLeQueryCountSqStat
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem1DegreeLeLambdaSqDegr
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Lemma9LambdaLeQueryCountRestrictedDegr

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.DegreeBounds
open scoped Matrix.Norms.L2Operator

/-- For a unitary circuit computing a Boolean function with success probability at least two
thirds, the exact degree is at most the squared query count multiplied by the square of `6 *
(3 + 2 * Real.sqrt 2)`. -/
theorem theorem3DegreeLeQueryCountSq : Theorem3DegreeLeQueryCountSq := by
  classical
  intro N W _ _ C ψ E f hC hψ hs
  have hd := theorem1DegreeLeLambdaSq (Fin N) f
  have hLambda := lemma9LambdaLeQueryCountRestricted N W C ψ E f hC hψ hs
  have hnon : 0 ≤ 6*(3+2*Real.sqrt 2)*(QueryCount C : ℝ) := by positivity
  exact hd.trans ((sq_le_sq₀ (norm_nonneg (sensAdjacency f)) hnon).mpr hLambda)

end Qatlib.Concepts.QueryComplexity.DegreeBounds
