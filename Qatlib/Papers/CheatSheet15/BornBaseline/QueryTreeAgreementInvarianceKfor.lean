/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.QueryTreeAgreementInvarianceStat

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.CheatSheet15.BornBaseline

/-- For oracles agreeing outside a set, a query tree visits that set with one oracle exactly
when it does with the other. If it never visits the set, the outputs agree. -/
theorem queryTreeAgreementInvariance : QueryTreeAgreementInvariance := by
  intro Q _ _ o₁ o₂ B τ hagree
  induction τ with
  | halt b => simp [queriesOf, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
  | ask q f t ihf iht =>
    by_cases hq : q ∈ B
    · have hhit (o : Q → Bool) : ∃ r : Q, r ∈ B ∧ r ∈ queriesOf o (.ask q f t) := by
        refine ⟨q, hq, ?_⟩
        simp only [queriesOf]
        split <;> simp
      exact ⟨iff_of_true (hhit o₁) (hhit o₂), fun h => False.elim (h (hhit o₁))⟩
    · have he := hagree q hq
      cases hv : o₁ q
      · have hv₂ : o₂ q = false := he.symm.trans hv
        simpa [queriesOf, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hv, hv₂,
            List.mem_cons, and_or_left, exists_or, hq] using ihf
      · have hv₂ : o₂ q = true := he.symm.trans hv
        simpa [queriesOf, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hv, hv₂,
            List.mem_cons, and_or_left, exists_or, hq] using iht

end Qatlib.Papers.CheatSheet15.BornBaseline
