/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.SignPolynomial
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial

def Lemma29RectangleApproximation : Prop :=
  ∀ (δ' ε' t : ℝ), 0 < δ' → δ' ≤ 1/2 → 0 < ε' → ε' ≤ 1/2 →
    δ' ≤ t → t ≤ 1 - δ' →
    ∃ (P : Polynomial ℝ) (k : ℕ),
      P.natDegree ≤ 3 ^ k ∧
      ((2 : ℝ) ^ k) ≤ 8 * Real.log (2/ε') / (δ'*δ') + 2 ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (3 ^ k + 1) P ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, -t + δ' ≤ x → x ≤ t - δ' →
        1 - ε' ≤ P.eval x ∧ P.eval x ≤ 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, (x ≤ -t - δ' ∨ t + δ' ≤ x) →
        0 ≤ P.eval x ∧ P.eval x ≤ ε')

end Qatlib.Concepts.QsvtCore.PolyApprox
