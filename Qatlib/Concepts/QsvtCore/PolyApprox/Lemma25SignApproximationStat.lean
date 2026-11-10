/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.SignPolynomial
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
set_option warningAsError false

open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial

def Lemma25SignApproximation : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → δ ≤ 2 → 0 < ε → ε ≤ 1/2 →
    ∃ (P : Polynomial ℝ) (k : ℕ),
      P.natDegree ≤ 3 ^ k ∧
      ((2 : ℝ) ^ k) ≤ 8 * Real.log (1/ε) / (δ*δ) + 2 ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (3 ^ k) P ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, |P.eval x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, δ ≤ |x| →
        |P.eval x - Real.sign x| ≤ ε)

end Qatlib.Concepts.QsvtCore.PolyApprox
