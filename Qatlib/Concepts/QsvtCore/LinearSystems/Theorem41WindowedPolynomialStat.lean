/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalReciprocal
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Polynomial

def Theorem41WindowedPolynomial : Prop :=
  ∀ (ε δ : ℝ), 0 < ε → ε ≤ δ → δ ≤ 1/2 →
    ∃ (Pw : Polynomial ℝ) (J k : ℕ),
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      Pw.natDegree ≤ 2*J+1+2*3^k ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (2*J+1+2*3^k) Pw ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε)

end Qatlib.Concepts.QsvtCore.LinearSystems
