/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.Macros
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SdpMmwSolver.BranchProofs

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def SdpLargerBranchPrimalWitness : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (σ₀ : Operator D) (j₀ : Fin m) (α R δ ε : ℝ),
    0 < α → 0 < R → 0 < δ → δ ≤ 1 → 0 < ε → ε ≤ δ/(16*R) →
    (∀ i, 1 ≤ b i) →
    A j₀ = 1 → b j₀ = R →
    IsDensityOperator σ₀ →
    (∀ y : Fin m → ℝ, (∀ i, 0 ≤ y i) →
      (∑ i, y i * (Matrix.trace (A i * σ₀)).re) ≥
        (Matrix.trace (Cv * σ₀)).re - 3*α*ε →
      α*(1 - 3*R*ε) ≤ ∑ i, y i * b i) →
    ∃ X : Operator D, X.PosSemidef ∧
      (∀ i, (Matrix.trace (A i * X)).re ≤ b i) ∧
      (Matrix.trace X).re ≤ R ∧
      (1 - δ)*α ≤ (Matrix.trace (Cv * X)).re

end Qatlib.Concepts.SdpMmwSolver.BranchProofs
