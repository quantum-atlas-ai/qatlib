/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphWindow
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreAuxiliary
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit

noncomputable def polynomialLipschitzWeight (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), (k : ℝ) * |p.coeff k|

noncomputable def polynomialResponseModulus (p : Polynomial ℝ) (δ : ℝ) : ℝ :=
  polynomialLipschitzWeight p * δ

def SignApproximation (S : Polynomial ℝ) (δ σ : ℝ) : Prop :=
  (∀ x : ℝ, |x| ≤ 2 → |S.eval x| ≤ 1) ∧
  (∀ x : ℝ, |x| ≤ 2 → δ ≤ |x| → |S.eval x - Real.sign x| ≤ σ) ∧
  (∀ x : ℝ, S.eval (-x) = -S.eval x)

noncomputable def rectanglePolynomial (S : Polynomial ℝ) (ε₀ t : ℝ) : Polynomial ℝ :=
  Polynomial.C ((1 - ε₀) / 2) *
    (S.comp (Polynomial.X + Polynomial.C t) +
      S.comp (Polynomial.C t - Polynomial.X)) +
    Polynomial.C ε₀

def RectangleBand (P : Polynomial ℝ) (ε₀ δ t e : ℝ) : Prop :=
  (∀ x : ℝ, |x| ≤ 1 → |P.eval x| ≤ 1) ∧
  (∀ x : ℝ, |x| ≤ 1 → (x ≤ -(t + δ) ∨ t + δ ≤ x) →
    ε₀ - e ≤ P.eval x ∧ P.eval x ≤ ε₀ + e) ∧
  (∀ x : ℝ, |x| ≤ 1 → -(t - δ) ≤ x ∧ x ≤ t - δ →
    1 - e ≤ P.eval x ∧ P.eval x ≤ 1 + e)

end Qatlib.Concepts.QsvtCore.ApproxToolkit
