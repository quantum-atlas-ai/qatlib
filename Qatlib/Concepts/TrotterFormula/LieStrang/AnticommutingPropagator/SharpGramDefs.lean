/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator.Defs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Data.Real.Sqrt
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
open Matrix
open scoped Matrix.Norms.L2Operator

def sharpGramComponent {I : Type*} [Fintype I]
    (P Q : Matrix I I ℂ) (c h : ℝ) : Matrix I I ℂ :=
  (c : ℂ) • Q - (Complex.I * (h : ℂ)) • (P * Q)

def sharpGramRadius (d : ℝ) : ℝ :=
  Real.sqrt (1 + d ^ 2) + |d|

def SharpGramSpecification : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (P Q : Matrix I I ℂ) (c h d : ℝ),
    P.IsHermitian → Q.IsHermitian →
    P * P = 1 → Q * Q = 1 → P * Q = -(Q * P) →
    c ^ 2 + h ^ 2 - d ^ 2 = 1 →
    let F := rescaledStep P Q d h c 1
    let T := sharpGramComponent P Q c h
    let R := sharpGramRadius d
    Fᴴ * F = (((1 + 2 * d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) +
      (((2 * d : ℝ) : ℂ)) • T ∧
    T.IsHermitian ∧
    T * T = (((1 + d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) ∧
    T * P = -(P * T) ∧
    ‖F‖ ≤ R ∧
    (∀ v : Qatlib.Foundations.PureStateMath.QState I,
      ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ ≤ R * ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (F *ᵥ v)‖)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (P Q : Matrix I I ℂ) (a ω ν t : ℝ),
    P.IsHermitian → Q.IsHermitian →
    P * P = 1 → Q * Q = 1 → P * Q = -(Q * P) →
    0 < a → a < ω → 0 < ν → ν ^ 2 = ω ^ 2 - a ^ 2 →
    let F := rescaledStep P Q a ω (Real.cos (ν * t)) (Real.sin (ν * t) / ν)
    let R := sharpGramRadius (a * (Real.sin (ν * t) / ν))
    let κ := (ω + a) / ν
    R ≤ κ ∧ ‖F‖ ≤ κ ∧
    (∀ v : Qatlib.Foundations.PureStateMath.QState I,
      ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (F *ᵥ v)‖ ≤ κ * ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ ∧
      ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ ≤ κ * ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (F *ᵥ v)‖))

end Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
