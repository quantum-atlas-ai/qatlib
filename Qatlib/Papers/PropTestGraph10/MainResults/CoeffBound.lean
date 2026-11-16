/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.CubeCoeff
public import Qatlib.Papers.PropTestGraph10.MainResults.Model.AcceptancePolynomial
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # The full acceptance-polynomial coefficient bound of Lemma 15

Fixed source: arXiv1012.3174v3, page 16. The actual multilinear polynomial
and its actual Boolean evaluations are used, with the entire original
arbitrary-variable-universe and monomial domain retained.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.PropTestGraph10.MainResults.CoeffBound
open Qatlib.Papers.PropTestGraph10.MainResults.Model
universe u

/-- Every full original Lemma15 coefficient bound follows from actual support restriction and Boolean Mobius inversion. -/
theorem coeffBound {σ : Type u} [Fintype σ] [DecidableEq σ]
    (P : AcceptancePolynomial σ) {k : ℕ} (d : σ →₀ ℕ) (hd : d.support.card=k) :
    |P.poly.coeff d| ≤ (2 : ℝ)^k := by
  have hb : ∀ x : σ → ℝ, (∀ i, x i=0 ∨ x i=1) → |MvPolynomial.eval x P.poly| ≤ 1 := by
    intro x hx
    apply abs_le.mpr
    constructor
    · linarith [P.nonneg x hx]
    · exact P.le_one x hx
  simpa only [hd] using
    Qatlib.Concepts.QueryComplexity.DegreeMethod.CubeCoeff.coeffBound P.poly P.multilinear hb d

end Qatlib.Papers.PropTestGraph10.MainResults.CoeffBound
