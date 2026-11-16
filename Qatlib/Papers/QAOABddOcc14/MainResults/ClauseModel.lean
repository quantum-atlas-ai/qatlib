/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOABddOcc14.MainResults.Instance.SourceInstanceModel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section


/-!
# The archived trigonometric clause expression as a finite functional

Legacy commit d8d59743ce7eb006f4a072c0a266ff7ca628f31d, SourceQaoaObjective;
arXiv:1412.6062v2, expressions surrounding (25).
This file preserves the finite expression used by the closed aggregation
proofs. It is not asserted to equal a QAOA expectation: the legacy coefficient
includes the distinguished clause, and the legacy phase sign also needs a
source bridge. For a sole positive clause the archived expression reduces
to sin(4 gamma)/8, whereas its archived state has expectation -sin(gamma)/2
at beta=pi/4. No admitted state-to-expression identity is imported here.
The original claim and its intended physical expectation remain unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QAOABddOcc14.MainResults

open scoped BigOperators
open Qatlib.Papers.QAOABddOcc14.MainResults

/-- The computational basis of the `n`-qubit register. -/
abbrev Basis (n : ℕ) := Fin n → Bool

/-- The `Z`-product of the two bits of clause `q` other than `i`, read as a real.
Used for the coefficient polynomials `c_1,c_2,c_3` of paper (19)–(21). -/
def otherProd {n : ℕ} (z : Basis n) (i : Fin n) (q : Triple n) : ℝ :=
  if i = q.first then (bitSign z q.second : ℝ) * (bitSign z q.third : ℝ)
  else if i = q.second then (bitSign z q.first : ℝ) * (bitSign z q.third : ℝ)
  else (bitSign z q.first : ℝ) * (bitSign z q.second : ℝ)

/-- The archived incident-clause coefficient, including the distinguished clause. No identification with the paper's target-excluded coefficient is asserted. -/
def localCoeff {n : ℕ} (I : E3Instance n) (i : Fin n) (z : Basis n) : ℝ :=
  ∑ q : Triple n,
    if I.d q ≠ 0 ∧ (q.first = i ∨ q.second = i ∨ q.third = i) then
      (I.d q : ℝ) * otherProd z i q
    else 0

/-- The archived sine functional. Its equality with the physical expectation is not assumed. -/
def clauseExpr {n : ℕ} (I : E3Instance n) (γ : ℝ) (p : Triple n) : ℝ :=
  (1 / 8) * (I.d p : ℝ) * ((2 : ℝ) ^ n)⁻¹ *
    ∑ z : Basis n,
      (Real.sin (γ * ((I.d p : ℝ) + localCoeff I p.first z + localCoeff I p.second z +
            localCoeff I p.third z))
        + Real.sin (γ * ((I.d p : ℝ) + localCoeff I p.first z - localCoeff I p.second z -
            localCoeff I p.third z))
        + Real.sin (γ * ((I.d p : ℝ) - localCoeff I p.first z + localCoeff I p.second z -
            localCoeff I p.third z))
        + Real.sin (γ * ((I.d p : ℝ) - localCoeff I p.first z - localCoeff I p.second z +
            localCoeff I p.third z)))

end Qatlib.Papers.QAOABddOcc14.MainResults
