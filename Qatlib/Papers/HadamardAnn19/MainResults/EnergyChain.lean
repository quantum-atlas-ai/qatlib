/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Order-Two Scalar Energy Chain

This module records the order-two scalar energy transformations of [SuksmonoMinato2019], from
the squared column inner product `ek2S` through the Boolean polynomial `ek2Q` to the
six-variable quadratic forms `e2Q` and `e2S`. The compensated Boolean expression agrees with the
original polynomial when the ancillary bits equal their prescribed products.

The inverse affine substitution is a polynomial identity over the reals. `correctedScalar22`
retains the coefficients of `e2S`, and `e2QTerms` provides a list of 22 distinct monomial
supports of degree at most two.

## Main statements

* `ek2S_eq_ek2Sreduced` expands the squared inner product on sign inputs.
* `e2Q_eq_ek2Q_on_manifold` establishes equality on the Boolean ancillary constraints.
* `e2Q_eq_e2S` verifies the inverse affine change of variables.
* `e2Q_eq_evalTerms`, `e2QTerms_card`, and `e2QTerms_twoBody` certify the explicit quadratic
  representation.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

namespace Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain

set_option autoImplicit false

/-- The scalar AND penalty `δ * (3 * qk + qi * qj - 2 * qi * qk - 2 * qj * qk)` used in the
energy chain of [SuksmonoMinato2019]. -/
def hAnd (qi qj qk δ : ℝ) : ℝ :=
  δ * (3 * qk + qi * qj - 2 * qi * qk - 2 * qj * qk)

/-- The AND penalty is zero when its ancillary coordinate is the product of the two Boolean
inputs. -/
theorem hAnd_and {qi qj δ : ℝ} (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) :
    hAnd qi qj (qi * qj) δ = 0 := by
  unfold hAnd
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num

/-- The squared inner product `(s0 * s2 + s1 * s3) ^ 2` of two columns of length two, as in Eq.
17 of [SuksmonoMinato2019]. -/
def ek2S (s0 s1 s2 s3 : ℝ) : ℝ :=
  (s0 * s2 + s1 * s3) ^ 2

/-- The quartic polynomial `2 + 2 * (s0 * s1 * s2 * s3)` obtained from the order-two squared
inner product on sign inputs. -/
def ek2Sreduced (s0 s1 s2 s3 : ℝ) : ℝ :=
  2 + 2 * (s0 * s1 * s2 * s3)

/-- The expanded four-variable polynomial obtained from `ek2Sreduced` by substituting `s = 1 - 2
* q`, matching Eq. 19 of [SuksmonoMinato2019]. -/
def ek2Q (q0 q1 q2 q3 : ℝ) : ℝ :=
  4 - 4 * q0 - 4 * q1 - 4 * q2 - 4 * q3
    + 8 * (q0 * q1) + 8 * (q0 * q2) + 8 * (q0 * q3)
    + 8 * (q1 * q2) + 8 * (q1 * q3) + 8 * (q2 * q3)
    - 16 * (q0 * q1 * q2) - 16 * (q0 * q1 * q3)
    - 16 * (q0 * q2 * q3) - 16 * (q1 * q2 * q3)
    + 32 * (q0 * q1 * q2 * q3)

/-- The quadratic polynomial obtained by replacing products `q0 * q2` and `q1 * q3` with `q4`
and `q5` in `ek2Q`. This expression precedes the addition of AND penalties. -/
def reducedQ (q0 q1 q2 q3 q4 q5 : ℝ) : ℝ :=
  4 - 4 * q0 - 4 * q1 - 4 * q2 - 4 * q3
    + 8 * (q0 * q1) + 8 * (q0 * q3) + 8 * (q1 * q2) + 8 * (q2 * q3)
    + 8 * q4 + 8 * q5
    - 16 * (q1 * q4) - 16 * (q0 * q5) - 16 * (q3 * q4) - 16 * (q2 * q5)
    + 32 * (q4 * q5)

/-- The six-variable quadratic polynomial of Eq. 20 of [SuksmonoMinato2019], with penalty
coefficient 16 for the two ancillary products. -/
def e2Q (q0 q1 q2 q3 q4 q5 : ℝ) : ℝ :=
  4 - 4 * q0 - 4 * q1 - 4 * q2 - 4 * q3 + 56 * q4 + 56 * q5
    + 8 * (q0 * q1) + 16 * (q0 * q2) + 8 * (q0 * q3)
    - 32 * (q0 * q4) - 16 * (q0 * q5)
    + 8 * (q1 * q2) + 16 * (q1 * q3) - 16 * (q1 * q4) - 32 * (q1 * q5)
    + 8 * (q2 * q3) - 32 * (q2 * q4) - 16 * (q2 * q5)
    - 16 * (q3 * q4) - 32 * (q3 * q5)
    + 32 * (q4 * q5)

/-- The six-variable quadratic spin polynomial obtained from `e2Q` by the inverse affine
substitution `q = (1 - s) / 2`. Its `s0 * s2` coefficient is four, as in Eq. 21 of
[SuksmonoMinato2019]. -/
def e2S (s0 s1 s2 s3 s4 s5 : ℝ) : ℝ :=
  28 + 6 * s0 + 6 * s1 + 6 * s2 + 6 * s3 - 12 * s4 - 12 * s5
    + 2 * (s0 * s1) + 4 * (s0 * s2) + 2 * (s0 * s3)
    - 8 * (s0 * s4) - 4 * (s0 * s5)
    + 2 * (s1 * s2) + 4 * (s1 * s3) - 4 * (s1 * s4) - 8 * (s1 * s5)
    + 2 * (s2 * s3) - 8 * (s2 * s4) - 4 * (s2 * s5)
    - 4 * (s3 * s4) - 8 * (s3 * s5)
    + 8 * (s4 * s5)

/-- The scalar form of the coefficient-consistent version of the reported Eq. 22, defined by
evaluating `e2S` on the six supplied real coordinates. -/
def correctedScalar22 (sigma0 sigma1 sigma2 sigma3 sigma4 sigma5 : ℝ) : ℝ :=
  e2S sigma0 sigma1 sigma2 sigma3 sigma4 sigma5

/-- When all four coordinates square to one, the squared inner product equals `2 + 2 * (s0 * s1
* s2 * s3)`, verifying Eqs. 17–18 of [SuksmonoMinato2019]. -/
theorem ek2S_eq_ek2Sreduced (s0 s1 s2 s3 : ℝ)
    (h0 : s0 ^ 2 = 1) (h1 : s1 ^ 2 = 1) (h2 : s2 ^ 2 = 1) (h3 : s3 ^ 2 = 1) :
    ek2S s0 s1 s2 s3 = ek2Sreduced s0 s1 s2 s3 := by
  have ha : (s0 * s2) ^ 2 = 1 := by rw [mul_pow, h0, h2]; norm_num
  have hb : (s1 * s3) ^ 2 = 1 := by rw [mul_pow, h1, h3]; norm_num
  unfold ek2S ek2Sreduced
  calc (s0 * s2 + s1 * s3) ^ 2
      = (s0 * s2) ^ 2 + (s1 * s3) ^ 2 + 2 * (s0 * s2) * (s1 * s3) := by ring
    _ = 2 + 2 * (s0 * s1 * s2 * s3) := by rw [ha, hb]; ring

/-- Substituting `s = 1 - 2 * q` in the reduced quartic spin polynomial gives `ek2Q` for
arbitrary real coordinates. -/
theorem ek2Sreduced_eq_ek2Q (q0 q1 q2 q3 : ℝ) :
    ek2Sreduced (1 - 2 * q0) (1 - 2 * q1) (1 - 2 * q2) (1 - 2 * q3) =
      ek2Q q0 q1 q2 q3 := by
  unfold ek2Sreduced ek2Q
  ring

/-- Setting `q4 = q0 * q2` and `q5 = q1 * q3` makes `reducedQ` equal `ek2Q` as a polynomial
identity over the reals. -/
theorem reducedQ_eq_ek2Q (q0 q1 q2 q3 : ℝ) :
    reducedQ q0 q1 q2 q3 (q0 * q2) (q1 * q3) = ek2Q q0 q1 q2 q3 := by
  unfold reducedQ ek2Q
  ring

/-- The explicit quadratic polynomial `e2Q` equals `reducedQ` plus 16 times the two
unit-coefficient AND penalties for arbitrary real coordinates. -/
theorem e2Q_eq_reducedQ_add_penalty (q0 q1 q2 q3 q4 q5 : ℝ) :
    e2Q q0 q1 q2 q3 q4 q5 =
      reducedQ q0 q1 q2 q3 q4 q5 +
        16 * (hAnd q0 q2 q4 1 + hAnd q1 q3 q5 1) := by
  unfold e2Q reducedQ hAnd
  ring

/-- For Boolean main coordinates and the prescribed product ancillas, `e2Q` agrees with the
original four-variable polynomial `ek2Q`. -/
theorem e2Q_eq_ek2Q_on_manifold {q0 q1 q2 q3 : ℝ}
    (h0 : q0 = 0 ∨ q0 = 1) (h1 : q1 = 0 ∨ q1 = 1)
    (h2 : q2 = 0 ∨ q2 = 1) (h3 : q3 = 0 ∨ q3 = 1) :
    e2Q q0 q1 q2 q3 (q0 * q2) (q1 * q3) = ek2Q q0 q1 q2 q3 := by
  rw [e2Q_eq_reducedQ_add_penalty, hAnd_and h0 h2, hAnd_and h1 h3,
    reducedQ_eq_ek2Q]
  ring

/-- Applying `q = (1 - s) / 2` to all six coordinates of `e2Q` gives `e2S` for arbitrary real
spins, verifying the scalar transformation in [SuksmonoMinato2019]. -/
theorem e2Q_eq_e2S (s0 s1 s2 s3 s4 s5 : ℝ) :
    e2Q ((1 - s0) / 2) ((1 - s1) / 2) ((1 - s2) / 2)
        ((1 - s3) / 2) ((1 - s4) / 2) ((1 - s5) / 2) =
      e2S s0 s1 s2 s3 s4 s5 := by
  unfold e2Q e2S
  ring

/-- The coefficient-consistent scalar expression `correctedScalar22` equals `e2S` by definition. -/
theorem correctedScalar22_eq_e2S (s0 s1 s2 s3 s4 s5 : ℝ) :
    correctedScalar22 s0 s1 s2 s3 s4 s5 = e2S s0 s1 s2 s3 s4 s5 := rfl

/-- The coefficient and variable-index list representing all 22 terms of `e2Q`, including its
constant term. -/
def e2QTerms : List (ℝ × List (Fin 6)) :=
  [(4, []),
   (-4, [0]), (-4, [1]), (-4, [2]), (-4, [3]),
   (56, [4]), (56, [5]),
   (8, [0, 1]), (16, [0, 2]), (8, [0, 3]), (-32, [0, 4]), (-16, [0, 5]),
   (8, [1, 2]), (16, [1, 3]), (-16, [1, 4]), (-32, [1, 5]),
   (8, [2, 3]), (-32, [2, 4]), (-16, [2, 5]),
   (-16, [3, 4]), (-32, [3, 5]),
   (32, [4, 5])]

/-- Evaluate a list of coefficient-index pairs by multiplying each coefficient by its indexed
coordinates and summing the resulting monomials. An empty index list contributes the
constant coefficient. -/
def evalTerms (terms : List (ℝ × List (Fin 6))) (q : Fin 6 → ℝ) : ℝ :=
  (terms.map (fun t => t.1 * (t.2.map q).prod)).sum

/-- The explicit term list for `e2Q` contains 22 entries. -/
theorem e2QTerms_length : e2QTerms.length = 22 := by decide

/-- The variable-index lists of the 22 terms in `e2QTerms` are pairwise distinct, as witnessed
by retaining length 22 after duplicate removal. -/
theorem e2QTerms_card : (e2QTerms.map (·.2)).eraseDups.length = 22 := by decide

/-- Every monomial index list in `e2QTerms` has length at most two. -/
theorem e2QTerms_twoBody : e2QTerms.all (fun t => decide (t.2.length ≤ 2)) = true := by
  decide

/-- Evaluating the explicit term list `e2QTerms` gives the same value as `e2Q` on any six real
coordinates. -/
theorem e2Q_eq_evalTerms (q : Fin 6 → ℝ) :
    e2Q (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) = evalTerms e2QTerms q := by
  simp only [e2Q, evalTerms, e2QTerms, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil]
  ring

end Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain
