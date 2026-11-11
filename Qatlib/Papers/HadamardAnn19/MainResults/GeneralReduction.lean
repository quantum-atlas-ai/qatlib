/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Constrained Monomial Reductions

This module verifies scalar three-body and four-body substitutions using the Boolean AND penalty
from [SuksmonoMinato2019]. `threeBodyReduced` replaces one product by an ancillary variable,
while `fourBodyReduced` uses two ancillary products and two penalties.

The identities assume that the ancillary coordinates equal the corresponding Boolean products.
They remain valid after multiplication by arbitrary real coefficients or, for the four-body
identity, an arbitrary remaining factor.

## Main statements

* `hAnd_and` proves that the penalty vanishes on a Boolean product.
* `threeBody_reduction` and `threeBody_reduction_mul` verify the three-body substitution.
* `fourBody_reduction`, `fourBody_reduction_mul`, and `fourBody_reduction_mul_rest` verify the
  four-body substitution and its scalar multiples.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

namespace Qatlib.Papers.HadamardAnn19.MainResults.GeneralReduction

set_option autoImplicit false

/-- The scalar AND penalty `δ * (3 * qk + qi * qj - 2 * qi * qk - 2 * qj * qk)` used in the
monomial substitutions of [SuksmonoMinato2019]. -/
def hAnd (qi qj qk δ : ℝ) : ℝ :=
  δ * (3 * qk + qi * qj - 2 * qi * qk - 2 * qj * qk)

/-- For two Boolean inputs, the AND penalty vanishes at their product for every real
coefficient. -/
theorem hAnd_and {qi qj δ : ℝ} (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) :
    hAnd qi qj (qi * qj) δ = 0 := by
  unfold hAnd
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num

/-- The quadratic expression `qe * qc` plus the AND penalty enforcing the ancillary relation `qe
= qa * qb`. -/
def threeBodyReduced (qa qb qc qe δ : ℝ) : ℝ :=
  qe * qc + hAnd qa qb qe δ

/-- For Boolean `qa` and `qb` and an ancilla `qe = qa * qb`, the reduced expression equals `qa *
qb * qc`. The third coordinate and penalty coefficient may be arbitrary reals. -/
theorem threeBody_reduction {qa qb qc qe δ : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (he : qe = qa * qb) :
    qa * qb * qc = threeBodyReduced qa qb qc qe δ := by
  subst he
  unfold threeBodyReduced
  rw [hAnd_and ha hb]
  ring

/-- Multiplying the constrained three-body reduction identity by any real coefficient preserves
equality. -/
theorem threeBody_reduction_mul {qa qb qc qe δ c : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (he : qe = qa * qb) :
    c * (qa * qb * qc) = c * threeBodyReduced qa qb qc qe δ := by
  rw [threeBody_reduction ha hb he]

/-- The ancillary product `qe * qf` plus two AND penalties enforcing `qe = qa * qb` and `qf = qc
* qd`. -/
def fourBodyReduced (qa qb qc qd qe qf δ : ℝ) : ℝ :=
  qe * qf + hAnd qa qb qe δ + hAnd qc qd qf δ

/-- For four Boolean main coordinates and the two prescribed product ancillas, `fourBodyReduced`
equals their fourfold product for every real penalty coefficient. -/
theorem fourBody_reduction {qa qb qc qd qe qf δ : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (hc : qc = 0 ∨ qc = 1) (hd : qd = 0 ∨ qd = 1)
    (he : qe = qa * qb) (hf : qf = qc * qd) :
    qa * qb * qc * qd = fourBodyReduced qa qb qc qd qe qf δ := by
  subst he
  subst hf
  unfold fourBodyReduced
  rw [hAnd_and ha hb, hAnd_and hc hd]
  ring

/-- Multiplying the constrained four-body reduction identity by any real coefficient preserves
equality. -/
theorem fourBody_reduction_mul {qa qb qc qd qe qf δ c : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (hc : qc = 0 ∨ qc = 1) (hd : qd = 0 ∨ qd = 1)
    (he : qe = qa * qb) (hf : qf = qc * qd) :
    c * (qa * qb * qc * qd) = c * fourBodyReduced qa qb qc qd qe qf δ := by
  rw [fourBody_reduction ha hb hc hd he hf]

/-- The constrained four-body substitution remains an equality after multiplication on the right
by an arbitrary real factor `R`. -/
theorem fourBody_reduction_mul_rest {qa qb qc qd qe qf δ R : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (hc : qc = 0 ∨ qc = 1) (hd : qd = 0 ∨ qd = 1)
    (he : qe = qa * qb) (hf : qf = qc * qd) :
    qa * qb * qc * qd * R = fourBodyReduced qa qb qc qd qe qf δ * R := by
  rw [fourBody_reduction ha hb hc hd he hf]

end Qatlib.Papers.HadamardAnn19.MainResults.GeneralReduction
