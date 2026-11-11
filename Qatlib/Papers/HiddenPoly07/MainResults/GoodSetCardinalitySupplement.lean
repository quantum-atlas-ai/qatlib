/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Qatlib.Papers.HiddenPoly07.MainResults.GoodSetCardinality

/-!
# HiddenPoly07.MainResults — the good set `X_good = (F^×)^n` of Prop. 4.1

Paper: T. Decker, J. Draisma, P. Wocjan, *Efficient Quantum Algorithm for
Identifying Hidden Polynomials*, arXiv:0706.1219v3, Proposition 4.1 and
Corollary 4.2 (Section 4.1).

Proposition 4.1 takes the characteristic `p` of `F` to be larger than `n`,
sets `X_good := (F^×)^n`, and lets `W_good^x` be the set of `w` whose fibre of
`f(x, ·)` over `w` is zero-dimensional, with `η_w^x ≥ 1`.  It then claims that
the requirements of Lemma 3.1 are satisfied and that
`|X_good| = Ω(d^n)` and `|W_good^x| = Ω(d^n)`.

This module formalizes the `X_good` half of that proposition:

* `optionUnitsEquiv` and `card_units_eq`: a finite field `F` of size `d` has
  exactly `d - 1` units, so `|F^×| = d - 1`;
* `Xgood` and `card_Xgood`: `|(F^×)^n| = (d - 1)^n`;
* `card_Xgood_ge`: `(d - 1)^n ≥ d^n / 2^n` for `d ≥ 2`, i.e. `|X_good| = Ω(d^n)`
  with the explicit constant `2^{-n}`.

Not formalized here (documented gap): the `W_good^x` half.  It requires that the
fibres of the map `b ↦ f(x, b)` are zero-dimensional on the open set of distinct
coordinates (`det(∂f_i/∂B_j) ≠ 0` because `p > n` and the Vandermonde matrix is
invertible), the Gröbner-basis uniformity bound `D`, and the Schwartz–Zippel
estimate `|I_x| ≤ κ d^{n-1}` for the image of the complement.  None of that
finite-field algebraic geometry exists in this repository, so `|W_good^x| = Ω(d^n)`
is left open.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HiddenPoly07.MainResults

open Qatlib.Papers.HiddenPoly07.MainResults

open scoped BigOperators

/-- The unit-image presentation of `X_good` agrees with the explicit
non-vanishing predicate used by the counting lemmas. -/
theorem Xgood_eq_filter_nonzero (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) :
    Xgood F n = Finset.univ.filter (fun x : Fin n → F => ∀ i, x i ≠ 0) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Xgood]

/-- The good-set predicate has a canonical all-ones witness, so `X_good` is
always nonempty for a field. -/
theorem Xgood_nonempty (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Xgood F n).Nonempty := by
  classical
  refine ⟨fun _ => 1, (mem_Xgood).2 ?_⟩
  intro i
  exact one_ne_zero

/-- In particular, the finite good-set cardinality is positive. -/
theorem card_Xgood_pos (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    0 < (Xgood F n).card :=
  Finset.card_pos.mpr (Xgood_nonempty F n)

end Qatlib.Papers.HiddenPoly07.MainResults
