/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Qatlib.Papers.HiddenPoly07.MainResults.MeasurementSuccessBound

/-!
# HiddenPoly07.MainResults — success probability of the approximate measurement (Lemma 3.1)

Paper: T. Decker, J. Draisma, P. Wocjan, *Efficient Quantum Algorithm for
Identifying Hidden Polynomials*, arXiv:0706.1219v3, Lemma 3.1 and its proof
(Section 3.4, Eqs. (11), (12), (15), (16)); printed page 8.

The source fixes `k = n` copies of the polynomial function state, a constant `D`
depending only on `n`, a set `X_good ⊆ F^n`, and for `x ∈ X_good` a set
`W_good^x ⊆ {w ∈ F^n | 1 ≤ η_w^x ≤ D}` of solution-fibre images, where
`η_w^x = |S_w^x|` counts the solutions of `Φ_n(b) x = w`.  The proof computes the
overall success probability

* Eq. (16): `d^{-3n} · Σ_{x ∈ X_good} (Σ_{w ∈ W_good^x} √η_w^x)^2`,

and concludes that it is at least

* Eq. (11): `d^{-3n} · |X_good| · |W_good|^2`.

## The square convention

The printed definition of the minimum is `|W_good| := min_{x ∈ X_good} |W_good^x|^2`
and Eq. (11) squares it once more, i.e. the printed bound is
`d^{-3n} · |X_good| · (min_x |W_good^x|^2)^2`.  That doubly squared form is *not*
what Eq. (16) yields: a single `x`-summand is only
`(Σ_{w} √η_w^x)^2 ≥ |W_good^x|^2 ≥ min_y |W_good^y|^2`, one square short of
`(min_y |W_good^y|^2)^2`, and it would exceed `1` in the regime of Prop. 4.1
(`|W_good^x| = Ω(d^n)`, `|X_good| = Ω(d^n)`), where a probability bound of
`d^{-3n} · d^n · d^{4n}` is impossible.  Remark 3.2 (`|W_good| = Ω(d^n)` for a
constant bound) and the chain of Cor. 4.2 (which yields `1/D^2 - O(1/d)`) are both
consistent with the *unsquared* minimum `min_x |W_good^x|` together with the single
square of Eq. (11).  The formalization therefore records all three statements:

* `lemma31_success_lower_bound` — the reading supported by Remark 3.2, Prop. 4.1
  and Cor. 4.2: `|W_good| := min_x |W_good^x|`, bound `d^{-3n}|X_good||W_good|^2`;
* `lemma31_min_square_bound` — literally the printed minimum
  `|W_good| := min_x |W_good^x|^2` with the single square, i.e. the strongest
  statement Eq. (16) actually gives for that definition;
* `lemma31_printed_bound` — the printed doubly squared form, which follows only in
  the degenerate case `|W_good| ≤ 1`.

Not formalized here (documented gaps): the state-identification measurement
itself — the density operator `ρ̃_Q^{⊗k}` of Eq. (4), the approximate unitary `V_x`
of Eqs. (13)–(14), the Fourier measurement of Eq. (8), and the computation of
Eq. (15) — as well as the efficiency of `V_x` from membership oracles for
`X_good`, `W_good^x` and enumeration of `S_w^x`, none of which enters Eq. (11) or
the proof of Eq. (11).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HiddenPoly07.MainResults

open Qatlib.Papers.HiddenPoly07.MainResults

open scoped BigOperators

/-- The full finite fibre family has a constant minimum good-set cardinality.
This is a reusable finite witness for the Lemma 3.1 interface: every fibre is
the whole finite codomain, so its minimum cardinality is the codomain size. -/
theorem WgoodMin_univ {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) :
    WgoodMin (Finset.univ : Finset (Fin n → F))
        (fun _ => (Finset.univ : Finset (Fin n → F))) =
      Fintype.card (Fin n → F) := by
  classical
  simp [WgoodMin, Finset.image_const]

/-- The full finite fibre family has a constant printed squared minimum.
This is the finite witness for the literal squared convention in Lemma 3.1. -/
theorem WgoodSq_univ {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) :
    WgoodSq (Finset.univ : Finset (Fin n → F))
        (fun _ => (Finset.univ : Finset (Fin n → F))) =
      (Fintype.card (Fin n → F)) ^ 2 := by
  classical
  simp [WgoodSq, Finset.image_const]

end Qatlib.Papers.HiddenPoly07.MainResults
