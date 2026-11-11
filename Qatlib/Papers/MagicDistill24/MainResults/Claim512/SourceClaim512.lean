/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Claim 5.1.2 (arXiv:2408.07764v2, p.39, Eq (247))

For any place `P ∉ 𝒫` (a place of `P''`), `ι_P(X) ∈ A_F(7A + E − D)`.

Here `F = 𝔽_q(x,y)` is the function field of the curve, `X` the function whose
principal divisor `(X)` is analysed in Claim 5.1.1, `ι_P` is the embedding of `F`
into the adele ring `A_F` where the `P`-slot is modified so as to absorb the only
possible pole of `X` (at `P`), and `A_F(7A+E−D)` is the adele lattice attached to
the divisor `7A + E − D`. The paper derives membership from the divisor estimate
`(X) ≥ 7A + E − D'' + ∑_{j} P_ij` (Eq (245)) together with the comparison of the
divisors `D''` and `D` (Eq (246)); a pole of `X` may only sit at `P`, and every
other local component is bounded exactly as the lattice `A_F(7A+E−D)` requires.

Formalisation boundary. Mathlib has no algebraic-function-field / adele /
Weil-differential theory, so the derivation of the *divisor inequality* from
Eq (245)–(246) is not formalised. What is captured faithfully here is the concrete
local-valuation content of adele-lattice membership: given the local bound
`-ν_Q(7A+E−D) ≤ ν_Q(X)` at every place `Q ≠ P` (the divisor-theoretic input), the
embedded adele `ι_P(X)` lies in the lattice `A_F(7A+E−D)` (with an arbitrary value in
the `P`-slot). This is the exact "local condition" form that the paper's containment
unfolds to; the divisor/Riemann–Roch derivation is the missing hypothesis.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Claim512

/-- An adele of a function field `F` over a set of places: one local-field element
per place. -/
structure Adeles (Place : Type*) (F : Type*) where
  comp : Place → F

/-- The embedding `ι_P` of Claim 5.1.2: the principal adele of `X` in which the
`P`-slot carries the distinguished value `0` (the paper allows an arbitrary value at
`P`, the only possible pole of `X`), and every other slot carries `X`. -/
def iotaP {Place F : Type*} [Zero F] [DecidableEq Place] (X : F) (P : Place) : Adeles Place F :=
  ⟨fun Q => if Q = P then Zero.zero else X⟩

/-- Membership in the adele lattice `A_F(D)` of a divisor `D` (given by its
coefficient function): at every place `Q`, a nonzero local component `a` is no more
singular than `D` permits, `-D(Q) ≤ ν_Q(a)`. -/
def AdeleLattice {Place F : Type*} [Zero F] (val : Place → F → ℤ) (D : Place → ℤ)
    (a : Adeles Place F) : Prop :=
  ∀ Q : Place, ∀ _ : a.comp Q ≠ Zero.zero, -D Q ≤ val Q (a.comp Q)

/-- Fixed arXiv:2408.07764v2, Claim 5.1.2 (p.39, Eq (247)): for a place `P` and a
function `X` that, away from `P`, satisfies the local bound prescribed by the divisor
`D = 7A + E − D` (the divisor-theoretic input from Eqs (245)–(246)), the embedded
adele `ι_P(X)` lies in the adele lattice `A_F(D)`. -/
theorem source_claim_5_1_2 {Place F : Type*} [Zero F] [DecidableEq Place]
    (val : Place → F → ℤ) (D : Place → ℤ) (X : F) (P : Place)
    (_hX : X ≠ 0)
    (hdiv : ∀ Q : Place, Q ≠ P → -D Q ≤ val Q X) :
    AdeleLattice val D (iotaP X P) := by
  unfold AdeleLattice
  intro Q hQ
  by_cases hQP : Q = P
  · subst hQP
    simp [iotaP] at hQ
  · have hcomp : (iotaP X P).comp Q = X := by simp [iotaP, hQP]
    rw [hcomp]
    exact hdiv Q hQP

end Qatlib.Papers.MagicDistill24.MainResults.Claim512
