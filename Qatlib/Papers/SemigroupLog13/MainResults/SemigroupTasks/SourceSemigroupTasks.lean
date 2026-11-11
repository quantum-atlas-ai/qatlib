/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemigroupLog13.MainResults.SemigroupAlgorithm.SourceSemigroupAlgorithm

set_option backward.isDefEq.respectTransparency false

/-!
# Problem targets of SemigroupLog13

Fixed paper: Childs--Ivanyos, *Quantum computation of discrete logarithms in
semigroups*, arXiv:1310.6238v2 (1 Nov 2013).

This file names the three search targets that the paper's algorithms compute:

* `dlogValue g x` is `log_g x` (Section 1, page 2): the smallest positive `a`
  with `g^a = x`, or `none` when no such `a` exists.
* `shiftValue y g x` is the shifted logarithm of Section 4 (Lemma 2): the
  smallest positive `a` with `x = y g^a`, or `none`.
* `MembershipOK g x a` is the constructive membership relation of Section 5
  (Theorem 2/Theorem 3/Lemma 3): `a` has positive total degree and
  `x = g_0^{a_0} ⋯ g_{k-1}^{a_{k-1}}`, with zero exponents meaning "no factor"
  (the product is taken in the identity-adjoined monoid `WithOne S`).

All three use `Nat.find`, so they return the least witness; the `_eq_some_iff`
lemmas record the exact distinguishing property (existence, correctness and
minimality), which is what the paper's binary search and Grover searches use.
-/

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace Qatlib.Papers.SemigroupLog13.MainResults

/-! ## §1. The ordinary discrete logarithm of the paper -/

section Dlog

variable {S : Type} [Semigroup S]

/-- `log_g x`: the smallest positive `a` with `g^a = x` in the
identity-adjoined monoid, or `none` when no such positive `a` exists
(Childs--Ivanyos, arXiv:1310.6238v2, Section 1, page 2). -/
def dlogValue (g x : S) : Option ℕ := by
  classical
  exact if h : ∃ a : ℕ, 0 < a ∧ spow g a = (x : WithOne S) then some (Nat.find h) else none

/-- Characterisation of `dlogValue`: it returns exactly the least positive
solution, and `none` exactly when no positive solution exists. -/
theorem dlogValue_eq_some_iff (g x : S) (a : ℕ) :
    dlogValue g x = some a ↔ 0 < a ∧ spow g a = (x : WithOne S) ∧
      ∀ b : ℕ, 0 < b → spow g b = (x : WithOne S) → a ≤ b := by
  unfold dlogValue
  by_cases hex : ∃ a : ℕ, 0 < a ∧ spow g a = (x : WithOne S)
  · rw [dif_pos hex]
    constructor
    · intro h
      have h' : Nat.find hex = a := Option.some.inj h
      subst h'
      exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2,
        fun b hb hsp => Nat.find_min' hex ⟨hb, hsp⟩⟩
    · rintro ⟨h1, h2, hmin⟩
      congr 1
      exact le_antisymm
        (Nat.find_min' hex ⟨h1, h2⟩)
        (hmin _ (Nat.find_spec hex).1 (Nat.find_spec hex).2)
  · rw [dif_neg hex]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨h1, h2, -⟩
      exact absurd ⟨a, h1, h2⟩ hex

end Dlog

/-! ## §2. The shifted discrete logarithm of Section 4 -/

section Shift

variable {S : Type} [Semigroup S]

/-- `shiftValue y g x`: the smallest positive `a` with `x = y g^a`, or `none`
when no such `a` exists (Lemma 2, Section 4, page 4). -/
def shiftValue (y g x : S) : Option ℕ := by
  classical
  exact if h : ∃ a : ℕ, 0 < a ∧ (x : WithOne S) = (y : WithOne S) * spow g a
    then some (Nat.find h) else none

/-- Characterisation of `shiftValue`: it returns exactly the least positive
solution of `x = y g^a`, and `none` exactly when no positive solution exists. -/
theorem shiftValue_eq_some_iff (y g x : S) (a : ℕ) :
    shiftValue y g x = some a ↔ 0 < a ∧ (x : WithOne S) = (y : WithOne S) * spow g a ∧
      ∀ b : ℕ, 0 < b → (x : WithOne S) = (y : WithOne S) * spow g b → a ≤ b := by
  unfold shiftValue
  by_cases hex : ∃ a : ℕ, 0 < a ∧ (x : WithOne S) = (y : WithOne S) * spow g a
  · rw [dif_pos hex]
    constructor
    · intro h
      have h' : Nat.find hex = a := Option.some.inj h
      subst h'
      exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2,
        fun b hb hsp => Nat.find_min' hex ⟨hb, hsp⟩⟩
    · rintro ⟨h1, h2, hmin⟩
      congr 1
      exact le_antisymm
        (Nat.find_min' hex ⟨h1, h2⟩)
        (hmin _ (Nat.find_spec hex).1 (Nat.find_spec hex).2)
  · rw [dif_neg hex]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨h1, h2, -⟩
      exact absurd ⟨a, h1, h2⟩ hex

end Shift

/-! ## §3. Constructive semigroup membership -/

section Membership

variable {S : Type} [CommSemigroup S] {k : ℕ}

/-- Constructive membership (Section 5, page 5): `a` is a nonzero exponent
tuple with `g_0^{a_0} ⋯ g_{k-1}^{a_{k-1}} = x`.  Zero exponents contribute no
factor; the product lives in the identity-adjoined monoid `WithOne S`. -/
def MembershipOK (g : Fin k → S) (x : S) (a : Fin k → ℕ) : Prop :=
  (∃ i, 0 < a i) ∧ ∏ i, (g i : WithOne S) ^ (a i) = (x : WithOne S)

end Membership

end Qatlib.Papers.SemigroupLog13.MainResults
