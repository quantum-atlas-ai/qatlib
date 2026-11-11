/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CipherAttack14.MainResults.KeTwoClaw

set_option backward.isDefEq.respectTransparency false

/-!
# CipherAttack14 — the dissection decomposition of KE₄

Fixed source: M. Kaplan, *Quantum attacks against iterated block ciphers*,
arXiv:1410.1434v2 (2015).  Section 3, printed pages 9–10:

* Definition 4 (p. 9) introduces `KE4^{P,C}` with four plaintext/ciphertext pairs
  `P = (P_1, …, P_4)`, `C = (C_1, …, C_4)`: the goal is a key quadruple
  `(k_1, k_2, k_3, k_4)` with `F_{k_4}(F_{k_3}(F_{k_2}(F_{k_1}(P_i)))) = C_i` for
  all `i`.
* The decision version `d-KE4` (p. 9) is the single-pair version, and the paper
  writes it as the composition of Equation (1),
  `d-KE4 = SEARCH ∘ (f_0 ∧ g_0, …, f_{M-1} ∧ g_{M-1})`, where `f_X` is the answer
  of `d-KE2^{P,X}` and `g_X` the answer of `d-KE2^{X,C}`.
* The proof of Theorem 4 (p. 10) runs a quantum walk on the complete graph whose
  vertices are the `M` candidates for the value `X` after two encryptions.  "This
  correct value is unique, and the goal of the quantum walk is to find it"; once
  it is found, `O(N^{2/3})` further queries recover the keys.

This module records the decomposition exactly: a key quadruple, the middle value
it produces after two encryptions, the equivalence of `d-KE4` with the existence
of a feasible middle value (Equation (1)), the four-pair version of Definition 4
and its relation to the single-pair decision problem, the size `M` of the walk's
search space, and the uniqueness of the feasible middle value under the
uniqueness promise.  It does not build the walk or its cost ledger, so it does not
cover the time and memory statements of Theorem 4.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CipherAttack14.MainResults

open Finset

open scoped Classical

variable {N M : ℕ}

/-- A candidate key quadruple for four iterated encryptions (source Definition 4,
p. 9). -/
structure KeyQuad (N : ℕ) where
  /-- The first key. -/
  k1 : Fin N
  /-- The second key. -/
  k2 : Fin N
  /-- The third key. -/
  k3 : Fin N
  /-- The fourth key. -/
  k4 : Fin N

/-- The encryption of a block by a key quadruple, i.e. the four-fold composition
`F_{k_4} ∘ F_{k_3} ∘ F_{k_2} ∘ F_{k_1}` of source Definition 4 (p. 9). -/
def KeyQuad.encrypt (q : KeyQuad N) (F : PermFamily N M) (x : Fin M) : Fin M :=
  F q.k4 (F q.k3 (F q.k2 (F q.k1 x)))

/-- The middle value produced by a key quadruple (source p. 10: the value `X`
"after two encryptions"). -/
def KeyQuad.middle (q : KeyQuad N) (F : PermFamily N M) (x : Fin M) : Fin M :=
  F q.k2 (F q.k1 x)

/-- The middle value is exactly the value that the dissection walk searches for:
the encryption factors through it. -/
theorem KeyQuad.encrypt_eq_apply_middle (q : KeyQuad N) (F : PermFamily N M) (x : Fin M) :
    q.encrypt F x = F q.k4 (F q.k3 (q.middle F x)) := rfl

/-- A four-fold composition of permutations is injective, so a key quadruple
determines the middle value from the plaintext in an injective way. -/
theorem KeyQuad.encrypt_injective (q : KeyQuad N) (F : PermFamily N M) :
    Function.Injective (q.encrypt F) := by
  intro x y h
  exact (F q.k1).injective ((F q.k2).injective ((F q.k3).injective ((F q.k4).injective h)))

/-- The single-pair decision version `d-KE4^{P,C}` of source p. 9. -/
def dKE4 (F : PermFamily N M) (P C : Fin M) : Prop :=
  ∃ q : KeyQuad N, q.encrypt F P = C

/-- Source Definition 4 (p. 9): the four-pair key-extraction problem. -/
def dKE4Pairs (F : PermFamily N M) (P C : Fin 4 → Fin M) : Prop :=
  ∃ q : KeyQuad N, ∀ i : Fin 4, q.encrypt F (P i) = C i

/-- The paper's `f_X` (p. 9): the answer of `d-KE2^{P,X}` on the input `F`. -/
def fValue (F : PermFamily N M) (P : Fin M) (X : Fin M) : Prop :=
  dKE2 F P X

/-- The paper's `g_X` (p. 9): the answer of `d-KE2^{X,C}` on the input `F`. -/
def gValue (F : PermFamily N M) (C : Fin M) (X : Fin M) : Prop :=
  dKE2 F X C

/-- The paper's `SEARCH` function (p. 9), lifted to propositions. -/
def SEARCH (u : Fin M → Prop) : Prop :=
  ∃ X : Fin M, u X

/-- Equation (1) of the paper (p. 9): `d-KE4` is the search, over the `M` candidate
middle values `X`, for one where both `d-KE2^{P,X}` and `d-KE2^{X,C}` hold. -/
theorem dKE4_iff_SEARCH_composition (F : PermFamily N M) (P C : Fin M) :
    dKE4 F P C ↔ SEARCH fun X => fValue F P X ∧ gValue F C X := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q.middle F P, ⟨q.k1, q.k2, rfl⟩, q.k3, q.k4, ?_⟩
    rw [← KeyQuad.encrypt_eq_apply_middle]
    exact hq
  · rintro ⟨X, ⟨k1, k2, h2⟩, k3, k4, h4⟩
    refine ⟨⟨k1, k2, k3, k4⟩, ?_⟩
    show F k4 (F k3 (F k2 (F k1 P))) = C
    rw [h2]
    exact h4

/-- The set of feasible middle values: the vertices of the complete graph that the
dissection walk of Theorem 4 searches (source p. 10). -/
noncomputable def middleCandidates (F : PermFamily N M) (P C : Fin M) : Finset (Fin M) :=
  univ.filter fun X => dKE2 F P X ∧ dKE2 F X C

/-- Membership in the candidate set is exactly Equation (1) at one vertex. -/
theorem mem_middleCandidates (F : PermFamily N M) (P C : Fin M) (X : Fin M) :
    X ∈ middleCandidates F P C ↔ dKE2 F P X ∧ dKE2 F X C := by
  simp [middleCandidates]

/-- The feasible middle values are exactly the middle values of the key quadruples
that encrypt `P` to `C`.  This is the sense in which the walk "searches for the
correct value `X`" (source p. 10). -/
theorem mem_middleCandidates_iff_exists_quad (F : PermFamily N M) (P C : Fin M) (X : Fin M) :
    X ∈ middleCandidates F P C ↔ ∃ q : KeyQuad N, q.middle F P = X ∧ q.encrypt F P = C := by
  rw [mem_middleCandidates]
  constructor
  · rintro ⟨⟨k1, k2, h2⟩, k3, k4, h4⟩
    refine ⟨⟨k1, k2, k3, k4⟩, ?_, ?_⟩
    · show F k2 (F k1 P) = X
      exact h2
    · show F k4 (F k3 (F k2 (F k1 P))) = C
      rw [h2]
      exact h4
  · rintro ⟨q, hmid, henc⟩
    refine ⟨⟨q.k1, q.k2, hmid⟩, q.k3, q.k4, ?_⟩
    rw [← hmid, ← KeyQuad.encrypt_eq_apply_middle]
    exact henc

/-- `d-KE4` holds exactly when the dissection search space is nonempty. -/
theorem dKE4_iff_middleCandidates_nonempty (F : PermFamily N M) (P C : Fin M) :
    dKE4 F P C ↔ (middleCandidates F P C).Nonempty := by
  rw [dKE4_iff_SEARCH_composition]
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, (mem_middleCandidates F P C X).2 hX⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, (mem_middleCandidates F P C X).1 hX⟩

/-- The walk of Theorem 4 runs on the complete graph with `M` vertices, one per
candidate middle value; this is the `M^{1/2}` Grover factor of the query count
`O(M^{1/2} N^{2/3})` in the proof of Theorem 4 (p. 10). -/
theorem middleCandidates_card_le (F : PermFamily N M) (P C : Fin M) :
    (middleCandidates F P C).card ≤ M := by
  simpa [middleCandidates] using card_filter_le (univ : Finset (Fin M))
    (fun X => dKE2 F P X ∧ dKE2 F X C)

/-- The paper's four-pair formulation implies the single-pair decision problem for
each known pair (the direction used on p. 10 when the uniqueness assumption is
replaced by four pairs of data). -/
theorem dKE4_of_dKE4Pairs (F : PermFamily N M) (P C : Fin 4 → Fin M)
    (h : dKE4Pairs F P C) (i : Fin 4) : dKE4 F (P i) (C i) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, hq i⟩

/-- Source p. 10: "this correct value is unique".  Under the uniqueness promise on
the key quadruple, the feasible middle values form a subsingleton, so a search over
the `M` candidates has a unique marked vertex. -/
theorem eq_of_mem_middleCandidates_of_unique (F : PermFamily N M) (P C : Fin M)
    (huniq : ∀ q q' : KeyQuad N, q.encrypt F P = C → q'.encrypt F P = C → q = q')
    {X Y : Fin M} (hX : X ∈ middleCandidates F P C) (hY : Y ∈ middleCandidates F P C) :
    X = Y := by
  obtain ⟨q, hmid, henc⟩ := (mem_middleCandidates_iff_exists_quad F P C X).1 hX
  obtain ⟨q', hmid', henc'⟩ := (mem_middleCandidates_iff_exists_quad F P C Y).1 hY
  have hq : q = q' := huniq q q' henc henc'
  rw [← hmid, ← hmid', hq]

end Qatlib.Papers.CipherAttack14.MainResults
