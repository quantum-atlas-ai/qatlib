/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemigroupLog13.MainResults.SemigroupCore.SourceSemigroupCore

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3: the pigeonhole bound on the lexicographically first exponent tuple

Fixed paper: Childs--Ivanyos, *Quantum computation of discrete logarithms in
semigroups*, arXiv:1310.6238v2 (1 Nov 2013), Lemma 3, page 6.

The paper states (for a finite abelian semigroup `S`): if `a = (a_1, …, a_k)` is
the lexicographically first tuple from `ℕ_0^k` with
`x = g_1^{a_1} ⋯ g_k^{a_k}`, then `∏ (a_i + 1) ≤ |S|`.

The pigeonhole map used in the proof has codomain `S ∪ {1}` (the empty exponent
tuple contributes the adjoined identity, which is not an element of a semigroup
without identity).  Hence the literal statement is sharp only when an identity
is present; for a plain commutative semigroup the exact bound is `|S| + 1`.
Both forms are recorded and proved here:

* `lemma3_pigeonhole` -- the paper's `|S|` bound in a finite commutative monoid
  (the reading under which the paper's inequality is true);
* `lemma3_pigeonhole_semigroup` -- the corrected `|S| + 1` bound for a finite
  commutative semigroup without an assumed identity.

A literal `|S|` bound in the semigroup case is false: on `{a, b, c}` with
`a·a = a`, `b·b = b`, `a·b = c` and `c` absorbing, `x = c = a·b` has
lexicographically first tuple `(1,1)` and `(1+1)(1+1) = 4 > 3 = |S|`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.SemigroupLog13.MainResults

namespace Qatlib.Papers.SemigroupLog13.MainResults.Lemma3Pigeonhole

/-- **Lemma 3** (Childs--Ivanyos, arXiv:1310.6238v2, Lemma 3, page 6), monoid
form.  Let `S` be a finite commutative monoid and `x, g_1, …, g_k ∈ S`.  If
`(a_1, …, a_k)` is the lexicographically first tuple from `ℕ_0^k` with
`x = g_1^{a_1} ⋯ g_k^{a_k}`, then `(a_1+1) ⋯ (a_k+1) ≤ |S|`.

The two hypotheses are the paper's "lexicographically first": `hfirst` records
that the tuple represents `x`, and `hmin` says no lexicographically smaller
tuple represents `x`. -/
theorem lemma3_pigeonhole {S : Type} [CommMonoid S] [Fintype S] {k : ℕ}
    (g : Fin k → S) (x : S) (a : Fin k → ℕ)
    (hfirst : tupleProd g a = x)
    (hmin : ∀ b : Fin k → ℕ, tupleProd g b = x → ¬ LexLt b a) :
    (∏ i, (a i + 1)) ≤ Fintype.card S :=
  lemma3_monoid g x a hfirst hmin

/-- **Lemma 3** (Childs--Ivanyos, arXiv:1310.6238v2, Lemma 3, page 6),
semigroup form without an assumed identity.  For a finite commutative semigroup
`S`, the pigeonhole argument over `S ∪ {1}` gives the sharp bound
`∏ (a_i + 1) ≤ |S| + 1`; see the module docstring for the three-element
counterexample showing that `|S|` itself is not valid without an identity. -/
theorem lemma3_pigeonhole_semigroup {S : Type} [CommSemigroup S] [Fintype S] {k : ℕ}
    (g : Fin k → S) (x : S) (a : Fin k → ℕ)
    (hfirst : tupleProd (fun i => (g i : WithOne S)) a = (x : WithOne S))
    (hmin : ∀ b : Fin k → ℕ,
      tupleProd (fun i => (g i : WithOne S)) b = (x : WithOne S) → ¬ LexLt b a) :
    (∏ i, (a i + 1)) ≤ Fintype.card S + 1 :=
  lemma3_semigroup g x a hfirst hmin

end Qatlib.Papers.SemigroupLog13.MainResults.Lemma3Pigeonhole
