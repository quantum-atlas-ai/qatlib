/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CipherCircuits.ChainingTags

/-!
# CBC suffix identities for the Simon attack

The results describe the tag obtained by appending `zblocks` to a message prefix and the
conditions that make this suffix nonzero and distinct from a queried block list. The tag formula
alternates between iterates of the two prefix chain values according to parity. See
[SantoliSchaffner2017] for the source development.

## Main statements

* `source_prefix_tag`: evaluates the CBC tag after the constructed suffix.
* `source_suffix_nonzero`: proves each suffix block is nonzero when the prefix chain values
  differ.
* `source_suffix_fresh`: distinguishes the suffix from any queried block list containing zero.

## References

* [Santoli and Schaffner, 2017][SantoliSchaffner2017]
-/

namespace Qatlib.Papers.SimonSymKey16.CbcAlgebra
set_option autoImplicit false
open Qatlib.Concepts.CipherCircuits.ChainingTags
variable {n : ℕ}

/-- For a nonempty prefix `b`, appending the constructed suffix gives the `(k + 1)`-fold
permutation iterate of `chain π a` when `k + 1` is even, and of `chain π b` otherwise. See
[SantoliSchaffner2017]. -/
theorem source_prefix_tag (π : Equiv.Perm (Block n))
    (a b : List (Block n)) (hb : b ≠ []) (k : ℕ) :
    cbc π (b ++ zblocks π k (chain π a) (chain π b)) =
      if Even (k+1) then piter π (k+1) (chain π a) else piter π (k+1) (chain π b) :=
  cbc_prefix_tag_identity π a b hb k

/-- If the two prefix chain values differ, every block in the constructed suffix is nonzero. -/
theorem source_suffix_nonzero (π : Equiv.Perm (Block n)) (a b : List (Block n))
    (hab : chain π a ≠ chain π b) (k : ℕ) :
    ∀ z ∈ zblocks π k (chain π a) (chain π b), z ≠ 0 :=
  zblocks_all_ne_zero π π.injective _ _ hab k

/-- If the prefix chain values differ, any queried block list containing zero differs from the
constructed suffix. See [SantoliSchaffner2017]. -/
theorem source_suffix_fresh (π : Equiv.Perm (Block n)) (a b : List (Block n))
    (hab : chain π a ≠ chain π b) (k : ℕ) (queried : List (Block n))
    (hq : 0 ∈ queried) : queried ≠ zblocks π k (chain π a) (chain π b) := by
  intro h
  subst queried
  exact source_suffix_nonzero π a b hab k 0 hq rfl
end Qatlib.Papers.SimonSymKey16.CbcAlgebra
