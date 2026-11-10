/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CipherCircuits.ChainingTags

namespace Qatlib.Papers.SimonSymKey16.CbcAlgebra
set_option autoImplicit false
open Qatlib.Concepts.CipherCircuits.ChainingTags
variable {n : ℕ}

theorem source_prefix_tag (π : Equiv.Perm (Block n))
    (a b : List (Block n)) (hb : b ≠ []) (k : ℕ) :
    cbc π (b ++ zblocks π k (chain π a) (chain π b)) =
      if Even (k+1) then piter π (k+1) (chain π a) else piter π (k+1) (chain π b) :=
  cbc_prefix_tag_identity π a b hb k

theorem source_suffix_nonzero (π : Equiv.Perm (Block n)) (a b : List (Block n))
    (hab : chain π a ≠ chain π b) (k : ℕ) :
    ∀ z ∈ zblocks π k (chain π a) (chain π b), z ≠ 0 :=
  zblocks_all_ne_zero π π.injective _ _ hab k

theorem source_suffix_fresh (π : Equiv.Perm (Block n)) (a b : List (Block n))
    (hab : chain π a ≠ chain π b) (k : ℕ) (queried : List (Block n))
    (hq : 0 ∈ queried) : queried ≠ zblocks π k (chain π a) (chain π b) := by
  intro h
  subst queried
  exact source_suffix_nonzero π a b hab k 0 hq rfl
end Qatlib.Papers.SimonSymKey16.CbcAlgebra
