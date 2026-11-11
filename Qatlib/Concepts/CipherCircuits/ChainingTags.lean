/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result

/-!
# Binary chaining tags and XOR periods

This module defines binary blocks, iterates of a block function, and the chaining recurrences
`cbc` and `chain`. It constructs the suffix `zblocks` from two iterated inputs and proves
explicit parity-dependent tag identities, providing algebra used in symmetric-key period
constructions [SantoliSchaffner2017].

The function `gfun` is invariant under a specified Boolean-and-block XOR shift. Injectivity of
the block function ensures that suffix blocks constructed from distinct inputs are nonzero.

## Main statements

* `cbc_eq_pi_chain`: the two chaining conventions differ by a final application of the block
  function on nonempty inputs.
* `cbc_prefix_tag_identity`: a constructed suffix gives a parity-dependent iterate of a prefix
  chain value.
* `zblocks_all_ne_zero`: injectivity and distinct seeds make every constructed block nonzero.
* `gfun_period`: the constructed XOR shift preserves `gfun`.

## References

* [Santoli and Schaffner, 2017][SantoliSchaffner2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CipherCircuits.ChainingTags

/-- A length-`n` binary block, represented by a function from `Fin n` to `ZMod 2`. -/
abbrev Block (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

/-- Adding a binary block to itself gives zero. -/
lemma block_add_self (x : Block n) : x + x = 0 := by
  calc x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp
    _ = ((1 : ZMod 2) + 1) • x := (add_smul (1 : ZMod 2) (1 : ZMod 2) x).symm
    _ = 0 := by
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h2, zero_smul]

/-- Adding the same binary block twice on the right cancels both copies. -/
lemma block_add_self_add (x y : Block n) : x + y + y = x := by
  rw [add_assoc, block_add_self, add_zero]

/-- In `x + y + x`, the two copies of `x` cancel. -/
lemma block_add_add_self (x y : Block n) : x + y + x = y := by
  rw [add_comm (x + y) x, ← add_assoc, block_add_self, zero_add]

/-- In `x + (x + y)`, the two copies of `x` cancel. -/
lemma add_add_self_left (x y : Block n) : x + (x + y) = y := by
  rw [← add_assoc, block_add_self, zero_add]

/-- In `x + (y + x)`, the two copies of `x` cancel. -/
lemma add_add_self_right (x y : Block n) : x + (y + x) = y := by
  rw [← add_assoc]
  exact block_add_add_self x y

/-- Two binary blocks are equal if their sum is zero. -/
lemma eq_of_add_eq_zero {x y : Block n} (h : x + y = 0) : x = y := by
  have h1 : x + (y + y) = x := by rw [block_add_self, add_zero]
  calc x = x + (y + y) := h1.symm
    _ = (x + y) + y := (add_assoc x y y).symm
    _ = 0 + y := by rw [h]
    _ = y := zero_add y

/-- The `k`-fold iterate of the block function `π`, with zeroth iterate equal to the identity. -/
def piter (π : Block n → Block n) : ℕ → Block n → Block n
  | 0 => id
  | k + 1 => π ∘ piter π k

/-- The zeroth iterate of a block function is the identity. -/
@[simp] lemma piter_zero (π : Block n → Block n) : piter π 0 = id := rfl

/-- The successor iterate is the composition of `π` with the preceding iterate. -/
@[simp] lemma piter_succ (π : Block n → Block n) (k : ℕ) :
    piter π (k + 1) = π ∘ piter π k := rfl

/-- Evaluating a successor iterate applies `π` to the value of the preceding iterate. -/
lemma piter_succ_apply (π : Block n → Block n) (k : ℕ) (x : Block n) :
    piter π (k + 1) x = π (piter π k x) := rfl

/-- The accumulator recurrence that replaces `acc` by `π (acc + m)` for each message block. -/
def cbcAux (π : Block n → Block n) : Block n → List (Block n) → Block n
  | acc, [] => acc
  | acc, m :: ms => cbcAux π (π (acc + m)) ms

/-- The CBC tag recurrence, returning zero on an empty message and starting a nonempty message
with `π` of its first block. -/
def cbc (π : Block n → Block n) : List (Block n) → Block n
  | [] => 0
  | m :: ms => cbcAux π (π m) ms

/-- The accumulator recurrence that replaces `acc` by `π acc + m` for each message block. -/
def chainAux (π : Block n → Block n) : Block n → List (Block n) → Block n
  | acc, [] => acc
  | acc, m :: ms => chainAux π (π acc + m) ms

/-- The chaining recurrence that starts with the first message block and returns zero on an
empty message. -/
def chain (π : Block n → Block n) : List (Block n) → Block n
  | [] => 0
  | m :: ms => chainAux π m ms

/-- Appending one block to the accumulator recurrence applies `π` to the previous accumulator
result plus that block. -/
lemma cbcAux_append (π : Block n → Block n) (acc : Block n)
    (xs : List (Block n)) (m : Block n) :
    cbcAux π acc (xs ++ [m]) = π (cbcAux π acc xs + m) := by
  induction xs generalizing acc with
  | nil => simp [cbcAux]
  | cons a as ih => simp [cbcAux, ih]

/-- Appending a block to a nonempty CBC message applies `π` to the previous tag plus the
appended block. -/
lemma cbc_append (π : Block n → Block n) (xs : List (Block n)) (hxs : xs ≠ [])
    (m : Block n) :
    cbc π (xs ++ [m]) = π (cbc π xs + m) := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons a as => simp [cbc, cbcAux_append]

/-- If the initial CBC accumulator is `π x`, the CBC accumulator result is `π` of the
corresponding `chainAux` result. -/
lemma cbcAux_eq_pi_chainAux (π : Block n → Block n) (as : List (Block n)) :
    ∀ (acc x : Block n), acc = π x →
      cbcAux π acc as = π (chainAux π x as) := by
  induction as with
  | nil => intro acc x h; simpa [cbcAux, chainAux] using h
  | cons m ms ih =>
      intro acc x h
      have h' : π (acc + m) = π (π x + m) := by rw [h]
      simp only [cbcAux, chainAux]
      exact ih (π (acc + m)) (π x + m) h'

/-- For a nonempty message, its CBC tag is `π` of its `chain` value. -/
lemma cbc_eq_pi_chain (π : Block n → Block n) (l : List (Block n)) (hl : l ≠ []) :
    cbc π l = π (chain π l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as =>
      simpa [cbc, chain] using cbcAux_eq_pi_chainAux π as (π a) a rfl

/-- The list of XORs of corresponding positive iterates of the two seeds, through iterate `k`. -/
def zblocks (π : Block n → Block n) (k : ℕ) (α β : Block n) : List (Block n) :=
  (List.range k).map (fun i => piter π (i + 1) α + piter π (i + 1) β)

/-- Increasing the length of `zblocks` appends the XOR of the next pair of iterates. -/
lemma zblocks_succ (π : Block n → Block n) (k : ℕ) (α β : Block n) :
    zblocks π (k + 1) α β =
      zblocks π k α β ++ [piter π (k + 1) α + piter π (k + 1) β] := by
  simp [zblocks, List.range_succ]

/-- Appending `zblocks` to a nonempty prefix with tag `π β` produces the `(k + 1)`-st iterate of
`α` when `k + 1` is even, and of `β` otherwise. -/
theorem cbc_prefix_zblocks (π : Block n → Block n) (pref : List (Block n))
    (hpref : pref ≠ []) (α β : Block n) (hβ : cbc π pref = π β) (k : ℕ) :
    cbc π (pref ++ zblocks π k α β) =
      if Even (k + 1) then piter π (k + 1) α else piter π (k + 1) β := by
  induction k with
  | zero =>
      have h1 : ¬ Even (0 + 1) := by simp
      rw [zblocks, List.range_zero, List.map_nil, List.append_nil, if_neg h1]
      simpa [piter] using hβ
  | succ k ih =>
      rw [zblocks_succ, ← List.append_assoc]
      have hne : pref ++ zblocks π k α β ≠ [] := by
        intro h
        exact hpref (List.append_eq_nil_iff.mp h).1
      rw [cbc_append π _ hne, ih]
      by_cases hk : Even (k + 1)
      · rw [if_pos hk]
        rw [if_neg (show ¬ Even (k + 1 + 1) by
          rw [Nat.even_add_one]
          exact not_not_intro hk)]
        rw [piter_succ_apply]
        congr 1
        rw [add_add_self_left]
      · rw [if_neg hk]
        rw [if_pos (show Even (k + 1 + 1) by
          rw [Nat.even_add_one]
          exact hk)]
        rw [piter_succ_apply]
        congr 1
        rw [add_add_self_right]

/-- The CBC tag of the singleton seed `α₁` followed by the constructed suffix alternates between
the `(k + 1)`-st iterates of `α₀` and `α₁` according to parity. -/
theorem cbc_tag_identity (π : Block n → Block n)
    (α₀ α₁ : Block n) (k : ℕ) :
    cbc π ([α₁] ++ zblocks π k α₀ α₁) =
      if Even (k + 1) then piter π (k + 1) α₀ else piter π (k + 1) α₁ := by
  have hne : ([α₁] : List (Block n)) ≠ [] := by simp
  have hβ : cbc π ([α₁] : List (Block n)) = π α₁ := by
    simp [cbc, cbcAux]
  exact cbc_prefix_zblocks π [α₁] hne α₀ α₁ hβ k

/-- Appending the suffix built from two chain values to the nonempty second message yields the
`(k + 1)`-st iterate of the first chain value for even `k + 1`, and of the second otherwise. -/
theorem cbc_prefix_tag_identity (π : Block n → Block n)
    (αBlocks βBlocks : List (Block n)) (hβne : βBlocks ≠ []) (k : ℕ) :
    cbc π (βBlocks ++ zblocks π k (chain π αBlocks) (chain π βBlocks)) =
      if Even (k + 1) then piter π (k + 1) (chain π αBlocks)
      else piter π (k + 1) (chain π βBlocks) := by
  have hβ : cbc π βBlocks = π (chain π βBlocks) := cbc_eq_pi_chain π βBlocks hβne
  exact cbc_prefix_zblocks π βBlocks hβne (chain π αBlocks) (chain π βBlocks) hβ k

/-- Every natural-number iterate of an injective block function is injective. -/
lemma piter_injective (π : Block n → Block n) (hπ : Function.Injective π) :
    ∀ j : ℕ, Function.Injective (piter π j)
  | 0 => fun _ _ h => h
  | j + 1 => by
      intro x y h
      have h' : piter π j x = piter π j y := hπ (by simpa [piter] using h)
      exact piter_injective π hπ j h'

/-- Corresponding iterates of distinct seeds under an injective block function have nonzero XOR. -/
lemma zblock_ne_zero (π : Block n → Block n) (hπ : Function.Injective π)
    (α β : Block n) (hαβ : α ≠ β) (j : ℕ) :
    piter π j α + piter π j β ≠ 0 := by
  intro h
  exact hαβ (piter_injective π hπ j (eq_of_add_eq_zero h))

/-- Every block in `zblocks` is nonzero when the block function is injective and the two seeds
are distinct. -/
lemma zblocks_all_ne_zero (π : Block n → Block n) (hπ : Function.Injective π)
    (α β : Block n) (hαβ : α ≠ β) (k : ℕ) :
    ∀ z ∈ zblocks π k α β, z ≠ 0 := by
  intro z hz
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hz
  exact zblock_ne_zero π hπ α β hαβ (i + 1)

/-- The shift that XORs a Boolean-and-block pair with the supplied Boolean-and-block offset. -/
def bxorShift (u s : Bool × Block n) : Bool × Block n :=
  (if s.1 then !u.1 else u.1, u.2 + s.2)

/-- The block function that selects a seed by a Boolean, iterates it `j` times, adds the input
block, and applies a further `m - j` iterates. -/
def gfun (π : Block n → Block n) (m j : ℕ) (α β : Block n)
    (u : Bool × Block n) : Block n :=
  piter π (m - j) (piter π j (if u.1 then β else α) + u.2)

/-- The repeated block `y` cancels in `y + (x + (p + y))`, leaving `p + x`. -/
lemma add_shift_cancel_aux₁ (x y p : Block n) : y + (x + (p + y)) = p + x := by
  have h : y + (x + (p + y)) = (y + y) + (x + p) := by abel
  rw [h, block_add_self, zero_add, add_comm x p]

/-- The repeated block `p` cancels in `p + (x + (p + q))`, leaving `q + x`. -/
lemma add_shift_cancel_aux₂ (x p q : Block n) : p + (x + (p + q)) = q + x := by
  have h : p + (x + (p + q)) = (p + p) + (x + q) := by abel
  rw [h, block_add_self, zero_add, add_comm x q]

/-- The function `gfun` is invariant under flipping its Boolean input and XORing its block input
with the sum of the `j`-th iterates of the two seeds. -/
theorem gfun_period (π : Block n → Block n) (m j : ℕ) (α β : Block n) :
    ∀ u : Bool × Block n,
      gfun π m j α β (bxorShift u (true, piter π j α + piter π j β)) =
        gfun π m j α β u := by
  intro u
  rcases u with ⟨b, x⟩
  cases b
  · simp only [gfun, bxorShift, if_true, if_false, Bool.not_false, Bool.false_eq_true]
    rw [add_shift_cancel_aux₁]
  · simp only [gfun, bxorShift, if_true, if_false, Bool.not_true, Bool.false_eq_true]
    rw [add_shift_cancel_aux₂]

end Qatlib.Concepts.CipherCircuits.ChainingTags
