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

set_option autoImplicit false

namespace Qatlib.Concepts.CipherCircuits.ChainingTags

abbrev Block (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

lemma block_add_self (x : Block n) : x + x = 0 := by
  calc x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp
    _ = ((1 : ZMod 2) + 1) • x := (add_smul (1 : ZMod 2) (1 : ZMod 2) x).symm
    _ = 0 := by
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h2, zero_smul]

lemma block_add_self_add (x y : Block n) : x + y + y = x := by
  rw [add_assoc, block_add_self, add_zero]

lemma block_add_add_self (x y : Block n) : x + y + x = y := by
  rw [add_comm (x + y) x, ← add_assoc, block_add_self, zero_add]

lemma add_add_self_left (x y : Block n) : x + (x + y) = y := by
  rw [← add_assoc, block_add_self, zero_add]

lemma add_add_self_right (x y : Block n) : x + (y + x) = y := by
  rw [← add_assoc]
  exact block_add_add_self x y

lemma eq_of_add_eq_zero {x y : Block n} (h : x + y = 0) : x = y := by
  have h1 : x + (y + y) = x := by rw [block_add_self, add_zero]
  calc x = x + (y + y) := h1.symm
    _ = (x + y) + y := (add_assoc x y y).symm
    _ = 0 + y := by rw [h]
    _ = y := zero_add y

def piter (π : Block n → Block n) : ℕ → Block n → Block n
  | 0 => id
  | k + 1 => π ∘ piter π k

@[simp] lemma piter_zero (π : Block n → Block n) : piter π 0 = id := rfl

@[simp] lemma piter_succ (π : Block n → Block n) (k : ℕ) :
    piter π (k + 1) = π ∘ piter π k := rfl

lemma piter_succ_apply (π : Block n → Block n) (k : ℕ) (x : Block n) :
    piter π (k + 1) x = π (piter π k x) := rfl

def cbcAux (π : Block n → Block n) : Block n → List (Block n) → Block n
  | acc, [] => acc
  | acc, m :: ms => cbcAux π (π (acc + m)) ms

def cbc (π : Block n → Block n) : List (Block n) → Block n
  | [] => 0
  | m :: ms => cbcAux π (π m) ms

def chainAux (π : Block n → Block n) : Block n → List (Block n) → Block n
  | acc, [] => acc
  | acc, m :: ms => chainAux π (π acc + m) ms

def chain (π : Block n → Block n) : List (Block n) → Block n
  | [] => 0
  | m :: ms => chainAux π m ms

lemma cbcAux_append (π : Block n → Block n) (acc : Block n)
    (xs : List (Block n)) (m : Block n) :
    cbcAux π acc (xs ++ [m]) = π (cbcAux π acc xs + m) := by
  induction xs generalizing acc with
  | nil => simp [cbcAux]
  | cons a as ih => simp [cbcAux, ih]

lemma cbc_append (π : Block n → Block n) (xs : List (Block n)) (hxs : xs ≠ [])
    (m : Block n) :
    cbc π (xs ++ [m]) = π (cbc π xs + m) := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons a as => simp [cbc, cbcAux_append]

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

lemma cbc_eq_pi_chain (π : Block n → Block n) (l : List (Block n)) (hl : l ≠ []) :
    cbc π l = π (chain π l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as =>
      simpa [cbc, chain] using cbcAux_eq_pi_chainAux π as (π a) a rfl

def zblocks (π : Block n → Block n) (k : ℕ) (α β : Block n) : List (Block n) :=
  (List.range k).map (fun i => piter π (i + 1) α + piter π (i + 1) β)

lemma zblocks_succ (π : Block n → Block n) (k : ℕ) (α β : Block n) :
    zblocks π (k + 1) α β =
      zblocks π k α β ++ [piter π (k + 1) α + piter π (k + 1) β] := by
  simp [zblocks, List.range_succ]

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

theorem cbc_tag_identity (π : Block n → Block n)
    (α₀ α₁ : Block n) (k : ℕ) :
    cbc π ([α₁] ++ zblocks π k α₀ α₁) =
      if Even (k + 1) then piter π (k + 1) α₀ else piter π (k + 1) α₁ := by
  have hne : ([α₁] : List (Block n)) ≠ [] := by simp
  have hβ : cbc π ([α₁] : List (Block n)) = π α₁ := by
    simp [cbc, cbcAux]
  exact cbc_prefix_zblocks π [α₁] hne α₀ α₁ hβ k

theorem cbc_prefix_tag_identity (π : Block n → Block n)
    (αBlocks βBlocks : List (Block n)) (hβne : βBlocks ≠ []) (k : ℕ) :
    cbc π (βBlocks ++ zblocks π k (chain π αBlocks) (chain π βBlocks)) =
      if Even (k + 1) then piter π (k + 1) (chain π αBlocks)
      else piter π (k + 1) (chain π βBlocks) := by
  have hβ : cbc π βBlocks = π (chain π βBlocks) := cbc_eq_pi_chain π βBlocks hβne
  exact cbc_prefix_zblocks π βBlocks hβne (chain π αBlocks) (chain π βBlocks) hβ k

lemma piter_injective (π : Block n → Block n) (hπ : Function.Injective π) :
    ∀ j : ℕ, Function.Injective (piter π j)
  | 0 => fun _ _ h => h
  | j + 1 => by
      intro x y h
      have h' : piter π j x = piter π j y := hπ (by simpa [piter] using h)
      exact piter_injective π hπ j h'

lemma zblock_ne_zero (π : Block n → Block n) (hπ : Function.Injective π)
    (α β : Block n) (hαβ : α ≠ β) (j : ℕ) :
    piter π j α + piter π j β ≠ 0 := by
  intro h
  exact hαβ (piter_injective π hπ j (eq_of_add_eq_zero h))

lemma zblocks_all_ne_zero (π : Block n → Block n) (hπ : Function.Injective π)
    (α β : Block n) (hαβ : α ≠ β) (k : ℕ) :
    ∀ z ∈ zblocks π k α β, z ≠ 0 := by
  intro z hz
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hz
  exact zblock_ne_zero π hπ α β hαβ (i + 1)

def bxorShift (u s : Bool × Block n) : Bool × Block n :=
  (if s.1 then !u.1 else u.1, u.2 + s.2)

def gfun (π : Block n → Block n) (m j : ℕ) (α β : Block n)
    (u : Bool × Block n) : Block n :=
  piter π (m - j) (piter π j (if u.1 then β else α) + u.2)

lemma add_shift_cancel_aux₁ (x y p : Block n) : y + (x + (p + y)) = p + x := by
  have h : y + (x + (p + y)) = (y + y) + (x + p) := by abel
  rw [h, block_add_self, zero_add, add_comm x p]

lemma add_shift_cancel_aux₂ (x p q : Block n) : p + (x + (p + q)) = q + x := by
  have h : p + (x + (p + q)) = (p + p) + (x + q) := by abel
  rw [h, block_add_self, zero_add, add_comm x q]

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
