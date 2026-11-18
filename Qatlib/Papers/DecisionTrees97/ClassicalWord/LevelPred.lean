/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The Section III level-predicate classical algorithm

Fixed source quant-ph/9706062v2, Section III (the paragraph beginning "We can
think of decision trees as associated with functions that impose constraints"
and the adaptive classical algorithm attributed to M. Sipser).  For a hidden
word `w`, the level predicate `f_{n-1}` is `0` exactly when the first
(one-based) position where the queried word differs from `w` is odd.  The
source observes that a classical algorithm *different from the random walk*
recognizes the family: querying `f_{n-1}` on words whose known prefix agrees
with `w`, the informative answer at each position reveals the next word bit,
and two final evaluations of the last-level predicate `f_n` decide the tree
question.  This is why the separation concerns the specified random walk, not
all classical algorithms.

Words have length `k + r`, where `k` is the length of the already-identified
prefix and `r` the number of remaining positions.  This module proves:

* `identBit`: receiving the parity-flip answer `!b` at position `k` forces
  the queried bit to equal the corresponding hidden bit;
* `lvlAuxF_force`: an agreeing bit followed by a differing bit *always*
  produces the flipped answer — the concrete forcing event;
* `twoEval_iff`: under the source's promise that `f_n` is `true` only on
  extensions of `w`, two evaluations decide the question.

The general uniform-query success mass (at least a quarter of the correct-prefix
queries return the informative answer), the global adaptive process with its
expected-query budget `≤ 4(n-1) + 2`, and the uniform family indexing by `n`
are not formalized here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred

/-! ### The level predicate on bit strings -/

/-- Core recursion of the level predicate on `Fin m → Bool`: on the first
differing bit the current parity flag `b` is returned (the parity of the
one-based first mismatch position, toggled each step); coinciding words
return `true`. -/
def lvlAuxF : ∀ {m : ℕ}, Bool → (Fin m → Bool) → (Fin m → Bool) → Bool
  | 0, _, _, _ => true
  | m + 1, b, w, x =>
      if w ⟨0, by omega⟩ = x ⟨0, by omega⟩ then
        lvlAuxF (!b) (Fin.tail w) (Fin.tail x) else b

/-- The flag carried into (zero-based) position `k`: `true` iff `k` is odd,
so that a first mismatch at (one-based) position `k+1` answers `flagAt k`. -/
def flagAt (k : ℕ) : Bool := decide (k % 2 = 1)

/-- The suffix of a word of length `k + r` starting at `k`. -/
def suf (k r : ℕ) (f : Fin (k + r) → Bool) : Fin r → Bool :=
  fun i => f ⟨k + i.val, by have := i.isLt; omega⟩

/-- Unfolds one step of the horizontal level-predicate recursion. -/
theorem lvlAuxF_step {m : ℕ} (b : Bool) (w x : Fin (m + 1) → Bool) :
    lvlAuxF b w x =
      (if w ⟨0, by omega⟩ = x ⟨0, by omega⟩ then
        lvlAuxF (!b) (Fin.tail w) (Fin.tail x) else b) := rfl

/-- Reading the tail after a suffix advances the source position by one. -/
theorem tail_suf (k r : ℕ) (f : Fin (k + (r + 1)) → Bool) :
    Fin.tail (suf k (r + 1) f) =
      fun i => f ⟨k + 1 + i.val, by have := i.isLt; omega⟩ := by
  funext i
  have hsucc : i.succ.val = i.val + 1 := rfl
  have hi : i.val < r := i.isLt
  show suf k (r + 1) f i.succ = f ⟨k + 1 + i.val, by have := i.isLt; omega⟩
  apply congrArg f
  apply Fin.ext
  show k + i.succ.val = k + 1 + i.val
  omega

/-- A mismatched bit forces the predicate answer: if the words first differ
at (zero-based) position `k`, the predicate evaluated from `k` returns the
flag `b`, whatever the rest of the words. -/
theorem lvlMismatch (k r : ℕ) (b : Bool) (w x : Fin (k + (r + 1)) → Bool)
    (hdiff : w ⟨k, by omega⟩ ≠ x ⟨k, by omega⟩) :
    lvlAuxF b (suf k (r + 1) w) (suf k (r + 1) x) = b := by
  rw [lvlAuxF_step]
  split
  · exact absurd ‹_› (by simpa only [suf, Nat.add_zero] using hdiff)
  · rfl

/-- The identification step of the source's algorithm: receiving the
parity-flipped answer `!b` at (zero-based) position `k` certifies that the
queried bit equals the hidden bit — a mismatched bit would have returned
`b`. -/
theorem identBit (k r : ℕ) (b : Bool) (w x : Fin (k + (r + 1)) → Bool)
    (h : lvlAuxF b (suf k (r + 1) w) (suf k (r + 1) x) = !b) :
    w ⟨k, by omega⟩ = x ⟨k, by omega⟩ := by
  by_cases hd : w ⟨k, by omega⟩ = x ⟨k, by omega⟩
  · exact hd
  · rw [lvlMismatch k r b w x hd] at h
    cases b <;> simp at h

/-- Two-level forcing: an agreeing bit followed by a differing bit makes the
level predicate return the flipped flag `!b`, independently of the remaining
bits — the concrete event behind an informative answer. -/
theorem lvlAuxF_force (k r : ℕ) (b : Bool) (w x : Fin (k + (r + 2)) → Bool)
    (h0 : w ⟨k, by omega⟩ = x ⟨k, by omega⟩)
    (h1 : w ⟨k + 1, by omega⟩ ≠ x ⟨k + 1, by omega⟩) :
    lvlAuxF b (suf k (r + 2) w) (suf k (r + 2) x) = !b := by
  rw [lvlAuxF_step]
  split
  · rw [tail_suf, tail_suf, lvlAuxF_step]
    split
    · exact absurd ‹_› (by
        simp only [Nat.add_zero]
        exact h1)
    · rfl
  · exact absurd ‹_› (by
      simpa only [suf, Nat.add_zero] using not_not_intro h0)

/-! ### Uniform-query success mass -/

/-- Extends the hidden prefix `w` (its first `k` bits) by a free tail on the
remaining `r` positions. -/
def extend (k r : ℕ) (w : Fin (k + r) → Bool) (t : Fin r → Bool) :
    Fin (k + r) → Bool :=
  fun j =>
    if h : (j : ℕ) < k then w ⟨j, by omega⟩
    else t ⟨(j : ℕ) - k, by have := j.isLt; omega⟩

/-- Extending a prefix preserves every already identified bit. -/
theorem extend_lt (k r : ℕ) (w : Fin (k + r) → Bool) (t : Fin r → Bool)
    {j : Fin (k + r)} (hj : (j : ℕ) < k) :
    extend k r w t j = w ⟨j, by omega⟩ := by
  simp only [extend]
  split
  · rfl
  · exact absurd hj ‹_›

/-- At and beyond the prefix, extension reads the supplied tail. -/
theorem extend_ge (k r : ℕ) (w : Fin (k + r) → Bool) (t : Fin r → Bool)
    {j : Fin (k + r)} (hj : k ≤ (j : ℕ)) :
    extend k r w t j = t ⟨(j : ℕ) - k, by have := j.isLt; omega⟩ := by
  simp only [extend]
  split
  · exact absurd ‹_› (by
      show ¬((j : ℕ) < k)
      exact Nat.not_lt.mpr hj)
  · rfl

/-- Distinct free tails give distinct prefix-preserving query words. -/
theorem extend_inj (k r : ℕ) (w : Fin (k + r) → Bool) :
    Function.Injective (extend k r w) := by
  intro t t' heq
  funext i
  have hi : i.val < r := i.isLt
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin (k + r), idx.val = k + i.val :=
    ⟨⟨k + i.val, by omega⟩, rfl⟩
  have h1 := congrFun heq idx
  rw [extend_ge k r w t (by omega), extend_ge k r w t' (by omega)] at h1
  have hidx' : (⟨idx.val - k, by have := idx.isLt; omega⟩ : Fin r) = i := by
    apply Fin.ext
    show idx.val - k = i.val
    omega
  rw [hidx'] at h1
  simpa using h1

/-- Reading the suffix of an extended word recovers the supplied tail. -/
theorem suf_of_extend (k r : ℕ) (w : Fin (k + r) → Bool) (t : Fin r → Bool) :
    suf k r (extend k r w t) = t := by
  funext i
  have hi : i.val < r := i.isLt
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin (k + r), idx.val = k + i.val :=
    ⟨⟨k + i.val, by omega⟩, rfl⟩
  have hval : suf k r (extend k r w t) i = extend k r w t idx := by
    simp only [suf]
    exact congrArg (extend k r w t) (Fin.ext hidx.symm)
  rw [hval, extend_ge k r w t (by omega)]
  apply congrArg t
  apply Fin.ext
  show idx.val - k = i.val
  omega

/-- A word with the correct prefix is recovered from its free suffix. -/
theorem extend_suf (k r : ℕ) (w x : Fin (k + r) → Bool)
    (hagree : ∀ i : Fin (k + r), (i : ℕ) < k → x i = w i) :
    extend k r w (suf k r x) = x := by
  funext j
  have hj : j.val < k + r := j.isLt
  rcases Nat.lt_or_ge (j : ℕ) k with hlt | hge
  · rw [extend_lt k r w _ hlt, hagree j hlt]
  · rw [extend_ge k r w _ hge, suf]
    apply congrArg x
    apply Fin.ext
    show k + ((j : ℕ) - k) = j.val
    omega

/-- The queries whose first `k` bits agree with the hidden word `w` — the
query space once the prefix `w₁…w_k` has been identified. -/
def prefixFixed (k r : ℕ) (w : Fin (k + r) → Bool) :
    Finset (Fin (k + r) → Bool) :=
  Finset.univ.filter fun x => ∀ i : Fin (k + r), (i : ℕ) < k → x i = w i

/-- Membership in the query set means agreement on the known prefix. -/
theorem mem_prefixFixed {k r : ℕ} {w x : Fin (k + r) → Bool} :
    x ∈ prefixFixed k r w ↔ ∀ i : Fin (k + r), (i : ℕ) < k → x i = w i := by
  simp only [prefixFixed, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The informative queries: the prefix is correct and the level predicate,
evaluated from position `k`, returns the flipped flag; by `identBit` the
answer then identifies bit `k` of `w`. -/
def informativeSet (k r : ℕ) (w : Fin (k + r) → Bool) :
    Finset (Fin (k + r) → Bool) :=
  (prefixFixed k r w).filter fun x =>
    lvlAuxF (flagAt k) (suf k r w) (suf k r x) = !(flagAt k)

/-- Every tail extension is a valid query with the known prefix. -/
theorem extend_mem (k r : ℕ) (w : Fin (k + r) → Bool)
    (t : Fin r → Bool) :
    extend k r w t ∈ prefixFixed k r w := by
  rw [mem_prefixFixed]
  intro i hi
  exact extend_lt k r w t hi

/-! ### The two-evaluation endpoint -/

/-- The two-evaluation endpoint under the source's one-hot promise for the
final predicate `f_n`: if `f_n` can be `true` only on inputs whose first
`m` bits extend `w`, then two evaluations — at `w` followed by `false` and
by `true` — decide whether the tree has a level-`n` node.  (The last bit is
encoded as an explicit `Bool` component.) -/
theorem twoEval_iff (m : ℕ) (w : Fin m → Bool)
    (fn : ((Fin m → Bool) × Bool) → Bool)
    (hpromise : ∀ p : (Fin m → Bool) × Bool, fn p = true →
      ∀ i : Fin m, p.1 ⟨i.val, by omega⟩ = w i) :
    (∃ p, fn p = true) ↔
      fn (w, false) = true ∨ fn (w, true) = true := by
  constructor
  · rintro ⟨⟨x, bl⟩, hx⟩
    have hxw : x = w := by
      funext i
      exact hpromise (x, bl) hx i
    rw [hxw] at hx
    rcases bl with _ | _
    · exact Or.inl hx
    · exact Or.inr hx
  · intro h
    rcases h with h | h
    · exact ⟨(w, false), h⟩
    · exact ⟨(w, true), h⟩

end Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred
