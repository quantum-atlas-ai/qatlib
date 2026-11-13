/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Splitting a claw between ordered lists

The predicate `OrderedOn N` expresses monotonicity on the one-based interval `[1, N]`. The
predicates `FirstSubproblemClaw` and `SecondSubproblemClaw` combine a block of length at most
`r` in one list with a length-at-most-`r` window in the other, whose start is a least index
satisfying a threshold comparison.

For positive `r`, `split_lemma` says that two ordered lists contain a claw exactly when one of
these subproblems contains a claw. This is the finite-index formulation of Lemma 6 in
[BuhrmanEtAl2005]; `block_bounds` and the strict-inequality lemmas justify the block and
first-occurrence arguments.

This is a logical equivalence between finite-index witness predicates. It does
not construct search circuits or establish a query recurrence or complexity bound.

## Main statements

* `block_bounds`: each index in `[1, N]` lies in its quotient-indexed block, whose index is at
  most `(N - 1) / r`.
* `split_lemma`: a global claw exists if and only if a first-family or second-family subproblem
  has a claw.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option autoImplicit false

namespace Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw

/-- Require an integer-valued function on natural indices to be monotone on the one-based
interval `[1, N]`. -/
def OrderedOn (N : ℕ) (h : ℕ → ℤ) : Prop :=
  ∀ x y : ℕ, 1 ≤ x → x ≤ y → y ≤ N → h x ≤ h y

/-- Require `j` to be the least index in `[1, N]` with `f (i * r + 1) ≤ g j`, and require a claw
between the `i`th block of `f` and the length-`r` window of `g` starting at `j`, with both
windows truncated at `N`. -/
def FirstSubproblemClaw (N r : ℕ) (f g : ℕ → ℤ) (i j : ℕ) : Prop :=
  IsLeast {j' : ℕ | 1 ≤ j' ∧ j' ≤ N ∧ f (i * r + 1) ≤ g j'} j ∧
  ∃ x y : ℕ, i * r + 1 ≤ x ∧ x ≤ (i + 1) * r ∧ x ≤ N ∧
    j ≤ y ∧ y ≤ j + r - 1 ∧ y ≤ N ∧ f x = g y

/-- Require `i` to be the least index in `[1, N]` with `g (j * r + 1) ≤ f i`, and require a claw
between the length-`r` window of `f` starting at `i` and the `j`th block of `g`, with both
windows truncated at `N`. -/
def SecondSubproblemClaw (N r : ℕ) (f g : ℕ → ℤ) (j i : ℕ) : Prop :=
  IsLeast {i' : ℕ | 1 ≤ i' ∧ i' ≤ N ∧ g (j * r + 1) ≤ f i'} i ∧
  ∃ x y : ℕ, i ≤ x ∧ x ≤ i + r - 1 ∧ x ≤ N ∧
    j * r + 1 ≤ y ∧ y ≤ (j + 1) * r ∧ y ≤ N ∧ f x = g y

/-- If `b` is the first index in `[1, N]` taking the value `g b`, then monotonicity forces every
earlier index `y` in that interval to satisfy `g y < g b`. -/
theorem g_lt_of_lt_first {N : ℕ} {g : ℕ → ℤ} (hg : OrderedOn N g)
    {b y : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) (hy : 1 ≤ y) (hyb : y < b)
    (h : ∀ y', 1 ≤ y' → y' ≤ N → g y' = g b → b ≤ y') :
    g y < g b := by
  have hyN : y ≤ N := le_trans (le_of_lt hyb) hbN
  have hle : g y ≤ g b := hg y b hy (le_of_lt hyb) hbN
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (h y hy hyN heq) (by omega)

/-- If `a` is the first index in `[1, N]` taking the value `f a`, then monotonicity forces every
earlier index `x` in that interval to satisfy `f x < f a`. -/
theorem f_lt_of_lt_first {N : ℕ} {f : ℕ → ℤ} (hf : OrderedOn N f)
    {a x : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) (hx : 1 ≤ x) (hxa : x < a)
    (h : ∀ x', 1 ≤ x' → x' ≤ N → f x' = f a → a ≤ x') :
    f x < f a := by
  have hxN : x ≤ N := le_trans (le_of_lt hxa) haN
  have hle : f x ≤ f a := hf x a hx (le_of_lt hxa) haN
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (h x hx hxN heq) (by omega)

/-- For positive block length `r`, an index `a` in `[1, N]` lies in the block numbered `(a - 1)
/ r`, whose start is at most `N` and whose number is at most `(N - 1) / r`. This is the
block arithmetic used for Lemma 6 of [BuhrmanEtAl2005]. -/
theorem block_bounds {a N r : ℕ} (hr : 0 < r) (ha : 1 ≤ a) (haN : a ≤ N) :
    (a - 1) / r * r + 1 ≤ a ∧ a ≤ ((a - 1) / r + 1) * r ∧
    (a - 1) / r * r + 1 ≤ N ∧ (a - 1) / r ≤ (N - 1) / r := by
  set α := (a - 1) / r with hα
  have h1 : α * r ≤ a - 1 := Nat.div_mul_le_self (a - 1) r
  have h2 : a - 1 < (α + 1) * r := (Nat.div_lt_iff_lt_mul hr).mp (Nat.lt_succ_self α)
  have h3 : α ≤ (N - 1) / r := Nat.div_le_div_right (by omega)
  omega

/-- For functions monotone on `[1, N]` and positive `r`, a claw exists exactly when one of the
two families of block-and-window subproblems contains a claw. This is the indexed splitting
statement of Lemma 6 in [BuhrmanEtAl2005]. -/
theorem split_lemma (N r : ℕ) (hr : 0 < r) (f g : ℕ → ℤ)
    (hf : OrderedOn N f) (hg : OrderedOn N g) :
    (∃ x y : ℕ, 1 ≤ x ∧ x ≤ N ∧ 1 ≤ y ∧ y ≤ N ∧ f x = g y) ↔
      (∃ i j : ℕ, i ≤ (N - 1) / r ∧ FirstSubproblemClaw N r f g i j) ∨
      (∃ j i : ℕ, j ≤ (N - 1) / r ∧ SecondSubproblemClaw N r f g j i) := by
  constructor
  · rintro ⟨x0, y0, hx0, hx0N, hy0, hy0N, hxy0⟩

    set z : ℤ := f x0 with hz
    have hy0z : g y0 = z := by rw [← hxy0]

    have hexa : ∃ x, 1 ≤ x ∧ x ≤ N ∧ f x = z := ⟨x0, hx0, hx0N, rfl⟩
    set a := Nat.find hexa with ha_def
    have ha : 1 ≤ a ∧ a ≤ N ∧ f a = z := Nat.find_spec hexa
    have ha_min : ∀ x', 1 ≤ x' → x' ≤ N → f x' = z → a ≤ x' :=
      fun x' h1 h2 h3 => Nat.find_min' hexa ⟨h1, h2, h3⟩

    have hexb : ∃ y, 1 ≤ y ∧ y ≤ N ∧ g y = z := ⟨y0, hy0, hy0N, hy0z⟩
    set b := Nat.find hexb with hb_def
    have hb : 1 ≤ b ∧ b ≤ N ∧ g b = z := Nat.find_spec hexb
    have hb_min : ∀ y', 1 ≤ y' → y' ≤ N → g y' = z → b ≤ y' :=
      fun y' h1 h2 h3 => Nat.find_min' hexb ⟨h1, h2, h3⟩
    obtain ⟨ha1, haN, hafz⟩ := ha
    obtain ⟨hb1, hbN, hbgz⟩ := hb

    set α := (a - 1) / r with hα
    set β := (b - 1) / r with hβ
    obtain ⟨hα1, hα2, hαN, hαrange⟩ := block_bounds (a := a) (N := N) (r := r) hr ha1 haN
    obtain ⟨hβ1, hβ2, hβN, hβrange⟩ := block_bounds (a := b) (N := N) (r := r) hr hb1 hbN

    set v : ℤ := f (α * r + 1) with hv
    set w : ℤ := g (β * r + 1) with hw
    have hvz : v ≤ z :=
      (hf (α * r + 1) a (by omega) hα1 haN).trans_eq hafz
    have hwz : w ≤ z :=
      (hg (β * r + 1) b (by omega) hβ1 hbN).trans_eq hbgz

    have hexj : ∃ j, 1 ≤ j ∧ j ≤ N ∧ v ≤ g j := ⟨b, hb1, hbN, by rw [hbgz]; exact hvz⟩
    set j := Nat.find hexj with hj_def
    have hj : 1 ≤ j ∧ j ≤ N ∧ v ≤ g j := Nat.find_spec hexj
    have hj_min : ∀ j', 1 ≤ j' → j' ≤ N → v ≤ g j' → j ≤ j' :=
      fun j' h1 h2 h3 => Nat.find_min' hexj ⟨h1, h2, h3⟩
    have hjb : j ≤ b := hj_min b hb1 hbN (by rw [hbgz]; exact hvz)
    have hexi : ∃ i, 1 ≤ i ∧ i ≤ N ∧ w ≤ f i := ⟨a, ha1, haN, by rw [hafz]; exact hwz⟩
    set i := Nat.find hexi with hi_def
    have hi : 1 ≤ i ∧ i ≤ N ∧ w ≤ f i := Nat.find_spec hexi
    have hi_min : ∀ i', 1 ≤ i' → i' ≤ N → w ≤ f i' → i ≤ i' :=
      fun i' h1 h2 h3 => Nat.find_min' hexi ⟨h1, h2, h3⟩
    have hia : i ≤ a := hi_min a ha1 haN (by rw [hafz]; exact hwz)

    have first_of : (f (α * r + 1) ≤ g j) → (b ≤ j + r - 1) →
        FirstSubproblemClaw N r f g α j := by
      intro hvj hwin
      refine ⟨⟨⟨hj.1, hj.2.1, hvj⟩, fun j' hj' => hj_min j' hj'.1 hj'.2.1 hj'.2.2⟩, ?_⟩
      exact ⟨a, b, hα1, hα2, haN, hjb, hwin, hbN, by rw [hafz, hbgz]⟩

    have second_of : (g (β * r + 1) ≤ f i) → (a ≤ i + r - 1) →
        SecondSubproblemClaw N r f g β i := by
      intro hwi hwin
      refine ⟨⟨⟨hi.1, hi.2.1, hwi⟩, fun i' hi' => hi_min i' hi'.1 hi'.2.1 hi'.2.2⟩, ?_⟩
      exact ⟨a, b, hia, hwin, haN, hβ1, hβ2, hbN, by rw [hafz, hbgz]⟩

    by_cases hv_eq : v = z
    · have haeq : a = α * r + 1 := by
        have h1 : α * r + 1 ≤ a := hα1
        have h2 : a ≤ α * r + 1 := ha_min _ (by omega) hαN (by rw [← hv]; exact hv_eq)
        omega
      have hbj : b ≤ j := by
        by_contra hcon
        have hlt : j < b := Nat.lt_of_not_le hcon
        have hgle : g j ≤ z := (hg j b hj.1 (le_of_lt hlt) hbN).trans_eq hbgz
        have hzle : z ≤ g j := by rw [← hv_eq]; exact hj.2.2
        have hge : g j = z := le_antisymm hgle hzle
        exact absurd (hb_min j hj.1 hj.2.1 hge) (Nat.not_le.mpr hlt)
      have hjb_eq : j = b := le_antisymm hjb hbj
      have hvj : f (α * r + 1) ≤ g j := by rw [← hv]; exact hj.2.2
      refine Or.inl ⟨α, j, hαrange, first_of hvj ?_⟩
      rw [hjb_eq]
      omega
    · have hvlt : v < z := lt_of_le_of_ne hvz hv_eq

      by_cases hb_win : b ≤ j + r - 1
      · refine Or.inl ⟨α, j, hαrange, first_of hj.2.2 hb_win⟩
      · have hb_late : j + r ≤ b := by omega
        have hjβ : j ≤ β * r := by
          have h1 : j ≤ b - r := Nat.le_sub_of_add_le hb_late
          have h2 : b - r ≤ (β + 1) * r - r := Nat.sub_le_sub_right hβ2 r
          have h3 : (β + 1) * r - r = β * r := by
            rw [Nat.add_mul, one_mul, Nat.add_sub_cancel]
          exact le_trans h1 (h2.trans_eq h3)
        by_cases hw_eq : w = z
        · have hbeq : b = β * r + 1 := by
            have h2 : β * r + 1 ≤ b := hβ1
            have h3 : g (β * r + 1) = z := hw_eq
            have h4 : b ≤ β * r + 1 := hb_min _ (Nat.le_add_left 1 (β * r)) hβN h3
            exact le_antisymm h4 h2
          have hieq : i = a := by
            refine le_antisymm hia ?_
            by_contra hcon
            have hlt : i < a := Nat.lt_of_not_le hcon
            have hle : f i ≤ f a := hf i a hi.1 (le_of_lt hlt) haN
            have hge : z ≤ f i := by rw [← hw_eq]; exact hi.2.2
            have hfi : f i = z := le_antisymm (hle.trans_eq hafz) hge
            exact absurd (ha_min i hi.1 hi.2.1 hfi) (Nat.not_le.mpr hlt)
          refine Or.inr ⟨β, i, hβrange, ?_⟩
          have hwin : a ≤ i + r - 1 := by rw [hieq]; omega
          exact second_of (by rw [← hw]; exact hi.2.2) hwin
        · have hwlt : w < z := lt_of_le_of_ne hwz hw_eq
          by_cases ha_win : a ≤ i + r - 1
          · refine Or.inr ⟨β, i, hβrange, second_of (by rw [← hw]; exact hi.2.2) ha_win⟩
          · have ha_late : i + r ≤ a := by omega
            have hiα : i ≤ α * r := by
              have h1 : i ≤ a - r := Nat.le_sub_of_add_le ha_late
              have h2 : a - r ≤ (α + 1) * r - r := Nat.sub_le_sub_right hα2 r
              have h3 : (α + 1) * r - r = α * r := by
                rw [Nat.add_mul, one_mul, Nat.add_sub_cancel]
              exact le_trans h1 (h2.trans_eq h3)
            have hfi_le_v : f i ≤ v := by
              have hmono := hf i (α * r + 1) hi.1 (by omega) hαN
              simpa [hv] using hmono
            have hgj_le_w : g j ≤ w := by
              have hmono := hg j (β * r + 1) hj.1 (by omega) hβN
              simpa [hw] using hmono
            have hfw : f i = w := by
              have h1 : w ≤ f i := hi.2.2
              have h2 : v ≤ g j := hj.2.2
              omega

            refine Or.inr ⟨β, i, hβrange, ?_⟩
            have hwi : g (β * r + 1) ≤ f i := by rw [hfw]
            refine ⟨⟨⟨hi.1, hi.2.1, hwi⟩,
              fun i' hi' => hi_min i' hi'.1 hi'.2.1 hi'.2.2⟩, ?_⟩
            exact ⟨i, β * r + 1, le_rfl,
              Nat.le_sub_of_add_le (Nat.add_le_add_left (Nat.one_le_of_lt hr) i),
              hi.2.1, le_rfl,
              (by rw [Nat.add_mul, one_mul]; omega),
              hβN, by rw [hfw]⟩
  · rintro (⟨i, j, -, h⟩ | ⟨j, i, -, h⟩)
    · obtain ⟨jmem, x, y, h1, h2, h3, h4, h5, h6, heq⟩ := h
      exact ⟨x, y, le_trans (Nat.le_add_left 1 (i * r)) h1, h3, le_trans jmem.1.1 h4, h6, heq⟩
    · obtain ⟨imem, x, y, h1, h2, h3, h4, h5, h6, heq⟩ := h
      exact ⟨x, y, le_trans imem.1.1 h1, h3, le_trans (Nat.le_add_left 1 (j * r)) h4, h6, heq⟩

end Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw
