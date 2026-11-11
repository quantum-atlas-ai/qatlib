/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.FibonacciStrings

/-!
# Finite Zeckendorf encoding of Fibonacci strings

`fibStringValue` gives a bijection from length-m Boolean strings with no adjacent true entries
to natural numbers below `Nat.fib (m + 2)`. The equivalence `zeckendorfEquiv` packages this
encoding and yields the exact cardinality of `FibString m`. See [ShorJordan2008].

## Main statements

* `zeckendorfEquiv`: The equivalence between length-m Fibonacci strings and natural numbers
  below `Nat.fib (m + 2)` induced by their weighted values.
* `fibString_card`: There are exactly `Nat.fib (m + 2)` Fibonacci strings of length m.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Zeckendorf

open Definitions

/-- The conjunction of the Fibonacci-value range bound, injectivity on length-m lists with no
adjacent true entries, and representation of every value below `Nat.fib (m + 2)`. -/
private def Good (m : ℕ) : Prop :=
  (∀ l : List Bool, l.length = m → NoAdjList l → zList l < Nat.fib (m + 2)) ∧
  (∀ l₁ l₂ : List Bool, l₁.length = m → l₂.length = m →
      NoAdjList l₁ → NoAdjList l₂ → zList l₁ = zList l₂ → l₁ = l₂) ∧
  (∀ v : ℕ, v < Nat.fib (m + 2) → ∃ l : List Bool, l.length = m ∧ NoAdjList l ∧ zList l = v)

/-- The third Fibonacci number is two. -/
lemma fib_three : Nat.fib 3 = 2 := by
  have := Nat.fib_add_two (n := 1); simpa using this

/-- For every length m, Fibonacci-weighted lists with no adjacent true entries satisfy the
range, uniqueness, and existence properties collected in `Good m`. -/
private theorem good : ∀ m, Good m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 =>
      refine ⟨?_, ?_, ?_⟩
      · intro l hl _
        rw [List.length_eq_zero_iff.mp hl]
        simp [zList]
      · intro l₁ l₂ h₁ h₂ _ _ _
        rw [List.length_eq_zero_iff.mp h₁, List.length_eq_zero_iff.mp h₂]
      · intro v hv
        have hv1 : v < 1 := by simpa using hv
        have hv0 : v = 0 := by omega
        subst hv0
        exact ⟨[], rfl, by simp [NoAdjList], rfl⟩
    | 1 =>
      refine ⟨?_, ?_, ?_⟩
      · intro l hl _
        obtain ⟨x, rfl⟩ : ∃ x, l = [x] := by
          match l with
          | [] => simp at hl
          | [x] => exact ⟨x, rfl⟩
          | a :: b :: t => simp at hl
        have hg : Nat.fib ((1 : ℕ) + 2) = 2 := by simpa using fib_three
        cases x with
        | false => decide
        | true => decide
      · intro l₁ l₂ h₁ h₂ _ _ hz
        obtain ⟨b₁, rfl⟩ : ∃ b₁, l₁ = [b₁] := by
          match l₁ with
          | [] => simp at h₁
          | [x] => exact ⟨x, rfl⟩
          | a :: b :: t => simp at h₁
        obtain ⟨b₂, rfl⟩ : ∃ b₂, l₂ = [b₂] := by
          match l₂ with
          | [] => simp at h₂
          | [x] => exact ⟨x, rfl⟩
          | a :: b :: t => simp at h₂
        cases b₁ <;> cases b₂ <;> simp_all [zList]
      · intro v hv
        have hv2 : v < 2 := by simpa [fib_three] using hv
        interval_cases v
        · exact ⟨[false], rfl, by simp [NoAdjList], by simp [zList]⟩
        · exact ⟨[true], rfl, by simp [NoAdjList], by simp [zList]⟩
    | k + 2 =>
      have ihk : Good k := ih k (by omega)
      have ihk1 : Good (k + 1) := ih (k + 1) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro l hl hno
        match l with
        | [] => simp at hl
        | [x] => simp at hl
        | a :: b :: t =>
          have htk : t.length = k := by simp at hl; omega
          cases a with
          | false =>
            have hrest : zList (b :: t) < Nat.fib ((k + 1) + 2) :=
              ihk1.1 (b :: t) (by simp [htk]) (NoAdjList.of_false_cons hno)
            rw [zList_false_cons]
            calc zList (b :: t) < Nat.fib ((k + 1) + 2) := hrest
              _ ≤ Nat.fib ((k + 2) + 2) := Nat.fib_mono (by omega)
          | true =>
            cases b with
            | true =>
              exfalso
              have h1 := hno
              simp only [NoAdjList] at h1
              exact h1.1 ⟨trivial, trivial⟩
            | false =>
              have htno : NoAdjList t := NoAdjList.of_true_false_cons hno
              have hrest : zList t < Nat.fib (k + 2) := ihk.1 t htk htno
              have hlen : (false :: t).length + 2 = (k + 2) + 1 := by simp [htk]
              have hfib : Nat.fib ((k + 2) + 2) = Nat.fib ((k + 2) + 1) + Nat.fib (k + 2) := by
                rw [Nat.fib_add_two (n := k + 2), Nat.add_comm]
              rw [zList_true_cons, hlen, zList_false_cons, hfib]
              exact Nat.add_lt_add_left hrest _
      · intro l₁ l₂ h₁ h₂ hn₁ hn₂ hz
        match l₁, l₂ with
        | [], _ => simp at h₁
        | _ :: _, [] => simp at h₂
        | [x], _ :: _ :: _ => simp at h₁
        | _ :: _ :: _, [y] => simp at h₂
        | a₁ :: b₁ :: t₁, a₂ :: b₂ :: t₂ =>
          have ht₁ : t₁.length = k := by simp at h₁; omega
          have ht₂ : t₂.length = k := by simp at h₂; omega
          cases a₁ with
          | false =>
            have hb₁ : zList (b₁ :: t₁) < Nat.fib ((k + 1) + 2) :=
              ihk1.1 (b₁ :: t₁) (by simp [ht₁]) (NoAdjList.of_false_cons hn₁)
            cases a₂ with
            | false =>
              have hzr : zList (b₁ :: t₁) = zList (b₂ :: t₂) := by
                rw [zList_false_cons, zList_false_cons] at hz; exact hz
              have heq : b₁ :: t₁ = b₂ :: t₂ :=
                ihk1.2.1 (b₁ :: t₁) (b₂ :: t₂) (by simp [ht₁]) (by simp [ht₂])
                  (NoAdjList.of_false_cons hn₁) (NoAdjList.of_false_cons hn₂) hzr
              rw [heq]
            | true =>
              cases b₂ with
              | true =>
                exfalso
                have h2 := hn₂
                simp only [NoAdjList] at h2
                exact h2.1 ⟨trivial, trivial⟩
              | false =>
                have hz1 : zList (false :: b₁ :: t₁) = zList (b₁ :: t₁) := by rw [zList_false_cons]
                have hz2 : zList (true :: false :: t₂) =
                    Nat.fib ((false :: t₂).length + 2) + zList t₂ := by
                  rw [zList_true_cons, zList_false_cons]
                have hz' : zList (b₁ :: t₁) =
                    Nat.fib ((false :: t₂).length + 2) + zList t₂ := by
                  rw [← hz1, ← hz2]; exact hz
                have hb₁' : zList (b₁ :: t₁) < Nat.fib ((false :: t₂).length + 2) := by
                  rw [show (false :: t₂).length + 2 = (b₁ :: t₁).length + 2 by simp [ht₁, ht₂],
                    show (b₁ :: t₁).length + 2 = (k + 1) + 2 by simp [ht₁]]
                  exact hb₁
                omega
          | true =>
            cases b₁ with
            | true =>
              exfalso
              have h2 := hn₁
              simp only [NoAdjList] at h2
              exact h2.1 ⟨trivial, trivial⟩
            | false =>
              cases a₂ with
              | false =>
                have hz1 : zList (false :: b₂ :: t₂) = zList (b₂ :: t₂) := by rw [zList_false_cons]
                have hz2 : zList (true :: false :: t₁) =
                    Nat.fib ((false :: t₁).length + 2) + zList t₁ := by
                  rw [zList_true_cons, zList_false_cons]
                have hz' : zList (b₂ :: t₂) =
                    Nat.fib ((false :: t₁).length + 2) + zList t₁ := by
                  rw [← hz1, ← hz2]; exact hz.symm
                have hb₂ : zList (b₂ :: t₂) < Nat.fib ((k + 1) + 2) :=
                  ihk1.1 (b₂ :: t₂) (by simp [ht₂]) (NoAdjList.of_false_cons hn₂)
                have hb₂' : zList (b₂ :: t₂) < Nat.fib ((false :: t₁).length + 2) := by
                  rw [show (false :: t₁).length + 2 = (b₂ :: t₂).length + 2 by simp [ht₁, ht₂],
                    show (b₂ :: t₂).length + 2 = (k + 1) + 2 by simp [ht₂]]
                  exact hb₂
                omega
              | true =>
                cases b₂ with
                | true =>
                  exfalso
                  have h2 := hn₂
                  simp only [NoAdjList] at h2
                  exact h2.1 ⟨trivial, trivial⟩
                | false =>
                  have hn₁t : NoAdjList t₁ := NoAdjList.of_true_false_cons hn₁
                  have hn₂t : NoAdjList t₂ := NoAdjList.of_true_false_cons hn₂
                  have hzr : zList t₁ = zList t₂ := by
                    rw [zList_true_cons, zList_true_cons, zList_false_cons, zList_false_cons] at hz
                    have h1 : (false :: t₁).length + 2 = (k + 2) + 1 := by simp [ht₁]
                    have h2 : (false :: t₂).length + 2 = (k + 2) + 1 := by simp [ht₂]
                    rw [h1, h2] at hz
                    exact Nat.add_left_cancel hz
                  have heq : t₁ = t₂ := ihk.2.1 t₁ t₂ ht₁ ht₂ hn₁t hn₂t hzr
                  rw [heq]
      · intro v hv
        have hfib : Nat.fib ((k + 2) + 2) = Nat.fib ((k + 2) + 1) + Nat.fib (k + 2) := by
          rw [Nat.fib_add_two (n := k + 2), Nat.add_comm]
        by_cases hlt : v < Nat.fib ((k + 2) + 1)
        · obtain ⟨l', hl', hno', hz'⟩ :=
            ihk1.2.2 v (by rwa [show (k + 1) + 2 = (k + 2) + 1 by omega])
          refine ⟨false :: l', ?_, NoAdjList.of_cons_false hno', ?_⟩
          · simp [hl']
          · rw [zList_false_cons]; exact hz'
        · have hle : Nat.fib ((k + 2) + 1) ≤ v := by omega
          have hvlt : v < Nat.fib ((k + 2) + 1) + Nat.fib (k + 2) := by rw [← hfib]; exact hv
          have hv' : v - Nat.fib ((k + 2) + 1) < Nat.fib (k + 2) := by omega
          obtain ⟨t, ht, hno, hz⟩ := ihk.2.2 (v - Nat.fib ((k + 2) + 1)) hv'
          refine ⟨true :: false :: t, ?_, NoAdjList.of_cons_true_false hno, ?_⟩
          · simp [ht]
          · rw [zList_true_cons]
            have hlen : (false :: t).length + 2 = (k + 2) + 1 := by simp [ht]
            rw [hlen, zList_false_cons, hz]
            exact Nat.add_sub_of_le hle

/-- The value of a length-m Fibonacci string is less than `Nat.fib (m + 2)`. -/
theorem fibStringValue_lt (m : ℕ) (s : FibString m) : fibStringValue s < Nat.fib (m + 2) :=
  (good m).1 s.1 s.2.1 s.2.2

/-- The Fibonacci-value map from `FibString m` to `Fin (Nat.fib (m + 2))` is bijective; see
[ShorJordan2008]. -/
theorem fibStringValue_bijective (m : ℕ) :
    Function.Bijective
      (fun s : FibString m => (⟨fibStringValue s, fibStringValue_lt m s⟩ : Fin (Nat.fib (m + 2)))) := by
  constructor
  · intro s₁ s₂ h
    apply Subtype.ext
    have hz : zList s₁.1 = zList s₂.1 := by
      have := congrArg Fin.val h
      simpa [fibStringValue] using this
    exact (good m).2.1 s₁.1 s₂.1 s₁.2.1 s₂.2.1 s₁.2.2 s₂.2.2 hz
  · intro v
    obtain ⟨l, hl, hno, hz⟩ := (good m).2.2 v.val v.2
    refine ⟨⟨l, hl, hno⟩, ?_⟩
    apply Fin.ext
    simp [fibStringValue, hz]

/-- The equivalence between length-m Fibonacci strings and natural numbers below `Nat.fib (m +
2)` induced by their weighted values; see [ShorJordan2008]. -/
noncomputable def zeckendorfEquiv (m : ℕ) : FibString m ≃ Fin (Nat.fib (m + 2)) :=
  Equiv.ofBijective _ (fibStringValue_bijective m)

noncomputable instance fibStringFintype (m : ℕ) : Fintype (FibString m) :=
  Fintype.ofEquiv (Fin (Nat.fib (m + 2))) (zeckendorfEquiv m).symm

/-- There are exactly `Nat.fib (m + 2)` Fibonacci strings of length m; see [ShorJordan2008]. -/
theorem fibString_card (m : ℕ) : Fintype.card (FibString m) = Nat.fib (m + 2) := by
  rw [Fintype.card_congr (zeckendorfEquiv m), Fintype.card_fin]

/-- The Fibonacci-value encoding of length-n Fibonacci strings is a bijection onto `Fin (Nat.fib
(n + 2))`; see [ShorJordan2008]. -/
theorem prop4_zeckendorf (n : ℕ) :
    Function.Bijective
      (fun s : FibString n => (⟨fibStringValue s, fibStringValue_lt n s⟩ : Fin (Nat.fib (n + 2)))) :=
  fibStringValue_bijective n

end Qatlib.Papers.JonesPolyShor07.MainResults.Zeckendorf
