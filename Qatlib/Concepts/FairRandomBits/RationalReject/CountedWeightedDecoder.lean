/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# Weighted interval decoding with comparison counts

`weightDecodeCounted` scans natural-number weights in label order, returning the bucket
containing a ticket and the number of comparisons performed. The accompanying
`weightTotalCounted` computes the total weight while counting its additions.

The module identifies every decoding interval, proves its fiber cardinality, and establishes
exact costs on both success and rejection. These finite counting constructions support the
classical randomized computation framework in [KitaevShenVyalyi2002].

## Main statements

* `weightDecodeCounted_some_iff`: a label is returned precisely on its half-open prefix
  interval.
* `weightDecodeCounted_fibers`: each label has as many valid tickets as its weight.
* `weighted_decoder_intervals_and_actual_cost`: the decoder satisfies the interval, fiber, and
  work-count specifications together.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

namespace Qatlib.Concepts.FairRandomBits.RationalReject

open scoped ENNReal Classical

section ScanHelpers

variable {N : ℕ}

/-- The sum of the natural-number weights in a list of label-weight pairs. -/
private def pairSum : List (Fin N × ℕ) → ℕ
  | [] => 0
  | (_, w) :: t => w + pairSum t

/-- The total weight of an empty pair list is zero. -/
@[simp] private theorem pairSum_nil : pairSum ([] : List (Fin N × ℕ)) = 0 := rfl

/-- Prepending a pair adds its weight to the total weight of the remaining list. -/
@[simp] private theorem pairSum_cons (e : Fin N × ℕ) (t : List (Fin N × ℕ)) :
    pairSum (e :: t) = e.2 + pairSum t := rfl

/-- The total weight of concatenated pair lists is the sum of their total weights. -/
private theorem pairSum_append (l₁ l₂ : List (Fin N × ℕ)) :
    pairSum (l₁ ++ l₂) = pairSum l₁ + pairSum l₂ := by
  induction l₁ with
  | nil => simp
  | cons e l ih =>
      show e.2 + pairSum (l ++ l₂) = (e.2 + pairSum l) + pairSum l₂
      rw [ih]
      omega

/-- Splitting a pair list into its first `k` entries and its remaining entries preserves the sum
of weights. -/
private theorem pairSum_split (l : List (Fin N × ℕ)) (k : ℕ) (_hk : k ≤ l.length) :
    pairSum l = pairSum (l.take k) + pairSum (l.drop k) :=
  calc pairSum l = pairSum (l.take k ++ l.drop k) := by rw [List.take_append_drop]
    _ = pairSum (l.take k) + pairSum (l.drop k) := pairSum_append _ _

/-- The total weight of a prefix is at most the total weight of the full list. -/
private theorem pairSum_take_le (l : List (Fin N × ℕ)) (m : ℕ) (hm : m ≤ l.length) :
    pairSum (l.take m) ≤ pairSum l := by
  have h := pairSum_split l m hm
  omega

/-- Extending a prefix by one entry increases its total weight by that entry's weight. -/
private theorem pairSum_take_succ (l : List (Fin N × ℕ)) (k : ℕ) (hk : k < l.length) :
    pairSum (l.take (k + 1)) = pairSum (l.take k) + l[k].2 := by
  have h1 : l.take (k + 1) = l.take k ++ [l[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    simp
  rw [h1, pairSum_append, pairSum_cons, pairSum_nil, add_zero]

/-- Prepending one pair increases the list length by one. -/
private theorem length_cons (e : Fin N × ℕ) (t : List (Fin N × ℕ)) :
    (e :: t).length = t.length + 1 := by simp

/-- Equality of the optional output and both natural-number components implies equality of the
corresponding triples. -/
private theorem triple_congr {α : Type} {o₁ o₂ : Option α} {a₁ a₂ b₁ b₂ : ℕ}
    (h₁ : o₁ = o₂) (h₂ : a₁ = a₂) (h₃ : b₁ = b₂) : (o₁, a₁, b₁) = (o₂, a₂, b₂) := by
  subst h₁
  simp only [h₂, h₃]

/-- Indexing a list constructed by `List.ofFn` recovers the corresponding function value. -/
private theorem ofFn_getElem {M : ℕ} {α : Type} (f : Fin M → α) (k : ℕ) (hk : k < M) :
    (List.ofFn f)[k]'(by rw [List.length_ofFn]; exact hk) = f ⟨k, hk⟩ := by
  exact List.getElem_ofFn (i := k) (by rw [List.length_ofFn]; exact hk)

/-- Scan weighted labels until the ticket lies below a cumulative upper bound, recording the
bound and comparison count. -/
private def weightScan : List (Fin N × ℕ) → ℕ → ℕ → ℕ → Option (Fin N) × ℕ × ℕ
  | [], k, acc, _ => (none, acc, k)
  | e :: t, k, acc, u =>
      let upper := acc + e.2
      if u < upper then (some e.1, upper, k + 1)
      else weightScan t (k + 1) upper u

/-- A nonempty list's prefix of length `q + 1` is its head followed by the tail's prefix of
length `q`. -/
private theorem cons_take_succ (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (q : ℕ) :
    (e :: t).take (q + 1) = [e] ++ t.take q := by
  have h1 : (e :: t).take 1 = [e] := by simp
  have h2 : (e :: t).drop 1 = t := rfl
  rw [show q + 1 = 1 + q by omega, List.take_add, h1, h2]

/-- A stopping inequality for a cons-list prefix implies the corresponding inequality with the
head weight added to the accumulator. -/
private theorem cons_stop (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (q acc u : ℕ)
    (h : u < acc + pairSum ((e :: t).take (q + 1))) :
    u < acc + e.2 + pairSum (t.take q) := by
  rw [cons_take_succ e t q, pairSum_append, pairSum_cons, pairSum_nil, add_zero] at h
  rw [← Nat.add_assoc] at h
  exact h

/-- Failure of a cons-list prefix stopping inequality implies failure of the corresponding
inequality with the head weight absorbed into the accumulator. -/
private theorem cons_stop'' (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (q acc u : ℕ)
    (h : ¬ (u < acc + pairSum ((e :: t).take (q + 1)))) :
    ¬ (u < acc + e.2 + pairSum (t.take q)) := by
  rw [cons_take_succ e t q, pairSum_append, pairSum_cons, pairSum_nil, add_zero] at h
  rw [← Nat.add_assoc] at h
  exact h

/-- A stopping inequality with the head weight absorbed into the accumulator gives the
corresponding cons-list prefix inequality. -/
private theorem cons_stop_lift (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (q acc u : ℕ)
    (h : u < acc + e.2 + pairSum (t.take q)) :
    u < acc + pairSum ((e :: t).take (q + 1)) := by
  rw [cons_take_succ e t q, pairSum_append, pairSum_cons, pairSum_nil, add_zero,
    ← Nat.add_assoc]
  exact h

/-- Failure of a stopping inequality with the head weight absorbed into the accumulator gives
failure of the corresponding cons-list prefix inequality. -/
private theorem cons_stop' (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (q acc u : ℕ)
    (h : ¬ (u < acc + e.2 + pairSum (t.take q))) :
    ¬ (u < acc + pairSum ((e :: t).take (q + 1))) := by
  rw [cons_take_succ e t q, pairSum_append, pairSum_cons, pairSum_nil, add_zero]
  intro hc
  exact h (by rw [Nat.add_assoc]; exact hc)

/-- The head's stopping inequality implies the stopping inequality for the prefix of length one. -/
private theorem cons_stop_head (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (acc u : ℕ)
    (h : u < acc + e.2) : u < acc + pairSum ((e :: t).take 1) := by
  rw [cons_take_succ e t 0, pairSum_append, pairSum_cons, pairSum_nil, add_zero]
  exact h

/-- Failure of the head's stopping inequality implies failure of the prefix-of-length-one
stopping inequality. -/
private theorem cons_stop_head' (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (acc u : ℕ)
    (h : ¬ (u < acc + e.2)) : ¬ (u < acc + pairSum ((e :: t).take 1)) := by
  rw [cons_take_succ e t 0, pairSum_append, pairSum_cons, pairSum_nil, add_zero]
  exact h

/-- The stopping inequality for a prefix of length one implies the head's stopping inequality. -/
private theorem cons_stop_head_inv (e : Fin N × ℕ) (t : List (Fin N × ℕ)) (acc u : ℕ)
    (h : u < acc + pairSum ((e :: t).take 1)) : u < acc + e.2 := by
  rw [cons_take_succ e t 0, pairSum_append, pairSum_cons, pairSum_nil, add_zero] at h
  exact h

/-- If `p` is the first prefix whose upper bound exceeds the ticket, the scan returns its label,
upper bound, and `k + p + 1` comparisons. -/
private theorem weightScan_spec_found (l : List (Fin N × ℕ)) (k acc u : ℕ) (p : ℕ)
    (hp : p < l.length) (hstop : u < acc + pairSum (l.take (p + 1)))
    (hbefore : ∀ q, q < p → ¬ (u < acc + pairSum (l.take (q + 1)))) :
    weightScan l k acc u = (some (l[p]).1, acc + pairSum (l.take (p + 1)), k + p + 1) := by
  induction l generalizing k acc p with
  | nil => exact absurd hp (by simp)
  | cons e t ih =>
      have hlen : (e :: t).length = t.length + 1 := length_cons e t
      rcases p with _ | p'
      · rw [weightScan, if_pos (cons_stop_head_inv e t acc u hstop)]
        simp
      · have hp' : p' < t.length := by omega
        have hbefore0 : ¬ (u < acc + e.2) := cons_stop'' e t 0 acc u (hbefore 0 (by omega))
        have hstop' : u < acc + e.2 + pairSum (t.take (p' + 1)) :=
          cons_stop e t (p' + 1) acc u hstop
        have hbefore' : ∀ q, q < p' → ¬ (u < acc + e.2 + pairSum (t.take (q + 1))) := by
          intro q hq
          exact cons_stop'' e t (q + 1) acc u (hbefore (q + 1) (by omega))
        rw [weightScan, if_neg hbefore0]
        have hi := ih (k := k + 1) (acc := acc + e.2) (p := p') hp' hstop' hbefore'
        have hget : ((e :: t)[p' + 1]).1 = (t[p']).1 := by rw [List.getElem_cons_succ]
        have key : (some (t[p']).1, acc + e.2 + pairSum (t.take (p' + 1)), (k + 1) + p' + 1)
            = (some (t[p']).1, acc + pairSum ((e :: t).take (p' + 1 + 1)), k + (p' + 1) + 1) := by
          rw [cons_take_succ e t (p' + 1), pairSum_append, pairSum_cons, pairSum_nil, add_zero]
          exact triple_congr rfl (by omega) (by omega)
        rw [hi, hget, key]

/-- If no prefix upper bound exceeds the ticket, the scan returns no label, the final
accumulated weight, and the initial count plus the list length. -/
private theorem weightScan_spec_none (l : List (Fin N × ℕ)) (k acc u : ℕ)
    (hnone : ∀ p, p < l.length → ¬ (u < acc + pairSum (l.take (p + 1)))) :
    weightScan l k acc u = (none, acc + pairSum l, k + l.length) := by
  induction l generalizing k acc with
  | nil => rfl
  | cons e t ih =>
      have hlen : (e :: t).length = t.length + 1 := length_cons e t
      have hbefore0 : ¬ (u < acc + e.2) := cons_stop'' e t 0 acc u (hnone 0 (by simp))
      have hnone' : ∀ p, p < t.length → ¬ (u < acc + e.2 + pairSum (t.take (p + 1))) := by
        intro p hp
        exact cons_stop'' e t (p + 1) acc u (hnone (p + 1) (by simp; omega))
      rw [weightScan, if_neg hbefore0]
      have hi := ih (k := k + 1) (acc := acc + e.2) hnone'
      have key : ((none : Option (Fin N)), acc + e.2 + pairSum t, (k + 1) + t.length)
          = ((none : Option (Fin N)), acc + pairSum (e :: t), k + (e :: t).length) := by
        simp only [pairSum_cons]
        exact triple_congr rfl (by omega) (by omega)
      rw [hi, key]

/-- The scan returns a label exactly when there is a first prefix upper bound exceeding the
ticket. -/
private theorem weightScan_found_iff (l : List (Fin N × ℕ)) (acc u : ℕ) :
    ∀ k : ℕ, (weightScan l k acc u).1 ≠ none ↔
      ∃ p, p < l.length ∧ u < acc + pairSum (l.take (p + 1))
        ∧ ∀ q, q < p → ¬ (u < acc + pairSum (l.take (q + 1))) := by
  induction l generalizing acc with
  | nil => intro k; simp [weightScan]
  | cons e t ih =>
      intro k
      have hlen : (e :: t).length = t.length + 1 := length_cons e t
      rw [weightScan]
      by_cases hstop : u < acc + e.2
      · rw [if_pos hstop]
        constructor
        · intro _
          exact ⟨0, by simp, cons_stop_head e t acc u hstop, by simp⟩
        · rintro ⟨_, _, _, _⟩
          exact Option.some_ne_none e.1
      · rw [if_neg hstop, ih (acc := acc + e.2) (k + 1)]
        constructor
        · rintro ⟨p, hp, hstop', hbefore'⟩
          rcases p with _ | p'
          · refine ⟨1, by omega, cons_stop_lift e t 1 acc u hstop', ?_⟩
            intro q hq
            have hq0 : q = 0 := by omega
            subst hq0
            exact cons_stop_head' e t acc u hstop
          · refine ⟨p' + 2, by omega, cons_stop_lift e t (p' + 2) acc u hstop', ?_⟩
            intro q hq
            by_cases hq0 : q = 0
            · subst hq0
              exact cons_stop_head' e t acc u hstop
            · have hlt : q - 1 ≤ p' := by omega
              have hbb := hbefore' (q - 1) (by omega)
              have hq1 : q - 1 + 1 = q := by omega
              rw [hq1] at hbb
              exact cons_stop' e t q acc u hbb
        · rintro ⟨p, hp, hstop', hbefore'⟩
          rcases p with _ | p'
          · exact absurd (cons_stop_head_inv e t acc u hstop') hstop
          · refine ⟨p', by omega, cons_stop e t (p' + 1) acc u hstop', ?_⟩
            intro q hq
            exact cons_stop'' e t (q + 1) acc u
              (hbefore' (q + 1) (by omega))

/-- If some prefix upper bound exceeds the ticket, there is a first such prefix. -/
private theorem weightScan_stop_exists (l : List (Fin N × ℕ)) (acc u : ℕ) (p : ℕ)
    (hp : p < l.length) (hstop : u < acc + pairSum (l.take (p + 1))) :
    ∃ p₀, p₀ < l.length ∧ u < acc + pairSum (l.take (p₀ + 1))
      ∧ ∀ q, q < p₀ → ¬ (u < acc + pairSum (l.take (q + 1))) := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
      by_cases hall : ∀ q, q < p → ¬ (u < acc + pairSum (l.take (q + 1)))
      · exact ⟨p, hp, hstop, hall⟩
      · rw [not_forall] at hall
        obtain ⟨q, hq⟩ := hall
        have hstopq : u < acc + pairSum (l.take (q + 1)) := by
          by_contra hc
          exact hq (fun _ => hc)
        by_cases hqp : q < p
        · have hpq : q < l.length := by omega
          exact ih q hqp hpq hstopq
        · exfalso
          exact hq (fun hnc _ => hqp hnc)

/-- Two prefix positions satisfying the first-stopping condition must be equal. -/
private theorem weightScan_stop_unique (l : List (Fin N × ℕ)) (acc u : ℕ) (p p' : ℕ)
    (hstop : u < acc + pairSum (l.take (p + 1)))
    (hbefore : ∀ q, q < p → ¬ (u < acc + pairSum (l.take (q + 1))))
    (hstop' : u < acc + pairSum (l.take (p' + 1)))
    (hbefore' : ∀ q, q < p' → ¬ (u < acc + pairSum (l.take (q + 1)))) : p = p' := by
  by_cases h : p < p'
  · exact absurd hstop (hbefore' p h)
  · by_cases h' : p' < p
    · exact absurd hstop' (hbefore p' h')
    · omega

/-- The scan returns a label exactly when some prefix upper bound exceeds the ticket. -/
private theorem weightScan_hit_iff (l : List (Fin N × ℕ)) (acc u k : ℕ) :
    (weightScan l k acc u).1 ≠ none ↔
      ∃ p, p < l.length ∧ u < acc + pairSum (l.take (p + 1)) := by
  constructor
  · intro h
    obtain ⟨p, hp, hstop, -⟩ := weightScan_found_iff l acc u k |>.1 h
    exact ⟨p, hp, hstop⟩
  · rintro ⟨p, hp, hstop⟩
    obtain ⟨p₀, hp₀, hstop₀, hbefore₀⟩ := weightScan_stop_exists l acc u p hp hstop
    exact weightScan_found_iff l acc u k |>.2 ⟨p₀, hp₀, hstop₀, hbefore₀⟩

end ScanHelpers

section WeightedDecoder

variable {N : ℕ}

/-- The sum of all natural-number label weights. -/
def weightTotal (w : Fin N → ℕ) : ℕ := ∑ j : Fin N, w j

/-- The sum of the weights of labels strictly preceding `j`. -/
def weightPrefix (w : Fin N → ℕ) (j : Fin N) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j.val), w i

/-- The list of labels paired with their weights in increasing label order. -/
private def weightList (w : Fin N → ℕ) : List (Fin N × ℕ) :=
  List.ofFn fun j : Fin N => (j, w j)

/-- The total weight of the first `k` entries of the ordered weight list. -/
private def lprefix (w : Fin N → ℕ) (k : ℕ) : ℕ := pairSum ((weightList w).take k)

/-- A sum over a finite type equals the corresponding sum over its universal finite set. -/
private theorem sum_univ {α : Type} [Fintype α] [DecidableEq α] (f : α → ℕ) :
    (∑ i : α, f i) = ∑ i ∈ Finset.univ, f i := by
  rw [← Finset.sum_attach]

/-- The labels below `k + 1` are the labels below `k` together with the label at position `k`. -/
private theorem filter_lt_eq_insert (k : ℕ) (hk : k < N) :
    ((Finset.univ.filter (fun i : Fin N => i.val < k + 1)) : Finset (Fin N))
      = (Finset.univ.filter (fun i : Fin N => i.val < k)) ∪ {⟨k, hk⟩} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    rcases Nat.lt_or_ge i.val k with hi | hi
    · exact Or.inl hi
    · have hie : i.val = k := by omega
      subst hie
      exact Or.inr rfl
  · rintro (hi | rfl)
    · omega
    · exact Nat.lt_succ_self k

/-- The weight sum below `k + 1` equals the sum below `k` plus the weight at position `k`. -/
private theorem sum_filter_lt_succ (w : Fin N → ℕ) (k : ℕ) (hk : k < N) :
    ((Finset.univ.filter (fun i : Fin N => i.val < k + 1)) : Finset (Fin N)).sum w
      = ((Finset.univ.filter (fun i : Fin N => i.val < k)) : Finset (Fin N)).sum w + w ⟨k, hk⟩ := by
  rw [filter_lt_eq_insert k hk,
    Finset.sum_union (Finset.disjoint_left.mpr fun i hi hmem => by
      simp only [Finset.mem_singleton] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      subst hmem
      simp at hi),
    Finset.sum_singleton]

/-- Increasing the cutoff cannot decrease the sum of natural-number weights below that cutoff. -/
private theorem sum_filter_mono (w : Fin N → ℕ) {k l : ℕ} (hkl : k ≤ l) :
    ((Finset.univ.filter (fun i : Fin N => i.val < k)) : Finset (Fin N)).sum w
      ≤ ((Finset.univ.filter (fun i : Fin N => i.val < l)) : Finset (Fin N)).sum w := by
  have hsub : ((Finset.univ.filter (fun i : Fin N => i.val < k)) : Finset (Fin N))
      ⊆ Finset.univ.filter (fun i : Fin N => i.val < l) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    omega
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro i _ _
  exact Nat.zero_le _

/-- For `k ≤ N`, summing weights of labels below `k` equals the weight-list prefix sum `lprefix
w k`. -/
private theorem sum_filter_lt (w : Fin N → ℕ) : ∀ (k : ℕ), k ≤ N →
    ((Finset.univ.filter (fun i : Fin N => i.val < k)) : Finset (Fin N)).sum w = lprefix w k := by
  intro k
  induction k with
  | zero =>
      intro hk
      have h0 : (Finset.univ.filter (fun i : Fin N => i.val < (0 : ℕ))) = ∅ := by
        ext i
        simp
      rw [h0, Finset.sum_empty]
      rfl
  | succ k ih =>
      intro hk
      have hk1 : k < N := by omega
      have hLen : (weightList w).length = N := List.length_ofFn
      have hkg : k < (weightList w).length := by omega
      have hget : (weightList w)[k] = (⟨k, hk1⟩, w ⟨k, hk1⟩) := by
        show (List.ofFn (fun j : Fin N => (j, w j)))[k] = (⟨k, hk1⟩, w ⟨k, hk1⟩)
        exact ofFn_getElem (fun j : Fin N => (j, w j)) k hk1
      calc ((Finset.univ.filter (fun i : Fin N => i.val < k + 1)) : Finset (Fin N)).sum w
          = ((Finset.univ.filter (fun i : Fin N => i.val < k)) : Finset (Fin N)).sum w
              + w ⟨k, hk1⟩ := sum_filter_lt_succ w k hk1
        _ = lprefix w k + w ⟨k, hk1⟩ :=
          congrArg (fun x : ℕ => x + w ⟨k, hk1⟩) (ih (Nat.le_of_lt hk1))
        _ = pairSum ((weightList w).take k) + w ⟨k, hk1⟩ := rfl
        _ = pairSum ((weightList w).take (k + 1)) := by
          rw [pairSum_take_succ (weightList w) k hkg, hget]
        _ = lprefix w (k + 1) := rfl

/-- The weight preceding label `j` equals the list prefix sum at `j.val`. -/
private theorem weightPrefix_eq_lprefix' (w : Fin N → ℕ) (j : Fin N) :
    weightPrefix w j = lprefix w j.val := by
  rw [weightPrefix, sum_filter_lt w j.val (by simp)]

/-- The total weight of the ordered weight list equals `weightTotal w`. -/
private theorem pairSum_weightList (w : Fin N → ℕ) : pairSum (weightList w) = weightTotal w := by
  have hLen : (weightList w).length = N := List.length_ofFn
  have htake : (weightList w).take N = weightList w :=
    (List.take_eq_self_iff (weightList w)).mpr (by simp [hLen])
  calc pairSum (weightList w) = pairSum ((weightList w).take N) := by rw [htake]
    _ = lprefix w N := rfl
    _ = ((Finset.univ.filter (fun i : Fin N => i.val < N)) : Finset (Fin N)).sum w :=
        (sum_filter_lt w N (le_refl N)).symm
    _ = ∑ j : Fin N, w j := by
        rw [show ((Finset.univ.filter (fun i : Fin N => i.val < N)) : Finset (Fin N))
            = Finset.univ by
          ext i
          simp, sum_univ]

/-- The prefix sum at the full label count equals the total weight. -/
private theorem lprefix_total (w : Fin N → ℕ) : lprefix w N = weightTotal w := by
  have hLen : (weightList w).length = N := List.length_ofFn
  have htake : (weightList w).take N = weightList w :=
    (List.take_eq_self_iff (weightList w)).mpr (by simp [hLen])
  rw [lprefix, htake, pairSum_weightList]

/-- Every prefix sum up to the label count is at most the total weight. -/
private theorem lprefix_le_total (w : Fin N → ℕ) (k : ℕ) (hk : k ≤ N) :
    lprefix w k ≤ weightTotal w := by
  have hLen : (weightList w).length = N := List.length_ofFn
  calc lprefix w k = pairSum ((weightList w).take k) := rfl
    _ ≤ pairSum (weightList w) :=
      pairSum_take_le (weightList w) k (by simpa [hLen] using hk)
    _ = weightTotal w := pairSum_weightList w

/-- The ordered list's prefix weight sum is monotone for cutoffs bounded by `N`. -/
private theorem lprefix_mono (w : Fin N → ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ N) :
    lprefix w k ≤ lprefix w l := by
  rw [← sum_filter_lt w k (by omega), ← sum_filter_lt w l hl]
  exact sum_filter_mono w hkl

/-- Extending a weight-list prefix by one label adds that label's weight. -/
private theorem lprefix_succ (w : Fin N → ℕ) (k : ℕ) (hk : k < N) :
    lprefix w (k + 1) = lprefix w k + w ⟨k, hk⟩ := by
  have hLen : (weightList w).length = N := List.length_ofFn
  have hkg : k < (weightList w).length := by omega
  have hget : (weightList w)[k] = (⟨k, hk⟩, w ⟨k, hk⟩) := by
    show (List.ofFn (fun j : Fin N => (j, w j)))[k] = (⟨k, hk⟩, w ⟨k, hk⟩)
    exact ofFn_getElem (fun j : Fin N => (j, w j)) k hk
  rw [lprefix, lprefix, pairSum_take_succ (weightList w) k hkg, hget]

/-- The prefix sum through label `j` equals `weightPrefix w j + w j`. -/
private theorem lprefix_succ' (w : Fin N → ℕ) (j : Fin N) :
    lprefix w (j.val + 1) = weightPrefix w j + w j := by
  rw [lprefix_succ w j.val j.isLt, weightPrefix_eq_lprefix' w j]

/-- The sum of weights in a prefix of length `q + 1` is at most that in a prefix of length `r`
when `q + 1 ≤ r`. -/
private theorem pairSum_take_mono (l : List (Fin N × ℕ)) {q r : ℕ} (hqr : q + 1 ≤ r)
    (_hr : r ≤ l.length) : pairSum (l.take (q + 1)) ≤ pairSum (l.take r) := by
  have hsub : q ≤ r := by omega
  have heq : q + (r - q) = r := by omega
  have hA : l.take (q + 1) = l.take q ++ List.take 1 (l.drop q) :=
    @List.take_add (Fin N × ℕ) l q 1
  have hB : l.take r = l.take q ++ List.take (r - q) (l.drop q) := by
    have := @List.take_add (Fin N × ℕ) l q (r - q)
    rwa [heq] at this
  have hinner : pairSum (List.take 1 (l.drop q))
      ≤ pairSum (List.take (r - q) (l.drop q)) := by
    have heq : 1 + (r - q - 1) = r - q := by omega
    have htake : List.take (r - q) (l.drop q)
        = List.take 1 (l.drop q) ++ List.take (r - q - 1) ((l.drop q).drop 1) := by
      have h := @List.take_add (Fin N × ℕ) (l.drop q) 1 (r - q - 1)
      rwa [heq] at h
    rw [htake, pairSum_append]
    exact Nat.le_add_right _ _
  rw [hA, hB, pairSum_append, pairSum_append]
  exact Nat.add_le_add_left hinner _

/-- Ordered weight-list prefix sums are monotone between the specified bounded prefix lengths. -/
private theorem pairSum_take_mono_w (w : Fin N → ℕ) {q r : ℕ} (hqr : q + 1 ≤ r) (hr : r ≤ N) :
    pairSum ((weightList w).take (q + 1)) ≤ pairSum ((weightList w).take r) := by
  have hLen : (weightList w).length = N := List.length_ofFn
  exact pairSum_take_mono (weightList w) hqr (by omega)

/-- Sum a list of weights and count one addition for each list entry. -/
private def weightTotalCountedAux : List (Fin N × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | (_, wj) :: t =>
      let r := weightTotalCountedAux t
      (r.1 + wj, r.2 + 1)

/-- The total label weight together with the number of additions used by the list-based
summation. -/
def weightTotalCounted (w : Fin N → ℕ) : ℕ × ℕ := weightTotalCountedAux (weightList w)

/-- The counted list summation returns its weight sum and its length as the addition count. -/
private theorem weightTotalCountedAux_spec : ∀ (l : List (Fin N × ℕ)),
    (weightTotalCountedAux l).1 = pairSum l ∧ (weightTotalCountedAux l).2 = l.length := by
  intro l
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons e t ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [weightTotalCountedAux]
      rw [h1, h2, pairSum_cons]
      exact ⟨by omega, rfl⟩

/-- Summing the ordered weights returns `(weightTotal w, N)`. -/
theorem weightTotalCounted_ofFn (w : Fin N → ℕ) :
    weightTotalCounted w = (weightTotal w, N) := by
  obtain ⟨h1, h2⟩ := weightTotalCountedAux_spec (weightList w)
  have hLen : (weightList w).length = N := List.length_ofFn
  rw [weightTotalCounted]
  exact Prod.ext (by rw [h1, pairSum_weightList]) (by rw [h2]; simp [hLen])

/-- Decode a natural-number ticket by a cumulative weight scan and return its optional label and
actual comparison count. -/
def weightDecodeCounted (w : Fin N → ℕ) (u : ℕ) : Option (Fin N) × ℕ :=
  let r := weightScan (weightList w) 0 0 u
  (r.1, r.2.2)

/-- The counted decoder's optional output equals the underlying weight scan's optional output. -/
private theorem weightDecodeCounted_out (w : Fin N → ℕ) (u : ℕ) :
    (weightDecodeCounted w u).1 = (weightScan (weightList w) 0 0 u).1 := rfl

/-- The counted decoder's comparison count equals the underlying weight scan's count. -/
private theorem weightDecodeCounted_cnt (w : Fin N → ℕ) (u : ℕ) :
    (weightDecodeCounted w u).2 = (weightScan (weightList w) 0 0 u).2.2 := rfl

/-- A successful decoding returns some label `j` after `j.val + 1` comparisons, with the ticket
in that label's prefix interval. -/
private theorem weightDecodeCounted_hit (w : Fin N → ℕ) (u : ℕ)
    (hr : (weightDecodeCounted w u).1 ≠ none) :
    ∃ (j : Fin N), weightDecodeCounted w u = (some j, j.val + 1) ∧
      weightPrefix w j ≤ u ∧ u < weightPrefix w j + w j := by
  have hLen : (weightList w).length = N := List.length_ofFn
  have hr' : (weightScan (weightList w) 0 0 u).1 ≠ none := by
    rw [← weightDecodeCounted_out]
    exact hr
  obtain ⟨p, hplen, hstop, hbefore⟩ :=
    weightScan_found_iff (weightList w) 0 u 0 |>.1 hr'
  obtain ⟨p₀, hp₀, hstop₀, hbefore₀⟩ :=
    weightScan_stop_exists (weightList w) 0 u p hplen hstop
  have huniq : p₀ = p :=
      weightScan_stop_unique (weightList w) 0 u p₀ p hstop₀ hbefore₀ hstop hbefore
  rw [huniq] at hstop₀ hbefore₀
  have hpl : p < N := by simpa [hLen] using hplen
  have hspec := weightScan_spec_found (weightList w) 0 0 u p hplen hstop₀ hbefore₀
  have hkg : p < (weightList w).length := by omega
  have hget : (weightList w)[p] = (⟨p, hpl⟩, w ⟨p, hpl⟩) := by
    show (List.ofFn (fun j : Fin N => (j, w j)))[p] = (⟨p, hpl⟩, w ⟨p, hpl⟩)
    exact ofFn_getElem (fun j : Fin N => (j, w j)) p hpl
  have hget' : ((weightList w)[p]).1 = ⟨p, hpl⟩ := congrArg Prod.fst hget
  refine ⟨⟨p, hpl⟩, ?_, ?_, ?_⟩
  · have h1 : weightDecodeCounted w u = ((weightScan (weightList w) 0 0 u).1,
        (weightScan (weightList w) 0 0 u).2.2) := rfl
    rw [h1, hspec, hget]
    simp
  · have hle : lprefix w p ≤ u := by
      by_cases hp0 : p = 0
      · subst hp0
        show pairSum ((weightList w).take 0) ≤ u
        rw [List.take_zero, pairSum_nil]
        exact Nat.zero_le _
      · have hne : ¬ (u < lprefix w ((p - 1) + 1)) := by
          have hh := hbefore₀ (p - 1) (by omega)
          simpa [lprefix] using hh
        have hp1 : (p - 1) + 1 = p := by omega
        rw [hp1] at hne
        omega
    rw [← weightPrefix_eq_lprefix' w ⟨p, hpl⟩] at hle
    exact hle
  · have hlt : u < lprefix w (p + 1) := by simpa [lprefix] using hstop₀
    rw [lprefix_succ' w ⟨p, hpl⟩] at hlt
    exact hlt

/-- A rejected ticket uses all `N` comparisons and reaches no prefix upper bound exceeding the
ticket. -/
private theorem weightDecodeCounted_miss (w : Fin N → ℕ) (u : ℕ)
    (hr : (weightDecodeCounted w u).1 = none) :
    (weightDecodeCounted w u).2 = N ∧ ∀ p : ℕ, p < N → ¬ (u < lprefix w (p + 1)) := by
  have hLen : (weightList w).length = N := List.length_ofFn
  have hno : ∀ p, p < (weightList w).length →
      ¬ (u < 0 + pairSum ((weightList w).take (p + 1))) := by
    intro p hp hc
    rw [weightDecodeCounted_out] at hr
    exact weightScan_hit_iff (weightList w) 0 u 0 |>.2 ⟨p, hp, hc⟩ hr
  have hspec := weightScan_spec_none (weightList w) 0 0 u hno
  rw [weightDecodeCounted_cnt, hspec]
  constructor
  · simp [hLen]
  · intro p hp hc
    exact hno p (by simpa [hLen] using hp) (by simpa [lprefix] using hc)

/-- Decoding uses at most `N` comparisons, exactly `N` on rejection, and exactly `j.val + 1`
when returning `j`. -/
theorem weightDecodeCounted_bounds (w : Fin N → ℕ) (u : ℕ) :
    (weightDecodeCounted w u).2 ≤ N ∧
      ((weightDecodeCounted w u).1 = none → (weightDecodeCounted w u).2 = N) ∧
      (∀ j : Fin N, (weightDecodeCounted w u).1 = some j →
        (weightDecodeCounted w u).2 = j.val + 1) := by
  by_cases hr : (weightDecodeCounted w u).1 = none
  · obtain ⟨hcnt, -⟩ := weightDecodeCounted_miss w u hr
    refine ⟨?_, ?_, ?_⟩
    · simp [hcnt]
    · intro _
      exact hcnt
    · intro j hj
      rw [hr] at hj
      simp at hj
  · obtain ⟨j, hj, -, -⟩ := weightDecodeCounted_hit w u hr
    refine ⟨?_, ?_, ?_⟩
    · simp [hj]
    · intro hc
      exact (hr hc).elim
    · intro i hi
      have hi' : i = j := Option.some.inj (by rw [hj] at hi; exact hi.symm)
      rw [hi', hj]

/-- If the decoder returns no label, its comparison count is exactly `N`. -/
theorem weightDecodeCounted_hit_count (w : Fin N → ℕ) (u : ℕ)
    (hr : (weightDecodeCounted w u).1 = none) : (weightDecodeCounted w u).2 = N :=
  (weightDecodeCounted_miss w u hr).1

/-- Decoding returns `j` exactly when the ticket lies in the half-open interval from
`weightPrefix w j` to `weightPrefix w j + w j`. -/
theorem weightDecodeCounted_some_iff (w : Fin N → ℕ) (u : ℕ) (j : Fin N) :
    (weightDecodeCounted w u).1 = some j ↔ weightPrefix w j ≤ u ∧ u < weightPrefix w j + w j := by
  constructor
  · intro hr
    obtain ⟨j', hj', hle, hlt⟩ := weightDecodeCounted_hit w u (by rw [hr]; simp)
    have : j' = j := Option.some.inj (by rw [hj'] at hr; exact hr)
    simpa [this] using And.intro hle hlt
  · rintro ⟨hle, hlt⟩
    have hLen : (weightList w).length = N := List.length_ofFn
    have hstop : u < 0 + pairSum ((weightList w).take (j.val + 1)) := by
      have hstep := lprefix_succ' w j
      simp only [lprefix] at hstep
      omega
    have hbefore : ∀ q, q < j.val →
        ¬ (u < 0 + pairSum ((weightList w).take (q + 1))) := by
      intro q hq hc
      have hqr : q + 1 ≤ j.val := by omega
      have hjr : j.val ≤ N := by omega
      have h1 := pairSum_take_mono_w w hqr hjr
      have h2 : pairSum ((weightList w).take j.val) ≤ u := by
        show lprefix w j.val ≤ u
        exact weightPrefix_eq_lprefix' w j ▸ hle
      omega
    have hspec := weightScan_spec_found (weightList w) 0 0 u j.val (by omega) hstop hbefore
    have hkg : j.val < (weightList w).length := by omega
    have hjg : (weightList w)[j.val]'hkg = (j, w j) := by
      show (List.ofFn (fun i : Fin N => (i, w i)))[j.val] = (j, w j)
      exact ofFn_getElem (fun i : Fin N => (i, w i)) j.val (by omega)
    have hget : ((weightList w)[j.val]).1 = j := congrArg Prod.fst hjg
    rw [weightDecodeCounted_out, hspec, hget]

/-- The decoder rejects a ticket exactly when the ticket is at least the total weight. -/
theorem weightDecodeCounted_none_iff (w : Fin N → ℕ) (u : ℕ) :
    (weightDecodeCounted w u).1 = none ↔ weightTotal w ≤ u := by
  constructor
  · intro hr
    obtain ⟨-, hnone⟩ := weightDecodeCounted_miss w u hr
    have h1 : ¬ (u < lprefix w N) := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · simp only [lprefix, hN, List.take_zero, pairSum_nil]
        exact Nat.not_lt_zero u
      · have hq := hnone (N - 1) (by omega)
        rwa [show N - 1 + 1 = N from by omega] at hq
    rw [lprefix_total] at h1
    omega
  · intro hr
    by_contra hne
    have hne' : (weightScan (weightList w) 0 0 u).1 ≠ none := by
      rw [weightDecodeCounted_out] at hne
      exact hne
    obtain ⟨p, hp, hstop⟩ := weightScan_hit_iff (weightList w) 0 u 0 |>.1 hne'
    have hLen : (weightList w).length = N := List.length_ofFn
    have h1 : lprefix w (p + 1) ≤ weightTotal w :=
      lprefix_le_total w (p + 1) (by omega)
    have hlp : lprefix w (p + 1) = pairSum ((weightList w).take (p + 1)) := rfl
    rw [hlp] at h1
    omega

/-- The cardinality of a filtered finite type equals the sum of its predicate's zero-one
indicator. -/
private theorem card_filter_eq_sum_ite {α : Type} [Fintype α] [DecidableEq α] (P : α → Prop)
    [DecidablePred P] : (Finset.univ.filter P).card = ∑ a : α, if P a then 1 else 0 := by
  calc (Finset.univ.filter P).card = ∑ a ∈ Finset.univ.filter P, (1 : ℕ) :=
        Finset.card_eq_sum_ones _
    _ = ∑ a ∈ Finset.univ, (if P a then 1 else 0) :=
        Finset.sum_filter P (fun _ => (1 : ℕ))
    _ = ∑ a : α, if P a then 1 else 0 :=
        (sum_univ (fun a => if P a then (1 : ℕ) else 0)).symm

/-- A half-open label bucket contained in the ticket space has cardinality equal to its weight. -/
private theorem card_bucket (w : Fin N → ℕ) (j : Fin N)
    (hj : weightPrefix w j + w j ≤ weightTotal w) :
    (Finset.univ.filter (fun u : Fin (weightTotal w) =>
      weightPrefix w j ≤ u.val ∧ u.val < weightPrefix w j + w j)).card = w j := by
  have key : ∀ u : Fin (weightTotal w),
      (weightPrefix w j ≤ u.val ∧ u.val < weightPrefix w j + w j) →
        weightPrefix w j + (u.val - weightPrefix w j) = u.val := by
    intro u hu
    have hu' : weightPrefix w j ≤ u.val ∧ u.val < weightPrefix w j + w j := hu
    omega
  refine Finset.card_eq_of_bijective
    (s := Finset.univ.filter fun u : Fin (weightTotal w) =>
      weightPrefix w j ≤ u.val ∧ u.val < weightPrefix w j + w j) (n := w j)
    (fun i hi => ⟨weightPrefix w j + i, by omega⟩) ?_ ?_ ?_
  · intro a ha
    have ha' : weightPrefix w j ≤ a.val ∧ a.val < weightPrefix w j + w j := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
    refine ⟨a.val - weightPrefix w j, by omega, ?_⟩
    apply Fin.ext
    exact key a ha'
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i j' hi hj' heq
    have h := congrArg Fin.val heq
    simp only at h
    omega

/-- Among tickets below the total weight, the decoder's fiber over label `j` has cardinality `w
j`. -/
theorem weightDecodeCounted_fibers (w : Fin N → ℕ) (j : Fin N) :
    (Finset.univ.filter (fun u : Fin (weightTotal w) =>
      (weightDecodeCounted w u.val).1 = some j)).card = w j := by
  have hj : weightPrefix w j + w j ≤ weightTotal w := by
    rw [← lprefix_succ' w j]
    exact lprefix_le_total w (j.val + 1) (by simp)
  have hcong : ((Finset.univ.filter (fun u : Fin (weightTotal w) =>
      (weightDecodeCounted w u.val).1 = some j)) : Finset (Fin (weightTotal w)))
      = Finset.univ.filter (fun u : Fin (weightTotal w) =>
        weightPrefix w j ≤ u.val ∧ u.val < weightPrefix w j + w j) :=
    Finset.filter_congr fun u _ => weightDecodeCounted_some_iff w u.val j
  rw [hcong, card_bucket w j hj]

/-- The upper endpoint of each label's prefix interval is at most the total weight. -/
theorem weightPrefix_add_le (w : Fin N → ℕ) (j : Fin N) :
    weightPrefix w j + w j ≤ weightTotal w := by
  rw [← lprefix_succ' w j]
  exact lprefix_le_total w (j.val + 1) (by simp)

/-- The label returned by decoding a ticket strictly below the positive total weight. -/
def weightTicket (w : Fin N → ℕ) (_hW : 0 < weightTotal w) (u : Fin (weightTotal w)) : Fin N :=
  (weightDecodeCounted w u.val).1.get (by
    rw [Option.isSome_iff_ne_none]
    intro hc
    rw [weightDecodeCounted_none_iff] at hc
    omega)

/-- The counted total and decoder satisfy the exact addition count, decoding intervals,
comparison counts, fiber cardinalities, and valid-ticket output specification. -/
theorem weighted_decoder_intervals_and_actual_cost :
    ∀ (N : ℕ) (w : Fin N → ℕ),
      (weightTotalCounted w).1 = weightTotal w ∧ (weightTotalCounted w).2 = N ∧
      (∀ u : ℕ, (weightDecodeCounted w u).2 ≤ N ∧
        ((weightDecodeCounted w u).1 = none ↔ weightTotal w ≤ u) ∧
        ((weightDecodeCounted w u).1 = none → (weightDecodeCounted w u).2 = N) ∧
        (∀ j : Fin N, ((weightDecodeCounted w u).1 = some j ↔
          weightPrefix w j ≤ u ∧ u < weightPrefix w j + w j) ∧
          ((weightDecodeCounted w u).1 = some j → (weightDecodeCounted w u).2 = j.val+1))) ∧
      (∀ j : Fin N, (Finset.univ.filter (fun u : Fin (weightTotal w) =>
        (weightDecodeCounted w u.val).1 = some j)).card = w j) ∧
      (∀ (hW : 0 < weightTotal w) (u : Fin (weightTotal w)),
        (weightDecodeCounted w u.val).1 = some (weightTicket w hW u)) := by
  intro N w
  have hct : weightTotalCounted w = (weightTotal w, N) := weightTotalCounted_ofFn w
  refine ⟨congrArg Prod.fst hct, congrArg Prod.snd hct, fun u => ?_,
    fun j => weightDecodeCounted_fibers w j, ?_⟩
  · obtain ⟨hb, hmiss, hhit⟩ := weightDecodeCounted_bounds w u
    refine And.intro hb (And.intro (weightDecodeCounted_none_iff w u) ?_)
    exact And.intro (fun hc => hmiss hc)
      (fun j => And.intro (weightDecodeCounted_some_iff w u j) (hhit j))
  · intro hW u
    cases hd : (weightDecodeCounted w u.val).1 with
    | none =>
        rw [weightDecodeCounted_none_iff] at hd
        omega
    | some j =>
        have htk : weightTicket w hW u = j := by
          simp [weightTicket, hd]
        rw [htk]

end WeightedDecoder

end Qatlib.Concepts.FairRandomBits.RationalReject
