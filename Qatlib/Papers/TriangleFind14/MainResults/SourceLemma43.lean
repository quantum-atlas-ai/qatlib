/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.3 of TriangleFind14

François Le Gall, *Improved Quantum Algorithm for Triangle Finding via
Combinatorial Arguments*, fixed version arXiv:1407.0085v2 (8 Sep 2014),
Lemma 4.3, printed p. 12.

The lemma is a sampling statement about the uniform `r`-element subset
`B ∈ S(A,r)` of a set `A` with `|A| > 3`.  For a fixed edge `{v1,v2} ∈ E(A)`
and a vertex `w`, the two conditions

(i)  `{v1,v2} ∈ E(B)`;
(ii) `|Δ_G(X,B,w)| ≤ 8(r-2)(r-3)/((|A|-2)(|A|-3)) · |Δ_G(X,A,w)|/3 + 16r`

hold simultaneously with probability at least `(r-1)²/(2|A|²)`.

The file contains two declarations:

* `pair_containment_probability` — the first half of the paper's proof,
  `Pr[i] = C(|A|-2,r-2)/C(|A|,r) ≥ (r-1)²/|A|²`, proved in full;
* `source_lemma_4_3` — the lemma itself, proved in full: conditioning on (i),
  the bijection `B ↦ B \ {v1,v2}` identifies the conditional law with the
  uniform `(r-2)`-subsets `C` of `A' = A \ {v1,v2}`; a double count of
  `∑_C |Δ_G(X,C∪{v1,v2},w)|` over the edges of `Δ_G(X,A,w)` splits by how an
  edge meets `{v1,v2}` and gives the expectation bound; Markov's inequality at
  twice that expectation leaves at most half of the `C` bad, so (i) and (ii)
  hold simultaneously with probability at least `(r-1)²/(2|A|²)`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.TriangleFind14.MainResults

/-- arXiv:1407.0085v2, Lemma 4.3, printed p. 12 (first display of the proof):
for `{v1,v2} ⊆ A` with `v1 ≠ v2` and `2 ≤ r ≤ |A|`, the uniform `r`-subset of
`A` contains both `v1` and `v2` with probability

`C(|A|-2, r-2) / C(|A|, r) = r(r-1)/(|A|(|A|-1)) ≥ (r-1)²/|A|²`.

This is exactly the paper's bound `Pr[Condition (i) holds] ≥ (r-1)²/|A|²`. -/
lemma pair_containment_probability {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (v1 v2 : V) (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (hne : v1 ≠ v2)
    (r : ℕ) (hr2 : 2 ≤ r) (hrA : r ≤ A.card) :
    (((r : ℝ) - 1) ^ 2) / ((A.card : ℝ) ^ 2) ≤
      subsetProb A r (fun B => ({v1, v2} : Finset V) ⊆ B) := by
  -- The pair is a two-element subset of `A`.
  have hs : ({v1, v2} : Finset V) ⊆ A := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv1
    · exact hv2
  have hscard : ({v1, v2} : Finset V).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hne
  -- Count the `r`-subsets of `A` that contain the pair.
  have hnum :
      ((A.powersetCard r).filter (fun B => ({v1, v2} : Finset V) ⊆ B)).card
        = Nat.choose (A.card - 2) (r - 2) := by
    have hle : ({v1, v2} : Finset V).card ≤ r := by omega
    have h := Finset.card_filter_powersetCard_subset ({v1, v2} : Finset V) A r hs hle
    rwa [hscard] at h
  -- Denominator: `C(|A|, r)`.
  have hden : (A.powersetCard r).card = Nat.choose A.card r :=
    Finset.card_powersetCard r A
  -- Positivity of the denominator.
  have hCpos : (0 : ℝ) < (Nat.choose A.card r : ℝ) := by
    exact_mod_cast Nat.choose_pos hrA
  have hn : (2 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast (le_trans hr2 hrA)
  have hnpos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hn1pos : (0 : ℝ) < (A.card : ℝ) - 1 := by linarith
  have hr1pos : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    linarith
  -- Pascal-type identity: `C(n,r)·C(r,2) = C(n,2)·C(n-2,r-2)`.
  have hchoose := Nat.choose_mul (n := A.card) (k := r) (s := 2) hr2
  have hcast :
      (Nat.choose A.card r : ℝ) * (Nat.choose r 2 : ℝ)
        = (Nat.choose A.card 2 : ℝ) * (Nat.choose (A.card - 2) (r - 2) : ℝ) := by
    exact_mod_cast hchoose
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hcast
  -- `C(n,r)·r(r-1) = n(n-1)·C(n-2,r-2)`.
  have hid :
      (Nat.choose A.card r : ℝ) * ((r : ℝ) * ((r : ℝ) - 1))
        = (A.card : ℝ) * ((A.card : ℝ) - 1)
            * (Nat.choose (A.card - 2) (r - 2) : ℝ) := by
    nlinarith [hcast]
  -- Ratio identity: the numerator over the denominator is
  -- `r(r-1)/(n(n-1))`.
  have hratio :
      (Nat.choose (A.card - 2) (r - 2) : ℝ) / (Nat.choose A.card r : ℝ)
        = (r : ℝ) * ((r : ℝ) - 1) / ((A.card : ℝ) * ((A.card : ℝ) - 1)) := by
    rw [div_eq_div_iff (ne_of_gt hCpos) (mul_ne_zero (ne_of_gt hnpos) (ne_of_gt hn1pos))]
    nlinarith [hid]
  rw [subsetProb]
  rw [Finset.filter_congr_decidable]
  rw [hnum, hden, hratio]
  -- `(r-1)²/n² ≤ r(r-1)/(n(n-1))`, equivalently `r+n-1 > 0`.
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hr1pos, hn1pos, hn]

set_option maxHeartbeats 1200000 in
/-- Lemma 4.3 of arXiv:1407.0085v2 (printed p. 12).  Let `A, X ⊆ V` with
`|A| > 3`, let `w ∈ V`, let `{v1,v2} ∈ E(A)`, and let `3 < r ≤ |A|`.
For `B` uniform in `S(A,r)`, conditions (i) and (ii) of the paper hold with
probability at least `(r-1)²/(2|A|²)`.

Lean representation: `B ∈ S(A,r)` is `B ∈ A.powersetCard r`, uniform
probability is `subsetProb`; condition (i) `{v1,v2} ∈ E(B)` is represented by
`{v1,v2} ⊆ B` (the adjacency `hpair` is a hypothesis and `B ⊆ A`), and
condition (ii) is the paper's displayed inequality.

Proof (paper pp. 12–13): the `r`-subsets of `A` containing `{v1,v2}` biject
with the `(r-2)`-subsets `C` of `A' = A \ {v1,v2}` via `C ↦ C ∪ {v1,v2}`, so
the conditional law of `B` given (i) is uniform on those `C`.  Writing
`Z C = |Δ_G(X,C∪{v1,v2},w)|` and double counting `∑_C Z C` over the edges of
`Δ_G(X,A,w)` by how an edge meets `{v1,v2}` (both endpoints: every `C`;
exactly one endpoint: `C(a-3,r-3)` choices; neither: `C(a-4,r-4)` choices,
where `a = |A|`) gives `∑_C Z C ≤ N'(α·m + 2r - 3)` with `N' = C(a-2,r-2)`,
`α = (r-2)(r-3)/((a-2)(a-3))` and `m = |Δ_G(X,A,w)|`.  The level
`t = 8α·m/3 + 16r` of condition (ii) is at least twice this expectation bound,
so Markov's inequality leaves at most half of the `C` bad; multiplying by
`Pr[i] ≥ (r-1)²/a²` (`pair_containment_probability`) gives the claim. -/
theorem source_lemma_4_3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X A : Finset V) (w v1 v2 : V) (r : ℕ)
    (hAcard : 3 < A.card) (hr : 3 < r) (hrA : r ≤ A.card)
    (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (hne : v1 ≠ v2) (hpair : G.Adj v1 v2) :
    ((r : ℝ) - 1) ^ 2 / (2 * (A.card : ℝ) ^ 2) ≤
      subsetProb A r (fun B =>
        ({v1, v2} : Finset V) ⊆ B ∧
          ((deltaSetW G X B w).card : ℝ) ≤
            8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
                (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
              (((deltaSetW G X A w).card : ℝ) / 3) + 16 * (r : ℝ)) := by
  classical
  set A' : Finset V := A \ ({v1, v2} : Finset V) with hA'def
  set S' : Finset (Finset V) := A'.powersetCard (r - 2) with hS'def
  set N' : ℕ := S'.card with hN'def
  set D : Finset (Finset V) := deltaSetW G X A w with hDdef
  set T : ℝ := 8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
      (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
      (((D.card : ℝ)) / 3) + 16 * (r : ℝ) with hTdef
  -- ### Basic facts
  have hpscard : ({v1, v2} : Finset V).card = 2 := Finset.card_pair_eq_two_iff.mpr hne
  have hpssub : ({v1, v2} : Finset V) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [hv1, hv2]
  have hA'card : A'.card = A.card - 2 := by
    rw [Finset.card_sdiff_of_subset hpssub, hpscard]
  have hA'mem : ∀ x : V, x ∈ A' ↔ (x ∈ A ∧ x ≠ v1 ∧ x ≠ v2) := by
    intro x; rw [hA'def]; simp [Finset.mem_sdiff]
  have hdA' : Disjoint A' ({v1, v2} : Finset V) := by
    rw [hA'def]
    exact (Finset.disjoint_sdiff (s := ({v1, v2} : Finset V)) (t := A)).symm
  have hr2 : 2 ≤ r - 2 := by omega
  have hr2A' : r - 2 ≤ A'.card := by omega
  have hN'eq : N' = Nat.choose A'.card (r - 2) := by
    rw [hN'def, hS'def, Finset.card_powersetCard]
  have hN'pos : 0 < N' := by rw [hN'eq]; exact Nat.choose_pos hr2A'
  have hsubA' : ∀ C ∈ S', C ∪ {v1, v2} ⊆ A := by
    intro C hC
    have hCsub : C ⊆ A' := (Finset.mem_powersetCard.1 hC).1
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact ((hA'mem _).1 (hCsub h)).1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      exacts [hv1, hv2]
  -- Real-order facts used throughout.
  have hn : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast (by omega : 2 ≤ A.card)
  have hn4 : (4 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast (by omega : 4 ≤ A.card)
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 4 ≤ r)
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hnpos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hn1pos : (0 : ℝ) < (A.card : ℝ) - 1 := by linarith
  have hr1pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < ((A.card : ℝ) - 2) * ((A.card : ℝ) - 3) := by
    nlinarith [hn4]
  -- ### Structure of an edge `e ∈ Δ_G(X,A,w)`
  have hedec : ∀ e ∈ D, e ⊆ A ∧ e.card = 2 := by
    intro e he
    rw [hDdef] at he
    unfold deltaSetW at he
    rw [Finset.mem_filter] at he
    obtain ⟨h1, h2, -⟩ := mem_edgeSetIn he.1
    exact ⟨h1.trans (Finset.filter_subset _ _), h2⟩
  -- ### Per-edge counts of candidate sets `C` covering the edge
  have hcount0 : ∀ e ∈ D, v1 ∉ e → v2 ∉ e →
      ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) := by
    intro e heD hv1e hv2e
    have hsubA : e ⊆ A := (hedec e heD).1
    have hcard2 := (hedec e heD).2
    have heA' : e ⊆ A' := by
      intro x hx
      exact (hA'mem x).2 ⟨hsubA hx, fun h => hv1e (h ▸ hx), fun h => hv2e (h ▸ hx)⟩
    have hiff : ∀ C : Finset V, (e ⊆ C ∪ {v1, v2} ↔ e ⊆ C) := by
      intro C
      constructor
      · intro h x hx
        rcases Finset.mem_union.1 (h hx) with h' | h'
        · exact h'
        · exfalso
          simp only [Finset.mem_insert, Finset.mem_singleton] at h'
          rcases h' with rfl | rfl
          exacts [hv1e hx, hv2e hx]
      · intro h y hy
        exact Finset.mem_union_left _ (h hy)
    rw [Finset.filter_congr (fun C _ => hiff C), hS'def]
    have hcard := Finset.card_filter_powersetCard_subset e A' (r - 2) heA'
      (by rw [hcard2]; omega)
    rw [hcard2] at hcard
    exact_mod_cast hcard
  have hcount1 : ∀ e ∈ D, v1 ∈ e → v2 ∉ e →
      ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) := by
    intro e heD hv1e hv2e
    have hsubA : e ⊆ A := (hedec e heD).1
    have hcard2 := (hedec e heD).2
    have hiff : ∀ C : Finset V, (e ⊆ C ∪ {v1, v2} ↔ e.erase v1 ⊆ C) := by
      intro C
      constructor
      · intro h x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx
        rcases Finset.mem_union.1 (h hx2) with h' | h'
        · exact h'
        · exfalso
          simp only [Finset.mem_insert, Finset.mem_singleton] at h'
          rcases h' with rfl | rfl
          · exact hx1 rfl
          · exact hv2e hx2
      · intro h x hx
        by_cases hxv1 : x = v1
        · refine Finset.mem_union_right _ ?_
          rw [hxv1]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_union_left _ (h (Finset.mem_erase.2 ⟨hxv1, hx⟩))
    have hsA' : e.erase v1 ⊆ A' := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx
      exact (hA'mem x).2 ⟨hsubA hx2, hx1, fun h => hv2e (h ▸ hx2)⟩
    have hscard : (e.erase v1).card = 1 := by
      have h1e := Finset.card_erase_of_mem hv1e
      omega
    rw [Finset.filter_congr (fun C _ => hiff C), hS'def]
    have hcard := Finset.card_filter_powersetCard_subset (e.erase v1) A' (r - 2) hsA'
      (by rw [hscard]; omega)
    rw [hscard] at hcard
    exact_mod_cast hcard
  have hcount1' : ∀ e ∈ D, v2 ∈ e → v1 ∉ e →
      ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) := by
    intro e heD hv2e hv1e
    have hsubA : e ⊆ A := (hedec e heD).1
    have hcard2 := (hedec e heD).2
    have hiff : ∀ C : Finset V, (e ⊆ C ∪ {v1, v2} ↔ e.erase v2 ⊆ C) := by
      intro C
      constructor
      · intro h x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx
        rcases Finset.mem_union.1 (h hx2) with h' | h'
        · exact h'
        · exfalso
          simp only [Finset.mem_insert, Finset.mem_singleton] at h'
          rcases h' with rfl | rfl
          · exact hv1e hx2
          · exact hx1 rfl
      · intro h x hx
        by_cases hxv2 : x = v2
        · refine Finset.mem_union_right _ ?_
          rw [hxv2]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · exact Finset.mem_union_left _ (h (Finset.mem_erase.2 ⟨hxv2, hx⟩))
    have hsA' : e.erase v2 ⊆ A' := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx
      exact (hA'mem x).2 ⟨hsubA hx2, fun h => hv1e (h ▸ hx2), hx1⟩
    have hscard : (e.erase v2).card = 1 := by
      have h2e := Finset.card_erase_of_mem hv2e
      omega
    rw [Finset.filter_congr (fun C _ => hiff C), hS'def]
    have hcard := Finset.card_filter_powersetCard_subset (e.erase v2) A' (r - 2) hsA'
      (by rw [hscard]; omega)
    rw [hscard] at hcard
    exact_mod_cast hcard
  have hcount2 : ∀ e ∈ D, v1 ∈ e → v2 ∈ e →
      ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) ≤ ((N' : ℕ) : ℝ) := by
    intro e heD _ _
    have hle := Finset.card_filter_le S' (fun C => e ⊆ C ∪ {v1, v2})
    calc ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) ≤ ((S'.card : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = ((N' : ℕ) : ℝ) := by rw [hN'def]
  -- ### Double counting: sum of `Z C = |Δ_G(X,C∪{v1,v2},w)|` over candidate sets
  have hcardite : ∀ e : Finset V,
      ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        ∑ C ∈ S', (if e ⊆ C ∪ {v1, v2} then (1 : ℝ) else 0) := by
    intro e
    rw [← Finset.sum_filter (p := fun C => e ⊆ C ∪ {v1, v2}) (f := fun _ => (1 : ℝ))]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp
  have hZite : ∀ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) =
      ∑ e ∈ D, (if e ∈ deltaSetW G X (C ∪ {v1, v2}) w then (1 : ℝ) else 0) := by
    intro C hC
    have hsub : deltaSetW G X (C ∪ {v1, v2}) w ⊆ D := deltaSetW_mono G X _ A w (hsubA' C hC)
    have h1 : ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) =
        ∑ e ∈ deltaSetW G X (C ∪ {v1, v2}) w, (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp
    rw [h1]
    have hfun : ∀ e ∈ deltaSetW G X (C ∪ {v1, v2}) w,
        ((1 : ℝ)) = (if e ∈ deltaSetW G X (C ∪ {v1, v2}) w then (1 : ℝ) else 0) := by
      intro e he
      exact (if_pos he).symm
    refine Eq.trans (Finset.sum_congr rfl hfun) ?_
    exact Finset.sum_subset hsub (fun e _ hne => if_neg hne)
  have hswap : ∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤
      ∑ e ∈ D, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) := by
    calc ∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)
        = ∑ C ∈ S', ∑ e ∈ D,
              (if e ∈ deltaSetW G X (C ∪ {v1, v2}) w then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun C hC => hZite C hC)
      _ ≤ ∑ C ∈ S', ∑ e ∈ D, (if e ⊆ C ∪ {v1, v2} then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun C _ => Finset.sum_le_sum (fun e _ => by
            by_cases h : e ∈ deltaSetW G X (C ∪ {v1, v2}) w
            · have hl : (if e ∈ deltaSetW G X (C ∪ {v1, v2}) w then (1 : ℝ) else 0) = 1 :=
                if_pos h
              have hr : (if e ⊆ C ∪ {v1, v2} then (1 : ℝ) else 0) = 1 :=
                if_pos (mem_deltaSetW_subset h)
              rw [hl, hr]
            · have hl : (if e ∈ deltaSetW G X (C ∪ {v1, v2}) w then (1 : ℝ) else 0) = 0 :=
                if_neg h
              have hr : (0 : ℝ) ≤ (if e ⊆ C ∪ {v1, v2} then (1 : ℝ) else 0) := by
                by_cases hs : e ⊆ C ∪ {v1, v2}
                · rw [if_pos hs]; norm_num
                · rw [if_neg hs]
              rw [hl]
              exact hr))
      _ = ∑ e ∈ D, ∑ C ∈ S', (if e ⊆ C ∪ {v1, v2} then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ e ∈ D, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) :=
          Finset.sum_congr rfl (fun e _ => (hcardite e).symm)
  -- ### Partition of `D` by how an edge meets `{v1,v2}`
  set F0 := D.filter (fun e => v1 ∉ e ∧ v2 ∉ e) with hF0
  set F1 := D.filter (fun e => (v1 ∈ e ∧ v2 ∉ e) ∨ (v2 ∈ e ∧ v1 ∉ e)) with hF1
  set F2 := D.filter (fun e => v1 ∈ e ∧ v2 ∈ e) with hF2
  have hd12 : Disjoint F1 F2 := by
    rw [hF1, hF2]
    refine Finset.disjoint_left.mpr (fun a ha hb => ?_)
    have ha' : ((v1 ∈ a ∧ v2 ∉ a) ∨ (v2 ∈ a ∧ v1 ∉ a)) := (Finset.mem_filter.1 ha).2
    have hb' : (v1 ∈ a ∧ v2 ∈ a) := (Finset.mem_filter.1 hb).2
    rcases ha' with h | h
    · exact absurd hb'.2 h.2
    · exact absurd hb'.1 h.2
  have hd02 : Disjoint F0 F2 := by
    rw [hF0, hF2]
    refine Finset.disjoint_left.mpr (fun a ha hb => ?_)
    have ha' : (v1 ∉ a ∧ v2 ∉ a) := (Finset.mem_filter.1 ha).2
    have hb' : (v1 ∈ a ∧ v2 ∈ a) := (Finset.mem_filter.1 hb).2
    exact absurd hb'.1 ha'.1
  have hd01 : Disjoint F0 F1 := by
    rw [hF0, hF1]
    refine Finset.disjoint_left.mpr (fun a ha hb => ?_)
    have ha' : (v1 ∉ a ∧ v2 ∉ a) := (Finset.mem_filter.1 ha).2
    have hb' : ((v1 ∈ a ∧ v2 ∉ a) ∨ (v2 ∈ a ∧ v1 ∉ a)) := (Finset.mem_filter.1 hb).2
    rcases hb' with h | h
    · exact absurd h.1 ha'.1
    · exact absurd h.1 ha'.2
  have hDsplit : ∑ e ∈ D, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
      (∑ e ∈ F0, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) +
       ∑ e ∈ F1, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ)) +
      ∑ e ∈ F2, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) := by
    have hpart : F0 ∪ F1 ∪ F2 = D := by
      ext e
      by_cases h1 : v1 ∈ e <;> by_cases h2 : v2 ∈ e <;>
        simp [hF0, hF1, hF2, h1, h2, Finset.mem_union]
    have hdunion : Disjoint (F0 ∪ F1) F2 := Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩
    rw [← hpart, Finset.sum_union hdunion, Finset.sum_union hd01]
  have hF2card : F2.card ≤ 1 := by
    have hsub : F2 ⊆ ({({v1, v2} : Finset V)} : Finset (Finset V)) := by
      intro e heF
      rw [hF2] at heF
      obtain ⟨heD, hv1e, hv2e⟩ := Finset.mem_filter.1 heF
      have heq : e = {v1, v2} := (Finset.eq_of_subset_of_card_le
        (Finset.insert_subset hv1e (Finset.singleton_subset_iff.2 hv2e))
        (by rw [(hedec e heD).2, hpscard])).symm
      rw [heq]; exact Finset.mem_singleton_self _
    exact (Finset.card_le_card hsub).trans (by simp)
  have hF1card : F1.card ≤ A'.card + A'.card := by
    have hsub : F1 ⊆ (Finset.image (fun s : Finset V => insert v1 s) (A'.powersetCard 1)) ∪
        (Finset.image (fun s : Finset V => insert v2 s) (A'.powersetCard 1)) := by
      intro e heF
      rw [hF1] at heF
      obtain ⟨heD, hx | hx⟩ := Finset.mem_filter.1 heF
      · obtain ⟨hv1e, hv2e⟩ := hx
        refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨e.erase v1, ?_, ?_⟩)
        · rw [Finset.mem_powersetCard]
          refine ⟨fun x hx' => ?_, ?_⟩
          · obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx'
            exact (hA'mem x).2 ⟨(hedec e heD).1 hx2, hx1, fun h => hv2e (h ▸ hx2)⟩
          · have h1e := Finset.card_erase_of_mem hv1e
            have hc := (hedec e heD).2
            omega
        · rw [Finset.insert_erase hv1e]
      · obtain ⟨hv2e, hv1e⟩ := hx
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨e.erase v2, ?_, ?_⟩)
        · rw [Finset.mem_powersetCard]
          refine ⟨fun x hx' => ?_, ?_⟩
          · obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx'
            exact (hA'mem x).2 ⟨(hedec e heD).1 hx2, fun h => hv1e (h ▸ hx2), hx1⟩
          · have h2e := Finset.card_erase_of_mem hv2e
            have hc := (hedec e heD).2
            omega
        · rw [Finset.insert_erase hv2e]
    calc F1.card ≤ ((Finset.image (fun s : Finset V => insert v1 s) (A'.powersetCard 1)) ∪
          (Finset.image (fun s : Finset V => insert v2 s) (A'.powersetCard 1))).card :=
          Finset.card_le_card hsub
      _ ≤ (A'.powersetCard 1).card + (A'.powersetCard 1).card := by
          refine Nat.le_trans (Finset.card_union_le _ _) ?_
          exact Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = A'.card + A'.card := by
          simp [Finset.card_powersetCard, Nat.choose_one_right]
  have hSum : ∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤
      ((D.card : ℕ) : ℝ) * (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) +
      2 * ((A'.card : ℕ) : ℝ) * (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) +
      ((N' : ℕ) : ℝ) := by
    have hb0 : ∀ e ∈ F0, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) := by
      intro e heF
      rw [hF0] at heF
      exact hcount0 e (Finset.mem_filter.1 heF).1
        ((Finset.mem_filter.1 heF).2).1 ((Finset.mem_filter.1 heF).2).2
    have hb1 : ∀ e ∈ F1, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) := by
      intro e heF
      rw [hF1] at heF
      rcases (Finset.mem_filter.1 heF).2 with ⟨hv1e, hv2e⟩ | ⟨hv2e, hv1e⟩
      · exact hcount1 e (Finset.mem_filter.1 heF).1 hv1e hv2e
      · exact hcount1' e (Finset.mem_filter.1 heF).1 hv2e hv1e
    have hb2 : ∀ e ∈ F2, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) ≤
        ((N' : ℕ) : ℝ) := by
      intro e heF
      rw [hF2] at heF
      exact hcount2 e (Finset.mem_filter.1 heF).1
        ((Finset.mem_filter.1 heF).2).1 ((Finset.mem_filter.1 heF).2).2
    refine hswap.trans ?_
    rw [hDsplit]
    have s0 : ∑ e ∈ F0, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        ((F0.card : ℕ) : ℝ) * (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) := by
      rw [Finset.sum_congr rfl (fun e heF => hb0 e heF), Finset.sum_const]
      simp
    have s1 : ∑ e ∈ F1, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) =
        ((F1.card : ℕ) : ℝ) * (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) := by
      rw [Finset.sum_congr rfl (fun e heF => hb1 e heF), Finset.sum_const]
      simp
    have s2 : ∑ e ∈ F2, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) ≤
        ((F2.card : ℕ) : ℝ) * ((N' : ℕ) : ℝ) := by
      calc ∑ e ∈ F2, ((S'.filter (fun C => e ⊆ C ∪ {v1, v2})).card : ℝ) ≤
            ∑ e ∈ F2, ((N' : ℕ) : ℝ) := Finset.sum_le_sum (fun e heF => hb2 e heF)
        _ = ((F2.card : ℕ) : ℝ) * ((N' : ℕ) : ℝ) := by
            rw [Finset.sum_const]; simp
    have hF0card : F0.card ≤ D.card := Finset.card_filter_le D (fun e => v1 ∉ e ∧ v2 ∉ e)
    have hnn4 : (0 : ℝ) ≤ (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) := Nat.cast_nonneg _
    have hnn3 : (0 : ℝ) ≤ (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) := Nat.cast_nonneg _
    have hnnN : (0 : ℝ) ≤ ((N' : ℕ) : ℝ) := Nat.cast_nonneg _
    have hF0c : ((F0.card : ℕ) : ℝ) ≤ ((D.card : ℕ) : ℝ) := by exact_mod_cast hF0card
    have hF1c : ((F1.card : ℕ) : ℝ) ≤ ((A'.card : ℕ) : ℝ) + ((A'.card : ℕ) : ℝ) := by
      exact_mod_cast hF1card
    have hF2c : ((F2.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hF2card
    nlinarith [s0, s1, s2, hF0c, hF1c, hF2c, hnn4, hnn3, hnnN,
      mul_le_mul_of_nonneg_left hF0c hnn4,
      mul_le_mul_of_nonneg_left hF1c hnn3,
      mul_le_mul_of_nonneg_left hF2c hnnN]
  -- ### Choose identities
  have hI3 : ((A'.card : ℕ) : ℝ) * (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) =
      ((N' : ℕ) : ℝ) * ((r : ℝ) - 2) := by
    have hch := Nat.choose_mul (n := A'.card) (k := r - 2) (s := 1) (by omega)
    rw [Nat.choose_one_right, Nat.choose_one_right] at hch
    rw [hN'eq]
    have hc := congrArg (Nat.cast (R := ℝ)) hch
    rw [Nat.cast_mul, Nat.cast_mul] at hc
    have hrc : (((r - 2 : ℕ) : ℝ)) = ((r : ℝ) - 2) := Nat.cast_sub (by omega)
    rw [hrc] at hc
    linarith
  have hI4 : (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
      (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) =
      ((N' : ℕ) : ℝ) * (((r : ℝ) - 2) * ((r : ℝ) - 3)) := by
    have hch := Nat.choose_mul (n := A'.card) (k := r - 2) (s := 2) hr2
    have hc := congrArg (Nat.cast (R := ℝ)) hch
    rw [Nat.cast_mul, Nat.cast_mul] at hc
    rw [Nat.cast_choose_two ℝ, Nat.cast_choose_two ℝ] at hc
    have hrc : (((r - 2 : ℕ) : ℝ)) = ((r : ℝ) - 2) := Nat.cast_sub (by omega)
    have hA'c : ((A'.card : ℕ) : ℝ) = ((A.card : ℝ) - 2) := by
      rw [hA'card, Nat.cast_sub (by omega : 2 ≤ A.card)]
      norm_num
    rw [hrc, hA'c] at hc
    have hX : (((r : ℝ) - 2) - 1) = ((r : ℝ) - 3) := by ring
    have hY : (((A.card : ℝ) - 2) - 1) = ((A.card : ℝ) - 3) := by ring
    rw [hX, hY] at hc
    rw [hN'eq]
    field_simp at hc ⊢
    linarith
  -- ### The multiplied sum bound and Markov's inequality
  have hSumMul : (∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)) *
      (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) ≤
      ((N' : ℕ) : ℝ) * ((((r : ℝ) - 2) * ((r : ℝ) - 3)) * ((D.card : ℝ)) +
        2 * ((r : ℝ)) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3))) := by
    have hPnn : (0 : ℝ) ≤ ((A.card : ℝ) - 2) * ((A.card : ℝ) - 3) := le_of_lt hdpos
    have hstep := mul_le_mul_of_nonneg_right hSum hPnn
    have hN'nn : (0 : ℝ) ≤ ((N' : ℕ) : ℝ) := Nat.cast_nonneg _
    have hQnn : (0 : ℝ) ≤ ((r : ℝ) - 2) * ((r : ℝ) - 3) := by nlinarith [hr4]
    have h3r : (3 : ℝ) ≤ 2 * ((r : ℝ)) := by linarith
    have e1 : (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
        (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) * ((D.card : ℝ)) =
        ((N' : ℕ) : ℝ) * (((r : ℝ) - 2) * ((r : ℝ) - 3)) * ((D.card : ℝ)) :=
      congrArg (fun z : ℝ => z * ((D.card : ℝ))) hI4
    have e2 : ((A'.card : ℕ) : ℝ) * (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ) *
        (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) =
        ((N' : ℕ) : ℝ) * ((r : ℝ) - 2) *
        (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) :=
      congrArg (fun z : ℝ => z * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3))) hI3
    have hstep' : (∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)) *
        (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) ≤
        ((D.card : ℝ)) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
          (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) +
        2 * (((A'.card : ℕ) : ℝ) * (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ)) *
          (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) +
        ((N' : ℕ) : ℝ) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) := by
      linear_combination hstep
    have h7 : ((D.card : ℝ)) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
        (Nat.choose (A'.card - 2) (r - 2 - 2) : ℝ) =
        ((N' : ℕ) : ℝ) * (((r : ℝ) - 2) * ((r : ℝ) - 3)) * ((D.card : ℝ)) := by
      rw [← e1]; ring
    have h8 : 2 * (((A'.card : ℕ) : ℝ) * (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ)) *
        (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) +
        ((N' : ℕ) : ℝ) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) ≤
        2 * ((N' : ℕ) : ℝ) * ((r : ℝ)) *
        (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) := by
      have hconv : 2 * (((A'.card : ℕ) : ℝ) *
          (Nat.choose (A'.card - 1) (r - 2 - 1) : ℝ)) *
          (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) =
          2 * ((N' : ℕ) : ℝ) * ((r : ℝ) - 2) *
          (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) := by
        have hI3m := congrArg
          (fun z : ℝ => 2 * z * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3))) hI3
        linarith [hI3m]
      rw [hconv]
      nlinarith [hN'nn, hPnn, hrpos, h3r]
    nlinarith [hstep', h7, h8]
  have hTP : T * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) =
      8 / 3 * (((r : ℝ) - 2) * ((r : ℝ) - 3)) * ((D.card : ℝ)) +
        16 * ((r : ℝ)) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) := by
    have hdne : (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) ≠ 0 := ne_of_gt hdpos
    have key1 : (8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
        (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) * (((D.card : ℝ)) / 3)) *
        (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) =
        8 / 3 * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((D.card : ℝ)) := by
      have h1 : 8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
          (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
          (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) =
          8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) :=
        div_mul_cancel₀ _ hdne
      linear_combination ((D.card : ℝ)) / 3 * h1
    rw [hTdef]
    linear_combination key1
  have h2E : (2 : ℝ) * ((((r : ℝ) - 2) * ((r : ℝ) - 3)) * ((D.card : ℝ)) +
      2 * ((r : ℝ)) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3))) ≤
      T * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) := by
    rw [hTP]
    have hQnn : (0 : ℝ) ≤ ((r : ℝ) - 2) * ((r : ℝ) - 3) := by nlinarith [hr4]
    have hmnn : (0 : ℝ) ≤ ((D.card : ℝ)) := Nat.cast_nonneg _
    field_simp
    nlinarith [hQnn, hmnn, hrpos, hdpos]
  set bad : ℕ := (S'.filter
    (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ))).card with hbaddef
  have hMark : ((bad : ℕ) : ℝ) * T ≤
      ∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) := by
    have h1 : ∑ C ∈ S'.filter
          (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)), T =
        ((S'.filter (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ))).card : ℝ) * T := by
      rw [Finset.sum_const]
      simp
    have h2 : ∑ C ∈ S'.filter
          (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)), T ≤
        ∑ C ∈ S'.filter (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)),
          ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) :=
      Finset.sum_le_sum (fun C hC => (Finset.mem_filter.1 hC).2.le)
    have h3 : ∑ C ∈ S'.filter
          (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)),
          ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤
        ∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) := by
      have hs := Finset.sum_filter_add_sum_filter_not
        (f := fun C => ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)) (s := S')
        (p := fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ))
      have hnn : ∀ C ∈ S'.filter
          (fun C => ¬ (T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ))),
          (0 : ℝ) ≤ ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) :=
        fun C _ => Nat.cast_nonneg _
      have h4 := Finset.sum_nonneg hnn
      linarith
    calc ((bad : ℕ) : ℝ) * T = ((S'.filter
          (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ))).card : ℝ) * T := by
          rw [hbaddef]
      _ = ∑ C ∈ S'.filter
            (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)), T := h1.symm
      _ ≤ ∑ C ∈ S'.filter (fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)),
            ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) := h2
      _ ≤ ∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) := h3
  have hTPpos : (0 : ℝ) < T * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) := by
    have hTpos : (0 : ℝ) < T := by
      rw [hTdef]
      have hQnn : (0 : ℝ) ≤ ((r : ℝ) - 2) * ((r : ℝ) - 3) := by nlinarith [hr4]
      have hmnn : (0 : ℝ) ≤ ((D.card : ℝ)) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ 8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
          (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) * (((D.card : ℝ)) / 3) := by
        apply mul_nonneg _ (div_nonneg (Nat.cast_nonneg _) (by norm_num))
        exact div_nonneg (by nlinarith [hr4]) (le_of_lt hdpos)
      linarith
    exact mul_pos hTpos hdpos
  have hbadhalfR : (2 : ℝ) * ((bad : ℕ) : ℝ) ≤ ((N' : ℕ) : ℝ) := by
    have hN'nn : (0 : ℝ) ≤ ((N' : ℕ) : ℝ) := Nat.cast_nonneg _
    have hPnn : (0 : ℝ) ≤ ((A.card : ℝ) - 2) * ((A.card : ℝ) - 3) := le_of_lt hdpos
    have e0 : ((bad : ℕ) : ℝ) * (T * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3))) ≤
        (∑ C ∈ S', ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ)) *
          (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) := by
      nlinarith [hMark, mul_le_mul_of_nonneg_right hMark hPnn]
    have e0' := e0.trans hSumMul
    have e2 : (2 : ℝ) * (((N' : ℕ) : ℝ) * ((((r : ℝ) - 2) * ((r : ℝ) - 3)) *
          ((D.card : ℝ)) + 2 * ((r : ℝ)) * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)))) ≤
        ((N' : ℕ) : ℝ) * (T * (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3))) := by
      have hmul := mul_le_mul_of_nonneg_left h2E hN'nn
      nlinarith [hmul]
    nlinarith [e0', e2, hTPpos, hN'nn]
  have hbad2 : 2 * bad ≤ N' := by
    have hcast : (((2 * bad : ℕ) : ℝ)) ≤ ((N' : ℕ) : ℝ) := by
      push_cast
      exact hbadhalfR
    exact Nat.cast_le.mp hcast
  have hbadle : bad ≤ N' := by omega
  -- ### The bijection between good `B` and good `C`
  have hgoodcount :
      (S'.filter (fun C => ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤ T)).card =
        N' - bad := by
    have hfil : S'.filter (fun C => ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤ T) =
        S'.filter (fun C => ¬ (T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ))) :=
      Finset.filter_congr (fun C _ => (not_lt (a := T)).symm)
    rw [hfil, hbaddef, hN'def]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S') (p := fun C => T < ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ))
    omega
  have hbij :
      ((A.powersetCard r).filter
        (fun B => ({v1, v2} : Finset V) ⊆ B ∧
          ((deltaSetW G X B w).card : ℝ) ≤ T)).card =
      (S'.filter (fun C => ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤ T)).card := by
    have hsplit : (A.powersetCard r).filter (fun B => ({v1, v2} : Finset V) ⊆ B) =
        (A'.powersetCard (r - 2)).image (fun C => C ∪ {v1, v2}) := by
      have h := Finset.filter_powersetCard_subset ({v1, v2} : Finset V) A r hpssub
        (by rw [hpscard]; omega)
      rw [← hA'def, hpscard] at h
      exact h
    have hfil : (A.powersetCard r).filter
        (fun B => ({v1, v2} : Finset V) ⊆ B ∧
          ((deltaSetW G X B w).card : ℝ) ≤ T) =
        ((A.powersetCard r).filter (fun B => ({v1, v2} : Finset V) ⊆ B)).filter
          (fun B => ((deltaSetW G X B w).card : ℝ) ≤ T) := by
      ext B
      simp only [Finset.mem_filter]
      tauto
    rw [hfil, hsplit]
    have hfi : ((A'.powersetCard (r - 2)).image (fun C => C ∪ {v1, v2})).filter
        (fun B => ((deltaSetW G X B w).card : ℝ) ≤ T) =
        ((A'.powersetCard (r - 2)).filter
          (fun C => ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤ T)).image
          (fun C => C ∪ {v1, v2}) := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · intro h
        obtain ⟨hmem, hQ⟩ := h
        obtain ⟨C, hC, hBeq⟩ := hmem
        have hQC : ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤ T := by
          rw [hBeq]; exact hQ
        exact ⟨C, ⟨hC, hQC⟩, hBeq⟩
      · intro h
        obtain ⟨C, hC, hBeq⟩ := h
        obtain ⟨hCpow, hQC⟩ := hC
        have hQB : ((deltaSetW G X B w).card : ℝ) ≤ T := by
          rw [← hBeq]; exact hQC
        exact ⟨⟨C, hCpow, hBeq⟩, hQB⟩
    have hinj : Set.InjOn (fun C => C ∪ {v1, v2})
        (↑((A'.powersetCard (r - 2)).filter
          (fun C => ((deltaSetW G X (C ∪ {v1, v2}) w).card : ℝ) ≤ T)) :
          Set (Finset V)) := by
      intro C₁ hC₁ C₂ hC₂ hEq
      have hd1 : C₁ ⊆ A' := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hC₁).1).1
      have hd2 : C₂ ⊆ A' := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hC₂).1).1
      calc C₁ = (C₁ ∪ {v1, v2}) \ {v1, v2} :=
            (Finset.union_sdiff_cancel_right
              (Finset.disjoint_of_subset_left hd1 hdA')).symm
        _ = (C₂ ∪ {v1, v2}) \ {v1, v2} := by
              rw [show (C₁ ∪ {v1, v2}) = (C₂ ∪ {v1, v2}) from hEq]
        _ = C₂ := Finset.union_sdiff_cancel_right
              (Finset.disjoint_of_subset_left hd2 hdA')
    rw [hfi, Finset.card_image_of_injOn hinj, hS'def]
  -- ### Final assembly
  rw [subsetProb]
  rw [Finset.filter_congr_decidable]
  rw [hbij, hgoodcount, Finset.card_powersetCard]
  have hCpos : (0 : ℝ) < (Nat.choose A.card r : ℝ) := by
    exact_mod_cast Nat.choose_pos hrA
  have hchoose := Nat.choose_mul (n := A.card) (k := r) (s := 2) (by omega)
  have hcast : ((Nat.choose A.card r : ℝ) * (Nat.choose r 2 : ℝ)) =
      ((Nat.choose A.card 2 : ℝ) * (Nat.choose (A.card - 2) (r - 2) : ℝ)) := by
    exact_mod_cast hchoose
  rw [Nat.cast_choose_two ℝ, Nat.cast_choose_two ℝ] at hcast
  have hN'ch : ((N' : ℕ) : ℝ) = (Nat.choose (A.card - 2) (r - 2) : ℝ) := by
    rw [hN'eq, hA'card]
  have h2eq : ((Nat.choose A.card r : ℝ)) * (((r : ℝ)) * (((r : ℝ)) - 1)) =
      ((A.card : ℝ)) * (((A.card : ℝ)) - 1) *
        (Nat.choose (A.card - 2) (r - 2) : ℝ) := by
    have h3 : (2 : ℝ) * (((Nat.choose A.card r : ℝ)) * (((r : ℝ)) * (((r : ℝ)) - 1))) =
        (2 : ℝ) * (((A.card : ℝ)) * (((A.card : ℝ)) - 1) *
          (Nat.choose (A.card - 2) (r - 2) : ℝ)) := by
      field_simp at hcast ⊢
      linarith
    linarith
  have hratioN : ((N' : ℕ) : ℝ) / ((Nat.choose A.card r : ℝ)) =
      (((r : ℝ)) * (((r : ℝ)) - 1)) / (((A.card : ℝ)) * (((A.card : ℝ)) - 1)) := by
    rw [div_eq_div_iff (ne_of_gt hCpos)
      (mul_ne_zero (ne_of_gt hnpos) (ne_of_gt hn1pos))]
    have hmul := congrArg (fun z : ℝ => z * (((A.card : ℝ)) * (((A.card : ℝ)) - 1))) hN'ch
    linarith [hmul, h2eq]
  have hge2 : ((2 : ℝ)) * (((N' - bad : ℕ) : ℝ)) ≥ ((N' : ℕ) : ℝ) := by
    have h1 : (((N' - bad : ℕ) : ℝ)) = ((N' : ℕ) : ℝ) - ((bad : ℕ) : ℝ) := by
      rw [Nat.cast_sub hbadle]
    rw [h1]
    linarith
  have key : ((r : ℝ) - 1) ^ 2 / ((A.card : ℝ) ^ 2) ≤
      ((N' : ℕ) : ℝ) / ((Nat.choose A.card r : ℝ)) := by
    rw [hratioN]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hr1pos, hn1pos, hn]
  calc ((r : ℝ) - 1) ^ 2 / (2 * (A.card : ℝ) ^ 2) =
        (((r : ℝ) - 1) ^ 2 / ((A.card : ℝ) ^ 2)) / 2 := by
        field_simp
    _ ≤ (((N' : ℕ) : ℝ) / ((Nat.choose A.card r : ℝ))) / 2 := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
        linarith [key]
    _ ≤ (((N' - bad : ℕ) : ℝ)) / ((Nat.choose A.card r : ℝ)) := by
        have hstep : (((N' : ℕ) : ℝ) / ((Nat.choose A.card r : ℝ))) / 2 *
            ((Nat.choose A.card r : ℝ)) = ((N' : ℕ) : ℝ) / 2 := by
          field_simp
        rw [le_div_iff₀ hCpos, hstep]
        linarith

end Qatlib.Papers.TriangleFind14.MainResults
