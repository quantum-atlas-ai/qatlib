/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.SourceModel

/-!
# Bijection Between Yamanouchi Words and Standard Young Tableaux

This module proves Proposition 1 of Larocca and Havlicek: for any Young diagram $\lambda$,
the set of Yamanouchi (ballot) words of content $\lambda$ is in bijection with the set of
standard Young tableaux of shape $\lambda$.

## Main statements

* `proposition1_bijection`: Explicit equivalence `YamanouchiWord lam ≃ StandardYoungTableau lam`
  for every Young diagram `lam`.

## References

* [Larocca and Havlicek, 2025][LaroccaHavlicek2025]
-/

set_option autoImplicit false

namespace Qatlib.Papers.RepMultiplic24.MainResults

open scoped BigOperators

private lemma prefix_count_mono (w : List ℕ) (a : ℕ) {j k : ℕ} (h : j ≤ k) :
    (w.take j).count a ≤ (w.take k).count a := by
  have hsub : w.take j = (w.take k).take j := by simp [List.take_take, Nat.min_eq_left h]
  rw [hsub]
  exact List.IsPrefix.count_le a (List.take_prefix ..)

private lemma prefix_count_step (w : List ℕ) {t : ℕ} (ht : t < w.length) :
    (w.take (t + 1)).count w[t] = (w.take t).count w[t] + 1 := by
  have heq := List.take_succ_eq_append_getElem ht
  exact congrArg (List.count w[t]) heq |>.trans (by
    simp only [List.count_append, List.count_singleton_self])

private lemma prefix_count_lt (w : List ℕ) {t : ℕ} (ht : t < w.length) :
    (w.take t).count w[t] < w.count w[t] := by
  have h := prefix_count_mono w w[t] (Nat.succ_le_of_lt ht)
  rw [List.take_length, prefix_count_step w ht] at h
  omega

private lemma count_ofFn {n : ℕ} (f : Fin n → ℕ) (a : ℕ) :
    (List.ofFn f).count a = (Finset.univ.filter (fun t => f t = a)).card := by
  rw [Finset.card_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq]
    omega

private lemma count_take_ofFn {n : ℕ} (f : Fin n → ℕ) (a j : ℕ) :
    ((List.ofFn f).take j).count a =
      (Finset.univ.filter (fun t => t.val < j ∧ f t = a)).card := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hj : j < n
    · rw [List.take_succ_eq_append_getElem (by simpa using hj), List.count_append, ih]
      have hset : (Finset.univ.filter (fun t : Fin n => t.val < j + 1 ∧ f t = a)) =
          (Finset.univ.filter (fun t => t.val < j ∧ f t = a)) ∪
            (if f ⟨j, hj⟩ = a then {⟨j, hj⟩} else ∅) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · rintro ⟨ht, hf⟩
          by_cases hlt : t.val < j
          · exact Or.inl ⟨hlt, hf⟩
          · have he : t = ⟨j, hj⟩ := Fin.ext (show t.val = j by omega)
            right
            rw [← he, ite_eq_left hf]
            exact Finset.mem_singleton_self t
        · rintro (⟨ht, hf⟩ | hm)
          · exact ⟨by omega, hf⟩
          · split_ifs at hm with hf
            · have he := Finset.mem_singleton.1 hm
              subst t
              exact ⟨by simp, hf⟩
            · exact False.elim (Finset.notMem_empty _ hm)
      rw [hset, Finset.card_union_of_disjoint]
      · simp only [List.getElem_ofFn, List.count_singleton, beq_iff_eq]
        split_ifs <;> simp
      · simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
        intro t ht
        split_ifs
        · intro he
          have he' := Finset.mem_singleton.1 he
          have hbad := ht.1
          rw [he'] at hbad
          exact (lt_irrefl j) hbad
        · exact Finset.notMem_empty t
    · rw [List.take_of_length_le (by simpa using (by omega : n ≤ j + 1)), count_ofFn]
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := t.isLt
      omega

private noncomputable def entryEquiv {lam : YoungDiagram} (T : StandardYoungTableau lam) :
    Cell lam ≃ Fin lam.cells.card :=
  Equiv.ofBijective T.entry ((Fintype.bijective_iff_injective_and_card _).2
    ⟨T.injective, by simp [Cell]⟩)

private noncomputable def tableauList {lam : YoungDiagram} (T : StandardYoungTableau lam) :
    List ℕ := List.ofFn (fun t => ((entryEquiv T).symm t).val.1 + 1)

private lemma tableau_count_prefix {lam : YoungDiagram} (T : StandardYoungTableau lam)
    (j i : ℕ) :
    ((tableauList T).take j).count (i + 1) =
      (Finset.univ.filter (fun c : Cell lam => (T.entry c).val < j ∧ c.val.1 = i)).card := by
  classical
  rw [tableauList, count_take_ofFn]
  apply Finset.card_equiv (entryEquiv T).symm
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.add_right_cancel_iff]
  have he : T.entry ((entryEquiv T).symm t) = t := (entryEquiv T).apply_symm_apply t
  rw [he]

private lemma row_prefix_card (lam : YoungDiagram) (i k : ℕ) (hk : k ≤ lam.rowLen i) :
    (Finset.univ.filter (fun c : Cell lam => c.val.1 = i ∧ c.val.2 < k)).card = k := by
  classical
  calc
    _ = (Finset.range k).card := by
      apply Finset.card_bij (fun c _ => c.val.2)
      · intro c hc
        exact Finset.mem_range.2 (Finset.mem_filter.1 hc).2.2
      · intro c hc d hd h
        apply Subtype.ext
        exact Prod.ext ((Finset.mem_filter.1 hc).2.1.trans
          (Finset.mem_filter.1 hd).2.1.symm) h
      · intro col hcol
        have hmem : (i, col) ∈ lam.cells :=
          YoungDiagram.mem_iff_lt_rowLen.2 ((Finset.mem_range.1 hcol).trans_le hk)
        exact ⟨⟨(i, col), hmem⟩, by simp [Finset.mem_range.1 hcol], rfl⟩
    _ = k := Finset.card_range k

private lemma tableau_count {lam : YoungDiagram} (T : StandardYoungTableau lam) (i : ℕ) :
    (tableauList T).count (i + 1) = lam.rowLen i := by
  classical
  have h := tableau_count_prefix T lam.cells.card i
  rw [List.take_of_length_le (by simp [tableauList])] at h
  rw [h, ← row_prefix_card lam i (lam.rowLen i) le_rfl]
  congr 1
  ext c
  have hc := YoungDiagram.mem_iff_lt_rowLen.1 c.property
  have ht := (T.entry c).isLt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hrow⟩
    exact ⟨hrow, hrow ▸ hc⟩
  · exact fun hrow => ⟨ht, hrow.1⟩

private lemma tableau_ballot {lam : YoungDiagram} (T : StandardYoungTableau lam)
    (j i : ℕ) :
    ((tableauList T).take j).count (i + 2) ≤
      ((tableauList T).take j).count (i + 1) := by
  classical
  rw [show i + 2 = (i + 1) + 1 from rfl, tableau_count_prefix, tableau_count_prefix]
  let f : {c : Cell lam // (T.entry c).val < j ∧ c.val.1 = i + 1} →
      {c : Cell lam // (T.entry c).val < j ∧ c.val.1 = i} := fun c => by
    have hr := c.property.2
    have hm : (i, c.val.val.2) ∈ lam.cells :=
      lam.up_left_mem (i2 := c.val.val.1) (j2 := c.val.val.2) (by omega) le_rfl c.val.property
    refine ⟨⟨(i, c.val.val.2), hm⟩, ?_, rfl⟩
    have hlt : (T.entry ⟨(i, c.val.val.2), hm⟩).val < (T.entry c.val).val :=
      T.col_mono ⟨(i, c.val.val.2), hm⟩ c.val rfl (by dsimp; omega)
    exact hlt.trans c.property.1
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact c.property.2.trans d.property.2.symm
    · have hc := congrArg (fun x => x.val.val.2) h
      exact hc
  simpa only [Fintype.card_subtype] using Fintype.card_le_of_injective f hf

private noncomputable def tableauToWord {lam : YoungDiagram} (T : StandardYoungTableau lam) :
    YamanouchiWord lam := by
  refine ⟨tableauList T, by simp [tableauList], ⟨?_, ?_⟩, tableau_count T⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hx
    exact Nat.succ_pos _
  · intro j _ i
    exact tableau_ballot T j i

-- A position determines its row by its letter and its column by its occurrence number.
private def wordCell {lam : YoungDiagram} (W : YamanouchiWord lam)
    (t : Fin lam.cells.card) : Cell lam := by
  have ht : t.val < W.val.length := by simpa only [W.property.1] using t.isLt
  have ha := W.property.2.1.1 _ (List.getElem_mem ht)
  refine ⟨(W.val[t.val] - 1, (W.val.take t.val).count W.val[t.val]), ?_⟩
  apply YoungDiagram.mem_iff_lt_rowLen.2
  have h := prefix_count_lt W.val ht
  have hc := W.property.2.2 (W.val[t.val] - 1)
  rw [Nat.sub_add_cancel ha] at hc
  omega

private lemma wordCell_letter {lam : YoungDiagram} (W : YamanouchiWord lam)
    (t : Fin lam.cells.card) :
    W.val[t.val]'(by simpa only [W.property.1] using t.isLt) = (wordCell W t).val.1 + 1 := by
  have ht : t.val < W.val.length := by simpa only [W.property.1] using t.isLt
  have ha := W.property.2.1.1 _ (List.getElem_mem ht)
  change W.val[t.val] = W.val[t.val] - 1 + 1
  omega

private lemma wordCell_rank {lam : YoungDiagram} (W : YamanouchiWord lam)
    (t : Fin lam.cells.card) :
    (W.val.take t.val).count ((wordCell W t).val.1 + 1) = (wordCell W t).val.2 := by
  rw [← wordCell_letter W t]
  rfl

private lemma wordCell_injective {lam : YoungDiagram} (W : YamanouchiWord lam) :
    Function.Injective (wordCell W) := by
  intro s t h
  have hs : s.val < W.val.length := by simpa only [W.property.1] using s.isLt
  have ht : t.val < W.val.length := by simpa only [W.property.1] using t.isLt
  have hr : W.val[s.val] = W.val[t.val] := by
    rw [wordCell_letter W s, wordCell_letter W t, h]
  have hc : (W.val.take s.val).count W.val[s.val] =
      (W.val.take t.val).count W.val[s.val] := by
    simpa only [← wordCell_letter W s, ← wordCell_letter W t, ← hr] using
      (wordCell_rank W s).trans ((congrArg (fun c : Cell lam => c.val.2) h).trans
        (wordCell_rank W t).symm)
  apply Fin.ext
  rcases lt_trichotomy s.val t.val with hst | hst | hst
  · have hm := prefix_count_mono W.val W.val[s.val] (Nat.succ_le_of_lt hst)
    rw [prefix_count_step W.val hs] at hm
    omega
  · exact hst
  · have hm := prefix_count_mono W.val W.val[t.val] (Nat.succ_le_of_lt hst)
    rw [prefix_count_step W.val ht, ← hr] at hm
    omega

private noncomputable def wordCellEquiv {lam : YoungDiagram} (W : YamanouchiWord lam) :
    Fin lam.cells.card ≃ Cell lam :=
  Equiv.ofBijective (wordCell W) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨wordCell_injective W, by simp [Cell]⟩)

private lemma wordCell_symm {lam : YoungDiagram} (W : YamanouchiWord lam) (c : Cell lam) :
    wordCell W ((wordCellEquiv W).symm c) = c :=
  (wordCellEquiv W).apply_symm_apply c

private lemma wordCell_row_order {lam : YoungDiagram} (W : YamanouchiWord lam)
    (s t : Fin lam.cells.card) (hr : (wordCell W s).val.1 = (wordCell W t).val.1)
    (hc : (wordCell W s).val.2 < (wordCell W t).val.2) : s < t := by
  by_contra hn
  have hm := prefix_count_mono W.val ((wordCell W s).val.1 + 1)
    (show t.val ≤ s.val from le_of_not_gt hn)
  rw [wordCell_rank, hr, wordCell_rank] at hm
  omega

private lemma wordCell_col_order {lam : YoungDiagram} (W : YamanouchiWord lam)
    (s t : Fin lam.cells.card) (hc : (wordCell W s).val.2 = (wordCell W t).val.2)
    (hr : (wordCell W s).val.1 < (wordCell W t).val.1) : s < t := by
  have ht : t.val < W.val.length := by simpa only [W.property.1] using t.isLt
  by_contra hn
  have hne : t ≠ s := by
    intro he
    subst t
    exact (lt_irrefl _ hr)
  have hts : t.val + 1 ≤ s.val := by
    have : t.val ≠ s.val := fun he => hne (Fin.ext he)
    have : t.val ≤ s.val := le_of_not_gt hn
    omega
  have hanti : Antitone (fun i => (W.val.take (t.val + 1)).count (i + 1)) := by
    apply antitone_nat_of_succ_le
    intro i
    exact W.property.2.1.2 (t.val + 1) (by omega) i
  have hb := hanti (Nat.le_of_lt hr)
  dsimp only at hb
  have hm := prefix_count_mono W.val ((wordCell W s).val.1 + 1) hts
  have he := prefix_count_step W.val ht
  rw [wordCell_letter W t, wordCell_rank] at he
  rw [wordCell_rank] at hm
  omega

private noncomputable def wordToTableau {lam : YoungDiagram} (W : YamanouchiWord lam) :
    StandardYoungTableau lam where
  entry := (wordCellEquiv W).symm
  injective := (wordCellEquiv W).symm.injective
  row_mono c d hr hc := by
    apply wordCell_row_order W
    · simpa only [wordCell_symm] using hr
    · simpa only [wordCell_symm] using hc
  col_mono c d hc hr := by
    apply wordCell_col_order W
    · simpa only [wordCell_symm] using hc
    · simpa only [wordCell_symm] using hr

private lemma word_tableau_word {lam : YoungDiagram} (W : YamanouchiWord lam) :
    tableauToWord (wordToTableau W) = W := by
  have he : entryEquiv (wordToTableau W) = (wordCellEquiv W).symm := by
    ext c
    rfl
  apply Subtype.ext
  apply List.ext_getElem
  · simp [tableauToWord, tableauList, W.property.1]
  · intro t ht hw
    have htN : t < lam.cells.card := by simpa only [W.property.1] using hw
    change (List.ofFn (fun s => ((entryEquiv (wordToTableau W)).symm s).val.1 + 1))[t] = _
    simp only [List.getElem_ofFn, he, Equiv.symm_symm]
    exact (wordCell_letter W ⟨t, htN⟩).symm

private lemma tableau_rank {lam : YoungDiagram} (T : StandardYoungTableau lam) (c : Cell lam) :
    ((tableauList T).take (T.entry c).val).count (c.val.1 + 1) = c.val.2 := by
  classical
  rw [tableau_count_prefix]
  rw [← row_prefix_card lam c.val.1 c.val.2
    (Nat.le_of_lt (YoungDiagram.mem_iff_lt_rowLen.1 c.property))]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht, hr⟩
    refine ⟨hr, ?_⟩
    by_contra hn
    rcases eq_or_lt_of_le (Nat.le_of_not_gt hn) with he | hlt
    · have hcd : c = d := Subtype.ext (Prod.ext hr.symm he)
      subst d
      exact (lt_irrefl _ ht)
    · have htc : (T.entry c).val < (T.entry d).val := T.row_mono c d hr.symm hlt
      omega
  · rintro ⟨hr, hc⟩
    exact ⟨T.row_mono d c hr hc, hr⟩

private lemma wordCell_tableau_entry {lam : YoungDiagram} (T : StandardYoungTableau lam)
    (c : Cell lam) : wordCell (tableauToWord T) (T.entry c) = c := by
  have hletter : (tableauList T)[(T.entry c).val]'(by simp [tableauList]) = c.val.1 + 1 := by
    change (List.ofFn (fun t => ((entryEquiv T).symm t).val.1 + 1))[(T.entry c).val] = _
    rw [List.getElem_ofFn]
    have he : (entryEquiv T).symm (T.entry c) = c := (entryEquiv T).symm_apply_apply c
    rw [he]
  have ht : (T.entry c).val < (tableauList T).length := by simp [tableauList]
  apply Subtype.ext
  apply Prod.ext
  · change (tableauList T)[(T.entry c).val] - 1 = c.val.1
    rw [hletter]
    omega
  · change ((tableauList T).take (T.entry c).val).count
      (tableauList T)[(T.entry c).val] = c.val.2
    rw [hletter]
    exact tableau_rank T c

private lemma tableau_ext {lam : YoungDiagram} (S T : StandardYoungTableau lam)
    (h : S.entry = T.entry) : S = T := by
  cases S
  cases T
  cases h
  rfl

private lemma tableau_word_tableau {lam : YoungDiagram} (T : StandardYoungTableau lam) :
    wordToTableau (tableauToWord T) = T := by
  have hentry : (wordToTableau (tableauToWord T)).entry = T.entry := by
    funext c
    apply (wordCellEquiv (tableauToWord T)).injective
    exact (wordCell_symm (tableauToWord T) c).trans (wordCell_tableau_entry T c).symm
  exact tableau_ext _ _ hentry

/-- **Proposition 1** [LaroccaHavlicek2025]: for every Young diagram `lam`, the Yamanouchi
words of type `lam` are in bijection with the standard Young tableaux of shape `lam`. -/
theorem proposition1_bijection (lam : YoungDiagram) :
    Nonempty (YamanouchiWord lam ≃ StandardYoungTableau lam) := by
  classical
  exact ⟨{
    toFun := wordToTableau
    invFun := tableauToWord
    left_inv := word_tableau_word
    right_inv := tableau_word_tableau
  }⟩

end Qatlib.Papers.RepMultiplic24.MainResults
