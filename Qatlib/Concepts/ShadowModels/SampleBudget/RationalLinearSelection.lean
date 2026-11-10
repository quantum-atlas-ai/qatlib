/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
set_option warningAsError false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.SampleBudget

def qInsertCounted (x : ℚ) : List ℚ → List ℚ × ℕ
  | [] => ([x],0)
  | y::ys => if x ≤ y then (x::y::ys,1) else
      let t := qInsertCounted x ys
      (y::t.1,t.2+1)
def qSortCounted : List ℚ → List ℚ × ℕ
  | [] => ([],0)
  | x::xs => let t := qSortCounted xs
             let u := qInsertCounted x t.1
             (u.1,t.2+u.2)
def qChunks5 : ℕ → List ℚ → List (List ℚ)
  | 0,_ => []
  | _+1,[] => []
  | f+1,x::xs => (x::xs).take 5 :: qChunks5 f ((x::xs).drop 5)
def qPartition (p : ℚ) (xs : List ℚ) : List ℚ × List ℚ × List ℚ × ℕ :=
  xs.foldl (fun z x => if x < p then (x::z.1,z.2.1,z.2.2.1,z.2.2.2+1) else
    if p < x then (z.1,z.2.1,x::z.2.2.1,z.2.2.2+2) else
      (z.1,x::z.2.1,z.2.2.1,z.2.2.2+2)) ([],[],[],0)
def qSelectFuel : ℕ → List ℚ → ℕ → ℚ × ℕ
  | 0,xs,k => let z := qSortCounted xs; (z.1.getD k 0,z.2)
  | f+1,xs,k =>
    if xs.length ≤ 1000 then let z := qSortCounted xs; (z.1.getD k 0,z.2) else
      let groups := (qChunks5 xs.length xs).map qSortCounted
      let pivots := groups.map (fun z => z.1.getD (z.1.length/2) 0)
      let p := qSelectFuel f pivots (pivots.length/2)
      let q := qPartition p.1 xs
      let initial := (groups.map Prod.snd).sum+p.2+q.2.2.2
      if k < q.1.length then let z := qSelectFuel f q.1 k; (z.1,initial+z.2) else
        if k < q.1.length+q.2.1.length then (p.1,initial) else
          let z := qSelectFuel f q.2.2.1 (k-q.1.length-q.2.1.length)
          (z.1,initial+z.2)
def qSelect (xs : List ℚ) (k : ℕ) : ℚ × ℕ := qSelectFuel xs.length xs k

theorem qInsertCounted_length (x : ℚ) (l : List ℚ) :
    (qInsertCounted x l).1.length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      simp only [qInsertCounted]
      split
      · rfl
      · show ((qInsertCounted x ys).1).length + 1 = (y :: ys).length + 1
        rw [ih]
        simp

theorem qInsertCounted_cost_le (x : ℚ) (l : List ℚ) :
    (qInsertCounted x l).2 ≤ l.length := by
  induction l with
  | nil => simp [qInsertCounted]
  | cons y ys ih =>
      simp only [qInsertCounted]
      split
      · simp
      · show (qInsertCounted x ys).2 + 1 ≤ (y :: ys).length
        have hlen : (y :: ys).length = ys.length + 1 := rfl
        omega

theorem qInsertCounted_perm (x : ℚ) (l : List ℚ) :
    (qInsertCounted x l).1.Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      simp only [qInsertCounted]
      split
      · exact List.Perm.refl _
      · exact List.Perm.trans (List.Perm.cons y ih) (List.Perm.swap x y ys)

theorem qInsertCounted_sorted {x : ℚ} {l : List ℚ} (hl : l.SortedLE) :
    (qInsertCounted x l).1.SortedLE := by
  induction l with
  | nil =>
      exact List.sortedLE_iff_pairwise.mpr
        (List.Pairwise.cons (fun b hb => absurd hb (List.not_mem_nil (a := b))) List.Pairwise.nil)
  | cons y ys ih =>
      simp only [qInsertCounted]
      rw [List.sortedLE_iff_pairwise] at hl ⊢
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
      split
      · next hxy =>
          refine List.Pairwise.cons (fun b hb => ?_) hl
          rcases List.mem_cons.mp hb with rfl | hbys
          · exact hxy
          · exact le_trans hxy (hhead b hbys)
      · next hnxy =>
          have hyx : y ≤ x := le_of_lt (lt_of_not_ge hnxy)
          refine List.Pairwise.cons (fun b hb => ?_)
            (List.sortedLE_iff_pairwise.mp (ih (List.sortedLE_iff_pairwise.mpr htail)))
          have hmem : b ∈ x :: ys := List.Perm.subset (qInsertCounted_perm x ys) hb
          rcases List.mem_cons.mp hmem with rfl | hbys
          · exact hyx
          · exact hhead b hbys

theorem qSortCounted_length (l : List ℚ) :
    (qSortCounted l).1.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show ((qInsertCounted x (qSortCounted xs).1).1).length = (x :: xs).length
      rw [qInsertCounted_length, ih]
      simp

theorem qSortCounted_perm (l : List ℚ) : (qSortCounted l).1.Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      show ((qInsertCounted x (qSortCounted xs).1).1).Perm (x :: xs)
      exact List.Perm.trans (qInsertCounted_perm x _) (List.Perm.cons x ih)

theorem qSortCounted_cost_le (l : List ℚ) :
    (qSortCounted l).2 ≤ l.length * l.length := by
  induction l with
  | nil => simp [qSortCounted]
  | cons x xs ih =>
      show (qSortCounted xs).2 + (qInsertCounted x (qSortCounted xs).1).2
        ≤ (x :: xs).length * (x :: xs).length
      have h1 := qInsertCounted_cost_le x (qSortCounted xs).1
      have h2 := qSortCounted_length xs
      have h3 : (x :: xs).length = xs.length + 1 := rfl
      have h4 : xs.length * xs.length + xs.length
          ≤ (x :: xs).length * (x :: xs).length := by
        rw [h3, Nat.succ_mul_succ]
        omega
      omega

theorem qSortCounted_sorted (l : List ℚ) : (qSortCounted l).1.SortedLE := by
  induction l with
  | nil => exact List.sortedLE_iff_pairwise.mpr List.Pairwise.nil
  | cons x xs ih =>
      show ((qInsertCounted x (qSortCounted xs).1).1).SortedLE
      exact qInsertCounted_sorted ih

theorem qChunks5_spec (f : ℕ) (xs : List ℚ) (hf : xs.length≤f) :
    (qChunks5 f xs).flatten=xs ∧
    (qChunks5 f xs).length=(xs.length+4)/5 ∧
    (∀ g ∈ qChunks5 f xs, 0<g.length ∧ g.length≤5) := by
  induction f generalizing xs with
  | zero =>
    have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp [qChunks5]
  | succ f ih =>
    cases xs with
    | nil => simp [qChunks5]
    | cons x xs =>
      have hr : ((x::xs).drop 5).length≤f := by
        simp only [List.length_drop,List.length_cons]
        simp only [List.length_cons] at hf
        omega
      obtain ⟨hflat,hlen,hgroups⟩ := ih ((x::xs).drop 5) hr
      simp only [qChunks5,List.flatten_cons,List.length_cons]
      refine ⟨?_,?_,?_⟩
      · rw [hflat,List.take_append_drop]
      · rw [hlen,List.length_drop]
        simp only [List.length_cons]
        omega
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · simp only [List.length_take,List.length_cons]
          omega
        · exact hgroups g hg

abbrev QPartitionState := List ℚ × List ℚ × List ℚ × ℕ

def qPartitionStep (p : ℚ) (z : QPartitionState) (x : ℚ) : QPartitionState :=
  if x<p then (x::z.1,z.2.1,z.2.2.1,z.2.2.2+1) else
  if p<x then (z.1,z.2.1,x::z.2.2.1,z.2.2.2+2) else
    (z.1,x::z.2.1,z.2.2.1,z.2.2.2+2)

theorem qPartitionStep_perm (p x : ℚ) (z : QPartitionState) :
    ((qPartitionStep p z x).1++(qPartitionStep p z x).2.1++
      (qPartitionStep p z x).2.2.1).Perm (x::(z.1++z.2.1++z.2.2.1)) := by
  unfold qPartitionStep
  split_ifs
  · exact List.Perm.refl _
  · simpa only [List.append_assoc] using
      (List.perm_middle : (z.1++z.2.1++x::z.2.2.1).Perm (x::((z.1++z.2.1)++z.2.2.1)))
  · simpa only [List.append_assoc,List.cons_append] using
      (List.perm_middle : (z.1++x::(z.2.1++z.2.2.1)).Perm (x::(z.1++(z.2.1++z.2.2.1))))

theorem qPartition_fold_spec (p : ℚ) (xs : List ℚ) (z : QPartitionState)
    (hl : ∀ x ∈ z.1,x<p) (he : ∀ x ∈ z.2.1,x=p) (hr : ∀ x ∈ z.2.2.1,p<x) :
    let t := xs.foldl (qPartitionStep p) z
    (t.1++t.2.1++t.2.2.1).Perm (xs.reverse++(z.1++z.2.1++z.2.2.1)) ∧
    (∀ x ∈ t.1,x<p) ∧ (∀ x ∈ t.2.1,x=p) ∧ (∀ x ∈ t.2.2.1,p<x) ∧
    t.2.2.2≤z.2.2.2+2*xs.length := by
  induction xs generalizing z with
  | nil => simp only [List.foldl_nil,List.reverse_nil,List.nil_append,List.length_nil,
      mul_zero,Nat.add_zero]; exact ⟨List.Perm.refl _,hl,he,hr,le_rfl⟩
  | cons x xs ih =>
    have hlo : ∀ y ∈ (qPartitionStep p z x).1,y<p := by
      unfold qPartitionStep
      split_ifs with h h'
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h
        · exact hl y hy
      · exact hl
      · exact hl
    have heq : ∀ y ∈ (qPartitionStep p z x).2.1,y=p := by
      unfold qPartitionStep
      split_ifs with h h'
      · exact he
      · exact he
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_antisymm (le_of_not_gt h') (le_of_not_gt h)
        · exact he y hy
    have hhi : ∀ y ∈ (qPartitionStep p z x).2.2.1,p<y := by
      unfold qPartitionStep
      split_ifs with h h'
      · exact hr
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h'
        · exact hr y hy
      · exact hr
    have hc : (qPartitionStep p z x).2.2.2≤z.2.2.2+2 := by
      unfold qPartitionStep
      split_ifs <;> simp
    obtain ⟨hp,hl',he',hr',hc'⟩ := ih (qPartitionStep p z x) hlo heq hhi
    simp only [List.foldl_cons]
    refine ⟨?_,hl',he',hr',?_⟩
    · exact hp.trans (by
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
          (List.Perm.append_left xs.reverse (qPartitionStep_perm p x z)))
    · simp only [List.length_cons]
      omega

theorem rational_selection_actual_sort_chunks_and_partition : ∀ (xs : List ℚ) (p : ℚ),
    (qSortCounted xs).1.Perm xs ∧ (qSortCounted xs).1.SortedLE ∧
    (qSortCounted xs).1.length=xs.length ∧ (qSortCounted xs).2≤xs.length^2 ∧
    (qChunks5 xs.length xs).flatten=xs ∧
    (qChunks5 xs.length xs).length=(xs.length+4)/5 ∧
    (∀ g ∈ qChunks5 xs.length xs,0<g.length ∧ g.length≤5) ∧
    let t := qPartition p xs
    (t.1++t.2.1++t.2.2.1).Perm xs ∧
    (∀ x ∈ t.1,x<p) ∧ (∀ x ∈ t.2.1,x=p) ∧ (∀ x ∈ t.2.2.1,p<x) ∧
    t.2.2.2≤2*xs.length := by
  intro xs p
  obtain ⟨hflat,hlen,hgroup⟩ := qChunks5_spec xs.length xs le_rfl
  have hp := qPartition_fold_spec p xs ([],[],[],0)
    (by simp) (by simp) (by simp)
  simp only [List.append_nil,Nat.zero_add] at hp
  refine ⟨qSortCounted_perm xs,qSortCounted_sorted xs,qSortCounted_length xs,
    by simpa only [pow_two] using qSortCounted_cost_le xs,hflat,hlen,hgroup,?_,
    hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
  exact hp.1.trans (List.reverse_perm xs)

def QRank (xs : List ℚ) (k : ℕ) (p : ℚ) : Prop :=
  p ∈ xs ∧ (xs.filter (fun x => x<p)).length≤k ∧
    k<(xs.filter (fun x => x≤p)).length

theorem qFilterLength_mono (xs : List ℚ) (P Q : ℚ → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x ∈ xs,P x → Q x) :
    (xs.filter (fun x => decide (P x))).length≤(xs.filter (fun x => decide (Q x))).length := by
  rw [← List.countP_eq_length_filter,← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun x hx hp => decide_eq_true_eq.mpr
    (h x hx (decide_eq_true_eq.mp hp)))

theorem qRank_unique {xs : List ℚ} {k : ℕ} {p q : ℚ}
    (hp : QRank xs k p) (hq : QRank xs k q) : p=q := by
  rcases lt_trichotomy p q with hl | he | hr
  · have hc := qFilterLength_mono xs (fun x => x≤p) (fun x => x<q)
      (fun x _ hx => lt_of_le_of_lt hx hl)
    have h1 := hp.2.2
    have h2 := hq.2.1
    try dsimp only at hc
    omega
  · exact he
  · have hc := qFilterLength_mono xs (fun x => x≤q) (fun x => x<p)
      (fun x _ hx => lt_of_le_of_lt hx hr)
    have h1 := hq.2.2
    have h2 := hp.2.1
    try dsimp only at hc
    omega

theorem qRank_perm {xs ys : List ℚ} {k : ℕ} {p : ℚ}
    (hperm : xs.Perm ys) (hp : QRank xs k p) : QRank ys k p := by
  refine ⟨hperm.mem_iff.mp hp.1,?_,?_⟩
  · rw [← (hperm.filter (fun x => x<p)).length_eq]
    exact hp.2.1
  · rw [← (hperm.filter (fun x => x≤p)).length_eq]
    exact hp.2.2

theorem qRank_sorted {s : List ℚ} (hs : s.SortedLE) (k : ℕ) (hk : k<s.length) :
    QRank s k (s.getD k 0) := by
  rw [List.getD_eq_getElem s 0 hk]
  refine ⟨List.getElem_mem hk,?_,?_⟩
  · have hdrop : ∀ x ∈ s.drop k,¬x < s[k] := by
      intro x hx
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hx
      have hil : k+i.val<s.length := by
        have hlen : i.val<s.length-k := by simpa using i.isLt
        omega
      have hx' : x=s[k+i.val] := by rw [← hi,List.get_eq_getElem,List.getElem_drop]
      rw [hx']
      exact not_lt_of_ge (hs.getElem_le_getElem_of_le (Nat.le_add_right _ _))
    have hz : (s.drop k).filter (fun x => x < s[k])=[] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp [hdrop x hx]
    have he := congrArg (List.filter (fun x => x < s[k])) (List.take_append_drop k s)
    rw [List.filter_append,hz,List.append_nil] at he
    rw [← he]
    exact (List.length_filter_le _ _).trans (by rw [List.length_take]; omega)
  · have htake : ∀ x ∈ s.take (k+1),x ≤ s[k] := by
      intro x hx
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hx
      have hil : i.val<s.length := by
        have hlen : i.val < min (k+1) s.length := by simpa using i.isLt
        omega
      have hx' : x=s[i.val] := by rw [← hi,List.get_eq_getElem,List.getElem_take]
      rw [hx']
      exact hs.getElem_le_getElem_of_le (by
        have hlen : i.val < min (k+1) s.length := by simpa using i.isLt
        omega)
    have hf : (s.take (k+1)).filter (fun x => x ≤ s[k])=s.take (k+1) := by
      apply List.filter_eq_self.mpr
      intro x hx
      exact decide_eq_true_eq.mpr (htake x hx)
    have hc := (List.take_sublist (k+1) s).countP_le (p := fun x => x ≤ s[k])
    rw [List.countP_eq_length_filter,List.countP_eq_length_filter,hf,List.length_take] at hc
    omega

theorem qRank_sort (xs : List ℚ) (k : ℕ) (hk : k<xs.length) :
    QRank xs k ((qSortCounted xs).1.getD k 0) :=
  qRank_perm (qSortCounted_perm xs)
    (qRank_sorted (qSortCounted_sorted xs) k (by rwa [qSortCounted_length]))

theorem qFilter_false (xs : List ℚ) (P : ℚ → Prop) [DecidablePred P]
    (h : ∀ x ∈ xs,¬P x) : xs.filter (fun x => decide (P x))=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  simp [h x hx]

theorem qFilter_true (xs : List ℚ) (P : ℚ → Prop) [DecidablePred P]
    (h : ∀ x ∈ xs,P x) : xs.filter (fun x => decide (P x))=xs := by
  apply List.filter_eq_self.mpr
  intro x hx
  exact decide_eq_true_eq.mpr (h x hx)

theorem qRank_partition_left (lo eq hi : List ℚ) (p : ℚ)
    (hl : ∀ x ∈ lo,x<p) (he : ∀ x ∈ eq,x=p) (hh : ∀ x ∈ hi,p<x)
    (k : ℕ) (v : ℚ) (hr : QRank lo k v) : QRank (lo++eq++hi) k v := by
  have hv : v<p := hl v hr.1
  have hel :=
      qFilter_false eq (fun x => x<v) (fun x hx => by rw [he x hx]; exact not_lt_of_ge hv.le)
  have hew := qFilter_false eq (fun x => x≤v) (fun x hx => by rw [he x hx]; exact not_le_of_gt hv)
  have hhl := qFilter_false hi (fun x => x<v) (fun x hx => not_lt_of_ge (hv.trans (hh x hx)).le)
  have hhw := qFilter_false hi (fun x => x≤v) (fun x hx => not_le_of_gt (hv.trans (hh x hx)))
  refine ⟨List.mem_append_left _ (List.mem_append_left _ hr.1),?_,?_⟩
  · simpa only [List.filter_append,hel,hhl,List.append_nil] using hr.2.1
  · simpa only [List.filter_append,hew,hhw,List.append_nil] using hr.2.2

theorem qRank_partition_middle (lo eq hi : List ℚ) (p : ℚ)
    (hl : ∀ x ∈ lo,x<p) (he : ∀ x ∈ eq,x=p) (hh : ∀ x ∈ hi,p<x)
    (k : ℕ) (hklo : lo.length≤k) (hkeq : k<lo.length+eq.length) :
    QRank (lo++eq++hi) k p := by
  obtain ⟨x,hx⟩ := List.length_pos_iff_exists_mem.mp (by omega : 0<eq.length)
  have hp : p∈eq := (he x hx) ▸ hx
  have hll := qFilter_true lo (fun x => x<p) hl
  have hlw := qFilter_true lo (fun x => x≤p) (fun x hx => (hl x hx).le)
  have hel := qFilter_false eq (fun x => x<p) (fun x hx => by rw [he x hx]; exact lt_irrefl p)
  have hew := qFilter_true eq (fun x => x≤p) (fun x hx => (he x hx).le)
  have hhl := qFilter_false hi (fun x => x<p) (fun x hx => not_lt_of_ge (hh x hx).le)
  have hhw := qFilter_false hi (fun x => x≤p) (fun x hx => not_le_of_gt (hh x hx))
  refine ⟨List.mem_append_left _ (List.mem_append_right _ hp),?_,?_⟩
  · simpa only [List.filter_append,hll,hel,hhl,List.append_nil] using hklo
  · simpa only [List.filter_append,hlw,hew,hhw,List.append_nil,List.length_append] using hkeq

theorem qRank_partition_right (lo eq hi : List ℚ) (p : ℚ)
    (hl : ∀ x ∈ lo,x<p) (he : ∀ x ∈ eq,x=p) (hh : ∀ x ∈ hi,p<x)
    (k : ℕ) (v : ℚ) (hr : QRank hi k v) : QRank (lo++eq++hi) (lo.length+eq.length+k) v := by
  have hv : p<v := hh v hr.1
  have hll := qFilter_true lo (fun x => x<v) (fun x hx => (hl x hx).trans hv)
  have hlw := qFilter_true lo (fun x => x≤v) (fun x hx => ((hl x hx).trans hv).le)
  have hel := qFilter_true eq (fun x => x<v) (fun x hx => by rw [he x hx]; exact hv)
  have hew := qFilter_true eq (fun x => x≤v) (fun x hx => by rw [he x hx]; exact hv.le)
  refine ⟨List.mem_append_right _ hr.1,?_,?_⟩
  · simp only [List.filter_append,hll,hel,List.length_append]
    exact Nat.add_le_add_left hr.2.1 _
  · simp only [List.filter_append,hlw,hew,List.length_append]
    exact Nat.add_lt_add_left hr.2.2 _

theorem qResult_fst_ite (P : Prop) [Decidable P] (a b : ℚ × ℕ) :
    (if P then a else b).1=if P then a.1 else b.1 := by
  split_ifs <;> rfl

theorem qSelectFuel_rank (f k : ℕ) (xs : List ℚ) (hk : k<xs.length) :
    QRank xs k (qSelectFuel f xs k).1 := by
  induction f generalizing xs k with
  | zero => exact qRank_sort xs k hk
  | succ f ih =>
    simp only [qSelectFuel]
    split
    · exact qRank_sort xs k hk
    · let groups := (qChunks5 xs.length xs).map qSortCounted
      let pivots := groups.map (fun z => z.1.getD (z.1.length/2) 0)
      let p := qSelectFuel f pivots (pivots.length/2)
      let q := qPartition p.1 xs
      have hparts := (rational_selection_actual_sort_chunks_and_partition xs p.1).2.2.2.2.2.2.2
      obtain ⟨hperm,hl,he,hh,_⟩ := hparts
      have hlen := hperm.length_eq
      simp only [List.length_append] at hlen
      simp only [qResult_fst_ite]
      change QRank xs k (if k<q.1.length then
        (qSelectFuel f q.1 k).1 else if k<q.1.length+q.2.1.length then p.1 else
          (qSelectFuel f q.2.2.1 (k-q.1.length-q.2.1.length)).1)
      by_cases hklo : k<q.1.length
      · rw [if_pos hklo]
        exact qRank_perm hperm (qRank_partition_left _ _ _ p.1 hl he hh _ _ (ih _ _ hklo))
      · rw [if_neg hklo]
        by_cases hkeq : k<q.1.length+q.2.1.length
        · rw [if_pos hkeq]
          exact qRank_perm hperm (qRank_partition_middle _ _ _ p.1 hl he hh _
            (show q.1.length≤k by omega) hkeq)
        · rw [if_neg hkeq]
          have hkh : k-q.1.length-q.2.1.length<q.2.2.1.length := by
            change q.1.length+q.2.1.length+q.2.2.1.length=xs.length at hlen
            omega
          have hr := qRank_partition_right _ _ _ p.1 hl he hh _ _ (ih _ _ hkh)
          have hsum : q.1.length+q.2.1.length+(k-q.1.length-q.2.1.length)=k := by omega
          rw [hsum] at hr
          exact qRank_perm hperm hr

theorem rational_selection_fuel_rank_and_duplicates : ∀ (f k : ℕ) (xs : List ℚ),
    k<xs.length → (qSelectFuel f xs k).1=(qSortCounted xs).1.getD k 0 ∧
    (qSelectFuel f xs k).1∈xs ∧
    (xs.filter (fun x => x<(qSelectFuel f xs k).1)).length≤k ∧
    k<(xs.filter (fun x => x≤(qSelectFuel f xs k).1)).length := by
  intro f k xs hk
  have hr := qSelectFuel_rank f k xs hk
  exact ⟨qRank_unique hr (qRank_sort xs k hk),hr⟩

@[simp] theorem qChunks5_nil (f : ℕ) : qChunks5 f []=[] := by cases f <;> rfl

theorem qChunks5_short_count (f : ℕ) (xs : List ℚ) (hf : xs.length≤f) :
    (qChunks5 f xs).countP (fun g => g.length<5)≤1 := by
  induction f generalizing xs with
  | zero => simp [qChunks5]
  | succ f ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      have hr : ((x::xs).drop 5).length≤f := by
        simp only [List.length_drop,List.length_cons]
        simp only [List.length_cons] at hf
        omega
      by_cases hs : (x::xs).length<5
      · have hd : (x::xs).drop 5=[] := List.drop_eq_nil_iff.mpr (by omega)
        simp only [qChunks5,hd,qChunks5_nil,List.countP_cons,List.countP_nil]
        split_ifs <;> omega
      · have ht : ((x::xs).take 5).length=5 := by rw [List.length_take]; omega
        simpa only [qChunks5,List.countP_cons,ht,lt_self_iff_false,decide_false,
          Bool.false_eq_true,if_false,Nat.zero_add] using! ih ((x::xs).drop 5) hr

def qGroupMedian (g : List ℚ) : ℚ := (qSortCounted g).1.getD ((qSortCounted g).1.length/2) 0

theorem qFilter_complement (xs : List ℚ) (p : ℚ) :
    (xs.filter (fun x => x<p)).length+(xs.filter (fun x => p≤x)).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x<p
    · simp [hx,not_le_of_gt hx]
      omega
    · simp [hx,le_of_not_gt hx]
      omega

theorem qFullGroup_lower_sets (g : List ℚ) (hg : g.length=5) (p : ℚ) :
    (qGroupMedian g≤p → 3≤(g.filter (fun x => x≤p)).length) ∧
    (p≤qGroupMedian g → 3≤(g.filter (fun x => p≤x)).length) := by
  have hr := qRank_sort g 2 (by omega)
  have hmed : qGroupMedian g=(qSortCounted g).1.getD 2 0 := by
    simp [qGroupMedian,qSortCounted_length,hg]
  rw [← hmed] at hr
  refine ⟨?_,?_⟩
  · intro hp
    have hm := qFilterLength_mono g (fun x => x≤qGroupMedian g) (fun x => x≤p)
      (fun x _ hx => hx.trans hp)
    try dsimp only at hm
    have hc := hr.2.2
    omega
  · intro hp
    have hc := qFilter_complement g (qGroupMedian g)
    have hl := hr.2.1
    have hm := qFilterLength_mono g (fun x => qGroupMedian g≤x) (fun x => p≤x)
      (fun x _ hx => hp.trans hx)
    try dsimp only at hm
    omega

theorem qGroups_count_lower (gs : List (List ℚ)) (P : ℚ → Prop) [DecidablePred P]
    (good : List ℚ → Bool) (hsize : ∀ g ∈ gs,g.length≤5)
    (hgood : ∀ g ∈ gs,g.length=5 → good g=true → 3≤(g.filter (fun x => decide (P x))).length) :
    3*gs.countP good≤(gs.map (fun g => (g.filter (fun x => decide (P x))).length)).sum+
      3*gs.countP (fun g => g.length<5) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ht := ih (fun t ht => hsize t (List.mem_cons_of_mem g ht))
      (fun t ht => hgood t (List.mem_cons_of_mem g ht))
    have hg := hsize g (List.mem_cons_self)
    have hlocal : 3*(if good g then 1 else 0)≤
        (g.filter (fun x => decide (P x))).length+3*(if g.length<5 then 1 else 0) := by
      cases hb : good g
      · simp
      · by_cases hs : g.length<5
        · simp [hs]
        · have he : g.length=5 := by omega
          simpa [hs] using hgood g (List.mem_cons_self) he hb
    simp only [List.countP_cons,List.map_cons,List.sum_cons]
    cases hb : good g <;> by_cases hs : g.length<5 <;>
      simp only [hb,hs,decide_true,decide_false,if_true,if_false,Bool.false_eq_true]
        at hlocal ⊢ <;> omega

theorem qPartition_complement_lengths (xs : List ℚ) (p : ℚ) :
    (qPartition p xs).1.length+(xs.filter (fun x => p≤x)).length=xs.length ∧
    (qPartition p xs).2.2.1.length+(xs.filter (fun x => x≤p)).length=xs.length := by
  obtain ⟨hp,hl,he,hh,_⟩ :=
    (rational_selection_actual_sort_chunks_and_partition xs p).2.2.2.2.2.2.2
  have hn := hp.length_eq
  simp only [List.length_append] at hn
  have hl0 := qFilter_false _ (fun x => p≤x) (fun x hx => not_le_of_gt (hl x hx))
  have he1 := qFilter_true _ (fun x => p≤x) (fun x hx => (he x hx).symm.le)
  have hh1 := qFilter_true _ (fun x => p≤x) (fun x hx => (hh x hx).le)
  have hl1 := qFilter_true _ (fun x => x≤p) (fun x hx => (hl x hx).le)
  have he2 := qFilter_true _ (fun x => x≤p) (fun x hx => (he x hx).le)
  have hh0 := qFilter_false _ (fun x => x≤p) (fun x hx => not_le_of_gt (hh x hx))
  have hge := (hp.filter (fun x => p≤x)).length_eq
  have hle := (hp.filter (fun x => x≤p)).length_eq
  simp only [List.filter_append,hl0,he1,hh1,List.nil_append,List.length_append] at hge
  simp only [List.filter_append,hl1,he2,hh0,List.append_nil,List.length_append] at hle
  omega

theorem qGroups_filter_length (gs : List (List ℚ)) (P : ℚ → Prop) [DecidablePred P] :
    (gs.map (fun g => (g.filter (fun x => decide (P x))).length)).sum=
      (gs.flatten.filter (fun x => decide (P x))).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [List.filter_append,ih]

theorem qMedian5_partition_bounds (f : ℕ) (xs : List ℚ) (hx : 1000<xs.length) :
    let gs := qChunks5 xs.length xs
    let pivots := gs.map qGroupMedian
    let p := (qSelectFuel f pivots (pivots.length/2)).1
    let q := qPartition p xs
    pivots.length<xs.length ∧ q.1.length<xs.length ∧ q.2.2.1.length<xs.length ∧
      7*xs.length+10000*pivots.length+10000*q.1.length≤10000*xs.length ∧
      7*xs.length+10000*pivots.length+10000*q.2.2.1.length≤10000*xs.length := by
  intro gs pivots p q
  obtain ⟨hflat,hlen,hsize⟩ := qChunks5_spec xs.length xs le_rfl
  have hg : pivots.length=(xs.length+4)/5 := by simpa [pivots] using hlen
  have hpos : 0<pivots.length := by omega
  have hr := qSelectFuel_rank f (pivots.length/2) pivots (by omega)
  change QRank pivots (pivots.length/2) p at hr
  have hshort := qChunks5_short_count xs.length xs le_rfl
  have hbelow := qGroups_count_lower gs (fun x => x≤p)
    (fun g => decide (qGroupMedian g≤p)) (fun g hg => (hsize g hg).2)
    (fun g hg hfull hgood => (qFullGroup_lower_sets g hfull p).1 (decide_eq_true_eq.mp hgood))
  have habove := qGroups_count_lower gs (fun x => p≤x)
    (fun g => decide (p≤qGroupMedian g)) (fun g hg => (hsize g hg).2)
    (fun g hg hfull hgood => (qFullGroup_lower_sets g hfull p).2 (decide_eq_true_eq.mp hgood))
  have hcb : (pivots.filter (fun x => x≤p)).length=
      gs.countP (fun g => decide (qGroupMedian g≤p)) := by
    rw [← List.countP_eq_length_filter]
    exact List.countP_map
  have hca : (pivots.filter (fun x => p≤x)).length=
      gs.countP (fun g => decide (p≤qGroupMedian g)) := by
    rw [← List.countP_eq_length_filter]
    exact List.countP_map
  rw [qGroups_filter_length,hflat] at hbelow habove
  have hweak := hr.2.2
  have hstrict := hr.2.1
  have hcomp := qFilter_complement pivots p
  rw [hcb] at hweak
  rw [hca] at hcomp
  obtain ⟨hlo,hhi⟩ := qPartition_complement_lengths xs p
  change q.1.length+(xs.filter (fun x => p≤x)).length=xs.length at hlo
  change q.2.2.1.length+(xs.filter (fun x => x≤p)).length=xs.length at hhi
  change gs.countP (fun g => g.length<5)≤1 at hshort
  omega

theorem qGroups_sort_cost (gs : List (List ℚ)) (hsize : ∀ g ∈ gs,g.length≤5) :
    (gs.map (fun g => (qSortCounted g).2)).sum≤5*(gs.map List.length).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hc := (qSortCounted_cost_le g).trans
      (Nat.mul_le_mul_right g.length (hsize g (List.mem_cons_self)))
    have ht := ih (fun t ht => hsize t (List.mem_cons_of_mem g ht))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem qChunks_sort_cost (xs : List ℚ) :
    (((qChunks5 xs.length xs).map qSortCounted).map Prod.snd).sum≤5*xs.length := by
  obtain ⟨hflat,_,hsize⟩ := qChunks5_spec xs.length xs le_rfl
  have h := qGroups_sort_cost (qChunks5 xs.length xs) (fun g hg => (hsize g hg).2)
  rw [← List.length_flatten,hflat] at h
  simpa only [List.map_map,Function.comp_def] using h

theorem qResult_snd_ite (P : Prop) [Decidable P] (a b : ℚ × ℕ) :
    (if P then a else b).2=if P then a.2 else b.2 := by split_ifs <;> rfl

theorem rational_selection_sufficient_fuel_linear_comparisons :
    ∀ (f k : ℕ) (xs : List ℚ), xs.length≤f → (qSelectFuel f xs k).2≤10000*xs.length := by
  intro f
  induction f with
  | zero =>
    intro k xs hf
    have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp [qSelectFuel,qSortCounted]
  | succ f ih =>
    intro k xs hf
    simp only [qSelectFuel]
    split
    · next hbase =>
        have hc := qSortCounted_cost_le xs
        have hm := Nat.mul_le_mul_right xs.length hbase
        nlinarith
    · next hlarge =>
        have hx : 1000<xs.length := by omega
        let groups := (qChunks5 xs.length xs).map qSortCounted
        let pivots := groups.map (fun z => z.1.getD (z.1.length/2) 0)
        let p := qSelectFuel f pivots (pivots.length/2)
        let q := qPartition p.1 xs
        have hpivots : pivots=(qChunks5 xs.length xs).map qGroupMedian := by
          simp only [pivots,groups,List.map_map,Function.comp_def]
          rfl
        have hb : pivots.length<xs.length ∧ q.1.length<xs.length ∧ q.2.2.1.length<xs.length ∧
            7*xs.length+10000*pivots.length+10000*q.1.length≤10000*xs.length ∧
            7*xs.length+10000*pivots.length+10000*q.2.2.1.length≤10000*xs.length := by
          dsimp only [q,p]
          rw [hpivots]
          exact qMedian5_partition_bounds f xs hx
        have hp : p.2≤10000*pivots.length := ih _ _ (by omega)
        have hlo : (qSelectFuel f q.1 k).2≤10000*q.1.length := ih _ _ (by omega)
        have hhi : (qSelectFuel f q.2.2.1 (k-q.1.length-q.2.1.length)).2≤10000*q.2.2.1.length :=
          ih _ _ (by omega)
        have hg : (groups.map Prod.snd).sum≤5*xs.length := qChunks_sort_cost xs
        have hq : q.2.2.2≤2*xs.length :=
          (rational_selection_actual_sort_chunks_and_partition xs p.1).2.2.2.2.2.2.2.2.2.2.2
        simp only [qResult_snd_ite]
        change (if k<q.1.length then (groups.map Prod.snd).sum+p.2+q.2.2.2+
          (qSelectFuel f q.1 k).2 else if k<q.1.length+q.2.1.length then
            (groups.map Prod.snd).sum+p.2+q.2.2.2 else
              (groups.map Prod.snd).sum+p.2+q.2.2.2+
                (qSelectFuel f q.2.2.1 (k-q.1.length-q.2.1.length)).2)≤10000*xs.length
        split_ifs <;> omega

theorem qSortCounted_cast (xs : List ℚ) :
    (qSortCounted xs).1.map (fun x : ℚ => (x : ℝ))=
      (insertionSortCounted (xs.map (fun x : ℚ => (x : ℝ)))).1 := by
  have hp := ((qSortCounted_perm xs).map (fun x : ℚ => (x : ℝ))).trans
    (insertionSortCounted_perm (xs.map (fun x : ℚ => (x : ℝ)))).symm
  have hq : ((qSortCounted xs).1.map (fun x : ℚ => (x : ℝ))).SortedLE := by
    rw [List.sortedLE_iff_pairwise,List.pairwise_map]
    exact (List.sortedLE_iff_pairwise.mp (qSortCounted_sorted xs)).imp
      (fun h => by exact_mod_cast h)
  exact hp.eq_of_pairwise' (List.sortedLE_iff_pairwise.mp hq)
    (List.sortedLE_iff_pairwise.mp (insertionSortCounted_sorted _))

theorem rational_selection_median_exact_real_sorted_semantics :
    ∀ (r : ℕ) (v : Fin (2*r+1) → ℚ),
    ((qSelect (List.ofFn v) r).1 : ℝ)=sortedBlockMedian r (fun j => (v j : ℝ)) ∧
      (qSelect (List.ofFn v) r).2≤10000*(2*r+1) := by
  intro r v
  have hk : r<(List.ofFn v).length := by simp; omega
  refine ⟨?_,?_⟩
  · rw [qSelect,(rational_selection_fuel_rank_and_duplicates _ _ _ hk).1]
    have hcast := qSortCounted_cast (List.ofFn v)
    have hd : ((qSortCounted (List.ofFn v)).1.getD r 0 : ℝ)=
        (((qSortCounted (List.ofFn v)).1.map (fun x : ℚ => (x : ℝ))).getD r 0) := by
      simpa using (List.getD_map (qSortCounted (List.ofFn v)).1 0 (n := r)
        (fun x : ℚ => (x : ℝ))).symm
    rw [hd,hcast]
    simp only [List.map_ofFn,Function.comp_def,sortedBlockMedian]
  · simpa only [qSelect,List.length_ofFn] using
      rational_selection_sufficient_fuel_linear_comparisons (List.ofFn v).length r
        (List.ofFn v) le_rfl

end Qatlib.Concepts.ShadowModels.SampleBudget
