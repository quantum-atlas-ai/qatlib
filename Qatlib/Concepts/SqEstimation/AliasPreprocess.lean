/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.Fintype.Fin
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SqEstimation.AliasPreprocess

open scoped BigOperators

def aliasWeightTotal {n : ℕ} (u : Fin n → ℕ) : ℕ := ∑ i, u i

structure AliasSt (n : ℕ) where
  small : List (Fin n)
  large : List (Fin n)
  v : Fin n → ℕ
  qN : Fin n → ℕ
  al : Fin n → Fin n
  steps : ℕ

def pendCount {n : ℕ} (st : AliasSt n) : ℕ := st.small.length + st.large.length

def pendSum {n : ℕ} (st : AliasSt n) : ℕ := (st.small.map st.v).sum + (st.large.map st.v).sum

def aliasMassOf {n : ℕ} (U : ℕ) (st : AliasSt n) (k : Fin n) : ℕ :=
  st.v k + ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ st.al i = k), (U - st.qN i)

def aliasStepCore {n : ℕ} (U : ℕ) (i j : Fin n) (s' l' : List (Fin n)) (st : AliasSt n) :
    AliasSt n :=
  { small := if st.v j - (U - st.v i) < U then s' ++ [j] else s'
    large := if st.v j - (U - st.v i) < U then l' else l' ++ [j]
    v := fun k => if k = j then st.v j - (U - st.v i) else st.v k
    qN := fun k => if k = i then st.v i else st.qN k
    al := fun k => if k = i then j else st.al k
    steps := st.steps + 1 }

def aliasStep {n : ℕ} (U : ℕ) (st : AliasSt n) : AliasSt n :=
  match st.small, st.large with
  | i :: s', j :: l' => aliasStepCore U i j s' l' st
  | _, _ => st

def aliasRun {n : ℕ} (U : ℕ) : ℕ → AliasSt n → AliasSt n
  | 0, st => st
  | f + 1, st => if st.small = [] ∨ st.large = [] then st else aliasRun U f (aliasStep U st)

def aliasInit {n : ℕ} (u : Fin n → ℕ) : AliasSt n :=
  { small := (List.finRange n).filter (fun i => decide (n * u i < aliasWeightTotal u))
    large := (List.finRange n).filter (fun i => decide (aliasWeightTotal u ≤ n * u i))
    v := fun i => n * u i
    qN := fun _ => aliasWeightTotal u
    al := fun i => i
    steps := 0 }

def aliasTable {n : ℕ} (u : Fin n → ℕ) : AliasSt n :=
  aliasRun (aliasWeightTotal u) n (aliasInit u)

def aliasDist {n : ℕ} (st : AliasSt n) (U : ℕ) (k : Fin n) : ℚ :=
  ((st.qN k : ℚ) / U +
    ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ st.al i = k),
      (1 - (st.qN i : ℚ) / U)) / n

private lemma list_sum_le_length_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (hf : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : f a ≤ c := hf a (by simp)
    have hft : ∀ x ∈ t, f x ≤ c := fun x hx => hf x (by simp [hx])
    have hih := ih hft
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private lemma list_sum_lt_length_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (hl : l ≠ []) (hf : ∀ x ∈ l, f x < c) : (l.map f).sum < l.length * c := by
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
    cases l with
    | nil => exact absurd rfl hl
    | cons a t => exact ⟨a, t, rfl⟩
  have ha : f a < c := hf a (by simp)
  have hft : ∀ x ∈ t, f x ≤ c := fun x hx => Nat.le_of_lt (hf x (by simp [hx]))
  have hge := list_sum_le_length_mul t f c hft
  rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
  omega

private lemma list_sum_ge_length_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (hf : ∀ x ∈ l, c ≤ f x) : l.length * c ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : c ≤ f a := hf a (by simp)
    have hft : ∀ x ∈ t, c ≤ f x := fun x hx => hf x (by simp [hx])
    have hih := ih hft
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private lemma list_all_eq_of_sum_eq {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (hf : ∀ x ∈ l, c ≤ f x) (hsum : (l.map f).sum = l.length * c) :
    ∀ x ∈ l, f x = c := by
  induction l with
  | nil => intro x hx; cases hx
  | cons a t ih =>
    have ha : c ≤ f a := hf a (by simp)
    have hft : ∀ y ∈ t, c ≤ f y := fun y hy => hf y (by simp [hy])
    have hge := list_sum_ge_length_mul t f c hft
    have hsumE : f a + (t.map f).sum = c + t.length * c := by
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at hsum
      omega
    have hsum' : (t.map f).sum = t.length * c := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact ih hft hsum' x hx

private lemma list_sum_filter_split {α : Type*} (l : List α) (p q : α → Bool)
    (f : α → ℕ) (h : ∀ x, p x = !q x) :
    ((l.filter p).map f).sum + ((l.filter q).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hqa : q a = true
    · have hp0 : p a = false := by rw [h a, hqa]; rfl
      have hfp : List.filter p (a :: t) = List.filter p t := by
        simp [hp0]
      have hfq : List.filter q (a :: t) = a :: List.filter q t := by
        simp [hqa]
      rw [hfp, hfq, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      omega
    · have hq0 : q a = false := by simpa using hqa
      have hp1 : p a = true := by rw [h a, hq0]; rfl
      have hfp : List.filter p (a :: t) = a :: List.filter p t := by
        simp [hp1]
      have hfq : List.filter q (a :: t) = List.filter q t := by
        simp [hq0]
      rw [hfp, hfq, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      omega

private lemma list_length_filter_split {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ x, p x = !q x) :
    (l.filter p).length + (l.filter q).length = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hqa : q a = true
    · have hp0 : p a = false := by rw [h a, hqa]; rfl
      have hfp : List.filter p (a :: t) = List.filter p t := by
        simp [hp0]
      have hfq : List.filter q (a :: t) = a :: List.filter q t := by
        simp [hqa]
      rw [hfp, hfq, List.length_cons, List.length_cons]
      omega
    · have hq0 : q a = false := by simpa using hqa
      have hp1 : p a = true := by rw [h a, hq0]; rfl
      have hfp : List.filter p (a :: t) = a :: List.filter p t := by
        simp [hp1]
      have hfq : List.filter q (a :: t) = List.filter q t := by
        simp [hq0]
      rw [hfp, hfq, List.length_cons, List.length_cons]
      omega

private theorem listSum_finRange : ∀ {m : ℕ} (f : Fin m → ℕ),
    ((List.finRange m).map f).sum = ∑ i, f i
  | 0, _ => by simp
  | k + 1, f => by
    have e2 : ((List.finRange k).map Fin.succ).map f
        = (List.finRange k).map (fun i => f i.succ) := by
      simp only [List.map_map, Function.comp_def]
    rw [List.finRange_succ, List.map_cons, List.sum_cons, Fin.sum_univ_succ, e2,
      listSum_finRange (fun i => f i.succ)]

private lemma filter_update_eq {α : Type*} [DecidableEq α] [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (a : α)
    (h : ∀ x, x ≠ a → (P x ↔ Q x)) (hPa : ¬ P a) (hQa : ¬ Q a) :
    Finset.univ.filter Q = Finset.univ.filter P := by
  ext x
  by_cases hxa : x = a
  · subst hxa; simp [Finset.mem_filter, hPa, hQa]
  · simp only [Finset.mem_filter, Finset.mem_univ]
    rw [h x hxa]

private lemma filter_insert_patch {α : Type*} [DecidableEq α] [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (a : α)
    (h : ∀ x, x ≠ a → (P x ↔ Q x)) (hPa : ¬ P a) (hQa : Q a) :
    Finset.univ.filter Q = insert a (Finset.univ.filter P) := by
  ext x
  by_cases hxa : x = a
  · subst hxa; simp [Finset.mem_filter, hQa]
  · simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert]
    rw [h x hxa]
    simp [hxa]

def AliasInv {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n) : Prop :=
  st.small.Nodup ∧ st.large.Nodup ∧
    (∀ x ∈ st.small, ∀ y ∈ st.large, x ≠ y) ∧
    (∀ x ∈ st.small, st.v x < U ∧ st.qN x = U ∧ st.al x = x) ∧
    (∀ x ∈ st.large, U ≤ st.v x ∧ st.qN x = U ∧ st.al x = x) ∧
    pendSum st + st.steps * U = n * U ∧
    pendCount st + st.steps = n ∧
    (∀ k, aliasMassOf U st k = n * u k) ∧
    (∀ k, k ∈ st.small ∨ k ∈ st.large ∨ (st.qN k ≠ U ∧ st.v k = st.qN k ∧ st.v k < U))

private lemma no_small_without_large {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n)
    (h : AliasInv u U st) (hL : st.large = []) : st.small = [] := by
  by_contra hS
  obtain ⟨_, _, _, h4, _, h6, h7, _, _⟩ := h
  have h3' : pendCount st * U + st.steps * U = n * U := by
    rw [← Nat.add_mul, h7]
  have h3 : pendSum st = pendCount st * U := by omega
  have hall : ∀ x ∈ st.small, st.v x < U := fun x hx => (h4 x hx).1
  have hlt := list_sum_lt_length_mul st.small st.v U hS hall
  simp only [pendSum, pendCount, hL, List.map_nil, List.sum_nil, List.length_nil,
    Nat.add_zero] at h3 hlt
  omega

theorem aliasStepCore_pendCount {n : ℕ} (U : ℕ) (i j : Fin n) (s' l' : List (Fin n))
    (st : AliasSt n) (hsm : st.small = i :: s') (hlg : st.large = j :: l') :
    pendCount (aliasStepCore U i j s' l' st) + 1 = pendCount st := by
  by_cases h : st.v j - (U - st.v i) < U
  · simp only [aliasStepCore, pendCount, hsm, hlg, if_pos h, List.length_cons,
      List.length_append, List.length_nil]
    omega
  · simp only [aliasStepCore, pendCount, hsm, hlg, if_neg h, List.length_cons,
      List.length_append, List.length_nil]
    omega

private lemma massOf_step {n : ℕ} (U : ℕ) (st : AliasSt n) (i j : Fin n)
    (s' l' : List (Fin n)) (k : Fin n)
    (hali : st.al i = i) (hij : i ≠ j) (hvjle : U - st.v i ≤ st.v j) :
    aliasMassOf U (aliasStepCore U i j s' l' st) k = aliasMassOf U st k := by
  simp only [aliasMassOf, aliasStepCore]
  have hPQoff : ∀ x, x ≠ i →
      ((x ≠ k ∧ st.al x = k) ↔ (x ≠ k ∧ (if x = i then j else st.al x) = k)) := by
    intro x hx
    simp only [if_neg hx]
  have hPi : ¬ (i ≠ k ∧ st.al i = k) := by simp [hali]
  have hcongr : ∀ x ∈ Finset.univ.filter (fun x => x ≠ k ∧ st.al x = k),
      (U - (if x = i then st.v i else st.qN x)) = U - st.qN x := by
    intro x hx
    have hxi : x ≠ i := by
      intro he
      have hx2 : x ≠ k ∧ st.al x = k := (Finset.mem_filter.mp hx).2
      rw [he] at hx2
      exact hx2.1 (hali ▸ hx2.2)
    simp only [if_neg hxi]
  by_cases hkj : k = j
  · subst hkj
    have hite : (if i = i then k else st.al i) = k := if_pos rfl
    have hQi : (i ≠ k ∧ (if i = i then k else st.al i) = k) := ⟨hij, hite⟩
    have hset := filter_insert_patch
      (fun x => x ≠ k ∧ st.al x = k) (fun x => x ≠ k ∧ (if x = i then k else st.al x) = k)
      i hPQoff hPi hQi
    rw [hset, Finset.sum_insert (by simp [Finset.mem_filter, hPi]), if_pos rfl,
      Finset.sum_congr rfl hcongr, if_pos rfl]
    omega
  · have hQi : ¬ (i ≠ k ∧ (if i = i then j else st.al i) = k) := by
      intro hcon
      have hite : (if i = i then j else st.al i) = j := if_pos rfl
      rw [hite] at hcon
      exact hkj hcon.2.symm
    have hset := filter_update_eq
      (fun x => x ≠ k ∧ st.al x = k) (fun x => x ≠ k ∧ (if x = i then j else st.al x) = k)
      i hPQoff hPi hQi
    rw [hset, Finset.sum_congr rfl hcongr, if_neg hkj]

theorem aliasStepCore_inv {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n) (i j : Fin n)
    (s' l' : List (Fin n)) (hsm : st.small = i :: s') (hlg : st.large = j :: l')
    (h : AliasInv u U st) : AliasInv u U (aliasStepCore U i j s' l' st) := by
  obtain ⟨hnd1, hnd2, hdis, h4, h5, h6, h7, h8, h9⟩ := h
  have hism : i ∈ st.small := by rw [hsm]; exact List.mem_cons_self ..
  have hjsm : j ∈ st.large := by rw [hlg]; exact List.mem_cons_self ..
  have hmem_s' : ∀ x ∈ s', x ∈ st.small := fun x hx => hsm ▸ List.mem_cons_of_mem _ hx
  have hmem_l' : ∀ x ∈ l', x ∈ st.large := fun x hx => hlg ▸ List.mem_cons_of_mem _ hx
  have hi_not_s' : i ∉ s' := (List.nodup_cons.mp (hsm ▸ hnd1)).1
  have hj_not_s' : j ∉ s' := fun hx => hdis j (hmem_s' j hx) j hjsm rfl
  have hj_not_l' : j ∉ l' := (List.nodup_cons.mp (hlg ▸ hnd2)).1
  have hvi : st.v i < U := (h4 i hism).1
  have hvj : U ≤ st.v j := (h5 j hjsm).1
  have hqNj : st.qN j = U := (h5 j hjsm).2.1
  have halj : st.al j = j := (h5 j hjsm).2.2
  have hali : st.al i = i := (h4 i hism).2.2
  have hij : i ≠ j := fun he => hdis i hism j hjsm he
  have hvjle : U - st.v i ≤ st.v j := by omega
  have hnd1' : s'.Nodup := (List.nodup_cons.mp (hsm ▸ hnd1)).2
  have hnd2' : l'.Nodup := (List.nodup_cons.mp (hlg ▸ hnd2)).2
  have hdisj_s' : List.Disjoint s' [j] := List.disjoint_iff_ne.mpr
    fun x hx y hy heq => hdis x (hmem_s' x hx) j hjsm (heq.trans (List.mem_singleton.mp hy))
  have hdisj_l' : List.Disjoint l' [j] := List.disjoint_iff_ne.mpr
    fun x hx y hy heq => hj_not_l' (by rw [← heq.trans (List.mem_singleton.mp hy)]; exact hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun k => (massOf_step U st i j s' l' k hali hij hvjle).trans (h8 k), ?_⟩
  · by_cases hc : st.v j - (U - st.v i) < U
    · simp only [aliasStepCore, if_pos hc]
      exact List.Nodup.append hnd1' (by simp : [j].Nodup) hdisj_s'
    · simp only [aliasStepCore, if_neg hc]; exact hnd1'
  · by_cases hc : st.v j - (U - st.v i) < U
    · simp only [aliasStepCore, if_pos hc]; exact hnd2'
    · simp only [aliasStepCore, if_neg hc]
      exact List.Nodup.append hnd2' (by simp : [j].Nodup) hdisj_l'
  · by_cases hc : st.v j - (U - st.v i) < U
    · simp only [aliasStepCore, if_pos hc]
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact hdis x (hmem_s' x hx) y (hmem_l' y hy)
      · exact fun he => hj_not_l' (by
          have hxj : x = j := List.mem_singleton.mp hx
          rw [← hxj, he]; exact hy)
    · simp only [aliasStepCore, if_neg hc]
      intro x hx y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hdis x (hmem_s' x hx) y (hmem_l' y hy)
      · exact fun he => hj_not_s' (by
          have hyj : y = j := List.mem_singleton.mp hy
          rw [← hyj, ← he]; exact hx)
  · by_cases hc : st.v j - (U - st.v i) < U
    · simp only [aliasStepCore, if_pos hc]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · refine ⟨?_, ?_, ?_⟩
        · show (if x = j then st.v j - (U - st.v i) else st.v x) < U
          rw [if_neg (show x ≠ j from fun he => hdis x (hmem_s' x hx) j hjsm he)]
          exact (h4 x (hmem_s' x hx)).1
        · show (if x = i then st.v i else st.qN x) = U
          rw [if_neg (show x ≠ i from fun he => hi_not_s' (he ▸ hx))]
          exact (h4 x (hmem_s' x hx)).2.1
        · show (if x = i then j else st.al x) = x
          rw [if_neg (show x ≠ i from fun he => hi_not_s' (he ▸ hx))]
          exact (h4 x (hmem_s' x hx)).2.2
      · have hxj : x = j := List.mem_singleton.mp hx
        refine ⟨?_, ?_, ?_⟩
        · show (if x = j then st.v j - (U - st.v i) else st.v x) < U
          rw [if_pos hxj]; exact hc
        · show (if x = i then st.v i else st.qN x) = U
          rw [if_neg (show x ≠ i from fun he => hij (hxj ▸ he).symm), hxj]
          exact hqNj
        · show (if x = i then j else st.al x) = x
          rw [if_neg (show x ≠ i from fun he => hij (hxj ▸ he).symm), hxj]
          exact halj
    · simp only [aliasStepCore, if_neg hc]
      intro x hx
      refine ⟨?_, ?_, ?_⟩
      · show (if x = j then st.v j - (U - st.v i) else st.v x) < U
        rw [if_neg (show x ≠ j from fun he => hdis x (hmem_s' x hx) j hjsm he)]
        exact (h4 x (hmem_s' x hx)).1
      · show (if x = i then st.v i else st.qN x) = U
        rw [if_neg (show x ≠ i from fun he => hi_not_s' (he ▸ hx))]
        exact (h4 x (hmem_s' x hx)).2.1
      · show (if x = i then j else st.al x) = x
        rw [if_neg (show x ≠ i from fun he => hi_not_s' (he ▸ hx))]
        exact (h4 x (hmem_s' x hx)).2.2
  · by_cases hc : st.v j - (U - st.v i) < U
    · simp only [aliasStepCore, if_pos hc]
      intro x hx
      refine ⟨?_, ?_, ?_⟩
      · show U ≤ (if x = j then st.v j - (U - st.v i) else st.v x)
        rw [if_neg (show x ≠ j from fun he => hj_not_l' (he ▸ hx))]
        exact (h5 x (hmem_l' x hx)).1
      · show (if x = i then st.v i else st.qN x) = U
        rw [if_neg (show x ≠ i from fun he => hdis i hism x (hmem_l' x hx) he.symm)]
        exact (h5 x (hmem_l' x hx)).2.1
      · show (if x = i then j else st.al x) = x
        rw [if_neg (show x ≠ i from fun he => hdis i hism x (hmem_l' x hx) he.symm)]
        exact (h5 x (hmem_l' x hx)).2.2
    · simp only [aliasStepCore, if_neg hc]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · refine ⟨?_, ?_, ?_⟩
        · show U ≤ (if x = j then st.v j - (U - st.v i) else st.v x)
          rw [if_neg (show x ≠ j from fun he => hj_not_l' (he ▸ hx))]
          exact (h5 x (hmem_l' x hx)).1
        · show (if x = i then st.v i else st.qN x) = U
          rw [if_neg (show x ≠ i from fun he => hdis i hism x (hmem_l' x hx) he.symm)]
          exact (h5 x (hmem_l' x hx)).2.1
        · show (if x = i then j else st.al x) = x
          rw [if_neg (show x ≠ i from fun he => hdis i hism x (hmem_l' x hx) he.symm)]
          exact (h5 x (hmem_l' x hx)).2.2
      · have hxj : x = j := List.mem_singleton.mp hx
        refine ⟨?_, ?_, ?_⟩
        · show U ≤ (if x = j then st.v j - (U - st.v i) else st.v x)
          rw [if_pos hxj]; omega
        · show (if x = i then st.v i else st.qN x) = U
          rw [if_neg (show x ≠ i from fun he => hij (hxj ▸ he).symm), hxj]
          exact hqNj
        · show (if x = i then j else st.al x) = x
          rw [if_neg (show x ≠ i from fun he => hij (hxj ▸ he).symm), hxj]
          exact halj
  · have hfun_s' : s'.map (aliasStepCore U i j s' l' st).v = s'.map st.v := by
      refine List.map_congr_left fun x hx => ?_
      show (if x = j then st.v j - (U - st.v i) else st.v x) = st.v x
      rw [if_neg (show x ≠ j from fun he => hdis x (hmem_s' x hx) j hjsm he)]
    have hfun_l' : l'.map (aliasStepCore U i j s' l' st).v = l'.map st.v := by
      refine List.map_congr_left fun x hx => ?_
      show (if x = j then st.v j - (U - st.v i) else st.v x) = st.v x
      rw [if_neg (show x ≠ j from fun he => hj_not_l' (he ▸ hx))]
    have hold : pendSum st = st.v i + (s'.map st.v).sum + (st.v j + (l'.map st.v).sum) := by
      simp only [pendSum, hsm, hlg, List.map_cons, List.sum_cons]
    have hsteps : (aliasStepCore U i j s' l' st).steps = st.steps + 1 := rfl
    have hvjv : (aliasStepCore U i j s' l' st).v j = st.v j - (U - st.v i) := by
      show (if j = j then st.v j - (U - st.v i) else st.v j)
          = st.v j - (U - st.v i)
      rw [if_pos rfl]
    show pendSum (aliasStepCore U i j s' l' st)
      + (aliasStepCore U i j s' l' st).steps * U = n * U
    by_cases hc : st.v j - (U - st.v i) < U
    · have hsmall : (aliasStepCore U i j s' l' st).small = s' ++ [j] := if_pos hc
      have hlarge : (aliasStepCore U i j s' l' st).large = l' := if_pos hc
      have hps : pendSum (aliasStepCore U i j s' l' st)
          = ((aliasStepCore U i j s' l' st).v j
            + (l'.map (aliasStepCore U i j s' l' st).v).sum)
          + (s'.map (aliasStepCore U i j s' l' st).v).sum := by
        simp only [pendSum, hsmall, hlarge, List.map_append, List.sum_append,
          List.map_singleton, List.sum_cons, List.sum_nil]
        omega
      rw [hps, hfun_s', hfun_l', hvjv, hsteps, Nat.add_mul, Nat.one_mul]
      omega
    · have hsmall : (aliasStepCore U i j s' l' st).small = s' := if_neg hc
      have hlarge : (aliasStepCore U i j s' l' st).large = l' ++ [j] := if_neg hc
      have hps : pendSum (aliasStepCore U i j s' l' st)
          = ((aliasStepCore U i j s' l' st).v j
            + (l'.map (aliasStepCore U i j s' l' st).v).sum)
          + (s'.map (aliasStepCore U i j s' l' st).v).sum := by
        simp only [pendSum, hsmall, hlarge, List.map_append, List.sum_append,
          List.map_singleton, List.sum_cons, List.sum_nil]
        omega
      rw [hps, hfun_s', hfun_l', hvjv, hsteps, Nat.add_mul, Nat.one_mul]
      omega

  · have hpc := aliasStepCore_pendCount U i j s' l' st hsm hlg
    show pendCount (aliasStepCore U i j s' l' st)
      + (aliasStepCore U i j s' l' st).steps = n
    have hst : (aliasStepCore U i j s' l' st).steps = st.steps + 1 := rfl
    omega
  · intro k
    have hk9 := h9 k
    by_cases hki : k = i
    · right; right
      have hq : (aliasStepCore U i j s' l' st).qN k ≠ U := by
        show (if k = i then st.v i else st.qN k) ≠ U
        rw [if_pos hki]; exact ne_of_lt hvi
      have hv : (aliasStepCore U i j s' l' st).v k
          = (aliasStepCore U i j s' l' st).qN k := by
        show (if k = j then st.v j - (U - st.v i) else st.v k)
            = (if k = i then st.v i else st.qN k)
        rw [if_neg (show k ≠ j from fun he => hij (hki ▸ he)), if_pos hki, hki]
      have hvU : (aliasStepCore U i j s' l' st).v k < U := by
        show (if k = j then st.v j - (U - st.v i) else st.v k) < U
        rw [if_neg (show k ≠ j from fun he => hij (hki ▸ he)), hki]
        exact hvi
      exact ⟨hq, hv, hvU⟩
    · by_cases hkj2 : k = j
      · by_cases hc : st.v j - (U - st.v i) < U
        · left
          simp only [aliasStepCore, if_pos hc, List.mem_append, List.mem_singleton]
          exact Or.inr hkj2
        · right; left
          simp only [aliasStepCore, if_neg hc, List.mem_append, List.mem_singleton]
          exact Or.inr hkj2
      · rcases hk9 with hk | hk | hk
        · rw [hsm] at hk
          rcases List.mem_cons.mp hk with he | hes
          · exact absurd he hki
          · left
            by_cases hc : st.v j - (U - st.v i) < U
            · simp only [aliasStepCore, if_pos hc, List.mem_append]
              exact Or.inl hes
            · simp only [aliasStepCore, if_neg hc]
              exact hes
        · rw [hlg] at hk
          rcases List.mem_cons.mp hk with he | hel
          · exact absurd he hkj2
          · right; left
            by_cases hc : st.v j - (U - st.v i) < U
            · simp only [aliasStepCore, if_pos hc]
              exact hel
            · simp only [aliasStepCore, if_neg hc, List.mem_append]
              exact Or.inl hel
        · right; right
          have hknsm : k ∉ st.small := fun hmem => hk.1 ((h4 k hmem).2.1)
          have hknlg : k ∉ st.large := fun hmem => hk.1 ((h5 k hmem).2.1)
          have hkineq : k ≠ i := fun he => hknsm (by rw [he]; exact hism)
          have hkjneq : k ≠ j := fun he => hknlg (by rw [he]; exact hjsm)
          refine ⟨?_, ?_, ?_⟩
          · show (if k = i then st.v i else st.qN k) ≠ U
            rw [if_neg hkineq]; exact hk.1
          · show (if k = j then st.v j - (U - st.v i) else st.v k)
              = (if k = i then st.v i else st.qN k)
            rw [if_neg hkjneq, if_neg hkineq]; exact hk.2.1
          · show (if k = j then st.v j - (U - st.v i) else st.v k) < U
            rw [if_neg hkjneq]; exact hk.2.2

private lemma aliasInit_pendCount {n : ℕ} (u : Fin n → ℕ) : pendCount (aliasInit u) ≤ n := by
  have h1 := list_length_filter_split (List.finRange n)
    (fun i => decide (n * u i < aliasWeightTotal u)) (fun i => decide (aliasWeightTotal u ≤ n * u i))
    (fun i => by
      by_cases h : n * u i < aliasWeightTotal u
      · simp [h]
      · rw [Nat.not_lt] at h; simp [h])
  show ((List.finRange n).filter (fun i => decide (n * u i < aliasWeightTotal u))).length
      + ((List.finRange n).filter (fun i => decide (aliasWeightTotal u ≤ n * u i))).length ≤ n
  rw [h1, List.length_finRange]

theorem aliasInit_inv {n : ℕ} (u : Fin n → ℕ) : AliasInv u (aliasWeightTotal u) (aliasInit u) := by
  have hcomp : ∀ x : Fin n,
      decide (n * u x < aliasWeightTotal u) = !decide (aliasWeightTotal u ≤ n * u x) := by
    intro x
    by_cases h : n * u x < aliasWeightTotal u
    · simp [h]
    · rw [Nat.not_lt] at h; simp [h]
  refine ⟨List.Nodup.filter _ (List.nodup_finRange n),
    List.Nodup.filter _ (List.nodup_finRange n),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hx' : n * u x < aliasWeightTotal u := by
      simpa using (List.mem_filter.mp hx).2
    have hy' : aliasWeightTotal u ≤ n * u y := by
      simpa using (List.mem_filter.mp hy).2
    intro he
    rw [he] at hx'
    omega
  · intro x hx
    have hx' : n * u x < aliasWeightTotal u := by
      simpa using (List.mem_filter.mp hx).2
    exact ⟨hx', rfl, rfl⟩
  · intro x hx
    have hx' : aliasWeightTotal u ≤ n * u x := by
      simpa using (List.mem_filter.mp hx).2
    exact ⟨hx', rfl, rfl⟩
  · have h1 := list_sum_filter_split (List.finRange n)
      (fun i => decide (n * u i < aliasWeightTotal u)) (fun i => decide (aliasWeightTotal u ≤ n * u i))
      (fun i => n * u i) hcomp
    show (((List.finRange n).filter (fun i => decide (n * u i < aliasWeightTotal u))).map
          (fun i => n * u i)).sum
        + (((List.finRange n).filter (fun i => decide (aliasWeightTotal u ≤ n * u i))).map
          (fun i => n * u i)).sum
        + 0 * aliasWeightTotal u = n * aliasWeightTotal u
    rw [h1, Nat.zero_mul, Nat.add_zero, listSum_finRange (fun i => n * u i)]
    show (∑ i : Fin n, n * u i) = n * (∑ i : Fin n, u i)
    rw [Finset.mul_sum]
  · have h1 := list_length_filter_split (List.finRange n)
      (fun i => decide (n * u i < aliasWeightTotal u)) (fun i => decide (aliasWeightTotal u ≤ n * u i))
      hcomp
    show ((List.finRange n).filter (fun i => decide (n * u i < aliasWeightTotal u))).length
        + ((List.finRange n).filter (fun i => decide (aliasWeightTotal u ≤ n * u i))).length
        + 0 = n
    rw [h1, List.length_finRange]
    omega
  · intro k
    have hfil : (Finset.univ.filter (fun i => i ≠ k ∧ (aliasInit u).al i = k)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.notMem_empty]
      exact iff_of_false (fun h => h.2.1 h.2.2) (fun h => h.elim)
    show (aliasInit u).v k + ∑ i ∈ Finset.univ.filter
        (fun i => i ≠ k ∧ (aliasInit u).al i = k), (aliasWeightTotal u - (aliasInit u).qN i) = n * u k
    rw [hfil, Finset.sum_empty]
    rfl
  · intro k
    by_cases h : decide (n * u k < aliasWeightTotal u) = true
    · left
      show k ∈ (List.finRange n).filter (fun i => decide (n * u i < aliasWeightTotal u))
      exact List.mem_filter.mpr ⟨List.mem_finRange k, h⟩
    · right; left
      show k ∈ (List.finRange n).filter (fun i => decide (aliasWeightTotal u ≤ n * u i))
      have hlt : ¬ (n * u k < aliasWeightTotal u) := by simpa using h
      rw [Nat.not_lt] at hlt
      exact List.mem_filter.mpr ⟨List.mem_finRange k, by exact decide_eq_true hlt⟩

theorem aliasRun_inv {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n) (h : AliasInv u U st)
    (fuel : ℕ) (hf : pendCount st ≤ fuel) :
    AliasInv u U (aliasRun U fuel st) ∧ (aliasRun U fuel st).small = [] := by
  induction fuel generalizing st with
  | zero =>
    refine ⟨h, ?_⟩
    by_contra hs
    have hlen : st.small.length ≠ 0 := by
      intro he
      exact hs (List.length_eq_zero_iff.mp he)
    have : pendCount st ≤ 0 := hf
    simp only [pendCount] at this
    omega
  | succ f ih =>
    by_cases hE : st.small = [] ∨ st.large = []
    · simp only [aliasRun, if_pos hE]
      refine ⟨h, ?_⟩
      rcases hE with hS | hL
      · exact hS
      · exact no_small_without_large u U st h hL
    · have hne : st.small ≠ [] ∧ st.large ≠ [] := by
        push Not at hE
        exact hE
      obtain ⟨i, s', hsm⟩ := List.exists_cons_of_ne_nil hne.1
      obtain ⟨j, l', hlg⟩ := List.exists_cons_of_ne_nil hne.2
      have hstep : aliasStep U st = aliasStepCore U i j s' l' st := by
        simp [aliasStep, hsm, hlg]
      have hinv' : AliasInv u U (aliasStep U st) := by
        rw [hstep]
        exact aliasStepCore_inv u U st i j s' l' hsm hlg h
      have hpc : pendCount (aliasStep U st) + 1 = pendCount st := by
        rw [hstep]
        exact aliasStepCore_pendCount U i j s' l' st hsm hlg
      have hf' : pendCount (aliasStep U st) ≤ f := by omega
      simp only [aliasRun, if_neg hE]
      exact ih (aliasStep U st) hinv' hf'

theorem aliasTable_spec {n : ℕ} (u : Fin n → ℕ) :
    AliasInv u (aliasWeightTotal u) (aliasTable u) ∧ (aliasTable u).small = [] :=
  aliasRun_inv u (aliasWeightTotal u) (aliasInit u) (aliasInit_inv u) n (aliasInit_pendCount u)

theorem aliasTable_inv {n : ℕ} (u : Fin n → ℕ) : AliasInv u (aliasWeightTotal u) (aliasTable u) :=
  (aliasTable_spec u).1

theorem aliasTable_small_empty {n : ℕ} (u : Fin n → ℕ) : (aliasTable u).small = [] :=
  (aliasTable_spec u).2

theorem aliasTable_steps_le {n : ℕ} (u : Fin n → ℕ) : (aliasTable u).steps ≤ n := by
  obtain ⟨_, _, _, _, _, _, h7, _, _⟩ := aliasTable_inv u
  omega

theorem aliasTable_pend_eq {n : ℕ} (u : Fin n → ℕ) :
    pendCount (aliasTable u) + (aliasTable u).steps = n := by
  obtain ⟨_, _, _, _, _, _, h7, _, _⟩ := aliasTable_inv u
  exact h7

theorem aliasTable_leftover_eq {n : ℕ} (u : Fin n → ℕ) (x : Fin n)
    (hx : x ∈ (aliasTable u).large) : (aliasTable u).v x = aliasWeightTotal u := by
  obtain ⟨h, hs⟩ := aliasTable_spec u
  obtain ⟨_, _, _, _, h5, h6, h7, _, _⟩ := h
  have h3' : pendCount (aliasTable u) * aliasWeightTotal u + (aliasTable u).steps * aliasWeightTotal u
      = n * aliasWeightTotal u := by
    rw [← Nat.add_mul, h7]
  have h3 : pendSum (aliasTable u) = pendCount (aliasTable u) * aliasWeightTotal u := by omega
  have hall : ∀ y ∈ (aliasTable u).large, aliasWeightTotal u ≤ (aliasTable u).v y :=
    fun y hy => (h5 y hy).1
  have hsum : ((aliasTable u).large.map (aliasTable u).v).sum
      = (aliasTable u).large.length * aliasWeightTotal u := by
    simp only [pendSum, pendCount, hs, List.map_nil, List.sum_nil, List.length_nil,
      Nat.zero_add] at h3
    omega
  exact list_all_eq_of_sum_eq _ _ _ hall hsum x hx

theorem aliasTable_v_eq_qN {n : ℕ} (u : Fin n → ℕ) (k : Fin n) :
    (aliasTable u).v k = (aliasTable u).qN k := by
  obtain ⟨h, hs⟩ := aliasTable_spec u
  obtain ⟨_, _, _, _, h5, _, _, _, h9⟩ := h
  rcases h9 k with hk | hk | hk
  · exact absurd hk (by rw [hs]; simp)
  · have hv := aliasTable_leftover_eq u k hk
    have hq := (h5 k hk).2.1
    omega
  · exact hk.2.1

theorem aliasTable_qN_le {n : ℕ} (u : Fin n → ℕ) (i : Fin n) :
    (aliasTable u).qN i ≤ aliasWeightTotal u := by
  obtain ⟨h, hs⟩ := aliasTable_spec u
  obtain ⟨_, _, _, _, h5, _, _, _, h9⟩ := h
  rcases h9 i with hi | hi | hi
  · exact absurd hi (by rw [hs]; simp)
  · exact (h5 i hi).2.1 ▸ Nat.le_refl _
  · omega

theorem aliasTable_accounting {n : ℕ} (u : Fin n → ℕ) (k : Fin n) :
    (aliasTable u).qN k + ∑ i ∈ Finset.univ.filter
        (fun i => i ≠ k ∧ (aliasTable u).al i = k),
        (aliasWeightTotal u - (aliasTable u).qN i) = n * u k := by
  obtain ⟨_, _, _, _, _, _, _, h8, _⟩ := aliasTable_inv u
  have hv := aliasTable_v_eq_qN u k
  have h := h8 k
  rw [aliasMassOf, hv] at h
  exact h

theorem aliasTable_dist {n : ℕ} (u : Fin n → ℕ) (hU : 0 < aliasWeightTotal u) (k : Fin n) :
    aliasDist (aliasTable u) (aliasWeightTotal u) k = ((u k : ℕ) : ℚ) / aliasWeightTotal u := by
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hz : aliasWeightTotal u = 0 := by simp [aliasWeightTotal]
    omega
  have hUq : ((aliasWeightTotal u : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hU.ne'
  have hnq : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hacc := aliasTable_accounting u k
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ (aliasTable u).al i = k),
      (1 - ((aliasTable u).qN i : ℚ) / aliasWeightTotal u)
      = (∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ (aliasTable u).al i = k),
          (((aliasWeightTotal u - (aliasTable u).qN i : ℕ) : ℚ))) / aliasWeightTotal u := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_div_iff hUq, sub_mul, one_mul, div_mul_cancel₀ _ hUq,
      Nat.cast_sub (aliasTable_qN_le u i)]
  have hcast : (((aliasTable u).qN k : ℕ) : ℚ)
      + ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ (aliasTable u).al i = k),
          (((aliasWeightTotal u - (aliasTable u).qN i : ℕ) : ℚ))
      = ((n * u k : ℕ) : ℚ) := by
    exact_mod_cast hacc
  simp only [aliasDist, hsum]
  rw [← add_div, div_div, hcast, Nat.cast_mul,
    mul_comm ((aliasWeightTotal u : ℕ) : ℚ) ((n : ℕ) : ℚ), mul_div_mul_left _ _ hnq]

theorem AliasInv_reorder {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n)
    (s l : List (Fin n)) (h : AliasInv u U st)
    (hs : s.Perm st.small) (hl : l.Perm st.large) :
    AliasInv u U { st with small := s, large := l } := by
  have hss := (hs.map st.v).sum_eq
  have hls := (hl.map st.v).sum_eq
  simpa only [AliasInv, pendSum, pendCount, aliasMassOf, hs.nodup_iff, hl.nodup_iff,
    hs.mem_iff, hl.mem_iff, hs.length_eq, hl.length_eq, hss, hls] using h

def aliasStackCore {n : ℕ} (U : ℕ) (i j : Fin n) (s' l' : List (Fin n)) (st : AliasSt n) :
    AliasSt n :=
  { small := if st.v j - (U - st.v i) < U then j :: s' else s'
    large := if st.v j - (U - st.v i) < U then l' else j :: l'
    v := fun k => if k = j then st.v j - (U - st.v i) else st.v k
    qN := fun k => if k = i then st.v i else st.qN k
    al := fun k => if k = i then j else st.al k
    steps := st.steps + 1 }

theorem aliasStackCore_inv {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n) (i j : Fin n)
    (s' l' : List (Fin n)) (hsm : st.small = i :: s') (hlg : st.large = j :: l')
    (h : AliasInv u U st) : AliasInv u U (aliasStackCore U i j s' l' st) := by
  apply AliasInv_reorder u U (aliasStepCore U i j s' l' st) _ _
    (aliasStepCore_inv u U st i j s' l' hsm hlg h)
  · by_cases hc : st.v j - (U - st.v i) < U
    · simpa only [aliasStepCore, hc, ↓reduceIte] using (List.perm_append_singleton j s').symm
    · simp [aliasStepCore, hc]
  · by_cases hc : st.v j - (U - st.v i) < U
    · simp [aliasStepCore, hc]
    · simpa only [aliasStepCore, hc, ↓reduceIte] using (List.perm_append_singleton j l').symm

theorem aliasStackCore_pendCount {n : ℕ} (U : ℕ) (i j : Fin n) (s' l' : List (Fin n))
    (st : AliasSt n) (hsm : st.small = i :: s') (hlg : st.large = j :: l') :
    pendCount (aliasStackCore U i j s' l' st) + 1 = pendCount st := by
  by_cases hc : st.v j - (U - st.v i) < U <;>
    simp [aliasStackCore, pendCount, hsm, hlg, hc] <;> omega

def aliasStackStep {n : ℕ} (U : ℕ) (st : AliasSt n) : AliasSt n :=
  match st.small, st.large with
  | i :: s', j :: l' => aliasStackCore U i j s' l' st
  | _, _ => st

def aliasStackRun {n : ℕ} (U : ℕ) : ℕ → AliasSt n → AliasSt n
  | 0, st => st
  | f + 1, st => if st.small = [] ∨ st.large = [] then st
      else aliasStackRun U f (aliasStackStep U st)

theorem aliasStackRun_inv {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n)
    (h : AliasInv u U st) (fuel : ℕ) (hf : pendCount st ≤ fuel) :
    AliasInv u U (aliasStackRun U fuel st) ∧ (aliasStackRun U fuel st).small = [] := by
  induction fuel generalizing st with
  | zero =>
    refine ⟨h, ?_⟩
    have hs : st.small.length = 0 := by unfold pendCount at hf; omega
    exact List.length_eq_zero_iff.mp hs
  | succ f ih =>
    by_cases he : st.small = [] ∨ st.large = []
    · simp only [aliasStackRun, if_pos he]
      refine ⟨h, ?_⟩
      rcases he with hs | hl
      · exact hs
      · exact no_small_without_large u U st h hl
    · have hne : st.small ≠ [] ∧ st.large ≠ [] := not_or.mp he
      obtain ⟨i, s', hsm⟩ := List.exists_cons_of_ne_nil hne.1
      obtain ⟨j, l', hlg⟩ := List.exists_cons_of_ne_nil hne.2
      have hstep : aliasStackStep U st = aliasStackCore U i j s' l' st := by
        simp [aliasStackStep, hsm, hlg]
      have hinv : AliasInv u U (aliasStackStep U st) := by
        rw [hstep]
        exact aliasStackCore_inv u U st i j s' l' hsm hlg h
      have hpc : pendCount (aliasStackStep U st) + 1 = pendCount st := by
        rw [hstep]
        exact aliasStackCore_pendCount U i j s' l' st hsm hlg
      simp only [aliasStackRun, if_neg he]
      exact ih _ hinv (by omega)

def aliasStackTable {n : ℕ} (u : Fin n → ℕ) : AliasSt n :=
  aliasStackRun (aliasWeightTotal u) n (aliasInit u)

theorem aliasStackTable_spec {n : ℕ} (u : Fin n → ℕ) :
    AliasInv u (aliasWeightTotal u) (aliasStackTable u) ∧ (aliasStackTable u).small = [] := by
  have h := aliasInit_inv u
  have hc := h.2.2.2.2.2.2.1
  have hz : (aliasInit u).steps = 0 := rfl
  exact aliasStackRun_inv u (aliasWeightTotal u) (aliasInit u) h n (by omega)

theorem aliasStackTable_inv {n : ℕ} (u : Fin n → ℕ) :
    AliasInv u (aliasWeightTotal u) (aliasStackTable u) := (aliasStackTable_spec u).1

theorem aliasStackTable_small_empty {n : ℕ} (u : Fin n → ℕ) :
    (aliasStackTable u).small = [] := (aliasStackTable_spec u).2

theorem aliasStackTable_steps_le {n : ℕ} (u : Fin n → ℕ) : (aliasStackTable u).steps ≤ n := by
  obtain ⟨_, _, _, _, _, _, h7, _, _⟩ := aliasStackTable_inv u
  omega

theorem aliasStackTable_pend_eq {n : ℕ} (u : Fin n → ℕ) :
    pendCount (aliasStackTable u) + (aliasStackTable u).steps = n := by
  obtain ⟨_, _, _, _, _, _, h7, _, _⟩ := aliasStackTable_inv u
  exact h7

theorem aliasStackTable_leftover_eq {n : ℕ} (u : Fin n → ℕ) (x : Fin n)
    (hx : x ∈ (aliasStackTable u).large) : (aliasStackTable u).v x = aliasWeightTotal u := by
  obtain ⟨h, hs⟩ := aliasStackTable_spec u
  obtain ⟨_, _, _, _, h5, h6, h7, _, _⟩ := h
  have h3' : pendCount (aliasStackTable u) * aliasWeightTotal u + (aliasStackTable u).steps * aliasWeightTotal u
      = n * aliasWeightTotal u := by
    rw [← Nat.add_mul, h7]
  have h3 : pendSum (aliasStackTable u) = pendCount (aliasStackTable u) * aliasWeightTotal u := by
    omega
  have hall : ∀ y ∈ (aliasStackTable u).large, aliasWeightTotal u ≤ (aliasStackTable u).v y :=
    fun y hy => (h5 y hy).1
  have hsum : ((aliasStackTable u).large.map (aliasStackTable u).v).sum
      = (aliasStackTable u).large.length * aliasWeightTotal u := by
    simp only [pendSum, pendCount, hs, List.map_nil, List.sum_nil, List.length_nil,
      Nat.zero_add] at h3
    omega
  exact list_all_eq_of_sum_eq _ _ _ hall hsum x hx

theorem aliasStackTable_v_eq_qN {n : ℕ} (u : Fin n → ℕ) (k : Fin n) :
    (aliasStackTable u).v k = (aliasStackTable u).qN k := by
  obtain ⟨h, hs⟩ := aliasStackTable_spec u
  obtain ⟨_, _, _, _, h5, _, _, _, h9⟩ := h
  rcases h9 k with hk | hk | hk
  · exact absurd hk (by rw [hs]; simp)
  · have hv := aliasStackTable_leftover_eq u k hk
    have hq := (h5 k hk).2.1
    omega
  · exact hk.2.1

theorem aliasStackTable_qN_le {n : ℕ} (u : Fin n → ℕ) (i : Fin n) :
    (aliasStackTable u).qN i ≤ aliasWeightTotal u := by
  obtain ⟨h, hs⟩ := aliasStackTable_spec u
  obtain ⟨_, _, _, _, h5, _, _, _, h9⟩ := h
  rcases h9 i with hi | hi | hi
  · exact absurd hi (by rw [hs]; simp)
  · exact (h5 i hi).2.1 ▸ Nat.le_refl _
  · omega

theorem aliasStackTable_accounting {n : ℕ} (u : Fin n → ℕ) (k : Fin n) :
    (aliasStackTable u).qN k + ∑ i ∈ Finset.univ.filter
        (fun i => i ≠ k ∧ (aliasStackTable u).al i = k),
        (aliasWeightTotal u - (aliasStackTable u).qN i) = n * u k := by
  obtain ⟨_, _, _, _, _, _, _, h8, _⟩ := aliasStackTable_inv u
  have hv := aliasStackTable_v_eq_qN u k
  have h := h8 k
  rw [aliasMassOf, hv] at h
  exact h

theorem aliasStackTable_dist {n : ℕ} (u : Fin n → ℕ) (hU : 0 < aliasWeightTotal u) (k : Fin n) :
    aliasDist (aliasStackTable u) (aliasWeightTotal u) k = ((u k : ℕ) : ℚ) / aliasWeightTotal u := by
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hz : aliasWeightTotal u = 0 := by simp [aliasWeightTotal]
    omega
  have hUq : ((aliasWeightTotal u : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hU.ne'
  have hnq : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hacc := aliasStackTable_accounting u k
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ (aliasStackTable u).al i = k),
      (1 - ((aliasStackTable u).qN i : ℚ) / aliasWeightTotal u)
      = (∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ (aliasStackTable u).al i = k),
          (((aliasWeightTotal u - (aliasStackTable u).qN i : ℕ) : ℚ))) / aliasWeightTotal u := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_div_iff hUq, sub_mul, one_mul, div_mul_cancel₀ _ hUq,
      Nat.cast_sub (aliasStackTable_qN_le u i)]
  have hcast : (((aliasStackTable u).qN k : ℕ) : ℚ)
      + ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ (aliasStackTable u).al i = k),
          (((aliasWeightTotal u - (aliasStackTable u).qN i : ℕ) : ℚ))
      = ((n * u k : ℕ) : ℚ) := by
    exact_mod_cast hacc
  simp only [aliasDist, hsum]
  rw [← add_div, div_div, hcast, Nat.cast_mul,
    mul_comm ((aliasWeightTotal u : ℕ) : ℚ) ((n : ℕ) : ℚ), mul_div_mul_left _ _ hnq]

abbrev WordArray (n : ℕ) (α : Type) := { a : Array α // a.size = n }

def wordRead {n : ℕ} {α : Type} (a : WordArray n α) (i : Fin n) : α :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

def wordWrite {n : ℕ} {α : Type} (a : WordArray n α) (i : Fin n) (x : α) : WordArray n α :=
  ⟨a.val.setIfInBounds i.val x, (Array.size_setIfInBounds).trans a.property⟩

def wordArray {n : ℕ} {α : Type} (f : Fin n → α) : WordArray n α :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

@[simp] theorem wordRead_wordArray {n : ℕ} {α : Type} (f : Fin n → α) (i : Fin n) :
    wordRead (wordArray f) i = f i := by simp [wordRead, wordArray]

@[simp] theorem wordRead_wordWrite {n : ℕ} {α : Type} (a : WordArray n α)
    (i k : Fin n) (x : α) : wordRead (wordWrite a i x) k = if k = i then x else wordRead a k := by
  have hk : k.val < a.val.size := by rw [a.property]; exact k.isLt
  have h := Array.getElem_setIfInBounds (xs := a.val) (i := i.val) (a := x) hk
  simpa only [wordRead, wordWrite, Fin.ext_iff, eq_comm] using h

structure AliasRAM (n : ℕ) where
  v : WordArray n ℕ
  qN : WordArray n ℕ
  al : WordArray n (Fin n)
  small : List (Fin n)
  large : List (Fin n)
  exchanges : ℕ
  i : Option (Fin n)
  j : Option (Fin n)
  x : ℕ
  y : ℕ
  gap : ℕ
  residual : ℕ
  below : Bool

def ramView {n : ℕ} (m : AliasRAM n) : AliasSt n where
  small := m.small
  large := m.large
  v := wordRead m.v
  qN := wordRead m.qN
  al := wordRead m.al
  steps := m.exchanges

def ramRepresentation {n : ℕ} (s : AliasSt n) : AliasRAM n where
  v := wordArray s.v
  qN := wordArray s.qN
  al := wordArray s.al
  small := s.small
  large := s.large
  exchanges := s.steps
  i := none
  j := none
  x := 0
  y := 0
  gap := 0
  residual := 0
  below := false

@[simp] theorem ramView_representation {n : ℕ} (s : AliasSt n) :
    ramView (ramRepresentation s) = s := by
  cases s
  simp [ramView, ramRepresentation, funext_iff]

inductive AliasRamOp where
  | popSmall | popLarge | loadSmall | loadLarge | subtractGap | subtractLarge
  | storeThreshold | storeAlias | storeLarge | compareCapacity
  | pushSmallWhen | pushLargeUnless | exchangeDone
  | controlSmall | controlLarge | branchWork
  | inputBucket (i : ℕ) | inputThreshold (r : ℕ)
  | loadThreshold | loadAlias | compareThreshold | selectOutput
  deriving DecidableEq, Repr

def ramOp {n : ℕ} (U : ℕ) (op : AliasRamOp) (m : AliasRAM n) : AliasRAM n :=
  match op with
  | .popSmall => { m with i := m.small.head?, small := m.small.tail }
  | .popLarge => { m with j := m.large.head?, large := m.large.tail }
  | .loadSmall => { m with x := m.i.elim 0 (wordRead m.v) }
  | .loadLarge => { m with y := m.j.elim 0 (wordRead m.v) }
  | .subtractGap => { m with gap := U - m.x }
  | .subtractLarge => { m with residual := m.y - m.gap }
  | .storeThreshold => match m.i with
    | none => m
    | some i => { m with qN := wordWrite m.qN i m.x }
  | .storeAlias => match m.i, m.j with
    | some i, some j => { m with al := wordWrite m.al i j }
    | _, _ => m
  | .storeLarge => match m.j with
    | none => m
    | some j => { m with v := wordWrite m.v j m.residual }
  | .compareCapacity => { m with below := decide (m.residual < U) }
  | .pushSmallWhen => if m.below then match m.j with
    | some j => { m with small := j :: m.small }
    | none => m
    else m
  | .pushLargeUnless => if m.below then m else match m.j with
    | some j => { m with large := j :: m.large }
    | none => m
  | .exchangeDone => { m with exchanges := m.exchanges + 1 }
  | .controlSmall => { m with x := if m.small = [] then 1 else 0 }
  | .controlLarge => { m with y := if m.large = [] then 1 else 0 }
  | .branchWork => { m with below := decide (m.x = 0 ∧ m.y = 0) }
  | .inputBucket a => { m with i := if h : a < n then some ⟨a, h⟩ else none }
  | .inputThreshold r => { m with y := r }
  | .loadThreshold => { m with x := m.i.elim 0 (wordRead m.qN) }
  | .loadAlias => { m with j := m.i.map (wordRead m.al) }
  | .compareThreshold => { m with below := decide (m.y < m.x) }
  | .selectOutput => { m with i := if m.below then m.i else m.j }

def ramExchangeCode : List AliasRamOp :=
  [.popSmall, .popLarge, .loadSmall, .loadLarge, .subtractGap, .subtractLarge,
    .storeThreshold, .storeAlias, .storeLarge, .compareCapacity,
    .pushSmallWhen, .pushLargeUnless, .exchangeDone]

def ramRun {n : ℕ} (U : ℕ) (code : List AliasRamOp) (m : AliasRAM n) : AliasRAM n :=
  code.foldl (fun m op => ramOp U op m) m

inductive RamExec {n : ℕ} (U : ℕ) : AliasRAM n → List AliasRamOp → AliasRAM n → Prop where
  | nil (m) : RamExec U m [] m
  | cons (m) (op) (ops) (m') : RamExec U (ramOp U op m) ops m' → RamExec U m (op :: ops) m'

theorem ramRun_exec {n : ℕ} (U : ℕ) (code : List AliasRamOp) (m : AliasRAM n) :
    RamExec U m code (ramRun U code m) := by
  induction code generalizing m with
  | nil => exact .nil m
  | cons op ops ih => exact .cons m op ops _ (ih _)

theorem ramExchangeCode_length : ramExchangeCode.length = 13 := rfl

set_option maxHeartbeats 2000000 in

theorem ramExchange_refines {n : ℕ} (U : ℕ) (m : AliasRAM n) (i j : Fin n)
    (s' l' : List (Fin n)) (hs : m.small = i :: s') (hl : m.large = j :: l') :
    ramView (ramRun U ramExchangeCode m) = aliasStackCore U i j s' l' (ramView m) := by
  by_cases hc : wordRead m.v j - (U - wordRead m.v i) < U <;>
    simp [ramRun, ramExchangeCode, List.foldl_cons, ramOp, hs, hl, ramView,
      aliasStackCore, hc, funext_iff]

def ramControlCode : List AliasRamOp := [.controlSmall, .controlLarge, .branchWork]

theorem ramControl_view {n : ℕ} (U : ℕ) (m : AliasRAM n) :
    ramView (ramRun U ramControlCode m) = ramView m := rfl

theorem ramControl_work {n : ℕ} (U : ℕ) (m : AliasRAM n) :
    (ramRun U ramControlCode m).below = decide (¬ (m.small = [] ∨ m.large = [])) := by
  by_cases hs : m.small = [] <;> by_cases hl : m.large = [] <;>
    simp [ramRun, ramControlCode, ramOp, hs, hl]

@[simp] theorem ramRun_nil {n : ℕ} (U : ℕ) (m : AliasRAM n) : ramRun U [] m = m := rfl

theorem ramRun_append {n : ℕ} (U : ℕ) (xs ys : List AliasRamOp) (m : AliasRAM n) :
    ramRun U (xs ++ ys) m = ramRun U ys (ramRun U xs m) := List.foldl_append

def ramLoop {n : ℕ} (U : ℕ) : ℕ → AliasRAM n → AliasRAM n
  | 0, m => m
  | fuel + 1, m =>
    let t := ramRun U ramControlCode m
    if t.below then ramLoop U fuel (ramRun U ramExchangeCode t) else t

def ramLoopCode {n : ℕ} (U : ℕ) : ℕ → AliasRAM n → List AliasRamOp
  | 0, _ => []
  | fuel + 1, m =>
    let t := ramRun U ramControlCode m
    ramControlCode ++ if t.below then
      ramExchangeCode ++ ramLoopCode U fuel (ramRun U ramExchangeCode t) else []

theorem ramLoop_run {n : ℕ} (U : ℕ) (fuel : ℕ) (m : AliasRAM n) :
    ramRun U (ramLoopCode U fuel m) m = ramLoop U fuel m := by
  induction fuel generalizing m with
  | zero => rfl
  | succ fuel ih =>
    simp only [ramLoopCode, ramRun_append, ramLoop]
    split
    · rw [ramRun_append, ih]
    · rfl

theorem ramLoop_exec {n : ℕ} (U : ℕ) (fuel : ℕ) (m : AliasRAM n) :
    RamExec U m (ramLoopCode U fuel m) (ramLoop U fuel m) := by
  rw [← ramLoop_run]
  exact ramRun_exec U _ m

theorem ramLoop_instruction_bound {n : ℕ} (U : ℕ) (fuel : ℕ) (m : AliasRAM n) :
    (ramLoopCode U fuel m).length ≤ 16 * fuel := by
  induction fuel generalizing m with
  | zero => simp [ramLoopCode]
  | succ fuel ih =>
    simp only [ramLoopCode, List.length_append]
    split
    · have h := ih (ramRun U ramExchangeCode (ramRun U ramControlCode m))
      simp only [List.length_append, ramExchangeCode_length] at *
      change 3 + (13 + _) ≤ _
      omega
    · simp [ramControlCode]
      omega

theorem ramLoop_refines {n : ℕ} (U : ℕ) (fuel : ℕ) (m : AliasRAM n) :
    ramView (ramLoop U fuel m) = aliasStackRun U fuel (ramView m) := by
  induction fuel generalizing m with
  | zero => rfl
  | succ fuel ih =>
    have hv := ramControl_view U m
    have hw := ramControl_work U m
    by_cases he : m.small = [] ∨ m.large = []
    · simp only [ramLoop, hw, he, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      rw [hv]
      simp [aliasStackRun, ramView, he]
    · have hne := not_or.mp he
      obtain ⟨i, s', hs⟩ := List.exists_cons_of_ne_nil hne.1
      obtain ⟨j, l', hl⟩ := List.exists_cons_of_ne_nil hne.2
      have hcore := ramExchange_refines U (ramRun U ramControlCode m) i j s' l' hs hl
      rw [hv] at hcore
      simp only [ramLoop, hw, he, not_false_eq_true, decide_true, ↓reduceIte]
      rw [ih, hcore]
      simp [aliasStackRun, aliasStackStep, ramView, hs, hl]

structure AliasInitFrame (n : ℕ) where
  m : AliasRAM n
  total : ℕ
  word : ℕ
  scaled : ℕ
  below : Bool

inductive AliasInitOp (n : ℕ) where
  | clearSmall | clearLarge | clearExchanges | clearTotal
  | readInput (i : Fin n) | addTotal | scaleInput
  | writeV (i : Fin n) | writeQ (i : Fin n) | writeAlias (i : Fin n)
  | compareScaled | pushSmall (i : Fin n) | pushLarge (i : Fin n)
  deriving DecidableEq, Repr

def initOp {n : ℕ} (input : WordArray n ℕ) (op : AliasInitOp n) (s : AliasInitFrame n) :
    AliasInitFrame n :=
  match op with
  | .clearSmall => { s with m := { s.m with small := [] } }
  | .clearLarge => { s with m := { s.m with large := [] } }
  | .clearExchanges => { s with m := { s.m with exchanges := 0 } }
  | .clearTotal => { s with total := 0 }
  | .readInput i => { s with word := wordRead input i }
  | .addTotal => { s with total := s.total + s.word }
  | .scaleInput => { s with scaled := n * s.word }
  | .writeV i => { s with m := { s.m with v := wordWrite s.m.v i s.scaled } }
  | .writeQ i => { s with m := { s.m with qN := wordWrite s.m.qN i s.total } }
  | .writeAlias i => { s with m := { s.m with al := wordWrite s.m.al i i } }
  | .compareScaled => { s with below := decide (s.scaled < s.total) }
  | .pushSmall i => if s.below then { s with m := { s.m with small := i :: s.m.small } } else s
  | .pushLarge i => if s.below then s else { s with m := { s.m with large := i :: s.m.large } }

def initRun {n : ℕ} (input : WordArray n ℕ) (code : List (AliasInitOp n)) (s : AliasInitFrame n) :
    AliasInitFrame n := code.foldl (fun s op => initOp input op s) s

def initResetCode (n : ℕ) : List (AliasInitOp n) :=
  [.clearSmall, .clearLarge, .clearExchanges, .clearTotal]

def initCellCode {n : ℕ} (i : Fin n) : List (AliasInitOp n) :=
  [.readInput i, .scaleInput, .writeV i, .writeQ i, .writeAlias i,
    .compareScaled, .pushSmall i, .pushLarge i]

def initSemanticCell {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (i : Fin n) (s : AliasSt n) : AliasSt n where
  small := if n * u i < U then i :: s.small else s.small
  large := if n * u i < U then s.large else i :: s.large
  v k := if k = i then n * u i else s.v k
  qN k := if k = i then U else s.qN k
  al k := if k = i then i else s.al k
  steps := s.steps

theorem initCellCode_refines {n : ℕ} (input : WordArray n ℕ) (i : Fin n) (s : AliasInitFrame n) :
    ramView (initRun input (initCellCode i) s).m =
      initSemanticCell (wordRead input) s.total i (ramView s.m) := by
  by_cases hc : n * wordRead input i < s.total <;>
    simp [initRun, initCellCode, initOp, ramView, initSemanticCell, hc, funext_iff]

theorem initCellCode_total {n : ℕ} (input : WordArray n ℕ) (i : Fin n) (s : AliasInitFrame n) :
    (initRun input (initCellCode i) s).total = s.total := by
  by_cases hc : n * wordRead input i < s.total <;>
    simp [initRun, initCellCode, initOp, hc]

def initCells {n : ℕ} (input : WordArray n ℕ) (xs : List (Fin n)) (s : AliasInitFrame n) :
    AliasInitFrame n := xs.foldr (fun i s => initRun input (initCellCode i) s) s

def initCellsCode {n : ℕ} (xs : List (Fin n)) : List (AliasInitOp n) :=
  xs.reverse.flatMap initCellCode

theorem initRun_append {n : ℕ} (input : WordArray n ℕ) (xs ys : List (AliasInitOp n))
    (s : AliasInitFrame n) : initRun input (xs ++ ys) s = initRun input ys (initRun input xs s) :=
  List.foldl_append

theorem initCells_run {n : ℕ} (input : WordArray n ℕ) (xs : List (Fin n)) (s : AliasInitFrame n) :
    initRun input (initCellsCode xs) s = initCells input xs s := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [initCellsCode, List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
      initRun_append, initCells, List.foldr_cons] at *
    rw [ih]

theorem initCells_total {n : ℕ} (input : WordArray n ℕ) (xs : List (Fin n)) (s : AliasInitFrame n) :
    (initCells input xs s).total = s.total := by
  induction xs with
  | nil => rfl
  | cons i xs ih => exact (initCellCode_total input i _).trans ih

def initSemanticCells {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (xs : List (Fin n)) (s : AliasSt n) :
    AliasSt n := xs.foldr (initSemanticCell u U) s

theorem initCells_refines {n : ℕ} (input : WordArray n ℕ) (xs : List (Fin n))
    (s : AliasInitFrame n) : ramView (initCells input xs s).m =
      initSemanticCells (wordRead input) s.total xs (ramView s.m) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change ramView (initRun input (initCellCode i) (initCells input xs s)).m = _
    rw [initCellCode_refines, initCells_total, ih]
    rfl

theorem aliasSt_ext {n : ℕ} (s t : AliasSt n) (hs : s.small = t.small) (hl : s.large = t.large)
    (hv : s.v = t.v) (hq : s.qN = t.qN) (ha : s.al = t.al) (hc : s.steps = t.steps) : s = t := by
  cases s
  cases t
  simp_all

theorem initSemanticCells_spec {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (xs : List (Fin n))
    (s : AliasSt n) : initSemanticCells u U xs s =
      { small := xs.filter (fun i => decide (n * u i < U)) ++ s.small
        large := xs.filter (fun i => decide (U ≤ n * u i)) ++ s.large
        v := fun k => if k ∈ xs then n * u k else s.v k
        qN := fun k => if k ∈ xs then U else s.qN k
        al := fun k => if k ∈ xs then k else s.al k
        steps := s.steps } := by
  induction xs with
  | nil => simp [initSemanticCells]
  | cons i xs ih =>
    change initSemanticCell u U i (initSemanticCells u U xs s) = _
    rw [ih]
    apply aliasSt_ext
    · by_cases hc : n * u i < U <;> simp [initSemanticCell, hc]
    · by_cases hc : n * u i < U <;> simp [initSemanticCell, hc, Nat.le_of_not_gt]
    · funext k
      by_cases hk : k = i <;> simp [initSemanticCell, hk]
    · funext k
      by_cases hk : k = i <;> simp [initSemanticCell, hk]
    · funext k
      by_cases hk : k = i <;> simp [initSemanticCell, hk]
    · rfl

def initSum {n : ℕ} (input : WordArray n ℕ) (xs : List (Fin n)) (s : AliasInitFrame n) :
    AliasInitFrame n :=
  xs.foldl (fun s i => initRun input [.readInput i, .addTotal] s) s

def initSumCode {n : ℕ} (xs : List (Fin n)) : List (AliasInitOp n) :=
  xs.flatMap (fun i => [.readInput i, .addTotal])

theorem initSum_run {n : ℕ} (input : WordArray n ℕ) (xs : List (Fin n)) (s : AliasInitFrame n) :
    initRun input (initSumCode xs) s = initSum input xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    simp only [initSumCode, List.flatMap_cons, initRun_append, initSum, List.foldl_cons] at *
    exact ih _

theorem initSum_spec {n : ℕ} (input : WordArray n ℕ) (xs : List (Fin n)) (s : AliasInitFrame n) :
    (initSum input xs s).total = s.total + (xs.map (wordRead input)).sum ∧
      (initSum input xs s).m = s.m := by
  induction xs generalizing s with
  | nil => simp [initSum]
  | cons i xs ih =>
    simpa [initSum, initRun, initOp, Nat.add_assoc] using
      ih (initRun input [.readInput i, .addTotal] s)

def ramInitialize {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) : AliasInitFrame n :=
  let reset := initRun input (initResetCode n) ⟨m, 0, 0, 0, false⟩
  let summed := initSum input (List.finRange n) reset
  initCells input (List.finRange n) summed

theorem ramInitialize_correct {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) :
    (ramInitialize input m).total = aliasWeightTotal (wordRead input) ∧
      ramView (ramInitialize input m).m = aliasInit (wordRead input) := by
  let reset := initRun input (initResetCode n) ⟨m, 0, 0, 0, false⟩
  let summed := initSum input (List.finRange n) reset
  have hsum := initSum_spec input (List.finRange n) reset
  have ht : summed.total = aliasWeightTotal (wordRead input) := by
    change (initSum input (List.finRange n) reset).total = _
    rw [hsum.1, listSum_finRange]
    simp [reset, initRun, initResetCode, initOp, aliasWeightTotal]
  refine ⟨(initCells_total input (List.finRange n) summed).trans ht, ?_⟩
  change ramView (initCells input (List.finRange n) summed).m = _
  rw [initCells_refines, ht, initSemanticCells_spec, hsum.2]
  simp [reset, initRun, initResetCode, initOp, ramView, aliasInit]

def initFullCode (n : ℕ) : List (AliasInitOp n) :=
  initResetCode n ++ initSumCode (List.finRange n) ++ initCellsCode (List.finRange n)

theorem ramInitialize_run {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) :
    initRun input (initFullCode n) ⟨m, 0, 0, 0, false⟩ = ramInitialize input m := by
  simp only [initFullCode, initRun_append, initSum_run, initCells_run, ramInitialize]

theorem initSumCode_length {n : ℕ} (xs : List (Fin n)) :
    (initSumCode xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [initSumCode, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at *
    omega

theorem initCellsCode_length {n : ℕ} (xs : List (Fin n)) :
    (initCellsCode xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [initCellsCode, List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
      List.length_append, List.length_cons] at *
    change _ + 8 = _
    omega

theorem initFullCode_length (n : ℕ) : (initFullCode n).length = 10 * n + 4 := by
  simp only [initFullCode, List.length_append, initSumCode_length, initCellsCode_length,
    List.length_finRange]
  change 4 + 2 * n + 8 * n = _
  omega

def ramPreprocess {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) : AliasRAM n :=
  let s := ramInitialize input m
  ramLoop s.total n s.m

theorem ramPreprocess_refines {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) :
    ramView (ramPreprocess input m) = aliasStackTable (wordRead input) := by
  unfold ramPreprocess
  rw [ramLoop_refines, (ramInitialize_correct input m).1, (ramInitialize_correct input m).2]
  rfl

theorem ramPreprocess_distribution {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hU : 0 < aliasWeightTotal (wordRead input)) (k : Fin n) :
    aliasDist (ramView (ramPreprocess input m)) (aliasWeightTotal (wordRead input)) k =
      ((wordRead input k : ℕ) : ℚ) / aliasWeightTotal (wordRead input) := by
  rw [ramPreprocess_refines]
  exact aliasStackTable_dist (wordRead input) hU k

theorem ramPreprocess_instruction_bound {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) :
    (initFullCode n).length +
      (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length ≤ 26 * n + 4 := by
  rw [initFullCode_length]
  have h := ramLoop_instruction_bound (ramInitialize input m).total n (ramInitialize input m).m
  omega

theorem aliasStackCore_selfAlias {n : ℕ} (U : ℕ) (st : AliasSt n) (i j : Fin n)
    (s' l' : List (Fin n)) (hij : i ≠ j)
    (hself : ∀ k, st.al k = k → st.qN k = U) :
    ∀ k, (aliasStackCore U i j s' l' st).al k = k →
      (aliasStackCore U i j s' l' st).qN k = U := by
  intro k hk
  by_cases hki : k = i
  · subst k
    have hbad : j = i := by simpa [aliasStackCore] using hk
    exact False.elim (hij hbad.symm)
  · have hold : st.al k = k := by simpa [aliasStackCore, hki] using hk
    simpa [aliasStackCore, hki] using hself k hold

theorem aliasStackRun_selfAlias {n : ℕ} (u : Fin n → ℕ) (U : ℕ) (st : AliasSt n)
    (hinv : AliasInv u U st) (hself : ∀ k, st.al k = k → st.qN k = U) (fuel : ℕ) :
    ∀ k, (aliasStackRun U fuel st).al k = k → (aliasStackRun U fuel st).qN k = U := by
  induction fuel generalizing st with
  | zero => exact hself
  | succ fuel ih =>
    by_cases he : st.small = [] ∨ st.large = []
    · simpa [aliasStackRun, he] using hself
    · obtain ⟨i, s', hs⟩ := List.exists_cons_of_ne_nil (not_or.mp he).1
      obtain ⟨j, l', hl⟩ := List.exists_cons_of_ne_nil (not_or.mp he).2
      have hij : i ≠ j := hinv.2.2.1 i (by simp [hs]) j (by simp [hl])
      have hi := aliasStackCore_inv u U st i j s' l' hs hl hinv
      have hh := aliasStackCore_selfAlias U st i j s' l' hij hself
      simpa only [aliasStackRun, if_neg he, aliasStackStep, hs, hl] using! ih _ hi hh

theorem aliasStackTable_selfAlias {n : ℕ} (u : Fin n → ℕ) :
    ∀ k, (aliasStackTable u).al k = k → (aliasStackTable u).qN k = aliasWeightTotal u :=
  aliasStackRun_selfAlias u (aliasWeightTotal u) (aliasInit u) (aliasInit_inv u)
    (by intro k _; rfl) n

def drawOutcome {n U : ℕ} (m : AliasRAM n) (i : Fin n) (r : Fin U) : Fin n :=
  if r.val < wordRead m.qN i then i else wordRead m.al i

def ramDrawCode {n U : ℕ} (i : Fin n) (r : Fin U) : List AliasRamOp :=
  [.inputBucket i.val, .inputThreshold r.val, .loadThreshold, .loadAlias,
    .compareThreshold, .selectOutput]

theorem ramDrawCode_length {n U : ℕ} (i : Fin n) (r : Fin U) :
    (ramDrawCode i r).length = 6 := rfl

theorem ramDraw_refines {n U : ℕ} (m : AliasRAM n) (i : Fin n) (r : Fin U) :
    (ramRun U (ramDrawCode i r) m).i = some (drawOutcome m i r) := by
  by_cases hc : r.val < wordRead m.qN i <;>
    simp [ramRun, ramDrawCode, ramOp, drawOutcome, i.isLt, hc]

theorem ramDraw_preserves_table {n U : ℕ} (m : AliasRAM n) (i : Fin n) (r : Fin U) :
    ramView (ramRun U (ramDrawCode i r) m) = ramView m := by
  simp [ramRun, ramDrawCode, ramOp, ramView]

private theorem threshold_lt_count {U q : ℕ} (h : q ≤ U) :
    (Finset.univ.filter (fun r : Fin U => r.val < q)).card = q := by
  rw [Fin.card_filter_val_lt, min_eq_right h]

private theorem threshold_ge_count {U q : ℕ} (h : q ≤ U) :
    (Finset.univ.filter (fun r : Fin U => q ≤ r.val)).card = U - q := by
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin U)))
    (fun r => r.val < q)
  rw [threshold_lt_count h] at hc
  simp only [Finset.card_univ, Fintype.card_fin, not_lt] at hc
  omega

private theorem drawOutcome_bucket_count {n U : ℕ} (m : AliasRAM n) (i k : Fin n)
    (hq : wordRead m.qN i ≤ U) :
    (Finset.univ.filter (fun r : Fin U => drawOutcome m i r = k)).card =
      (if i = k then wordRead m.qN i else 0) +
        (if wordRead m.al i = k then U - wordRead m.qN i else 0) := by
  have hlow := threshold_lt_count hq
  have hhigh := threshold_ge_count hq
  by_cases hi : i = k <;> by_cases ha : wordRead m.al i = k <;>
    simp_all [drawOutcome, ite_eq_iff, not_lt]

private theorem card_prod_filter {n U : ℕ} (P : Fin n × Fin U → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ i : Fin n, (Finset.univ.filter (fun r : Fin U => P (i, r))).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

theorem drawOutcome_count {n U : ℕ} (m : AliasRAM n)
    (hq : ∀ i, wordRead m.qN i ≤ U)
    (hself : ∀ i, wordRead m.al i = i → wordRead m.qN i = U) (k : Fin n) :
    (Finset.univ.filter (fun p : Fin n × Fin U => drawOutcome m p.1 p.2 = k)).card =
      wordRead m.qN k + ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ wordRead m.al i = k),
        (U - wordRead m.qN i) := by
  rw [card_prod_filter]
  simp_rw [drawOutcome_bucket_count m _ k (hq _)]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = k
  · subst i
    by_cases ha : wordRead m.al k = k
    · simp [ha, hself k ha]
    · simp [ha]
  · simp [hi]

theorem ramPreprocess_threshold {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) (k : Fin n) :
    wordRead (ramPreprocess input m).qN k ≤ aliasWeightTotal (wordRead input) := by
  change (ramView (ramPreprocess input m)).qN k ≤ _
  rw [ramPreprocess_refines]
  exact aliasStackTable_qN_le (wordRead input) k

theorem ramPreprocess_selfAlias {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) (k : Fin n) :
    wordRead (ramPreprocess input m).al k = k →
      wordRead (ramPreprocess input m).qN k = aliasWeightTotal (wordRead input) := by
  change (ramView (ramPreprocess input m)).al k = k → _
  change (ramView (ramPreprocess input m)).al k = k →
    (ramView (ramPreprocess input m)).qN k = _
  rw [ramPreprocess_refines]
  exact aliasStackTable_selfAlias (wordRead input) k

theorem ramPreprocess_draw_count {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n) (k : Fin n) :
    (Finset.univ.filter (fun p : Fin n × Fin (aliasWeightTotal (wordRead input)) =>
      (ramRun (aliasWeightTotal (wordRead input)) (ramDrawCode p.1 p.2) (ramPreprocess input m)).i
        = some k)).card = n * wordRead input k := by
  simp only [ramDraw_refines, Option.some.injEq]
  rw [drawOutcome_count _ (ramPreprocess_threshold input m) (ramPreprocess_selfAlias input m)]
  change (ramView (ramPreprocess input m)).qN k +
    ∑ i ∈ Finset.univ.filter (fun i => i ≠ k ∧ (ramView (ramPreprocess input m)).al i = k),
      (aliasWeightTotal (wordRead input) - (ramView (ramPreprocess input m)).qN i) = _
  rw [ramPreprocess_refines]
  exact aliasStackTable_accounting (wordRead input) k

noncomputable def ramDrawLaw {n U : ℕ} (m : AliasRAM n) (hn : 0 < n) (hU : 0 < U) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Option (Fin n)) where
  prob o := ((Finset.univ.filter (fun p : Fin n × Fin U =>
    (ramRun U (ramDrawCode p.1 p.2) m).i = o)).card : ℝ) / ((n * U : ℕ) : ℝ)
  nonneg _ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  sum_one := by
    rw [← Finset.sum_div]
    have hc : (∑ o : Option (Fin n), (Finset.univ.filter (fun p : Fin n × Fin U =>
        (ramRun U (ramDrawCode p.1 p.2) m).i = o)).card) = n * U := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp
    have hr : (∑ o : Option (Fin n), ((Finset.univ.filter (fun p : Fin n × Fin U =>
        (ramRun U (ramDrawCode p.1 p.2) m).i = o)).card : ℝ)) = ((n * U : ℕ) : ℝ) := by
      exact_mod_cast hc
    rw [hr]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt hn) (Nat.ne_of_gt hU)))

theorem positive_input_size {n : ℕ} (input : WordArray n ℕ)
    (hU : 0 < aliasWeightTotal (wordRead input)) : 0 < n := by
  by_contra h
  have hz : n = 0 := by omega
  subst n
  simp [aliasWeightTotal] at hU

theorem ramDrawLaw_preprocessed {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hU : 0 < aliasWeightTotal (wordRead input)) (k : Fin n) :
    (ramDrawLaw (ramPreprocess input m) (positive_input_size input hU) hU).prob (some k) =
      ((wordRead input k : ℕ) : ℝ) / aliasWeightTotal (wordRead input) := by
  change ((Finset.univ.filter (fun p : Fin n × Fin (aliasWeightTotal (wordRead input)) =>
    (ramRun (aliasWeightTotal (wordRead input)) (ramDrawCode p.1 p.2) (ramPreprocess input m)).i
      = some k)).card : ℝ) / _ = _
  rw [ramPreprocess_draw_count, Nat.cast_mul]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (positive_input_size input hU))
  simp only [Nat.cast_mul]
  exact mul_div_mul_left _ _ hn

private theorem drawOutcome_of_view_eq {n U : ℕ} (a b : AliasRAM n)
    (h : ramView a = ramView b) (i : Fin n) (r : Fin U) : drawOutcome a i r = drawOutcome b i r := by
  have hq := congrArg (fun s : AliasSt n => s.qN i) h
  have ha := congrArg (fun s : AliasSt n => s.al i) h
  change wordRead a.qN i = wordRead b.qN i at hq
  change wordRead a.al i = wordRead b.al i at ha
  simp only [drawOutcome, hq, ha]

def ramSamplesAcc {n U : ℕ} : List (Fin n × Fin U) → AliasRAM n →
    List (Option (Fin n)) → List (Option (Fin n)) × AliasRAM n
  | [], m, out => (out, m)
  | p :: ps, m, out =>
    let t := ramRun U (ramDrawCode p.1 p.2) m
    ramSamplesAcc ps t (t.i :: out)

inductive SampleEvent where
  | readPair | word (op : AliasRamOp) | emitOutput | done
  deriving DecidableEq, Repr

def ramSamplesTrace {n U : ℕ} : List (Fin n × Fin U) → AliasRAM n → List SampleEvent
  | [], _ => [.done]
  | p :: ps, m =>
    let t := ramRun U (ramDrawCode p.1 p.2) m
    .readPair :: (ramDrawCode p.1 p.2).map .word ++
      .emitOutput :: ramSamplesTrace ps t

inductive SamplesExec {n U : ℕ} : List (Fin n × Fin U) → AliasRAM n → List (Option (Fin n)) →
    List SampleEvent → List (Option (Fin n)) → AliasRAM n → Prop where
  | done (m out) : SamplesExec [] m out [.done] out m
  | step (p ps m out t trace result final) :
      RamExec U m (ramDrawCode p.1 p.2) t →
      SamplesExec ps t (t.i :: out) trace result final →
      SamplesExec (p :: ps) m out
        (.readPair :: (ramDrawCode p.1 p.2).map .word ++ .emitOutput :: trace) result final

theorem ramSamples_exec {n U : ℕ} (ps : List (Fin n × Fin U)) (m : AliasRAM n)
    (out : List (Option (Fin n))) :
    SamplesExec ps m out (ramSamplesTrace ps m)
      (ramSamplesAcc ps m out).1 (ramSamplesAcc ps m out).2 := by
  induction ps generalizing m out with
  | nil => exact .done m out
  | cons p ps ih =>
    exact .step p ps m out _ _ _ _ (ramRun_exec U _ m) (ih _ _)

theorem ramSamples_instruction_count {n U : ℕ} (ps : List (Fin n × Fin U)) (m : AliasRAM n) :
    (ramSamplesTrace ps m).length = 8 * ps.length + 1 := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    simp only [ramSamplesTrace, List.length_append, List.length_cons, List.length_map,
      ramDrawCode_length, ih]
    omega

theorem ramSamples_correct {n U : ℕ} (ps : List (Fin n × Fin U)) (m : AliasRAM n)
    (out : List (Option (Fin n))) :
    (ramSamplesAcc ps m out).1 = (ps.map (fun p => some (drawOutcome m p.1 p.2))).reverse ++ out ∧
      ramView (ramSamplesAcc ps m out).2 = ramView m := by
  induction ps generalizing m out with
  | nil => simp [ramSamplesAcc]
  | cons p ps ih =>
    let t := ramRun U (ramDrawCode p.1 p.2) m
    have htable := ramDraw_preserves_table m p.1 p.2
    have hi := ih t (t.i :: out)
    have hmap : ps.map (fun p => some (drawOutcome t p.1 p.2)) =
        ps.map (fun p => some (drawOutcome m p.1 p.2)) := by
      apply List.map_congr_left
      intro p' _
      rw [drawOutcome_of_view_eq t m htable]
    refine ⟨?_, hi.2.trans htable⟩
    simpa only [ramSamplesAcc, hmap, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, t, ramDraw_refines] using hi.1

theorem ramPreprocess_and_samples_bound {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (ps : List (Fin n × Fin (aliasWeightTotal (wordRead input)))) :
    (initFullCode n).length +
      (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length +
      (ramSamplesTrace ps (ramPreprocess input m)).length ≤ 26 * n + 8 * ps.length + 5 := by
  have hp := ramPreprocess_instruction_bound input m
  rw [ramSamples_instruction_count]
  omega

theorem ram_amortize_budget_iff (n q : ℕ) :
    (26 * n + 4 ≤ 8 * q) ↔ (26 * n + 11) / 8 ≤ q := by omega

def ramStackSize {n : ℕ} (m : AliasRAM n) : ℕ := m.small.length + m.large.length

def ramWorkspaceWords {n : ℕ} (m : AliasRAM n) (codeWords : ℕ) : ℕ :=
  3 * n + 2 * ramStackSize m + 24 + 3 * codeWords

theorem ramOp_stack_bound {n : ℕ} (U : ℕ) (op : AliasRamOp) (m : AliasRAM n) :
    ramStackSize (ramOp U op m) ≤ ramStackSize m + 1 := by
  cases op <;> cases hi : m.i <;> cases hj : m.j <;> cases hb : m.below <;>
    simp_all [ramOp, ramStackSize] <;> omega

theorem initOp_stack_bound {n : ℕ} (input : WordArray n ℕ) (op : AliasInitOp n)
    (s : AliasInitFrame n) : ramStackSize (initOp input op s).m ≤ ramStackSize s.m + 1 := by
  cases op <;> cases hb : s.below <;> simp_all [initOp, ramStackSize] <;> omega

theorem ramRun_stack_bound {n : ℕ} (U : ℕ) (ops : List AliasRamOp) (m : AliasRAM n) :
    ramStackSize (ramRun U ops m) ≤ ramStackSize m + ops.length := by
  induction ops generalizing m with
  | nil => simp [ramRun]
  | cons op ops ih =>
    have h := ih (ramOp U op m)
    have hs := ramOp_stack_bound U op m
    change ramStackSize (ramRun U ops (ramOp U op m)) ≤ _
    simp only [List.length_cons]
    omega

theorem initRun_stack_bound {n : ℕ} (input : WordArray n ℕ) (ops : List (AliasInitOp n))
    (s : AliasInitFrame n) : ramStackSize (initRun input ops s).m ≤ ramStackSize s.m + ops.length := by
  induction ops generalizing s with
  | nil => simp [initRun]
  | cons op ops ih =>
    have h := ih (initOp input op s)
    have hs := initOp_stack_bound input op s
    change ramStackSize (initRun input ops (initOp input op s)).m ≤ _
    simp only [List.length_cons]
    omega

theorem ramInitialize_stack_bound {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hs : m.small = []) (hl : m.large = []) :
    ramStackSize (ramInitialize input m).m ≤ 10 * n + 4 := by
  have h := initRun_stack_bound input (initFullCode n) ⟨m, 0, 0, 0, false⟩
  rw [ramInitialize_run, initFullCode_length] at h
  simpa [ramStackSize, hs, hl] using h

theorem ramInitialize_prefix_space {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hs : m.small = []) (hl : m.large = []) (k : ℕ) :
    ramWorkspaceWords (initRun input ((initFullCode n).take k) ⟨m, 0, 0, 0, false⟩).m
      ((initFullCode n).length +
        (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length)
      ≤ 133 * n + 44 := by
  have hstack := initRun_stack_bound input ((initFullCode n).take k) ⟨m, 0, 0, 0, false⟩
  have htake : ((initFullCode n).take k).length ≤ (initFullCode n).length := by
    simp only [List.length_take]
    omega
  have hcode := ramPreprocess_instruction_bound input m
  rw [initFullCode_length] at htake
  have hz : ramStackSize m = 0 := by simp [ramStackSize, hs, hl]
  rw [hz, Nat.zero_add] at hstack
  unfold ramWorkspaceWords
  omega

theorem ramLoop_prefix_space {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hs : m.small = []) (hl : m.large = []) (k : ℕ) :
    ramWorkspaceWords (ramRun (ramInitialize input m).total
      ((ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).take k)
      (ramInitialize input m).m)
      ((initFullCode n).length +
        (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length)
      ≤ 133 * n + 44 := by
  have hinit := ramInitialize_stack_bound input m hs hl
  have hstack := ramRun_stack_bound (ramInitialize input m).total
    ((ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).take k)
    (ramInitialize input m).m
  have htake : ((ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).take k).length
      ≤ (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length := by
    simp only [List.length_take]
    omega
  have hloop := ramLoop_instruction_bound (ramInitialize input m).total n (ramInitialize input m).m
  have hcode := ramPreprocess_instruction_bound input m
  unfold ramWorkspaceWords
  omega

theorem ramFrontier {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hs : m.small = []) (hl : m.large = []) (hU : 0 < aliasWeightTotal (wordRead input)) :
    (∀ k, (ramDrawLaw (ramPreprocess input m) (positive_input_size input hU) hU).prob (some k) =
      ((wordRead input k : ℕ) : ℝ) / aliasWeightTotal (wordRead input)) ∧
    (∀ ps : List (Fin n × Fin (aliasWeightTotal (wordRead input))),
      (initFullCode n).length +
        (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length +
        (ramSamplesTrace ps (ramPreprocess input m)).length ≤ 26 * n + 8 * ps.length + 5) ∧
    (∀ k, ramWorkspaceWords
      (initRun input ((initFullCode n).take k) ⟨m, 0, 0, 0, false⟩).m
      ((initFullCode n).length +
        (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length) ≤ 133 * n + 44) ∧
    (∀ k, ramWorkspaceWords
      (ramRun (ramInitialize input m).total
        ((ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).take k)
        (ramInitialize input m).m)
      ((initFullCode n).length +
        (ramLoopCode (ramInitialize input m).total n (ramInitialize input m).m).length) ≤ 133 * n + 44) :=
  ⟨ramDrawLaw_preprocessed input m hU, ramPreprocess_and_samples_bound input m,
    ramInitialize_prefix_space input m hs hl, ramLoop_prefix_space input m hs hl⟩

end Qatlib.Concepts.SqEstimation.AliasPreprocess
