/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorRefined

/-!
# Support counting and wire routing for product formulas

This module shows that nonzero nested commutators of a finite-range family have successively
attached supports and bounds the number of such words using support size and site occupancy.
These estimates describe the support combinatorics underlying commutator scaling in
[ChildsEtAl2021Trotter].

It also constructs swap lists that gather supports into consecutive wire intervals. `frontier1`
and `frontier1_layers` route a disjoint-support layer with an explicit swap budget.

## Main statements

* `nested_ne_zero_imp_supportAttached`: nonzero nested commutators require attached supports.
* `nonzeroNestedWords_card_le`: a product bound on the number of nonzero nested words.
* `gatherSwapPairs_spec`: gathering a nonempty support with at most its size minus one swaps.
* `frontier1`: routing a disjoint-support layer into disjoint intervals.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSupportRouting

open Matrix
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs
open Qatlib
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

section Attached

variable {D Λ : ℕ}

/-- The matrix commutator vanishes exactly when the two matrices commute. -/
theorem pfComm_eq_zero_iff_commute {I : Type} [Fintype I] (X Y : Matrix I I ℂ) :
    pfComm X Y = 0 ↔ X * Y = Y * X := by
  constructor
  · intro h
    unfold pfComm at h
    exact sub_eq_zero.mp h
  · intro h
    unfold pfComm
    rw [h, sub_self]

/-- A matrix commuting with `X` and `Y` also commutes with their product. -/
private theorem comm_mul_right_of_comm {I : Type} [Fintype I] {Z X Y : Matrix I I ℂ}
    (hZX : Z * X = X * Z) (hZY : Z * Y = Y * Z) :
    Z * (X * Y) = (X * Y) * Z := by
  calc Z * (X * Y) = (Z * X) * Y := by rw [mul_assoc]
    _ = (X * Z) * Y := by rw [hZX]
    _ = X * (Z * Y) := by rw [← mul_assoc]
    _ = X * (Y * Z) := by rw [hZY]
    _ = (X * Y) * Z := by rw [← mul_assoc]

/-- A matrix commuting with every list entry and the initial accumulator commutes with the
iterated commutator fold. -/
private theorem commutes_fold_pfComm {I : Type} [Fintype I] (Z : Matrix I I ℂ) :
    ∀ (l : List (Matrix I I ℂ)) (acc : Matrix I I ℂ),
      (∀ Y ∈ l, Z * Y = Y * Z) → Z * acc = acc * Z →
      Z * (l.foldl (fun D Y => pfComm Y D) acc)
        = (l.foldl (fun D Y => pfComm Y D) acc) * Z := by
  intro l
  induction l with
  | nil => intro acc _ hz; exact hz
  | cons Y t ih =>
      intro acc hall hz
      have hzY : Z * Y = Y * Z := hall Y (List.mem_cons_self ..)
      have hzt : ∀ Y' ∈ t, Z * Y' = Y' * Z :=
        fun Y' hY' => hall Y' (List.mem_cons_of_mem _ hY')
      have hstep : Z * pfComm Y acc = pfComm Y acc * Z := by
        unfold pfComm
        rw [mul_sub, sub_mul, comm_mul_right_of_comm hzY hz,
          comm_mul_right_of_comm hz hzY, ← comm_mul_right_of_comm hzY hz,
          ← comm_mul_right_of_comm hz hzY]
      have hfold := ih (pfComm Y acc) hzt hstep
      simpa only [List.foldl_cons] using! hfold

/-- A matrix commuting with every entry of a list commutes with its nested commutator. -/
theorem pfNestedCommList_commute_of_forall {I : Type} [Fintype I]
    (Z : Matrix I I ℂ) (l : List (Matrix I I ℂ))
    (h : ∀ Y ∈ l, Z * Y = Y * Z) :
    Z * pfNestedCommList l = pfNestedCommList l * Z := by
  cases l with
  | nil => simp [pfNestedCommList]
  | cons X t =>
      have hX : Z * X = X * Z := h X (List.mem_cons_self ..)
      have ht : ∀ Y ∈ t, Z * Y = Y * Z := fun Y hY => h Y (List.mem_cons_of_mem _ hY)
      exact commutes_fold_pfComm Z t X ht hX

/-- An iterated commutator fold starting at zero remains zero. -/
private theorem foldl_pfComm_zero {I : Type} [Fintype I] :
    ∀ (l : List (Matrix I I ℂ)), l.foldl (fun D Y => pfComm Y D) 0 = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons Y t ih =>
      show t.foldl (fun D Y => pfComm Y D) (pfComm Y 0) = 0
      rw [show pfComm Y 0 = 0 by simp [pfComm]]
      exact ih

/-- The property that each successive term support meets the union of the initial region and the
preceding supports. -/
def attachedAfter (F : Fin Λ → LocalTerm D Λ) :
    Finset (Fin Λ) → List (Fin Λ) → Prop
  | _, [] => True
  | S, i :: t => (F i).support ∩ S ≠ ∅ ∧ attachedAfter F ((F i).support ∪ S) t

/-- The property that a word is empty or every support after the first attaches to the
accumulated preceding supports. -/
def IsSupportAttached (F : Fin Λ → LocalTerm D Λ) : List (Fin Λ) → Prop
  | [] => True
  | i :: t => attachedAfter F (F i).support t

/-- Accumulating supports from an initial union `A ∪ B` equals adjoining `A` to the accumulation
from `B`. -/
private theorem nestedSupport_union (F : Fin Λ → LocalTerm D Λ) :
    ∀ (w : List (Fin Λ)) (A B : Finset (Fin Λ)),
      w.foldl (fun acc i => acc ∪ (F i).support) (A ∪ B)
        = A ∪ w.foldl (fun acc i => acc ∪ (F i).support) B := by
  intro w
  induction w with
  | nil => intro A B; rfl
  | cons i t ih =>
      intro A B
      simp only [List.foldl_cons]
      rw [Finset.union_assoc, ih A (B ∪ (F i).support)]

/-- The accumulated support of `i :: t` is the union of the support of `i` with the accumulated
support of `t`. -/
theorem nestedSupport_cons (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) (t : List (Fin Λ)) :
    nestedSupport F ∅ (i :: t) = (F i).support ∪ nestedSupport F ∅ t := by
  show (i :: t).foldl (fun acc k => acc ∪ (F k).support) ∅
    = (F i).support ∪ t.foldl (fun acc k => acc ∪ (F k).support) ∅
  rw [List.foldl_cons,
    show (∅ : Finset (Fin Λ)) ∪ (F i).support = (F i).support ∪ ∅ from
      Finset.union_comm ∅ (F i).support,
    nestedSupport_union F t (F i).support ∅]

/-- The support of any label occurring in a word is contained in the word's accumulated support. -/
theorem support_subset_nestedSupport (F : Fin Λ → LocalTerm D Λ) :
    ∀ (u : List (Fin Λ)) (k : Fin Λ), k ∈ u →
      (F k).support ⊆ nestedSupport F ∅ u := by
  intro u
  induction u with
  | nil => intro k hk; simp at hk
  | cons i t ih =>
      intro k hk
      rw [nestedSupport_cons]
      rcases List.mem_cons.mp hk with hk' | hk'
      · rw [← hk']; exact fun a ha => Finset.mem_union.mpr (Or.inl ha)
      · exact (ih k hk').trans (fun a ha => Finset.mem_union.mpr (Or.inr ha))

/-- Failure of successive attachment gives a decomposition with a term disjoint from the initial
region and all preceding supports. -/
theorem exists_detached_of_not_attachedAfter (F : Fin Λ → LocalTerm D Λ) :
    ∀ (t : List (Fin Λ)) (S : Finset (Fin Λ)),
      ¬ attachedAfter F S t →
      ∃ (u : List (Fin Λ)) (j : Fin Λ) (v : List (Fin Λ)),
        t = u ++ j :: v ∧
        (F j).support ∩ (S ∪ nestedSupport F ∅ u) = ∅ := by
  intro t
  induction t with
  | nil => intro S h; exact absurd True.intro h
  | cons i t' ih =>
      intro S h
      by_cases hstep : (F i).support ∩ S ≠ ∅
      · have hrest : ¬ attachedAfter F ((F i).support ∪ S) t' := by
          intro hc; exact h ⟨hstep, hc⟩
        obtain ⟨u, j, v, hsplit, hj⟩ := ih ((F i).support ∪ S) hrest
        refine ⟨i :: u, j, v, by rw [hsplit, List.cons_append], ?_⟩
        rw [nestedSupport_cons]
        have hac : ((F i).support ∪ S) ∪ nestedSupport F ∅ u
            = S ∪ ((F i).support ∪ nestedSupport F ∅ u) := by
          simp only [Finset.union_assoc, Finset.union_comm]
        rw [hac] at hj
        exact hj
      · refine ⟨[], i, t', rfl, ?_⟩
        have hnil : nestedSupport F ∅ [] = ∅ := rfl
        rw [hnil, Finset.union_empty]
        exact of_not_not hstep

/-- For a family commuting on disjoint supports, every word with nonzero nested commutator has
successively attached supports. -/
theorem nested_ne_zero_imp_supportAttached (F : Fin Λ → LocalTerm D Λ)
    (hF : IsFiniteRangeFamily F) (w : List (Fin Λ))
    (hnz : pfNestedCommList (w.map (fun i => (F i).op)) ≠ 0) :
    IsSupportAttached F w := by
  cases w with
  | nil => exact True.intro
  | cons x t =>
      show attachedAfter F (F x).support t
      by_contra hatt
      obtain ⟨u, j, v, hsplit, hj⟩ :=
        exists_detached_of_not_attachedAfter F t (F x).support hatt
      apply hnz
      have hword : (x :: t).map (fun i => (F i).op)
          = (F x).op :: (u.map (fun i => (F i).op)
              ++ (F j).op :: v.map (fun i => (F i).op)) := by
        rw [hsplit]
        simp [List.map_cons, List.map_append]
      have hmeet : ∀ k ∈ x :: u, Disjoint (F j).support (F k).support := by
        intro k hk
        have hsub : (F k).support ⊆ (F x).support ∪ nestedSupport F ∅ u := by
          rcases List.mem_cons.mp hk with hk' | hk'
          · rw [hk']; exact fun a ha => Finset.mem_union.mpr (Or.inl ha)
          · exact (support_subset_nestedSupport F u k hk').trans
              (fun a ha => Finset.mem_union.mpr (Or.inr ha))
        have hdisj : Disjoint (F j).support ((F x).support ∪ nestedSupport F ∅ u) :=
          Finset.disjoint_iff_inter_eq_empty.mpr hj
        exact Finset.disjoint_of_subset_right hsub hdisj
      have hcomm : ∀ Y ∈ (F x).op :: u.map (fun i => (F i).op),
          (F j).op * Y = Y * (F j).op := by
        intro Y hY
        rcases List.mem_cons.mp hY with hY' | hY'
        · rw [hY']
          exact (pfComm_eq_zero_iff_commute (F j).op (F x).op).mp
            (hF j x (hmeet x (List.mem_cons_self ..)))
        · obtain ⟨k', hk'u, hk'⟩ := List.mem_map.mp hY'
          rw [← hk']
          exact (pfComm_eq_zero_iff_commute (F j).op (F k').op).mp
            (hF j k' (hmeet k' (List.mem_cons_of_mem _ hk'u)))
      have hDcomm : (F j).op * (u.map (fun i => (F i).op)).foldl
            (fun D Y => pfComm Y D) (F x).op
          = (u.map (fun i => (F i).op)).foldl (fun D Y => pfComm Y D) (F x).op
              * (F j).op :=
        commutes_fold_pfComm (F j).op (u.map (fun i => (F i).op)) (F x).op
          (fun Y hY => hcomm Y (List.mem_cons_of_mem _ hY))
          (hcomm ((F x).op) (List.mem_cons_self ..))
      have hzero : pfComm (F j).op
          ((u.map (fun i => (F i).op)).foldl (fun D Y => pfComm Y D) (F x).op) = 0 :=
        (pfComm_eq_zero_iff_commute _ _).mpr hDcomm
      rw [hword]
      simp only [pfNestedCommList, List.foldl_append, List.foldl_cons]
      rw [hzero]
      exact foldl_pfComm_zero _

/-- The finite set of term labels whose supports intersect `S`. -/
def meetingLabels (F : Fin Λ → LocalTerm D Λ) (S : Finset (Fin Λ)) :
    Finset (Fin Λ) :=
  Finset.univ.filter (fun i => (F i).support ∩ S ≠ ∅)

/-- If each site belongs to at most `occ` supports, at most `occ * S.card` labels meet `S`. -/
theorem meetingLabels_card_le (F : Fin Λ → LocalTerm D Λ) (occ : ℕ)
    (hocc : ∀ s : Fin Λ, (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ)
    (S : Finset (Fin Λ)) :
    (meetingLabels F S).card ≤ occ * S.card := by
  classical
  have hcover : meetingLabels F S ⊆ S.biUnion (fun s : Fin Λ =>
      Finset.univ.filter (fun i => s ∈ (F i).support)) := by
    intro i hi
    rw [meetingLabels, Finset.mem_filter] at hi
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hi.2
    rcases Finset.mem_inter.mp hs with ⟨hsi, hss⟩
    refine Finset.mem_biUnion.mpr ⟨s, hss, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hsi⟩
  calc (meetingLabels F S).card ≤ (S.biUnion (fun s : Fin Λ =>
        Finset.univ.filter (fun i => s ∈ (F i).support))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ s ∈ S, (Finset.univ.filter (fun i => s ∈ (F i).support)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ s ∈ S, occ := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact hocc s
    _ = S.card * occ := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ = occ * S.card := Nat.mul_comm _ _

/-- Adjoining a set of size at most `d` that meets `S` increases cardinality by at most `d - 1`. -/
theorem card_union_le_of_meets {d : ℕ} {S T : Finset (Fin Λ)}
    (hcard : T.card ≤ d) (hne : S ∩ T ≠ ∅) :
    (S ∪ T).card ≤ S.card + d - 1 := by
  have hle : (S ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
  have heq : (S ∪ T).card + (S ∩ T).card = S.card + T.card :=
    Finset.card_union_add_card_inter S T
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hpos : 1 ≤ (S ∩ T).card := by
    have hne0 : (S ∩ T).card ≠ 0 := by
      intro h0
      have hempty : S ∩ T = ∅ := Finset.card_eq_zero.mp h0
      rw [hempty] at he
      simp at he
    omega
  omega

/-- Successively adjoining supports of size at most `d` to `S` increases its size by at most `(d
- 1)` times the word length. -/
theorem attachedAfter_union_growth (F : Fin Λ → LocalTerm D Λ) (d : ℕ)
    (hsupp : ∀ i, (F i).support.card ≤ d) :
    ∀ (t : List (Fin Λ)) (S : Finset (Fin Λ)), attachedAfter F S t →
      (S ∪ nestedSupport F ∅ t).card ≤ S.card + (d - 1) * t.length := by
  intro t
  induction t with
  | nil => intro S h; simp [nestedSupport]
  | cons i t' ih =>
      intro S h
      obtain ⟨hne, hchain⟩ := h
      have hstep0 : (S ∪ (F i).support).card ≤ S.card + d - 1 :=
        card_union_le_of_meets (hsupp i) (by rw [Finset.inter_comm]; exact hne)
      have hstep : ((F i).support ∪ S).card ≤ S.card + d - 1 := by
        rwa [Finset.union_comm S (F i).support] at hstep0
      have hrec := ih ((F i).support ∪ S) hchain
      have hset : S ∪ nestedSupport F ∅ (i :: t')
          = ((F i).support ∪ S) ∪ nestedSupport F ∅ t' := by
        rw [nestedSupport_cons]
        simp only [Finset.union_assoc, Finset.union_comm]
      rw [hset]
      have hring : (d - 1) * (i :: t').length = (d - 1) * t'.length + (d - 1) := by
        simp only [List.length_cons]
        ring
      omega

/-- An attached word of supports of size at most `d` has union cardinality at most `1 + (d - 1)
* w.length`. -/
theorem attached_union_card_le (F : Fin Λ → LocalTerm D Λ) (d : ℕ)
    (hsupp : ∀ i, (F i).support.card ≤ d) {w : List (Fin Λ)}
    (hw : IsSupportAttached F w) :
    (nestedSupport F ∅ w).card ≤ 1 + (d - 1) * w.length := by
  match w with
  | [] => simp [nestedSupport]
  | x :: t =>
      have hrec := attachedAfter_union_growth F d hsupp t (F x).support hw
      have hcardx : (F x).support.card ≤ d := hsupp x
      have hset : nestedSupport F ∅ (x :: t) = (F x).support ∪ nestedSupport F ∅ t :=
        nestedSupport_cons F x t
      rw [hset]
      have hring : (d - 1) * (x :: t).length = (d - 1) * t.length + (d - 1) := by
        simp only [List.length_cons]
        ring
      have hxle : (F x).support.card ≤ 1 + (d - 1) := by omega
      omega

/-- Every nonempty list can be written as a prefix followed by a singleton. -/
private theorem exists_concat {α : Type} : ∀ (l : List α), l ≠ [] →
    ∃ (u : List α) (a : α), l = u ++ [a]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: t, _ => by
      obtain ⟨u, c, h⟩ := exists_concat (b :: t) (List.cons_ne_nil b t)
      exact ⟨a :: u, c, by rw [h, List.cons_append]⟩

/-- The finite set of all words of a given length over `Fin Λ`, constructed by appending one
label at each step. -/
def allWordsOfLength (Λ : ℕ) : ℕ → Finset (List (Fin Λ))
  | 0 => {[]}
  | k + 1 => (allWordsOfLength Λ k).biUnion
      (fun u => Finset.univ.image (fun i => u ++ [i]))

/-- Membership in `allWordsOfLength Λ k` is equivalent to having length `k`. -/
theorem mem_allWordsOfLength_iff {Λ : ℕ} :
    ∀ (k : ℕ) (w : List (Fin Λ)), w ∈ allWordsOfLength Λ k ↔ w.length = k := by
  intro k
  induction k with
  | zero =>
      intro w
      simp [allWordsOfLength]
  | succ k ih =>
      intro w
      constructor
      · intro h
        rw [allWordsOfLength, Finset.mem_biUnion] at h
        obtain ⟨u, hu, hi⟩ := h
        rw [Finset.mem_image] at hi
        obtain ⟨i', _, hi'⟩ := hi
        rw [← hi']
        have hulen : u.length = k := (ih u).mp hu
        simp only [List.length_append, List.length_singleton]
        omega
      · intro h
        obtain ⟨u, i, hw⟩ := exists_concat (α := Fin Λ) w (by
          intro hnil
          rw [hnil] at h
          simp at h)
        have hlen : (u ++ [i]).length = k + 1 := by rw [← hw]; exact h
        rw [allWordsOfLength, Finset.mem_biUnion]
        refine ⟨u, ?_, ?_⟩
        · rw [ih]
          have hsplit : (u ++ [i]).length = u.length + 1 := by
            simp only [List.length_append, List.length_singleton]
          omega
        · rw [Finset.mem_image]
          exact ⟨i, Finset.mem_univ i, hw.symm⟩

/-- Successive attachment of a concatenated word implies successive attachment of its initial
part. -/
theorem attachedAfter_append_init (F : Fin Λ → LocalTerm D Λ) :
    ∀ (t₁ t₂ : List (Fin Λ)) (S : Finset (Fin Λ)),
      attachedAfter F S (t₁ ++ t₂) → attachedAfter F S t₁ := by
  intro t₁
  induction t₁ with
  | nil => intro t₂ S h; exact True.intro
  | cons i t₁' ih =>
      intro t₂ S h
      rw [List.cons_append] at h
      exact ⟨h.1, ih t₂ ((F i).support ∪ S) h.2⟩

/-- The last support of an attached extension meets the union of the initial region and the
preceding word supports. -/
theorem attachedAfter_append_last (F : Fin Λ → LocalTerm D Λ) :
    ∀ (t₁ : List (Fin Λ)) (i : Fin Λ) (S : Finset (Fin Λ)),
      attachedAfter F S (t₁ ++ [i]) →
        (F i).support ∩ (S ∪ nestedSupport F ∅ t₁) ≠ ∅ := by
  intro t₁
  induction t₁ with
  | nil =>
      intro i S h
      have h1 : (F i).support ∩ S ≠ ∅ := h.1
      have hnil : nestedSupport F ∅ ([] : List (Fin Λ)) = ∅ := rfl
      rwa [hnil, Finset.union_empty]
  | cons j t₁' ih =>
      intro i S h
      have hrec := ih i ((F j).support ∪ S) h.2
      have hset : ((F j).support ∪ S) ∪ nestedSupport F ∅ t₁'
          = S ∪ nestedSupport F ∅ (j :: t₁') := by
        rw [nestedSupport_cons]
        simp only [Finset.union_assoc, Finset.union_comm]
      rwa [hset] at hrec

/-- Removing the final label from an attached word preserves attachment. -/
theorem isSupportAttached_append_prefix (F : Fin Λ → LocalTerm D Λ) :
    ∀ (u : List (Fin Λ)) (i : Fin Λ),
      IsSupportAttached F (u ++ [i]) → IsSupportAttached F u := by
  intro u i h
  match u with
  | [] => exact True.intro
  | x :: u' =>
      show attachedAfter F (F x).support u'
      exact attachedAfter_append_init F u' [i] (F x).support h

/-- For a nonempty prefix, attachment after appending a label forces its support to meet the
prefix support union. -/
theorem isSupportAttached_append_meets (F : Fin Λ → LocalTerm D Λ) :
    ∀ (u : List (Fin Λ)) (i : Fin Λ), u ≠ [] →
      IsSupportAttached F (u ++ [i]) →
        (F i).support ∩ nestedSupport F ∅ u ≠ ∅ := by
  intro u i hne h
  match u with
  | [] => exact absurd rfl hne
  | x :: u' =>
      rw [nestedSupport_cons]
      exact attachedAfter_append_last F u' i (F x).support h

/-- The finite set of support-attached label words of length `k`. -/
def attachedWordsOfLength (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    Finset (List (Fin Λ)) :=
  (allWordsOfLength Λ k).filter (fun w => IsSupportAttached F w)

/-- The finite set of length-`k` label words whose associated nested commutators are nonzero. -/
def nonzeroNestedWords (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    Finset (List (Fin Λ)) :=
  (allWordsOfLength Λ k).filter
    (fun w => pfNestedCommList (w.map (fun i => (F i).op)) ≠ 0)

/-- For positive `k`, the number of attached words is at most `Λ` times the product of the
occupancy and accumulated-support bounds over the remaining `k - 1` positions. -/
theorem attachedWords_card_le (F : Fin Λ → LocalTerm D Λ) (d occ : ℕ)
    (hsupp : ∀ i, (F i).support.card ≤ d)
    (hocc : ∀ s : Fin Λ, (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ) :
    ∀ k, 1 ≤ k → (attachedWordsOfLength F k).card ≤
      Λ * ∏ j ∈ Finset.range (k - 1), occ * (1 + (d - 1) * (j + 1)) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0

        have hsub : attachedWordsOfLength F 1 ⊆
            Finset.univ.image (fun i : Fin Λ => [i]) := by
          intro w hw
          have hmem : w ∈ allWordsOfLength Λ 1 := Finset.filter_subset _ _ hw
          rw [allWordsOfLength, Finset.mem_biUnion] at hmem
          obtain ⟨u, hu, hi⟩ := hmem
          rw [Finset.mem_image] at hi
          obtain ⟨i', _, hi'⟩ := hi
          have hu0 : u = [] := by
            simpa [allWordsOfLength] using! hu
          rw [Finset.mem_image]
          refine ⟨i', Finset.mem_univ i', ?_⟩
          rw [← hi', hu0]
          simp
        have himg : (Finset.univ.image (fun i : Fin Λ => [i])).card = Λ := by
          rw [Finset.card_image_of_injOn (by
            intro a _ b _ h
            simpa using! h), Finset.card_univ, Fintype.card_fin]
        have hle := Finset.card_le_card hsub
        rw [himg] at hle
        have hbound : Λ * ∏ j ∈ Finset.range (1 - 1), occ * (1 + (d - 1) * (j + 1))
            = Λ := by simp
        rw [hbound]
        exact hle
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩

        have ih1 := ih (by omega)
        have hsub : attachedWordsOfLength F (m + 2) ⊆
            (attachedWordsOfLength F (m + 1)).biUnion
              (fun u => (meetingLabels F (nestedSupport F ∅ u)).image
                (fun i => u ++ [i])) := by
          intro w hw
          have hmem : w ∈ allWordsOfLength Λ (m + 2) := Finset.filter_subset _ _ hw
          have hatt0 : IsSupportAttached F w := (Finset.mem_filter.mp hw).2
          have hlen : w.length = m + 2 := (mem_allWordsOfLength_iff _ _).mp hmem
          obtain ⟨u, i, hsplit⟩ := exists_concat (α := Fin Λ) w (by
            intro hnil
            rw [hnil] at hlen
            simp at hlen)
          rw [hsplit] at hatt0
          have hatt := hatt0
          have hulen : (u ++ [i]).length = m + 2 := by rw [← hsplit]; exact hlen
          have hune : u ≠ [] := by
            intro hnil
            rw [hnil] at hulen
            simp at hulen
          rw [Finset.mem_biUnion]
          refine ⟨u, ?_, ?_⟩
          · rw [attachedWordsOfLength, Finset.mem_filter]
            refine ⟨?_, isSupportAttached_append_prefix F u i hatt⟩
            rw [mem_allWordsOfLength_iff]
            have hsplit2 : (u ++ [i]).length = u.length + 1 := by
              simp only [List.length_append, List.length_singleton]
            omega
          · rw [Finset.mem_image]
            refine ⟨i, ?_, hsplit.symm⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
              isSupportAttached_append_meets F u i hune hatt⟩
        have hbUnion : ((attachedWordsOfLength F (m + 1)).biUnion
            (fun u => (meetingLabels F (nestedSupport F ∅ u)).image
              (fun i => u ++ [i]))).card
            ≤ ∑ u ∈ attachedWordsOfLength F (m + 1),
                ((meetingLabels F (nestedSupport F ∅ u)).image
                  (fun i => u ++ [i])).card :=
          Finset.card_biUnion_le
        calc (attachedWordsOfLength F (m + 2)).card
            ≤ ∑ u ∈ attachedWordsOfLength F (m + 1),
                ((meetingLabels F (nestedSupport F ∅ u)).image (fun i => u ++ [i])).card :=
                Finset.card_le_card hsub |>.trans hbUnion
          _ ≤ ∑ u ∈ attachedWordsOfLength F (m + 1),
                occ * (1 + (d - 1) * (m + 1)) := by
              refine Finset.sum_le_sum fun u hu => ?_
              have hmeet := meetingLabels_card_le F occ hocc (nestedSupport F ∅ u)
              have hsize := attached_union_card_le F d hsupp
                (Finset.mem_filter.mp hu).2
              have huleneq : u.length = m + 1 := by
                have huw := (mem_allWordsOfLength_iff (m + 1) u).mp
                  (Finset.filter_subset _ _ hu)
                omega
              have himg : ((meetingLabels F (nestedSupport F ∅ u)).image
                  (fun i => u ++ [i])).card
                  = (meetingLabels F (nestedSupport F ∅ u)).card := by
                exact Finset.card_image_of_injOn (fun a _ b _ h => by simpa using! h)
              rw [himg]
              have hgrow : (d - 1) * u.length ≤ (d - 1) * (m + 1) :=
                Nat.mul_le_mul_left _ (by omega)
              have hle : (nestedSupport F ∅ u).card ≤ 1 + (d - 1) * (m + 1) := by omega
              exact Nat.le_trans hmeet (Nat.mul_le_mul_left occ hle)
          _ = (attachedWordsOfLength F (m + 1)).card * (occ * (1 + (d - 1) * (m + 1))) := by
              rw [Finset.sum_const, Nat.nsmul_eq_mul]
          _ ≤ Λ * ∏ j ∈ Finset.range (m + 1), occ * (1 + (d - 1) * (j + 1)) := by
              have hprod : ∏ j ∈ Finset.range (m + 1), occ * (1 + (d - 1) * (j + 1))
                  = (∏ j ∈ Finset.range m, occ * (1 + (d - 1) * (j + 1)))
                    * (occ * (1 + (d - 1) * (m + 1))) := by
                rw [Finset.prod_range_succ]
              rw [hprod]
              calc (attachedWordsOfLength F (m + 1)).card * (occ * (1 + (d - 1) * (m + 1)))
                  ≤ (Λ * ∏ j ∈ Finset.range m, occ * (1 + (d - 1) * (j + 1)))
                      * (occ * (1 + (d - 1) * (m + 1))) :=
                    Nat.mul_le_mul_right _ ih1
                _ = Λ * ((∏ j ∈ Finset.range m, occ * (1 + (d - 1) * (j + 1)))
                      * (occ * (1 + (d - 1) * (m + 1)))) := by ring
          _ = Λ * ∏ j ∈ Finset.range ((m + 2) - 1), occ * (1 + (d - 1) * (j + 1)) := by
              rw [show (m + 2) - 1 = m + 1 by omega]

/-- For a finite-range family and positive word length, the number of nonzero nested commutators
satisfies the same support-size and occupancy product bound as attached words. -/
theorem nonzeroNestedWords_card_le (F : Fin Λ → LocalTerm D Λ)
    (hF : IsFiniteRangeFamily F) (d occ : ℕ)
    (hsupp : ∀ i, (F i).support.card ≤ d)
    (hocc : ∀ s : Fin Λ, (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ)
    (k : ℕ) (hk : 1 ≤ k) :
    (nonzeroNestedWords F k).card ≤
      Λ * ∏ j ∈ Finset.range (k - 1), occ * (1 + (d - 1) * (j + 1)) := by
  have hsub : nonzeroNestedWords F k ⊆ attachedWordsOfLength F k := by
    intro w hw
    rw [nonzeroNestedWords, Finset.mem_filter] at hw
    rw [attachedWordsOfLength, Finset.mem_filter]
    exact ⟨hw.1, nested_ne_zero_imp_supportAttached F hF w hw.2⟩
  exact Nat.le_trans (Finset.card_le_card hsub)
    (attachedWords_card_le F d occ hsupp hocc k hk)

section Routing

variable {D Λ : ℕ}

/-- The wires whose contents under the assignment `ρ` lie in the site set `S`. -/
def supportWires (ρ : Fin Λ → Fin Λ) (S : Finset (Fin Λ)) : Finset (Fin Λ) :=
  Finset.univ.filter (fun w => ρ w ∈ S)

/-- The wires in `Fin Λ` with indices in the half-open interval from `a` to `a + s`. -/
def wireInterval (Λ a s : ℕ) : Finset (Fin Λ) :=
  Finset.univ.filter (fun w => a ≤ w.val ∧ w.val < a + s)

/-- A wire belongs to `wireInterval Λ a s` exactly when its index is at least `a` and less than
`a + s`. -/
theorem mem_wireInterval_iff {Λ a s : ℕ} {w : Fin Λ} :
    w ∈ wireInterval Λ a s ↔ a ≤ w.val ∧ w.val < a + s := by
  simp [wireInterval]

/-- The wire assignment obtained by exchanging the contents of `w₁` and `w₂`. -/
def wireSwapContents (w₁ w₂ : Fin Λ) (ρ : Fin Λ → Fin Λ) : Fin Λ → Fin Λ :=
  fun w => if w = w₁ then ρ w₂ else if w = w₂ then ρ w₁ else ρ w

/-- The function exchanging wires `w₁` and `w₂` and fixing all other wires. -/
def wireSwapFn (w₁ w₂ : Fin Λ) : Fin Λ → Fin Λ :=
  fun w => if w = w₁ then w₂ else if w = w₂ then w₁ else w

/-- The wire permutation represented by a list of swaps, with the head transposition composed on
the left. -/
def swapWordFn : List (Fin Λ × Fin Λ) → Fin Λ → Fin Λ
  | [] => id
  | p :: rest => wireSwapFn p.1 p.2 ∘ swapWordFn rest

/-- The assignment obtained by applying a list of content swaps in list order. -/
def swapWordApply : List (Fin Λ × Fin Λ) → (Fin Λ → Fin Λ) → Fin Λ → Fin Λ
  | [], ρ => ρ
  | p :: rest, ρ => swapWordApply rest (wireSwapContents p.1 p.2 ρ)

/-- Swapping wire contents equals precomposing the assignment with the corresponding wire
transposition. -/
private theorem wireSwapContents_apply (w₁ w₂ : Fin Λ) (ρ : Fin Λ → Fin Λ)
    (w : Fin Λ) : wireSwapContents w₁ w₂ ρ w = ρ (wireSwapFn w₁ w₂ w) := by
  unfold wireSwapContents wireSwapFn
  by_cases h1 : w = w₁
  · rw [if_pos h1, if_pos h1]
  · by_cases h2 : w = w₂
    · rw [if_neg h1, if_pos h2, if_pos h2, if_neg h1]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

/-- Applying a swap word to an assignment evaluates as the original assignment composed with
`swapWordFn`. -/
theorem swapWordApply_apply (W : List (Fin Λ × Fin Λ)) (ρ : Fin Λ → Fin Λ)
    (w : Fin Λ) : swapWordApply W ρ w = ρ (swapWordFn W w) := by
  induction W generalizing ρ w with
  | nil => rfl
  | cons p rest ih =>
      rw [swapWordApply, ih (wireSwapContents p.1 p.2 ρ) w,
        wireSwapContents_apply p.1 p.2 ρ (swapWordFn rest w), swapWordFn,
        Function.comp_apply]

/-- The permutation of a concatenated swap word is the composition of the permutations of its
two parts. -/
theorem swapWordFn_append (W₁ W₂ : List (Fin Λ × Fin Λ)) :
    swapWordFn (W₁ ++ W₂) = swapWordFn W₁ ∘ swapWordFn W₂ := by
  induction W₁ with
  | nil => rfl
  | cons p t ih => rw [List.cons_append, swapWordFn, swapWordFn, ih]; rfl

/-- Exchanging the same pair of wires twice fixes every wire. -/
theorem wireSwapFn_involution (w₁ w₂ : Fin Λ) (w : Fin Λ) :
    wireSwapFn w₁ w₂ (wireSwapFn w₁ w₂ w) = w := by
  unfold wireSwapFn
  by_cases h1 : w = w₁
  · rw [if_pos h1]
    by_cases h2 : w₂ = w₁
    · rw [if_pos h2, h2, h1]
    · rw [if_neg h2, if_pos rfl, h1]
  · by_cases h2 : w = w₂
    · rw [if_neg h1, if_pos h2, if_pos rfl, h2]
    · rw [if_neg h1, if_neg h2]
      by_cases h3 : w = w₂
      · exact absurd h3 h2
      · rw [if_neg h1, if_neg h3]

/-- Every wire transposition is bijective. -/
theorem wireSwapFn_bijective (w₁ w₂ : Fin Λ) :
    Function.Bijective (wireSwapFn w₁ w₂) := by
  constructor
  · intro a b hab
    have ha := wireSwapFn_involution w₁ w₂ a
    have hb := wireSwapFn_involution w₁ w₂ b
    rw [← ha, ← hb, hab]
  · intro b
    exact ⟨wireSwapFn w₁ w₂ b, wireSwapFn_involution w₁ w₂ b⟩

/-- The wire function of every swap word is bijective. -/
theorem swapWordFn_bijective (W : List (Fin Λ × Fin Λ)) :
    Function.Bijective (swapWordFn W) := by
  induction W with
  | nil => exact Function.bijective_id
  | cons p t ih => rw [swapWordFn]; exact (wireSwapFn_bijective p.1 p.2).comp ih

/-- A wire absent from both endpoints of every swap is fixed by the swap word. -/
theorem swapWordFn_eq_of_untouched : ∀ (W : List (Fin Λ × Fin Λ)) (w : Fin Λ),
    (∀ p ∈ W, p.1 ≠ w ∧ p.2 ≠ w) → swapWordFn W w = w := by
  intro W
  induction W with
  | nil => intro w _; rfl
  | cons p t ih =>
      intro w h
      have hp := h p (List.mem_cons_self ..)
      rw [swapWordFn, Function.comp_apply,
        ih w (fun q hq => h q (List.mem_cons_of_mem _ hq)), wireSwapFn,
        if_neg (Fin.ne_of_val_ne (by
          have := h p (List.mem_cons_self ..); omega)),
        if_neg (Fin.ne_of_val_ne (by
          have := h p (List.mem_cons_self ..); omega))]

/-- A swap word using only endpoints at or above `M` fixes all wires below `M`. -/
theorem swapWordFn_low_fix : ∀ (W : List (Fin Λ × Fin Λ)) (M : ℕ),
    (∀ p ∈ W, M ≤ p.1.val ∧ M ≤ p.2.val) →
    ∀ w : Fin Λ, w.val < M → swapWordFn W w = w := by
  intro W
  induction W with
  | nil => intro M _ w _; rfl
  | cons p t ih =>
      intro M h w hw
      have hp := h p (List.mem_cons_self ..)
      rw [swapWordFn, Function.comp_apply,
        ih M (fun q hq => h q (List.mem_cons_of_mem _ hq)) w hw, wireSwapFn,
        if_neg (Fin.ne_of_val_ne (by omega)),
        if_neg (Fin.ne_of_val_ne (by omega))]

/-- A swap word using only endpoints at or above `M` maps every wire at or above `M` to that
region. -/
theorem swapWordFn_high_preserve : ∀ (W : List (Fin Λ × Fin Λ)) (M : ℕ),
    (∀ p ∈ W, M ≤ p.1.val ∧ M ≤ p.2.val) →
    ∀ w : Fin Λ, M ≤ w.val → M ≤ (swapWordFn W w).val := by
  intro W
  induction W with
  | nil => intro M _ w hw; simpa using! hw
  | cons p t ih =>
      intro M h w hw
      have hp := h p (List.mem_cons_self ..)
      have hrest := ih M (fun q hq => h q (List.mem_cons_of_mem _ hq)) w hw
      rw [swapWordFn, Function.comp_apply]
      have hcase : wireSwapFn p.1 p.2 (swapWordFn t w)
          = swapWordFn t w ∨ wireSwapFn p.1 p.2 (swapWordFn t w) = p.1
            ∨ wireSwapFn p.1 p.2 (swapWordFn t w) = p.2 := by
        unfold wireSwapFn
        by_cases hu1 : swapWordFn t w = p.1
        · rw [if_pos hu1]; exact Or.inr (Or.inr rfl)
        · by_cases hu2 : swapWordFn t w = p.2
          · rw [if_neg hu1, if_pos hu2]; exact Or.inr (Or.inl rfl)
          · rw [if_neg hu1, if_neg hu2]; exact Or.inl rfl
      rcases hcase with hcase | hcase | hcase
      · rw [hcase]; exact hrest
      · rw [hcase]; exact hp.1
      · rw [hcase]; exact hp.2

/-- A bijective wire assignment preserves the cardinality of each support when expressed as
occupied wires. -/
theorem supportWires_card (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (S : Finset (Fin Λ)) : (supportWires ρ S).card = S.card := by
  classical
  have himg : Finset.image ρ (supportWires ρ S) = S := by
    apply Finset.ext
    intro s
    constructor
    · intro hs
      obtain ⟨w, hw, hws⟩ := Finset.mem_image.mp hs
      have := (Finset.mem_filter.mp hw).2
      rwa [hws] at this
    · intro hs
      obtain ⟨w, hw⟩ := hρ.2 s
      refine Finset.mem_image.mpr ⟨w, ?_, hw⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw.symm ▸ hs⟩
  calc (supportWires ρ S).card = (Finset.image ρ (supportWires ρ S)).card :=
        (Finset.card_image_of_injOn (fun a _ b _ hab => hρ.1 hab)).symm
    _ = S.card := by rw [himg]

/-- The embedding of `Fin s` into `Fin Λ` sending `j` to `a + j`, given that the interval fits. -/
private def intervalFin (Λ a s : ℕ) (_h : a + s ≤ Λ) (j : Fin s) : Fin Λ :=
  ⟨a + j.val, by have := j.isLt; omega⟩

/-- The index of the interval embedding of `j` is `a + j.val`. -/
private theorem intervalFin_val {Λ a s : ℕ} (h : a + s ≤ Λ) (j : Fin s) :
    (intervalFin Λ a s h j).val = a + j.val := rfl

/-- An interval starting at `a` with length `s` has cardinality `s` when `a + s ≤ Λ`. -/
theorem wireInterval_card (Λ a s : ℕ) (h : a + s ≤ Λ) :
    (wireInterval Λ a s).card = s := by
  classical
  have himg : (Finset.univ : Finset (Fin s)).image (intervalFin Λ a s h)
      = wireInterval Λ a s := by
    apply Finset.ext
    intro w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_wireInterval_iff]
    constructor
    · rintro ⟨j, hj⟩
      subst hj
      have hj' := j.isLt
      rw [intervalFin_val]
      constructor <;> omega
    · intro hmem
      obtain ⟨hm1, hm2⟩ := hmem
      refine ⟨⟨w.val - a, by omega⟩, ?_⟩
      apply Fin.ext
      show a + (w.val - a) = w.val
      omega
  rw [← himg,
    Finset.card_image_of_injOn (by
      intro x _ y _ hxy
      apply Fin.ext
      have hv := congrArg Fin.val hxy
      rw [intervalFin_val, intervalFin_val] at hv
      omega),
    Finset.card_univ, Fintype.card_fin]

/-- Two wire intervals are disjoint when the first ends at or before the start of the second. -/
theorem wireInterval_disjoint (Λ a₁ s₁ a₂ s₂ : ℕ) (h : a₁ + s₁ ≤ a₂) :
    Disjoint (wireInterval Λ a₁ s₁) (wireInterval Λ a₂ s₂) := by
  rw [Finset.disjoint_iff_ne]
  intro w hw1 w' hw2
  obtain ⟨hm1, hm2⟩ := mem_wireInterval_iff.mp hw1
  obtain ⟨hm3, hm4⟩ := mem_wireInterval_iff.mp hw2
  exact Fin.ne_of_val_ne (by omega)

/-- The least wire index carrying a site of `S`, with default value zero when no such wire
exists. -/
def minWire (ρ : Fin Λ → Fin Λ) (S : Finset (Fin Λ)) : ℕ :=
  if h : (supportWires ρ S).Nonempty then ((supportWires ρ S).min' h).val else 0

/-- Under a bijective assignment, a nonempty support occupies a nonempty set of wires. -/
theorem supportWires_nonempty (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (S : Finset (Fin Λ)) (hS : S.Nonempty) : (supportWires ρ S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨w, hw⟩ := hρ.2 s
  exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw.symm ▸ hs⟩⟩

/-- The least occupied wire index is at most the index of any occupied wire. -/
theorem minWire_le (ρ : Fin Λ → Fin Λ) (S : Finset (Fin Λ))
    (hne : (supportWires ρ S).Nonempty) {w : Fin Λ} (hw : w ∈ supportWires ρ S) :
    minWire ρ S ≤ w.val := by
  rw [minWire, dif_pos hne]
  exact Fin.le_def.mp ((supportWires ρ S).min'_le w hw)

/-- For a nonempty occupied-wire set, its least index is less than `Λ`. -/
theorem minWire_lt (ρ : Fin Λ → Fin Λ) (S : Finset (Fin Λ))
    (hne : (supportWires ρ S).Nonempty) : minWire ρ S < Λ := by
  rw [minWire, dif_pos hne]
  exact ((supportWires ρ S).min' hne).isLt

/-- The wire with index `minWire ρ S` belongs to the nonempty occupied-wire set. -/
theorem minWire_mem (ρ : Fin Λ → Fin Λ) (S : Finset (Fin Λ))
    (hne : (supportWires ρ S).Nonempty) :
    (⟨minWire ρ S, minWire_lt ρ S hne⟩ : Fin Λ) ∈ supportWires ρ S := by
  have h := Finset.min'_mem (supportWires ρ S) hne
  convert! h using 1
  simp only [minWire, dif_pos hne]

/-- For a bijective assignment and nonempty support, the interval starting at its least wire and
having its cardinality fits within `Fin Λ`. -/
theorem minWire_fit (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (S : Finset (Fin Λ)) (hS : S.Nonempty) : minWire ρ S + S.card ≤ Λ := by
  classical
  have hne := supportWires_nonempty ρ hρ S hS
  have hcardW : (supportWires ρ S).card = S.card := supportWires_card ρ hρ S
  have hlt : minWire ρ S < Λ := minWire_lt ρ S hne
  have hge : ∀ w ∈ supportWires ρ S, minWire ρ S ≤ w.val :=
    fun w hw => minWire_le ρ S hne hw
  have hTcard : ((supportWires ρ S).image
      (fun w => w.val - minWire ρ S)).card = S.card := by
    rw [Finset.card_image_of_injOn
      (by
        intro x hx y hy hxy
        have h1 := hge x hx
        have h2 := hge y hy
        have hxy' : x.val - minWire ρ S = y.val - minWire ρ S := hxy
        exact Fin.ext (by omega)),
      hcardW]
  have hsub : (supportWires ρ S).image (fun w => w.val - minWire ρ S)
      ⊆ Finset.range (Λ - minWire ρ S) := by
    intro j hj
    obtain ⟨w, hw, hjw⟩ := Finset.mem_image.mp hj
    rw [← hjw]
    simp only [Finset.mem_range]
    omega
  have hle := Finset.card_le_card hsub
  rw [hTcard, Finset.card_range] at hle
  omega

/-- The first component of an entry in a zipped list belongs to the left list. -/
private theorem mem_zip_left {α β : Type} : ∀ (l₁ : List α) (l₂ : List β)
    (p : α × β), p ∈ l₁.zip l₂ → p.1 ∈ l₁
  | [], _, _, hp => by simp at hp
  | _ :: _, [], _, hp => by simp at hp
  | a :: t₁, b :: t₂, p, hp => by
      rcases List.mem_cons.mp hp with hp' | hp'
      · exact hp' ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_zip_left t₁ t₂ p hp')

/-- The second component of an entry in a zipped list belongs to the right list. -/
private theorem mem_zip_right {α β : Type} : ∀ (l₁ : List α) (l₂ : List β)
    (p : α × β), p ∈ l₁.zip l₂ → p.2 ∈ l₂
  | [], _, _, hp => by simp at hp
  | _ :: _, [], _, hp => by simp at hp
  | a :: t₁, b :: t₂, p, hp => by
      rcases List.mem_cons.mp hp with hp' | hp'
      · exact hp' ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_zip_right t₁ t₂ p hp')

/-- Swapping two wire contents leaves the contents of every other wire unchanged. -/
private theorem wireSwapContents_of_ne (ρ : Fin Λ → Fin Λ) (h x w : Fin Λ)
    (w1 : w ≠ h) (w2 : w ≠ x) : wireSwapContents h x ρ w = ρ w := by
  rw [wireSwapContents, if_neg w1, if_neg w2]

/-- Swapping a wire outside the support with a wire inside it replaces the latter occupied wire
by the former. -/
private theorem supportWires_single_swap (S : Finset (Fin Λ)) (ρ : Fin Λ → Fin Λ)
    (h x : Fin Λ) (hρh : ρ h ∉ S) (hρx : ρ x ∈ S) :
    supportWires (wireSwapContents h x ρ) S
      = insert h ((supportWires ρ S).erase x) := by
  classical
  apply Finset.ext
  intro w
  simp only [supportWires, Finset.mem_filter, Finset.mem_univ, true_and, wireSwapContents,
    Finset.mem_insert, Finset.mem_erase]
  by_cases hw1 : w = h
  · rw [hw1, if_pos rfl]
    constructor
    · intro _; exact Or.inl rfl
    · intro _; exact hρx
  · by_cases hw2 : w = x
    · rw [hw2] at hw1 ⊢
      rw [if_neg hw1, if_pos rfl]
      constructor
      · intro hc
        exact absurd hc hρh
      · intro hc
        rcases hc with hc | hc
        · exact absurd hc hw1
        · exact absurd rfl hc.1
    · rw [if_neg hw1, if_neg hw2]
      constructor
      · intro hmem
        exact Or.inr ⟨hw2, hmem⟩
      · intro hc
        rcases hc with hc | hc
        · exact absurd hc hw1
        · exact hc.2

/-- Swapping paired distinct holes and occupied wires replaces the listed occupied wires by the
listed holes, under the stated equal-length and disjointness conditions. -/
theorem supportWires_swap_zip (S : Finset (Fin Λ)) :
    ∀ (hs xs : List (Fin Λ)) (ρ : Fin Λ → Fin Λ),
      hs.length = xs.length → hs.Nodup → xs.Nodup →
      (∀ h ∈ hs, ρ h ∉ S) → (∀ x ∈ xs, ρ x ∈ S) →
      (∀ h ∈ hs, ∀ x ∈ xs, h ≠ x) →
      supportWires (swapWordApply (hs.zip xs) ρ) S
        = ((supportWires ρ S \ xs.toFinset) ∪ hs.toFinset) := by
  intro hs
  induction hs with
  | nil =>
      intro xs ρ hlen _ _ _ _ _
      have : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst this
      simp [swapWordApply]
  | cons h t ih =>
      intro xs ρ hlen hndup1 hndup2 hout hin hcross
      cases xs with
      | nil => simp at hlen
      | cons x t' =>
          have hρh : ρ h ∉ S := hout h (List.mem_cons_self ..)
          have hρx : ρ x ∈ S := hin x (List.mem_cons_self ..)
          have hne : h ≠ x := by
            intro heq
            exact hρh (heq ▸ hρx)
          have hnt' : h ∉ t' := by
            intro hmem
            exact hcross h (List.mem_cons_self ..) h (List.mem_cons_of_mem _ hmem)
              rfl
          have hndt : t.Nodup := (List.nodup_cons.mp hndup1).2
          have hndt' : t'.Nodup := (List.nodup_cons.mp hndup2).2
          have hout' : ∀ h' ∈ t, wireSwapContents h x ρ h' ∉ S := by
            intro h' hh'
            have hc := hcross h' (List.mem_cons_of_mem _ hh') x (List.mem_cons_self ..)
            rw [wireSwapContents_of_ne ρ h x h'
              (fun heq => (List.nodup_cons.mp hndup1).1 (heq ▸ hh')) hc]
            exact hout h' (List.mem_cons_of_mem _ hh')
          have hin' : ∀ x' ∈ t', wireSwapContents h x ρ x' ∈ S := by
            intro x' hx'
            have hc := hcross h (List.mem_cons_self ..) x' (List.mem_cons_of_mem _ hx')
            have hxnx : x' ≠ x := by
              intro heq
              have := (List.nodup_cons.mp hndup2).1
              exact this (heq ▸ hx')
            rw [wireSwapContents_of_ne ρ h x x' (fun heq => hc heq.symm) hxnx]
            exact hin x' (List.mem_cons_of_mem _ hx')
          have hsingle := supportWires_single_swap S ρ h x hρh hρx
          have hlent : t.length = t'.length := by
            simp only [List.length_cons] at hlen
            omega
          have hrec := ih t' (wireSwapContents h x ρ) hlent hndt hndt'
            hout' hin'
            (fun h' hh' x' hx' => hcross h' (List.mem_cons_of_mem _ hh')
              x' (List.mem_cons_of_mem _ hx'))
          have hW : h ∉ supportWires ρ S := by
            intro hmem
            exact hρh (Finset.mem_filter.mp hmem).2
          have hInT' : ¬ (h ∈ t'.toFinset) := fun hc => hnt' (List.mem_toFinset.mp hc)
          rw [List.zip_cons_cons, swapWordApply, hrec, hsingle]
          apply Finset.ext
          intro w
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
            Finset.mem_erase, List.mem_toFinset, List.toFinset_cons]
          have key : w = h → ¬ (w ∈ t') := by
            intro hwh hmem
            exact hnt' (hwh ▸ hmem)
          tauto

/-- A wire occupies support `S` exactly when its assigned site lies in `S`. -/
theorem mem_supportWires_iff {ρ : Fin Λ → Fin Λ} {S : Finset (Fin Λ)} {w : Fin Λ} :
    w ∈ supportWires ρ S ↔ ρ w ∈ S := by
  rw [supportWires, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The list representation of a finite wire set has length equal to its cardinality. -/
private theorem finset_toList_length (s : Finset (Fin Λ)) : s.toList.length = s.card := by
  rw [Finset.toList, Multiset.length_toList]
  rfl

/-- Applying a concatenated swap word is equivalent to applying its first part and then its
second part. -/
theorem swapWordApply_append (W₁ W₂ : List (Fin Λ × Fin Λ)) (ρ : Fin Λ → Fin Λ) :
    swapWordApply (W₁ ++ W₂) ρ = swapWordApply W₂ (swapWordApply W₁ ρ) := by
  induction W₁ generalizing ρ with
  | nil => rfl
  | cons p t ih => rw [List.cons_append, swapWordApply, swapWordApply, ih]

/-- Applying any swap word preserves bijectivity of a wire assignment. -/
theorem swapWordApply_bijective (W : List (Fin Λ × Fin Λ)) (ρ : Fin Λ → Fin Λ)
    (hρ : Function.Bijective ρ) : Function.Bijective (swapWordApply W ρ) := by
  have hfun : swapWordApply W ρ = ρ ∘ swapWordFn W :=
    funext (fun w => swapWordApply_apply W ρ w)
  rw [hfun]
  exact hρ.comp (swapWordFn_bijective W)

/-- The swap list pairing holes in the target interval with occupied support wires outside that
interval. -/
def gatherSwapPairs (ρ : Fin Λ → Fin Λ) (S : Finset (Fin Λ)) : List (Fin Λ × Fin Λ) :=
  ((wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S).toList).zip
    ((supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).toList)

/-- For a nonempty support under a bijective assignment, the target interval has as many holes
as there are occupied wires outside it. -/
theorem gatherSwapPairs_holes_outside (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (S : Finset (Fin Λ)) (hS : S.Nonempty) :
    ((wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S).toList).length
      = ((supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).toList).length := by
  rw [finset_toList_length, finset_toList_length, Finset.card_sdiff, Finset.card_sdiff,
    supportWires_card ρ hρ S,
    wireInterval_card Λ (minWire ρ S) S.card (minWire_fit ρ hρ S hS),
    Finset.inter_comm]

/-- The least occupied wire belongs both to the support wires and to their target interval. -/
theorem anchor_mem_inter (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (S : Finset (Fin Λ)) (hS : S.Nonempty) :
    (⟨minWire ρ S, minWire_lt ρ S (supportWires_nonempty ρ hρ S hS)⟩ : Fin Λ)
      ∈ wireInterval Λ (minWire ρ S) S.card ∩ supportWires ρ S := by
  have hs : 1 ≤ S.card := Finset.one_le_card.mpr hS
  refine Finset.mem_inter.mpr ⟨?_, minWire_mem ρ S (supportWires_nonempty ρ hρ S hS)⟩
  rw [mem_wireInterval_iff]
  show minWire ρ S ≤ minWire ρ S ∧ minWire ρ S < minWire ρ S + S.card
  omega

/-- An occupied wire outside the target interval lies at or beyond the interval's upper
endpoint. -/
theorem outsideWire_ge (ρ : Fin Λ → Fin Λ) (S : Finset (Fin Λ))
    (hne : (supportWires ρ S).Nonempty) {w : Fin Λ} (hw : w ∈ supportWires ρ S)
    (hni : w ∉ wireInterval Λ (minWire ρ S) S.card) :
    minWire ρ S + S.card ≤ w.val := by
  have h1 := minWire_le ρ S hne hw
  rw [mem_wireInterval_iff] at hni
  omega

/-- Under distinctness, disjointness, and sufficient right-list length, each left endpoint of a
zipped swap word is mapped to some right endpoint. -/
theorem swapWordFn_zip_apply_left (hs : List (Fin Λ)) :
    ∀ (xs : List (Fin Λ)) (_hlen : hs.length ≤ xs.length),
      hs.Nodup → xs.Nodup → (∀ h ∈ hs, ∀ x ∈ xs, h ≠ x) →
      ∀ h ∈ hs, ∃ x ∈ xs, swapWordFn (hs.zip xs) h = x := by
  induction hs with
  | nil => intro xs _ _ _ _ h hh; exact absurd hh (by simp)
  | cons h₀ t ih =>
      intro xs hlen hndup1 hndup2 hcross h hh
      cases xs with
      | nil => simp at hlen
      | cons x₀ t' =>
          by_cases hh0 : h = h₀
          · rw [hh0]
            have hunt : swapWordFn (t.zip t') h₀ = h₀ := by
              refine swapWordFn_eq_of_untouched (t.zip t') h₀ ?_
              intro p hp
              refine ⟨?_, ?_⟩
              · intro he
                exact (List.nodup_cons.mp hndup1).1 (he ▸ (mem_zip_left t t' p hp))
              · exact (hcross h₀ (List.mem_cons_self ..) p.2
                  (List.mem_cons_of_mem _ (mem_zip_right t t' p hp))).symm
            rw [List.zip_cons_cons, swapWordFn, Function.comp_apply, hunt, wireSwapFn,
              if_pos rfl]
            exact ⟨x₀, List.mem_cons_self .., rfl⟩
          · have hht : h ∈ t := by
              rcases List.mem_cons.mp hh with he | he
              · exact absurd he hh0
              · exact he
            have hlen' : t.length ≤ t'.length := by
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨xk, hxk, hxik⟩ := ih t' hlen' (List.nodup_cons.mp hndup1).2
              (List.nodup_cons.mp hndup2).2
              (fun h' hh' x' hx' => hcross h' (List.mem_cons_of_mem _ hh')
                x' (List.mem_cons_of_mem _ hx'))
              h hht
            have e1 : xk ≠ h₀ :=
              (hcross h₀ (List.mem_cons_self ..) xk (List.mem_cons_of_mem _ hxk)).symm
            have e2 : xk ≠ x₀ := by
              intro he
              exact (List.nodup_cons.mp hndup2).1 (he ▸ hxk)
            rw [List.zip_cons_cons, swapWordFn, Function.comp_apply, hxik, wireSwapFn,
              if_neg e1, if_neg e2]
            exact ⟨xk, List.mem_cons_of_mem _ hxk, rfl⟩

/-- Under distinctness, disjointness, and sufficient left-list length, each right endpoint of a
zipped swap word is mapped to some left endpoint. -/
theorem swapWordFn_zip_apply_right (xs : List (Fin Λ)) :
    ∀ (hs : List (Fin Λ)) (_hlen : xs.length ≤ hs.length),
      hs.Nodup → xs.Nodup → (∀ h ∈ hs, ∀ x ∈ xs, h ≠ x) →
      ∀ x ∈ xs, ∃ h ∈ hs, swapWordFn (hs.zip xs) x = h := by
  induction xs with
  | nil => intro hs _ _ _ _ x hx; exact absurd hx (by simp)
  | cons x₀ t' ih =>
      intro hs hlen hndup1 hndup2 hcross x hx
      cases hs with
      | nil => simp at hlen
      | cons h₀ t =>
          by_cases hx0 : x = x₀
          · rw [hx0]
            have hunt : swapWordFn (t.zip t') x₀ = x₀ := by
              refine swapWordFn_eq_of_untouched (t.zip t') x₀ ?_
              intro p hp
              refine ⟨?_, ?_⟩
              · exact hcross p.1 (List.mem_cons_of_mem _ (mem_zip_left t t' p hp)) x₀
                  (List.mem_cons_self ..)
              · intro he
                exact (List.nodup_cons.mp hndup2).1 (he ▸ (mem_zip_right t t' p hp))
            have hne0 : x₀ ≠ h₀ :=
              (hcross h₀ (List.mem_cons_self ..) x₀ (List.mem_cons_self ..)).symm
            rw [List.zip_cons_cons, swapWordFn, Function.comp_apply, hunt, wireSwapFn,
              if_neg hne0, if_pos rfl]
            exact ⟨h₀, List.mem_cons_self .., rfl⟩
          · have hxt : x ∈ t' := by
              rcases List.mem_cons.mp hx with he | he
              · exact absurd he hx0
              · exact he
            have hlen' : t'.length ≤ t.length := by
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨hk, hhk, hxih⟩ := ih t hlen' (List.nodup_cons.mp hndup1).2
              (List.nodup_cons.mp hndup2).2
              (fun h' hh' x' hx' => hcross h' (List.mem_cons_of_mem _ hh')
                x' (List.mem_cons_of_mem _ hx'))
              x hxt
            have e1 : hk ≠ x₀ :=
              hcross hk (List.mem_cons_of_mem h₀ hhk) x₀ (List.mem_cons_self ..)
            have e2 : hk ≠ h₀ := by
              intro he
              exact (List.nodup_cons.mp hndup1).1 (he ▸ hhk)
            rw [List.zip_cons_cons, swapWordFn, Function.comp_apply, hxih, wireSwapFn,
              if_neg e2, if_neg e1]
            exact ⟨hk, List.mem_cons_of_mem _ hhk, rfl⟩

/-- Gathering a nonempty support uses fewer swaps than its cardinality, fills its target
interval exactly, and pairs only target holes with occupied wires outside. -/
theorem gatherSwapPairs_spec (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (S : Finset (Fin Λ)) (hS : S.Nonempty) :
    (gatherSwapPairs ρ S).length + 1 ≤ S.card
    ∧ supportWires (swapWordApply (gatherSwapPairs ρ S) ρ) S
        = wireInterval Λ (minWire ρ S) S.card
    ∧ ∀ p ∈ gatherSwapPairs ρ S,
        p.1 ∈ wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S
        ∧ p.2 ∈ supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card := by
  have hfit := minWire_fit ρ hρ S hS
  have hIcard : (wireInterval Λ (minWire ρ S) S.card).card = S.card :=
    wireInterval_card Λ (minWire ρ S) S.card hfit
  have hWcard : (supportWires ρ S).card = S.card := supportWires_card ρ hρ S
  have hlen : ((wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S).toList).length
      = ((supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).toList).length :=
    gatherSwapPairs_holes_outside ρ hρ S hS
  have hout : ∀ h ∈ (wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S).toList,
      ρ h ∉ S := by
    intro h hh
    have hnotin : h ∉ supportWires ρ S :=
      (Finset.mem_sdiff.mp (Finset.mem_toList.mp hh)).2
    intro hcon
    exact hnotin (mem_supportWires_iff.mpr hcon)
  have hin : ∀ x ∈ (supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).toList,
      ρ x ∈ S :=
    fun x hx => mem_supportWires_iff.mp (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1
  have hcross : ∀ h ∈ (wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S).toList,
      ∀ x ∈ (supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).toList, h ≠ x := by
    intro h hh x hx heq
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).2
      (heq ▸ (Finset.mem_sdiff.mp (Finset.mem_toList.mp hh)).1)
  have hzip := supportWires_swap_zip S
    (wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S).toList
    (supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).toList
    ρ hlen
    (wireInterval Λ (minWire ρ S) S.card \ supportWires ρ S).nodup_toList
    (supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).nodup_toList
    hout hin hcross
  constructor
  · have hcardIW : 1 ≤ (wireInterval Λ (minWire ρ S) S.card ∩ supportWires ρ S).card :=
      Finset.one_le_card.mpr ⟨_, anchor_mem_inter ρ hρ S hS⟩
    have hlen' : (gatherSwapPairs ρ S).length
        = (supportWires ρ S \ wireInterval Λ (minWire ρ S) S.card).card := by
      rw [gatherSwapPairs, List.length_zip, hlen, finset_toList_length]
      omega
    rw [hlen', Finset.card_sdiff, hWcard]
    have hs1 : 1 ≤ S.card := Finset.one_le_card.mpr hS
    omega
  · constructor
    · rw [gatherSwapPairs, hzip, Finset.toList_toFinset, Finset.toList_toFinset]
      apply Finset.ext
      intro w
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    · intro p hp
      rw [gatherSwapPairs] at hp
      exact ⟨Finset.mem_toList.mp (mem_zip_left _ _ p hp),
             Finset.mem_toList.mp (mem_zip_right _ _ p hp)⟩

/-- Gathering a support with least anchor among two disjoint nonempty supports leaves all wires
of the other support beyond the gathered interval. -/
theorem gatherSwapPairs_other_low (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (Sstar Si : Finset (Fin Λ)) (hSstar : Sstar.Nonempty) (hSi : Si.Nonempty)
    (hdisj : Disjoint Sstar Si)
    (hgreedy : minWire ρ Sstar ≤ minWire ρ Si) :
    ∀ w ∈ supportWires (swapWordApply (gatherSwapPairs ρ Sstar) ρ) Si,
      minWire ρ Sstar + Sstar.card ≤ w.val := by
  have hWstar := supportWires_nonempty ρ hρ Sstar hSstar
  have hWi := supportWires_nonempty ρ hρ Si hSi
  obtain ⟨_, hfinal, hpairs⟩ := gatherSwapPairs_spec ρ hρ Sstar hSstar
  have hlen : ((wireInterval Λ (minWire ρ Sstar) Sstar.card
        \ supportWires ρ Sstar).toList).length
      = ((supportWires ρ Sstar
        \ wireInterval Λ (minWire ρ Sstar) Sstar.card).toList).length :=
    gatherSwapPairs_holes_outside ρ hρ Sstar hSstar
  have hziple : ∀ h ∈ (wireInterval Λ (minWire ρ Sstar) Sstar.card
        \ supportWires ρ Sstar).toList,
      ∃ x ∈ (supportWires ρ Sstar
        \ wireInterval Λ (minWire ρ Sstar) Sstar.card).toList,
        swapWordFn (gatherSwapPairs ρ Sstar) h = x := by
    intro h hh
    refine swapWordFn_zip_apply_left _ _ (le_of_eq hlen)
      (wireInterval Λ (minWire ρ Sstar) Sstar.card \ supportWires ρ Sstar).nodup_toList
      (supportWires ρ Sstar \ wireInterval Λ (minWire ρ Sstar) Sstar.card).nodup_toList ?_ h hh
    intro h' hh' x' hx' heq
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx')).2
      (heq ▸ (Finset.mem_sdiff.mp (Finset.mem_toList.mp hh')).1)
  intro w hw
  by_contra hcon
  have hwlt : w.val < minWire ρ Sstar + Sstar.card := by omega
  have hmem : ρ (swapWordFn (gatherSwapPairs ρ Sstar) w) ∈ Si := by
    have h := mem_supportWires_iff.mp hw
    rw [swapWordApply_apply] at h
    exact h
  by_cases hwI : w ∈ wireInterval Λ (minWire ρ Sstar) Sstar.card
  · by_cases hwW : w ∈ supportWires ρ Sstar
    · have hfix : swapWordFn (gatherSwapPairs ρ Sstar) w = w := by
        refine swapWordFn_eq_of_untouched _ w ?_
        intro p hp
        obtain ⟨hm1, hm2⟩ := hpairs p hp
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hm1
        obtain ⟨h3, h4⟩ := Finset.mem_sdiff.mp hm2
        refine ⟨?_, ?_⟩
        · intro heq
          exact h2 (by rw [heq]; exact hwW)
        · intro heq
          exact h4 (by rw [heq]; exact hwI)
      rw [hfix] at hmem
      exact absurd rfl (Finset.disjoint_iff_ne.mp hdisj (ρ w)
        (mem_supportWires_iff.mp hwW) (ρ w) hmem)
    · have hwmem : w ∈ (wireInterval Λ (minWire ρ Sstar) Sstar.card
          \ supportWires ρ Sstar).toList :=
        Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hwI, hwW⟩)
      obtain ⟨x, hxmem, hxσ⟩ := hziple w hwmem
      rw [hxσ] at hmem
      have hxW : x ∈ supportWires ρ Sstar :=
        (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxmem)).1
      exact absurd rfl (Finset.disjoint_iff_ne.mp hdisj (ρ x)
        (mem_supportWires_iff.mp hxW) (ρ x) hmem)
  · by_cases hwW : w ∈ supportWires ρ Sstar
    · exact absurd (outsideWire_ge ρ Sstar hWstar hwW hwI) (by omega)
    · have hfix : swapWordFn (gatherSwapPairs ρ Sstar) w = w := by
        refine swapWordFn_eq_of_untouched _ w ?_
        intro p hp
        obtain ⟨hm1, hm2⟩ := hpairs p hp
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hm1
        obtain ⟨h3, h4⟩ := Finset.mem_sdiff.mp hm2
        refine ⟨?_, ?_⟩
        · intro heq
          exact hwI (by rw [← heq]; exact h1)
        · intro heq
          exact hwW (by rw [← heq]; exact h3)
      rw [hfix] at hmem
      have hwWi : w ∈ supportWires ρ Si := mem_supportWires_iff.mpr hmem
      have hmin := minWire_le ρ Si hWi hwWi
      rw [mem_wireInterval_iff] at hwI
      omega

/-- In a list without duplicates, membership after erasing `a` implies original membership and
inequality with `a`. -/
private theorem mem_erase_imp {Λ : ℕ} : ∀ (l : List (Fin Λ)) (a b : Fin Λ),
    l.Nodup → b ∈ l.erase a → b ≠ a ∧ b ∈ l := by
  intro l
  induction l with
  | nil => intro a b _ h; simp at h
  | cons c t ih =>
      intro a b hndup h
      by_cases hca : c = a
      · rw [hca] at h ⊢
        rw [List.erase_cons] at h
        simp at h
        have hanot : a ∉ t := by
          have hcnot : c ∉ t := (List.nodup_cons.mp hndup).1
          rw [← hca]; exact hcnot
        exact ⟨fun heq => hanot (heq ▸ h), List.mem_cons_of_mem _ h⟩
      · have heq : (c :: t).erase a = c :: t.erase a := by
          rw [List.erase_cons]; simp [hca]
        rw [heq] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact ⟨fun heq2 => hca (h' ▸ heq2), h' ▸ List.mem_cons_self ..⟩
        · have this := ih a b (List.nodup_cons.mp hndup).2 h'
          exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩

/-- A list member distinct from the erased element remains in the erased list. -/
private theorem mem_of_ne_erase {Λ : ℕ} {l : List (Fin Λ)} {a x : Fin Λ}
    (hx : x ∈ l) (hxa : x ≠ a) : x ∈ l.erase a := by
  induction l with
  | nil => simp at hx
  | cons c t ih =>
      by_cases hca : c = a
      · rw [hca] at hx ⊢
        rw [List.erase_cons]
        simp
        rcases List.mem_cons.mp hx with h' | h'
        · exact absurd (hca ▸ h') hxa
        · exact h'
      · have heq : (c :: t).erase a = c :: t.erase a := by
          rw [List.erase_cons]; simp [hca]
        rw [heq]
        rcases List.mem_cons.mp hx with h' | h'
        · exact h' ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h')

/-- For a duplicate-free list containing `a`, its finite set is obtained by inserting `a` into
the finite set of the erased list. -/
private theorem toFinset_erase_insert {Λ : ℕ} {l : List (Fin Λ)} {a : Fin Λ}
    (hndup : l.Nodup) (h : a ∈ l) : l.toFinset = insert a (l.erase a).toFinset := by
  classical
  apply Finset.ext
  intro x
  rw [Finset.mem_insert, List.mem_toFinset, List.mem_toFinset]
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (mem_of_ne_erase hx hxa)
  · intro hx
    rcases hx with hx | hx
    · exact hx ▸ h
    · exact (mem_erase_imp l a x hndup hx).2

/-- A duplicate-free layer of disjoint nonempty supports above frontier `M` can be gathered into
disjoint intervals using the stated swap budget and only wires at or above `M`. -/
private theorem layer_compile_aux {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) :
    ∀ (n : ℕ) (l : List (Fin Λ)) (ρ : Fin Λ → Fin Λ) (M : ℕ),
      (∀ i ∈ l, ∀ j ∈ l, i ≠ j → Disjoint (F i).support (F j).support) →
      l.length ≤ n → l.Nodup → Function.Bijective ρ →
      (∀ i ∈ l, (F i).support.Nonempty) →
      (∀ i ∈ l, ∀ w ∈ supportWires ρ (F i).support, M ≤ w.val) →
      ∃ (W : List (Fin Λ × Fin Λ)) (anchor : Fin Λ → ℕ) (M' : ℕ),
        W.length ≤ clause52LayerRouteSwaps F l ∧
        (∀ p ∈ W, M ≤ p.1.val ∧ M ≤ p.2.val) ∧
        M ≤ M' ∧
        (∀ i ∈ l, anchor i + (F i).support.card ≤ Λ ∧ M ≤ anchor i ∧
          supportWires (swapWordApply W ρ) (F i).support
            = wireInterval Λ (anchor i) (F i).support.card) ∧
        (∀ i ∈ l, ∀ j ∈ l, i ≠ j →
          Disjoint (wireInterval Λ (anchor i) (F i).support.card)
            (wireInterval Λ (anchor j) (F j).support.card)) := by
  intro n
  induction n with
  | zero =>
      intro l ρ M hF hn hndup hρ hNE hlow
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons _ _ => simp at hn
      subst hl
      refine ⟨[], fun _ => M, M, by simp [clause52LayerRouteSwaps], fun p hp => absurd hp (by simp),
        Nat.le_refl _, fun i hi => absurd hi (by simp),
        fun i hi j hj hij => absurd hi (by simp)⟩
  | succ n ih =>
      intro l ρ M hF hn hndup hρ hNE hlow
      cases l with
      | nil =>
          refine ⟨[], fun _ => M, M, by simp [clause52LayerRouteSwaps], fun p hp => absurd hp (by simp),
            Nat.le_refl _, fun i hi => absurd hi (by simp),
            fun i hi j hj hij => absurd hi (by simp)⟩
      | cons u₀ rest₀ =>
          have hAne : ((u₀ :: rest₀).toFinset.image
              (fun i => minWire ρ (F i).support)).Nonempty :=
            ⟨minWire ρ (F u₀).support, Finset.mem_image.mpr ⟨u₀, by simp, rfl⟩⟩
          have hminmem := Finset.min'_mem _ hAne
          obtain ⟨ustar, hustar_fin, hustar_aeq⟩ := Finset.mem_image.mp hminmem
          have hustar_mem : ustar ∈ u₀ :: rest₀ := List.mem_toFinset.mp hustar_fin
          have hgreedy : ∀ i ∈ u₀ :: rest₀,
              minWire ρ (F ustar).support ≤ minWire ρ (F i).support := by
            intro i hi
            have hle := Finset.min'_le _ (minWire ρ (F i).support)
              (Finset.mem_image.mpr ⟨i, List.mem_toFinset.mpr hi, by rfl⟩)
            rw [hustar_aeq]
            exact hle
          have hNEustar : (F ustar).support.Nonempty := hNE ustar hustar_mem
          have hWstarNe := supportWires_nonempty ρ hρ (F ustar).support hNEustar
          have hMstar : M ≤ minWire ρ (F ustar).support :=
            hlow ustar hustar_mem _ (minWire_mem ρ (F ustar).support hWstarNe)
          have hfitstar : minWire ρ (F ustar).support + (F ustar).support.card ≤ Λ :=
            minWire_fit ρ hρ (F ustar).support hNEustar
          have hρg : Function.Bijective
              (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) :=
            swapWordApply_bijective _ ρ hρ
          obtain ⟨hlenWg, hfinalg, hpairsg⟩ :=
            gatherSwapPairs_spec ρ hρ (F ustar).support hNEustar
          have hrestlen : ((u₀ :: rest₀).erase ustar).length = (u₀ :: rest₀).length - 1 :=
            List.length_erase_of_mem hustar_mem
          have hrestNodup : ((u₀ :: rest₀).erase ustar).Nodup := hndup.erase ustar
          have hrestsub : ∀ i ∈ (u₀ :: rest₀).erase ustar, i ∈ u₀ :: rest₀ ∧ i ≠ ustar :=
            fun i hi => ⟨(mem_erase_imp (u₀ :: rest₀) ustar i hndup hi).2,
              (mem_erase_imp (u₀ :: rest₀) ustar i hndup hi).1⟩
          have hustar_rest : ustar ∉ (u₀ :: rest₀).erase ustar :=
            fun hc => (mem_erase_imp (u₀ :: rest₀) ustar ustar hndup hc).1 rfl
          have hNE' : ∀ i ∈ (u₀ :: rest₀).erase ustar, (F i).support.Nonempty :=
            fun i hi => hNE i (hrestsub i hi).1
          have hlow' : ∀ i ∈ (u₀ :: rest₀).erase ustar,
              ∀ w ∈ supportWires
                (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) (F i).support,
              max M (minWire ρ (F ustar).support + (F ustar).support.card) ≤ w.val := by
            intro i hi w hw
            have hne : ustar ≠ i := fun heq =>
              (mem_erase_imp (u₀ :: rest₀) ustar i hndup hi).1 heq.symm
            have hdisj : Disjoint (F ustar).support (F i).support :=
              hF ustar hustar_mem i (hrestsub i hi).1 hne
            have hgr := hgreedy i (hrestsub i hi).1
            have hlowi := gatherSwapPairs_other_low ρ hρ (F ustar).support (F i).support hNEustar
              (hNE' i hi) hdisj hgr w hw
            omega
          obtain ⟨Wr, anchor_r, Mr', hlenWr, hpairsWr, hMMr, hfinalr, hdisjr⟩ :=
            ih ((u₀ :: rest₀).erase ustar)
              (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ)
              (max M (minWire ρ (F ustar).support + (F ustar).support.card))
              (fun i hi j hj hij =>
                hF i (mem_erase_imp (u₀ :: rest₀) ustar i hndup hi).2
                  j (mem_erase_imp (u₀ :: rest₀) ustar j hndup hj).2 hij)
              (by rw [hrestlen]; simp only [List.length_cons] at hn ⊢; omega)
              hrestNodup hρg hNE' hlow'
          refine ⟨gatherSwapPairs ρ (F ustar).support ++ Wr,
            fun i => if i = ustar then minWire ρ (F ustar).support else anchor_r i, Mr', ?_, ?_, ?_, ?_, ?_⟩
          · have hsplit : (u₀ :: rest₀).toFinset
                = insert ustar ((u₀ :: rest₀).erase ustar).toFinset :=
              toFinset_erase_insert hndup hustar_mem
            have hsum : clause52LayerRouteSwaps F (u₀ :: rest₀)
                = clause52TermRouteSwaps F ustar + clause52LayerRouteSwaps F ((u₀ :: rest₀).erase ustar) := by
              rw [clause52LayerRouteSwaps, clause52LayerRouteSwaps, hsplit, Finset.sum_insert
                (fun hc => hustar_rest (List.mem_toFinset.mp hc))]
            have hterm : clause52TermRouteSwaps F ustar = (F ustar).support.card - 1 := rfl
            rw [List.length_append, hsum, hterm]
            have h1 := hlenWg
            have h2 := hlenWr
            omega
          · intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · obtain ⟨hm1, hm2⟩ := hpairsg p hp
              obtain ⟨h1, _⟩ := Finset.mem_sdiff.mp hm1
              obtain ⟨h3, h4⟩ := Finset.mem_sdiff.mp hm2
              obtain ⟨hw1, hw2⟩ := mem_wireInterval_iff.mp h1
              have hout := outsideWire_ge ρ (F ustar).support hWstarNe h3 h4
              constructor <;> omega
            · have h := hpairsWr p hp
              constructor <;> omega
          · exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hMMr) (Nat.le_refl _)
          · intro i hi
            by_cases hiu : i = ustar
            · simp only [hiu]
              have hWapp : swapWordApply (gatherSwapPairs ρ (F ustar).support ++ Wr) ρ
                  = swapWordApply Wr (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) :=
                swapWordApply_append _ Wr ρ
              have hin : ∀ w ∈ wireInterval Λ (minWire ρ (F ustar).support) (F ustar).support.card,
                  (swapWordApply (gatherSwapPairs ρ (F ustar).support ++ Wr) ρ) w
                    = (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) w := by
                intro w hw
                obtain ⟨hw1, hw2⟩ := mem_wireInterval_iff.mp hw
                rw [hWapp, swapWordApply_apply, swapWordApply_apply,
                  swapWordFn_low_fix Wr _ hpairsWr w (by omega), swapWordApply_apply]
              refine ⟨hfitstar, hMstar, ?_⟩
              apply Finset.ext
              intro w
              constructor
              · intro hwm
                have hwval : (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ)
                    (swapWordFn Wr w) ∈ (F ustar).support := by
                  have h0 := mem_supportWires_iff.mp hwm
                  rw [hWapp, swapWordApply_apply] at h0
                  exact h0
                have hσI : swapWordFn Wr w ∈ supportWires
                    (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) (F ustar).support :=
                  mem_supportWires_iff.mpr hwval
                rw [hfinalg] at hσI
                obtain ⟨hσ1, hσ2⟩ := mem_wireInterval_iff.mp hσI
                have hwlt : w.val
                    < max M (minWire ρ (F ustar).support + (F ustar).support.card) := by
                  by_contra hc
                  have hge : max M (minWire ρ (F ustar).support + (F ustar).support.card) ≤ w.val :=
                    by omega
                  have hhp := swapWordFn_high_preserve Wr _ hpairsWr w hge
                  omega
                have hfix : swapWordFn Wr w = w :=
                  swapWordFn_low_fix Wr _ hpairsWr w hwlt
                have hwin : w ∈ supportWires
                    (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) (F ustar).support := by
                  rw [hfix] at hwval
                  exact mem_supportWires_iff.mpr hwval
                rw [hfinalg] at hwin
                exact hwin
              · intro hwI
                refine mem_supportWires_iff.mpr ?_
                have hval : (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) w
                    ∈ (F ustar).support := by
                  have hw' : w ∈ supportWires
                      (swapWordApply (gatherSwapPairs ρ (F ustar).support) ρ) (F ustar).support := by
                    rw [hfinalg]; exact hwI
                  exact mem_supportWires_iff.mp hw'
                rw [hin w hwI]
                exact hval
            · have hiR : i ∈ (u₀ :: rest₀).erase ustar := mem_of_ne_erase hi hiu
              have hsub := hfinalr i hiR
              simp only [if_neg hiu]
              rw [swapWordApply_append, hsub.2.2]
              exact ⟨hsub.1, Nat.le_trans (Nat.le_max_left _ _) hsub.2.1, rfl⟩
          · intro i hi j hj hij
            by_cases hiu : i = ustar
            · simp only [hiu]
              have hjne : j ≠ ustar := fun heq => hij (by rw [hiu, heq])
              have hjsub : j ∈ (u₀ :: rest₀).erase ustar := mem_of_ne_erase hj hjne
              have hrestr := hfinalr j hjsub
              simp only [if_neg hjne]
              have hge : minWire ρ (F ustar).support + (F ustar).support.card ≤ anchor_r j :=
                Nat.le_trans (Nat.le_max_right _ _) hrestr.2.1
              exact wireInterval_disjoint Λ (minWire ρ (F ustar).support) (F ustar).support.card
                (anchor_r j) (F j).support.card hge
            · by_cases hju : j = ustar
              · simp only [hju, if_neg hiu]
                have hisub : i ∈ (u₀ :: rest₀).erase ustar := mem_of_ne_erase hi hiu
                have hrestr := hfinalr i hisub
                have hge : minWire ρ (F ustar).support + (F ustar).support.card ≤ anchor_r i :=
                  Nat.le_trans (Nat.le_max_right _ _) hrestr.2.1
                exact (wireInterval_disjoint Λ (minWire ρ (F ustar).support) (F ustar).support.card
                  (anchor_r i) (F i).support.card hge).symm
              · simp only [if_neg hiu, if_neg hju]
                exact hdisjr i (mem_of_ne_erase hi hiu) j (mem_of_ne_erase hj hju) hij

end Routing

end Attached

/-- A duplicate-free layer of pairwise disjoint nonempty supports can be routed into disjoint
consecutive intervals with at most `clause52LayerRouteSwaps F l` swaps. -/
theorem frontier1 {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (l : List (Fin Λ))
    (ρ : Fin Λ → Fin Λ)
    (hF : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Disjoint (F i).support (F j).support)
    (hndup : l.Nodup) (hρ : Function.Bijective ρ)
    (hNE : ∀ i ∈ l, (F i).support.Nonempty) :
    ∃ (W : List (Fin Λ × Fin Λ)) (anchor : Fin Λ → ℕ),
      W.length ≤ clause52LayerRouteSwaps F l ∧
      (∀ i ∈ l, anchor i + (F i).support.card ≤ Λ ∧
        supportWires (swapWordApply W ρ) (F i).support
          = wireInterval Λ (anchor i) (F i).support.card) ∧
      (∀ i ∈ l, ∀ j ∈ l, i ≠ j →
        Disjoint (wireInterval Λ (anchor i) (F i).support.card)
          (wireInterval Λ (anchor j) (F j).support.card)) := by
  obtain ⟨W, anchor, _, hlen, _, _, hfinal, hdisj⟩ :=
    layer_compile_aux F l.length l ρ 0 hF (Nat.le_refl _) hndup hρ hNE
      (fun _ _ _ _ => Nat.zero_le _)
  refine ⟨W, anchor, hlen, fun i hi => ⟨(hfinal i hi).1, (hfinal i hi).2.2⟩, hdisj⟩

/-- Every layer in `clause52Schedule F L` can be routed within its swap budget so that its
nonempty supports occupy pairwise disjoint consecutive intervals. -/
theorem frontier1_layers {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (L : ℕ)
    (ρ : Fin Λ → Fin Λ) (hρ : Function.Bijective ρ)
    (l : List (Fin Λ)) (hl : l ∈ clause52Schedule F L) :
    ∃ (W : List (Fin Λ × Fin Λ)) (anchor : Fin Λ → ℕ),
      W.length ≤ clause52LayerRouteSwaps F l ∧
      (∀ i ∈ l, (F i).support.Nonempty →
        anchor i + (F i).support.card ≤ Λ ∧
        supportWires (swapWordApply W ρ) (F i).support
          = wireInterval Λ (anchor i) (F i).support.card) ∧
      (∀ i ∈ l, ∀ j ∈ l, i ≠ j → (F i).support.Nonempty → (F j).support.Nonempty →
        Disjoint (wireInterval Λ (anchor i) (F i).support.card)
          (wireInterval Λ (anchor j) (F j).support.card)) := by
  have hdisjL : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Disjoint (F i).support (F j).support :=
    fun i hi j hj hij => clause52Schedule_layer_disjoint F L l hl i j hi hj hij
  obtain ⟨c, _, hcl⟩ := List.mem_map.mp hl
  have hndup : (l.filter (fun i => (F i).support.Nonempty)).Nodup := by
    subst hcl
    exact (List.Nodup.filter _ (List.nodup_finRange Λ)).filter _
  obtain ⟨W, anchor, hlen', hfinal', hdisj'⟩ :=
    frontier1 F (l.filter (fun i => (F i).support.Nonempty)) ρ
      (fun i hi j hj hij =>
        hdisjL i (List.mem_of_mem_filter hi) j (List.mem_of_mem_filter hj) hij)
      hndup hρ (fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2)
  have hsub : (l.filter (fun i => (F i).support.Nonempty)).toFinset ⊆ l.toFinset :=
    fun i hi =>
      List.mem_toFinset.mpr (List.mem_of_mem_filter (List.mem_toFinset.mp hi))
  have hsum : (l.filter (fun i => (F i).support.Nonempty)).toFinset.sum
        (fun i => clause52TermRouteSwaps F i)
      = l.toFinset.sum (fun i => clause52TermRouteSwaps F i) := by
    refine Finset.sum_subset hsub ?_
    intro i hi hni
    have hcard : (F i).support.card = 0 := by
      by_contra hpos
      have hgt : 0 < (F i).support.card := Nat.pos_of_ne_zero hpos
      exact hni (List.mem_toFinset.mpr
        (List.mem_filter.mpr ⟨List.mem_toFinset.mp hi,
          decide_eq_true (Finset.card_pos.mp hgt)⟩))
    simp [clause52TermRouteSwaps, hcard]
  refine ⟨W, anchor, ?_, ?_, ?_⟩
  · have h1 : clause52LayerRouteSwaps F l
        = l.toFinset.sum (fun i => clause52TermRouteSwaps F i) := rfl
    rw [h1, ← hsum]
    exact hlen'
  · intro i hi hne
    exact hfinal' i (List.mem_filter.mpr ⟨hi, decide_eq_true hne⟩)
  · intro i hi j hj hij hnei hnej
    exact hdisj' i (List.mem_filter.mpr ⟨hi, decide_eq_true hnei⟩)
      j (List.mem_filter.mpr ⟨hj, decide_eq_true hnej⟩) hij

end Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSupportRouting
