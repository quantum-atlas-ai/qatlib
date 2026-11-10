/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.MultiControl.Section7.GrayParity
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open scoped BigOperators

namespace Qatlib.Papers.ElemGates95.MultiControl.Section7

def prependBit {m : ℕ} (b : Bool) (v : Fin m → Bool) : Fin (m + 1) → Bool :=
  Fin.cases b v

@[simp] theorem prependBit_zero {m : ℕ} (b : Bool) (v : Fin m → Bool) :
    prependBit b v 0 = b := by
  simp [prependBit]

@[simp] theorem prependBit_succ {m : ℕ} (b : Bool) (v : Fin m → Bool) (j : Fin m) :
    prependBit b v (Fin.succ j) = v j := by
  simp [prependBit]

theorem prependBit_injective {m : ℕ} (b : Bool) :
    Function.Injective (prependBit (m := m) b) := by
  intro u v h
  funext j
  have := congrFun h (Fin.succ j)
  simpa using! this

def zeroVec (m : ℕ) : Fin m → Bool := fun _ => false

def grayCode : (m : ℕ) → List (Fin m → Bool)
  | 0 => [zeroVec 0]
  | m + 1 =>
      (grayCode m).map (prependBit false) ++ (grayCode m).reverse.map (prependBit true)

theorem grayCode_length : ∀ m : ℕ, (grayCode m).length = 2 ^ m
  | 0 => by simp [grayCode]
  | m + 1 => by
      rw [grayCode]
      simp only [List.length_append, List.length_map, List.length_reverse,
        grayCode_length m]
      rw [pow_succ]
      ring

theorem mem_grayCode : ∀ {m : ℕ} (v : Fin m → Bool), v ∈ grayCode m
  | 0, v => by
      have hv : v = zeroVec 0 := by
        funext i
        exact Fin.elim0 i
      rw [hv]
      simp [grayCode]
  | m + 1, v => by
      have hv : v = prependBit (v 0) (fun j => v (Fin.succ j)) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j; simp
      rw [hv]
      rw [grayCode, List.mem_append, List.mem_map, List.mem_map]
      cases h0 : v 0
      · left
        exact ⟨fun j => v (Fin.succ j), mem_grayCode _, by simp⟩
      · right
        refine ⟨fun j => v (Fin.succ j), ?_, by simp⟩
        rw [List.mem_reverse]
        exact mem_grayCode _

theorem grayCode_head : ∀ m : ℕ, (grayCode m).head? = some (zeroVec m)
  | 0 => by simp [grayCode]
  | m + 1 => by
      rw [grayCode]
      have hne : ((grayCode m).map (prependBit (m := m) false)) ≠ [] := by
        intro h
        have hnil : grayCode m = [] := List.map_eq_nil_iff.mp h
        have hpos : 0 < (grayCode m).length := by
          rw [grayCode_length]; positivity
        rw [hnil] at hpos
        simp at hpos
      rw [List.head?_append_of_ne_nil _ hne, List.head?_map, grayCode_head m]
      simp only [Option.map_some]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i <;> simp [zeroVec]

theorem grayCode_nodup : ∀ m : ℕ, (grayCode m).Nodup
  | 0 => by simp [grayCode]
  | m + 1 => by
      rw [grayCode]
      refine List.Nodup.append
        (List.Nodup.map (prependBit_injective false) (grayCode_nodup m))
        (List.Nodup.map (prependBit_injective true) (List.nodup_reverse.mpr (grayCode_nodup m)))
        ?_
      intro v hvA hvB
      simp only [List.mem_map] at hvA hvB
      obtain ⟨u, _, rfl⟩ := hvA
      obtain ⟨w, _, hw⟩ := hvB
      have := congrFun hw 0
      simp at this

def DiffOne {m : ℕ} (u v : Fin m → Bool) : Prop :=
  ∃ k : Fin m, u k ≠ v k ∧ ∀ j : Fin m, j ≠ k → u j = v j

theorem DiffOne.symm {m : ℕ} {u v : Fin m → Bool} (h : DiffOne u v) : DiffOne v u := by
  obtain ⟨k, hk, hrest⟩ := h
  exact ⟨k, hk.symm, fun j hj => (hrest j hj).symm⟩

theorem DiffOne.prepend_same {m : ℕ} (b : Bool) {u v : Fin m → Bool}
    (h : DiffOne u v) : DiffOne (prependBit b u) (prependBit b v) := by
  obtain ⟨k, hk, hrest⟩ := h
  refine ⟨Fin.succ k, ?_, ?_⟩
  · simpa using! hk
  · intro j hj
    induction j using Fin.cases with
    | zero => simp
    | succ i =>
      have hik : i ≠ k := by
        intro hEq
        exact hj (congrArg Fin.succ hEq)
      simpa using! hrest i hik

theorem DiffOne.prepend_diff {m : ℕ} (u : Fin m → Bool) :
    DiffOne (prependBit false u) (prependBit true u) := by
  refine ⟨0, ?_, ?_⟩
  · simp
  · intro j hj
    induction j using Fin.cases with
    | zero => exact absurd rfl hj
    | succ i => simp

theorem grayCode_isChain : ∀ m : ℕ, (grayCode m).IsChain DiffOne
  | 0 => by
      rw [grayCode]
      exact List.isChain_singleton _
  | m + 1 => by
      rw [grayCode]
      refine List.IsChain.append ?_ ?_ ?_
      · exact List.isChain_map_of_isChain (prependBit false)
          (fun _ _ h => DiffOne.prepend_same false h) (grayCode_isChain m)
      · refine List.isChain_map_of_isChain (prependBit true)
          (fun _ _ h => DiffOne.prepend_same true h) ?_
        rw [List.isChain_reverse]
        exact (grayCode_isChain m).imp (fun _ _ h => h.symm)
      · intro x hx y hy
        rw [List.getLast?_map] at hx
        rw [List.head?_map, List.head?_reverse] at hy
        cases hl : (grayCode m).getLast? with
        | none => rw [hl] at hx; simp at hx
        | some u =>
          rw [hl] at hx hy
          simp only [Option.map_some, Option.mem_some_iff] at hx hy
          rw [← hx, ← hy]
          exact DiffOne.prepend_diff u

def grayNonempty (m : ℕ) : List (Fin m → Bool) := (grayCode m).tail

theorem grayNonempty_length (m : ℕ) : (grayNonempty m).length = 2 ^ m - 1 := by
  rw [grayNonempty, List.length_tail, grayCode_length]

theorem grayNonempty_nodup (m : ℕ) : (grayNonempty m).Nodup :=
  List.Pairwise.tail (grayCode_nodup m)

theorem grayNonempty_isChain (m : ℕ) : (grayNonempty m).IsChain DiffOne := by
  rw [grayNonempty]
  exact (grayCode_isChain m).tail

theorem grayNonempty_ne_zero (m : ℕ) {v : Fin m → Bool} (hv : v ∈ grayNonempty m) :
    v ≠ zeroVec m := by
  intro hveq
  have hhead : zeroVec m ∈ (grayCode m).head? := by rw [grayCode_head]; simp
  have hlist : zeroVec m :: (grayCode m).tail = grayCode m := List.cons_head?_tail hhead
  have hnd : (zeroVec m :: (grayCode m).tail).Nodup := by rw [hlist]; exact grayCode_nodup m
  have hnot := (List.nodup_cons.mp hnd).1
  apply hnot
  rw [← hveq]
  exact hv

theorem mem_grayNonempty_of_ne_zero (m : ℕ) {v : Fin m → Bool} (hv : v ≠ zeroVec m) :
    v ∈ grayNonempty m := by
  have hmem : v ∈ grayCode m := mem_grayCode v
  have hhead : zeroVec m ∈ (grayCode m).head? := by rw [grayCode_head]; simp
  have hlist : zeroVec m :: (grayCode m).tail = grayCode m := List.cons_head?_tail hhead
  rw [← hlist, List.mem_cons] at hmem
  rcases hmem with h | h
  · exact absurd h hv
  · exact h

theorem gray_lemma71_counts (n : ℕ) (_hn : 3 ≤ n) :
    (grayNonempty (n - 1)).length = 2 ^ (n - 1) - 1 ∧
      (grayNonempty (n - 1)).length - 1 = 2 ^ (n - 1) - 2 := by
  refine ⟨grayNonempty_length (n - 1), ?_⟩
  rw [grayNonempty_length, Nat.sub_sub]

def support {m : ℕ} (v : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => v i = true)

theorem support_zeroVec (m : ℕ) : support (zeroVec m) = ∅ := by
  ext i; simp [support, zeroVec]

theorem support_eq_empty_iff {m : ℕ} (v : Fin m → Bool) :
    support v = ∅ ↔ v = zeroVec m := by
  constructor
  · intro h
    funext i
    have hni : i ∉ support v := by rw [h]; simp
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hni
    have : v i = false := by
      cases hv : v i
      · rfl
      · exact absurd hv hni
    simpa [zeroVec] using! this
  · intro h
    rw [h]
    exact support_zeroVec m

theorem support_injective (m : ℕ) : Function.Injective (support (m := m)) := by
  intro u v h
  funext i
  have hiff : (u i = true) ↔ (v i = true) := by
    have := Finset.ext_iff.mp h i
    simpa [support] using! this
  cases hu : u i <;> cases hv : v i <;> simp_all

def indicatorSet {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool :=
  fun i => decide (i ∈ S)

theorem support_indicatorSet {m : ℕ} (S : Finset (Fin m)) :
    support (indicatorSet S) = S := by
  ext i; simp [support, indicatorSet]

theorem indicatorSet_ne_zero {m : ℕ} {S : Finset (Fin m)} (hS : S.Nonempty) :
    indicatorSet S ≠ zeroVec m := by
  intro h
  have hsupp : support (indicatorSet S) = support (zeroVec m) := by rw [h]
  rw [support_indicatorSet, support_zeroVec] at hsupp
  exact (Finset.nonempty_iff_ne_empty.mp hS) hsupp

def grayTerm {m : ℕ} (x : Fin m → Bool) (v : Fin m → Bool) : ℚ :=
  (-1 : ℚ) ^ ((support v).card - 1) * xorVal x (support v)

noncomputable def grayExponent (m : ℕ) (x : Fin m → Bool) : ℚ :=
  ((grayNonempty m).map (grayTerm x)).sum

theorem grayTerm_empty {m : ℕ} (x : Fin m → Bool) :
    (-1 : ℚ) ^ ((∅ : Finset (Fin m)).card - 1) * xorVal x ∅ = 0 := by
  simp [xorVal, subsetSign]

theorem grayExponent_eq (m : ℕ) (hm : 1 ≤ m) (x : Fin m → Bool) :
    grayExponent m x
      = (2 : ℚ) ^ (m - 1) * (if (∀ i, x i = true) then 1 else 0) := by
  unfold grayExponent
  have hnd := grayNonempty_nodup m
  have hsum : ((grayNonempty m).map (grayTerm x)).sum
      = (grayNonempty m).toFinset.sum (grayTerm x) :=
    (List.sum_toFinset (grayTerm x) hnd).symm
  rw [hsum]
  have htof : (grayNonempty m).toFinset
      = (Finset.univ : Finset (Fin m → Bool)).filter (fun v => v ≠ zeroVec m) := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hv => grayNonempty_ne_zero m hv,
      fun hv => mem_grayNonempty_of_ne_zero m hv⟩
  rw [htof]
  have hbij : (∑ v ∈ (Finset.univ : Finset (Fin m → Bool)).filter (fun v => v ≠ zeroVec m),
        grayTerm x v)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.Nonempty),
          ((-1 : ℚ) ^ (S.card - 1) * xorVal x S) := by
    refine Finset.sum_bij (fun v _ => support v) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [Finset.nonempty_iff_ne_empty]
      intro hzero
      exact hv ((support_eq_empty_iff v).mp hzero)
    · intro a _ b _ hab
      exact support_injective m hab
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      refine ⟨indicatorSet S, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact indicatorSet_ne_zero hS
      · exact support_indicatorSet S
    · intro v _
      rfl
  rw [hbij]

  have hfilter : (∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.Nonempty),
        ((-1 : ℚ) ^ (S.card - 1) * xorVal x S))
      = ∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1) * xorVal x S := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun S _ => by
      by_cases hS : S.Nonempty
      · simp [hS]
      · have hempty : S = ∅ := by
          simpa [Finset.not_nonempty_iff_eq_empty] using! hS
        subst hempty
        simp [xorVal, subsetSign]
  rw [hfilter]
  exact altSum_identity hm x

end Qatlib.Papers.ElemGates95.MultiControl.Section7
