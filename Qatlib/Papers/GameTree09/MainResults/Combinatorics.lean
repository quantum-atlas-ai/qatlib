/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GameTree09.MainResults.Composition
import Mathlib.Data.Fin.SuccPred
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Classical
open scoped BigOperators

namespace Qatlib.Papers.GameTree09.MainResults

namespace Formula

variable {m n : ℕ}

theorem eval_mapLeaf (f : Fin m → Fin n) (ψ : Formula m) (x : Fin n → Bool) :
    (ψ.mapLeaf f).eval x = ψ.eval (fun i => x (f i)) := by
  induction ψ with
  | leaf i => simp [mapLeaf, eval]
  | and a b ha hb => simp [mapLeaf, eval, ha, hb]
  | or a b ha hb => simp [mapLeaf, eval, ha, hb]

theorem nodeAt_mapLeaf (f : Fin m → Fin n) (ψ : Formula m) (p : List Bool) :
    (ψ.mapLeaf f).nodeAt p = (ψ.nodeAt p).map (Formula.mapLeaf f) := by
  induction ψ generalizing p with
  | leaf i =>
      cases p with
      | nil => simp [mapLeaf, nodeAt]
      | cons c rest => cases c <;> simp [mapLeaf, nodeAt]
  | and a b ha hb =>
      cases p with
      | nil => simp [mapLeaf, nodeAt]
      | cons c rest => cases c <;> simp [mapLeaf, nodeAt, ha rest, hb rest]
  | or a b ha hb =>
      cases p with
      | nil => simp [mapLeaf, nodeAt]
      | cons c rest => cases c <;> simp [mapLeaf, nodeAt, ha rest, hb rest]

theorem eval_allTrue (ψ : Formula n) : ψ.eval (fun _ => true) = true := by
  induction ψ with
  | leaf i => simp [eval]
  | and a b ha hb => simp [eval, ha, hb]
  | or a b ha hb => simp [eval, ha, hb]

end Formula

theorem parentGate_castSucc {J : ℕ} (hJ : 0 < J) (g : Fin (J + 1) → Bool)
    (k : Fin (J + 1)) :
    parentGate (J + 1) g k.castSucc = parentGate J (fun i => g i.succ) k := by
  conv_lhs => unfold parentGate
  rw [dif_neg (by simp only [Fin.val_castSucc]; omega)]
  rw [dif_neg (by omega)]
  congr 1

theorem parentGate_last {J : ℕ} (g : Fin (J + 1) → Bool) :
    parentGate (J + 1) g (Fin.last (J + 1)) = some (g 0) := by
  conv_lhs => unfold parentGate
  rw [dif_pos (Fin.val_last (J + 1))]

theorem comb_succ_eq (J : ℕ) (g : Fin (J + 1) → Bool) :
    comb (J + 1) g =
      (if g 0 then Formula.and (Formula.mapLeaf Fin.castSucc (comb J (fun i => g i.succ)))
          (Formula.leaf (Fin.last (J + 1)))
       else Formula.or (Formula.mapLeaf Fin.castSucc (comb J (fun i => g i.succ)))
          (Formula.leaf (Fin.last (J + 1)))) := rfl

def pref {J : ℕ} (x : Fin (J + 2) → Bool) : Fin (J + 1) → Bool := fun i => x i.castSucc

theorem comb_nodeAt (J : ℕ) (g : Fin J → Bool) (k : Fin (J + 1)) :
    (comb J g).nodeAt (combPath J k) = some (Formula.leaf k) := by
  induction J with
  | zero =>
      have hk : k = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (by omega)
      subst hk
      simp [comb, combPath, Formula.nodeAt]
  | succ J ih =>
      by_cases h : k.val = J + 1
      · have hk : k = Fin.last (J + 1) := Fin.ext (by rw [h, Fin.val_last])
        subst hk
        have hpath : combPath (J + 1) (Fin.last (J + 1)) = [true] := by
          simp only [combPath]
          rw [dif_pos (Fin.val_last (J + 1))]
        rw [hpath, comb_succ_eq]
        split_ifs with hg <;> simp [Formula.nodeAt]
      · have hkne : k ≠ Fin.last (J + 1) := by
          intro hk; apply h; rw [hk, Fin.val_last]
        obtain ⟨k', hk'⟩ := Fin.eq_castSucc_of_ne_last hkne
        rw [← hk']
        have hpath : combPath (J + 1) k'.castSucc = false :: combPath J k' := by
          conv_lhs => rw [combPath]
          rw [dif_neg (by simp only [Fin.val_castSucc]; omega)]
          simp only [List.cons.injEq, true_and]
          congr 1
        rw [hpath, comb_succ_eq]
        split_ifs with hg
        · simp only [Formula.nodeAt, Bool.false_eq_true, if_false, Formula.nodeAt_mapLeaf,
            ih (fun i => g i.succ) k']
          simp [Formula.mapLeaf]
        · simp only [Formula.nodeAt, Bool.false_eq_true, if_false, Formula.nodeAt_mapLeaf,
            ih (fun i => g i.succ) k']
          simp [Formula.mapLeaf]

theorem comb_eval_succ (J : ℕ) (g : Fin (J + 1) → Bool) (x : Fin (J + 2) → Bool) :
    (comb (J + 1) g).eval x =
      (if g 0 then (comb J (fun i => g i.succ)).eval (pref x) && x (Fin.last (J + 1))
       else (comb J (fun i => g i.succ)).eval (pref x) || x (Fin.last (J + 1))) := by
  rw [comb_succ_eq]
  split_ifs with hg
  · simp only [Formula.eval]; rw [Formula.eval_mapLeaf]; rfl
  · simp only [Formula.eval]; rw [Formula.eval_mapLeaf]; rfl

theorem combFalseInput_castSucc_apply {J : ℕ} (g : Fin (J + 1) → Bool)
    (j k : Fin (J + 1)) :
    combFalseInput (J + 1) g j.castSucc k.castSucc =
      combFalseInput J (fun i => g i.succ) j k := by
  unfold combFalseInput
  by_cases hlt : k.val < j.val
  · simp [Fin.val_castSucc, hlt]
  · by_cases heq : k.val = j.val
    · simp [Fin.val_castSucc, heq]
    · have hJ : 0 < J := by have := k.isLt; omega
      have hpg := parentGate_castSucc (J := J) hJ g k
      simp only [Fin.val_castSucc, hlt, heq, if_false]
      rw [hpg]

theorem combFalseInput_castSucc_last {J : ℕ} (g : Fin (J + 1) → Bool)
    (j : Fin (J + 1)) :
    combFalseInput (J + 1) g j.castSucc (Fin.last (J + 1)) = g 0 := by
  unfold combFalseInput
  have hl : ¬ ((Fin.last (J + 1) : Fin (J + 2)).val < j.castSucc.val) := by
    simp only [Fin.val_last, Fin.val_castSucc]; omega
  have he : ¬ ((Fin.last (J + 1) : Fin (J + 2)).val = j.castSucc.val) := by
    simp only [Fin.val_last, Fin.val_castSucc]; omega
  rw [if_neg hl, if_neg he, parentGate_last]
  rfl

theorem combFalseInput_last {J : ℕ} (g : Fin (J + 1) → Bool) (k : Fin (J + 2)) :
    combFalseInput (J + 1) g (Fin.last (J + 1)) k =
      if k = Fin.last (J + 1) then false else true := by
  unfold combFalseInput
  by_cases hk : k = Fin.last (J + 1)
  · subst hk; simp [Fin.val_last]
  · have hlt : k.val < J + 1 := by
      have hne : k.val ≠ J + 1 := by
        intro hv; exact hk (Fin.ext (by rw [hv, Fin.val_last]))
      have := k.isLt; omega
    simp [Fin.val_last, hlt, hk]

theorem inTF_castSucc {J : ℕ} (g : Fin (J + 1) → Bool) (j : Fin (J + 1)) :
    InTF (J + 1) g j.castSucc ↔ InTF J (fun i => g i.succ) j := by
  unfold InTF
  by_cases hj : j.val = 0
  · simp [Fin.val_castSucc, hj]
  · have hJ : 0 < J := by have := j.isLt; omega
    have hpg := parentGate_castSucc (J := J) hJ g j
    simp only [Fin.val_castSucc, hj]
    rw [hpg]

theorem inTF_last {J : ℕ} (g : Fin (J + 1) → Bool) :
    InTF (J + 1) g (Fin.last (J + 1)) ↔ g 0 = true := by
  unfold InTF
  rw [parentGate_last]
  simp [Fin.val_last]

theorem pref_update {J : ℕ} (x : Fin (J + 2) → Bool) (i : Fin (J + 1)) (b : Bool) :
    pref (Function.update x i.castSucc b) = Function.update (pref x) i b := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [pref, Function.update_self]
  · have hcast : k.castSucc ≠ i.castSucc := fun h => hk (Fin.castSucc_injective _ h)
    change Function.update x i.castSucc b k.castSucc = Function.update (pref x) i b k
    rw [Function.update_of_ne hcast b x, Function.update_of_ne hk b (pref x)]
    rfl

theorem update_castSucc_last {J : ℕ} (x : Fin (J + 2) → Bool) (i : Fin (J + 1)) (b : Bool) :
    Function.update x i.castSucc b (Fin.last (J + 1)) = x (Fin.last (J + 1)) :=
  Function.update_of_ne (Fin.castSucc_ne_last i).symm b x

theorem update_last_castSucc {J : ℕ} (x : Fin (J + 2) → Bool) (i : Fin (J + 1)) (b : Bool) :
    Function.update x (Fin.last (J + 1)) b i.castSucc = x i.castSucc :=
  Function.update_of_ne (Fin.castSucc_ne_last i) b x

theorem isMaximalFalse_or_root {J : ℕ} (ψ : Formula (J + 1)) (x : Fin (J + 2) → Bool) :
    (Formula.or (ψ.mapLeaf Fin.castSucc) (Formula.leaf (Fin.last (J + 1)))).IsMaximalFalse x ↔
      ψ.IsMaximalFalse (pref x) ∧ x (Fin.last (J + 1)) = false := by
  unfold Formula.IsMaximalFalse
  constructor
  · rintro ⟨hval, hmax⟩
    simp only [Formula.eval, Formula.eval_mapLeaf] at hval
    change (ψ.eval (pref x) || x (Fin.last (J + 1))) = false at hval
    rw [Bool.or_eq_false_iff] at hval
    obtain ⟨hsub, hlast⟩ := hval
    refine ⟨⟨hsub, ?_⟩, hlast⟩
    intro i hi
    have h := hmax i.castSucc hi
    simp only [Formula.eval, Formula.eval_mapLeaf] at h
    rw [update_castSucc_last, hlast, Bool.or_false] at h
    change ψ.eval (pref (Function.update x i.castSucc true)) = true at h
    rwa [pref_update] at h
  · rintro ⟨⟨hsub, hmax⟩, hlast⟩
    refine ⟨?_, ?_⟩
    · simp only [Formula.eval, Formula.eval_mapLeaf]
      change (ψ.eval (pref x) || x (Fin.last (J + 1))) = false
      rw [hsub, hlast]; rfl
    · intro k hk
      simp only [Formula.eval, Formula.eval_mapLeaf]
      rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
      · rw [update_castSucc_last, hlast, Bool.or_false]
        change ψ.eval (pref (Function.update x i.castSucc true)) = true
        rw [pref_update]
        exact hmax i hk
      · rw [Function.update_self]
        simp

theorem isMaximalFalse_and_root {J : ℕ} (ψ : Formula (J + 1)) (x : Fin (J + 2) → Bool) :
    (Formula.and (ψ.mapLeaf Fin.castSucc) (Formula.leaf (Fin.last (J + 1)))).IsMaximalFalse x ↔
      (x (Fin.last (J + 1)) = false ∧ ∀ i, pref x i = true) ∨
        (ψ.IsMaximalFalse (pref x) ∧ x (Fin.last (J + 1)) = true) := by
  unfold Formula.IsMaximalFalse
  constructor
  · rintro ⟨hval, hmax⟩
    simp only [Formula.eval, Formula.eval_mapLeaf] at hval
    change (ψ.eval (pref x) && x (Fin.last (J + 1))) = false at hval
    rw [Bool.and_eq_false_iff] at hval
    rcases hval with hsub | hlast
    · right
      have hlastT : x (Fin.last (J + 1)) = true := by
        by_contra hf
        have hf' : x (Fin.last (J + 1)) = false := by
          cases hx : x (Fin.last (J + 1)) <;> simp_all
        have h := hmax (Fin.last (J + 1)) hf'
        simp only [Formula.eval, Formula.eval_mapLeaf] at h
        rw [Function.update_self] at h
        rw [show (fun i : Fin (J + 1) =>
              Function.update x (Fin.last (J + 1)) true (Fin.castSucc i)) = pref x from by
          funext i; exact update_last_castSucc x i true] at h
        rw [hsub, Bool.false_and] at h
        exact absurd h (by simp)
      refine ⟨⟨hsub, ?_⟩, hlastT⟩
      intro i hi
      have h := hmax i.castSucc hi
      simp only [Formula.eval, Formula.eval_mapLeaf] at h
      rw [update_castSucc_last, hlastT, Bool.and_true] at h
      change ψ.eval (pref (Function.update x i.castSucc true)) = true at h
      rwa [pref_update] at h
    · left
      refine ⟨hlast, ?_⟩
      intro i
      by_contra hi
      have hi' : pref x i = false := by cases hh : pref x i <;> simp_all
      have h := hmax i.castSucc hi'
      simp only [Formula.eval, Formula.eval_mapLeaf] at h
      rw [update_castSucc_last, hlast, Bool.and_false] at h
      exact absurd h (by simp)
  · rintro (⟨hlast, hall⟩ | ⟨⟨hsub, hmax⟩, hlast⟩)
    · refine ⟨?_, ?_⟩
      · simp only [Formula.eval, Formula.eval_mapLeaf]
        change (ψ.eval (pref x) && x (Fin.last (J + 1))) = false
        rw [show pref x = (fun _ => true) from funext (fun i => hall i)]
        rw [Formula.eval_allTrue, hlast, Bool.true_and]
      · intro k hk
        simp only [Formula.eval, Formula.eval_mapLeaf]
        rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
        · exact absurd (hall i) (by simp [pref, hk])
        · rw [Function.update_self]
          rw [show (fun i : Fin (J + 1) =>
                Function.update x (Fin.last (J + 1)) true (Fin.castSucc i)) = pref x from by
            funext i; exact update_last_castSucc x i true]
          rw [show pref x = (fun _ => true) from funext (fun i => hall i)]
          rw [Formula.eval_allTrue, Bool.true_and]
    · refine ⟨?_, ?_⟩
      · simp only [Formula.eval, Formula.eval_mapLeaf]
        change (ψ.eval (pref x) && x (Fin.last (J + 1))) = false
        rw [hsub, hlast, Bool.false_and]
      · intro k hk
        simp only [Formula.eval, Formula.eval_mapLeaf]
        rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
        · rw [update_castSucc_last, hlast, Bool.and_true]
          change ψ.eval (pref (Function.update x i.castSucc true)) = true
          rw [pref_update]
          exact hmax i hk
        · rw [hlast] at hk
          exact absurd hk (by simp)

theorem comb_false_input_iff (J : ℕ) (g : Fin J → Bool) (j : Fin (J + 1))
    (hj : InTF J g j) :
    (comb J g).IsMaximalFalse (combFalseInput J g j) := by
  induction J with
  | zero =>
      have hk : j = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (by omega)
      subst hk
      have hx : combFalseInput 0 g ⟨0, Nat.succ_pos 0⟩ = (fun _ => false) := by
        funext i
        have hi : i = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (by omega)
        subst hi
        simp [combFalseInput]
      rw [hx]
      refine ⟨?_, ?_⟩
      · simp [comb, Formula.eval]
      · intro i hi
        have hi0 : i = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (by omega)
        subst hi0
        simp [comb, Formula.eval, Function.update]
  | succ J ih =>
      by_cases hg : g 0 = true
      · rw [comb_succ_eq, if_pos hg, isMaximalFalse_and_root]
        by_cases hjlast : j = Fin.last (J + 1)
        · subst hjlast
          left
          refine ⟨by rw [combFalseInput_last]; simp, ?_⟩
          intro i
          show combFalseInput (J + 1) g (Fin.last (J + 1)) i.castSucc = true
          rw [combFalseInput_last]
          simp [Fin.castSucc_ne_last]
        · obtain ⟨j', rfl⟩ := (Fin.eq_castSucc_or_eq_last j).resolve_right hjlast
          have hsub : InTF J (fun i => g i.succ) j' := (inTF_castSucc g j').mp hj
          right
          refine ⟨?_, by rw [combFalseInput_castSucc_last]; exact hg⟩
          rw [show pref (combFalseInput (J + 1) g j'.castSucc) =
              combFalseInput J (fun i => g i.succ) j' from by
            funext i; exact combFalseInput_castSucc_apply g j' i]
          exact ih (fun i => g i.succ) j' hsub
      · have hgf : g 0 = false := by cases h : g 0 <;> simp_all
        rw [comb_succ_eq, if_neg hg, isMaximalFalse_or_root]
        have hjNotLast : j ≠ Fin.last (J + 1) := by
          intro h; subst h; exact hg ((inTF_last g).mp hj)
        obtain ⟨j', rfl⟩ := (Fin.eq_castSucc_or_eq_last j).resolve_right hjNotLast
        have hsub : InTF J (fun i => g i.succ) j' := (inTF_castSucc g j').mp hj
        refine ⟨?_, by rw [combFalseInput_castSucc_last]; exact hgf⟩
        rw [show pref (combFalseInput (J + 1) g j'.castSucc) =
            combFalseInput J (fun i => g i.succ) j' from by
          funext i; exact combFalseInput_castSucc_apply g j' i]
        exact ih (fun i => g i.succ) j' hsub

theorem comb_maximal_false_iff (J : ℕ) (g : Fin J → Bool) (x : Fin (J + 1) → Bool) :
    (comb J g).IsMaximalFalse x ↔
      ∃ j : Fin (J + 1), InTF J g j ∧ x = combFalseInput J g j := by
  induction J with
  | zero =>
      constructor
      · intro hx
        refine ⟨⟨0, Nat.succ_pos 0⟩, by unfold InTF; simp, ?_⟩
        funext i
        have hi : i = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (by omega)
        subst hi
        have h := hx.1
        simp [comb, Formula.eval] at h
        simpa [combFalseInput] using h
      · rintro ⟨j, _, rfl⟩
        exact comb_false_input_iff 0 g j (by unfold InTF; simp)
  | succ J ih =>
      by_cases hg : g 0 = true
      · rw [comb_succ_eq, if_pos hg, isMaximalFalse_and_root]
        constructor
        · rintro (⟨hlast, hall⟩ | ⟨hsub, hlast⟩)
          · refine ⟨Fin.last (J + 1), (inTF_last g).mpr hg, ?_⟩
            funext k
            rw [combFalseInput_last]
            by_cases hk : k = Fin.last (J + 1)
            · subst hk; simp [hlast]
            · rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
              · simp only [if_neg (Fin.castSucc_ne_last i)]
                exact hall i
              · exact absurd rfl hk
          · obtain ⟨j', hj'TF, hj'x⟩ :=
              (ih (fun i => g i.succ) (pref x)).mp hsub
            refine ⟨j'.castSucc, (inTF_castSucc g j').mpr hj'TF, ?_⟩
            funext k
            rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
            · rw [combFalseInput_castSucc_apply]; exact congrFun hj'x i
            · rw [combFalseInput_castSucc_last, hlast]; exact hg.symm
        · rintro ⟨j, hjTF, rfl⟩
          have h := comb_false_input_iff (J + 1) g j hjTF
          rw [comb_succ_eq, if_pos hg] at h
          exact (isMaximalFalse_and_root (comb J (fun i => g i.succ))
            (combFalseInput (J + 1) g j)).mp h
      · have hgf : g 0 = false := by cases h : g 0 <;> simp_all
        rw [comb_succ_eq, if_neg hg, isMaximalFalse_or_root]
        constructor
        · rintro ⟨hsub, hlast⟩
          obtain ⟨j', hj'TF, hj'x⟩ := (ih (fun i => g i.succ) (pref x)).mp hsub
          refine ⟨j'.castSucc, (inTF_castSucc g j').mpr hj'TF, ?_⟩
          funext k
          rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
          · rw [combFalseInput_castSucc_apply]; exact congrFun hj'x i
          · rw [combFalseInput_castSucc_last, hlast]; exact hgf.symm
        · rintro ⟨j, hjTF, rfl⟩
          have h := comb_false_input_iff (J + 1) g j hjTF
          rw [comb_succ_eq, if_neg hg] at h
          exact (isMaximalFalse_or_root (comb J (fun i => g i.succ))
            (combFalseInput (J + 1) g j)).mp h

theorem comb_false_input_injective (J : ℕ) (g : Fin J → Bool) {j j' : Fin (J + 1)}
    (h : combFalseInput J g j = combFalseInput J g j') : j = j' := by
  rcases lt_trichotomy j.val j'.val with hlt | heq | hgt
  · have h1 : combFalseInput J g j j = false := by simp [combFalseInput]
    have h2 : combFalseInput J g j' j = true := by
      unfold combFalseInput; rw [if_pos hlt]
    have := congrFun h j
    rw [h1, h2] at this
    exact absurd this (by simp)
  · exact Fin.ext heq
  · have h1 : combFalseInput J g j' j' = false := by simp [combFalseInput]
    have h2 : combFalseInput J g j j' = true := by
      unfold combFalseInput; rw [if_pos hgt]
    have := congrFun h j'
    rw [h1, h2] at this
    exact absurd this (by simp)

theorem comb_maximal_false_bijection (J : ℕ) (g : Fin J → Bool) :
    (∀ j, InTF J g j → (comb J g).IsMaximalFalse (combFalseInput J g j)) ∧
      (∀ x, (comb J g).IsMaximalFalse x →
        ∃ j, InTF J g j ∧ x = combFalseInput J g j) ∧
      (∀ j j', InTF J g j → InTF J g j' →
        combFalseInput J g j = combFalseInput J g j' → j = j') :=
  ⟨fun j hj => comb_false_input_iff J g j hj,
   fun x hx => (comb_maximal_false_iff J g x).mp hx,
   fun j j' _ _ h => comb_false_input_injective J g h⟩

theorem comb_witness (J : ℕ) (g : Fin J → Bool) :
    ∀ u : (comb J g).MaxFalse,
      SpanProgram.NegWitness (Pphi (comb J g) (combPath J)) u.val
        (fun v => if v = u then 1 / (Pphi (comb J g) (combPath J)).target u else 0) := by
  have hγ : IsLeafPath (comb J g) (combPath J) := fun k => comb_nodeAt J g k
  exact (source_lemma_3_6 (comb J g) (combPath J) hγ).2

end Qatlib.Papers.GameTree09.MainResults
