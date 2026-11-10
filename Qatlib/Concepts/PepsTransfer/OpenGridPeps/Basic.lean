/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.PepsTransfer.OpenGridPeps.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.PepsTransfer.OpenGridPeps
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem amplitude_single (d D : ℕ) (hD : 0 < D) (A : Tensor 1 1 d D)
    (x : Fin 1 → Fin 1 → Fin d) :
    amplitude hD A x = A 0 0 (x 0 0) ⟨0,hD⟩ ⟨0,hD⟩ ⟨0,hD⟩ ⟨0,hD⟩ := by
  simp [amplitude, value]

theorem amplitude_empty (a b d D : ℕ) (hD : 0 < D) (A : Tensor a b d D)
    (x : Fin a → Fin b → Fin d) (h : a = 0 ∨ b = 0) : amplitude hD A x = 1 := by
  rcases h with rfl | rfl <;> simp [amplitude]

private theorem delta_horizontal_zero {a b d D : ℕ} (hD : 0 < D)
    (t : Fin a → Fin b → Fin d → ℂ) (x : Fin a → Fin b → Fin d)
    (h : Fin a × Fin (b-1) → Fin D) (v : Fin (a-1) × Fin b → Fin D)
    (hh : h ≠ fun _ => ⟨0,hD⟩) :
    (∏ i, ∏ j, value hD
      (fun i j s u v l r => if u.val=0 ∧ v.val=0 ∧ l.val=0 ∧ r.val=0
        then t i j s else 0) x h v i j) = 0 := by
  obtain ⟨⟨i,k⟩, hk⟩ := Function.ne_iff.mp hh
  have hb : k.val < b := by omega
  let j : Fin b := ⟨k.val,hb⟩
  have hj : j.val+1 < b := by dsimp [j]; omega
  have hn : (h (i,k)).val ≠ 0 := by
    intro he
    apply hk
    exact Fin.ext he
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  have he : (⟨j.val, by omega⟩ : Fin (b-1)) = k := Fin.ext rfl
  simp only [value, dif_pos hj, he]
  exact if_neg (fun hp => hn hp.2.2.2)

private theorem delta_vertical_zero {a b d D : ℕ} (hD : 0 < D)
    (t : Fin a → Fin b → Fin d → ℂ) (x : Fin a → Fin b → Fin d)
    (h : Fin a × Fin (b-1) → Fin D) (v : Fin (a-1) × Fin b → Fin D)
    (hv : v ≠ fun _ => ⟨0,hD⟩) :
    (∏ i, ∏ j, value hD
      (fun i j s u v l r => if u.val=0 ∧ v.val=0 ∧ l.val=0 ∧ r.val=0
        then t i j s else 0) x h v i j) = 0 := by
  obtain ⟨⟨k,j⟩, hk⟩ := Function.ne_iff.mp hv
  have ha : k.val < a := by omega
  let i : Fin a := ⟨k.val,ha⟩
  have hi : i.val+1 < a := by dsimp [i]; omega
  have hn : (v (k,j)).val ≠ 0 := by
    intro he
    apply hk
    exact Fin.ext he
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  have he : (⟨i.val, by omega⟩ : Fin (a-1)) = k := Fin.ext rfl
  simp only [value, dif_pos hi, he]
  exact if_neg (fun hp => hn hp.2.1)

theorem amplitude_product (a b d D : ℕ) (hD : 0 < D)
    (t : Fin a → Fin b → Fin d → ℂ) (x : Fin a → Fin b → Fin d) :
    amplitude hD (fun i j s u v l r =>
      if u.val=0 ∧ v.val=0 ∧ l.val=0 ∧ r.val=0 then t i j s else 0) x =
        ∏ i, ∏ j, t i j (x i j) := by
  unfold amplitude
  rw [Finset.sum_eq_single (fun _ => ⟨0,hD⟩)]
  · rw [Finset.sum_eq_single (fun _ => ⟨0,hD⟩)]
    · apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      simp [value]
    · intro v _ hv
      exact delta_vertical_zero hD t x _ v hv
    · intro hv
      exact (hv (Finset.mem_univ _)).elim
  · intro h _ hh
    apply Finset.sum_eq_zero
    intro v _
    exact delta_horizontal_zero hD t x h v hh
  · intro hh
    exact (hh (Finset.mem_univ _)).elim

theorem g1 :
    (∀ (d D : ℕ) (hD : 0<D) (A : Tensor 1 1 d D) (x : Fin 1→Fin 1→Fin d),
      amplitude hD A x = A 0 0 (x 0 0) ⟨0,hD⟩ ⟨0,hD⟩ ⟨0,hD⟩ ⟨0,hD⟩) ∧
    (∀ (a b d D : ℕ) (hD : 0<D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d),
      a=0 ∨ b=0 → amplitude hD A x=1) ∧
    (∀ (a b d D : ℕ) (hD : 0<D) (t : Fin a→Fin b→Fin d→ℂ) (x : Fin a→Fin b→Fin d),
      amplitude hD (fun i j s u v l r =>
        if u.val=0 ∧ v.val=0 ∧ l.val=0 ∧ r.val=0 then t i j s else 0) x =
          ∏ i, ∏ j, t i j (x i j)) :=
  ⟨amplitude_single, amplitude_empty, amplitude_product⟩

theorem matrix_product_paths {S : Type*} [Fintype S] [DecidableEq S]
    (n : ℕ) (M : Fin (n+1) → Matrix S S ℂ) (u w : S) :
    (List.ofFn M).prod u w =
      ∑ v : Fin n → S, ∏ i : Fin (n+1), M i (Fin.cons (α := fun _ => S) u v i) (Fin.snoc (α := fun _ => S) v w i) := by
  induction n generalizing u w with
  | zero => simp [List.ofFn_succ, Fin.snoc_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    calc
      (∑ t, M 0 u t * (List.ofFn (fun i => M i.succ)).prod t w) =
          ∑ t, ∑ v : Fin n → S,
            M 0 u t * ∏ i : Fin (n+1), M i.succ (Fin.cons (α := fun _ => S) t v i) (Fin.snoc (α := fun _ => S) v w i) := by
        simp_rw [ih, Finset.mul_sum]
      _ = ∑ v : Fin (n+1) → S,
          ∏ i : Fin (n+2), M i (Fin.cons (α := fun _ => S) u v i) (Fin.snoc (α := fun _ => S) v w i) := by
        rw [← (Fin.consEquiv (fun _ : Fin (n+1) => S)).sum_comp]
        simp only [Fintype.sum_prod_type, Fin.consEquiv]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro v _
        dsimp only [Equiv.coe_fn_mk]
        symm
        rw [← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ]
        simp

private theorem value_curried {n b d D : ℕ} (hD : 0 < D)
    (A : Tensor (n+1) b d D) (x : Fin (n+1) → Fin b → Fin d)
    (H : Fin (n+1) → Fin (b-1) → Fin D) (V : Fin n → Fin b → Fin D)
    (i : Fin (n+1)) (j : Fin b) :
    value hD A x (Function.uncurry H) (Function.uncurry V) i j =
      A i j (x i j) (Fin.cons (α := fun _ => Fin b → Fin D) (fun _ => ⟨0,hD⟩) V i j)
        (Fin.snoc (α := fun _ => Fin b → Fin D) V (fun _ => ⟨0,hD⟩) i j)
        (if hj : 0 < j.val then H i ⟨j.val-1,by omega⟩ else ⟨0,hD⟩)
        (if hj : j.val+1 < b then H i ⟨j.val,by omega⟩ else ⟨0,hD⟩) := by
  have hu : (if hi : 0 < i.val then V ⟨i.val-1,by omega⟩ j else ⟨0,hD⟩) =
      Fin.cons (α := fun _ => Fin b → Fin D) (fun _ => ⟨0,hD⟩) V i j := by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp
  have hd : (if hi : i.val+1 < n+1 then V ⟨i.val,by omega⟩ j else ⟨0,hD⟩) =
      Fin.snoc (α := fun _ => Fin b → Fin D) V (fun _ => ⟨0,hD⟩) i j := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp
    · simp [show k.val+1 < n+1 by omega]
  dsimp only [value, Function.uncurry]
  rw [← hu, ← hd]
  try (split_ifs <;> rfl)

theorem amplitude_rows {n b d D : ℕ} (hD : 0 < D)
    (A : Tensor (n+1) b d D) (x : Fin (n+1) → Fin b → Fin d) :
    amplitude hD A x =
      ∑ V : Fin n → (Fin b → Fin D), ∏ i : Fin (n+1),
        rowMatrix hD A x i (Fin.cons (α := fun _ => Fin b → Fin D) (fun _ => ⟨0,hD⟩) V i)
          (Fin.snoc (α := fun _ => Fin b → Fin D) V (fun _ => ⟨0,hD⟩) i) := by
  unfold amplitude
  rw [Finset.sum_comm]
  calc
    (∑ v : Fin n × Fin b → Fin D,
      ∑ h : Fin (n+1) × Fin (b-1) → Fin D, ∏ i, ∏ j, value hD A x h v i j) =
        ∑ V : Fin n → Fin b → Fin D,
          ∑ H : Fin (n+1) → Fin (b-1) → Fin D,
            ∏ i, ∏ j, value hD A x (Function.uncurry H) (Function.uncurry V) i j := by
      rw [← (Equiv.curry (Fin n) (Fin b) (Fin D)).symm.sum_comp]
      apply Finset.sum_congr rfl
      intro V _
      exact ((Equiv.curry (Fin (n+1)) (Fin (b-1)) (Fin D)).symm.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro V _
      simp_rw [value_curried]
      exact (Fintype.prod_sum (fun (i : Fin (n+1)) (h : Fin (b-1) → Fin D) => ∏ j : Fin b,
        A i j (x i j) (Fin.cons (α := fun _ => Fin b → Fin D) (fun _ => ⟨0,hD⟩) V i j)
          (Fin.snoc (α := fun _ => Fin b → Fin D) V (fun _ => ⟨0,hD⟩) i j)
          (if hj : 0 < j.val then h ⟨j.val-1,by omega⟩ else ⟨0,hD⟩)
          (if hj : j.val+1 < b then h ⟨j.val,by omega⟩ else ⟨0,hD⟩))).symm

theorem g2 :
    ∀ (a b d D : ℕ) (hD : 0<D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d),
      rowAmplitude hD A x = amplitude hD A x ∧
        Fintype.card (Fin b→Fin D) = D^b := by
  intro a b d D hD A x
  constructor
  · cases a with
    | zero => simp [rowAmplitude, amplitude]
    | succ n =>
      rw [rowAmplitude, matrix_product_paths, amplitude_rows]
  · simp

end Qatlib.Concepts.PepsTransfer.OpenGridPeps
