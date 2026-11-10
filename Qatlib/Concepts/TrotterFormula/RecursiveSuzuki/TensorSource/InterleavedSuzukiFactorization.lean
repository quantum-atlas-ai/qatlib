/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiConsumers
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization
open Matrix Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical BigOperators Matrix.Norms.L2Operator

abbrev LocalMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev RegisterMatrix (N : ℕ) := Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ

def slot {N : ℕ} (j : Fin N) (A : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.RegisterMatrix N :=
  Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun i => if i = j then A else 1)

theorem slot_apply {N : ℕ} (j : Fin N) (A : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix)
    (x y : Fin N → Fin 2) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A x y = A (x j) (y j) *
      ∏ i ∈ Finset.univ.erase j, (1 : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (x i) (y i) := by
  unfold Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_erase] at hi
  simp [hi.1]

theorem slot_add {N : ℕ} (j : Fin N) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A+B) = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A + Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j B := by
  ext x y
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_apply, Matrix.add_apply, add_mul]

theorem slot_zero {N : ℕ} (j : Fin N) : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (0 : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) = 0 := by
  ext x y
  simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_apply]

theorem slot_smul {N : ℕ} (j : Fin N) (a : ℝ) (A : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (a • A) = a • Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A := by
  ext x y
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_apply, Matrix.smul_apply, smul_mul_assoc]

theorem slot_one {N : ℕ} (j : Fin N) : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (1 : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) = 1 := by
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot,
      ite_self, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_one]

theorem slot_mul {N : ℕ} (j : Fin N) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A*B) = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A * Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j B := by
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot,
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_mul]
  congr 1
  funext i
  split_ifs <;> simp

def slotHom {N : ℕ} (j : Fin N) : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix →+* Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.RegisterMatrix N where
  toFun := Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j
  map_zero' := Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_zero j
  map_one' := Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_one j
  map_add' := Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_add j
  map_mul' := Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_mul j

set_option backward.isDefEq.respectTransparency false in

theorem slot_exp {N : ℕ} (j : Fin N) (A : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    NormedSpace.exp (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A) = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (NormedSpace.exp A) := by
  have hc : Continuous (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slotHom j) := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    change Continuous
        (fun A : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix => Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A x y)
    simp_rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_apply]
    fun_prop
  open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slotHom j) hc A).symm

theorem slot_commute {N : ℕ} (j k : Fin N) (hjk : j ≠ k)
    (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) : Commute (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A) (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot k B) := by
  change Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A * Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot k B = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot k B * Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot,
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_mul]
  congr 1
  funext i
  by_cases hij : i = j
  · subst i
    simp [hjk]
  · by_cases hik : i = k
    · subst i
      simp [hij]
    · simp [hij, hik]

abbrev Tagged (N : ℕ) :=
    Fin N × Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix

def pick {N : ℕ} (i : Fin N) : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N) → List Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix
  | [] => []
  | (j,A)::xs => if j = i then A :: Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs else Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs

theorem pick_append {N : ℕ} (i : Fin N) (xs ys : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i (xs++ys) = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs ++ Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨j,A⟩
    by_cases h : j = i <;> simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick, h, ih]

theorem pick_reverse {N : ℕ} (i : Fin N) (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs.reverse = (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨j,A⟩
    by_cases h : j = i <;> simp [List.reverse_cons, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_append, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick, h, ih]

def tagScale {N : ℕ} (a : ℝ) (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N) :=
  xs.map (fun x => (x.1, a • x.2))

theorem pick_scale {N : ℕ} (i : Fin N) (a : ℝ) (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale a xs) = (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs).map (fun A => a • A) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨j,A⟩
    simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale] at ih
    by_cases h : j = i <;> simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick, h, ih]

def taggedSuzuki {N : ℕ} (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) : ℕ → List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)
  | 0 => Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale (1/2) xs ++ Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale (1/2) xs.reverse
  | k+1 =>
    let a :=
        Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale
        (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiScale k)
        (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki xs k)
    let b :=
        Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale
        (1-4*Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiScale k)
        (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki xs k)
    a ++ a ++ b ++ a ++ a

theorem pick_taggedSuzuki {N : ℕ} (i : Fin N) (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) (k : ℕ) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki xs k) = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs) k := by
  induction k with
  | zero => simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_append, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_scale, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_reverse,
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators]
  | succ k ih => simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_append, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_scale, ih,
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators]

def liftTags {N : ℕ} (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.RegisterMatrix N) :=
  xs.map (fun x => Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot x.1 x.2)

theorem liftTags_scale {N : ℕ} (a : ℝ) (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale a xs) = (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags xs).map (fun A => a • A) := by
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagScale, List.map_map, Function.comp_def, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_smul]

theorem liftTags_taggedSuzuki {N : ℕ} (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) (k : ℕ) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki xs k) = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags xs) k := by
  have ha (as bs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) :
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags (as++bs) = Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags as ++ Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags bs := List.map_append
  have hr (as : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) :
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags as.reverse = (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags as).reverse := List.map_reverse
  induction k with
  | zero => simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki, ha, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags_scale, hr, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators]
  | succ k ih => simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.taggedSuzuki, ha, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags_scale, ih, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators]

theorem tagged_exp_product {N : ℕ} (xs : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N)) (t : ℝ) :
    ((Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags xs).map (fun A => NormedSpace.exp (t • A))).prod =
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun i => ((Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i xs).map (fun A => NormedSpace.exp (t • A))).prod) := by
  induction xs with
  | nil => simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_one]
  | cons x xs ih =>
    rcases x with ⟨j,A⟩
    change NormedSpace.exp (t • Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A) *
      ((Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags xs).map (fun B => NormedSpace.exp (t • B))).prod = _
    rw [← Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_smul,
        Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_exp, ih]
    simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot,
        Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_mul]
    congr 1
    funext i
    by_cases h : j = i
    · subst i
      simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick]
    · simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick, h,
        Ne.symm h]

def interleavedTags (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.Tagged N) :=
  (List.finRange N).flatMap (fun j => [(j,A),(j,B)])

def interleaved (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) : List (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.RegisterMatrix N) :=
  Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleavedTags N A B)

theorem pick_blocks {N : ℕ} (i : Fin N) (js : List (Fin N))
    (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (hj : js.Nodup) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i (js.flatMap (fun j => [(j,A),(j,B)])) =
      if i ∈ js then [A,B] else [] := by
  induction js with
  | nil => simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick]
  | cons j js ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hj
    by_cases h : j = i
    · subst j
      simp [List.flatMap_cons,
          Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick, ih htail, hnot]
    · simp [List.flatMap_cons,
        Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick, ih htail, h, Ne.symm h]

theorem pick_interleaved {N : ℕ} (i : Fin N) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick i (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleavedTags N A B) = [A,B] := by
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleavedTags, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_blocks i _ A B (List.nodup_finRange N)]
  simp

theorem interleaved_segment (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (k : ℕ) (t : ℝ) :
    ((Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B) k).map
      (fun X => NormedSpace.exp (t • X))).prod =
    Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => ((Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators [A,B] k).map
      (fun X => NormedSpace.exp (t • X))).prod) := by
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved,
      ← Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags_taggedSuzuki, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.tagged_exp_product]
  congr 1
  funext i
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_taggedSuzuki, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.pick_interleaved]

theorem productMatrix_pow (N : ℕ) (A : Fin N → Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (r : ℕ) :
    Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix A ^ r = Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun i => A i ^ r) := by
  induction r with
  | zero => simp only [pow_zero, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_one]
  | succ r ih => rw [pow_succ, ih, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_mul]; rfl

theorem interleaved_word (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (k : ℕ) (t : ℝ) (r : ℕ) :
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B) k t r).prod =
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord [A,B] k t r).prod) := by
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord, List.prod_flatten,
      List.map_replicate, List.prod_replicate]
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved_segment, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.productMatrix_pow]

theorem exp_sum_slots (N : ℕ) (A : Fin N → Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (s : Finset (Fin N)) :
    NormedSpace.exp (∑ j ∈ s, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A j)) =
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun i => if i ∈ s then NormedSpace.exp (A i) else 1) := by
  induction s using Finset.induction_on with
  | empty => simp [Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_one]
  | @insert j s hj ih =>
    have hc : Commute (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A j)) (∑ k ∈ s, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot k (A k)) := by
      change Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A j) * (∑ k ∈ s, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot k (A k)) =
        (∑ k ∈ s, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot k (A k)) * Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A j)
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      exact Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_commute j k (by intro h; subst k; exact hj hk) (A j) (A k)
    rw [Finset.sum_insert hj, Matrix.exp_add_of_commute _ _ hc,
        Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_exp, ih]
    simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot,
        Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_mul]
    congr 1
    funext i
    by_cases hi : i = j
    · subst i
      simp [hj]
    · simp [hi]

theorem interleaved_sum (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B).sum = ∑ j : Fin N, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A+B) := by
  have hs (js : List (Fin N)) :
      (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags (js.flatMap (fun j => [(j,A),(j,B)]))).sum =
        (js.map (fun j => Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j (A+B))).sum := by
    induction js with
    | nil => simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags]
    | cons j js ih =>
      simpa [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_add, add_assoc] using!
        congrArg (fun C => Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j A + (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot j B + C)) ih
  simpa [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleavedTags, List.finRange, List.map_ofFn, List.sum_ofFn]
    using! hs (List.finRange N)

theorem interleaved_ideal (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (t : ℝ) :
    NormedSpace.exp (t • (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B).sum) =
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => NormedSpace.exp (t • (A+B))) := by
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved_sum, Finset.smul_sum]
  simp_rw [← Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_smul]
  simpa using!
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.exp_sum_slots N
      (fun _ => t • (A+B)) Finset.univ

theorem interleaved_length (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B).length = 2*N := by
  simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleavedTags, List.length_flatMap,
    List.map_const', Nat.mul_comm]

theorem interleaved_word_length (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (k : ℕ) (t : ℝ) (r : ℕ) :
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B) k t r).length = r*(4*N*5^k) := by
  have hl :=
      (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursive_suzuki_length_and_mass _ (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B) k).1
  simp only [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord, List.length_flatten, List.map_replicate,
    List.sum_replicate, List.length_map, hl, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved_length, smul_eq_mul]
  ring

theorem interleaved_fourth_order_visits (N : ℕ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) (t : ℝ) (r : ℕ) :
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B) 1 t r).length = 20*N*r := by
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved_word_length]
  ring

theorem interleaved_smul (N : ℕ) (a : ℝ) (A B : Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.LocalMatrix) :
    Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N (a • A) (a • B) = (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved N A B).map (fun X => a • X) := by
  simp [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleaved,
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.liftTags, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.interleavedTags, List.map_flatMap, Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization.slot_smul]

end Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.InterleavedSuzukiFactorization
