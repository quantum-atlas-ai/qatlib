/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Qatlib.Concepts.DyadicProgram.DyadicContract.DyadicMpsProgramDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.DyadicProgram.DyadicContract
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

private def enc (z : GI) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

private theorem decode_eq (p : ℕ) (z : GI) : decode p z = enc z / (2:ℂ)^p := rfl

private theorem enc_add (x y : GI) : enc (add x y) = enc x + enc y := by
  simp only [enc, add, Int.cast_add]
  ring

private theorem enc_mul (x y : GI) : enc (mul x y) = enc x * enc y := by
  simp only [enc, mul, Int.cast_add, Int.cast_sub, Int.cast_mul]
  linear_combination -((x.2 : ℂ) * (y.2 : ℂ)) * Complex.I_sq

private theorem enc_fold (xs : List GI) (z : GI) :
    enc (xs.foldl add z) = enc z + (xs.map enc).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih, enc_add, add_assoc]

private theorem decode_row {D : ℕ} (q p : ℕ) (v : Fin D → GI)
    (A : Matrix (Fin D) (Fin D) GI) :
    (fun j => decode (q+p) (row v A j)) =
      (fun j => decode q (v j)) ᵥ* (fun i j => decode p (A i j)) := by
  funext j
  simp only [decode_eq, row, dot]
  rw [enc_fold]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, enc_mul]
  simp only [enc, Int.cast_zero, zero_mul, add_zero, zero_add, pow_add,
    Matrix.vecMul, dotProduct]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem decode_initial {D : ℕ} (hD : 0 < D) :
    (fun j => decode 0 (initial D j)) = (1 : Matrix (Fin D) (Fin D) ℂ) ⟨0,hD⟩ := by
  funext j
  by_cases hj : j.val = 0 <;>
    simp [decode, initial, hj, Matrix.one_apply, Fin.ext_iff, eq_comm]

noncomputable def standardMatrixWord {D : ℕ} (p : ℕ)
    (As : List (Matrix (Fin D) (Fin D) GI)) : Matrix (Fin D) (Fin D) ℂ :=
  List.prod (α := Matrix (Fin D) (Fin D) ℂ) (As.map fun A i j => decode p (A i j))

private theorem decode_fold {D : ℕ} (p q : ℕ)
    (As : List (Matrix (Fin D) (Fin D) GI)) (v : Fin D → GI) :
    (fun j => decode (q+p*As.length) (As.foldl row v j)) =
      (fun j => decode q (v j)) ᵥ* standardMatrixWord p As := by
  induction As generalizing q v with
  | nil => simp [standardMatrixWord, Matrix.vecMul_one]
  | cons A As ih =>
    simp only [List.foldl_cons, List.length_cons, standardMatrixWord, List.map_cons, List.prod_cons]
    rw [show q+p*(As.length+1) = (q+p)+p*As.length by ring]
    rw [ih, decode_row, Matrix.vecMul_vecMul]
    rfl

theorem decode_standard_scalar : ∀ (D p : ℕ) (hD : 0<D) (As : List (Matrix (Fin D) (Fin D) GI)),
    decode (p*As.length) (scalar hD As)=standardMatrixWord p As ⟨0,hD⟩ ⟨0,hD⟩ ∧
    scalar hD []=(1,0) := by
  intro D p hD As
  constructor
  · have h := decode_fold p 0 As (initial D)
    rw [decode_initial hD] at h
    simpa [scalar, run, Matrix.vecMul, dotProduct, Matrix.one_apply] using congrFun h ⟨0,hD⟩
  · simp [scalar, run, initial]

private theorem dot_count_fold (xs : List (GI × GI)) (s : Counted GI) :
    let t := xs.foldl (fun s xy =>
      (⟨add s.value (mul xy.1 xy.2), s.muls+4, s.adds+4⟩ : Counted GI)) s
    t.value = (xs.map fun xy => mul xy.1 xy.2).foldl add s.value ∧
    t.muls = s.muls+4*xs.length ∧ t.adds = s.adds+4*xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simpa [List.foldl_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (⟨add s.value (mul x.1 x.2), s.muls+4, s.adds+4⟩ : Counted GI)

private theorem dot_count {D : ℕ} (v : Fin D → GI)
    (A : Matrix (Fin D) (Fin D) GI) (j : Fin D) :
    (dotCounted v A j).value = dot v A j ∧
    (dotCounted v A j).muls = 4*D ∧ (dotCounted v A j).adds = 4*D := by
  simpa [dotCounted, dot, List.map_ofFn] using!
    dot_count_fold (List.ofFn fun i : Fin D => (v i,A i j)) ⟨(0,0),0,0⟩

private theorem row_count {D : ℕ} (v : Fin D → GI)
    (A : Matrix (Fin D) (Fin D) GI) :
    (rowCounted v A).value = row v A ∧
    (rowCounted v A).muls = 4*D^2 ∧ (rowCounted v A).adds = 4*D^2 := by
  constructor
  · funext j
    simpa [rowCounted, row] using (dot_count v A j).1
  · constructor
    · simp [rowCounted, List.map_ofFn, List.sum_ofFn, (dot_count v A _).2.1]
      ring
    · simp [rowCounted, List.map_ofFn, List.sum_ofFn, (dot_count v A _).2.2]
      ring

private theorem run_count_fold {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI))
    (s : Counted (Fin D → GI)) :
    let t := As.foldl (fun s A => let t := rowCounted s.value A
      (⟨t.value,s.muls+t.muls,s.adds+t.adds⟩ : Counted (Fin D → GI))) s
    t.value = As.foldl row s.value ∧
    t.muls = s.muls+4*As.length*D^2 ∧ t.adds = s.adds+4*As.length*D^2 := by
  induction As generalizing s with
  | nil => simp
  | cons A As ih =>
    obtain ⟨hv,hm,ha⟩ := row_count s.value A
    simpa only [List.foldl_cons, List.length_cons, hv, hm, ha, Nat.mul_add,
      Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (⟨(rowCounted s.value A).value,s.muls+(rowCounted s.value A).muls,
        s.adds+(rowCounted s.value A).adds⟩ : Counted (Fin D → GI))

theorem g2 : ∀ (D : ℕ) (As : List (Matrix (Fin D) (Fin D) GI)),
    (runCounted As).value=run As ∧
    (runCounted As).muls=4*As.length*D^2 ∧ (runCounted As).adds=4*As.length*D^2 := by
  intro D As
  simpa [runCounted, run] using run_count_fold As ⟨initial D,0,0⟩

private def Bounded (B : ℕ) (z : GI) : Prop := z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B

private theorem bound_add {B C : ℕ} {x y : GI} (hx : Bounded B x) (hy : Bounded C y) :
    Bounded (B+C) (add x y) := by
  exact ⟨(Int.natAbs_add_le _ _).trans (Nat.add_le_add hx.1 hy.1),
    (Int.natAbs_add_le _ _).trans (Nat.add_le_add hx.2 hy.2)⟩

private theorem bound_mul {B C : ℕ} {x y : GI} (hx : Bounded B x) (hy : Bounded C y) :
    Bounded (2*B*C) (mul x y) := by
  constructor
  · exact (Int.natAbs_sub_le _ _).trans (by
      simp only [Int.natAbs_mul]
      nlinarith [Nat.mul_le_mul hx.1 hy.1, Nat.mul_le_mul hx.2 hy.2])
  · exact (Int.natAbs_add_le _ _).trans (by
      simp only [Int.natAbs_mul]
      nlinarith [Nat.mul_le_mul hx.1 hy.2, Nat.mul_le_mul hx.2 hy.1])

private theorem bound_fold {B C : ℕ} (xs : List GI) (z : GI)
    (hz : Bounded B z) (hx : ∀ x ∈ xs, Bounded C x) :
    Bounded (B+xs.length*C) (xs.foldl add z) := by
  induction xs generalizing B z with
  | nil => simpa using hz
  | cons x xs ih =>
    have h := ih (add z x) (bound_add hz (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))
    simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem bound_row {D B C : ℕ} (v : Fin D → GI)
    (A : Matrix (Fin D) (Fin D) GI) (hv : ∀ j, Bounded B (v j))
    (hA : ∀ i j, Bounded C (A i j)) (j : Fin D) :
    Bounded (B*(2*D*C)) (row v A j) := by
  have h := bound_fold (List.ofFn fun i : Fin D => mul (v i) (A i j)) (0,0)
    (B := 0) (C := 2*B*C) (by simp [Bounded]) (by
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact bound_mul (hv i) (hA i j))
  convert! h using 1
  simp only [List.length_ofFn, Nat.zero_add]
  ring

private theorem bound_run_fold {D B C : ℕ}
    (As : List (Matrix (Fin D) (Fin D) GI)) (v : Fin D → GI)
    (hv : ∀ j, Bounded B (v j)) (hA : ∀ A ∈ As, ∀ i j, Bounded C (A i j)) :
    ∀ j, Bounded (B*(2*D*C)^As.length) (As.foldl row v j) := by
  induction As generalizing B v with
  | nil => simpa using hv
  | cons A As ih =>
    have h := ih (row v A) (bound_row v A hv (hA A (by simp)))
      (fun A h => hA A (by simp [h]))
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem g3 : ∀ (D b : ℕ) (_hD : 0<D) (As : List (Matrix (Fin D) (Fin D) GI)),
    (∀ A∈As, ∀ i j, (A i j).1.natAbs ≤ 2^b ∧ (A i j).2.natAbs ≤ 2^b) →
    ∀ j, (run As j).1.natAbs ≤ (2*D)^As.length*2^(b*As.length) ∧
      (run As j).2.natAbs ≤ (2*D)^As.length*2^(b*As.length) ∧
      (run As j).1.natAbs ≤ 2^(As.length*(b+Nat.clog 2 (2*D))) ∧
      (run As j).2.natAbs ≤ 2^(As.length*(b+Nat.clog 2 (2*D))) := by
  intro D b _ As hA j
  have hv : ∀ i : Fin D, Bounded 1 (initial D i) := by
    intro i
    simp only [initial]
    split <;> simp [Bounded]
  have h := bound_run_fold As (initial D) hv hA j
  have hpow : (2*D)^As.length*2^(b*As.length) ≤
      2^(As.length*(b+Nat.clog 2 (2*D))) := by
    calc
      _ ≤ (2^Nat.clog 2 (2*D))^As.length*2^(b*As.length) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) (2*D)) As.length)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have h' : (run As j).1.natAbs ≤ (2*D)^As.length*2^(b*As.length) ∧
      (run As j).2.natAbs ≤ (2*D)^As.length*2^(b*As.length) := by
    simpa [Bounded, run, mul_pow, ← pow_mul] using h
  exact ⟨h'.1,h'.2,h'.1.trans hpow,h'.2.trans hpow⟩

end Qatlib.Concepts.DyadicProgram.DyadicContract
