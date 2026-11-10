/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Init.Data.Vector.OfFn
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.GramQueryCore.GramRealization.RationalLDL
set_option autoImplicit false
set_option maxHeartbeats 500000
open Matrix
open scoped BigOperators

theorem zero_row {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℝ) (hM : M.PosSemidef) (i : I) (hi : M i i = 0) (j : I) : M i j = 0 := by
  have hs : M j i = M i j := by simpa using congrArg (fun A => A i j) hM.1
  let v : I → ℝ := (M j j + 1) • Pi.single i 1 - M i j • Pi.single j 1
  have h := hM.dotProduct_mulVec_nonneg v
  have hh : 0 ≤ M j j := hM.diag_nonneg
  simp only [v,star_trivial,Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
    smul_dotProduct,dotProduct_sub,dotProduct_smul,Matrix.mulVec_single_one,
    single_dotProduct,smul_eq_mul,Matrix.col_apply,hi,hs,one_mul,mul_zero] at h
  nlinarith [sq_nonneg (M i j),mul_nonneg hh (sq_nonneg (M i j))]
noncomputable def schurReal {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0

theorem schurReal_psd {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hM : M.PosSemidef) (hp : M 0 0 ≠ 0) : (schurReal M).PosSemidef := by
  let B : Matrix (Fin (n+1)) (Fin n) ℝ := fun k j =>
    Fin.cases (-M 0 j.succ / M 0 0) (fun i => if i = j then 1 else 0) k
  have hprod (a : Fin (n+1)) (j : Fin n) :
      (M*B) a j = M a 0 * (-M 0 j.succ / M 0 0) + M a j.succ := by
    rw [Matrix.mul_apply,Fin.sum_univ_succ]
    simp [B]
  have hz (j : Fin n) : (M*B) 0 j = 0 := by
    rw [hprod]
    field_simp
    ring
  have he : Bᴴ*M*B = schurReal M := by
    rw [Matrix.mul_assoc]
    ext i j
    rw [Matrix.mul_apply,Fin.sum_univ_succ,hz]
    simp [Matrix.conjTranspose_apply,B,hprod,schurReal]
    ring
  rw [← he]
  exact hM.conjTranspose_mul_mul_same B

def schur {n : ℕ} (K : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => K i.succ j.succ - K i.succ 0 * K 0 j.succ / K 0 0

noncomputable def realMatrix {I J : Type*} (K : Matrix I J ℚ) : Matrix I J ℝ :=
    fun i j => (K i j : ℝ)

theorem schur_psd {n : ℕ} (K : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hK : (realMatrix K).PosSemidef) : (realMatrix (schur K)).PosSemidef := by
  by_cases hp : K 0 0 = 0
  · convert hK.submatrix Fin.succ using 1
    ext i j
    simp [realMatrix,schur,hp]
  · have hp' : realMatrix K 0 0 ≠ 0 := by
      change (K 0 0 : ℝ) ≠ 0
      exact_mod_cast hp
    convert schurReal_psd (realMatrix K) hK hp' using 1
    ext i j
    simp [realMatrix,schur,schurReal]

structure Data (n : ℕ) where
  lower : Matrix (Fin n) (Fin n) ℚ
  diagonal : Fin n → ℚ

def lift {n : ℕ} (K : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (F : Data n) : Data (n+1) where
  lower := fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun a => Fin.cases (K a.succ 0 / K 0 0) (fun b => F.lower a b) j) i
  diagonal := Fin.cons (K 0 0) F.diagonal

def materializeData {n : ℕ} (K : Matrix (Fin n) (Fin n) ℚ) : Vector (Vector ℚ n) n :=
  Vector.ofFn (fun i : Fin n => Vector.ofFn (fun j : Fin n => K i j))

def tableMatrix {n : ℕ} (rows : Vector (Vector ℚ n) n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (rows.get i).get j

@[simp] theorem tableMatrix_materializeData {n : ℕ} (K : Matrix (Fin n) (Fin n) ℚ) :
    tableMatrix (materializeData K) = K := by
  ext i j
  simp [tableMatrix,materializeData,Vector.get]

def core : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → Option (Data n)
  | 0,_ => some ⟨1,fun i => Fin.elim0 i⟩
  | n+1,K => if K 0 0 < 0 then none else
      if K 0 0 = 0 ∧ ∃ i : Fin n, K i.succ 0 ≠ 0 then none else
        let rows := materializeData (schur K)
        (core n (tableMatrix rows)).map (lift K)

def compute (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) : Option (Data n) :=
  let rows := materializeData K
  let M := tableMatrix rows
  if ∀ i j, M i j = M j i then core n M else none

theorem core_complete (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ)
    (hK : (realMatrix K).PosSemidef) : ∃ F, core n K = some F := by
  induction n with
  | zero => exact ⟨_,rfl⟩
  | succ n ih =>
    have hp : 0 ≤ K 0 0 := by
      have h := hK.diag_nonneg (i := 0)
      change (0 : ℝ) ≤ (K 0 0 : ℝ) at h
      exact_mod_cast h
    have hz : ¬(K 0 0 = 0 ∧ ∃ i : Fin n, K i.succ 0 ≠ 0) := by
      rintro ⟨h0,i,hi⟩
      apply hi
      have hr := zero_row (realMatrix K) hK 0 (by change (K 0 0 : ℝ) = 0; exact_mod_cast h0) i.succ
      have hc : (K i.succ 0 : ℝ) = (K 0 i.succ : ℝ) := by
        simpa [realMatrix] using congrArg (fun A => A 0 i.succ) hK.1
      have he : (K i.succ 0 : ℝ) = 0 := hc.trans hr
      exact_mod_cast he
    obtain ⟨F,hF⟩ := ih (schur K) (schur_psd K hK)
    exact ⟨lift K F,by simp only [core,tableMatrix_materializeData,not_lt.mpr hp,if_false,hz,hF,Option.map_some]⟩

def factor {n : ℕ} (F : Data n) : Matrix (Fin n) (Fin n) ℚ :=
  F.lower * Matrix.diagonal F.diagonal * F.lowerᵀ

theorem factor_entry {n : ℕ} (F : Data n) (i j : Fin n) :
    factor F i j = ∑ h, F.lower i h * F.diagonal h * F.lower j h := by
  rw [factor,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]

theorem schur_symmetric {n : ℕ} (K : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hs : ∀ i j, K i j = K j i) : ∀ i j, schur K i j = schur K j i := by
  intro i j
  unfold schur
  rw [hs i.succ j.succ,hs i.succ 0,hs 0 j.succ]
  ring

theorem lift_factor {n : ℕ} (K : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (F : Data n)
    (hs : ∀ i j, K i j = K j i) (hz : K 0 0 = 0 → ∀ i : Fin n, K i.succ 0 = 0)
    (hF : factor F = schur K) : factor (lift K F) = K := by
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · rw [factor_entry,Fin.sum_univ_succ]
      simp [lift]
    · rw [factor_entry,Fin.sum_univ_succ]
      simp only [lift,Fin.cases_zero,Fin.cases_succ,Fin.cons_zero,one_mul,zero_mul,Finset.sum_const_zero,add_zero]
      by_cases hp : K 0 0 = 0
      · rw [hs 0 b.succ,hp,hz hp b]
        simp
      · rw [hs 0 b.succ]
        field_simp
  · refine Fin.cases ?_ (fun b => ?_) j
    · rw [factor_entry,Fin.sum_univ_succ]
      simp only [lift,Fin.cases_zero,Fin.cases_succ,Fin.cons_zero,mul_one,mul_zero,Finset.sum_const_zero,add_zero]
      by_cases hp : K 0 0 = 0
      · rw [hp,hz hp a]
        simp
      · field_simp
    · rw [factor_entry,Fin.sum_univ_succ]
      simp only [lift,Fin.cases_succ,Fin.cases_zero,Fin.cons_succ,Fin.cons_zero]
      have he : factor F a b = schur K a b := congrArg (fun A => A a b) hF
      rw [factor_entry] at he
      rw [he]
      unfold schur
      rw [hs 0 b.succ]
      by_cases hp : K 0 0 = 0
      · simp [hp]
      · field_simp
        ring

theorem core_sound (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) (F : Data n)
    (hs : ∀ i j, K i j = K j i) (hF : core n K = some F) :
    factor F = K ∧ ∀ i, 0 ≤ F.diagonal i := by
  induction n with
  | zero =>
    constructor
    · ext i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    simp only [core,tableMatrix_materializeData] at hF
    split_ifs at hF with hp hz
    cases hG : core n (schur K) with
    | none => simp [hG] at hF
    | some G =>
      simp only [hG,Option.map_some,Option.some.injEq] at hF
      subst F
      obtain ⟨hEq,hd⟩ := ih (schur K) G (schur_symmetric K hs) hG
      have hzero : K 0 0 = 0 → ∀ i : Fin n, K i.succ 0 = 0 := by
        intro h0 i
        by_contra hi
        exact hz ⟨h0,i,hi⟩
      refine ⟨lift_factor K G hs hzero hEq,?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_of_not_gt hp
      · exact hd j

theorem realMatrix_factor {n : ℕ} (F : Data n) : realMatrix (factor F) =
    realMatrix F.lower * Matrix.diagonal (fun i => (F.diagonal i : ℝ)) * (realMatrix F.lower)ᵀ := by
  ext i j
  change (factor F i j : ℝ) = _
  rw [factor_entry,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,realMatrix]
  simp

theorem factor_psd {n : ℕ} (F : Data n) (hd : ∀ i, 0 ≤ F.diagonal i) :
    (realMatrix (factor F)).PosSemidef := by
  have hD : (Matrix.diagonal (fun i => (F.diagonal i : ℝ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℝ) ≤ (F.diagonal i : ℝ)
      exact_mod_cast hd i)
  rw [realMatrix_factor]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hD.mul_mul_conjTranspose_same (realMatrix F.lower)

theorem compute_complete (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ)
    (hK : (realMatrix K).PosSemidef) : ∃ F, compute n K = some F := by
  have hs : ∀ i j, K i j = K j i := by
    intro i j
    have he := congrArg (fun A => A j i) hK.1
    have he' : (K i j : ℝ) = (K j i : ℝ) := by simpa [realMatrix] using he
    exact_mod_cast he'
  obtain ⟨F,hF⟩ := core_complete n K hK
  exact ⟨F,by simp only [compute,tableMatrix_materializeData,if_pos hs,hF]⟩

theorem compute_sound (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) (F : Data n)
    (hF : compute n K = some F) : factor F = K ∧ ∀ i, 0 ≤ F.diagonal i := by
  simp only [compute,tableMatrix_materializeData] at hF
  split_ifs at hF with hs
  exact core_sound n K F hs hF

theorem compute_success_iff (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) :
    (∃ F, compute n K = some F) ↔ (realMatrix K).PosSemidef := by
  constructor
  · rintro ⟨F,hF⟩
    obtain ⟨hEq,hd⟩ := compute_sound n K F hF
    rw [← hEq]
    exact factor_psd F hd
  · exact compute_complete n K

theorem core_lower (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) (F : Data n)
    (hF : core n K = some F) :
    (∀ i, F.lower i i = 1) ∧ (∀ i j, i < j → F.lower i j = 0) := by
  induction n with
  | zero => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    simp only [core,tableMatrix_materializeData] at hF
    split_ifs at hF
    cases hG : core n (schur K) with
    | none => simp [hG] at hF
    | some G =>
      simp only [hG,Option.map_some,Option.some.injEq] at hF
      subst F
      obtain ⟨hu,ht⟩ := ih (schur K) G hG
      constructor
      · intro i
        refine Fin.cases rfl (fun j => hu j) i
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hij)
          | succ b => rfl
        | succ a =>
          cases j using Fin.cases with
          | zero => exact False.elim (Nat.not_lt_zero _ hij)
          | succ b => exact ht a b (by simpa using hij)

theorem compute_lower (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) (F : Data n)
    (hF : compute n K = some F) :
    (∀ i, F.lower i i = 1) ∧ (∀ i j, i < j → F.lower i j = 0) := by
  simp only [compute,tableMatrix_materializeData] at hF
  split_ifs at hF
  exact core_lower n K F hF

def isPSD (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) : Bool := (compute n K).isSome

theorem isPSD_iff (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) :
    isPSD n K = true ↔ (realMatrix K).PosSemidef := by
  rw [← compute_success_iff]
  cases hc : compute n K <;> simp [isPSD,hc]

end Qatlib.Concepts.GramQueryCore.GramRealization.RationalLDL
