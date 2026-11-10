/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneWayDanos05.MainResults.BiFlowAdjunction
import Qatlib.Papers.OneWayDanos05.MainResults.FlowFrame
import Qatlib.Concepts.PauliClifford.ExactRank.MatrixTensor
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.PauliClifford.ExactRank
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

variable {n : ℕ}

theorem pauliX_apply (i j : Fin 2) : pauliX i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [pauliX]

theorem pauliZ_apply (i j : Fin 2) :
    pauliZ i j = if i = j then (if i = 0 then 1 else -1) else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ]

theorem one2_apply (i j : Fin 2) : (1 : Operator 2) i j = if i = j then 1 else 0 :=
  Matrix.one_apply

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliProductDensity_congr {m : ℕ} {A B : Fin m → Operator 2}
    (h : ∀ k, A k = B k) : pauliProductDensity A = pauliProductDensity B := by
  ext x y
  simp only [pauliProductDensity, Matrix.of_apply]
  exact Finset.prod_congr rfl fun k _ => by rw [h k]

theorem pauliProductDensity_comm {m : ℕ} (A B : Fin m → Operator 2)
    (h : ∀ k, A k * B k = B k * A k) :
    pauliProductDensity A * pauliProductDensity B
      = pauliProductDensity B * pauliProductDensity A := by
  rw [pauliProductDensity_mul, pauliProductDensity_mul]
  exact pauliProductDensity_congr h

theorem comm_mul_of_comm {X A B : Matrix (Reg n) (Reg n) ℂ}
    (hA : X * A = A * X) (hB : X * B = B * X) : X * (A * B) = (A * B) * X := by
  calc X * (A * B) = (X * A) * B := (Matrix.mul_assoc X A B).symm
    _ = (A * X) * B := by rw [hA]
    _ = A * (X * B) := Matrix.mul_assoc A X B
    _ = A * (B * X) := by rw [hB]
    _ = (A * B) * X := (Matrix.mul_assoc A B X).symm

theorem localZ_eq_ppd (v : Fin n) :
    localZ v = pauliProductDensity (fun k => if k = v then pauliZ else (1 : Operator 2)) := by
  ext x y
  rw [localZ, Matrix.diagonal_apply, pauliProductDensity, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Fintype.prod_eq_single v]
    · cases hx : x v <;> simp [pauliZ_apply, boolEquivFin2, hx]
    · intro k hk
      rw [if_neg hk, one2_apply, if_pos rfl]
  · rw [if_neg hxy]
    symm
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      by_cases hiv : i = v
      · subst hiv
        rw [if_pos rfl, pauliZ_apply, if_neg (fun he => hi (boolEquivFin2.injective he))]
      · rw [if_neg hiv, one2_apply, if_neg (fun he => hi (boolEquivFin2.injective he))])

theorem localX_eq_ppd (v : Fin n) :
    localX v = pauliProductDensity (fun k => if k = v then pauliX else (1 : Operator 2)) := by
  ext x y
  have hL : localX v x y = if x = flipBit v y then (1 : ℂ) else 0 := rfl
  rw [hL, pauliProductDensity, Matrix.of_apply]
  by_cases hxy : x = flipBit v y
  · rw [if_pos hxy]
    symm
    apply Finset.prod_eq_one
    intro i _
    by_cases hiv : i = v
    · rw [if_pos hiv]
      have hxv : x i = !(y i) := by
        have hh := congrFun hxy i
        rw [← hiv] at hh
        simpa [flipBit] using hh
      have hne : x i ≠ y i := by
        intro h
        rw [h] at hxv
        exact Bool.not_ne_self (y i) hxv.symm
      rw [pauliX_apply, if_neg (fun he => hne (boolEquivFin2.injective he))]
    · rw [if_neg hiv, one2_apply]
      have hxyi : x i = y i := by
        have hh := congrFun hxy i
        simpa [flipBit, hiv] using hh
      rw [if_pos (by rw [hxyi])]
  · rw [if_neg hxy]
    symm
    have hnot : ¬ (x v = !(y v) ∧ ∀ i, i ≠ v → x i = y i) := by
      rintro ⟨hv, hrest⟩
      apply hxy
      funext i
      by_cases hi : i = v
      · subst hi; simpa [flipBit] using hv
      · simp [flipBit, hi, hrest i hi]
    by_cases hvv : x v = y v
    · refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
      rw [if_pos rfl, pauliX_apply, if_pos (by rw [hvv])]
    · have hxv : x v = !(y v) := by cases hx : x v <;> cases hy : y v <;> simp_all
      have hnall : ¬ ∀ i, i ≠ v → x i = y i := fun h => hnot ⟨hxv, h⟩
      push_neg at hnall
      obtain ⟨i, hiv, hixy⟩ := hnall
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [if_neg hiv, one2_apply, if_neg (fun he => hixy (boolEquivFin2.injective he))]

theorem zDiag_eq_ppd (L : Finset (Fin n)) :
    Matrix.diagonal (fun x : Reg n => ∏ k ∈ L, (if x k then (-1 : ℂ) else 1))
      = pauliProductDensity (fun k => if k ∈ L then pauliZ else (1 : Operator 2)) := by
  ext x y
  rw [Matrix.diagonal_apply, pauliProductDensity, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    symm
    have hsplit : (∏ k, (if k ∈ L then pauliZ else (1 : Operator 2))
          (boolEquivFin2 (x k)) (boolEquivFin2 (x k)))
        = ∏ k, if k ∈ L then pauliZ (boolEquivFin2 (x k)) (boolEquivFin2 (x k))
            else (1 : ℂ) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k ∈ L
      · rw [if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk, one2_apply, if_pos rfl]
    rw [hsplit, ← Finset.prod_filter]
    rw [show Finset.univ.filter (fun k => k ∈ L) = L from by ext k; simp]
    apply Finset.prod_congr rfl
    intro k _
    rw [pauliZ_apply]
    cases hx : x k <;> simp [boolEquivFin2, hx] <;> norm_num
  · rw [if_neg hxy]
    symm
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      by_cases hiL : i ∈ L
      · rw [if_pos hiL, pauliZ_apply, if_neg (fun he => hi (boolEquivFin2.injective he))]
      · rw [if_neg hiL, one2_apply, if_neg (fun he => hi (boolEquivFin2.injective he))])

theorem depZMatrix_eq_ppd (G : MbqcGraph n) (w v : Fin n) :
    depZMatrix G w v
      = pauliProductDensity
          (fun k => if k ∈ (nbhd G w).erase v then pauliZ else (1 : Operator 2)) := by
  unfold depZMatrix depZVal
  exact zDiag_eq_ppd ((nbhd G w).erase v)

theorem localZ_comm_localX_disjoint (v w : Fin n) (hvw : v ≠ w) :
    localZ v * localX w = localX w * localZ v := by
  rw [localZ_eq_ppd, localX_eq_ppd]
  apply pauliProductDensity_comm
  intro k
  by_cases hkv : k = v
  · subst hkv
    simp [hvw]
  · by_cases hkw : k = w
    · subst hkw
      simp [hkv]
    · simp [hkv, hkw]

theorem depZMatrix_comm_localX_of_not_mem (G : MbqcGraph n) (w v u : Fin n)
    (hu : u ∉ (nbhd G w).erase v) :
    depZMatrix G w v * localX u = localX u * depZMatrix G w v := by
  rw [depZMatrix_eq_ppd, localX_eq_ppd]
  apply pauliProductDensity_comm
  intro k
  by_cases hku : k = u
  · subst hku
    simp [hu]
  · by_cases hkz : k ∈ (nbhd G w).erase v
    · simp [hkz, hku]
    · simp [hkz, hku]

end Qatlib.Papers.OneWayDanos05.MainResults
