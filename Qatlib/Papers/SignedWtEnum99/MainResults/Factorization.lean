/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SignedWtEnum99.MainResults.QSEN
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults

def qsen2 {m n : ℕ} (A1 A2 : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : ℤ) : ℤ :=
  ∑ b : Fin n → ZMod 2,
    if A1.mulVec b = 0 ∧ A2.mulVec b = 0 then
      sgnZ (quadForm B b) * x ^ bitWeight b * y ^ (n - bitWeight b)
    else 0

lemma qsen2_congr {m m' n : ℕ} {A1 A2 : Matrix (Fin m) (Fin n) (ZMod 2)}
    {A1' A2' : Matrix (Fin m') (Fin n) (ZMod 2)}
    {B1 B2 : Matrix (Fin n) (Fin n) (ZMod 2)} (x y : ℤ)
    (hA1 : ∀ b : Fin n → ZMod 2, A1.mulVec b = 0 ↔ A1'.mulVec b = 0)
    (hA2 : ∀ b : Fin n → ZMod 2, A2.mulVec b = 0 ↔ A2'.mulVec b = 0)
    (hB : B1 = B2) : qsen2 A1 A2 B1 x y = qsen2 A1' A2' B2 x y := by
  subst hB
  classical
  unfold qsen2
  apply Finset.sum_congr rfl
  intro b _
  by_cases h1 : A1.mulVec b = 0
  · by_cases h2 : A2.mulVec b = 0
    · rw [if_pos ⟨h1, h2⟩, if_pos ⟨(hA1 b).mp h1, (hA2 b).mp h2⟩]
    · have h2' : ¬ A2'.mulVec b = 0 := fun hh => h2 ((hA2 b).mpr hh)
      rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => h2' hh.2)]
  · have h1' : ¬ A1'.mulVec b = 0 := fun hh => h1 ((hA1 b).mpr hh)
    rw [if_neg (fun hh => h1 hh.1), if_neg (fun hh => h1' hh.1)]

lemma mulVec_eq_sum_cols {N k : ℕ} (X : Matrix (Fin N) (Fin k) (ZMod 2))
    (v : Fin k → ZMod 2) :
    X *ᵥ v = ∑ j : Fin k, v j • (fun i : Fin N => X i j) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma mulVec_eq_zero_iff_of_indep_cols {N k : ℕ} (X : Matrix (Fin N) (Fin k) (ZMod 2))
    (h : LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => X i j))
    (v : Fin k → ZMod 2) : X *ᵥ v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hsum : ∑ j : Fin k, v j • (fun i : Fin N => X i j) = 0 := by
      rw [← mulVec_eq_sum_cols]
      exact hv
    have hz := (Fintype.linearIndependent_iff.mp h) v hsum
    funext j
    exact hz j
  · intro hv
    rw [hv]
    exact Matrix.mulVec_zero _

theorem qsen2_eq_of_factorization {N k : ℕ} (C : Matrix (Fin N) (Fin N) (ZMod 2))
    (X Y : Matrix (Fin N) (Fin k) (ZMod 2)) (hC : C = X * Yᵀ)
    (hX : LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => X i j))
    (hY : LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => Y i j))
    (x y : ℤ) :
    qsen2 C Cᵀ (lwtr C) x y = qsen2 Yᵀ Xᵀ (lwtr C) x y := by
  apply qsen2_congr x y
  · intro b
    rw [hC, ← Matrix.mulVec_mulVec]
    exact mulVec_eq_zero_iff_of_indep_cols X hX (Yᵀ *ᵥ b)
  · intro b
    have hCt : Cᵀ = Y * Xᵀ := by
      rw [hC, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hCt, ← Matrix.mulVec_mulVec]
    exact mulVec_eq_zero_iff_of_indep_cols Y hY (Xᵀ *ᵥ b)
  · rfl

end Qatlib.Papers.SignedWtEnum99.MainResults
