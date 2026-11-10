/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SignedWtEnum99.MainResults.Factorization
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults

variable {N : ℕ}

lemma qsen_congr {m m' n : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod 2)}
    {A' : Matrix (Fin m') (Fin n) (ZMod 2)}
    {B : Matrix (Fin n) (Fin n) (ZMod 2)} (x y : ℤ)
    (hA : ∀ b : Fin n → ZMod 2, A.mulVec b = 0 ↔ A'.mulVec b = 0) :
    qsen A B x y = qsen A' B x y := by
  classical
  unfold qsen
  apply Finset.sum_congr rfl
  intro b _
  by_cases h1 : A.mulVec b = 0
  · rw [if_pos h1, if_pos ((hA b).mp h1)]
  · have h1' : ¬ A'.mulVec b = 0 := fun hh => h1 ((hA b).mpr hh)
    rw [if_neg h1, if_neg h1']

lemma linearIndependent_cols_of_injective {N k : ℕ} (X : Matrix (Fin N) (Fin k) (ZMod 2))
    (h : Function.Injective (Matrix.mulVecLin X)) :
    LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => X i j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hXc : X *ᵥ c = 0 := by
    rw [mulVec_eq_sum_cols]
    exact hc
  have hc0 : c = 0 := h (by simpa [Matrix.mulVecLin_apply] using hXc)
  intro j
  exact congrFun hc0 j

lemma linearIndependent_rows_of_surjective {r N : ℕ} (M : Matrix (Fin r) (Fin N) (ZMod 2))
    (h : Function.Surjective (Matrix.mulVecLin M)) :
    LinearIndependent (ZMod 2) (fun j : Fin r => fun i : Fin N => M j i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hrow : ∀ i : Fin N, ∑ j' : Fin r, c j' * M j' i = 0 := by
    intro i
    have h1 := congrFun hc i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h1
  intro j
  obtain ⟨u, hu⟩ := h (Pi.single j (1 : ZMod 2))
  have hu' : M *ᵥ u = Pi.single j (1 : ZMod 2) := by
    rw [← Matrix.mulVecLin_apply]
    exact hu
  have hzero : ∑ j' : Fin r, c j' * (M *ᵥ u) j' = 0 := by
    have hexp : ∀ j' : Fin r,
        c j' * (M *ᵥ u) j' = ∑ i : Fin N, (c j' * M j' i) * u i := by
      intro j'
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [Finset.sum_congr rfl (fun j' _ => hexp j'), Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.sum_mul]
    simp [hrow i]
  have hval : ∑ j' : Fin r, c j' * (M *ᵥ u) j' = c j := by
    rw [hu']
    simp [Pi.single_apply]
  rw [← hval, hzero]

theorem exists_indep_cols_factorization (C : Matrix (Fin N) (Fin N) (ZMod 2)) :
    ∃ (k : ℕ) (X Y : Matrix (Fin N) (Fin k) (ZMod 2)),
      LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => X i j) ∧
      LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => Y i j) ∧
      C = X * Yᵀ := by
  classical
  let f : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin N → ZMod 2) := Matrix.mulVecLin C
  let W : Submodule (ZMod 2) (Fin N → ZMod 2) := LinearMap.range f
  haveI hWfin : Module.Finite (ZMod 2) W :=
    Module.Finite.of_injective W.subtype Subtype.val_injective
  let bW : Module.Basis (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W :=
    Module.finBasis (ZMod 2) W
  let e : (Fin (Module.finrank (ZMod 2) W) → ZMod 2) ≃ₗ[ZMod 2] W := bW.equivFun.symm
  let g : (Fin N → ZMod 2) →ₗ[ZMod 2] W :=
    LinearMap.codRestrict W f (fun x => LinearMap.mem_range_self f x)
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp w.2
    exact ⟨x, Subtype.ext hx⟩
  let q : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) W) → ZMod 2) :=
    e.symm.toLinearMap.comp g
  have hq : Function.Surjective q := e.symm.surjective.comp hg
  let X : Matrix (Fin N) (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) :=
    LinearMap.toMatrix'
      (W.subtype.comp (e : (Fin (Module.finrank (ZMod 2) W) → ZMod 2) →ₗ[ZMod 2] W))
  let M : Matrix (Fin (Module.finrank (ZMod 2) W)) (Fin N) (ZMod 2) := LinearMap.toMatrix' q
  have hX : Matrix.mulVecLin X =
      W.subtype.comp (e : (Fin (Module.finrank (ZMod 2) W) → ZMod 2) →ₗ[ZMod 2] W) := by
    rw [show Matrix.mulVecLin X = Matrix.toLin' X from rfl]
    simp [X]
  have hM : Matrix.mulVecLin M = q := by
    rw [show Matrix.mulVecLin M = Matrix.toLin' M from rfl]
    simp [M]
  have hC : Matrix.mulVecLin C = f := rfl
  refine ⟨Module.finrank (ZMod 2) W, X, Mᵀ, ?_, ?_, ?_⟩
  · exact linearIndependent_cols_of_injective X
      (by rw [hX]; exact Subtype.val_injective.comp e.injective)
  · have hcols : (fun j : Fin (Module.finrank (ZMod 2) W) => fun i : Fin N => (Mᵀ) i j)
        = (fun j : Fin (Module.finrank (ZMod 2) W) => fun i : Fin N => M j i) := rfl
    rw [hcols]
    exact linearIndependent_rows_of_surjective M (by rw [hM]; exact hq)
  · have hprod : X * (Mᵀ)ᵀ = X * M := by rw [Matrix.transpose_transpose]
    rw [hprod]
    have hlin : Matrix.mulVecLin (X * M) = Matrix.mulVecLin C := by
      rw [Matrix.mulVecLin_mul, hX, hM, hC]
      apply LinearMap.ext
      intro u
      show W.subtype (e (e.symm (g u))) = f u
      rw [LinearEquiv.apply_symm_apply]
      rfl
    exact (Matrix.toLin'.injective (show Matrix.toLin' (X * M) = Matrix.toLin' C from hlin)).symm

theorem qsen2_problem4_eq_sum19 (C : Matrix (Fin N) (Fin N) (ZMod 2)) (x y : ℤ) :
    ∃ (k : ℕ) (X Y : Matrix (Fin N) (Fin k) (ZMod 2)),
      LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => X i j) ∧
      LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => Y i j) ∧
      C = X * Yᵀ ∧
      qsen2 C Cᵀ (lwtr C) x y = qsen2 Yᵀ Xᵀ (lwtr C) x y := by
  obtain ⟨k, X, Y, hX, hY, hC⟩ := exists_indep_cols_factorization C
  exact ⟨k, X, Y, hX, hY, hC, qsen2_eq_of_factorization C X Y hC hX hY x y⟩

theorem qsen_problem3_eq_sum18 (C : Matrix (Fin N) (Fin N) (ZMod 2)) (x y : ℤ) :
    qsen C (lwtr ((1 : Matrix (Fin N) (Fin N) (ZMod 2))ᵀ * C)) x y
      = qsen C (lwtr C) x y := by
  simp

theorem qsen_eq_of_indep_rows {m : ℕ} (H0 H1 : Matrix (Fin m) (Fin N) (ZMod 2))
    (h0 : LinearIndependent (ZMod 2) (fun j : Fin m => fun i : Fin N => H0 j i)) (x y : ℤ) :
    qsen H1 (lwtr (H0ᵀ * H1)) x y = qsen (H0ᵀ * H1) (lwtr (H0ᵀ * H1)) x y := by
  classical
  apply qsen_congr x y
  intro b
  constructor
  · intro hb
    rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_zero]
  · intro hb
    rw [← Matrix.mulVec_mulVec] at hb
    have h0' : LinearIndependent (ZMod 2) (fun j : Fin m => fun i : Fin N => (H0ᵀ) i j) := by
      simpa using h0
    exact (mulVec_eq_zero_iff_of_indep_cols H0ᵀ h0' (H1 *ᵥ b)).mp hb

end Qatlib.Papers.SignedWtEnum99.MainResults
