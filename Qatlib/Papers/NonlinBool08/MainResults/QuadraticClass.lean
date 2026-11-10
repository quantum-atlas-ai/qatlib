/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.BentCore.BentFacts
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.QuadraticClass

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

def quad {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (L : BVec n)
    (x : BVec n) : ZMod 2 :=
  dot x (Q.mulVec x) + dot L x

def symplectic {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  Q + Qᵀ

def pt {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (w : BVec n) : BVec n :=
  (symplectic Q)⁻¹.mulVec w

def dualQ {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  ((symplectic Q)⁻¹)ᵀ * Q * (symplectic Q)⁻¹

def dualL {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (L : BVec n) : BVec n :=
  ((symplectic Q)⁻¹)ᵀ.mulVec L

lemma quad_polar {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (L : BVec n)
    (x z : BVec n) :
    quad Q L x + quad Q L (x + z)
      = dot x ((symplectic Q).mulVec z) + quad Q L z := by
  unfold quad symplectic
  simp only [dot, Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.add_mulVec]
  rw [dotProduct_comm z (Q.mulVec x)]
  rw [show dotProduct (Q.mulVec x) z = dotProduct x (Qᵀ.mulVec z) from dot_mulVec Q x z]
  ring_nf
  try rw [show (2 : ZMod 2) = 0 from by decide]
  try simp

lemma pt_spec {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (hB : IsUnit (symplectic Q).det) (w : BVec n) :
    (symplectic Q).mulVec (pt Q w) = w := by
  unfold pt
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]

lemma symplectic_mulVec_eq_zero_iff {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (hB : IsUnit (symplectic Q).det)
    (z : BVec n) :
    (symplectic Q).mulVec z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hinj : Function.Injective (symplectic Q).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det (symplectic Q)).mpr hB)
    have hz : z = 0 := hinj (by rw [h]; simp)
    exact hz
  · intro h
    rw [h]
    simp

lemma quad_autocorrelation {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (L : BVec n) (hB : IsUnit (symplectic Q).det) (z : BVec n) :
    (∑ x : BVec n, eps (quad Q L x + quad Q L (x + z)))
      = if z = 0 then (2 : ℤ) ^ n else 0 := by
  have hz := symplectic_mulVec_eq_zero_iff Q hB z
  have hterm : ∀ x : BVec n,
      eps (quad Q L x + quad Q L (x + z))
        = eps (quad Q L z) * eps (dot x ((symplectic Q).mulVec z)) := by
    intro x
    rw [quad_polar Q L x z, eps_add]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, sum_w_eps_dot]
  by_cases h : z = 0
  · rw [if_pos (hz.mpr h), if_pos h]
    subst h
    simp [quad]
  · rw [if_neg (fun hc => h (hz.mp hc)), if_neg h]
    simp

lemma quad_walsh_sq {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (L : BVec n) (hB : IsUnit (symplectic Q).det) (w : BVec n) :
    walsh (quad Q L) w ^ 2 = (2 : ℤ) ^ n := by
  rw [walsh_sq_deriv]
  have hterm : ∀ z : BVec n,
      eps (dot w z) * (∑ x : BVec n, eps (quad Q L x + quad Q L (x + z)))
        = if z = 0 then (2 : ℤ) ^ n else 0 := by
    intro z
    rw [quad_autocorrelation Q L hB z]
    by_cases h : z = 0
    · subst h
      simp
    · rw [if_neg h]
      simp
  simp only [hterm]
  rw [Finset.sum_eq_single 0]
  · rw [if_pos rfl]
  · intro z _ hz
    rw [if_neg hz]
  · intro hmem
    simp at hmem

lemma quad_complete {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (L : BVec n) (hB : IsUnit (symplectic Q).det) (x w : BVec n) :
    quad Q L x + dot w x = quad Q L (x + pt Q w) + quad Q L (pt Q w) := by
  have hp := pt_spec Q hB w
  have h := quad_polar Q L x (pt Q w)
  rw [hp] at h
  have hB' : quad Q L (x + pt Q w)
      = (quad Q L x + dot x w) + quad Q L (pt Q w) := by
    have hcancel : (quad Q L x + quad Q L (x + pt Q w)) + quad Q L x
        = quad Q L (x + pt Q w) := by
      rw [add_comm (quad Q L x + quad Q L (x + pt Q w)) (quad Q L x),
          ← add_assoc, add_self_zmod2, zero_add]
    calc quad Q L (x + pt Q w)
        = (quad Q L x + quad Q L (x + pt Q w)) + quad Q L x := hcancel.symm
      _ = (dot x w + quad Q L (pt Q w)) + quad Q L x := by rw [h]
      _ = (quad Q L x + dot x w) + quad Q L (pt Q w) := by abel
  have hwx : dot w x = dot x w := by
    simp only [dot]
    rw [dotProduct_comm]
  rw [hwx, hB']
  rw [show ((quad Q L x + dot x w) + quad Q L (pt Q w)) + quad Q L (pt Q w)
      = quad Q L x + dot x w from by
    rw [add_assoc, add_self_zmod2, add_zero]]

lemma quad_walsh_shift_at {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (L : BVec n) (hB : IsUnit (symplectic Q).det) (w : BVec n) :
    walsh (quad Q L) w = eps (quad Q L (pt Q w)) * walsh (quad Q L) 0 := by
  have h0 : walsh (quad Q L) 0 = ∑ x : BVec n, eps (quad Q L x) := by
    rw [walsh_eq_sum_eps_add]
    apply Finset.sum_congr rfl
    intro x _
    rw [show dot (0 : BVec n) x = 0 from by simp [dot], zero_add]
  have hterm : ∀ x : BVec n, eps (dot w x + quad Q L x)
      = eps (quad Q L (pt Q w)) * eps (quad Q L (x + pt Q w)) := by
    intro x
    have hc := quad_complete Q L hB x w
    rw [show dot w x + quad Q L x
        = quad Q L (x + pt Q w) + quad Q L (pt Q w) from by
      rw [add_comm (dot w x) (quad Q L x)]
      exact hc]
    rw [eps_add]
    ring
  have hre : (∑ x : BVec n, eps (quad Q L (x + pt Q w)))
      = ∑ y : BVec n, eps (quad Q L y) := by
    refine Fintype.sum_bijective (fun x : BVec n => x + pt Q w)
      (shift_bijective (pt Q w))
      (fun x => eps (quad Q L (x + pt Q w))) (fun y => eps (quad Q L y)) ?_
    intro x
    rfl
  rw [h0, walsh_eq_sum_eps_add]
  simp only [hterm]
  rw [← Finset.mul_sum, hre]

lemma quad_walsh0_sign {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (L : BVec n) (hB : IsUnit (symplectic Q).det) (hn : Even n) :
    ∃ c : ZMod 2, walsh (quad Q L) 0 = (2 : ℤ) ^ (n / 2) * eps c := by
  have hs : walsh (quad Q L) 0 ^ 2 = ((2 : ℤ) ^ (n / 2)) ^ 2 := by
    rw [show ((2 : ℤ) ^ (n / 2)) ^ 2 = (2 : ℤ) ^ n from by
      rw [pow_two]
      exact pow_half_mul hn]
    exact quad_walsh_sq Q L hB 0
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hs) with h | h
  · exact ⟨0, by rw [h, eps_zero, mul_one]⟩
  · exact ⟨1, by rw [h, eps_one]; ring⟩

lemma quad_comp {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (L : BVec n)
    (w : BVec n) :
    quad Q L (pt Q w) = quad (dualQ Q) (dualL Q L) w := by
  unfold quad pt dualQ dualL
  have hQ : dot ((symplectic Q)⁻¹.mulVec w) (Q.mulVec ((symplectic Q)⁻¹.mulVec w))
      = dot w ((((symplectic Q)⁻¹)ᵀ * Q * (symplectic Q)⁻¹).mulVec w) := by
    rw [dot_mulVec ((symplectic Q)⁻¹) w (Q.mulVec ((symplectic Q)⁻¹.mulVec w))]
    congr 1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hL : dot L ((symplectic Q)⁻¹.mulVec w)
      = dot (((symplectic Q)⁻¹)ᵀ.mulVec L) w := by
    rw [show dot L ((symplectic Q)⁻¹.mulVec w)
        = dot ((symplectic Q)⁻¹.mulVec w) L from dotProduct_comm _ _]
    rw [dot_mulVec ((symplectic Q)⁻¹) w L]
    rw [show dot w (((symplectic Q)⁻¹)ᵀ.mulVec L)
        = dot (((symplectic Q)⁻¹)ᵀ.mulVec L) w from dotProduct_comm _ _]
  rw [hQ, hL]

theorem corollary3_quadratic_bent {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (L : BVec n)
    (hn : Even n) (hB : IsUnit (symplectic Q).det) :
    Bent (quad Q L) ∧
    (∃ (Q' : Matrix (Fin n) (Fin n) (ZMod 2)) (L' : BVec n) (c : ZMod 2),
      IsDual (quad Q L) (fun w => quad Q' L' w + c) ∧
      Bent (fun w => quad Q' L' w + c)) := by
  have hbent : Bent (quad Q L) := fun w => quad_walsh_sq Q L hB w
  obtain ⟨c, hc⟩ := quad_walsh0_sign Q L hB hn
  have hd : IsDual (quad Q L) (fun w => quad (dualQ Q) (dualL Q L) w + c) := by
    intro w
    rw [quad_walsh_shift_at Q L hB w, hc, quad_comp Q L w, eps_add]
    ring
  exact ⟨hbent, dualQ Q, dualL Q L, c, hd, bent_dual_bent hd (pow_half_mul hn)⟩

end Qatlib.Papers.NonlinBool08.MainResults.QuadraticClass
