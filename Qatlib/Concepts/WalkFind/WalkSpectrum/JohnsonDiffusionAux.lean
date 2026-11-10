/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.BlockUnitary
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.WalkSpectrum
open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

theorem jwD2_population_fixed (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A+B)
    (a : Bool) :
    jwD2 (B/(A+B)) a false * (Real.sqrt A : ℂ) +
      jwD2 (B/(A+B)) a true * (Real.sqrt B : ℂ) =
      (if a then (Real.sqrt B : ℂ) else (Real.sqrt A : ℂ)) := by
  have hsqA := Real.sq_sqrt hA
  have hsqB := Real.sq_sqrt hB
  have hs : Real.sqrt (B/(A+B) - B/(A+B)*(B/(A+B))) =
      Real.sqrt A * Real.sqrt B / (A+B) := by
    have he : B/(A+B) - B/(A+B)*(B/(A+B)) = A*B/(A+B)^2 := by
      field_simp
      ring
    rw [he, Real.sqrt_div (mul_nonneg hA hB), Real.sqrt_mul hA,
      Real.sqrt_sq_eq_abs, abs_of_pos hAB]
  cases a <;> simp only [jwD2, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false]
  all_goals rw [hs]
  all_goals norm_cast
  all_goals norm_num
  all_goals field_simp
  · linear_combination 2 * Real.sqrt A * hsqB
  · linear_combination 2 * Real.sqrt B * hsqA

theorem jwCnt_inserted_false (k N r j : ℕ) (hjr : j ≤ r) (hjk : j ≤ k)
    (_hNr : k ≤ N-r) :
    jwCnt k N r j false =
      Nat.choose k j * Nat.choose (N-k) (r+1-j) * (r+1-j) := by
  have h := Nat.choose_succ_right_eq (N-k) (r-j)
  have h1 : r-j+1 = r+1-j := by omega
  have h2 : N-k-(r-j) = N-r-(k-j) := by omega
  rw [h1,h2] at h
  unfold jwCnt
  simp only [Bool.false_eq_true, if_false]
  rw [mul_assoc, ← h, ← mul_assoc]

theorem jwCnt_inserted_true (k N r j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r+1)
    (_hjk : j ≤ k) :
    jwCnt k N r (j-1) true =
      Nat.choose k j * Nat.choose (N-k) (r+1-j) * j := by
  have h := Nat.choose_succ_right_eq k (j-1)
  have h1 : j-1+1 = j := by omega
  have h2 : r-(j-1) = r+1-j := by omega
  rw [h1] at h
  unfold jwCnt
  simp only [if_true, h2]
  calc
    _ = (Nat.choose k (j-1) * (k-(j-1))) * Nat.choose (N-k) (r+1-j) := by ring
    _ = _ := by rw [← h]; ring

theorem jw_unitary_pow_eigenvector_lift (m t : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (start v : Fin m → ℂ) (ν : ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (heigen : U ^ t *ᵥ v = ν • v)
    (horth : (∑ i, star (v i) * start i) = 0) (hv : v ≠ 0) :
    ∃ (μ : ℂ) (w : Fin m → ℂ), U *ᵥ w = μ • w ∧
      (∑ i, star (w i) * start i) = 0 ∧ w ≠ 0 ∧ μ ^ t = ν := by
  classical
  let f : Module.End ℂ (Fin m → ℂ) := U.toLin'
  let g : (Fin m → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun w => star start ⬝ᵥ w
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun a w => by simp [dotProduct_smul, smul_eq_mul] }
  have hadj : star U *ᵥ start = start := by
    calc
      _ = star U *ᵥ (U *ᵥ start) := by rw [hstart]
      _ = start := by rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  have hrow : star start ᵥ* U = star start := by
    simpa only [Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using congrArg star hadj
  have hg (w : Fin m → ℂ) : g (f w) = g w := by
    change star start ⬝ᵥ (U *ᵥ w) = star start ⬝ᵥ w
    rw [Matrix.dotProduct_mulVec, hrow]
  have hconj (w : Fin m → ℂ) :
      g w = star (∑ i, star (w i) * start i) := by
    change star start ⬝ᵥ w = _
    simp [dotProduct, star_sum, star_mul, mul_comm]
  let S : Submodule ℂ (Fin m → ℂ) := Module.End.eigenspace (f ^ t) ν ⊓ LinearMap.ker g
  have hvS : v ∈ S := by
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      simpa only [f, ← Matrix.toLin'_pow, Matrix.toLin'_apply] using heigen
    · change g v = 0
      rw [hconj, horth, star_zero]
  have hS : ∀ w ∈ S, f w ∈ S := by
    intro w hw
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      have hwe := Module.End.mem_eigenspace_iff.mp hw.1
      have hcomm : (f ^ t) (f w) = f ((f ^ t) w) := by
        simpa only [pow_one, Module.End.mul_apply] using
          congrArg (fun a : Module.End ℂ (Fin m → ℂ) => a w) (pow_mul_comm f t 1)
      rw [hcomm, hwe, map_smul]
    · change g (f w) = 0
      rw [hg]
      exact hw.2
  have hvs : (⟨v, hvS⟩ : S) ≠ 0 := by
    intro h
    exact hv (congrArg Subtype.val h)
  letI : Nontrivial S := nontrivial_of_ne _ _ hvs
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hS)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 : (w : Fin m → ℂ) ≠ 0 := by
    intro h
    apply hw.2
    exact Subtype.ext h
  have hwU : U *ᵥ (w : Fin m → ℂ) = μ • (w : Fin m → ℂ) := by
    exact congrArg Subtype.val hw.apply_eq_smul
  have hwf : f.HasEigenvector μ (w : Fin m → ℂ) :=
    ⟨Module.End.mem_eigenspace_iff.mpr hwU, hw0⟩
  have hpow : μ ^ t = ν := by
    apply smul_left_injective ℂ hw0
    exact (hwf.pow_apply t).symm.trans (Module.End.mem_eigenspace_iff.mp w.2.1)
  refine ⟨μ, w, hwU, ?_, hw0, hpow⟩
  have hz : g (w : Fin m → ℂ) = 0 := w.2.2
  rw [hconj] at hz
  exact star_eq_zero.mp hz

theorem jwD2_population_normalized (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (a b : Bool) :
    jwD2 (B/(A+B)) a b * ((1 / Real.sqrt (if a then B else A) : ℝ) : ℂ) =
      (((2*(if b then B else A)/(A+B) - if a = b then 1 else 0) /
        Real.sqrt (if b then B else A) : ℝ) : ℂ) := by
  have hs : Real.sqrt (B/(A+B) - B/(A+B)*(B/(A+B))) =
      Real.sqrt A * Real.sqrt B / (A+B) := by
    have he : B/(A+B) - B/(A+B)*(B/(A+B)) = A*B/(A+B)^2 := by
      field_simp
      ring
    rw [he,Real.sqrt_div (by positivity),Real.sqrt_mul (le_of_lt hA),
      Real.sqrt_sq_eq_abs,abs_of_pos (by linarith : 0 < A+B)]
  have ha : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hA)
  have hb : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  have hab : A+B ≠ 0 := by linarith
  have hsqA := Real.sq_sqrt (le_of_lt hA)
  have hsqB := Real.sq_sqrt (le_of_lt hB)
  cases a <;> cases b <;> simp only [jwD2, Bool.false_eq_true, Bool.true_eq_false,
    ite_true,ite_false]
  all_goals try rw [hs]
  all_goals norm_cast
  all_goals norm_num
  all_goals field_simp
  all_goals nlinarith

theorem jwD2_fiber_normalized (C a b : ℝ) (hC : 0 < C) (ha : 0 < a) (hb : 0 < b)
    (o l : Bool) :
    jwD2 (b/(a+b)) o l * ((1 / Real.sqrt (C*(if o then b else a)) : ℝ) : ℂ) =
      (((2*(if l then b else a)/(a+b) - if o = l then 1 else 0) /
        Real.sqrt (C*(if l then b else a)) : ℝ) : ℂ) := by
  have h := jwD2_population_normalized (C*a) (C*b) (mul_pos hC ha) (mul_pos hC hb) o l
  have he : C*b/(C*a+C*b) = b/(a+b) := by
    rw [← mul_add,mul_div_mul_left _ _ (ne_of_gt hC)]
  have he' : (if l then C*b else C*a)/(C*a+C*b) = (if l then b else a)/(a+b) := by
    cases l
    · change C*a/(C*a+C*b) = a/(a+b)
      rw [← mul_add,mul_div_mul_left _ _ (ne_of_gt hC)]
    · exact he
  rw [he,show 2*(if l then C*b else C*a)/(C*a+C*b) =
      2*((if l then C*b else C*a)/(C*a+C*b)) by ring,he'] at h
  cases o <;> cases l <;> simpa [mul_div_assoc] using h

end Qatlib.Concepts.WalkFind.WalkSpectrum
