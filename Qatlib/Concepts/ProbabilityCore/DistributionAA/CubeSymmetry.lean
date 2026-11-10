/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

theorem cube_hamming_eq_sum {n : ℕ} (x : Fin n → Bool) :
    cubeHamming x = ∑ i, if x i then (1 : ℕ) else 0 := by
  symm
  exact Finset.sum_boole (R := ℕ) _ _

theorem cube_hamming_permutation {n : ℕ} (x : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
    cubeHamming (fun i => x (e i)) = cubeHamming x := by
  rw [cube_hamming_eq_sum, cube_hamming_eq_sum]
  exact Equiv.sum_comp e (fun i => if x i then (1 : ℕ) else 0)

theorem cube_swap_as_permutation {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    cubeSwap x i j = fun k => x ((Equiv.swap i j) k) := by
  ext k
  simp only [cubeSwap, Equiv.swap_apply_def]
  split_ifs <;> rfl

theorem cube_swap_involution {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    cubeSwap (cubeSwap x i j) i j = x := by
  rw [cube_swap_as_permutation, cube_swap_as_permutation]
  ext k
  simp

def cubeSwapEquiv {n : ℕ} (i j : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := fun x => cubeSwap x i j
  invFun := fun x => cubeSwap x i j
  left_inv x := cube_swap_involution x i j
  right_inv x := cube_swap_involution x i j

theorem cube_hamming_swap {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    cubeHamming (cubeSwap x i j) = cubeHamming x := by
  rw [cube_swap_as_permutation, cube_hamming_permutation]

theorem nuWeight_swap {n : ℕ} (p : ℝ) (x : Fin n → Bool) (i j : Fin n) :
    nuWeight p n (cubeSwap x i j) = nuWeight p n x := by
  unfold nuWeight sliceWeight
  rw [cube_hamming_swap]

theorem cube_expect_swap {n : ℕ} (p : ℝ) (f : (Fin n → Bool) → ℝ) (i j : Fin n) :
    cubeExpect n (nuWeight p n) (fun x => f (cubeSwap x i j)) = cubeExpect n (nuWeight p n) f := by
  have he := (cubeSwapEquiv i j).sum_comp (fun x => nuWeight p n x*f x)
  simpa only [cubeExpect, cubeSwapEquiv, Equiv.coe_fn_mk, nuWeight_swap] using he

theorem cube_swap_flip_path {n : ℕ} (x : Fin n → Bool) (i j : Fin n) (h : x i ≠ x j) :
    cubeFlip (cubeSwap x i j) j = cubeFlip x i := by
  have hij : i ≠ j := by intro he; subst j; exact h rfl
  ext k
  by_cases hki : k=i
  · subst k
    cases hi : x i <;> cases hj : x j <;> simp_all [cubeFlip,cubeSwap]
  · by_cases hkj : k=j
    · subst k
      cases hi : x i <;> cases hj : x j <;> simp_all [cubeFlip,cubeSwap]
    · simp [cubeFlip,cubeSwap,hki,hkj]

theorem cube_swap_same_bits {n : ℕ} (x : Fin n → Bool) (i j : Fin n) (h : x i=x j) :
    cubeSwap x i j = x := by
  ext k
  by_cases hki : k=i
  · subst k; simpa [cubeSwap] using h.symm
  · by_cases hkj : k=j
    · subst k; simp [cubeSwap,hki,h]
    · simp [cubeSwap,hki,hkj]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
