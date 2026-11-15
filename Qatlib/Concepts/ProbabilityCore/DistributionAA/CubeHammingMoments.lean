/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceCoupling

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Computes the product-measure expectation of a coordinate indicator as the bias. -/
theorem cube_mu_bit_expect (p : ℝ) (n : ℕ) (i : Fin n) :
    cubeExpect n (muWeight p n) (fun x => if x i then (1 : ℝ) else 0) = p := by
  have he := cube_coordinate_monomial_expect (fun _ : Fin n => p) {i}
  have hm : cubeMonomial ({i} : Finset (Fin n)) = (fun x => if x i then (1 : ℝ) else 0) := by
    ext x
    simp [cubeMonomial]
  change cubeExpect n (muWeight p n) (cubeMonomial {i}) = _ at he
  rw [hm] at he
  simpa only [Finset.prod_singleton] using he

/-- Computes the product-measure expectation of two coordinate indicators, distinguishing equal
and distinct coordinates. -/
theorem cube_mu_bit_pair_expect (p : ℝ) (n : ℕ) (i j : Fin n) :
    cubeExpect n (muWeight p n) (fun x => (if x i then (1 : ℝ) else 0)*(if x j then (1 : ℝ) else 0)) =
      if i=j then p else p^2 := by
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    have hp : (fun x : Fin n → Bool => (if x i then (1 : ℝ) else 0)*(if x i then (1 : ℝ) else 0)) =
        (fun x => if x i then (1 : ℝ) else 0) := by ext x; cases x i <;> simp
    rw [hp,cube_mu_bit_expect]
  · rw [ite_eq_right hij]
    have he := cube_coordinate_monomial_expect (fun _ : Fin n => p) {i,j}
    have hm : cubeMonomial ({i,j} : Finset (Fin n)) =
        (fun x => (if x i then (1 : ℝ) else 0)*(if x j then (1 : ℝ) else 0)) := by
      ext x
      simp [cubeMonomial,Finset.prod_insert,hij]
    change cubeExpect n (muWeight p n) (cubeMonomial {i,j}) = _ at he
    rw [hm] at he
    simpa [hij,pow_two] using he

/-- Computes the mean Hamming weight under the product measure as dimension times bias. -/
theorem cube_mu_hamming_mean (p : ℝ) (n : ℕ) :
    cubeExpect n (muWeight p n) (fun x => (cubeHamming x : ℝ)) = (n : ℝ)*p := by
  have hp : (fun x : Fin n → Bool => (cubeHamming x : ℝ)) =
      (fun x => ∑ i : Fin n, if x i then (1 : ℝ) else 0) := by ext x; exact (cube_hamming_cast_sum x).symm
  rw [hp,cube_expect_sum]
  simp only [cube_mu_bit_expect,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Computes the second moment of Hamming weight under the product measure. -/
theorem cube_mu_hamming_second_moment (p : ℝ) (n : ℕ) :
    cubeExpect n (muWeight p n) (fun x => (cubeHamming x : ℝ)^2) =
      (n : ℝ)*p+((n : ℝ)^2-n)*p^2 := by
  have hp : (fun x : Fin n → Bool => (cubeHamming x : ℝ)^2) =
      (fun x => ∑ i : Fin n, ∑ j : Fin n,
        (if x i then (1 : ℝ) else 0)*(if x j then (1 : ℝ) else 0)) := by
    ext x
    rw [← cube_hamming_cast_sum,pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hp,cube_expect_sum]
  simp_rw [cube_expect_sum,cube_mu_bit_pair_expect]
  have hi (i : Fin n) : (∑ j : Fin n, if i=j then p else p^2) = p+((n : ℝ)-1)*p^2 := by
    have he (j : Fin n) : (if i=j then p else p^2) = p^2+(if i=j then p-p^2 else 0) := by
      split_ifs <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  simp_rw [hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Computes the Hamming-weight variance as dimension times bias times one minus bias. -/
theorem cube_mu_hamming_variance {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    cubeVar n (muWeight p n) (fun x => (cubeHamming x : ℝ)) = (n : ℝ)*p*(1-p) := by
  rw [cube_var_eq_second_moment_sub_sq n (muWeight_cubeWeight hp0 hp1 n),
    cube_mu_hamming_mean,cube_mu_hamming_second_moment]
  ring

end Qatlib.Concepts.ProbabilityCore.DistributionAA
