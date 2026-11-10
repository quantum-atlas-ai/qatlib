/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSymmetry
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

def cubePermute {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => x (e i)

def cubePermuteEquiv {n : ℕ} (e : Equiv.Perm (Fin n)) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := cubePermute e
  invFun := cubePermute e.symm
  left_inv x := by ext i; simp [cubePermute]
  right_inv x := by ext i; simp [cubePermute]

theorem cube_expect_permutation {n : ℕ} (p : ℝ) (e : Equiv.Perm (Fin n)) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (nuWeight p n) (fun x => f (cubePermute e x)) = cubeExpect n (nuWeight p n) f := by
  have hw (x : Fin n → Bool) : nuWeight p n (cubePermute e x) = nuWeight p n x := by
    unfold nuWeight sliceWeight cubePermute
    rw [cube_hamming_permutation]
  have he := Equiv.sum_comp (cubePermuteEquiv e) (fun x => nuWeight p n x*f x)
  simpa only [cubeExpect,cubePermuteEquiv,Equiv.coe_fn_mk,hw] using he

theorem cube_same_hamming_permutation {n : ℕ} (x y : Fin n → Bool) (h : cubeHamming x=cubeHamming y) :
    ∃ e : Equiv.Perm (Fin n), cubePermute e x=y := by
  have hc : Fintype.card {i : Fin n // y i=true} = Fintype.card {i : Fin n // x i=true} := by
    simpa only [Fintype.card_subtype,cubeHamming] using h.symm
  let e := (Fintype.equivOfCardEq hc).extendSubtype
  refine ⟨e, ?_⟩
  ext i
  by_cases hi : y i=true
  · change x (e i)=y i
    rw [hi]
    exact (Fintype.equivOfCardEq hc).extendSubtype_mem i hi
  · have he := (Fintype.equivOfCardEq hc).extendSubtype_not_mem i hi
    change x (e i) ≠ true at he
    change x (e i)=y i
    cases hx : x (e i) <;> cases hy : y i <;> simp_all

def cubePermutationMean {n : ℕ} (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ e : Equiv.Perm (Fin n), f (cubePermute e x)

theorem cube_permutation_mean_invariant {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (e : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    cubePermutationMean f (cubePermute e x)=cubePermutationMean f x := by
  unfold cubePermutationMean
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft e) (fun r : Equiv.Perm (Fin n) => f (cubePermute r x))
  simpa only [Equiv.coe_mulLeft,Equiv.Perm.mul_apply,cubePermute] using! he

theorem cube_permutation_mean_eq_expect {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) (hx : cubeHamming x=Nat.floor (p*n)) :
    cubePermutationMean f x=cubeExpect n (nuWeight p n) f := by
  have hw := nuWeight_cubeWeight hp0 hp1 n
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hconst (y : Fin n → Bool) (hy : cubeHamming y=Nat.floor (p*n)) :
      cubePermutationMean f y=cubePermutationMean f x := by
    obtain ⟨e,he⟩ := cube_same_hamming_permutation x y (hx.trans hy.symm)
    rw [← he,cube_permutation_mean_invariant]
  have havg : cubeExpect n (nuWeight p n) (cubePermutationMean f)=cubeExpect n (nuWeight p n) f := by
    unfold cubePermutationMean
    rw [cube_expect_const_mul,cube_expect_sum]
    simp_rw [cube_expect_permutation]
    simp [hc]
  rw [← havg]
  symm
  calc
    _ = cubeExpect n (nuWeight p n) (fun _ => cubePermutationMean f x) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : cubeHamming y=Nat.floor (p*n)
      · rw [hconst y hy]
      · simp [nuWeight,sliceWeight,hy]
    _ = cubePermutationMean f x := by simp [cubeExpect,← Finset.sum_mul,hw.2]

theorem cube_permutation_pair_energy {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (Fin n → Bool) → ℝ) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
      ∑ e : Equiv.Perm (Fin n), cubeExpect n (nuWeight p n) (fun x => (f x-f (cubePermute e x))^2) =
      2*cubeVar n (nuWeight p n) f := by
  let c := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hc : c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ)=1 :=
      inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  have hw := nuWeight_cubeWeight hp0 hp1 n
  have hcross : c*(∑ e : Equiv.Perm (Fin n), cubeExpect n (nuWeight p n) (fun x => f x*f (cubePermute e x))) =
      (cubeExpect n (nuWeight p n) f)^2 := by
    rw [← cube_expect_sum,← cube_expect_const_mul]
    have hpnt (x : Fin n → Bool) : nuWeight p n x*(c*∑ e : Equiv.Perm (Fin n), f x*f (cubePermute e x)) =
        nuWeight p n x*(f x*cubeExpect n (nuWeight p n) f) := by
      by_cases hx : cubeHamming x=Nat.floor (p*n)
      · rw [← Finset.mul_sum,show c*(f x*∑ e : Equiv.Perm (Fin n), f (cubePermute e x)) = f x*cubePermutationMean f x by
          dsimp [c,cubePermutationMean]; ring]
        rw [cube_permutation_mean_eq_expect hp0 hp1 f x hx]
      · simp [nuWeight,sliceWeight,hx]
    change (∑ x, _) = _
    simp_rw [hpnt]
    rw [show (∑ x, nuWeight p n x*(f x*cubeExpect n (nuWeight p n) f)) =
        cubeExpect n (nuWeight p n) f*cubeExpect n (nuWeight p n) f by
      unfold cubeExpect; simp_rw [← mul_assoc]; rw [← Finset.sum_mul]]
    ring
  have he (e : Equiv.Perm (Fin n)) : cubeExpect n (nuWeight p n) (fun x => (f x-f (cubePermute e x))^2) =
      2*cubeExpect n (nuWeight p n) (fun x => f x^2)-
        2*cubeExpect n (nuWeight p n) (fun x => f x*f (cubePermute e x)) := by
    have hre (x) :
        (f x-f (cubePermute e x))^2 = f x^2+f (cubePermute e x)^2-2*(f x*f (cubePermute e x)) := by
          ring
    simp_rw [hre]
    rw [cube_expect_sub,cube_expect_add,cube_expect_const_mul,
      cube_expect_permutation p e (fun x => f x^2)]
    ring
  simp_rw [he]
  change c*(∑ e : Equiv.Perm (Fin n), _) = _
  rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,nsmul_eq_mul]
  simp only [Finset.card_univ]
  rw [cube_var_eq_second_moment_sub_sq n hw f]
  calc
    _ = 2*(c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ))*cubeExpect n (nuWeight p n) (fun x => f x^2)-
        2*(c*∑ e : Equiv.Perm (Fin n), cubeExpect n (nuWeight p n) (fun x => f x*f (cubePermute e x))) := by ring
    _ = _ := by rw [hc,hcross]; ring

end Qatlib.Concepts.ProbabilityCore.DistributionAA
