/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ComplexOrder
namespace Qatlib.Concepts.FermionAlgebra.CarJordanWigner.WeightedModes
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

theorem weighted_anticommutator {A I J : Type*} [Ring A] [Algebra ℝ A]
    [Fintype I] [Fintype J] (a : I → A) (b : J → A) (v : I → ℝ) (w : J → ℝ) :
    (∑ i, v i • a i) * (∑ j, w j • b j) +
      (∑ j, w j • b j) * (∑ i, v i • a i) =
        ∑ i, ∑ j, (v i*w j) • (a i*b j+b j*a i) := by
  have hfirst : (∑ i, v i • a i) * (∑ j, w j • b j) =
      ∑ i, ∑ j, (v i*w j) • (a i*b j) := by
    rw [Fintype.sum_mul_sum]
    simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,mul_comm]
  have hsecond : (∑ j, w j • b j) * (∑ i, v i • a i) =
      ∑ i, ∑ j, (v i*w j) • (b j*a i) := by
    rw [Fintype.sum_mul_sum]
    simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
    rw [Finset.sum_comm]
  rw [hfirst,hsecond]
  simp only [smul_add,Finset.sum_add_distrib]

def lower {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ i, v i • annihilation i

def raise {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ i, v i • creation i

theorem raise_adjoint {n : ℕ} (v : Fin n → ℝ) : raise v = (lower v)ᴴ := by
  simp only [raise,lower,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(g1 n).2.1 i]
  simp

theorem mixed_car {n : ℕ} (v w : Fin n → ℝ) :
    lower v*raise w+raise w*lower v = (∑ i, v i*w i) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [lower,raise,weighted_anticommutator]
  simp_rw [fun i j => ((g1 n).1 i j).1]
  simp only [smul_ite,smul_zero]
  simp
  rw [Finset.sum_smul]

theorem lower_car {n : ℕ} (v w : Fin n → ℝ) :
    lower v*lower w+lower w*lower v = 0 := by
  rw [lower,lower,weighted_anticommutator]
  simp_rw [fun i j => ((g1 n).1 i j).2.1]
  simp

theorem raise_car {n : ℕ} (v w : Fin n → ℝ) :
    raise v*raise w+raise w*raise v = 0 := by
  rw [raise,raise,weighted_anticommutator]
  simp_rw [fun i j => ((g1 n).1 i j).2.2]
  simp

theorem lower_square {n : ℕ} (v : Fin n → ℝ) : lower v*lower v = 0 := by
  have h : (2 : ℝ) • (lower v*lower v) = 0 := by
    simpa only [two_smul] using! lower_car v v
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem raise_square {n : ℕ} (v : Fin n → ℝ) : raise v*raise v = 0 := by
  have h : (2 : ℝ) • (raise v*raise v) = 0 := by
    simpa only [two_smul] using! raise_car v v
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

def occupation {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ := raise v*lower v

theorem occupation_idempotent {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i^2 = 1) :
    occupation v*occupation v = occupation v := by
  have hcar : lower v*raise v+raise v*lower v = 1 := by
    simpa only [← pow_two,hv,one_smul] using! mixed_car v v
  have hl := lower_square v
  have hr := raise_square v
  have heq : lower v*raise v = 1-raise v*lower v := eq_sub_of_add_eq hcar
  unfold occupation
  calc
    _ = raise v*(lower v*raise v)*lower v := by noncomm_ring
    _ = raise v*(1-raise v*lower v)*lower v := by rw [heq]
    _ = raise v*lower v-(raise v*raise v)*(lower v*lower v) := by noncomm_ring
    _ = _ := by rw [hl,hr]; simp

theorem occupation_hermitian {n : ℕ} (v : Fin n → ℝ) : (occupation v).IsHermitian := by
  rw [occupation,raise_adjoint]
  exact Matrix.isHermitian_conjTranspose_mul_self _

theorem occupation_positive {n : ℕ} (v : Fin n → ℝ) : (occupation v).PosSemidef := by
  rw [occupation,raise_adjoint]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def reflection {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ := 1-(2 : ℝ) • occupation v

theorem reflection_hermitian {n : ℕ} (v : Fin n → ℝ) : (reflection v).IsHermitian := by
  exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      ((occupation_hermitian v).smul (by norm_num : IsSelfAdjoint (2 : ℝ)))

theorem reflection_square {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i^2 = 1) :
    reflection v*reflection v = 1 := by
  have h := occupation_idempotent v hv
  unfold reflection
  have he : (1-(2 : ℝ) • occupation v)*(1-(2 : ℝ) • occupation v) =
      1+(4 : ℝ) • (occupation v*occupation v-occupation v) := by
    simp only [show (2 : ℝ) = 1+1 by norm_num,
      show (4 : ℝ) = 1+1+1+1 by norm_num,add_smul,one_smul]
    noncomm_ring
  rw [he,h,sub_self,smul_zero,add_zero]

theorem reflection_unitary {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i^2 = 1) :
    reflection v ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change reflection v*(reflection v)ᴴ = 1
  rw [(reflection_hermitian v).eq]
  exact reflection_square v hv

end Qatlib.Concepts.FermionAlgebra.CarJordanWigner.WeightedModes
