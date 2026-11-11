/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.Tactic

/-!
# Real weighted fermionic modes

`lower` and `raise` form real linear combinations of the mode annihilation and creation
operators. Their mixed anticommutator is the real coefficient inner product times the identity,
while any two lowering combinations or two raising combinations anticommute, as consequences of
the canonical relations [BravyiKitaev2002].

The weighted occupation operator is Hermitian and positive semidefinite. For a unit coefficient
vector it is idempotent, and `reflection` gives the associated Hermitian involution and unitary.

## Main statements

* `mixed_car`: the mixed anticommutator equals the coefficient inner product times the identity.
* `occupation_idempotent`: a normalized real mode vector defines an idempotent occupation
  operator.
* `reflection_unitary`: the reflection associated with a normalized real mode vector is unitary.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

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

/-- The anticommutator of two finite real linear combinations expands into the doubly weighted
sum of the pairwise anticommutators. -/
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

/-- The real-weighted sum of the fermionic annihilation operators. -/
def lower {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ i, v i • annihilation i

/-- The real-weighted sum of the fermionic creation operators. -/
def raise {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ i, v i • creation i

/-- For real coefficients, the weighted creation operator is the adjoint of the weighted
annihilation operator. -/
theorem raise_adjoint {n : ℕ} (v : Fin n → ℝ) : raise v = (lower v)ᴴ := by
  simp only [raise,lower,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(g1 n).2.1 i]
  simp

/-- The mixed weighted anticommutator equals the real coefficient inner product times the
identity. -/
theorem mixed_car {n : ℕ} (v w : Fin n → ℝ) :
    lower v*raise w+raise w*lower v = (∑ i, v i*w i) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [lower,raise,weighted_anticommutator]
  simp_rw [fun i j => ((g1 n).1 i j).1]
  simp only [smul_ite,smul_zero]
  simp
  rw [Finset.sum_smul]

/-- Any two real-weighted annihilation combinations have zero anticommutator. -/
theorem lower_car {n : ℕ} (v w : Fin n → ℝ) :
    lower v*lower w+lower w*lower v = 0 := by
  rw [lower,lower,weighted_anticommutator]
  simp_rw [fun i j => ((g1 n).1 i j).2.1]
  simp

/-- Any two real-weighted creation combinations have zero anticommutator. -/
theorem raise_car {n : ℕ} (v w : Fin n → ℝ) :
    raise v*raise w+raise w*raise v = 0 := by
  rw [raise,raise,weighted_anticommutator]
  simp_rw [fun i j => ((g1 n).1 i j).2.2]
  simp

/-- Every real-weighted annihilation combination has square zero. -/
theorem lower_square {n : ℕ} (v : Fin n → ℝ) : lower v*lower v = 0 := by
  have h : (2 : ℝ) • (lower v*lower v) = 0 := by
    simpa only [two_smul] using! lower_car v v
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- Every real-weighted creation combination has square zero. -/
theorem raise_square {n : ℕ} (v : Fin n → ℝ) : raise v*raise v = 0 := by
  have h : (2 : ℝ) • (raise v*raise v) = 0 := by
    simpa only [two_smul] using! raise_car v v
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- The weighted occupation matrix `raise v * lower v`. -/
def occupation {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ := raise v*lower v

/-- The weighted occupation matrix is idempotent when the real coefficients have sum of squares
equal to one. -/
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

/-- The weighted occupation matrix is Hermitian for every real coefficient vector. -/
theorem occupation_hermitian {n : ℕ} (v : Fin n → ℝ) : (occupation v).IsHermitian := by
  rw [occupation,raise_adjoint]
  exact Matrix.isHermitian_conjTranspose_mul_self _

/-- The weighted occupation matrix is positive semidefinite for every real coefficient vector. -/
theorem occupation_positive {n : ℕ} (v : Fin n → ℝ) : (occupation v).PosSemidef := by
  rw [occupation,raise_adjoint]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The matrix `1 - (2 : ℝ) • occupation v` associated with a real weighted mode. -/
def reflection {n : ℕ} (v : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ := 1-(2 : ℝ) • occupation v

/-- The weighted-mode reflection matrix is Hermitian for every real coefficient vector. -/
theorem reflection_hermitian {n : ℕ} (v : Fin n → ℝ) : (reflection v).IsHermitian := by
  exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      ((occupation_hermitian v).smul (by norm_num : IsSelfAdjoint (2 : ℝ)))

/-- For a real coefficient vector of squared norm one, the weighted-mode reflection has square
equal to the identity. -/
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

/-- For a real coefficient vector of squared norm one, the weighted-mode reflection is unitary. -/
theorem reflection_unitary {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i^2 = 1) :
    reflection v ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change reflection v*(reflection v)ᴴ = 1
  rw [(reflection_hermitian v).eq]
  exact reflection_square v hv

end Qatlib.Concepts.FermionAlgebra.CarJordanWigner.WeightedModes
