/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
import Qatlib.Papers.AnalogDigital96.MainResults.EvolutionBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.HamGrover03.MainResults

open Qatlib.Foundations.PureStateMath
set_option warningAsError false

abbrev marked {I : Type} [DecidableEq I] (m : I) : QState I :=
  Qatlib.Foundations.PureStateMath.Ket m

@[simp] theorem marked_apply {I : Type} [DecidableEq I] (m j : I) :
    marked m j = if j = m then 1 else 0 := rfl

@[simp] theorem marked_self {I : Type} [DecidableEq I] (m : I) : marked m m = 1 := by
  rw [marked_apply, if_pos rfl]

def uniformState (I : Type) [Fintype I] : QState I :=
  fun _ => ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ)

def rankOneProj {I : Type} [Fintype I] (v : QState I) : Matrix I I ℂ :=
  Matrix.vecMulVec v v

def oracleHamiltonian {I : Type} [Fintype I] [DecidableEq I] (m : I) : Matrix I I ℂ :=
  (1 : Matrix I I ℂ) - rankOneProj (marked m)

def initialHamiltonian (I : Type) [Fintype I] [DecidableEq I] : Matrix I I ℂ :=
  (1 : Matrix I I ℂ) - rankOneProj (uniformState I)

def analogHamiltonian (I : Type) [Fintype I] [DecidableEq I] (m : I) : Matrix I I ℂ :=
  initialHamiltonian I + oracleHamiltonian m

def analogContinuousAngle (N : ℕ) (t : ℝ) : ℝ :=
  t / Real.sqrt (N : ℝ)

theorem vecMulVec_mulVec {I : Type} [Fintype I] (w v : I → ℂ) (x : QState I) :
    Matrix.vecMulVec w v *ᵥ x = (v ⬝ᵥ x) • w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sum_uniform_sq (I : Type) [Fintype I] (hN : 0 < Fintype.card I) :
    ∑ i, uniformState I i * uniformState I i = 1 := by
  have hNpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (Fintype.card I : ℝ) ≠ 0 := by positivity
  have hreal : (Fintype.card I : ℝ) *
      ((Real.sqrt (Fintype.card I : ℝ))⁻¹ * (Real.sqrt (Fintype.card I : ℝ))⁻¹) = 1 := by
    field_simp
    rw [Real.sq_sqrt hNpos.le]
  have hsum : ∑ i, uniformState I i * uniformState I i =
      (((Fintype.card I : ℝ) *
        ((Real.sqrt (Fintype.card I : ℝ))⁻¹ *
          (Real.sqrt (Fintype.card I : ℝ))⁻¹)) : ℝ) := by
    simp only [uniformState]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum, hreal]
  norm_num

theorem ket_dot_add (I : Type) [Fintype I] [DecidableEq I] (m : I) :
    (marked m : I → ℂ) ⬝ᵥ (uniformState I + marked m) = uniformState I m + 1 := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single m (by intro b _ hb; rw [marked_apply, if_neg hb, zero_mul])
    (by simp)]
  rw [Finset.sum_eq_single m (by intro b _ hb; rw [marked_apply, if_neg hb, zero_mul])
    (by simp)]
  rw [marked_self, one_mul, mul_one]

theorem ket_dot_sub (I : Type) [Fintype I] [DecidableEq I] (m : I) :
    (marked m : I → ℂ) ⬝ᵥ (uniformState I - marked m) = uniformState I m - 1 := by
  simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single m (by intro b _ hb; rw [marked_apply, if_neg hb, zero_mul])
    (by simp)]
  rw [Finset.sum_eq_single m (by intro b _ hb; rw [marked_apply, if_neg hb, zero_mul])
    (by simp)]
  rw [marked_self, one_mul, mul_one]

theorem uniform_dot_add (I : Type) [Fintype I] [DecidableEq I] (m : I)
    (hN : 0 < Fintype.card I) :
    uniformState I ⬝ᵥ (uniformState I + marked m) = 1 + uniformState I m := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [sum_uniform_sq I hN]
  rw [Finset.sum_eq_single m (by intro b _ hb; rw [marked_apply, if_neg hb, mul_zero])
    (by simp)]
  rw [marked_self, mul_one]

theorem uniform_dot_sub (I : Type) [Fintype I] [DecidableEq I] (m : I)
    (hN : 0 < Fintype.card I) :
    uniformState I ⬝ᵥ (uniformState I - marked m) = 1 - uniformState I m := by
  simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [sum_uniform_sq I hN]
  rw [Finset.sum_eq_single m (by intro b _ hb; rw [marked_apply, if_neg hb, mul_zero])
    (by simp)]
  rw [marked_self, mul_one]

theorem analogH_mulVec_add (I : Type) [Fintype I] [DecidableEq I] (m : I)
    (hN : 0 < Fintype.card I) :
    analogHamiltonian I m *ᵥ (uniformState I + marked m) =
      ((((1 : ℝ) - (Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℝ)) : ℂ) •
        (uniformState I + marked m) := by
  unfold analogHamiltonian initialHamiltonian oracleHamiltonian rankOneProj
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
    vecMulVec_mulVec, vecMulVec_mulVec,
    uniform_dot_add I m hN, ket_dot_add I m]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.one_mulVec, uniformState]
  push_cast
  ring

theorem analogH_mulVec_sub (I : Type) [Fintype I] [DecidableEq I] (m : I)
    (hN : 0 < Fintype.card I) :
    analogHamiltonian I m *ᵥ (uniformState I - marked m) =
      ((((1 : ℝ) + (Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℝ)) : ℂ) •
        (uniformState I - marked m) := by
  unfold analogHamiltonian initialHamiltonian oracleHamiltonian rankOneProj
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
    vecMulVec_mulVec, vecMulVec_mulVec,
    uniform_dot_sub I m hN, ket_dot_sub I m]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.one_mulVec, uniformState]
  push_cast
  ring

theorem analog_rotation (I : Type) [Fintype I] [DecidableEq I] (m : I)
    (hN : 0 < Fintype.card I) (t : ℝ) :
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
        (fun _ => Complex.I • analogHamiltonian I m) 0 t *ᵥ uniformState I =
      Complex.exp (-(Complex.I * (t : ℂ))) •
        ((((Real.cos (t / Real.sqrt (Fintype.card I : ℝ)) : ℝ) : ℂ) • uniformState I) +
          ((Complex.I * ((Real.sin (t / Real.sqrt (Fintype.card I : ℝ)) : ℝ) : ℂ)) • marked m)) := by
  rw [Qatlib.Concepts.LchsSimulation.TimeOrdered.orderedEvolution_constant_hamiltonian,
    sub_zero]
  set r : ℝ := (Real.sqrt (Fintype.card I : ℝ))⁻¹ with hrdef
  have hNpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (Fintype.card I : ℝ) ≠ 0 := by positivity

  have hdecomp : uniformState I =
      (2⁻¹ : ℂ) • ((uniformState I + marked m) + (uniformState I - marked m)) := by
    ext i; simp [Pi.add_apply, Pi.sub_apply]; ring
  nth_rewrite 1 [hdecomp]
  rw [Matrix.mulVec_smul, Matrix.mulVec_add,
    Qatlib.Papers.AnalogDigital96.MainResults.hamiltonianEvolution_eigenvector
      _ _ _ _ (analogH_mulVec_add I m hN),
    Qatlib.Papers.AnalogDigital96.MainResults.hamiltonianEvolution_eigenvector
      _ _ _ _ (analogH_mulVec_sub I m hN)]

  have harg_plus :
      -Complex.I * (t : ℂ) *
          ((((1 : ℝ) - (Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℝ)) : ℂ) =
        -(Complex.I * (t : ℂ)) + (((t * r : ℝ)) : ℂ) * Complex.I := by
    simp only [hrdef]
    push_cast
    ring
  have harg_minus :
      -Complex.I * (t : ℂ) *
          ((((1 : ℝ) + (Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℝ)) : ℂ) =
        -(Complex.I * (t : ℂ)) + (((-(t * r) : ℝ)) : ℂ) * Complex.I := by
    simp only [hrdef]
    push_cast
    ring
  rw [harg_plus, harg_minus, Complex.exp_add, Complex.exp_add]

  have hmul (θ : ℝ) : Complex.exp (((θ : ℝ) : ℂ) * Complex.I) =
      ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using!
      Complex.exp_mul_I (x := ((θ : ℝ) : ℂ))
  have hmul_neg (θ : ℝ) : Complex.exp ((((-θ : ℝ)) : ℂ) * Complex.I) =
      ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    have h := hmul (-θ)
    simpa [Real.cos_neg, Real.sin_neg] using! h
  rw [hmul (t * r), hmul_neg (t * r)]
  have htheta : t * r = t / Real.sqrt (Fintype.card I : ℝ) := by
    rw [hrdef, div_eq_mul_inv]
  rw [htheta]

  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem analog_reaches_solution (I : Type) [Fintype I] [DecidableEq I] (m : I)
    (hN : 0 < Fintype.card I) :
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
        (fun _ => Complex.I • analogHamiltonian I m) 0
        ((Real.pi / 2) * Real.sqrt (Fintype.card I : ℝ)) *ᵥ uniformState I =
      Complex.exp (-(Complex.I *
        (((Real.pi / 2) * Real.sqrt (Fintype.card I : ℝ) : ℝ) : ℂ))) •
        (Complex.I • marked m) := by
  have hNpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (Fintype.card I : ℝ) ≠ 0 := by positivity
  have hangle : (Real.pi / 2) * Real.sqrt (Fintype.card I : ℝ) /
      Real.sqrt (Fintype.card I : ℝ) = Real.pi / 2 := by
    field_simp
  rw [analog_rotation I m hN, hangle]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem analog_angle_eq_grover (N : ℕ) (j : ℕ) :
    analogContinuousAngle N (2 * (j : ℝ)) = 2 * (j : ℝ) / Real.sqrt (N : ℝ) := by
  unfold analogContinuousAngle
  ring

theorem analog_continuous_at_T (N : ℕ) (hN : 0 < N) :
    analogContinuousAngle N ((Real.pi / 2) * Real.sqrt (N : ℝ)) = Real.pi / 2 := by
  unfold analogContinuousAngle
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  field_simp

end Qatlib.Papers.HamGrover03.MainResults
