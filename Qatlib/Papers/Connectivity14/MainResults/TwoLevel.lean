/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.Connectivity14.MainResults

variable {I : Type} [Fintype I] [DecidableEq I]

theorem matrix_exp_mulVec_of_eigen (A : Matrix I I ℂ) (u : QState I) (z : ℂ)
    (hu : A *ᵥ u = z • u) : NormedSpace.exp A *ᵥ u = Complex.exp z • u := by
  let L : Matrix I I ℂ →L[ℂ] QState I :=
    ((Matrix.mulVecBilin ℂ ℂ).flip u).toContinuousLinearMap
  have hp (n : ℕ) : A ^ n *ᵥ u = z ^ n • u := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hu, smul_smul]
      rw [pow_succ, mul_comm]
  have hm := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL L
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).smul_const u
  have he : (fun n => L ((n.factorial : ℂ)⁻¹ • A ^ n)) =
      (fun n => (((n.factorial : ℂ)⁻¹ • z ^ n) • u)) := by
    funext n
    change ((n.factorial : ℂ)⁻¹ • A ^ n) *ᵥ u = _
    rw [Matrix.smul_mulVec, hp, smul_smul]
    rfl
  rw [he] at hm
  rw [← Complex.exp_eq_exp_ℂ] at hs
  exact hm.unique hs

theorem hamiltonianEvolution_eigenvector (H : Matrix I I ℂ) (u : QState I) (ℓ t : ℝ)
    (hu : H *ᵥ u = (ℓ : ℂ) • u) :
    HamiltonianEvolution H t *ᵥ u = Complex.exp ((-Complex.I * (t : ℂ)) * (ℓ : ℂ)) • u := by
  unfold HamiltonianEvolution
  apply matrix_exp_mulVec_of_eigen
  rw [Matrix.smul_mulVec, hu, smul_smul]

def twoLevelH (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ), (d : ℂ); (d : ℂ), (c : ℂ)]

def twoKet0 : QState (Fin 2) := ![1, 0]

def twoKet1 : QState (Fin 2) := ![0, 1]

def twoPlus : QState (Fin 2) := ![1, 1]

def twoMinus : QState (Fin 2) := ![1, -1]

theorem twoLevelH_eigen_plus (c d : ℝ) :
    twoLevelH c d *ᵥ twoPlus = ((c + d : ℝ) : ℂ) • twoPlus := by
  ext i
  fin_cases i <;>
    simp [twoLevelH, twoPlus, Matrix.mulVec] <;> try ring

theorem twoLevelH_eigen_minus (c d : ℝ) :
    twoLevelH c d *ᵥ twoMinus = ((c - d : ℝ) : ℂ) • twoMinus := by
  ext i
  fin_cases i <;>
    simp [twoLevelH, twoMinus, Matrix.mulVec] <;> try ring

theorem twoKet1_decomp :
    twoKet1 = (2⁻¹ : ℂ) • (twoPlus - twoMinus) := by
  ext i
  fin_cases i <;> norm_num [twoKet1, twoPlus, twoMinus]

theorem twoLevel_evolution_mulVec (c d t : ℝ) :
    HamiltonianEvolution (twoLevelH c d) t *ᵥ twoKet1 =
      (2⁻¹ : ℂ) •
        (Complex.exp ((-Complex.I * (t : ℂ)) * ((c + d : ℝ) : ℂ)) • twoPlus -
         Complex.exp ((-Complex.I * (t : ℂ)) * ((c - d : ℝ) : ℂ)) • twoMinus) := by
  nth_rewrite 1 [twoKet1_decomp]
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub,
    hamiltonianEvolution_eigenvector _ _ _ _ (twoLevelH_eigen_plus c d),
    hamiltonianEvolution_eigenvector _ _ _ _ (twoLevelH_eigen_minus c d)]

theorem twoLevel_phase_combination (c d t : ℝ) :
    (2⁻¹ : ℂ) *
        (Complex.exp ((-Complex.I * (t : ℂ)) * ((c + d : ℝ) : ℂ)) -
         Complex.exp ((-Complex.I * (t : ℂ)) * ((c - d : ℝ) : ℂ))) =
      -Complex.I * Complex.exp ((-Complex.I * (t : ℂ)) * (c : ℂ)) *
        ((Real.sin (d * t) : ℝ) : ℂ) := by
  have ha : (-Complex.I * (t : ℂ)) * ((c + d : ℝ) : ℂ) =
      (-Complex.I * (t : ℂ)) * (c : ℂ) + ((-(d * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hb : (-Complex.I * (t : ℂ)) * ((c - d : ℝ) : ℂ) =
      (-Complex.I * (t : ℂ)) * (c : ℂ) + ((d * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ha, hb, Complex.exp_add, Complex.exp_add, Complex.exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem twoLevel_amplitude (c d t : ℝ) :
    (HamiltonianEvolution (twoLevelH c d) t *ᵥ twoKet1) 0 =
      -Complex.I * Complex.exp ((-Complex.I * (t : ℂ)) * (c : ℂ)) *
        ((Real.sin (d * t) : ℝ) : ℂ) := by
  rw [twoLevel_evolution_mulVec]
  have h0 : twoPlus 0 = (1 : ℂ) := rfl
  have h1 : twoMinus 0 = (1 : ℂ) := rfl
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h0, h1, mul_one]
  exact twoLevel_phase_combination c d t

theorem twoLevel_transition_prob (c d t : ℝ) :
    ‖(HamiltonianEvolution (twoLevelH c d) t *ᵥ twoKet1) 0‖ ^ 2 = Real.sin (d * t) ^ 2 := by
  rw [twoLevel_amplitude]
  have hexp : ‖Complex.exp ((-Complex.I * (t : ℂ)) * (c : ℂ))‖ = 1 := by
    rw [show (-Complex.I * (t : ℂ)) * (c : ℂ) = ((-(c * t) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, hexp, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem twoLevel_transition_prob_peak (c d : ℝ) (hd : 0 < d) :
    ‖(HamiltonianEvolution (twoLevelH c d) (Real.pi / (2 * d)) *ᵥ twoKet1) 0‖ ^ 2 = 1 := by
  rw [twoLevel_transition_prob]
  have harg : d * (Real.pi / (2 * d)) = Real.pi / 2 := by
    field_simp
  rw [harg, Real.sin_pi_div_two]
  norm_num

end Qatlib.Papers.Connectivity14.MainResults
