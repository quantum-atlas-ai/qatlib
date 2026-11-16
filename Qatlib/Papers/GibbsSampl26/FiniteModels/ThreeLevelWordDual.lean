/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCellMatrices

@[expose] public section


/-!
# An inverse-filter lower bound for all length-two recovery coefficients

Every literal filtered word is evaluated internally. The finite sum proof
allows arbitrary complex coefficients and any finite family of words.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelWordDual

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

/-- The linear functional is evaluated in the computational basis 00,01,10,11. -/
def dual : Operator 4 →ₗ[ℂ] ℂ where
  toFun X := X 1 3 + 2 * X 2 3 + X 3 1 + 2 * X 3 2
  map_add' X Y := by simp only [Matrix.add_apply]; ring
  map_smul' z X := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def letterDual : Fin 6 → ℂ := ![2, 0, 0, 4, 0, 0]

def pairDual : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,0,0,0,0,-2;
     0,0,2*Complex.I,0,0,0;
     0,-2*Complex.I,0,-4,0,0;
     0,0,-4,0,0,0;
     0,0,0,0,0,4*Complex.I;
     -2,0,0,0,-4*Complex.I,0]

local macro "cell_arith" : tactic => `(tactic|
  norm_num [Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.normSq_apply, Complex.conj_re, Complex.conj_im] <;> ring)


/-- Psi unit for the stated finite source data. -/
theorem psi_unit : (∑ i : Fin 4, star (psi i) * psi i) = (1:ℂ) := by
  simp [psi, Fin.sum_univ_succ]
  cell_arith

/-- P One mul self for the stated finite source data. -/
theorem pOne_mul_self : pOne * pOne = pOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pOne, Matrix.mul_apply, Fin.sum_univ_succ]

/-- P Two mul self for the stated finite source data. -/
theorem pTwo_mul_self : pTwo * pTwo = pTwo := by
  ext i j
  simp only [Matrix.mul_apply, pTwo]
  calc
    (∑ k, psi i * star (psi k) * (psi k * star (psi j))) =
        (psi i * star (psi j)) * (∑ k : Fin 4, star (psi k) * psi k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [psi_unit, mul_one]

/-- P One mul p Two for the stated finite source data. -/
theorem pOne_mul_pTwo : pOne * pTwo = 0 := by
  ext i j
  fin_cases i <;>
    simp [pOne, pTwo, psi, Matrix.mul_apply, Fin.sum_univ_succ]

/-- P Two mul p One for the stated finite source data. -/
theorem pTwo_mul_pOne : pTwo * pOne = 0 := by
  ext i j
  fin_cases j <;>
    simp [pOne, pTwo, psi, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Projectors mul for the stated finite source data. -/
theorem projectors_mul (i j : Fin 3) :
    projectors i * projectors j = if i=j then projectors i else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [projectors, pZero, sub_mul, mul_sub, pOne_mul_self,
      pTwo_mul_self, pOne_mul_pTwo, pTwo_mul_pOne]

/-- Projectors hermitian for the stated finite source data. -/
theorem projectors_hermitian (i : Fin 3) : (projectors i).IsHermitian := by
  change (projectors i)ᴴ = projectors i
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [projectors, pZero, pOne, pTwo_entries, Matrix.conjTranspose_apply]

/-- Projectors sum for the stated finite source data. -/
theorem projectors_sum : (∑ i : Fin 3, projectors i) = 1 := by
  simp [projectors, pZero, Fin.sum_univ_succ]

/-- Dimensionless spectral levels, including all degeneracies and both signs. -/
def energies (x c : ℝ) : Fin 3 → ℝ := ![0, x, c*x]

def cellHamiltonian (s x c : ℝ) : Operator 4 :=
  ∑ i : Fin 3, ((s + energies x c i):ℂ) • projectors i

/-- Cell Hamiltonian mul projector for the stated finite source data. -/
theorem cellHamiltonian_mul_projector (s x c : ℝ) (j : Fin 3) :
    cellHamiltonian s x c * projectors j =
      ((s + energies x c j):ℂ) • projectors j := by
  classical
  simp only [cellHamiltonian, Finset.sum_mul, Matrix.smul_mul, projectors_mul]
  simp [smul_ite]

/-- Cell Hamiltonian formula for the stated finite source data. -/
theorem cellHamiltonian_formula (s x c : ℝ) :
    cellHamiltonian s x c =
      (s:ℂ) • (1:Operator 4) + (x:ℂ) • pOne + ((c*x):ℂ) • pTwo := by
  simp [cellHamiltonian, energies, projectors, pZero, Fin.sum_univ_succ]
  module

/-- The actual Gaussian spectral multiplier, without replacing any source. -/
def gaussianSource (x c : ℝ) (k : Fin 6) : Operator 4 :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (Real.exp (-((energies x c i - energies x c j)^2)/8):ℂ) •
      (projectors i * source k * projectors j)

/-- Gaussian weights for the stated finite source data. -/
theorem gaussian_weights (x c : ℝ) (i j : Fin 3) :
    (Real.exp (-((energies x c i - energies x c j)^2)/8):ℂ) =
      weights (Real.exp (-x^2/8)) (Real.exp (-(c*x)^2/8))
        (Real.exp (-((c-1)*x)^2/8)) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [energies, weights] <;> congr 2 <;> ring

/-- Gaussian Source eq filtered for the stated finite source data. -/
theorem gaussianSource_eq_filtered (x c : ℝ) (k : Fin 6) :
    gaussianSource x c k =
      filtered (Real.exp (-x^2/8)) (Real.exp (-(c*x)^2/8))
        (Real.exp (-((c-1)*x)^2/8)) k := by
  simp only [gaussianSource, filtered, gaussian_weights]

/-- Gaussian evenly spaced eq for the stated finite source data. -/
theorem gaussian_evenly_spaced_eq (x : ℝ) (k : Fin 6) :
    gaussianSource x 2 k =
      filtered (Real.exp (-x^2/8)) ((Real.exp (-x^2/8))^4)
        (Real.exp (-x^2/8)) k := by
  have ht : Real.exp (-(2*x)^2/8) = (Real.exp (-x^2/8))^4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [gaussianSource_eq_filtered, ht]
  norm_num


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelWordDual
