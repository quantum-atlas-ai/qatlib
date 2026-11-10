/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.TITCMTReport98.MainResults.PhysicalEvolution
open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.PureStateMath

def spinHamiltonian (h gamma : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(h : ℂ), -(gamma : ℂ); -(gamma : ℂ), (h : ℂ)]

theorem spinHamiltonian_hermitian (h gamma : ℝ) : (spinHamiltonian h gamma).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinHamiltonian, Matrix.conjTranspose]

theorem spinHamiltonian_continuous (h gamma : ℝ → ℝ)
    (hh : Continuous h) (hg : Continuous gamma) :
    Continuous (fun t => spinHamiltonian (h t) (gamma t)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [spinHamiltonian] <;> fun_prop

def spinEvolution (h gamma : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  orderedEvolution (fun u => Complex.I • spinHamiltonian (h u) (gamma u)) s t

theorem spinEvolution_self (h gamma : ℝ → ℝ) (s : ℝ) : spinEvolution h gamma s s = 1 :=
  orderedEvolution_self _ _

theorem spinEvolution_hasDerivAt (h gamma : ℝ → ℝ)
    (hh : Continuous h) (hg : Continuous gamma) (s t : ℝ) :
    HasDerivAt (spinEvolution h gamma s)
      (-((Complex.I • spinHamiltonian (h t) (gamma t)) * spinEvolution h gamma s t)) t := by
  have hc : Continuous (fun u => Complex.I • spinHamiltonian (h u) (gamma u)) := by
    have := spinHamiltonian_continuous h gamma hh hg
    fun_prop
  exact orderedEvolution_hasDerivAt _ hc s t

theorem spinEvolution_unitary (h gamma : ℝ → ℝ)
    (hh : Continuous h) (hg : Continuous gamma) (s t : ℝ) :
    spinEvolution h gamma s t ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  ordered_evolution_hermitian_unitary _ _ (spinHamiltonian_continuous h gamma hh hg)
    (fun u => spinHamiltonian_hermitian (h u) (gamma u)) s t

def spinState (h gamma : ℝ → ℝ) (s : ℝ) (psi : QState (Fin 2)) (t : ℝ) : QState (Fin 2) :=
  ApplyGate (spinEvolution h gamma s t) psi

theorem spinState_normalized (h gamma : ℝ → ℝ)
    (hh : Continuous h) (hg : Continuous gamma) (s t : ℝ)
    (psi : QState (Fin 2)) (hn : Normalized psi) : Normalized (spinState h gamma s psi t) :=
  normalized_applyGate (spinEvolution_unitary h gamma hh hg s t) hn

theorem spinState_Born_pair (h gamma : ℝ → ℝ)
    (hh : Continuous h) (hg : Continuous gamma) (s t : ℝ)
    (psi : QState (Fin 2)) (hn : Normalized psi) :
    ‖spinState h gamma s psi t 0‖ ^ 2 + ‖spinState h gamma s psi t 1‖ ^ 2 = 1 := by
  simpa only [Normalized, Fin.sum_univ_two] using! spinState_normalized h gamma hh hg s t psi hn

theorem linear_schedule_continuous (h c : ℝ) :
    Continuous (fun t => spinHamiltonian h (-c * t)) :=
  spinHamiltonian_continuous _ _ continuous_const (by fun_prop)

def sqrtClockHamiltonian (h c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinHamiltonian (2 * h * s) (2 * c)

theorem sqrtClock_continuous (h c : ℝ) : Continuous (sqrtClockHamiltonian h c) :=
  spinHamiltonian_continuous _ _ (by fun_prop) continuous_const

theorem sqrtClock_identity (h c s : ℝ) (hs : 0 < s) :
    sqrtClockHamiltonian h c s =
      (2 * (s : ℂ)) • spinHamiltonian h (c / Real.sqrt (s ^ 2)) := by
  rw [Real.sqrt_sq hs.le]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sqrtClockHamiltonian, spinHamiltonian]
  all_goals field_simp [show (s : ℂ) ≠ 0 by exact_mod_cast hs.ne']

def inverseClockHamiltonian (h c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinHamiltonian (h * Real.exp s) c

theorem inverseClock_continuous (h c : ℝ) : Continuous (inverseClockHamiltonian h c) :=
  spinHamiltonian_continuous _ _ (by fun_prop) continuous_const

theorem inverseClock_identity (h c s : ℝ) :
    inverseClockHamiltonian h c s =
      (Real.exp s : ℂ) • spinHamiltonian h (c / Real.exp s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inverseClockHamiltonian, spinHamiltonian]
  all_goals field_simp [show (Real.exp s : ℂ) ≠ 0 by exact_mod_cast Real.exp_ne_zero s]

theorem sqrtClock_physical_derivative (h c t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun u => spinEvolution (fun s => 2 * h * s) (fun _ => 2 * c) 0 (Real.sqrt u))
      (-((Complex.I • spinHamiltonian h (c / Real.sqrt t)) *
        spinEvolution (fun s => 2 * h * s) (fun _ => 2 * c) 0 (Real.sqrt t))) t := by
  have hd := spinEvolution_hasDerivAt (fun s => 2 * h * s) (fun _ => 2 * c)
    (by fun_prop) continuous_const 0 (Real.sqrt t)
  have hc := hd.scomp t (Real.hasDerivAt_sqrt ht.ne')
  convert! hc using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHamiltonian, Matrix.vecMul, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  all_goals field_simp [show (Real.sqrt t : ℂ) ≠ 0 by exact_mod_cast (Real.sqrt_pos.mpr ht).ne']

theorem inverseClock_physical_derivative (h c t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun u => spinEvolution (fun s => h * Real.exp s) (fun _ => c) 0 (Real.log u))
      (-((Complex.I • spinHamiltonian h (c / t)) *
        spinEvolution (fun s => h * Real.exp s) (fun _ => c) 0 (Real.log t))) t := by
  have hd := spinEvolution_hasDerivAt (fun s => h * Real.exp s) (fun _ => c)
    (by fun_prop) continuous_const 0 (Real.log t)
  have hc := hd.scomp t (Real.hasDerivAt_log ht.ne')
  convert! hc using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHamiltonian, Matrix.vecMul, dotProduct, Fin.sum_univ_two, smul_eq_mul,
        Real.exp_log ht]
  all_goals field_simp [show (t : ℂ) ≠ 0 by exact_mod_cast ht.ne']

theorem sqrtClock_initial_state (h c : ℝ) (psi : QState (Fin 2)) :
    spinState (fun s => 2 * h * s) (fun _ => 2 * c) 0 psi (Real.sqrt 0) = psi := by
  simp [spinState, spinEvolution, applyGate_one]

theorem spinState_ground_readout_range (h gamma : ℝ → ℝ)
    (hh : Continuous h) (hg : Continuous gamma) (s t : ℝ)
    (psi : QState (Fin 2)) (hn : Normalized psi) :
    0 ≤ MeasureProb (spinState h gamma s psi t) {0} ∧
      MeasureProb (spinState h gamma s psi t) {0} ≤ 1 := by
  have hp := spinState_Born_pair h gamma hh hg s t psi hn
  simp only [MeasureProb, Finset.sum_singleton, BornProb]
  exact ⟨sq_nonneg _, by nlinarith [sq_nonneg ‖spinState h gamma s psi t 1‖]⟩

end Qatlib.Papers.TITCMTReport98.MainResults.PhysicalEvolution
