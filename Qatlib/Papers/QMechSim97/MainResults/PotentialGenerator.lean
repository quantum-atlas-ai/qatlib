/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.BlochBranch
import Qatlib.Papers.QMechSim97.MainResults.PotentialWord
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.PotentialGenerator

open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
open Qatlib.Papers.QMechSim97.MainResults.BlochBranch
open Qatlib.Papers.QMechSim97.MainResults.PotentialWord
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Matrix Complex

def externalPhaseAngle (eps U : ℝ) : ℝ := eps ^ 2 * U

def externalPhaseOn {N : ℕ} (i : Fin N) (θ : ℝ) : Matrix (Reg N) (Reg N) ℂ :=
  Matrix.diagonal (fun x => if x i then Complex.exp (-θ * I) else 1)

theorem externalPhaseOn_apply {N : ℕ} (i : Fin N) (θ : ℝ)
    (ψ : QState (Reg N)) (x : Reg N) :
    ApplyGate (externalPhaseOn i θ) ψ x =
      (if x i then Complex.exp (-θ * I) else 1) * ψ x := by
  simp [externalPhaseOn, ApplyGate, Matrix.mulVec_diagonal]

theorem externalPhase_normSq (θ : ℝ) :
    Complex.normSq (Complex.exp (-θ * I)) = 1 := by
  have h : (-θ * I : ℂ) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [h]
  exact normSq_exp_pure_imaginary (-θ)

theorem externalPhaseOn_unitary {N : ℕ} (i : Fin N) (θ : ℝ) :
    externalPhaseOn i θ ∈ Matrix.unitaryGroup (Reg N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold externalPhaseOn
  apply diagonal_phase_unitary
  intro x
  by_cases hx : x i
  · rw [if_pos hx]; exact externalPhase_normSq θ
  · rw [if_neg hx]; exact Complex.normSq_one

theorem externalPhase_hasDerivAt (U : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(s * U) * I)) (-(U : ℂ) * I) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => (-(s * U) : ℝ)) (-U) 0 := by
    have hh : HasDerivAt (fun s : ℝ => s * U) U 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const U
    simpa using! hh.neg
  have h2 : HasDerivAt (fun s : ℝ => ((-(s * U) : ℝ) : ℂ)) ((-U : ℝ) : ℂ) 0 :=
    h1.ofReal_comp
  have h3 : HasDerivAt (fun s : ℝ => ((-(s * U) : ℝ) : ℂ) * I)
      (((-U : ℝ) : ℂ) * I) 0 := h2.mul_const I
  have h4 : HasDerivAt (fun s : ℝ => Complex.exp (((-(s * U) : ℝ) : ℂ) * I))
      (Complex.exp (((-(0 * U) : ℝ) : ℂ) * I) * ((((-U : ℝ) : ℂ) * I))) 0 :=
    (Complex.hasDerivAt_exp _).comp 0 h3
  simpa using h4

theorem combined_phase_generator (f : ℝ → ℂ) (c : ℂ) (U : ℝ)
    (hf : HasDerivAt f c 0) (h0 : f 0 = 1) :
    HasDerivAt (fun s => f s * Complex.exp (-(s * U) * I)) (c + (-(U : ℂ) * I)) 0 := by
  have hp := hf.mul (externalPhase_hasDerivAt U)
  simpa [h0] using! hp

theorem potential_schrodinger_identity (a b κ U : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    I * (-(I * (dispersionCoeff a b * κ ^ 2 + U))) =
      schrodingerCoeff (particleMass1D a b) * κ ^ 2 + U := by
  rw [schrodingerCoeff_mass a b ha hb]
  calc I * (-(I * (dispersionCoeff a b * κ ^ 2 + U)))
      = -((I * I) * (dispersionCoeff a b * κ ^ 2 + U)) := by ring
    _ = dispersionCoeff a b * κ ^ 2 + U := by rw [Complex.I_mul_I]; ring

theorem smooth_potential_generator (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    {N : ℕ} (i : Fin N) (U κ : ℂ) :
    externalPhaseOn i 0 ∈ Matrix.unitaryGroup (Reg N) ℂ ∧
    (∀ (ψ : QState (Reg N)) (x : Reg N),
      ApplyGate (externalPhaseOn i 0) ψ x = ψ x) ∧
    (∀ (f : ℝ → ℂ) (c : ℂ), HasDerivAt f c 0 → f 0 = 1 →
      HasDerivAt (fun s => f s * Complex.exp (-(s * (U.re)) * I))
        (c + (-((U.re : ℝ) : ℂ) * I)) 0) ∧
    I * (-(I * (dispersionCoeff a b * κ ^ 2 + U))) =
      schrodingerCoeff (particleMass1D a b) * κ ^ 2 + U := by
  refine ⟨externalPhaseOn_unitary i 0, ?_, ?_, potential_schrodinger_identity a b κ U ha hb⟩
  · intro ψ x
    rw [externalPhaseOn_apply]
    simp
  · intro f c hf h0
    exact combined_phase_generator f c U.re hf h0

end Qatlib.Papers.QMechSim97.MainResults.PotentialGenerator
