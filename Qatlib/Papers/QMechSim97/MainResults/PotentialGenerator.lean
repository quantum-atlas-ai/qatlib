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

/-!
# External potential phase generators

Defines the scaled angle `externalPhaseAngle` and the diagonal occupation-dependent operator
`externalPhaseOn` for the negative potential phase in [BoghosianTaylor1998]. Unitarity,
amplitude formulas, and derivatives at zero describe how multiplication by this phase adds the
potential term to a scalar generator.

## Main statements

* `potential_schrodinger_identity`: For nonzero collision parameters, multiplying the frequency
  expression by `I` gives the mass-based kinetic coefficient plus the potential term.
* `smooth_potential_generator`: Collects the identity action and unitarity at zero phase, the
  derivative rule for adding the real part of the potential, and the mass-based Schrödinger
  coefficient identity [BoghosianTaylor1998].

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

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

/-- The external potential phase angle `eps ^ 2 * U` at lattice scale `eps`. -/
def externalPhaseAngle (eps U : ℝ) : ℝ := eps ^ 2 * U

/-- The diagonal operator multiplying a basis state by `exp (-θ * I)` when occupation bit `i` is
true, and by one otherwise. -/
def externalPhaseOn {N : ℕ} (i : Fin N) (θ : ℝ) : Matrix (Reg N) (Reg N) ℂ :=
  Matrix.diagonal (fun x => if x i then Complex.exp (-θ * I) else 1)

/-- Applying `externalPhaseOn i θ` multiplies each amplitude by the phase selected by occupation
bit `i`. -/
theorem externalPhaseOn_apply {N : ℕ} (i : Fin N) (θ : ℝ)
    (ψ : QState (Reg N)) (x : Reg N) :
    ApplyGate (externalPhaseOn i θ) ψ x =
      (if x i then Complex.exp (-θ * I) else 1) * ψ x := by
  simp [externalPhaseOn, ApplyGate, Matrix.mulVec_diagonal]

/-- The negative potential phase `exp (-θ * I)` has squared modulus one for real `θ`. -/
theorem externalPhase_normSq (θ : ℝ) :
    Complex.normSq (Complex.exp (-θ * I)) = 1 := by
  have h : (-θ * I : ℂ) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [h]
  exact normSq_exp_pure_imaginary (-θ)

/-- The occupation-dependent external potential phase operator is unitary. -/
theorem externalPhaseOn_unitary {N : ℕ} (i : Fin N) (θ : ℝ) :
    externalPhaseOn i θ ∈ Matrix.unitaryGroup (Reg N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold externalPhaseOn
  apply diagonal_phase_unitary
  intro x
  by_cases hx : x i
  · rw [if_pos hx]; exact externalPhase_normSq θ
  · rw [if_neg hx]; exact Complex.normSq_one

/-- The phase `exp (-(s * U) * I)` has derivative `-U * I` at zero. -/
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

/-- Multiplying a function with value one and derivative `c` at zero by the negative potential
phase changes its derivative to `c - U * I`. -/
theorem combined_phase_generator (f : ℝ → ℂ) (c : ℂ) (U : ℝ)
    (hf : HasDerivAt f c 0) (h0 : f 0 = 1) :
    HasDerivAt (fun s => f s * Complex.exp (-(s * U) * I)) (c + (-(U : ℂ) * I)) 0 := by
  have hp := hf.mul (externalPhase_hasDerivAt U)
  simpa [h0] using! hp

/-- For nonzero collision parameters, multiplying the frequency expression by `I` gives the
mass-based kinetic coefficient plus the potential term. -/
theorem potential_schrodinger_identity (a b κ U : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    I * (-(I * (dispersionCoeff a b * κ ^ 2 + U))) =
      schrodingerCoeff (particleMass1D a b) * κ ^ 2 + U := by
  rw [schrodingerCoeff_mass a b ha hb]
  calc I * (-(I * (dispersionCoeff a b * κ ^ 2 + U)))
      = -((I * I) * (dispersionCoeff a b * κ ^ 2 + U)) := by ring
    _ = dispersionCoeff a b * κ ^ 2 + U := by rw [Complex.I_mul_I]; ring

/-- Collects the identity action and unitarity at zero phase, the derivative rule for adding the
real part of the potential, and the mass-based Schrödinger coefficient identity
[BoghosianTaylor1998]. -/
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
