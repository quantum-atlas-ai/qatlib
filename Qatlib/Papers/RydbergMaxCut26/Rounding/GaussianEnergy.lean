/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianEndpoints
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical ComplexOrder
open MeasureTheory ProbabilityTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix

theorem physicalFitEuclidean_dot (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) :
    inner ℝ (physicalFitEuclidean n ρ hρ htr i) (physicalFitEuclidean n ρ hρ htr j)=tParam ρ i j := by
  simpa [physicalFitEuclidean,PiLp.inner_apply,mul_comm] using physical_fit_dot n ρ hρ htr i j hij

theorem physical_row_covariance (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) :
    cov[fun x : Row (Fin 2 × MomentIndex n) => inner ℝ (physicalFitEuclidean n ρ hρ htr i) x,
      fun x : Row (Fin 2 × MomentIndex n) => inner ℝ (physicalFitEuclidean n ρ hρ htr j) x;
      stdGaussian (Row (Fin 2 × MomentIndex n))]=tParam ρ i j := by
  rw [row_projection_covariance,physicalFitEuclidean_dot n ρ hρ htr i j hij]

theorem physical_dot_expectation (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) :
    (∫ R : Fin 3 → Fin 2 × MomentIndex n → ℝ,
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a ∂rawMatrixLaw (Fin 2 × MomentIndex n))=
      rawExpectation (physicalFitEuclidean n ρ hρ htr i) (physicalFitEuclidean n ρ hρ htr j) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun R => physical_dot_eq n ρ hρ htr i j R)

theorem physical_energy_integrable {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    Integrable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ =>
      energy (qmcHamiltonian ends w) (productState (physicalRound n ρ hρ htr R))) (rawMatrixLaw (Fin 2 × MomentIndex n)) := by
  have hi : Integrable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ =>
      -(1/4:ℝ)*∑ e,w e*(1-∑ a : Fin 3,physicalRound n ρ hρ htr R (ends e).1 a*
        physicalRound n ρ hρ htr R (ends e).2 a)) (rawMatrixLaw (Fin 2 × MomentIndex n)) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro e _
    exact ((integrable_const (1:ℝ)).sub (physical_dot_integrable n ρ hρ htr (ends e).1 (ends e).2)).const_mul (w e)
  exact hi.congr
      (Filter.Eventually.of_forall (fun R => (physical_round_energy ends hends w ρ hρ htr R).symm))

theorem physical_energy_expectation {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (∫ R : Fin 3 → Fin 2 × MomentIndex n → ℝ,
      energy (qmcHamiltonian ends w) (productState (physicalRound n ρ hρ htr R)) ∂rawMatrixLaw (Fin 2 × MomentIndex n))=
      -(1/4:ℝ)*∑ e,w e*(1-rawExpectation (physicalFitEuclidean n ρ hρ htr (ends e).1)
        (physicalFitEuclidean n ρ hρ htr (ends e).2)) := by
  have heq : (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ =>
      energy (qmcHamiltonian ends w) (productState (physicalRound n ρ hρ htr R)))=
      fun R => -(1/4:ℝ)*∑ e,w e*(1-∑ a : Fin 3,physicalRound n ρ hρ htr R (ends e).1 a*
        physicalRound n ρ hρ htr R (ends e).2 a) := funext (physical_round_energy ends hends w ρ hρ htr)
  rw [heq,integral_const_mul]
  have hi (e : E) : Integrable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ =>
      w e*(1-∑ a : Fin 3,physicalRound n ρ hρ htr R (ends e).1 a*physicalRound n ρ hρ htr R (ends e).2 a))
      (rawMatrixLaw (Fin 2 × MomentIndex n)) :=
    ((integrable_const (1:ℝ)).sub (physical_dot_integrable n ρ hρ htr (ends e).1 (ends e).2)).const_mul (w e)
  rw [integral_finsetSum _ (fun e _ => hi e)]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_const_mul,integral_sub (integrable_const _) (physical_dot_integrable n ρ hρ htr (ends e).1 (ends e).2),
    physical_dot_expectation]
  simp

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
