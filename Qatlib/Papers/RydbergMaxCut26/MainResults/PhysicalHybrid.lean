/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.RatioBounds.ClippedCertificates
import Qatlib.Papers.RydbergMaxCut26.Rounding.ExpectedProduct

/-!
# Measurability and integrability of physical rounding

This module proves analytic regularity for the rounded vectors `physicalRound` and the
associated `productCandidate`. Coordinatewise measurable projection matrices yield measurable
rounded coordinates and product energies; the Bloch-ball bounds ensure integrability on a
probability space.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `round_ball`: each rounded vector lies in the closed unit ball.
* `product_energy_integrable`: the rounded product-state energy is integrable.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix Qatlib MeasureTheory
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalHybrid
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.Rounding.Projection Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Ground
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.Rounding.Expectation
open Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Clipped
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase

/-- Each coordinate of `physicalRound` is measurable when all entries of the projection matrix
are measurable. -/
theorem round_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Ω → Fin 3 → Fin 2×MomentIndex n → ℝ)
    (hR : ∀ a c,Measurable (fun ω => R ω a c)) (i : Fin n) (a : Fin 3) :
    Measurable (fun ω => physicalRound n ρ hρ htr (R ω) i a) := by
  unfold physicalRound roundVector Qatlib.Papers.RydbergMaxCut26.Rounding.Projection.normalize sqnorm
  fun_prop

/-- Every vector produced by `physicalRound` has squared norm at most one. -/
theorem round_ball {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Fin 3 → Fin 2×MomentIndex n → ℝ) (i : Fin n) :
    sqnorm (physicalRound n ρ hρ htr R i) ≤ 1 := normalize_ball _

/-- The absolute inner product of two real three-dimensional vectors of squared norm at most one
is at most one. -/
theorem dot_abs_le_one (u v : Fin 3 → ℝ) (hu : sqnorm u ≤ 1) (hv : sqnorm v ≤ 1) :
    |∑ a,u a*v a| ≤ 1 := by
  have hp := bloch_dot_le_one u v hu hv
  have hn := bloch_dot_le_one u (fun a => -v a) hu (by simpa only [sqnorm,neg_sq] using hv)
  simp only [mul_neg,Finset.sum_neg_distrib] at hn
  exact abs_le.mpr ⟨by linarith,hp⟩

/-- The inner product of two physically rounded vectors is integrable for a probability measure
when the projection entries are measurable. -/
theorem round_dot_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Ω → Fin 3 → Fin 2×MomentIndex n → ℝ)
    (hR : ∀ a c,Measurable (fun ω => R ω a c)) (i j : Fin n) :
    Integrable (fun ω => ∑ a,physicalRound n ρ hρ htr (R ω) i a*
      physicalRound n ρ hρ htr (R ω) j a) μ := by
  have hm : Measurable (fun ω => ∑ a,physicalRound n ρ hρ htr (R ω) i a*
      physicalRound n ρ hρ htr (R ω) j a) :=
    Finset.measurable_sum _ (fun a _ => (round_measurable ρ hρ htr R hR i a).mul
      (round_measurable ρ hρ htr R hR j a))
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs] using
    (dot_abs_le_one _ _ (round_ball ρ hρ htr (R ω) i) (round_ball ρ hρ htr (R ω) j))

/-- The quantum Max Cut energy of `productCandidate` is measurable for distinct-site edges and
coordinatewise measurable projections. -/
theorem product_energy_measurable {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    {n : ℕ} (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Ω → Fin 3 → Fin 2×MomentIndex n → ℝ)
    (hR : ∀ a c,Measurable (fun ω => R ω a c)) :
    Measurable (fun ω => energy (qmcHamiltonian ends w) (productCandidate ρ hρ htr R ω)) := by
  have he : (fun ω => energy (qmcHamiltonian ends w) (productCandidate ρ hρ htr R ω))=
      (fun ω => -(1/4:ℝ)*∑ e,w e*(1-∑ a,physicalRound n ρ hρ htr (R ω) (ends e).1 a*
        physicalRound n ρ hρ htr (R ω) (ends e).2 a)) := by
    funext ω
    exact qmc_product_energy ends hends w _
  rw [he]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  apply Measurable.const_mul
  apply Measurable.const_sub
  exact Finset.measurable_sum _ (fun a _ => (round_measurable ρ hρ htr R hR (ends e).1 a).mul
    (round_measurable ρ hρ htr R hR (ends e).2 a))

/-- The quantum Max Cut energy of `productCandidate` is integrable on a probability space for
distinct-site edges and coordinatewise measurable projections. -/
theorem product_energy_integrable {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Ω → Fin 3 → Fin 2×MomentIndex n → ℝ)
    (hR : ∀ a c,Measurable (fun ω => R ω a c)) :
    Integrable (fun ω => energy (qmcHamiltonian ends w) (productCandidate ρ hρ htr R ω)) μ := by
  have he : (fun ω => energy (qmcHamiltonian ends w) (productCandidate ρ hρ htr R ω))=
      (fun ω => -(1/4:ℝ)*∑ e,w e*(1-∑ a,physicalRound n ρ hρ htr (R ω) (ends e).1 a*
        physicalRound n ρ hρ htr (R ω) (ends e).2 a)) := by
    funext ω
    exact qmc_product_energy ends hends w _
  rw [he]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro e _
  exact ((integrable_const 1).sub (round_dot_integrable μ ρ hρ htr R hR (ends e).1 (ends e).2)).const_mul (w e)
end Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalHybrid
