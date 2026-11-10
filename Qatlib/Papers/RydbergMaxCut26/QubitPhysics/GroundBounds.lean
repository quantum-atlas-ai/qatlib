/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open MeasureTheory
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Ground
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds

noncomputable def mixed {n : ℕ} : Matrix (Reg n) (Reg n) ℂ :=
  productState (fun _ _ => 0)

theorem mixed_density (n : ℕ) : (mixed (n:=n)).PosSemidef ∧ (mixed (n:=n)).trace=1 :=
  product_density (fun _ : Fin n => fun _ => 0) (fun _ => by norm_num [sqnorm])

theorem mixed_energy {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (hends : ∀ e, (ends e).1≠(ends e).2) (w : E → ℝ) :
    energy (qmcHamiltonian ends w) (mixed (n:=n)) = -(1/4:ℝ)*∑ e,w e := by
  simpa only [mixed,zero_mul,Finset.sum_const_zero,sub_zero,mul_one] using
    qmc_product_energy ends hends w (fun _ _ => 0)

theorem ground_energy_negative {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (hends : ∀ e, (ends e).1≠(ends e).2) (w : E → ℝ) (hW : 0<∑ e,w e)
    (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hground : ∀ σ : Matrix (Reg n) (Reg n) ℂ, σ.PosSemidef → σ.trace=1 →
      energy (qmcHamiltonian ends w) ρ ≤ energy (qmcHamiltonian ends w) σ) :
    energy (qmcHamiltonian ends w) ρ < 0 := by
  have h := hground (mixed (n:=n)) (mixed_density n).1 (mixed_density n).2
  rw [mixed_energy ends hends w] at h
  nlinarith

theorem mean_bloch_dot_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u v : Ω → Fin 3 → ℝ) (hu : ∀ ω,sqnorm (u ω)≤1) (hv : ∀ ω,sqnorm (v ω)≤1)
    (hint : Integrable (fun ω => ∑ a, u ω a*v ω a) μ) :
    (∫ ω, ∑ a, u ω a*v ω a ∂μ) ≤ 1 := by
  have h : (∫ ω, ∑ a, u ω a*v ω a ∂μ) ≤ ∫ _ : Ω, (1:ℝ) ∂μ :=
    integral_mono_ae hint (integrable_const 1) (Filter.Eventually.of_forall
      (fun ω => bloch_dot_le_one (u ω) (v ω) (hu ω) (hv ω)))
  simpa using h

theorem clipped_expected_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p t : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (u v : Ω → Fin 3 → ℝ)
    (hu : ∀ ω,sqnorm (u ω)≤1) (hv : ∀ ω,sqnorm (v ω)≤1)
    (hint : Integrable (fun ω => ∑ a, u ω a*v ω a) μ) :
    0≤-4*p*min t 0+(1-p)*(1-∫ ω, ∑ a, u ω a*v ω a ∂μ) := by
  have ht : min t 0≤0 := min_le_right _ _
  have hprod := mean_bloch_dot_le_one μ u v hu hv hint
  exact add_nonneg (mul_nonneg_of_nonpos_of_nonpos (by nlinarith) ht)
    (mul_nonneg (by linarith) (by linarith))
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Ground
