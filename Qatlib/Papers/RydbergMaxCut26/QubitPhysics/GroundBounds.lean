/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Mixed-state ground-energy and expectation bounds

`mixed` is the product of zero-vector Bloch states, with QMC energy equal to minus one quarter
of the total edge weight. This comparison proves strict negativity for any matrix whose energy
is no larger than that of every density matrix when the total weight is positive; the module
also integrates the Bloch inner-product bound.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `ground_energy_negative`: obtains strict negativity from the mixed-state comparison.
* `clipped_expected_nonneg`: proves nonnegativity of the expected clipped mixture.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

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

/-- The maximally mixed register state, constructed as the product of the zero-vector Bloch
matrices. -/
noncomputable def mixed {n : ℕ} : Matrix (Reg n) (Reg n) ℂ :=
  productState (fun _ _ => 0)

/-- The maximally mixed register matrix is positive semidefinite and has trace one. -/
theorem mixed_density (n : ℕ) : (mixed (n:=n)).PosSemidef ∧ (mixed (n:=n)).trace=1 :=
  product_density (fun _ : Fin n => fun _ => 0) (fun _ => by norm_num [sqnorm])

/-- For distinct-site edges, the QMC energy of the maximally mixed state is −1/4 times the sum
of the edge weights. -/
theorem mixed_energy {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (hends : ∀ e, (ends e).1≠(ends e).2) (w : E → ℝ) :
    energy (qmcHamiltonian ends w) (mixed (n:=n)) = -(1/4:ℝ)*∑ e,w e := by
  simpa only [mixed,zero_mul,Finset.sum_const_zero,sub_zero,mul_one] using
    qmc_product_energy ends hends w (fun _ _ => 0)

/-- For distinct-site edges of positive total weight, any matrix whose QMC energy is at most
that of every physical density matrix has strictly negative energy. -/
theorem ground_energy_negative {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (hends : ∀ e, (ends e).1≠(ends e).2) (w : E → ℝ) (hW : 0<∑ e,w e)
    (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hground : ∀ σ : Matrix (Reg n) (Reg n) ℂ, σ.PosSemidef → σ.trace=1 →
      energy (qmcHamiltonian ends w) ρ ≤ energy (qmcHamiltonian ends w) σ) :
    energy (qmcHamiltonian ends w) ρ < 0 := by
  have h := hground (mixed (n:=n)) (mixed_density n).1 (mixed_density n).2
  rw [mixed_energy ends hends w] at h
  nlinarith

/-- On a probability space, the integral of an integrable inner product of two pointwise
Bloch-ball vectors is at most one. -/
theorem mean_bloch_dot_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u v : Ω → Fin 3 → ℝ) (hu : ∀ ω,sqnorm (u ω)≤1) (hv : ∀ ω,sqnorm (v ω)≤1)
    (hint : Integrable (fun ω => ∑ a, u ω a*v ω a) μ) :
    (∫ ω, ∑ a, u ω a*v ω a ∂μ) ≤ 1 := by
  have h : (∫ ω, ∑ a, u ω a*v ω a ∂μ) ≤ ∫ _ : Ω, (1:ℝ) ∂μ :=
    integral_mono_ae hint (integrable_const 1) (Filter.Eventually.of_forall
      (fun ω => bloch_dot_le_one (u ω) (v ω) (hu ω) (hv ω)))
  simpa using h

/-- For `p ∈ [0, 1]`, the clipped mixture of `min t 0` and the expected inner product of two
Bloch-ball vectors is nonnegative, provided that inner product is integrable. -/
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
