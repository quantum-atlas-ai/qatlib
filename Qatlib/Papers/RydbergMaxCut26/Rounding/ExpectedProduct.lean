/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.GroundBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open MeasureTheory
open scoped Classical
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Expectation
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch

theorem expected_product_energy {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (ends : E → Fin n×Fin n)
    (hends : ∀ e, (ends e).1≠(ends e).2) (w : E → ℝ) (v : Ω → Fin n → Fin 3 → ℝ)
    (hint : ∀ e, Integrable (fun ω => ∑ a, v ω (ends e).1 a*v ω (ends e).2 a) μ) :
    (∫ ω, energy (qmcHamiltonian ends w) (productState (v ω)) ∂μ) =
      -(1/4:ℝ)*∑ e, w e*(1-∫ ω, ∑ a, v ω (ends e).1 a*v ω (ends e).2 a ∂μ) := by
  have he : (fun ω => energy (qmcHamiltonian ends w) (productState (v ω))) =
      (fun ω => -(1/4:ℝ)*∑ e, w e*(1-∑ a, v ω (ends e).1 a*v ω (ends e).2 a)) := by
    funext ω
    exact qmc_product_energy ends hends w (v ω)
  have hi (e : E) : Integrable (fun ω => w e*(1-∑ a, v ω (ends e).1 a*v ω (ends e).2 a)) μ :=
    ((integrable_const 1).sub (hint e)).const_mul (w e)
  rw [he,integral_const_mul,integral_finsetSum Finset.univ (fun e _ => hi e)]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_const_mul,integral_sub (integrable_const 1) (hint e)]
  simp
end Qatlib.Papers.RydbergMaxCut26.Rounding.Expectation
