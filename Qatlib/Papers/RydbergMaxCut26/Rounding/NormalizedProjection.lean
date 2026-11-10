/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.GroundBounds
import Qatlib.Papers.RydbergMaxCut26.MomentSdp.GramFactor
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Projection
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram

noncomputable def normalize (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun a => v a/Real.sqrt (sqnorm v)

theorem normalize_sqnorm (v : Fin 3 → ℝ) :
    sqnorm (normalize v) = if sqnorm v=0 then 0 else 1 := by
  have hs : 0 ≤ sqnorm v := Finset.sum_nonneg (fun a _ => sq_nonneg (v a))
  have he : sqnorm (normalize v) = sqnorm v/(Real.sqrt (sqnorm v))^2 := by
    simp only [sqnorm,normalize,div_pow,Finset.sum_div]
  rw [he,Real.sq_sqrt hs]
  by_cases hz : sqnorm v=0
  · simp only [hz,div_zero,ite_true]
  · simp only [hz,ite_false,div_self hz]

theorem normalize_ball (v : Fin 3 → ℝ) : sqnorm (normalize v)≤1 := by
  rw [normalize_sqnorm]
  split <;> norm_num

noncomputable def roundVector {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (hΔ : Δ.PosSemidef) (R : Fin 3 → (Fin 2×MomentIndex n) → ℝ) (i : Fin n) : Fin 3 → ℝ :=
  normalize (fun a => ∑ c, R a c*fitVector Δ hΔ i c)

theorem rounded_product_density {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (hΔ : Δ.PosSemidef) (R : Fin 3 → (Fin 2×MomentIndex n) → ℝ) :
    (productState (roundVector Δ hΔ R)).PosSemidef ∧ (productState (roundVector Δ hΔ R)).trace=1 :=
  product_density _ (fun _ => normalize_ball _)
end Qatlib.Papers.RydbergMaxCut26.Rounding.Projection
