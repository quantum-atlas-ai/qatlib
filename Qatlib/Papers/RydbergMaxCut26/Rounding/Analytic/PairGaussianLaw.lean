/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceFubini
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.Gaussian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Scalar pair coordinates for Gaussian moments

The map `packPair` groups three independent pairs of scalar standard Gaussians into two
Euclidean Gaussian vectors. Transport along this map rewrites `tiltedMoment` as an integral of
explicit coordinate sums. See [CrostaSaubanereHuber2026].

## Main statements

* `packPair_preserving`: transports the scalar product law to `sourceLaw`.
* `tiltedMoment_pairs`: expresses the tilted moment in scalar pair coordinates.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical NNReal
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

/-- The product law of three independent pairs of standard real Gaussian variables. -/
abbrev pairRowsLaw : Measure (Fin 3→ℝ×ℝ) := Measure.pi (fun _ : Fin 3=>standard1.prod standard1)

/-- The pair of Euclidean vectors formed from the first and second coordinates of three scalar
pairs. -/
def packPair (R : Fin 3→ℝ×ℝ) : V×V :=
  (WithLp.toLp 2 (fun r=> (R r).1),WithLp.toLp 2 (fun r=> (R r).2))

/-- Packing the scalar pairs into two vectors preserves the scalar product law and the Gaussian
source law. -/
theorem packPair_preserving : MeasurePreserving packPair pairRowsLaw sourceLaw := by
  have hp : MeasurePreserving (WithLp.toLp 2) (Measure.pi (fun _ : Fin 3=>standard1)) gamma :=
    ⟨by fun_prop,gamma_from_iid⟩
  exact (hp.prod hp).comp (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)
    (fun _=>standard1) (fun _=>standard1))

/-- The tilted Gaussian moment equals the scalar pair integral of the correlated coordinate dot
product times its quadratic exponential weight. -/
theorem tiltedMoment_pairs (t a b : ℝ) :
    tiltedMoment t a b=
      ∫ R : Fin 3→ℝ×ℝ,(∑ r : Fin 3,(R r).1*(t*(R r).1+Real.sqrt (1-t^2)*(R r).2))*
        Real.exp (-(a*(∑ r : Fin 3,(R r).1^2)+
          b*(∑ r : Fin 3,(t*(R r).1+Real.sqrt (1-t^2)*(R r).2)^2))) ∂pairRowsLaw := by
  have hm : Measurable (fun w : V×V => inner ℝ w.1 (correlated t w)*
      Real.exp (-(a*‖w.1‖^2+b*‖correlated t w‖^2))) := by
    unfold correlated
    fun_prop
  rw [tiltedMoment,← packPair_preserving.map_eq,
    integral_map packPair_preserving.measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply]
  simp [packPair,correlated,mul_comm]

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
