/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.PureStateTV
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
set_option warningAsError false

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance
open Matrix Qatlib
open scoped BigOperators InnerProductSpace
section Hilbert

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

omit [DecidableEq I] in

private theorem inner_vec (x y : I → ℂ) :
    inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = star x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

theorem matrix_inner (A B : Matrix J I ℂ) (x y : EuclideanSpace ℂ I) :
    inner ℂ (A.toEuclideanLin x) (B.toEuclideanLin y) =
      inner ℂ x ((Aᴴ * B).toEuclideanLin y) := by
  change inner ℂ (WithLp.toLp 2 (A *ᵥ x.ofLp)) (WithLp.toLp 2 (B *ᵥ y.ofLp)) =
    inner ℂ (WithLp.toLp 2 x.ofLp) (WithLp.toLp 2 ((Aᴴ * B) *ᵥ y.ofLp))
  rw [inner_vec, inner_vec]
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

private theorem matrix_one_apply (x : EuclideanSpace ℂ I) :
    (1 : Matrix I I ℂ).toEuclideanLin x = x := by
  change WithLp.toLp 2 ((1 : Matrix I I ℂ) *ᵥ x.ofLp) = x
  rw [Matrix.one_mulVec]

def matrixIsometry (A : Matrix J I ℂ) (hA : Aᴴ * A = 1) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J :=
  A.toEuclideanLin.isometryOfInner (by
    intro x y
    rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.matrix_inner, hA,
        matrix_one_apply])

theorem matrixIsometry_apply (A : Matrix J I ℂ) (hA : Aᴴ * A = 1)
    (x : EuclideanSpace ℂ I) : Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.matrixIsometry A hA x = A.toEuclideanLin x := rfl

end Hilbert

section Coordinates

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [Fintype J] [DecidableEq J] in

private theorem normalized_coordinates (x : EuclideanSpace ℂ I) (hx : ‖x‖ = 1) :
    Qatlib.Foundations.PureStateMath.Normalized x.ofLp := by
  change ∑ i : I, ‖x.ofLp i‖ ^ 2 = 1
  calc
    _ = ‖x‖ ^ 2 := (EuclideanSpace.norm_sq_eq x).symm
    _ = 1 := by rw [hx, one_pow]

omit [DecidableEq I] [Fintype J] [DecidableEq J] in

private theorem coordinates_inner (x y : EuclideanSpace ℂ I) :
    Qatlib.Foundations.PureStateMath.Inner x.ofLp y.ofLp = inner ℂ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact dotProduct_comm _ _

omit [Fintype J] [DecidableEq J] in

theorem euclidean_basis_born_tv (x y : EuclideanSpace ℂ I)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (1 / 2 : ℝ) * ∑ z : I, |Qatlib.Foundations.PureStateMath.BornProb x.ofLp z - Qatlib.Foundations.PureStateMath.BornProb y.ofLp z| ≤
      Real.sqrt (1 - ‖inner ℂ x y‖ ^ 2) := by
  have h := Qatlib.Concepts.MonteCarloMean.FinDistBounds.pureState_born_tv_le_sqrt_fidelity (1 : Matrix I I ℂ)
    (Matrix.unitaryGroup I ℂ).one_mem x.ofLp y.ofLp
    (normalized_coordinates x hx) (normalized_coordinates y hy)
  simpa only [Qatlib.Foundations.PureStateMath.ApplyGate, Matrix.one_mulVec,
      coordinates_inner] using h

theorem rectangular_born_tv_le_sqrt_fidelity (A : Matrix J I ℂ) (hA : Aᴴ * A = 1)
    (x y : EuclideanSpace ℂ I) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (1 / 2 : ℝ) * ∑ z : J,
      |Qatlib.Foundations.PureStateMath.BornProb (A *ᵥ x.ofLp) z - Qatlib.Foundations.PureStateMath.BornProb (A *ᵥ y.ofLp) z| ≤
      Real.sqrt (1 - ‖inner ℂ x y‖ ^ 2) := by
  let V :=
      Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.matrixIsometry A hA
  have hxV : ‖V x‖ = 1 := by rw [LinearIsometry.norm_map, hx]
  have hyV : ‖V y‖ = 1 := by rw [LinearIsometry.norm_map, hy]
  have h :=
      Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.euclidean_basis_born_tv (V x) (V y) hxV hyV
  simpa only [LinearIsometry.inner_map_map] using! h

end Coordinates
end Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance
