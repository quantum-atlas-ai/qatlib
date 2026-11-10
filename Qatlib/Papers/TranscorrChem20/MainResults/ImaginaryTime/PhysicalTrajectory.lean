/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.NormalizedEvolution
import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.GroundSpace
import Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity.MetricObservables
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace Filter
open Qatlib.Concepts.ImaginaryFlow.Similarity
open scoped Topology
open Qatlib.Concepts.ImaginaryFlow.Normalize
open Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity

namespace Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime

theorem physical_propagator {d : ℕ} (H g : Op d) (t : ℝ) :
    exp g * exp ((-t) • tc H g) = exp ((-t) • H) * exp g := by
  rw [actual_tc_exp]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (actual_exp_inverse g).2, Matrix.one_mul]

theorem physical_actualState {d : ℕ} (H g : Op d) (φ : State d) (t : ℝ) :
    expEquiv g (actualState H g φ t) =
      Matrix.toEuclideanLin (exp ((-t) • H)) (expEquiv g φ) := by
  change Matrix.toEuclideanLin (exp g) (Matrix.toEuclideanLin (exp ((-t) • tc H g)) φ) = _
  rw [← matrix_action_mul, physical_propagator, matrix_action_mul]
  rfl

theorem physical_normalizedState {d : ℕ} (H g : Op d) (φ : State d) (t : ℝ) :
    expEquiv g (normalized (actualState H g φ t)) =
      ‖actualState H g φ t‖⁻¹ •
        Matrix.toEuclideanLin (exp ((-t) • H)) (expEquiv g φ) := by
  simp only [normalized, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, physical_actualState]

theorem physical_inverse_metric_norm {d : ℕ} (H g : Op d) (φ : State d)
    (hφ : φ ≠ 0) (t : ℝ) :
    let ψ := expEquiv g (normalized (actualState H g φ t))
    inner ℂ ψ (Matrix.toEuclideanLin (tcMetric (-g)) ψ) = 1 := by
  (try dsimp only)
  rw [metric_norm_form]
  have hc : expEquiv (-g) (expEquiv g (normalized (actualState H g φ t))) =
      normalized (actualState H g φ t) := (expEquiv g).symm_apply_apply _
  rw [hc, actual_tc_normalized_norm H g φ hφ t]
  norm_num

theorem tc_adjoint {d : ℕ} (H g : Op d) (hH : H.IsHermitian) (hg : g.IsHermitian) :
    (tc H g).conjTranspose = tc H (-g) := by
  simp only [tc, Matrix.conjTranspose_mul, hH.eq, hg.exp.eq, hg.neg.exp.eq, neg_neg,
    Matrix.mul_assoc]

theorem actual_left_normalized_limit {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (hg : g.IsHermitian) (φ : State d) (i0 : Fin d)
    (hgap : ∀ i : Fin d, i ≠ i0 → hH.eigenvalues i0 < hH.eigenvalues i)
    (hoverlap : coefficients (-g) hH φ i0 ≠ 0) :
    Tendsto (fun t : ℝ => normalized (rawState (tc H g).conjTranspose φ t)) atTop
      (𝓝 (normalized (rightComponent (-g) hH φ i0))) := by
  rw [tc_adjoint H g hH hg]
  exact actual_normalized_limit H (-g) hH φ i0 hgap hoverlap

theorem actual_left_groundspace_limit {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (hg : g.IsHermitian) (φ : State d) (i0 : Fin d)
    (hmin : ∀ i, hH.eigenvalues i0 ≤ hH.eigenvalues i)
    (hoverlap : GroundSpace.rightGround (-g) hH φ i0 ≠ 0) :
    Tendsto (fun t : ℝ => normalized (rawState (tc H g).conjTranspose φ t)) atTop
      (𝓝 (normalized (GroundSpace.rightGround (-g) hH φ i0))) := by
  rw [tc_adjoint H g hH hg]
  exact GroundSpace.actual_normalized_groundspace_limit H (-g) hH φ i0 hmin hoverlap

end Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime
