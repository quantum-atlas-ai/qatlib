/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualPaths
import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.ActualGram
import Qatlib.Foundations.MatrixAlgebra.FrameProject.TensorErrors
import Qatlib.Concepts.MixedFidelity.FidelityMetric.PurificationErrors
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Foundations.MatrixAlgebra.FrameProject.Tensor
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Purification
set_option warningAsError false

def histogramPurification0 {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) : Matrix (Fin d × Fin a) (Fin d → Fin q) ℂ :=
  pathCoefficient Alg n * histogramBasis (pathHistogram Alg n q hn)

def histogramPurification1 {d a : ℕ} (eps : ℝ) (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) : Matrix (Fin d × Fin a) (Fin d → Fin q) ℂ :=
  pathCoefficient Alg n * columns (transformedColumn eps q) (pathHistogram Alg n q hn)

theorem actual_histogram_domination {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (hn : n<q) :
    (reduced (histogramPurification1 eps Alg n q hn) -
      (((1-4*(n:ℝ)*eps^2:ℝ):ℂ) • reduced (histogramPurification0 Alg n q hn))).PosSemidef := by
  classical
  let hist := pathHistogram Alg n q hn
  let K := transformedColumn eps q
  let Phi := histogramBasis hist
  let E := errorColumn K hist
  let alpha := fun h => diagonalAmplitude K (hist h)
  have hPhi : Phi * Phiᴴ = 1 := by
    ext h k
    simpa only [Phi,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using!
      histogramBasis_orthonormal hist (pathHistogram_injective Alg n q hn) h k
  have hE : Phi * Eᴴ = 0 := by
    ext h k
    exact histogramBasis_error_orthogonal K (transformedColumn_upper eps q) hist
      (pathHistogram_mass Alg n q hn) h k
  have halpha (h : pathSupport Alg n) : 1-4*(n:ℝ)*eps^2 ≤ ‖alpha h‖^2 := by
    have hb := diagonal_tensor_budget (by omega : 0<q) K (transformedColumn_upper eps q)
      (transformedColumn_normalized eps q hq he0 he1) (4*eps^2) (by positivity)
      (transformedColumn_diagonal eps q hq he0 he1) (hist h)
    rw [pathHistogram_mass Alg n q hn h] at hb
    simpa only [alpha] using!
        (show 1-4*(n:ℝ)*eps^2 ≤ ‖diagonalAmplitude K (hist h)‖^2 by nlinarith [hb])
  have hdec : columns K hist = Matrix.diagonal alpha * Phi + E := tensor_decomposition K hist
  have hp := reduced_errors_domination (pathCoefficient Alg n) Phi E alpha
    (4*(n:ℝ)*eps^2) hPhi hE halpha
  change (reduced (pathCoefficient Alg n * columns K hist) -
    (((1-4*(n:ℝ)*eps^2:ℝ):ℂ) • reduced (pathCoefficient Alg n * Phi))).PosSemidef
  rw [hdec]
  exact hp

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
