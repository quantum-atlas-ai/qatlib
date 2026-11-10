/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LinearTail
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FiniteTupleTail

theorem actual_finite_tuple_tail {r N : ℕ} {J : Type} [Fintype J]
    (z : J→Fin (r+1)→EuclideanSpace ℝ (Fin N)) (hz : ∀ j a,‖z j a‖=1)
    (ε : ℝ) (hε : 0≤ε) :
    (gaussianTensorLaw r N).real {A | ∃ j,ε≤|tensorForm A (z j)|}≤
      2*(Fintype.card J:ℝ)*Real.exp (-ε^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) := by
  have hj (j : J) : (gaussianTensorLaw r N).real {A | ε≤|tensorForm A (z j)|}≤
      2*Real.exp (-ε^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) := by
    have hu (a : Fin (r+1)) : ∑ i,(z j a i)^2=1 := by
      rw [← EuclideanSpace.real_norm_sq_eq,hz,one_pow]
    simpa only [multilinearEval,← tensorForm_apply] using
        unit_multilinear_abs_tail (fun a i => z j a i) hu ε hε
  have he : {A : Tensor (r+1) N | ∃ j,ε≤|tensorForm A (z j)|}=⋃ j : J,{A | ε≤|tensorForm A (z j)|} := by
    ext A
    simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _j : J,2*Real.exp (-ε^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp; ring

theorem actual_finite_tuple_scaled_tail {r N : ℕ} (hN : 0<N) {J : Type} [Fintype J]
    (z : J→Fin (r+1)→EuclideanSpace ℝ (Fin N)) (hz : ∀ j a,‖z j a‖=1)
    (a : ℝ) (ha : 0≤a) :
    (gaussianTensorLaw r N).real {A | ∃ j,a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)≤|tensorForm A (z j)|}≤
      2*(Fintype.card J:ℝ)*Real.exp (-a^2*(N:ℝ)/2) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hp : (N:ℝ)^r≠0 := pow_ne_zero _ hn.ne'
  have h := actual_finite_tuple_tail z hz (a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)) (by positivity)
  have he : -(a*Real.sqrt ((N:ℝ)/(N:ℝ)^r))^2/(2*(((N:NNReal)^r)⁻¹:ℝ))= -a^2*(N:ℝ)/2 := by
    simp only [NNReal.coe_natCast]
    rw [mul_pow,Real.sq_sqrt (by positivity : 0≤(N:ℝ)/(N:ℝ)^r)]
    field_simp
  simpa only [he] using h

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FiniteTupleTail
