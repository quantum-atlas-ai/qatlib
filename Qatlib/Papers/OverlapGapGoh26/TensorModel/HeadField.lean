/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorDiff

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.TensorModel.HeadField

def sparseQuartic : Tensor 4 2 := Pi.single (![0,1,1,1] : Fin 4 → Fin 2) 1

theorem sparse_quartic_full_gradient : tensorGradient sparseQuartic (fun _ => 1) 1=3 := by
  classical
  simp [tensorGradient,tensorDirectional,sparseQuartic,Pi.single_apply]
  have hc : (Finset.univ.filter (fun x : Fin 4 => (![0,1,1,1] : Fin 4 → Fin 2) x=1)).card=3 := by
    decide
  exact_mod_cast hc

theorem sparse_quartic_head_field :
    interaction (fun i k => sparseQuartic (Fin.cons i k)) (fun _ => 1) 1=0 := by
  classical
  have he (k : Fin 3 → Fin 2) : Fin.cons (1 : Fin 2) k≠(![0,1,1,1] : Fin 4 → Fin 2) := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  simp [interaction,sparseQuartic,he]

theorem ordered_full_gradient_ne_scaled_head :
    tensorGradient sparseQuartic (fun _ => 1) 1≠
      (4:ℝ)*interaction (fun i k => sparseQuartic (Fin.cons i k)) (fun _ => 1) 1 := by
  rw [sparse_quartic_full_gradient,sparse_quartic_head_field]
  norm_num

end Qatlib.Papers.OverlapGapGoh26.TensorModel.HeadField
