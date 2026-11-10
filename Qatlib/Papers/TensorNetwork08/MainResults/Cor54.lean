/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Norm
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor54

open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
open Qatlib.Papers.TensorNetwork08.MainResults.Norm

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def generalModelScale (q b : ℕ) (eNorm : E → ℝ) : ℝ :=
  (Real.sqrt q) ^ b * ∏ e : E, eNorm e

theorem generalModelScale_eq_bubble_prod (q b m : ℕ) (eNorm : E → ℝ) :
    (Real.sqrt q) ^ b * (1 : ℝ) ^ m * ∏ e : E, eNorm e
      = generalModelScale q b eNorm := by
  simp [generalModelScale]

theorem corollary5_4_general_model_scale (q b m : ℕ) (eNorm : E → ℝ) :
    generalModelScale q b eNorm
      = (Real.sqrt q) ^ b * (1 : ℝ) ^ m * ∏ e : E, eNorm e :=
  (generalModelScale_eq_bubble_prod q b m eNorm).symm

theorem extreme_vertex_norm {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] (a : Fin n) :
    tensorNorm (diagTensor a (fun _ : C => (1 : ℂ))) = Real.sqrt (Fintype.card C) :=
  deltaTensor_norm a

theorem identity_vertex_norm {n m : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (a : Fin n) (b : Fin m) (α : C → ℂ) :
    tensorNorm (diagTensor a α) = tensorNorm (diagTensor b α) :=
  identityTensor_norm_eq a b α

theorem corollary5_4_finite_lattice_scale (q : ℕ) (eNorm : E → ℝ) :
    generalModelScale q 2 eNorm = (q : ℝ) * ∏ e : E, eNorm e := by
  unfold generalModelScale
  rw [show (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) from Real.sq_sqrt (Nat.cast_nonneg q)]

end Qatlib.Papers.TensorNetwork08.MainResults.Cor54
