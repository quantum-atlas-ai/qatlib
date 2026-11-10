/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Cor54
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor59

open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
open Qatlib.Papers.TensorNetwork08.MainResults.Norm

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

noncomputable def edgeWeight (h : E → C → ℝ) (β : ℝ) (e : E) (j : C) : ℝ :=
  Real.exp (-(β * h e j))

noncomputable def energyNorm (h : E → C → ℝ) (β : ℝ) (e : E) : ℝ :=
  Real.sqrt (∑ j : C, |edgeWeight h β e j| ^ 2)

noncomputable def differenceScale (q n : ℕ) (h : E → C → ℝ) (β : ℝ) : ℝ :=
  (Real.sqrt (q : ℝ)) ^ (n + 1) * ∏ e : E, energyNorm h β e

noncomputable def bubblePlaneScale (q n : ℕ) (h : E → C → ℝ) (β : ℝ) : ℝ :=
  (Real.sqrt (q : ℝ)) ^ (n - 1) * ∏ e : E, energyNorm h β e

theorem corollary5_9_four_plane_norms (q n m₁ m₂ : ℕ) (h : E → C → ℝ) (β : ℝ) :
    (Real.sqrt (q : ℝ)) ^ (n - 1) * (1 : ℝ) ^ m₁ * (1 : ℝ) ^ m₂ * ∏ e : E, energyNorm h β e
      = bubblePlaneScale q n h β := by
  simp [bubblePlaneScale]

theorem corollary5_9_bubbling_scale {q n : ℕ} (hn : 0 < n) (hq : 0 ≤ (q : ℝ))
    (h : E → C → ℝ) (β : ℝ) :
    (q : ℝ) * bubblePlaneScale q n h β = differenceScale q n h β := by
  unfold bubblePlaneScale differenceScale
  have hpow : (q : ℝ) = (Real.sqrt (q : ℝ)) ^ 2 := (Real.sq_sqrt hq).symm
  have hstep : (q : ℝ) * (Real.sqrt (q : ℝ)) ^ (n - 1) = (Real.sqrt (q : ℝ)) ^ (n + 1) := by
    nth_rewrite 1 [hpow]
    rw [← pow_add]
    congr 1
    omega
  calc (q : ℝ) * ((Real.sqrt (q : ℝ)) ^ (n - 1) * ∏ e : E, energyNorm h β e)
      = ((q : ℝ) * (Real.sqrt (q : ℝ)) ^ (n - 1)) * ∏ e : E, energyNorm h β e := by ring
    _ = (Real.sqrt (q : ℝ)) ^ (n + 1) * ∏ e : E, energyNorm h β e := by rw [hstep]

theorem corollary5_9_difference_scale (h : E → C → ℝ) (β : ℝ) (n : ℕ) :
    differenceScale (Fintype.card C) n h β
      = (Real.sqrt (Fintype.card C : ℝ)) ^ (n + 1) * ∏ e : E, energyNorm h β e := rfl

end Qatlib.Papers.TensorNetwork08.MainResults.Cor59
