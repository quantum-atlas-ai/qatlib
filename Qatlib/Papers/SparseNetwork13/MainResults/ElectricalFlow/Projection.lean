/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow.KernelFlowCharacterization
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! The kernel-coordinate conclusion of Lemma 9, proved without an SVD. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow
open Matrix BigOperators
open Qatlib.Papers.SparseNetwork13.MainResults.Model
open Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- Incidence duality for an arbitrary edge flow and potential. -/
theorem flowDual (G : ElecNetwork V E) (v : V → ℝ) (f : E → ℝ) :
    (∑ e, ((incident G)ᵀ *ᵥ v) e * f e) =
      ∑ x, v x * (incident G *ᵥ f) x := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext x
  apply Finset.sum_congr rfl
  intro e _
  ring

end Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow
