/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.ProductEffects

/-!
# Attainment of product-state scores

This module proves continuity of the weighted quadratic score as a function of the block states
of `partitionState`. Compactness of the finite family of state spaces then gives a product state
attaining the maximum score. See [XuEtAl2026] for background.

## Main statements

* `product_score_continuous`: continuity of the score on block states.
* `product_score_attained`: existence of a maximizing partition product state.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.PureStateMath
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] {N : ℕ} (sizes : J → ℕ)

/-- The weighted quadratic score of a partition product state depends continuously on its family
of block states. -/
theorem product_score_continuous (sites : Fin N ≃ Σ j,Fin (sizes j))
    (S : V → HermitianMat (Reg N) ℂ) (w : V → ℝ) :
    Continuous (fun ρ : ∀ j,MState (Reg (sizes j)) => quadraticScore S w (partitionState sizes sites ρ)) := by
  unfold quadraticScore MState.exp_val
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul continuous_const
  apply Continuous.pow
  apply Continuous.inner
  · apply continuous_induced_rng.mpr
    change Continuous (fun ρ : ∀ j,MState (Reg (sizes j)) =>
      ((MState.piProd ρ).M.reindex (partitionRegister sizes sites).symm).mat)
    change Continuous (fun ρ : ∀ j,MState (Reg (sizes j)) =>
      (Matrix.piProd (fun j => (ρ j).m)).submatrix (partitionRegister sizes sites) (partitionRegister sizes sites))
    unfold Matrix.piProd Matrix.submatrix
    fun_prop
  · exact continuous_const

/-- There exists a family of block states whose partition product state maximizes the weighted
quadratic score over all such families. -/
theorem product_score_attained (sites : Fin N ≃ Σ j,Fin (sizes j))
    (S : V → HermitianMat (Reg N) ℂ) (w : V → ℝ) :
    ∃ ρ : ∀ j,MState (Reg (sizes j)),∀ σ : ∀ j,MState (Reg (sizes j)),
      quadraticScore S w (partitionState sizes sites σ) ≤ quadraticScore S w (partitionState sizes sites ρ) := by
  obtain ⟨ρ,_,hρ⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set (∀ j,MState (Reg (sizes j)))).Nonempty from ⟨fun _ => MState.uniform,Set.mem_univ _⟩)
    (product_score_continuous sizes sites S w).continuousOn
  exact ⟨ρ,fun σ => hρ (Set.mem_univ σ)⟩

end Qatlib.Concepts.ShadowModels.ProductPOVM
