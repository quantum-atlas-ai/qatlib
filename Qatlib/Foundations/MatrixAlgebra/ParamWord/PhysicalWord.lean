/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.ActualContract
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix.Norms.L2Operator RightActions
namespace Qatlib.Foundations.MatrixAlgebra.ParamWord
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
local instance : CStarAlgebra (Matrix I I ℂ) where
local instance : NormedAlgebra ℝ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _

omit [Nonempty I] in

theorem matrix_paramWord_eq_prod {K : ℕ} (F : Fin K→EuclideanSpace ℝ (Fin K)→Matrix I I ℂ)
    (js : List (Fin K)) (θ : EuclideanSpace ℝ (Fin K)) :
    paramWord F js θ=(js.map (fun j => F j θ)).prod := by
  induction js with
  | nil => rfl
  | cons j js ih => simpa only [paramWord,List.map_cons,List.prod_cons] using congrArg (fun A => F j θ*A) ih

omit [Nonempty I] in

theorem exponentialWord_eq_source {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) :
    exponentialWord G W θ=
      (List.ofFn (fun j : Fin K => NormedSpace.exp ((-Complex.I*(θ j:ℂ)) • G j)*W j)).prod := by
  rw [exponentialWord,matrix_paramWord_eq_prod,← List.ofFn_eq_map]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  rw [expSlot_eq_evolve]
  unfold Qatlib.Foundations.MatrixGeometry.SpectralCutoff.evolve
  apply congrArg (fun z : ℂ => NormedSpace.exp (z • G j)*W j)
  push_cast
  ring

omit [Nonempty I] in

theorem exponentialWord_unitary {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (hG : ∀j,(G j).IsHermitian) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : exponentialWord G W θ∈unitary (Matrix I I ℂ) := by
  have h (js : List (Fin K)) : paramWord (fun j => expSlot (G j) (W j) j) js θ∈unitary (Matrix I I ℂ) := by
    induction js with
    | nil => exact (unitary _).one_mem
    | cons j js ih => exact (unitary _).mul_mem (expSlot_unitary _ _ _ (hG j) (hW j) θ) ih
  exact h _

omit [Nonempty I] in

theorem wordState_norm_eq {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hG : ∀j,(G j).IsHermitian) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖wordState G W ψ θ‖=‖ψ‖ := by
  let f := Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)
  have hu := exponentialWord_unitary G W hG hW θ
  have h1 := congrArg f (Unitary.star_mul_self_of_mem hu)
  have h2 := congrArg f (Unitary.mul_star_self_of_mem hu)
  have ht : f (exponentialWord G W θ)∈unitary (EuclideanSpace ℂ I→L[ℂ]EuclideanSpace ℂ I) := by
    rw [Unitary.mem_iff]
    exact ⟨by simpa only [map_mul,map_star,map_one] using h1,
      by simpa only [map_mul,map_star,map_one] using h2⟩
  exact ContinuousLinearMap.norm_map_of_mem_unitary ht ψ
end Qatlib.Foundations.MatrixAlgebra.ParamWord
