/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.GaussianMap
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.FermLinOpt04.MainResults.Model

namespace Qatlib.Papers.FermLinOpt04.MainResults.Claims

theorem lemma6_compose_tp {n : ℕ} (E1 E2 : GaussianMap n)
    (h1 : ∀ X : Fock n, Matrix.trace (E1.toFun X) = Matrix.trace X)
    (h2 : ∀ X : Fock n, Matrix.trace (E2.toFun X) = Matrix.trace X) :
    ∀ X : Fock n, Matrix.trace (E2.toFun (E1.toFun X)) = Matrix.trace X := by
  intro X
  rw [h2, h1]

theorem isCP_comp {n : ℕ} {F G : Fock n →ₗ[ℂ] Fock n}
    (hF : IsCP F) (hG : IsCP G) : IsCP (G.comp F) := by
  obtain ⟨ι1, inst1, A1, h1⟩ := hF
  obtain ⟨ι2, inst2, A2, h2⟩ := hG
  letI := inst1
  letI := inst2
  refine ⟨ι2 × ι1, inferInstance, (fun p : ι2 × ι1 => A2 p.1 * A1 p.2), ?_⟩
  intro X
  simp only [LinearMap.comp_apply]
  rw [h2, h1]
  simp only [Matrix.mul_sum, Finset.sum_mul, Matrix.conjTranspose_mul]
  conv_rhs => rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  noncomm_ring

theorem lemma7_compose_cp {n : ℕ} (E1 E2 : GaussianMap n)
    (h1 : IsCP E1.toFun) (h2 : IsCP E2.toFun) :
    IsCP (E2.toFun.comp E1.toFun) :=
  isCP_comp h1 h2

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
