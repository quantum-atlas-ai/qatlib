/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPoly06.MainResults

theorem SourceLemma62
    (M : ℕ) (hM : 0 < M) {X : Type*} [Fintype X] [DecidableEq X]
    (p : Fin M → FinDist X) (f : X → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) :
    eventMass (independent p)
      (fun ω => δ ≤ |weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹)
          (fun _ x => f x) ω
        - (independent p).expect
            (weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) (fun _ x => f x))|)
      ≤ 2 * Real.exp (-(M : ℝ) * δ ^ 2 / 4) := by
  classical
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM

  have hSval : (∑ _i : Fin M, (((M : ℝ))⁻¹) ^ 2 * ((1 : ℝ) - 0) ^ 2)
      = ((M : ℝ))⁻¹ := by
    simp only [sub_zero]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hSpos : 0 < ∑ _i : Fin M, (((M : ℝ))⁻¹) ^ 2 * ((1 : ℝ) - 0) ^ 2 := by
    rw [hSval]
    exact inv_pos.mpr hMR

  have hhab : ∀ _i : Fin M, (0 : ℝ) ≤ 1 := fun _ => by norm_num
  have hfI : ∀ (_i : Fin M) (x : X), f x ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ x => hf x
  have hbase :=
    independent_weighted_hoeffding (I := Fin M) p
      (fun _ : Fin M => ((M : ℝ))⁻¹) (fun (_ : Fin M) x => f x)
      (fun _ : Fin M => (0 : ℝ)) (fun _ : Fin M => (1 : ℝ))
      δ hhab hfI hδ hSpos
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  apply Real.exp_le_exp.mpr

  rw [hSval, div_inv_eq_mul]
  nlinarith [hMR.le, sq_nonneg δ, mul_nonneg hMR.le (sq_nonneg δ)]

end Qatlib.Papers.JonesPoly06.MainResults
