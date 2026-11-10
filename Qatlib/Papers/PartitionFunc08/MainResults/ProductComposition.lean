/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PartitionFunc08.MainResults.Model.SchemeDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Qatlib.Papers.PartitionFunc08.MainResults.ProductComposition

theorem lemma3_product_composition
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℓ : ℕ) (hℓ : 0 < ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (α : Fin ℓ → ℝ) (Q : Fin ℓ → Ω → ℝ) (hα : ∀ i, 0 < α i)
    (hQ : ∀ i, Measurable (Q i))
    (hacc : ∀ i,
      1 - 1 / (4 * (ℓ : ℝ)) ≤
        μ.real (relAccEvent (α i) (ε / (2 * (ℓ : ℝ))) (Q i))) :
    3 / 4 ≤ μ.real (relAccEvent (∏ i, α i) ε (fun ω => ∏ i, Q i ω)) := by
  classical
  set A : Fin ℓ → Set Ω :=
    fun i => relAccEvent (α i) (ε / (2 * (ℓ : ℝ))) (Q i) with hA
  have hAmeas : ∀ i, MeasurableSet (A i) := by
    intro i
    have hset : A i =
        Q i ⁻¹' Set.Icc ((1 - ε / (2 * (ℓ : ℝ))) * α i)
          ((1 + ε / (2 * (ℓ : ℝ))) * α i) := by
      ext ω
      simp [hA, relAccEvent, Set.mem_Icc]
    rw [hset]
    exact measurableSet_Icc.preimage (hQ i)
  have hcompl : ∀ i, μ.real (A i)ᶜ = 1 - μ.real (A i) := by
    intro i
    rw [measureReal_compl (hAmeas i), probReal_univ]
  have hUnionLe : μ.real (⋃ i, (A i)ᶜ) ≤ 1 / 4 := by
    calc
      μ.real (⋃ i, (A i)ᶜ) ≤ ∑ i, μ.real ((A i)ᶜ) := measureReal_iUnion_fintype_le _
      _ = ∑ i, (1 - μ.real (A i)) := by simp [hcompl]
      _ ≤ ∑ _i : Fin ℓ, (1 / (4 * (ℓ : ℝ))) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have := hacc i
            linarith
      _ = 1 / 4 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
            have h4lne : (4 : ℝ) * (ℓ : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hℓpos)
            rw [mul_one_div, div_eq_iff h4lne]
            ring
  have hUnionMeas : MeasurableSet (⋃ i, (A i)ᶜ) :=
    MeasurableSet.iUnion (fun i => (hAmeas i).compl)
  have hinter : 3 / 4 ≤ μ.real (⋂ i, A i) := by
    have hset : (⋂ i, A i) = (⋃ i, (A i)ᶜ)ᶜ := by
      rw [Set.compl_iUnion]
      simp
    rw [hset, measureReal_compl hUnionMeas, probReal_univ]
    linarith
  refine le_trans hinter (measureReal_mono ?_)
  intro ω hω
  simp only [Set.mem_iInter, hA, relAccEvent, Set.mem_setOf_eq] at hω ⊢
  exact prod_rel_acc hℓ hε0 hε1 hα hω

end Qatlib.Papers.PartitionFunc08.MainResults.ProductComposition
