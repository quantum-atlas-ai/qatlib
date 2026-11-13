/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Qatlib.Papers.PartitionFunc08.MainResults.Model.SchemeDefs

/-!
# Median amplification of ratio estimators

The predicate `IsMedianOf` bounds the number of observations strictly above or below a candidate
median. A majority of accurate estimates forces the median into the same interval, and
independent failure indicators give the exponential probability bound used by `lemma2_powering`.
These estimates form part of the partition-function scheme in [WocjanEtAl2009a].

## Main statements

* `median_mem_Icc`: If more than `k` of `2 * k + 1` values lie in a closed interval, any value
  satisfying the median rank bounds lies in that interval.
* `lemma2_powering`: A measurable median of the estimators has relative-accuracy probability at
  least `1 - δboost` under the independent failure-indicator assumptions and the exponential
  failure budget.

## References

* [Wocjan et al., 2009][WocjanEtAl2009a]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace Qatlib.Papers.PartitionFunc08.MainResults.Powering

open ProbabilityTheory

/-- The condition that at most `k` of the `2 * k + 1` values lie strictly below `m` and at most
`k` lie strictly above it. -/
def IsMedianOf (k : ℕ) (x : Fin (2 * k + 1) → ℝ) (m : ℝ) : Prop :=
  (Finset.univ.filter (fun i => x i < m)).card ≤ k ∧
    (Finset.univ.filter (fun i => m < x i)).card ≤ k

/-- If more than `k` of `2 * k + 1` values lie in a closed interval, any value satisfying the
median rank bounds lies in that interval. See [Wocjan et al., 2009][WocjanEtAl2009a]. -/
theorem median_mem_Icc {k : ℕ} {x : Fin (2 * k + 1) → ℝ} {m L U : ℝ}
    {s : Finset (Fin (2 * k + 1))} (hcard : k < s.card)
    (hs : ∀ i ∈ s, x i ∈ Set.Icc L U)
    (hlt : (Finset.univ.filter (fun i => x i < m)).card ≤ k)
    (hgt : (Finset.univ.filter (fun i => m < x i)).card ≤ k) :
    m ∈ Set.Icc L U := by
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have hmL : m < L := lt_of_not_ge hcon
    have hsub : s ⊆ Finset.univ.filter (fun i => m < x i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le hmL (hs i hi).1
    have := Finset.card_le_card hsub
    omega
  · by_contra hcon
    have hUm : U < m := lt_of_not_ge hcon
    have hsub : s ⊆ Finset.univ.filter (fun i => x i < m) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hs i hi).2 hUm
    have := Finset.card_le_card hsub
    omega

/-- For independent measurable zero-one failure indicators with means at most `1 - p` and `p > 1
/ 2`, the probability of at least `k + 1` failures satisfies the stated exponential bound.
See [Wocjan et al., 2009][WocjanEtAl2009a]. -/
theorem powering_failure_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) {p : ℝ} (hp : 1 / 2 < p)
    (X : Fin (2 * k + 1) → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hindep : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≤ 1 - p) :
    μ.real {ω | (k : ℝ) + 1 ≤ ∑ i, X i ω} ≤
      Real.exp (-(2 * (((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p)) ^ 2) /
        (2 * (k : ℝ) + 1)) := by
  classical
  set ε : ℝ := ((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    nlinarith [hp, hk0]

  set c₀ : ℝ≥0 := ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) with hc0def
  have hcval : c₀ = 1 / 4 := by
    rw [hc0def]
    have h1 : (‖(1 : ℝ) - 0‖₊ : ℝ≥0) = 1 := by
      apply NNReal.coe_injective
      simp
    rw [h1]
    apply NNReal.coe_injective
    push_cast
    norm_num
  have hcR : (c₀ : ℝ) = 1 / 4 := by
    rw [hcval]
    simp

  have hmemIcc : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards with ω
    rcases hX01 i ω with h | h <;> simp [h]
  have hsubG : ∀ i, HasSubgaussianMGF (fun ω => X i ω - ∫ ω, X i ω ∂μ) c₀ μ := by
    intro i
    rw [hc0def]
    exact hasSubgaussianMGF_of_mem_Icc (hmeas i).aemeasurable (hmemIcc i)

  have hindepY : iIndepFun (fun i ω => X i ω - ∫ ω, X i ω ∂μ) μ := by
    have h := hindep.comp (fun i x => x - ∫ ω, X i ω ∂μ)
      (fun i => measurable_id.sub measurable_const)
    simpa [Function.comp_def] using h
  have hhoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (μ := μ) (X := fun i ω => X i ω - ∫ ω, X i ω ∂μ) hindepY (s := Finset.univ)
    (c := fun _ => c₀) (fun i _ => hsubG i) hε.le

  have hsubset : {ω | (k : ℝ) + 1 ≤ ∑ i, X i ω} ⊆
      {ω | ε ≤ ∑ i, (X i ω - ∫ ω, X i ω ∂μ)} := by
    intro ω hω
    have hsum_le : ∑ i : Fin (2 * k + 1), (∫ ω, X i ω ∂μ) ≤ (2 * (k : ℝ) + 1) * (1 - p) := by
      calc ∑ i : Fin (2 * k + 1), (∫ ω, X i ω ∂μ)
          ≤ ∑ _i : Fin (2 * k + 1), (1 - p) := Finset.sum_le_sum (fun i _ => hmean i)
        _ = (2 * (k : ℝ) + 1) * (1 - p) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_add, Nat.cast_mul]
            norm_num
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [Finset.sum_sub_distrib, hεdef]
    linarith
  refine (measureReal_mono hsubset).trans ?_

  have hsum_c : (∑ i ∈ (Finset.univ : Finset (Fin (2 * k + 1))), c₀) =
      ((2 * k + 1 : ℕ) : ℝ≥0) * c₀ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : (((∑ i ∈ (Finset.univ : Finset (Fin (2 * k + 1))), c₀) : ℝ≥0) : ℝ) =
      ((2 * k : ℝ) + 1) * (1 / 4) := by
    rw [hsum_c, show ((((2 * k + 1 : ℕ) : ℝ≥0) * c₀ : ℝ≥0) : ℝ) =
      ((((2 * k + 1 : ℕ) : ℝ≥0) : ℝ) * (c₀ : ℝ)) from NNReal.coe_mul _ _,
      hcR]
    push_cast <;> ring
  have htail : Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ (Finset.univ : Finset (Fin (2 * k + 1))),
        c₀) : ℝ≥0) : ℝ))
      ≤ Real.exp (-(2 * ε ^ 2) / (2 * (k : ℝ) + 1)) := by
    apply Real.exp_le_exp.mpr
    rw [hcast]
    have hA : (2 * (k : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    field_simp
    linarith
  simpa using hhoeff.trans htail

/-- The exponential majority-failure bound is at most positive `δ` when its squared deviation
satisfies the stated logarithmic budget. -/
theorem powering_delta_bound {k : ℕ} {p δ : ℝ} (hp : 1 / 2 < p) (hδ0 : 0 < δ)
    (h : ((2 * (k : ℝ) + 1) / 2) * Real.log (1 / δ) ≤
      (((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p)) ^ 2) :
    Real.exp (-(2 * (((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p)) ^ 2) /
      (2 * (k : ℝ) + 1)) ≤ δ := by
  set ε : ℝ := ((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p) with hεdef
  have hn : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have hlog : Real.log (1 / δ) ≤ 2 * ε ^ 2 / (2 * (k : ℝ) + 1) := by
    have h2 : ((2 * (k : ℝ) + 1) / 2) * Real.log (1 / δ) ≤ ε ^ 2 := by
      rw [hεdef]
      exact h
    rw [le_div_iff₀ hn]
    linarith
  have hexp_le : Real.exp (-(2 * ε ^ 2) / (2 * (k : ℝ) + 1)) ≤
      Real.exp (-Real.log (1 / δ)) := by
    apply Real.exp_le_exp.mpr
    have : -(2 * ε ^ 2) / (2 * (k : ℝ) + 1) = -(2 * ε ^ 2 / (2 * (k : ℝ) + 1)) := by ring
    rw [this]
    linarith
  refine hexp_le.trans ?_
  rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hδ0), one_div, inv_inv]

/-- A measurable median of the estimators has relative-accuracy probability at least `1 -
δboost` under the independent failure-indicator assumptions and the exponential failure
budget. See [Wocjan et al., 2009][WocjanEtAl2009a]. -/
theorem lemma2_powering
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) {p : ℝ} (hp : 1 / 2 < p)
    (X : Fin (2 * k + 1) → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hindep : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≤ 1 - p)
    {q εR : ℝ} (hq0 : 0 < q)
    (Z : Fin (2 * k + 1) → Ω → ℝ)
    (hacc : ∀ i ω, X i ω = 0 → (1 - εR) * q ≤ Z i ω ∧ Z i ω ≤ (1 + εR) * q)
    (W : Ω → ℝ) (hWmeas : Measurable W)
    (hW : ∀ ω, IsMedianOf k (fun i => Z i ω) (W ω))
    {δboost : ℝ}
    (hδ : Real.exp (-(2 * (((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p)) ^ 2) /
      (2 * (k : ℝ) + 1)) ≤ δboost) :
    1 - δboost ≤ μ.real (relAccEvent q εR W) := by
  classical
  set B : Set Ω := relAccEvent q εR W with hB
  have hBmeas : MeasurableSet B := by
    have hset : B = W ⁻¹' Set.Icc ((1 - εR) * q) ((1 + εR) * q) := by
      ext ω
      simp [hB, relAccEvent, Set.mem_Icc]
    rw [hset]
    exact measurableSet_Icc.preimage hWmeas

  have hcompl_sub : Bᶜ ⊆ {ω | (k : ℝ) + 1 ≤ ∑ i, X i ω} := by
    intro ω hω
    by_contra hF
    simp only [Set.mem_setOf_eq, not_le] at hF

    have hsum_eq : ∑ i : Fin (2 * k + 1), X i ω =
        ((Finset.univ.filter (fun i => X i ω = 1)).card : ℝ) := by
      rw [← Finset.sum_boole (fun i => X i ω = 1) (Finset.univ)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases hX01 i ω with h | h <;> simp [h]
    have hfail_lt : (Finset.univ.filter (fun i => X i ω = 1)).card < k + 1 := by
      have hlt : ((Finset.univ.filter (fun i => X i ω = 1)).card : ℝ) < (k + 1 : ℕ) := by
        rw [← hsum_eq]; push_cast; linarith
      exact_mod_cast hlt
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * k + 1)))) (p := fun i => X i ω = 1)
    have huniv : (Finset.univ : Finset (Fin (2 * k + 1))).card = 2 * k + 1 := by simp
    rw [huniv] at hsplit
    set s : Finset (Fin (2 * k + 1)) := Finset.univ.filter (fun i => ¬ X i ω = 1) with hsdef
    have hscard : k < s.card := by
      have hsplit' : (Finset.univ.filter (fun i => X i ω = 1)).card + s.card = 2 * k + 1 := by
        rw [hsdef]
        simpa using hsplit
      omega

    have hsacc : ∀ i ∈ s, Z i ω ∈ Set.Icc ((1 - εR) * q) ((1 + εR) * q) := by
      intro i hi
      rw [hsdef, Finset.mem_filter] at hi
      have hzero : X i ω = 0 := by
        rcases hX01 i ω with h | h
        · exact h
        · exact absurd h hi.2
      exact Set.mem_Icc.mpr (hacc i ω hzero)
    have hmed := median_mem_Icc (k := k) (x := fun i => Z i ω) (m := W ω)
      (L := (1 - εR) * q) (U := (1 + εR) * q) hscard hsacc (hW ω).1 (hW ω).2
    exact hω (Set.mem_Icc.mp hmed)
  have hBc : μ.real Bᶜ = 1 - μ.real B := by
    rw [measureReal_compl hBmeas, probReal_univ]
  have hle : μ.real Bᶜ ≤ δboost :=
    (measureReal_mono hcompl_sub).trans
      ((powering_failure_bound μ k hp X hmeas hX01 hindep hmean).trans hδ)
  linarith

end Qatlib.Papers.PartitionFunc08.MainResults.Powering
