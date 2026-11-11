/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Probability.Independence.Basic

set_option backward.isDefEq.respectTransparency false

/-! Supplement Lemma `lemma:collision` of arXiv:2503.20498v1: if an output
string list passes the mixed cross-entropy benchmark `MLXEB_{b,k}`, then
independently resampled strings hit at least one position with probability at
least `bk/N - (bk/N)^2`. The proof content is a second-order Bonferroni bound
for independent events: the union probability is bounded via the product of
complements, and the elementary product inequality
`∏ (1 - pⱼ) ≤ 1 - σ + σ²/2` replaces the paper's inclusion-exclusion
computation. This file proves that core faithfully with the exact constant
(the paper states the remainder as `O(1/N²)`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Qatlib.Papers.RandCertLiu25.MainResults.Collision

/-- Second-order union bound, arithmetic form: products of complements are
bounded by one minus the total mass plus half its square, by induction on the
prefix length. -/
theorem prod_one_sub_le (n : ℕ) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) :
    ∏ j ∈ Finset.range n, (1 - p j) ≤
      1 - (∑ j ∈ Finset.range n, p j) + (∑ j ∈ Finset.range n, p j) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpσ : 0 ≤ ∑ j ∈ Finset.range n, p j := Finset.sum_nonneg (fun j _ => (hp j).1)
      have hpn : 0 ≤ p n := (hp n).1
      have h1pn : 0 ≤ 1 - p n := by linarith [(hp n).2]
      rw [Finset.range_add_one, Finset.prod_insert (Finset.notMem_range_self (n := n)),
        Finset.sum_insert (Finset.notMem_range_self (n := n))]
      calc (1 - p n) * ∏ j ∈ Finset.range n, (1 - p j)
          ≤ (1 - p n) * (1 - ∑ j ∈ Finset.range n, p j
              + (∑ j ∈ Finset.range n, p j) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left ih h1pn
        _ ≤ 1 - (p n + ∑ j ∈ Finset.range n, p j)
            + (p n + ∑ j ∈ Finset.range n, p j) ^ 2 / 2 := by
            have h1 : (1 - p n) * (1 - ∑ j ∈ Finset.range n, p j
                + (∑ j ∈ Finset.range n, p j) ^ 2 / 2)
                = 1 - ∑ j ∈ Finset.range n, p j + (∑ j ∈ Finset.range n, p j) ^ 2 / 2 - p n
                  + p n * ∑ j ∈ Finset.range n, p j
                  - p n * (∑ j ∈ Finset.range n, p j) ^ 2 / 2 := by ring
            have h2 : 1 - (p n + ∑ j ∈ Finset.range n, p j)
                + (p n + ∑ j ∈ Finset.range n, p j) ^ 2 / 2
                = 1 - ∑ j ∈ Finset.range n, p j + (∑ j ∈ Finset.range n, p j) ^ 2 / 2 - p n
                  + p n * ∑ j ∈ Finset.range n, p j + p n ^ 2 / 2 := by ring
            rw [h1, h2]
            nlinarith [hpσ, hpn]

/-- Arithmetic core of the collision lemma: if the per-position hit
probabilities lie in `[0,1]` and sum to `σ ∈ [c, 1]`, then the complement
product satisfies `1 - ∏ (1 - pⱼ) ≥ c - c²`. -/
theorem collision_arith (k : ℕ) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (c : ℝ) (hc : c ≤ ∑ j ∈ Finset.range k, p j) (hσ : ∑ j ∈ Finset.range k, p j ≤ 1) :
    c - c ^ 2 ≤ 1 - ∏ j ∈ Finset.range k, (1 - p j) := by
  set σ := ∑ j ∈ Finset.range k, p j with hσd
  have hpσ : 0 ≤ σ := Finset.sum_nonneg (fun j _ => (hp j).1)
  have hprod : ∏ j ∈ Finset.range k, (1 - p j) ≤ 1 - σ + σ ^ 2 / 2 :=
    prod_one_sub_le k p hp
  have key : σ - σ ^ 2 / 2 ≥ c - c ^ 2 := by
    nlinarith [hc, hσ, hpσ]
  exact le_trans key (by nlinarith [hprod, hpσ])

/-- Probability core of Supplement Lemma `lemma:collision`: for finitely many
independent events whose probabilities sum to `σ ∈ [c, 1]`, the union has
probability at least `c - c²`. The MLXEB application takes `A j` to be the
event that the independently resampled string `sⱼ` equals the fixed output
`zⱼ` and `c = bk/N`, recovering the paper's `bk/N - (bk/N)²` bound exactly
(no asymptotics). -/
theorem collision_probability_lower {Ω : Type} [MeasurableSpace Ω] (k : ℕ)
    (μ : Measure Ω) (A : ℕ → Set Ω) (hA : ∀ j, MeasurableSet (A j))
    (hInd : ProbabilityTheory.iIndep (fun _ : ℕ => ‹MeasurableSpace Ω›) μ)
    (c : ℝ) (hc : c ≤ ∑ j ∈ Finset.range k, (μ (A j)).toReal)
    (hσ : ∑ j ∈ Finset.range k, (μ (A j)).toReal ≤ 1) :
    (μ (⋃ j ∈ Finset.range k, A j)).toReal ≥ c - c ^ 2 := by
  classical
  have hprob : IsProbabilityMeasure μ := hInd.isProbabilityMeasure
  have hAc : ∀ j ∈ Finset.range k, MeasurableSet ((A j)ᶜ) := fun j _ => (hA j).compl
  have hInter : μ (⋂ j ∈ Finset.range k, (A j)ᶜ) = ∏ j ∈ Finset.range k, μ ((A j)ᶜ) :=
    hInd.meas_biInter hAc
  have hle1 : ∀ j, (μ (A j)).toReal ≤ 1 := by
    intro j
    have hle : μ (A j) ≤ 1 := by
      have hle' : μ (A j) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rwa [measure_univ] at hle'
    exact_mod_cast ENNReal.toReal_le_coe_of_le_coe hle
  have hcompl : ∀ j, (μ ((A j)ᶜ)).toReal = 1 - (μ (A j)).toReal := by
    intro j
    have hle : μ (A j) ≤ 1 := by
      have hle' : μ (A j) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rwa [measure_univ] at hle'
    have h1 : (μ ((A j)ᶜ)).toReal = (μ Set.univ - μ (A j)).toReal := by
      rw [measure_compl (hA j) (by simp)]
    rw [measure_univ, ENNReal.toReal_sub_of_le hle (by simp)] at h1
    simpa using h1
  have h2 : (⋃ j ∈ Finset.range k, A j)ᶜ = ⋂ j ∈ Finset.range k, (A j)ᶜ := by
    ext ω
    simp
  have hmeasU : MeasurableSet (⋃ j ∈ Finset.range k, A j) :=
    Finset.measurableSet_biUnion (Finset.range k) (fun j _ => hA j)
  have hμUc : (μ ((⋃ j ∈ Finset.range k, A j)ᶜ)).toReal
      = ∏ j ∈ Finset.range k, (1 - (μ (A j)).toReal) := by
    rw [h2, hInter, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl (fun j _ => hcompl j)
  have hμU : (μ (⋃ j ∈ Finset.range k, A j)).toReal
      = 1 - ∏ j ∈ Finset.range k, (1 - (μ (A j)).toReal) := by
    have hleU : μ (⋃ j ∈ Finset.range k, A j) ≤ 1 := by
      have hle : μ (⋃ j ∈ Finset.range k, A j) ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      rwa [measure_univ] at hle
    have hleUc : μ ((⋃ j ∈ Finset.range k, A j)ᶜ) ≤ 1 := by
      have hle : μ ((⋃ j ∈ Finset.range k, A j)ᶜ) ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      rwa [measure_univ] at hle
    have hcU : μ ((⋃ j ∈ Finset.range k, A j)ᶜ)
        = μ Set.univ - μ (⋃ j ∈ Finset.range k, A j) :=
      measure_compl hmeasU (by simp)
    rw [measure_univ] at hcU
    have hsub : μ (⋃ j ∈ Finset.range k, A j) + μ ((⋃ j ∈ Finset.range k, A j)ᶜ) = 1 := by
      rw [measure_add_measure_compl hmeasU, measure_univ]
    have hmain : μ (⋃ j ∈ Finset.range k, A j) = 1 - μ ((⋃ j ∈ Finset.range k, A j)ᶜ) := by
      rw [← hsub, ENNReal.add_sub_cancel_right (ne_of_lt
        (lt_of_le_of_lt hleUc (by norm_num)))]
    rw [hmain, ENNReal.toReal_sub_of_le hleUc (by simp), hμUc]
    simp
  have harith := collision_arith k (fun j => (μ (A j)).toReal)
    (fun j => ⟨ENNReal.toReal_nonneg, hle1 j⟩) c hc hσ
  rw [hμU]
  exact harith

end Collision
