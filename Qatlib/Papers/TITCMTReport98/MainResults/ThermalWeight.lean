/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TITCMTReport98.MainResults.Defs
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Gibbs weights and ground-state deficiency

This module defines a finite nonempty Boltzmann partition function and its normalized Gibbs
weights, as used in the thermal comparison of [KadowakiNishimori1998]. It expresses the
deficiency of a distinguished level through energy differences and establishes the
low-temperature equivalent for a unique lowest-energy level.

For two levels, the deficiency is the logistic expression `twoLevelGibbsDeficiency`. Different
gaps determine different functions of inverse temperature.

## Main statements

* `sum_gibbsWeight`: the Gibbs weights sum to one.
* `ground_deficiency_eq`: expresses the distinguished-level deficiency through the other energy
  differences.
* `ground_deficiency_lowT_asymptotic`: gives the equivalent as inverse temperature grows.
* `twoLevelGibbsDeficiency_eq`: identifies the two-level logistic formula.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Filter Finset
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The finite Boltzmann partition function `∑ i, exp (-β * E i)`. -/
def boltzmannPartition (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-(β * E i))

/-- The Boltzmann factor of level `i` divided by the partition function. -/
def gibbsWeight (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-(β * E i)) / boltzmannPartition E β

omit [DecidableEq ι] in

/-- The Boltzmann partition function of a finite nonempty collection of real energies is
strictly positive [KadowakiNishimori1998]. -/
theorem boltzmannPartition_pos (E : ι → ℝ) (β : ℝ) : 0 < boltzmannPartition E β := by
  unfold boltzmannPartition
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- Every Gibbs weight in a finite nonempty collection is strictly positive
[KadowakiNishimori1998]. -/
theorem gibbsWeight_pos (E : ι → ℝ) (β : ℝ) (i : ι) : 0 < gibbsWeight E β i := by
  unfold gibbsWeight
  exact div_pos (Real.exp_pos _) (boltzmannPartition_pos E β)

/-- The finite Gibbs weights sum to one [KadowakiNishimori1998]. -/
theorem sum_gibbsWeight (E : ι → ℝ) (β : ℝ) : ∑ i, gibbsWeight E β i = 1 := by
  unfold gibbsWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (boltzmannPartition_pos E β))

/-- Every Gibbs weight is at most one [KadowakiNishimori1998]. -/
theorem gibbsWeight_le_one (E : ι → ℝ) (β : ℝ) (i : ι) : gibbsWeight E β i ≤ 1 := by
  have hsum := sum_gibbsWeight E β
  have hle : gibbsWeight E β i ≤ ∑ j, gibbsWeight E β j :=
    Finset.single_le_sum (fun j _ => (gibbsWeight_pos E β j).le) (Finset.mem_univ i)
  rw [hsum] at hle
  exact hle

omit [Nonempty ι] in

/-- Factors the Boltzmann partition function by the factor of a distinguished level `g`, leaving
one plus the sum of relative Boltzmann factors over `i ≠ g` [KadowakiNishimori1998]. -/
theorem boltzmannPartition_ground_factor (E : ι → ℝ) (β : ℝ) (g : ι) :
    boltzmannPartition E β
      = Real.exp (-(β * E g))
          * (1 + ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g)))) := by
  have hsplit : boltzmannPartition E β
      = Real.exp (-(β * E g))
        + ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * E i)) := by
    unfold boltzmannPartition
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ g)]
    ring
  rw [hsplit, mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.exp_add]
  congr 1
  ring

/-- The deficiency `1 - gibbsWeight E β g` equals the sum of relative Boltzmann factors over `i
≠ g` divided by one plus that sum [KadowakiNishimori1998]. -/
theorem ground_deficiency_eq (E : ι → ℝ) (β : ℝ) (g : ι) :
    1 - gibbsWeight E β g
      = (∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g))))
          / (1 + ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g)))) := by
  have hZ := boltzmannPartition_ground_factor E β g
  have hgpos : 0 < Real.exp (-(β * E g)) := Real.exp_pos _
  unfold gibbsWeight
  rw [hZ]
  have hne : Real.exp (-(β * E g)) ≠ 0 := ne_of_gt hgpos
  have hden : (1 + ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g)))) ≠ 0 := by
    have hnonneg : 0 ≤ ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g))) :=
      Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
    positivity
  field_simp
  ring

/-- If a level other than `g` exists, the deficiency of the Gibbs weight at `g` is strictly
positive [KadowakiNishimori1998]. -/
theorem ground_deficiency_pos (E : ι → ℝ) (β : ℝ) (g : ι)
    (hne : (Finset.univ.erase g).Nonempty) :
    0 < 1 - gibbsWeight E β g := by
  rw [ground_deficiency_eq]
  have hSpos : 0 < ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g))) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) hne
  have hD : 0 < 1 + ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g))) := by
    positivity
  exact div_pos hSpos hD

/-- The deficiency of any distinguished Gibbs weight is strictly less than one
[KadowakiNishimori1998]. -/
theorem ground_deficiency_lt_one (E : ι → ℝ) (β : ℝ) (g : ι) :
    1 - gibbsWeight E β g < 1 := by
  have := gibbsWeight_pos E β g
  linarith

/-- If `g` has strictly lower energy than every other level and another level exists, its Gibbs
deficiency is asymptotically equivalent to the sum of relative Boltzmann factors as `β`
tends to infinity [KadowakiNishimori1998]. -/
theorem ground_deficiency_lowT_asymptotic (E : ι → ℝ) (g : ι)
    (hgap : ∀ i, i ≠ g → E g < E i)
    (hne : (Finset.univ.erase g).Nonempty) :
    Asymptotics.IsEquivalent atTop
      (fun β : ℝ => 1 - gibbsWeight E β g)
      (fun β : ℝ => ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g)))) := by
  set S : ℝ → ℝ := fun β => ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g)))
    with hS
  have hSpos : ∀ β, 0 < S β := fun β =>
    Finset.sum_pos (fun i _ => Real.exp_pos _) hne
  have hSne : ∀ᶠ β in atTop, S β ≠ 0 := Eventually.of_forall (fun β => (hSpos β).ne')
  rw [Asymptotics.isEquivalent_iff_tendsto_one hSne]
  have hratio : ∀ β, (1 - gibbsWeight E β g) / S β = (1 + S β)⁻¹ := by
    intro β
    rw [hS]
    rw [ground_deficiency_eq E β g]
    have hSpos' : 0 < ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g))) :=
      Finset.sum_pos (fun i _ => Real.exp_pos _) hne
    have hD : 1 + ∑ i ∈ Finset.univ.erase g, Real.exp (-(β * (E i - E g))) ≠ 0 := by
      positivity
    field_simp
  refine Tendsto.congr (fun β => (hratio β).symm) ?_
  have hterm : ∀ i ∈ Finset.univ.erase g,
      Tendsto (fun β : ℝ => Real.exp (-(β * (E i - E g)))) atTop (𝓝 0) := by
    intro i hi
    have hmem : i ≠ g := Finset.ne_of_mem_erase hi
    have hgt : 0 < E i - E g := sub_pos.mpr (hgap i hmem)
    have hslope : Tendsto (fun β : ℝ => β * (E i - E g)) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos (f := id) hgt).mpr tendsto_id
    have hcomp : Tendsto (fun β : ℝ => Real.exp (-(β * (E i - E g)))) atTop (𝓝 0) := by
      have h0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hslope
      simpa [Function.comp_def, neg_mul] using h0
    exact hcomp
  have hSlim : Tendsto S atTop (𝓝 (∑ i ∈ Finset.univ.erase g, (0 : ℝ))) :=
    tendsto_finsetSum _ (fun i hi => hterm i hi)
  rw [Finset.sum_const_zero] at hSlim
  have hD : Tendsto (fun β : ℝ => 1 + S β) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hSlim
  have hinv : Tendsto (fun β : ℝ => (1 + S β)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
    hD.inv₀ (by norm_num)
  simpa using hinv

/-- The two-level logistic deficiency `1 / (exp (β * d) + 1)`. -/
def twoLevelGibbsDeficiency (d β : ℝ) : ℝ := 1 / (Real.exp (β * d) + 1)

/-- For two energy levels zero and `d`, the deficiency of the Gibbs weight at level zero equals
`twoLevelGibbsDeficiency d β` [KadowakiNishimori1998]. -/
theorem twoLevelGibbsDeficiency_eq (d β : ℝ) :
    1 - gibbsWeight (fun i : Fin 2 => ![0, d] i) β 0
      = twoLevelGibbsDeficiency d β := by
  have hsum : boltzmannPartition (fun i : Fin 2 => ![0, d] i) β
      = 1 + Real.exp (-(β * d)) := by
    unfold boltzmannPartition
    rw [Fin.sum_univ_two]
    norm_num
  unfold gibbsWeight twoLevelGibbsDeficiency
  rw [hsum]
  have hground : Real.exp (-(β * (fun i : Fin 2 => ![0, d] i) 0)) = 1 := by
    norm_num
  rw [hground]
  rw [Real.exp_neg]
  have hE : Real.exp (β * d) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-- Distinct real gaps give distinct two-level Gibbs-deficiency functions of inverse temperature
[KadowakiNishimori1998]. -/
theorem twoLevelGibbsDeficiency_depends_on_gap {d₁ d₂ : ℝ}
    (hne : d₁ ≠ d₂) :
    twoLevelGibbsDeficiency d₁ ≠ twoLevelGibbsDeficiency d₂ := by
  intro hfun
  have h := congrFun hfun 1
  unfold twoLevelGibbsDeficiency at h
  have e1 : Real.exp (1 * d₁) = Real.exp d₁ := by ring_nf
  have e2 : Real.exp (1 * d₂) = Real.exp d₂ := by ring_nf
  rw [e1, e2] at h
  have hcross : Real.exp d₁ + 1 = Real.exp d₂ + 1 := by
    field_simp at h
    linarith
  have hexp : Real.exp d₁ = Real.exp d₂ := by linarith
  exact hne (Real.exp_injective hexp)

end Qatlib.Papers.TITCMTReport98.MainResults
