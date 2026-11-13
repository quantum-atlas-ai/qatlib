/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityLevelSubgoalStat

/-!
# Existence and optimality of source-constrained fidelity levels

The theorem `sourceFidelityLevelSubgoal` proves that normalized nonnegative rational source and
positive target profiles possess a water level in a tight nondegenerate bracket for every
threshold between `waterPmin` and `waterPmax`. The selected profile maximizes squared mass among
source-box competitors satisfying the fidelity inequality, as in quantum rejection sampling
[OzolsRoettelerRoland2013].

## Main statements

* `sourceFidelityLevelSubgoal`: establish the water-level existence and source-box optimality
  statement.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.LevelFidelity

open scoped BigOperators

/-- For normalized nonnegative source and positive target profiles with tight distinct bracket
endpoints, every threshold between `waterPmin` and `waterPmax` has a bracketed water level
satisfying the fidelity equality and maximizing squared mass among feasible source-box
vectors [OzolsRoettelerRoland2013]. -/
theorem sourceFidelityLevelSubgoal : SourceFidelityLevelSubgoal := by
  intro m π σ γlo γhi hπ hσ hπnorm _hσnorm hlohi hlow hwit hhigh hwit2 p hpmin hpmax
  obtain ⟨i₀, hπ₀, heq₀⟩ := hwit
  obtain ⟨i₁, hπ₁, heq₁⟩ := hwit2
  have hσpos : ∀ i, (0 : ℝ) < (σ i : ℝ) := fun i => by exact_mod_cast hσ i
  have hπ₀' : (0 : ℝ) < (π i₀ : ℝ) := by exact_mod_cast hπ₀
  have hγlo : (0 : ℝ) < γlo := by
    by_contra hcon
    have hle : γlo ≤ 0 := le_of_not_gt hcon
    have hprod : (0 : ℝ) ≤ (-γlo) * (σ i₀ : ℝ) :=
      mul_nonneg (neg_nonneg.mpr hle) (hσpos i₀).le
    have hle2 : γlo * (σ i₀ : ℝ) ≤ 0 := by nlinarith [hprod]
    rw [heq₀] at hle2
    exact absurd hπ₀' (not_lt.mpr hle2)
  have hPmaxpos : (0 : ℝ) < waterPmax π σ := by
    have hterm : (0 : ℝ) < if 0 < π i₀ then (σ i₀ : ℝ) ^ 2 else 0 := by
      rw [if_pos hπ₀]
      exact sq_pos_of_ne_zero (ne_of_gt (hσpos i₀))
    have hrest : (0 : ℝ) ≤ ∑ i ∈ Finset.univ.erase i₀,
        (if 0 < π i then (σ i : ℝ) ^ 2 else 0) :=
      Finset.sum_nonneg fun i _ => by
        split
        · exact sq_nonneg _
        · exact le_rfl
    have hsum : (∑ i ∈ Finset.univ.erase i₀,
        (if 0 < π i then (σ i : ℝ) ^ 2 else 0)) +
        (if 0 < π i₀ then (σ i₀ : ℝ) ^ 2 else 0) =
        ∑ i, (if 0 < π i then (σ i : ℝ) ^ 2 else 0) :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i₀)
    unfold waterPmax
    linarith [hterm, hrest, hsum]
  have hfilllo : ∀ i : Fin m, levelFill π σ γlo i =
      if 0 < π i then γlo * (σ i : ℝ) else 0 := by
    intro i
    by_cases hpi : 0 < π i
    · unfold levelFill
      rw [min_eq_right (hlow i hpi), if_pos hpi]
    · have hπi0 : (π i : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hpi)
      have hc : (π i : ℝ) ≤ γlo * (σ i : ℝ) :=
        hπi0.trans (mul_nonneg hγlo.le (hσpos i).le)
      unfold levelFill
      rw [min_eq_left hc, if_neg hpi]
      exact_mod_cast (show π i = 0 from le_antisymm (le_of_not_gt hpi) (hπ i))
  have hAlo : levelDot π σ γlo = γlo * waterPmax π σ := by
    unfold levelDot waterPmax
    have per : ∀ i : Fin m, (σ i : ℝ) * levelFill π σ γlo i =
        γlo * (if 0 < π i then (σ i : ℝ) ^ 2 else 0) := by
      intro i
      rw [hfilllo i]
      by_cases hpi : 0 < π i
      · simp only [hpi, if_true]
        ring
      · simp only [hpi, if_false]
        ring
    rw [show ∑ i, (σ i : ℝ) * levelFill π σ γlo i =
        ∑ i, (γlo * (if 0 < π i then (σ i : ℝ) ^ 2 else 0)) from
      Finset.sum_congr rfl fun i _ => per i, Finset.mul_sum]
  have hBlo : levelMass π σ γlo = γlo * γlo * waterPmax π σ := by
    unfold levelMass waterPmax
    have per : ∀ i : Fin m, (levelFill π σ γlo i) ^ 2 =
        γlo * γlo * (if 0 < π i then (σ i : ℝ) ^ 2 else 0) := by
      intro i
      rw [hfilllo i]
      by_cases hpi : 0 < π i
      · simp only [hpi, if_true]
        ring
      · simp only [hpi, if_false]
        ring
    rw [show ∑ i, (levelFill π σ γlo i) ^ 2 =
        ∑ i, (γlo * γlo * (if 0 < π i then (σ i : ℝ) ^ 2 else 0)) from
      Finset.sum_congr rfl fun i _ => per i, Finset.mul_sum]
  have hAhi : levelDot π σ γhi = ∑ i, (π i : ℝ) * (σ i : ℝ) := by
    unfold levelDot
    exact Finset.sum_congr rfl fun i _ => by
      rw [show levelFill π σ γhi i = (π i : ℝ) from min_eq_left (hhigh i)]
      ring
  have hBhi : levelMass π σ γhi = 1 := by
    unfold levelMass
    rw [show ∑ i, (levelFill π σ γhi i) ^ 2 = ∑ i, ((π i : ℝ) ^ 2) from
      Finset.sum_congr rfl fun i _ => by
        rw [show levelFill π σ γhi i = (π i : ℝ) from min_eq_left (hhigh i)]]
    exact hπnorm
  have contFill : ∀ i : Fin m, Continuous (fun γ : ℝ => levelFill π σ γ i) := by
    intro i
    unfold levelFill
    fun_prop
  have contA : Continuous (fun γ : ℝ => levelDot π σ γ) := by
    unfold levelDot
    exact continuous_finsetSum Finset.univ fun i _ => continuous_const.mul (contFill i)
  have contB : Continuous (fun γ : ℝ => levelMass π σ γ) := by
    unfold levelMass
    exact continuous_finsetSum Finset.univ fun i _ => (contFill i).pow 2
  have contf : Continuous (fun γ : ℝ =>
      levelDot π σ γ ^ 2 - p * levelMass π σ γ) :=
    (contA.pow 2).sub (continuous_const.mul contB)
  have hflo : (0 : ℝ) ≤ levelDot π σ γlo ^ 2 - p * levelMass π σ γlo := by
    have key : levelDot π σ γlo ^ 2 - p * levelMass π σ γlo =
        γlo * γlo * (waterPmax π σ - p) * waterPmax π σ := by
      rw [hAlo, hBlo]; ring
    rw [key]
    have h2 : (0 : ℝ) ≤ γlo * γlo := mul_nonneg hγlo.le hγlo.le
    have h3 : (0 : ℝ) ≤ waterPmax π σ - p := by linarith
    exact mul_nonneg (mul_nonneg h2 h3) hPmaxpos.le
  have hfhi : levelDot π σ γhi ^ 2 - p * levelMass π σ γhi ≤ 0 := by
    rw [hAhi, hBhi, mul_one]
    unfold waterPmin at hpmin
    linarith
  have hivt := intermediate_value_Icc' hlohi.le contf.continuousOn
  have hzero : (0 : ℝ) ∈ Set.Icc (levelDot π σ γhi ^ 2 - p * levelMass π σ γhi)
      (levelDot π σ γlo ^ 2 - p * levelMass π σ γlo) := ⟨hfhi, hflo⟩
  obtain ⟨gbar, hgmem, _heqraw⟩ := (Set.mem_image _ _ _).mp (hivt hzero)
  have hgbar_eq : levelDot π σ gbar ^ 2 - p * levelMass π σ gbar = 0 := _heqraw
  have hgpeg : levelDot π σ gbar ^ 2 = p * levelMass π σ gbar :=
    sub_eq_zero.mp hgbar_eq
  have hBlo' : (0 : ℝ) < levelMass π σ γlo := by
    rw [hBlo]
    exact mul_pos (mul_pos hγlo hγlo) hPmaxpos
  have hBgbar : (0 : ℝ) < levelMass π σ gbar :=
    lt_of_lt_of_le hBlo' (levelMass_mono π σ hπ hσ hγlo.le hgmem.1)
  have hgbpos : (0 : ℝ) < gbar := lt_of_lt_of_le hγlo hgmem.1
  refine ⟨gbar, hgmem.1, hgmem.2, hgpeg, ?_⟩
  intro v hv hfaith
  by_cases hle : (∑ i, v i ^ 2) ≤ levelMass π σ gbar
  · exact hle
  · exfalso
    have hper : ∀ i : Fin m, v i ^ 2 ≤ (π i : ℝ) ^ 2 := by
      intro i
      have h0 : (0 : ℝ) ≤ v i := (hv i).1
      have h1 : v i ≤ (π i : ℝ) := (hv i).2
      nlinarith [h0, h1]
    have hvle1 : (∑ i, v i ^ 2) ≤ 1 := by
      calc (∑ i, v i ^ 2) ≤ ∑ i, ((π i : ℝ) ^ 2) :=
            Finset.sum_le_sum fun i _ => hper i
        _ = 1 := hπnorm
    have hivt2 := intermediate_value_Icc hgmem.2 contB.continuousOn
    have hmem : (∑ i, v i ^ 2) ∈ Set.Icc (levelMass π σ gbar) (levelMass π σ γhi) :=
      ⟨le_of_not_ge hle, hvle1.trans_eq hBhi.symm⟩
    obtain ⟨gstar, hgsmem, _heqraw2⟩ := (Set.mem_image _ _ _).mp (hivt2 hmem)
    have hgs_eq : levelMass π σ gstar = ∑ i, v i ^ 2 := _heqraw2
    have hgspos : (0 : ℝ) < gstar := lt_of_lt_of_le hγlo (hgmem.1.trans hgsmem.1)
    have hgblt : gbar < gstar := by
      by_contra hcon
      have hmono := levelMass_mono π σ hπ hσ hgspos.le (le_of_not_gt hcon)
      rw [hgs_eq] at hmono
      exact absurd hmono hle
    have hov := levelOverlapLe π σ hσ hgspos v hv hgs_eq.ge
    have hAnonneg : (0 : ℝ) ≤ levelDot π σ gstar := by
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hσpos i).le
        (levelFill_nonneg π σ hπ hσ hgspos.le i)
    have hvnonneg : (0 : ℝ) ≤ ∑ i, (σ i : ℝ) * v i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hσpos i).le (hv i).1
    have hsq : (∑ i, (σ i : ℝ) * v i) ^ 2 ≤ levelDot π σ gstar ^ 2 := by
      nlinarith [hvnonneg, hov, hAnonneg]
    have hanti := levelFidelityStrictAnti m π σ γlo γhi hπ hσ hlohi hlow
      ⟨i₀, hπ₀, heq₀⟩ hhigh ⟨i₁, hπ₁, heq₁⟩ hgbpos hgblt hgmem.1 hgsmem.2
    rw [hgpeg, hgs_eq] at hanti
    have hc1 : p * levelMass π σ gbar * (∑ i, v i ^ 2) ≤
        levelMass π σ gbar * (∑ i, (σ i : ℝ) * v i) ^ 2 := by
      nlinarith [hfaith, hBgbar]
    have hc2 : levelMass π σ gbar * (∑ i, (σ i : ℝ) * v i) ^ 2 ≤
        levelMass π σ gbar * levelDot π σ gstar ^ 2 := by
      nlinarith [hsq, hBgbar]
    linarith [hanti, hc1, hc2]

end Qatlib.Concepts.Waterfill.LevelFidelity
