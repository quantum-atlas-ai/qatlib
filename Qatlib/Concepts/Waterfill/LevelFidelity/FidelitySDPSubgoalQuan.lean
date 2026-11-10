/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySDPSubgoalStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.LevelFidelity
open scoped BigOperators ComplexOrder

private theorem water_trace {m : ℕ} (π σ : Fin m → ℚ) (g : ℝ) :
    (Matrix.trace (sourceWaterMatrix π σ g)).re = levelMass π σ g := by
  simp [Matrix.trace, sourceWaterMatrix, levelMass, pow_two, Complex.re_sum]

private theorem water_overlap {m : ℕ} (π σ : Fin m → ℚ) (g : ℝ) :
    (∑ i, ∑ j, (σ i : ℂ) * sourceWaterMatrix π σ g i j * (σ j : ℂ)).re =
      levelDot π σ g ^ 2 := by
  simp only [Complex.re_sum, sourceWaterMatrix, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im, mul_zero, zero_mul, sub_zero]
  unfold levelDot
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceFidelitySDPSubgoal : SourceFidelitySDPSubgoal := by
  classical
  intro m π σ γlo γhi hπ hσ hπnorm hσnorm hlohi hlow hwit hhigh hwit2 p hpmin hpmax
  obtain ⟨g, hgl, hgh, hfid, hopt⟩ := sourceFidelityLevelSubgoal m π σ γlo γhi
    hπ hσ hπnorm hσnorm hlohi hlow hwit hhigh hwit2 p hpmin hpmax
  have hσpos : ∀ i, (0 : ℝ) < (σ i : ℝ) := fun i => by exact_mod_cast hσ i
  have hπnonneg : ∀ i, (0 : ℝ) ≤ (π i : ℝ) := fun i => by exact_mod_cast hπ i
  have hlo : 0 < γlo := by
    obtain ⟨i, hi, he⟩ := hwit
    have hi' : (0 : ℝ) < (π i : ℝ) := by exact_mod_cast hi
    by_contra hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (hσpos i).le
    linarith
  have hg : 0 ≤ g := hlo.le.trans hgl
  have hfill : ∀ i, 0 ≤ levelFill π σ g i := levelFill_nonneg π σ hπ hσ hg
  refine ⟨g, hgl, hgh, hfid, ?_, ?_, water_trace π σ g, ?_, ?_⟩
  · have he : sourceWaterMatrix π σ g =
        Matrix.vecMulVec (fun i => (levelFill π σ g i : ℂ))
          (star (fun i => (levelFill π σ g i : ℂ))) := by
      ext i j
      simp [sourceWaterMatrix, Matrix.vecMulVec]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star _
  · intro i
    have hb : levelFill π σ g i ≤ (π i : ℝ) := min_le_left _ _
    have hs := (sq_le_sq₀ (hfill i) (hπnonneg i)).mpr hb
    simpa [sourceWaterMatrix, pow_two] using! hs
  · rw [water_overlap, water_trace]
    exact hfid
  · intro M hM hdiag hfidelity
    let v : Fin m → ℝ := fun i => Real.sqrt (M i i).re
    have hd (i : Fin m) : 0 ≤ (M i i).re := (Complex.nonneg_iff.mp hM.diag_nonneg).1
    have hv2 (i : Fin m) : v i ^ 2 = (M i i).re := Real.sq_sqrt (hd i)
    have htrace : (Matrix.trace M).re = ∑ i, v i ^ 2 := by
      simp only [Matrix.trace, Complex.re_sum, hv2]
      rfl
    rw [htrace]
    apply hopt v
    · intro i
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      have hs := hdiag i
      rw [← hv2] at hs
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (hπnonneg i)).mp hs
    · have hbound := psd_weighted_overlap_diagonal m M (fun i => (σ i : ℝ)) hM
        (fun i => (hσpos i).le)
      rw [htrace] at hfidelity
      exact hfidelity.trans (by simpa only [Complex.ofReal_ratCast, v] using! hbound)

end Qatlib.Concepts.Waterfill.LevelFidelity
