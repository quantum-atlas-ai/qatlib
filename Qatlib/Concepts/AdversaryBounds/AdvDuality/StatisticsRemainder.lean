/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.StatisticsRemainderDefs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Finite-sample obstructions to variance bounds

The rare-event family has variance `(D - 1) * A^2` while an all-zero sample remains likely.
`no_uniform_finite_sample_variance_upper` uses this family to show that any real-valued pilot
based on a fixed number of samples can underestimate variance with arbitrarily high probability;
the result also extends to any finite nonempty family of pilots.

The module also gives the exact rare-outcome probability for a bounded rejection sampler. These
results clarify the role of variance information in Monte Carlo estimation, the setting of
[Montanaro2015].

## Main statements

* `rare_variance`: computes the variance of the rare-event family.
* `no_uniform_finite_seed_variance_upper`: gives simultaneous underestimation for every pilot in
  a finite family.
* `rareSampler_return`: computes a bounded sampler's rare-outcome mass.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped Classical ENNReal

/-- The variance of `rareValue D A` under `rareBitLaw D hD` is `(D - 1) * A^2`. -/
theorem rare_variance (D A : ℕ) (hD : 2 ≤ D) :
    (rareBitLaw D hD).variance (rareValue D A) = ((D : ℝ) - 1) * (A : ℝ) ^ 2 := by
  have hne : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Fintype.sum_bool, rareBitLaw, rareValue,
    Bool.false_eq_true, ↓reduceIte]
  push_cast
  field_simp
  ring

/-- If the pilot underestimates variance on the all-zero sample, its failure probability is at
least `(1 - 1 / D)^m`. -/
theorem pilotFailure_lower (D A m : ℕ) (hD : 2 ≤ D)
    (pilot : (Fin m → ℝ) → ℝ)
    (hB : pilot (fun _ => 0) < (rareBitLaw D hD).variance (rareValue D A)) :
    (1 - 1 / (D : ℝ)) ^ m ≤ pilotFailure D A m hD pilot := by
  have hp : (rareBitLaw D hD).probOf (fun _ : Fin m => false) = (1 - 1 / (D : ℝ)) ^ m := by
    simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf, rareBitLaw]
  rw [← hp]
  apply Finset.single_le_sum
  · intro ω _
    exact Finset.prod_nonneg fun i _ => (rareBitLaw D hD).nonneg (ω i)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [rareValue, Bool.false_eq_true, ↓reduceIte] using hB

/-- For `0 ≤ p ≤ 1`, Bernoulli's inequality gives `1 - m * p ≤ (1 - p)^m`. -/
theorem pow_one_sub_lower (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * p ≤ (1 - p) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp1)
      have hmp : 0 ≤ (m : ℝ) * p * p := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hp) hp
      rw [pow_succ]
      push_cast
      nlinarith

/-- For every real-valued pilot based on `m` samples and every `k`, a rare-event distribution
makes it underestimate variance with probability at least `1 - 1 / (k + 1)`. -/
theorem no_uniform_finite_sample_variance_upper (m k : ℕ)
    (pilot : (Fin m → ℝ) → ℝ) :
    ∃ D A : ℕ, ∃ hD : 2 ≤ D,
      pilot (fun _ => 0) < (rareBitLaw D hD).variance (rareValue D A) ∧
      1 - 1 / ((k : ℝ) + 1) ≤ pilotFailure D A m hD pilot := by
  let D := (m + 1) * (k + 1) + 1
  have hD : 2 ≤ D := by dsimp [D]; nlinarith
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨A, hA⟩ := exists_nat_gt (max (pilot (fun _ => 0)) 1)
  have hAB : pilot (fun _ => 0) < A := lt_of_le_of_lt (le_max_left _ _) hA
  have hA1 : (1 : ℝ) < A := lt_of_le_of_lt (le_max_right _ _) hA
  have hAA : (A : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith
  have hvar : (A : ℝ) ^ 2 ≤ ((D : ℝ) - 1) * (A : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (D : ℝ) - 2 by linarith) (sq_nonneg (A : ℝ))]
  have hB : pilot (fun _ => 0) < (rareBitLaw D hD).variance (rareValue D A) := by
    rw [rare_variance]
    exact lt_of_lt_of_le (lt_of_lt_of_le hAB hAA) hvar
  refine ⟨D, A, hD, hB, ?_⟩
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmk : (m : ℝ) / D ≤ 1 / ((k : ℝ) + 1) := by
    apply (div_le_div_iff₀ hDp hkp).mpr
    dsimp [D]
    push_cast
    nlinarith
  calc
    1 - 1 / ((k : ℝ) + 1) ≤ 1 - (m : ℝ) * (1 / (D : ℝ)) := by
      simpa only [mul_one_div] using sub_le_sub_left hmk 1
    _ ≤ (1 - 1 / (D : ℝ)) ^ m :=
      pow_one_sub_lower _ (by positivity) ((div_le_one hDp).mpr hD1) m
    _ ≤ _ := pilotFailure_lower D A m hD pilot hB

/-- For any finite nonempty family of pilots, a single rare-event distribution makes all pilots
underestimate variance simultaneously with probability at least `1 - 1 / (k + 1)`. -/
theorem no_uniform_finite_seed_variance_upper {R : Type} [Fintype R] [Nonempty R]
    (m k : ℕ) (pilot : R → (Fin m → ℝ) → ℝ) :
    ∃ D A : ℕ, ∃ hD : 2 ≤ D,
      (∀ r, pilot r (fun _ => 0) < (rareBitLaw D hD).variance (rareValue D A)) ∧
      1 - 1 / ((k : ℝ) + 1) ≤ (rareBitLaw D hD).probEvent (fun ω : Fin m → Bool =>
        ∀ r, pilot r (fun i => rareValue D A (ω i)) <
          (rareBitLaw D hD).variance (rareValue D A)) := by
  let envelope := fun xs => Finset.univ.sup' Finset.univ_nonempty (fun r : R => pilot r xs)
  obtain ⟨D, A, hD, hB, hp⟩ := no_uniform_finite_sample_variance_upper m k envelope
  refine ⟨D, A, hD, ?_, ?_⟩
  · simpa only [envelope, Finset.sup'_lt_iff, Finset.mem_univ, forall_const] using hB
  · simpa only [pilotFailure, envelope, Finset.sup'_lt_iff, Finset.mem_univ, forall_const]
      using hp

/-- For `D ≥ 2`, the two rare-event sampling weights sum to `D`. -/
theorem rareWeights_total (D : ℕ) (hD : 2 ≤ D) : weightTotal (rareWeights D) = D := by
  rw [weightTotal, Fin.sum_univ_two]
  change D - 1 + 1 = D
  omega

/-- When `D ≤ 2^b`, the bounded weighted sampler returns the rare outcome with mass `1 / D`
times one minus the `fuel`th power of the rejection mass. -/
theorem rareSampler_return (D b fuel : ℕ) (hD : 2 ≤ D) (hb : D ≤ 2 ^ b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler (rareWeights D) b fuel).law
      (fun z => rejectionOutcome z.1.1 = .inl 1) =
      1 / (D : ℝ≥0∞) * (1 - rationalRejectMass (rareWeights D) b ^ fuel) := by
  rw [weightedSampler_return _ _ _ (by rw [rareWeights_total D hD]; omega)
    (by rw [rareWeights_total D hD]; exact hb) 1, rareWeights_total D hD]
  norm_num [rareWeights, Fin.ext_iff]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
