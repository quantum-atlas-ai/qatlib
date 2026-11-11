/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringAlgorithmStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessingShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringRepetitionConsumerShor

/-!
# Factoring success after preprocessing

Proves `factoringAlgorithm` by combining preprocessing with independent factoring attempts. The
result gives a repeated-attempt success bound and soundness of factors returned by preprocessing
or an attempt, within the finite probability model associated with [Shor1997].

## Main statements

* `attemptBound_le_one`: Bounds the single-attempt lower-bound expression by one.
* `factoringAlgorithm`: Establishes the complete factoring success and soundness contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

/-- For `N ≥ 3` and enough sampler bits to encode every unit, the single-attempt bound
`shorAttemptBound N k` is at most one. -/
private theorem attemptBound_le_one (N k : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hk : Fintype.card (ZMod N)ˣ ≤ 2 ^ k) : shorAttemptBound N k ≤ 1 := by
  have hs : 1 ≤ N.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
  have hz : (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hzn : 0 ≤ (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) := by positivity
  have ha : (Fintype.card (ZMod N)ˣ : ℝ) / 2 ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hk
  have han : 0 ≤ (Fintype.card (ZMod N)ˣ : ℝ) / 2 ^ k := by positivity
  have hpn : 0 < Real.pi ^ 2 := by positivity
  have hrn : 0 ≤ (8 : ℝ) / Real.pi ^ 2 := by positivity
  have hr : (8 : ℝ) / Real.pi ^ 2 ≤ 2 := by
    rw [div_le_iff₀ hpn]
    nlinarith [Real.pi_gt_three]
  have hC : ((8 / Real.pi ^ 2 : ℝ) ^ 2 / 4) ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  unfold shorAttemptBound
  calc
    (Fintype.card (ZMod N)ˣ : ℝ) / 2 ^ k *
        (1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ))) *
        ((8 / Real.pi ^ 2) ^ 2 / 4) ≤ 1 * 1 * 1 := by
      gcongr; linarith
    _ = 1 := by ring

/-- Establishes preprocessing soundness, the repeated-attempt factoring success bound, and
soundness of individual factor outputs in the probability model associated with [Shor1997]. -/
theorem factoringAlgorithm : FactoringAlgorithm := by
  intro N R k M _ hM hk hN hcomposite hsize
  refine ⟨fun d h => factoringPreprocessing.1 N d hN h, ?_, attemptFactor_sound N M⟩
  unfold shorProgramSuccessProb
  cases hpre : shorPreprocess N with
  | factor d =>
    have hc := attemptBound_le_one N k hN hk
    have hn : 0 ≤ (1 - shorAttemptBound N k) ^ R :=
      pow_nonneg (by linarith) R
    linarith
  | residue =>
    have hcert := factoringPreprocessing.2 N hN hpre
    have hs := hcert.2.resolve_left hcomposite
    exact (factoringRepetitionConsumer N M k R hM hk hN hcert.1 hs hsize).1

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
