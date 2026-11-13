/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodStat
import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanNearPeriodSampling

/-!
# Simon decoding as a near-period distinguisher

Proves `boundedErrorNearPeriodDistinguisher` by combining the counted Simon decoding pipeline
with the near-period Fourier sampling bound. For injective functions, the probability of an
output other than the zero string is at most `2 ^ (-k)` after `n + k` samples.

For a nonzero near period with at most `2 ^ n / (n + k)` violating inputs, the probability of
not returning the zero string is at least `(1 - 1 / (n + k)) ^ (n + k)`. This develops the
bounded-error extension of Simon's sampling method [Simon1997].

## Main statements

* `allDot_reject_zero`: rules out the zero-string output when samples are orthogonal to a
  nonzero vector.
* `boundedErrorNearPeriodDistinguisher`: establishes the distinguisher specification and its
  resource counts.

## References

* [Simon, 1997][Simon1997]
-/

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.HspRecovery.BackendAudit Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher
open scoped Classical ENNReal

/-- If every decoded sample is orthogonal to a nonzero Boolean vector `s`, the Simon secret
decoder does not return the zero string. -/
private lemma allDot_reject_zero {n m : ℕ}
    (s : BooleanVec n) (hs : s ≠ 0) (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hx : ∀ i, booleanDot s (booleanDecodedSamples xs i) = 0) :
    decodeSimonSecret (simonRecordBits xs) ≠ some (ZeroStr n) := by
  intro hd
  have hc := (boolean_gaussian_simon_decode_iff (simonRecordBits xs) (ZeroStr n)).mp hd
  rw [regBooleanEquiv_simonRecordBits, regBooleanEquiv_zeroStr, booleanSimonSubgroup_zero] at hc
  have hm : s ∈ booleanSampleCandidate (booleanDecodedSamples xs) := by
    apply (mem_booleanSampleCandidate _ _).mpr
    intro i
    rw [booleanDot_comm']
    exact hx i
  rw [hc] at hm
  exact hs (by simpa using hm)

/-- Establishes the counted Simon near-period distinguisher specification, including the
injective-case error bound and the near-period lower bound for not returning the zero string
[Simon1997]. -/
theorem boundedErrorNearPeriodDistinguisher : BoundedErrorNearPeriodDistinguisher := by
  intro n k R _ _ _ f
  refine ⟨(simon_actual_preparation_and_quantum_cost f (n + k)).2.2.2.2, ?_, ?_⟩
  · intro hf
    apply (simon_gaussian_accessible_budget f (ZeroStr n) k _).2
    rw [regBooleanEquiv_zeroStr]
    exact (booleanSimonPromise_zero_iff f).mpr hf
  · intro s hs hbudget
    have hn : 0 < n := by
      by_contra h
      have hz : n = 0 := by omega
      subst n
      exact hs (Subsingleton.elim _ _)
    have hm : 0 < n + k := by omega
    let q := Nat.card {x : BooleanVec n | f x ≠ f (x + s)}
    have hq : NearPeriodPromise f s q := le_rfl
    have hqn : q ≤ 2 ^ n := by
      calc
        q = q * 1 := (Nat.mul_one q).symm
        _ ≤ q * (n + k) := Nat.mul_le_mul_left q hm
        _ ≤ 2 ^ n := hbudget
    have hgood := hiddenSubgroupFreshSamples_allDot_ge_of_nearPeriod f s q hqn hq (n + k)
    have hmR : (0 : ℝ) < (n + k : ℕ) := by exact_mod_cast hm
    have hdiv : (q : ℝ) / 2 ^ n ≤ 1 / (n + k : ℕ) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n) hmR]
      norm_cast
      simpa only [one_mul, q] using hbudget
    have hbase : (0 : ℝ) ≤ 1 - 1 / (n + k : ℕ) := by
      have hm1 : (1 : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast hm
      have hd : (1 : ℝ) / (n + k : ℕ) ≤ 1 := (div_le_one hmR).mpr hm1
      linarith
    have hp : (1 - 1 / (n + k : ℕ) : ℝ) ^ (n + k) ≤
        (1 - (q : ℝ) / 2 ^ n) ^ (n + k) :=
      pow_le_pow_left₀ hbase (by linarith) (n + k)
    have hreject : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (simonDecodedRun f (n + k)).1
        (fun out => out ≠ some (ZeroStr n)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv (n + k))
        (fun xs => decodeSimonSecret (simonRecordBits xs) ≠ some (ZeroStr n)) := by
      unfold simonDecodedRun Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    have hmono : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv (n + k))
        (fun xs => ∀ i, booleanDot s (booleanDecodedSamples xs i) = 0) ≤
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (simonDecodedRun f (n + k)).1 (fun out => out ≠ some (ZeroStr n)) := by
      rw [hreject]
      unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      apply ENNReal.tsum_le_tsum
      intro xs
      by_cases hx : ∀ i, booleanDot s (booleanDecodedSamples xs i) = 0
      · have hr := allDot_reject_zero s hs xs hx
        simp only [booleanDecodedSamples] at hx
        simp [hx, hr]
      · simp only [booleanDecodedSamples] at hx
        simp [hx]
    simpa only [Nat.cast_add] using
      (ENNReal.ofReal_le_ofReal hp).trans (hgood.trans hmono)

end Qatlib.Concepts.HspRecovery.Distinguisher
