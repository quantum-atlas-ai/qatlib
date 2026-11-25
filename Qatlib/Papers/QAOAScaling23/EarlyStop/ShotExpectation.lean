/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Qatlib.Papers.AdiabaticQLS23.MainResults.FilterCost
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section

/-!
# Expected number of independent shots

The sampling TTS in arXiv:2308.02342v2 is the mean waiting time for an
optimal basis outcome. Count the successful shot in addition to the
failures. The event of needing more than `m` shots is the event of at
least `m` failures.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open Qatlib.Papers.AdiabaticQLS23.MainResults (expectedAttempts expectedAttempts_eq retryMass)
open Qatlib.Foundations.PureStateMath
open scoped ENNReal

namespace Qatlib.Papers.QAOAScaling23.EarlyStop

/-- A finite PMF assigns the success set a probability in the unit interval. -/
def shotSuccessProbability {I : Type*} (p : PMF I) (S : Finset I) : unitInterval :=
  ⟨∑ x ∈ S, (p x).toReal, by
    constructor
    · exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    · have hs : (∑ x ∈ S, p x) ≤ 1 := by
        rw [← p.toOuterMeasure_apply_finset S]
        calc
          _ ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ _)
          _ = 1 := (p.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)
      rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x)]
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hs⟩

/-- The computational-basis outcomes of a normalized state form its finite Born PMF. -/
def bornShot {I : Type*} [Fintype I] (ψ : QState I) (hψ : Normalized ψ) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (BornProb ψ i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg ψ i),
      bornProb_sum_eq_one hψ, ENNReal.ofReal_one])

/-- The probability of the success event in a Born shot is its total Born weight. -/
theorem bornShot_success_eq {I : Type*} [Fintype I]
    (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) :
    (shotSuccessProbability (bornShot ψ hψ) S : ℝ) = MeasureProb ψ S := by
  simp only [shotSuccessProbability, bornShot, PMF.ofFintype_apply, MeasureProb,
    ENNReal.toReal_ofReal (bornProb_nonneg _ _)]

/-- The expectation for positive success mass counts the last successful shot. -/
theorem directShot_geometric_mean (q : unitInterval) (hq : 0 < (q : ℝ)) :
    (∫ k : ℕ, (k + 1 : ℝ) ∂geometricMeasure q) = 1 / (q : ℝ) := by
  have hn : q ≠ 0 := by
    intro hz
    have hv := congrArg Subtype.val hz
    exact hq.ne' hv
  calc
    (∫ k : ℕ, (k + 1 : ℝ) ∂geometricMeasure q) = expectedAttempts (1 - (q : ℝ)) := by
      rw [integral_geometricMeasure hn, expectedAttempts]
      apply tsum_congr
      intro k
      simp only [retryMass, smul_eq_mul]
      ring
    _ = 1 / (q : ℝ) := by
      simpa using expectedAttempts_eq (r := 1 - (q : ℝ))
        (sub_nonneg.mpr q.2.2) (by linarith)

/-- The probability of needing more than `m` shots is the probability of at least `m`
failures in the geometric law. -/
theorem directShot_tail (q : unitInterval) (hq : 0 < (q : ℝ)) (m : ℕ) :
    (geometricMeasure q).real (Set.Ici m) = (1 - (q : ℝ)) ^ m := by
  have hn : q ≠ 0 := by
    intro hz
    have hv := congrArg Subtype.val hz
    exact hq.ne' hv
  let e : ℕ ≃ Set.Ici m :=
    { toFun := fun n => ⟨n + m, by show m ≤ n + m; omega⟩
      invFun := fun n => n.val - m
      left_inv := fun n => by simp
      right_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.prop) }
  calc
    (geometricMeasure q).real (Set.Ici m) =
        ∫ n : ℕ, (Set.Ici m).indicator (1 : ℕ → ℝ) n ∂geometricMeasure q :=
      (integral_indicator_one (measurableSet_Ici : MeasurableSet (Set.Ici m))).symm
    _ = ∑' n : Set.Ici m, (1 - (q : ℝ)) ^ n.val * (q : ℝ) := by
      rw [integral_geometricMeasure hn, tsum_subtype (Set.Ici m) (fun n : ℕ => (1 - (q : ℝ)) ^ n * (q : ℝ))]
      apply tsum_congr
      intro n
      by_cases hm : n ∈ Set.Ici m
      · simp [Set.indicator_of_mem hm, smul_eq_mul]
      · simp [Set.indicator_of_notMem hm]
    _ = ∑' n : ℕ, (1 - (q : ℝ)) ^ (n + m) * (q : ℝ) :=
      (e.tsum_eq (fun n : Set.Ici m => (1 - (q : ℝ)) ^ n.val * (q : ℝ))).symm
    _ = (1 - (q : ℝ)) ^ m := by
      have hs := (hasSum_one_geometricMeasure hn).mul_right ((1 - (q : ℝ)) ^ m)
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hs.tsum_eq

/-- For any finite outcome PMF, the direct first-hit mean and strict tail use the same event mass. -/
theorem directShot_mean {I : Type*} (p : PMF I) (S : Finset I)
    (hp : 0 < ∑ x ∈ S, (p x).toReal) (m : ℕ) :
    let law := geometricMeasure (shotSuccessProbability p S)
    (∫ k : ℕ, (k + 1 : ℝ) ∂law) = 1 / (∑ x ∈ S, (p x).toReal) ∧
      law.real (Set.Ici m) = (1 - ∑ x ∈ S, (p x).toReal) ^ m := by
  exact ⟨directShot_geometric_mean (shotSuccessProbability p S) hp,
    directShot_tail (shotSuccessProbability p S) hp m⟩

/-- The paper's sampling TTS is exactly the reciprocal total mass of its optimal basis states. -/
theorem bornShot_tts {I : Type*} [Fintype I] (ψ : QState I)
    (hψ : Normalized ψ) (S : Finset I) (hp : 0 < MeasureProb ψ S) (m : ℕ) :
    let law := geometricMeasure (shotSuccessProbability (bornShot ψ hψ) S)
    (∫ k : ℕ, (k + 1 : ℝ) ∂law) = 1 / MeasureProb ψ S ∧
      law.real (Set.Ici m) = (1 - MeasureProb ψ S) ^ m := by
  have he := bornShot_success_eq ψ hψ S
  have hq : 0 < (shotSuccessProbability (bornShot ψ hψ) S : ℝ) := by rw [he]; exact hp
  dsimp only
  exact ⟨(directShot_geometric_mean _ hq).trans (by rw [he]),
    (directShot_tail _ hq m).trans (by rw [he])⟩

end Qatlib.Papers.QAOAScaling23.EarlyStop
