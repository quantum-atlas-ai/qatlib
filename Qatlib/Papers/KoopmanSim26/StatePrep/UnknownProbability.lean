/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.StatePrep.LowerBoundSchedule
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Mathlib.Tactic

/-!
# State preparation with unknown success probability

The costed laws `attempt`, `stage`, and `stages` implement randomized amplitude amplification
with dyadically increasing windows and stopping on success. For positive initial success
probability, potential bounds control the expected query cost uniformly in the finite execution
budget, while the failure probability tends to zero. The density identities show that successful
outputs remain proportional to the desired postselected pure state. See [ZhangEtAl2026] for the
paper context.

## Main statements

* `unknown_probability_program`: For positive success probability `p ≤ 1`, the dyadic program
  has expected cost at most `496 / sqrt p` for every finite budget and real failure probability
  tending to zero.
* `unknown_balanced_source`: If at least an `η` fraction of target entries have norm at least `c
  * G`, the stated positivity and boundedness hypotheses give uniform expected cost at most `496
  / (c * sqrt η)` and real failure probability tending to zero.
* `unknown_stopped_density`: For a nonzero target, every finite stopped stage density equals its
  total success probability times the outer product of the postselected state.

## References

* [Zhang et al., 2026][ZhangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Papers.KoopmanSim26.StatePrep.Observables
open Qatlib.Papers.KoopmanSim26.StatePrep.LowerSchedule
open scoped Classical ENNReal
set_option warningAsError false
namespace Qatlib.Papers.KoopmanSim26.StatePrep.UnknownSchedule

/-- The extended nonnegative real number `1 / 8` is the image of its real counterpart under
`ENNReal.ofReal`. -/
theorem rat18 : (1/8:ℝ≥0∞) = ENNReal.ofReal (1/8:ℝ) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8)]
  norm_num

/-- The extended nonnegative real number `7 / 8` is the image of its real counterpart under
`ENNReal.ofReal`. -/
theorem rat78 : (7/8:ℝ≥0∞) = ENNReal.ofReal (7/8:ℝ) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8)]
  norm_num

/-- The extended nonnegative real number `3 / 8` is the image of its real counterpart under
`ENNReal.ofReal`. -/
theorem rat38 : (3/8:ℝ≥0∞) = ENNReal.ofReal (3/8:ℝ) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8)]
  norm_num

/-- For a nonnegative real function on a finite distribution, its extended nonnegative
expectation equals `ENNReal.ofReal` of its real expectation. -/
theorem finite_expect_nn {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    expectation (toPMF p) (fun x => ENNReal.ofReal (f x)) = ENNReal.ofReal (p.expect f) := by
  simp only [expectation, toPMF, PMF.ofFintype_apply, tsum_fintype, FinDist.expect]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))]
  apply Finset.sum_congr rfl
  intro x _
  exact (ENNReal.ofReal_mul (p.nonneg x)).symm

/-- The costed Boolean law of one randomized amplification attempt, recording membership in the
good set and the number of preparation queries. -/
noncomputable def attempt {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) : CostedLaw Bool :=
  (jointPMF A hA j S M hM).map (fun x =>
    (decide (x.2 ∈ S), preparedInputQueries (preparedAAWord j (chosenRound x.1))))

/-- The probability that a costed Boolean law returns `false`. -/
noncomputable def failure (p : CostedLaw Bool) : ℝ≥0∞ := event p (fun x => x.1=false)

/-- The probability that an amplification attempt returns `true` equals the real success
probability embedded in the extended nonnegative reals. -/
theorem attempt_success {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) :
    event (attempt A hA j S M hM) (fun x => x.1=true) = ENNReal.ofReal (success A j S M) := by
  simp only [event, attempt, expectation_map, jointPMF]
  rw [← success_is_actual A hA j S M hM]
  rw [← finite_expect_nn (jointLaw A hA j S M hM) (fun x => if x.2 ∈ S then 1 else 0)
    (fun _ => by (try dsimp only); split_ifs <;> norm_num)]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro x
  by_cases h : x.2 ∈ S <;> simp [h]

/-- An amplification attempt with positive window size `M` uses at most `2 * M + 1` queries. -/
theorem attempt_bounded {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) : BoundedBy (attempt A hA j S M hM) (2*M+1) := by
  intro y hy
  obtain ⟨x,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  exact selected_count_le A hA j S x.1

/-- Failure and success probabilities of a costed Boolean law sum to one. -/
theorem flag_partition (p : CostedLaw Bool) : failure p + event p (fun x => x.1=true) = 1 := by
  rw [failure, event, event, ← expectation_add]
  calc
    _ = expectation p (fun _ => 1) := by
      congr 1
      funext x
      cases x.1 <;> simp
    _ = 1 := expectation_const _ _

/-- The failure probability of a costed Boolean law is at most one. -/
theorem failure_le_one (p : CostedLaw Bool) : failure p ≤ 1 :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one p _

/-- For positive success probability at most one, a window satisfying `1 ≤ M * sqrt p` gives
failure probability at most `7 / 8`. -/
theorem attempt_failure_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hmature : 1 ≤ (M:ℝ)*Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    failure (attempt A hA j S M hM) ≤ (7/8:ℝ≥0∞) := by
  have hs := ENNReal.ofReal_le_ofReal (mature_window_success A hA j S M hM hp0 hp1 hmature)
  rw [← attempt_success A hA j S M hM] at hs
  apply ENNReal.le_of_add_le_add_right (a := (1/8:ℝ≥0∞)) (by norm_num)
  calc
    _ ≤ failure (attempt A hA j S M hM) + event (attempt A hA j S M hM) (fun x => x.1=true) := by
      gcongr
      simpa using! hs
    _ = 1 := flag_partition _
    _ = (7/8:ℝ≥0∞)+(1/8:ℝ≥0∞) := by
      rw [rat78, rat18, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

/-- Run the first costed Boolean law and return immediately on success, running the second law
only on failure. -/
noncomputable def stopThen (p q : CostedLaw Bool) : CostedLaw Bool :=
  CostedLaw.bind p (fun good => if good then ret true else q)

/-- Adding a fixed cost to a law preserves its failure probability. -/
theorem failure_charge (p : CostedLaw Bool) (n : ℕ) : failure (charge n p) = failure p := by
  simp only [failure, event, charge, expectation_map]

/-- A deterministic Boolean return fails with probability one exactly when its value is `false`. -/
theorem failure_ret (b : Bool) : failure (ret b) = if b=false then 1 else 0 := by
  simp [failure, event, ret]

/-- The expectation of a constant charged only on failure equals that constant times the failure
probability. -/
theorem indicator_expect (p : PMF (Bool × ℕ)) (c : ℝ≥0∞) :
    expectation p (fun x => if x.1=false then c else 0) = c * failure p := by
  rw [failure, event,
      ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro x
  split_ifs <;> simp

/-- The failure probability of two attempts composed with stopping on success is the product of
their failure probabilities. -/
theorem failure_stopThen (p q : CostedLaw Bool) : failure (stopThen p q) = failure p * failure q := by
  calc
    _ = expectation p (fun x => failure (charge x.2 (if x.1 then ret true else q))) := by
      unfold failure stopThen CostedLaw.bind event
      exact expectation_bind p _ _
    _ = expectation p (fun x => if x.1=false then failure q else 0) := by
      apply congrArg (expectation p)
      funext x
      rw [failure_charge]
      cases x.1 <;> simp [failure_ret]
    _ = failure q * failure p := indicator_expect p (failure q)
    _ = _ := mul_comm _ _

/-- The expected cost of `stopThen p q` is the cost of `p` plus its failure probability times
the expected cost of `q`. -/
theorem cost_stopThen (p q : CostedLaw Bool) :
    expectedCost (stopThen p q) = expectedCost p + failure p * expectedCost q := by
  rw [stopThen, expectedCost_bind]
  have h (x : Bool × ℕ) : expectedCost (if x.1 then ret true else q) =
      if x.1=false then expectedCost q else 0 := by
    cases x.1 <;> simp
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr h, indicator_expect,
      mul_comm]

/-- Repeat a costed Boolean law at most the specified number of times, stopping at the first
success. -/
noncomputable def repeatAttempts (p : CostedLaw Bool) : ℕ → CostedLaw Bool
  | 0 => ret false
  | n+1 => stopThen p (repeatAttempts p n)

/-- Repeating a law at most `n` times gives failure probability equal to its single-attempt
failure probability raised to `n`. -/
theorem repeat_failure (p : CostedLaw Bool) (n : ℕ) : failure (repeatAttempts p n) = (failure p)^n := by
  induction n with
  | zero => simp [repeatAttempts, failure_ret]
  | succ n ih => rw [repeatAttempts, failure_stopThen, ih, pow_succ]; ring

/-- If one attempt has cost at most `B`, then at most `n` attempts have cost at most `n * B`. -/
theorem repeat_bounded (p : CostedLaw Bool) (B n : ℕ) (hp : BoundedBy p B) :
    BoundedBy (repeatAttempts p n) (n*B) := by
  induction n with
  | zero => simp [repeatAttempts]
  | succ n ih =>
    have hf : ∀ good : Bool, BoundedBy (if good then ret true else repeatAttempts p n) (n*B) := by
      intro good
      cases good
      · exact ih
      · exact boundedBy_ret true _
    have h : BoundedBy (stopThen p (repeatAttempts p n)) (B+n*B) := hp.bind hf
    simpa [repeatAttempts, Nat.succ_mul, Nat.add_comm] using! h

/-- A stage consisting of at most eight amplification attempts with window size `2 ^ h`,
stopping on success. -/
noncomputable def stage {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) (h : ℕ) : CostedLaw Bool :=
  repeatAttempts (attempt A hA j S (2^h) (by positivity)) 8

/-- The cost of stage `h` is bounded by `24 * 2 ^ h`. -/
theorem stage_bounded {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) (h : ℕ) :
    BoundedBy (stage A hA j S h) (24*2^h) := by
  have hb := repeat_bounded (attempt A hA j S (2^h) (by positivity)) (2*2^h+1) 8
    (attempt_bounded A hA j S (2^h) (by positivity))
  intro x hx
  have hl := hb x hx
  have hp : 1 ≤ 2^h := Nat.one_le_pow h 2 (by omega)
  omega

/-- A stage whose dyadic window satisfies `1 ≤ 2 ^ h * sqrt p` has failure probability at most
`3 / 8`, for positive `p ≤ 1`. -/
theorem stage_failure_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) (h : ℕ)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hmature : 1 ≤ (2:ℝ)^h * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    failure (stage A hA j S h) ≤ (3/8:ℝ≥0∞) := by
  rw [stage, repeat_failure]
  have ha := attempt_failure_le A hA j S (2^h) (by positivity) hp0 hp1 (by exact_mod_cast hmature)
  calc
    _ ≤ (7/8:ℝ≥0∞)^8 := pow_le_pow_left' ha _
    _ ≤ (3/8:ℝ≥0∞) := by
      rw [rat78, rat38, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤7/8)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Run a finite sequence of stages starting at the given offset, increasing the dyadic exponent
after each failure. -/
noncomputable def stages {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) :
    ℕ → ℕ → CostedLaw Bool
  | _off, 0 => ret false
  | off, fuel+1 => stopThen (stage A hA j S off) (stages A hA j S (off+1) fuel)

/-- The piecewise real potential `124 * 2 ^ h0 - 24 * 2 ^ off` before the threshold and `100 * 2
^ off` at or after it. -/
noncomputable def potential (h0 off : ℕ) : ℝ :=
  if off<h0 then 124*(2:ℝ)^h0-24*(2:ℝ)^off else 100*(2:ℝ)^off

/-- The stage-cost potential is nonnegative at every threshold and offset. -/
theorem potential_nonneg (h0 off : ℕ) : 0 ≤ potential h0 off := by
  unfold potential
  split_ifs with h
  · have hm : (2:ℝ)^off ≤ (2:ℝ)^h0 := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt h)
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) h0]
  · positivity

/-- Before the threshold, the current potential covers `24 * 2 ^ off` plus the next potential. -/
theorem potential_before (h0 off : ℕ) (h : off<h0) :
    24*(2:ℝ)^off + potential h0 (off+1) ≤ potential h0 off := by
  unfold potential
  rw [if_pos h]
  by_cases hn : off+1<h0
  · rw [if_pos hn]
    simp only [pow_succ]
    linarith
  · rw [if_neg hn]
    have he : off+1=h0 := by omega
    rw [← he]
    simp only [pow_succ]
    linarith

/-- At or after the threshold, the current potential covers `24 * 2 ^ off` plus `3 / 8` of the
next potential. -/
theorem potential_after (h0 off : ℕ) (h : h0≤off) :
    24*(2:ℝ)^off + (3/8)*potential h0 (off+1) ≤ potential h0 off := by
  have hn : ¬off+1<h0 := by omega
  have ho : ¬off<h0 := by omega
  simp only [potential, if_neg hn, if_neg ho, pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) off]

/-- Once a dyadic window satisfies the maturity inequality, every larger exponent satisfies it
as well. -/
theorem mature_later {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (h0 off : ℕ) (h : h0≤off)
    (hm : 1 ≤ (2:ℝ)^h0 * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    1 ≤ (2:ℝ)^off * Real.sqrt (MeasureProb (preparedAAState A j) S) :=
  hm.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (Real.sqrt_nonneg _))

/-- If the threshold window satisfies `1 ≤ 2 ^ h0 * sqrt p` with positive `p ≤ 1`, the expected
cost of any finite stage sequence is bounded by the potential at its starting offset. -/
theorem stages_cost_potential {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) (h0 : ℕ)
    (hm : 1 ≤ (2:ℝ)^h0 * Real.sqrt (MeasureProb (preparedAAState A j) S)) (fuel off : ℕ) :
    expectedCost (stages A hA j S off fuel) ≤ ENNReal.ofReal (potential h0 off) := by
  induction fuel generalizing off with
  | zero => simp [stages]
  | succ fuel ih =>
    rw [stages, cost_stopThen]
    have hc : expectedCost (stage A hA j S off) ≤ ENNReal.ofReal (24*(2:ℝ)^off) := by
      simpa using! (stage_bounded A hA j S off).expectedCost_le
    have ht := ih (off+1)
    have hn := potential_nonneg h0 (off+1)
    by_cases ho : off<h0
    · calc
        _ ≤ ENNReal.ofReal (24*(2:ℝ)^off) + 1*ENNReal.ofReal (potential h0 (off+1)) :=
          add_le_add hc (mul_le_mul' (failure_le_one _) ht)
        _ = ENNReal.ofReal (24*(2:ℝ)^off + potential h0 (off+1)) := by
          rw [one_mul, ENNReal.ofReal_add (by positivity) hn]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (potential_before h0 off ho)
    · have hq := stage_failure_le A hA j S off hp0 hp1 (mature_later A j S h0 off (by omega) hm)
      calc
        _ ≤ ENNReal.ofReal (24*(2:ℝ)^off) + (3/8:ℝ≥0∞)*ENNReal.ofReal (potential h0 (off+1)) :=
          add_le_add hc (mul_le_mul' hq ht)
        _ = ENNReal.ofReal (24*(2:ℝ)^off + (3/8)*potential h0 (off+1)) := by
          rw [rat38, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3/8),
            ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) hn)]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (potential_after h0 off (by omega))

/-- Under the maturity condition at `h0` and positive `p ≤ 1`, every finite stage sequence
starting at zero has expected cost at most `124 * 2 ^ h0`. -/
theorem stages_cost_uniform {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) (h0 : ℕ)
    (hm : 1 ≤ (2:ℝ)^h0 * Real.sqrt (MeasureProb (preparedAAState A j) S)) (fuel : ℕ) :
    expectedCost (stages A hA j S 0 fuel) ≤ ENNReal.ofReal (124*(2:ℝ)^h0) := by
  refine (stages_cost_potential A hA j S hp0 hp1 h0 hm fuel 0).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold potential
  split_ifs with h
  · norm_num
  · have he : h0=0 := by omega
    norm_num [he]

/-- Composition of costed Boolean laws with stopping on success is associative. -/
theorem stopThen_assoc (p q r : CostedLaw Bool) : stopThen (stopThen p q) r = stopThen p (stopThen q r) := by
  simp only [stopThen, CostedLaw.bind_assoc]
  congr 1
  funext b
  cases b <;> simp

/-- Splitting a stage sequence into two consecutive parts is equivalent to composing those parts
with stopping on success. -/
theorem stages_concat {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (off a b : ℕ) :
    stages A hA j S off (a+b) = stopThen (stages A hA j S off a) (stages A hA j S (off+a) b) := by
  induction a generalizing off with
  | zero => simp [stages, stopThen]
  | succ a ih =>
    rw [Nat.succ_add, stages, ih, ← stopThen_assoc, stages]
    congr 2
    omega

/-- For positive `p ≤ 1`, a sequence starting at or beyond a mature threshold has failure
probability at most `(3 / 8) ^ fuel`. -/
theorem stages_failure_mature {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) (h0 : ℕ)
    (hm : 1 ≤ (2:ℝ)^h0 * Real.sqrt (MeasureProb (preparedAAState A j) S)) (fuel off : ℕ)
    (hoff : h0≤off) : failure (stages A hA j S off fuel) ≤ (3/8:ℝ≥0∞)^fuel := by
  induction fuel generalizing off with
  | zero => simp [stages, failure_ret]
  | succ fuel ih =>
    rw [stages, failure_stopThen, pow_succ]
    have hq := stage_failure_le A hA j S off hp0 hp1 (mature_later A j S h0 off hoff hm)
    have ht := ih (off+1) (by omega)
    calc
      _ ≤ (3/8:ℝ≥0∞) * (3/8:ℝ≥0∞)^fuel := mul_le_mul' hq ht
      _ = _ := mul_comm _ _

/-- For positive `p ≤ 1` and mature threshold `h0`, running `h0 + fuel` stages from zero gives
failure probability at most `(3 / 8) ^ fuel`. -/
theorem stages_failure_after {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) (h0 : ℕ)
    (hm : 1 ≤ (2:ℝ)^h0 * Real.sqrt (MeasureProb (preparedAAState A j) S)) (fuel : ℕ) :
    failure (stages A hA j S 0 (h0+fuel)) ≤ (3/8:ℝ≥0∞)^fuel := by
  rw [stages_concat, failure_stopThen, Nat.zero_add]
  calc
    _ ≤ 1 * failure (stages A hA j S h0 fuel) :=
      mul_le_mul_left (failure_le_one _) _
    _ ≤ (3/8:ℝ≥0∞)^fuel := by
      rw [one_mul]
      exact stages_failure_mature A hA j S hp0 hp1 h0 hm fuel h0 le_rfl

/-- For positive success probability at most one and a mature threshold, the real failure
probabilities tend to zero as the stage budget tends to infinity. -/
theorem stages_failure_tendsto_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) (h0 : ℕ)
    (hm : 1 ≤ (2:ℝ)^h0 * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    Filter.Tendsto (fun fuel => (failure (stages A hA j S 0 fuel)).toReal) Filter.atTop (nhds 0) := by
  apply (Filter.tendsto_add_atTop_iff_nat h0).mp
  have hu (fuel : ℕ) : (failure (stages A hA j S 0 (fuel+h0))).toReal ≤ (3/8:ℝ)^fuel := by
    have hh := stages_failure_after A hA j S hp0 hp1 h0 hm fuel
    rw [Nat.add_comm h0 fuel] at hh
    have he : (3/8:ℝ≥0∞)^fuel = ENNReal.ofReal ((3/8:ℝ)^fuel) := by
      rw [rat38, ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤3/8)]
    rw [he] at hh
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [ENNReal.toReal_ofReal (pow_nonneg (by norm_num : (0:ℝ)≤3/8) fuel)] using! ht
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hu
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤3/8) (by norm_num : (3/8:ℝ)<1))

/-- For positive `M`, the dyadic power selected by `Nat.clog 2 M` is at most `2 * M`. -/
theorem pow_clog_le_twice (M : ℕ) (hM : 0 < M) : 2^(Nat.clog 2 M) ≤ 2*M := by
  by_cases h : M≤1
  · have he : M=1 := by omega
    simp [he]
  · have hgt : 1<M := by omega
    have hc : 0<Nat.clog 2 M := Nat.clog_pos (by omega) hgt
    have hl := Nat.pow_pred_clog_lt_self (by omega : 1<2) hgt
    calc
      2^Nat.clog 2 M = 2^(Nat.clog 2 M-1+1) := by congr 1; omega
      _ = 2 * 2^(Nat.clog 2 M-1) := by rw [pow_succ]; omega
      _ ≤ 2*M := Nat.mul_le_mul_left 2 hl.le

/-- For `0 < p ≤ 1`, there is a dyadic exponent satisfying the maturity inequality and `2 ^ h0 ≤
4 / sqrt p`. -/
theorem threshold_exists (p : ℝ) (hp0 : 0<p) (hp1 : p≤1) :
    ∃ h0 : ℕ, 1 ≤ (2:ℝ)^h0 * Real.sqrt p ∧ (2:ℝ)^h0 ≤ 4/Real.sqrt p := by
  let M := window p
  let h0 := Nat.clog 2 M
  have hw := window_bounds p hp0 hp1
  have hM : 0<M := window_pos p
  have hlo : (M:ℝ) ≤ (2:ℝ)^h0 := by exact_mod_cast Nat.le_pow_clog (by omega : 1<2) M
  have hhi : (2:ℝ)^h0 ≤ 2*(M:ℝ) := by exact_mod_cast pow_clog_le_twice M hM
  refine ⟨h0, hw.1.trans (mul_le_mul_of_nonneg_right hlo (Real.sqrt_nonneg p)), ?_⟩
  have hr : 4/Real.sqrt p = 2*(2/Real.sqrt p) := by ring
  linarith

/-- For positive success probability `p ≤ 1`, the dyadic program has expected cost at most `496
/ sqrt p` for every finite budget and real failure probability tending to zero. -/
theorem unknown_probability_program {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    (∀ fuel, expectedCost (stages A hA j S 0 fuel) ≤
      ENNReal.ofReal (496/Real.sqrt (MeasureProb (preparedAAState A j) S))) ∧
    Filter.Tendsto (fun fuel => (failure (stages A hA j S 0 fuel)).toReal) Filter.atTop (nhds 0) := by
  obtain ⟨h0,hm,hb⟩ := threshold_exists _ hp0 hp1
  constructor
  · intro fuel
    refine (stages_cost_uniform A hA j S hp0 hp1 h0 hm fuel).trans (ENNReal.ofReal_le_ofReal ?_)
    have hr : 496/Real.sqrt (MeasureProb (preparedAAState A j) S) =
        124*(4/Real.sqrt (MeasureProb (preparedAAState A j) S)) := by ring
    linarith
  · exact stages_failure_tendsto_zero A hA j S hp0 hp1 h0 hm

/-- A run of `h` fair bits chooses uniformly among `2 ^ h` outcomes with zero rejection
probability, cost bounded by `h`, and expected cost exactly `h`. -/
theorem dyadic_fair_choice (h : ℕ) :
    event (finiteCoinRun h (2^h) 1) (fun x => x.1=Sum.inr ()) = 0 ∧
    (∀ i : Fin (2^h), event (finiteCoinRun h (2^h) 1) (fun x => x.1=Sum.inl i) =
      1/((2^h:ℕ):ℝ≥0∞)) ∧
    BoundedBy (finiteCoinRun h (2^h) 1) h ∧
    expectedCost (finiteCoinRun h (2^h) 1) = (h:ℝ≥0∞) := by
  have hr := finite_coin_return_and_pending h (2^h) 1 (by positivity) le_rfl
  have hc := finite_coin_actual_bit_cost h (2^h) 1 le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [coinRejectMass] using! hr.1
  · intro i
    simpa [coinRejectMass] using! hr.2 i
  · simpa using! hc.1
  · simpa [coinRejectMass] using! hc.2

/-- For a nonzero target and values bounded by positive `G`, every finite stage budget has
expected cost at most `496 * sqrt (2 ^ n) * G / sqrt (targetNormSq b value)`, and real
failure probability tends to zero. -/
theorem unknown_observables_source {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) :
    let A := preparation b value G
    let hA := preparation_unitary b value G hG hvalue
    (∀ fuel, expectedCost (stages A hA (seed n m) (goodSet n m) 0 fuel) ≤
      ENNReal.ofReal (496*(Real.sqrt ((2:ℝ)^n)*G/Real.sqrt (targetNormSq b value)))) ∧
    Filter.Tendsto (fun fuel => (failure (stages A hA (seed n m) (goodSet n m) 0 fuel)).toReal)
      Filter.atTop (nhds 0) := by
  have hp0 : 0 < MeasureProb (preparedAAState (preparation b value G) (seed n m)) (goodSet n m) := by
    change 0 < MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m)
    rw [actual_success_probability b value G hG]
    exact div_pos (targetNormSq_pos b value hu) (by positivity)
  have hh := unknown_probability_program (preparation b value G) (preparation_unitary b value G hG hvalue)
    (seed n m) (goodSet n m) hp0 (actual_probability_le_one b value G hG hvalue)
  refine ⟨?_, hh.2⟩
  intro fuel
  refine (hh.1 fuel).trans (le_of_eq (congrArg ENNReal.ofReal ?_))
  have hr := actual_overhead b value G hG
  change 1/Real.sqrt
      (MeasureProb (preparedAAState (preparation b value G) (seed n m)) (goodSet n m)) = _ at hr
  calc
    _ = 496*(1/Real.sqrt (MeasureProb (preparedAAState (preparation b value G) (seed n m)) (goodSet n m))) := by ring
    _ = _ := by rw [hr]

/-- If at least an `η` fraction of target entries have norm at least `c * G`, the stated
positivity and boundedness hypotheses give uniform expected cost at most `496 / (c * sqrt
η)` and real failure probability tending to zero. -/
theorem unknown_balanced_source {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G c η : ℝ) (hG : 0 < G) (hc : 0 < c) (hη : 0 < η)
    (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) (S : Finset (Reg n))
    (hcard : η * (2:ℝ)^n ≤ S.card)
    (hbig : ∀ j ∈ S, c * G ≤ ‖target b value j‖) :
    let A := preparation b value G
    let hA := preparation_unitary b value G hG hvalue
    (∀ fuel, expectedCost (stages A hA (seed n m) (goodSet n m) 0 fuel) ≤
      ENNReal.ofReal (496/(c*Real.sqrt η))) ∧
    Filter.Tendsto (fun fuel => (failure (stages A hA (seed n m) (goodSet n m) 0 fuel)).toReal)
      Filter.atTop (nhds 0) := by
  have hh := unknown_observables_source b value G hG hvalue hu
  refine ⟨?_, hh.2⟩
  intro fuel
  refine (hh.1 fuel).trans (ENNReal.ofReal_le_ofReal ?_)
  have hb := balanced_actual_overhead b value G c η hG hc hη S hcard hbig
  calc
    _ ≤ 496*(1/(c*Real.sqrt η)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- Accumulate a successful density over finitely many attempts, weighting each continuation by
the real failure probability. -/
noncomputable def repeatedDensity {I : Type} [Fintype I] [DecidableEq I]
    (p : CostedLaw Bool) (D : Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 0
  | n+1 => D + ((failure p).toReal : ℂ) • repeatedDensity p D n

/-- If the single-attempt density is its success probability times `ρ`, the repeated density is
the total repeated success probability times `ρ`. -/
theorem repeatedDensity_ray {I : Type} [Fintype I] [DecidableEq I]
    (p : CostedLaw Bool) (D ρ : Matrix I I ℂ)
    (hD : D = ((1-(failure p).toReal : ℝ) : ℂ) • ρ) (n : ℕ) :
    repeatedDensity p D n = ((1-(failure (repeatAttempts p n)).toReal : ℝ) : ℂ) • ρ := by
  induction n with
  | zero => simp [repeatedDensity, repeatAttempts, failure_ret]
  | succ n ih =>
    simp only [repeatedDensity, repeatAttempts, failure_stopThen, ENNReal.toReal_mul]
    rw [ih, hD, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- For a nonzero target, the successful density of one amplification attempt is its success
probability times the outer product of the postselected state. -/
theorem attempt_density_coeff {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0)
    (M : ℕ) (hM : 0 < M) :
    successfulDensity b value G M =
      ((1-(failure (attempt (preparation b value G) (preparation_unitary b value G hG hvalue)
        (seed n m) (goodSet n m) M hM)).toReal : ℝ) : ℂ) • outerProduct (postselected b value G) := by
  let A := preparation b value G
  let hA := preparation_unitary b value G hG hvalue
  let p := attempt A hA (seed n m) (goodSet n m) M hM
  have hpart := flag_partition p
  rw [attempt_success] at hpart
  have hq : failure p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (failure_le_one p)
  have hsn : 0 ≤ success A (seed n m) (goodSet n m) M :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (measureProb_nonneg _ _))
  have hreal := congrArg ENNReal.toReal hpart
  rw [ENNReal.toReal_add hq ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hsn,
      ENNReal.toReal_one] at hreal
  have he : success A (seed n m) (goodSet n m) M = 1-(failure p).toReal := by linarith
  rw [actual_successful_density b value G hG hvalue hu M, he]

/-- The successful output density accumulated over the eight stopped attempts of a dyadic stage. -/
noncomputable def stageDensity {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (h : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  repeatedDensity
    (attempt (preparation b value G) (preparation_unitary b value G hG hvalue)
      (seed n m) (goodSet n m) (2^h) (by positivity))
    (successfulDensity b value G (2^h)) 8

/-- For a nonzero target, a stage density equals its success probability times the outer product
of the postselected state. -/
theorem stageDensity_ray {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) (h : ℕ) :
    stageDensity b value G hG hvalue h =
      ((1-(failure (stage (preparation b value G) (preparation_unitary b value G hG hvalue)
        (seed n m) (goodSet n m) h)).toReal : ℝ) : ℂ) • outerProduct (postselected b value G) :=
  repeatedDensity_ray _ _ _ (attempt_density_coeff b value G hG hvalue hu (2^h) (by positivity)) 8

/-- The successful density accumulated over consecutive dyadic stages, with continuation
weighted by each stage's failure probability. -/
noncomputable def stoppedDensity {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) : ℕ → ℕ → Matrix (Reg n) (Reg n) ℂ
  | _off, 0 => 0
  | off, fuel+1 => stageDensity b value G hG hvalue off +
      ((failure (stage (preparation b value G) (preparation_unitary b value G hG hvalue)
        (seed n m) (goodSet n m) off)).toReal : ℂ) • stoppedDensity b value G hG hvalue (off+1) fuel

/-- For a nonzero target, every finite stopped stage density equals its total success
probability times the outer product of the postselected state. -/
theorem unknown_stopped_density {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0)
    (fuel off : ℕ) :
    stoppedDensity b value G hG hvalue off fuel =
      ((1-(failure (stages (preparation b value G) (preparation_unitary b value G hG hvalue)
        (seed n m) (goodSet n m) off fuel)).toReal : ℝ) : ℂ) • outerProduct (postselected b value G) := by
  induction fuel generalizing off with
  | zero => simp [stoppedDensity, stages, failure_ret]
  | succ fuel ih =>
    simp only [stoppedDensity, stages, failure_stopThen, ENNReal.toReal_mul]
    rw [stageDensity_ray b value G hG hvalue hu off, ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

end Qatlib.Papers.KoopmanSim26.StatePrep.UnknownSchedule
