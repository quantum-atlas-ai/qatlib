/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionDefs
import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodSimo
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionAmplification
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionOracle

/-!
# Simon amplification and random-oracle bounds

Assembles two-sided error estimates and repeated-run cost ledgers for the near-period
distinguisher in [Simon1997]. It also bounds classical query-tree success in guessing the
sampled branch of `simonOracleConstruction`; that construction samples masks uniformly,
including the zero mask.

## Main statements

* `simonNegligibleErrorAmplification`: For `n + k ≥ 2`, amplification has error at most `r * (1
  / 2)^k` on injective functions and at most `(3 / 4)^r` under the stated nonzero near-period
  condition; the first two single-run ledger fields are `n + k` and `2 * (n + k)` [Simon1997].
* `simonClassicalRandomOracleBound`: For `n ≥ 1`, a randomized query tree bounded by the natural
  budget `2^(n / 4)` guesses the sampled oracle branch with mass at most `1 / 2 + 2^(-n / 2)`
  [Simon1997].
* `clause5_complete`: The combined two-sided amplification, exact ledger and marginal
  statements, and classical random-oracle branch-guessing bound hold as specified by
  `Clause5TwoSidedAmplification` [Simon1997].

## References

* [Simon, 1997][Simon1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
open Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.QPowerSimon97.Recovery
variable {n : ℕ}
noncomputable section

/-- For `n + k ≥ 2`, amplification has error at most `r * (1 / 2)^k` on injective functions and
at most `(3 / 4)^r` under the stated nonzero near-period condition; the first two single-run
ledger fields are `n + k` and `2 * (n + k)` [Simon1997]. -/
theorem simonNegligibleErrorAmplification :
    ∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
      (f : BooleanVec n → R) (k r : ℕ), 2 ≤ n + k →
    (Function.Injective f →
      (simonAmplifiedReject f (n + k) r) true ≤
        ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k)) ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n →
        (simonAmplifiedReject f (n + k) r) false ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r)) ∧
    ((simonDecodedRun f (n + k)).2.1 = n + k ∧
      (simonDecodedRun f (n + k)).2.2.1 = 2 * (n + k)) := by
  intro n R _ _ _ f k r hnk
  exact ⟨fun hf => amplified_true_le hf r,
    fun s hs hnear => amplified_false_le hnk hs hnear r,
    simonDecodedRun_ledger f⟩
end
end Qatlib.Papers.QPowerSimon97.Recovery
namespace Qatlib.Papers.QPowerSimon97.Recovery.SimonAssembly
variable {n : ℕ}
noncomputable section

/-- Nested expectations of a nonnegative extended-real function under two probability mass
functions can be interchanged. -/
lemma expectation_swap {α β : Type} (p : PMF α) (q : PMF β)
    (F : α → β → ℝ≥0∞) :
    expectation p (fun a => expectation q (F a)) =
      expectation q (fun b => expectation p (fun a => F a b)) := by
  unfold expectation
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  ac_rfl
end
noncomputable section

/-- Expectation under the uniform Boolean distribution is one half of each of the two function
values. -/
lemma expectation_uniform_bool (F : Bool → ℝ≥0∞) :
    expectation (PMF.uniformOfFintype' Bool) F =
      (1 / 2 : ℝ≥0∞) * F true + (1 / 2 : ℝ≥0∞) * F false := by
  simp [expectation, tsum_fintype, PMF.uniformOfFintype'_apply]
end
noncomputable section

/-- The oracle branch-guessing mass decomposes into the uniform-mask expectation of the equally
weighted strict-two-to-one and permutation branch success masses. -/
lemma guess_mass_decomp {n : ℕ} (P : PMF (SimonQueryTree n)) :
    simonOracleGuessMass P = expectation (PMF.uniformOfFintype' (BooleanVec n))
      (fun s => (1 / 2 : ℝ≥0∞) *
        (expectation (simonTwoToOneDist s) (fun f => SimonQueryTree.guessMass P f true) +
         expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
           (fun (π : Equiv.Perm (BooleanVec n)) => SimonQueryTree.guessMass P π false))) := by
  unfold simonOracleGuessMass
  rw [simonOracleConstruction, expectation_bind]
  apply expectation_congr
  intro s
  rw [expectation_bind, expectation_uniform_bool]
  simp only [Bool.false_eq_true, if_false, if_true, expectation_map]
  rw [mul_add]
  congr 1
  congr 1
  change expectation ((PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
    (fun (π : Equiv.Perm (BooleanVec n)) => (π : BooleanVec n → BooleanVec n)))
    (fun f => SimonQueryTree.guessMass P f false) = _
  rw [expectation_map]
end
noncomputable section

/-- A bound `bad ≤ (q^2 + 1) / 2^n` with `q ≥ 1` implies `(1 / 2) * (1 + bad) ≤ 1 / 2 + q^2 /
2^n` in the extended nonnegative reals. -/
lemma half_bad_le {n q : ℕ} (hq : 1 ≤ q) (bad : ℝ≥0∞)
    (hbad : bad ≤ ((q * q + 1 : ℕ) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹) :
    (1 / 2 : ℝ≥0∞) * (1 + bad) ≤
      (1 / 2 : ℝ≥0∞) + ((q * q : ℕ) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by
  have hqq : 1 ≤ q * q := by nlinarith
  have hnat : q * q + 1 ≤ 2 * (q * q) := by omega
  have hcast : ((q * q + 1 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) * (q * q : ℕ) := by
    exact_mod_cast hnat
  calc
    _ ≤ (1 / 2 : ℝ≥0∞) * (1 + 2 * (q * q : ℕ) * (2 ^ n : ℝ≥0∞)⁻¹) := by
      gcongr
      exact hbad.trans (mul_le_mul_of_nonneg_right hcast bot_le)
    _ = _ := by
      have hh : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
        rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by simp)]
      rw [mul_add, mul_one]
      congr 1
      calc
        (1 / 2 : ℝ≥0∞) * (2 * (q * q : ℕ) * (2 ^ n : ℝ≥0∞)⁻¹)
            = ((1 / 2 : ℝ≥0∞) * 2) * ((q * q : ℕ) * (2 ^ n : ℝ≥0∞)⁻¹) := by ac_rfl
        _ = _ := by rw [hh, one_mul]
end
noncomputable section

/-- If `q ≤ 2^(n / 4)` with natural division in the exponent, the extended-real birthday term
`q^2 / 2^n` is at most `2^(-n / 2)`. -/
lemma birthday_ennreal_le (n q : ℕ) (hq : q ≤ 2 ^ (n / 4)) :
    ((q * q : ℕ) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) / 2)) := by
  have h := ENNReal.ofReal_le_ofReal (birthday_query_le n q hq)
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ n),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] at h
  norm_num only [ENNReal.ofReal_ofNat] at h
  simpa only [div_eq_mul_inv] using! h
end
end Qatlib.Papers.QPowerSimon97.Recovery.SimonAssembly
namespace Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
variable {n : ℕ}
noncomputable section

/-- The expectation of the indicator that a Boolean-valued function equals `b` is the mass of
that event. -/
private lemma expectation_bool_indicator {α : Type} (p : PMF α) (F : α → Bool)
    (b : Bool) : expectation p (fun x => if F x = b then 1 else 0) =
      event p (fun x => F x = b) := by
  unfold event
  apply expectation_congr
  intro x
  split_ifs <;> rfl
end
noncomputable section

/-- For `n ≥ 1` and positive `q`, a randomized query tree bounded by `q` has oracle
branch-guessing mass at most `1 / 2 + q^2 / 2^n`. -/
lemma simonOracleGuessMass_le_birthday {n q : ℕ} (hn : 1 ≤ n) (hqpos : 1 ≤ q)
    (P : PMF (SimonQueryTree n)) (hq : SimonQueryTree.bounded P q) :
    simonOracleGuessMass P ≤ (1 / 2 : ℝ≥0∞) +
      ((q * q : ℕ) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by
  classical
  let ρ := simonPermutationLaw n
  let U := PMF.uniformOfFintype' (BooleanVec n)
  let A := expectation P (fun τ => event ρ (fun f => (SimonQueryTree.run f τ).1 = true))
  let B := expectation P (fun τ => event ρ (fun f => (SimonQueryTree.run f τ).1 = false))
  let D := fun s τ => event ρ (fun f => SimonQueryTree.periodHit s τ f)
  let bad := expectation U (fun s => expectation P (D s) + if s = 0 then 1 else 0)
  have hAB : A + B = 1 := by
    dsimp [A, B]
    rw [← expectation_add]
    calc
      _ = expectation P (fun _ => 1) := by
        apply expectation_congr
        intro τ
        have hfalse : event ρ (fun f => (SimonQueryTree.run f τ).1 = false) =
            event ρ (fun f => ¬ (SimonQueryTree.run f τ).1 = true) := by
          apply event_congr
          intro f
          cases (SimonQueryTree.run f τ).1 <;> simp
        rw [hfalse, event_partition]
      _ = 1 := expectation_const P 1
  have hstrict (s : BooleanVec n) :
      expectation (simonTwoToOneDist s) (fun f => SimonQueryTree.guessMass P f true) ≤
        A + (expectation P (D s) + if s = 0 then 1 else 0) := by
    unfold SimonQueryTree.guessMass
    rw [SimonAssembly.expectation_swap]
    simp_rw [expectation_bool_indicator]
    rw [← expectation_const P (if s = 0 then 1 else 0)]
    dsimp [A]
    rw [← expectation_add, ← expectation_add]
    apply expectation_le_of_forall
    intro τ
    by_cases hs : s = 0
    · simp only [hs, if_true]
      exact (event_le_one _ _).trans (le_add_left (le_add_left le_rfl))
    · simp only [hs, if_false, add_zero]
      exact simon_twoToOne_true_le_reference hn s hs τ
  have hB : expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
      (fun (π : Equiv.Perm (BooleanVec n)) => SimonQueryTree.guessMass P π false) = B := by
    dsimp [B]
    unfold SimonQueryTree.guessMass
    rw [SimonAssembly.expectation_swap]
    apply expectation_congr
    intro τ
    rw [expectation_bool_indicator]
    exact (event_map (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
      (fun (π : Equiv.Perm (BooleanVec n)) => (π : BooleanVec n → BooleanVec n))
      (fun f => (SimonQueryTree.run f τ).1 = false)).symm
  have hguess : simonOracleGuessMass P ≤ (1 / 2 : ℝ≥0∞) * (1 + bad) := by
    rw [SimonAssembly.guess_mass_decomp]
    rw [hB]
    calc
      _ ≤ expectation U (fun s => (1 / 2 : ℝ≥0∞) *
          ((A + (expectation P (D s) + if s = 0 then 1 else 0)) + B)) := by
        apply expectation_le_of_forall
        intro s
        gcongr
        exact hstrict s
      _ = (1 / 2 : ℝ≥0∞) * (1 + bad) := by
        rw [expectation_const_mul]
        have heq : (fun s => (A + (expectation P (D s) + if s = 0 then 1 else 0)) + B) =
            (fun s => 1 + (expectation P (D s) + if s = 0 then 1 else 0)) := by
          funext s
          calc
            _ = (A + B) + (expectation P (D s) + if s = 0 then 1 else 0) := by ac_rfl
            _ = _ := by rw [hAB]
        rw [heq, expectation_add, expectation_const]
  have hD : expectation U (fun s => expectation P (D s)) ≤
      ((q * q : ℕ) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by
    have h := randomized_independent_path_period_hit P ρ hq
    simp only [event_bind, event_map] at h
    rw [booleanVec_card] at h
    rw [Nat.cast_pow, Nat.cast_ofNat] at h
    rw [SimonAssembly.expectation_swap]
    refine (le_of_eq ?_).trans h
    apply expectation_congr
    intro τ
    exact SimonAssembly.expectation_swap U ρ
      (fun s f => if SimonQueryTree.periodHit s τ f then 1 else 0)
  have hzero : expectation U (fun s => if s = 0 then 1 else 0) =
      (2 ^ n : ℝ≥0∞)⁻¹ := by
    unfold expectation
    rw [tsum_eq_single 0]
    · simp [U, PMF.uniformOfFintype'_apply]
    · intro s hs
      simp [hs]
  have hbad : bad ≤ ((q * q + 1 : ℕ) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by
    dsimp [bad]
    rw [expectation_add, hzero]
    calc
      _ ≤ ((q * q : ℕ) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ + (2 ^ n : ℝ≥0∞)⁻¹ := by
        gcongr
      _ = _ := by simp [Nat.cast_add, add_mul]
  exact hguess.trans (SimonAssembly.half_bad_le hqpos bad hbad)
end
noncomputable section

/-- For `n ≥ 1`, a randomized query tree bounded by the natural budget `2^(n / 4)` guesses the
sampled oracle branch with mass at most `1 / 2 + 2^(-n / 2)` [Simon1997]. -/
theorem simonClassicalRandomOracleBound (n : ℕ) (hn : 1 ≤ n)
    (P : PMF (SimonQueryTree n)) (hq : SimonQueryTree.bounded P (2 ^ (n / 4))) :
    simonOracleGuessMass P ≤ ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
  have h := simonOracleGuessMass_le_birthday hn
    (Nat.one_le_pow (n / 4) 2 (by omega)) P hq
  refine h.trans ?_
  have hb := SimonAssembly.birthday_ennreal_le n (2 ^ (n / 4)) le_rfl
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))]
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using! add_le_add_right hb (1 / 2 : ℝ≥0∞)
end
noncomputable section

/-- Mapping a probability mass function twice equals mapping it once by the composite function. -/
theorem pmf_map_map {α β γ : Type} (g : β → γ) (f : α → β) (p : PMF α) :
    PMF.map g (PMF.map f p) = PMF.map (g ∘ f) p := by
  rw [← PMF.bind_pure_comp, PMF.bind_map, Function.comp_assoc, ← PMF.bind_pure_comp]
end
noncomputable section

/-- Each coordinate marginal of the fresh-run distribution equals the original decoded-run
distribution. -/
theorem simonFreshRuns_marginal {n r : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (m : ℕ) :
    ∀ i : Fin r, PMF.map (fun v => v i) (simonFreshRuns f m r) = (simonDecodedRun f m).1 := by
  induction r with
  | zero => intro i; exact Fin.elim0 i
  | succ r ih =>
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [simonFreshRuns]
      rw [PMF.map_bind]
      simp only [pmf_map_map, Function.comp_def, Fin.cons_zero]
      simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_const]
      calc PMF.bind (simonDecodedRun f m).1 (fun a => PMF.pure a)
          = PMF.map id (simonDecodedRun f m).1 := by
            simpa only [Function.comp_def] using!
              (PMF.bind_pure_comp (p := (simonDecodedRun f m).1) (f := id))
        _ = (simonDecodedRun f m).1 := PMF.map_id _
    · simp only [simonFreshRuns]
      rw [PMF.map_bind]
      simp only [pmf_map_map, Function.comp_def, Fin.cons_succ]
      simp only [PMF.bind_const]
      exact ih i'
end
noncomputable section

/-- The fresh runs have the original decoded-run marginals, and their three total ledger fields
equal `r * (n + k)`, `r * (2 * (n + k))`, and `r * (n + k)`. -/
theorem simonAmplifiedTotalLedger {n k r : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) :
    (∀ i : Fin r, PMF.map (fun v => v i) (simonFreshRuns f (n + k) r) =
      (simonDecodedRun f (n + k)).1) ∧
    r * (simonDecodedRun f (n + k)).2.1 = r * (n + k) ∧
    r * (simonDecodedRun f (n + k)).2.2.1 = r * (2 * (n + k)) ∧
    r * (simonDecodedRun f (n + k)).2.2.2 = r * (n + k) := by
  refine ⟨simonFreshRuns_marginal f (n + k), ?_, ?_, ?_⟩
  · have h := (simon_actual_preparation_and_quantum_cost f (n + k)).2.2.2.2
    rw [h]
  · have h := (simon_actual_preparation_and_quantum_cost f (n + k)).2.2.2.2
    rw [h]
  · have h := (simon_actual_preparation_and_quantum_cost f (n + k)).2.2.2.2
    rw [h]
end
noncomputable section

/-- For `n` runs with `n + 2 * n` samples each, the three total ledger fields are `3 * n^2`, `6
* n^2`, and `3 * n^2`. -/
theorem simonAmplifiedPaperSchedule (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) :
    n * (simonDecodedRun f (n + 2 * n)).2.1 = 3 * n ^ 2 ∧
    n * (simonDecodedRun f (n + 2 * n)).2.2.1 = 6 * n ^ 2 ∧
    n * (simonDecodedRun f (n + 2 * n)).2.2.2 = 3 * n ^ 2 := by
  have h := (simon_actual_preparation_and_quantum_cost f (n + 2 * n)).2.2.2.2
  rw [h]
  refine ⟨?_, ?_, ?_⟩ <;> ring
end
noncomputable section

/-- The combined two-sided amplification, exact ledger and marginal statements, and classical
random-oracle branch-guessing bound hold as specified by `Clause5TwoSidedAmplification`
[Simon1997]. -/
theorem clause5_complete : Clause5TwoSidedAmplification := by
  constructor
  · intro n R _ _ _ f k r hnk
    obtain ⟨hinj, hnear, _⟩ := simonNegligibleErrorAmplification n R f k r hnk
    refine ⟨hinj, hnear, ?_⟩
    constructor
    · exact (simon_actual_preparation_and_quantum_cost f (n + k)).2.2.2.2
    · exact simonFreshRuns_marginal f (n + k)
  · exact simonClassicalRandomOracleBound
end
noncomputable section

/-- If the natural query count is at most the real threshold `2^(n / 4)`, then the real birthday
term `q^2 / 2^n` is at most `2^(-n / 2)`. -/
lemma birthday_real_query_le (n q : ℕ)
    (hq : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4)) :
    ((q * q : ℕ) : ℝ) / (2 ^ n : ℝ) ≤ (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  have hp : ((2 : ℝ) ^ ((n : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  calc
    ((q * q : ℕ) : ℝ) / (2 ^ n : ℝ) = (q : ℝ) ^ 2 / (2 : ℝ) ^ n := by
      simp only [Nat.cast_mul, pow_two]
    _ ≤ ((2 : ℝ) ^ ((n : ℝ) / 4)) ^ 2 / (2 : ℝ) ^ n := by
      gcongr
    _ = (2 : ℝ) ^ ((n : ℝ) / 2) / (2 : ℝ) ^ (n : ℝ) := by
      rw [hp, Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((n : ℝ) / 2 - n) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ (-(n : ℝ) / 2) := by congr 1; ring
end
noncomputable section

/-- For `n ≥ 1`, a randomized query tree whose query bound is at most the real threshold `2^(n /
4)` guesses the sampled oracle branch with mass at most `1 / 2 + 2^(-n / 2)` [Simon1997]. -/
theorem simonClassicalRandomOracleBound_realBudget (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (P : PMF (SimonQueryTree n)) (hq : SimonQueryTree.bounded P q)
    (hreal : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4)) :
    simonOracleGuessMass P ≤ ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
  by_cases hqzero : q = 0
  · subst q
    apply simonClassicalRandomOracleBound n hn P
    intro τ hτ
    exact (hq τ hτ).trans (Nat.zero_le _)
  · have h := simonOracleGuessMass_le_birthday hn (by omega : 1 ≤ q) P hq
    have hb := ENNReal.ofReal_le_ofReal (birthday_real_query_le n q hreal)
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ n),
      ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] at hb
    norm_num only [ENNReal.ofReal_ofNat] at hb
    rw [div_eq_mul_inv] at hb
    refine h.trans ?_
    rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))]
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using! add_le_add_right hb (1 / 2 : ℝ≥0∞)
end
end Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
