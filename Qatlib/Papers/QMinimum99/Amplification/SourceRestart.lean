/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QMinimum99.Amplification.SourceIndependentRuns
public import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoal

@[expose] public section


/-!
# Two-entry restart comparison in the public source-clock model

Fixed source: Dürr--Høyer, arXiv:quant-ph/9607014v2, §2 and §3, pp. 1--2.
PDF SHA256: `ff5c2ff71415e22f0ddf799b31e9b82d1990db9c1fc9d62ea2aabea5907e06cf`.

For the strictly ordered two-entry table, this file evaluates the actual
`sourceInitialPMF`, including the source's unit initialization cost, its `6/5`
BBHT schedule, zero-iteration retries, and final quantum prefix observation.
At every deadline `d ≥ 1`, the exact bad-output probability is
`(1/4) * (1/3)^(floor d)`. The derivation uses the actual Born laws and
`sourceCallEval_bellman`, followed by bounded recurrence uniqueness.

The printed deadline D lies between 33 and 33.5. Thus one run at 2D has
failure `(1/4) * (1/3)^66`, whereas exactly two independent runs at D,
followed by the actual minimum fold, have failure `(1/16) * (1/3)^66`.
`longer_worse` proves the strict reverse comparison inside this public
source-clock model at the nominal timeouts derived from the paper.
Each interrupted run has its own strict-overrun final observation; these
boundaries are part of the source convention. No equality of realized
execution costs is assumed. The valid independent-repetition guarantee and
the original half-success theorem remain available in the imported library.

The public executor charges j Grover iterations, compressing zero-j retries
without charging sampling or the final membership check. Its checked quantum
attempt separately uses j+1 oracle queries. BBHT quant-ph/9605034v1, §4,
pp. 3--4, bounds Grover iterations and relates total time only up to order;
§3.1 also distinguishes Grover iterations from table lookups. A pathwise
paper-level total-cost bridge covering all those operations is still missing.
Thus this result is a model diagnosis, not a claimed refutation of the paper
under a fully charged physical/total-time semantics. A full source-cost comparison lies outside this result's scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical BigOperators ENNReal
open Filter
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Papers.QMinimum99.Amplification

/-- The strictly ordered two-entry table used to evaluate the original clock. -/
def twoTable (i : Fin 2) : ℕ := i.val

/-- The exact marked set below the larger entry of the two-entry table. -/
def twoMarked : Finset (Fin 2) := {0}

/-- The original table comparison marks precisely the smaller entry. -/
theorem marked_two : strictMarked twoTable 1 = twoMarked := by
  ext i
  fin_cases i <;> simp [strictMarked, twoTable, twoMarked]

/-- The two-entry table has the unique minimum at address zero. -/
theorem two_minimum (i : Fin 2) : (∀ j, twoTable i ≤ twoTable j) ↔ i = 0 := by
  fin_cases i <;> simp [twoTable, Fin.forall_fin_two]

/-- The source initialization clock on two entries is exactly one. -/
theorem log_two : binaryLog 2 = 1 := by
  simp [binaryLog, (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']

/-- Every positive stage of the actual BBHT schedule has two iteration choices. -/
theorem schedule_two (k : ℕ) (hk : 0 < k) : ExponentialSizes 2 k = 2 := by
  have hlow : 2 ≤ ExponentialSizes 2 k := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact sizes_ge_two_succ 2 j (by decide)
  have hhi : ExponentialSizes 2 k ≤ 2 := by
    unfold ExponentialSizes
    apply Nat.ceil_le.mpr
    rw [(search_exponential_schedule 2 (by decide)).1 k]
    refine (min_le_right _ _).trans ?_
    have hr : Real.sqrt (2:ℝ) ≤ 2 := by
      nlinarith [Real.sqrt_nonneg (2:ℝ), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    simpa only [Nat.cast_ofNat] using hr
  omega

/-- In the actual two-dimensional Grover state, zero or one iteration gives half marked mass. -/
theorem born_half (j : Fin 2) : MeasureProb (SearchState twoMarked j.val) twoMarked = 1/2 := by
  let θ := knownCountAngle (1/2)
  obtain ⟨_,_,_,hsq,hcos⟩ := knownCountAngle_spec (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ) < 1)
  have hs : Real.sin θ ≠ 0 := by intro hz; change (Real.sin θ)^2 = 1/2 at hsq; rw [hz] at hsq; norm_num at hsq
  rw [measureProb_groverState (by decide) twoMarked θ (by simpa [twoMarked, θ] using hsq) hs hcos]
  fin_cases j
  · simpa [θ] using hsq
  · norm_num only [Fin.val_one, Nat.cast_one, mul_one, show (2:ℝ)+1=3 by norm_num]
    rw [Real.sin_three_mul]
    change (Real.sin θ)^2 = 1/2 at hsq
    have he : 3 * Real.sin θ - 4 * Real.sin θ ^ 3 = Real.sin θ := by
      nlinarith [congrArg (fun t : ℝ => t * Real.sin θ) hsq]
    simpa [he] using hsq

/-- The actual checked output mass for the unique marked index is one half. -/
theorem checked_good (j : Fin 2) : CheckedOutputMass twoMarked j.val 0 = 1/2 := by
  rw [(search_checked_attempt (by decide : 0 < Fintype.card (Fin 2)) twoMarked j.val).2.1]
  simpa [twoMarked, MeasureProb] using born_half j

/-- No actual successful checked search outcome has the unmarked address. -/
theorem checked_bad (j : ℕ) : CheckedOutputMass twoMarked j 1 = 0 := by
  rw [(search_checked_attempt (by decide : 0 < Fintype.card (Fin 2)) twoMarked j).2.1]
  simp [twoMarked]

/-- The actual checked rejection mass is one half for both available iteration counts. -/
theorem reject_half (j : Fin 2) : CheckedRejectMass twoMarked j.val = 1/2 := by
  rw [(search_checked_attempt (by decide : 0 < Fintype.card (Fin 2)) twoMarked j.val).2.2.1,
    born_half]
  norm_num

/-- One available query includes the complete one-iteration Grover circuit and its final gates. -/
theorem partial_good : partialObsMass twoMarked 1 1 0 = 1/2 := by
  unfold partialObsMass partialState
  rw [queryPrefix_eq_self _ _ (by
    rw [queryCount_liftCircuit, (search_circuit_laws (by decide : 0 < Fintype.card (Fin 2)) twoMarked 1).1])]
  rw [(search_bit_oracle_compile_phase (fun i : Fin 2 => decide (i ∈ twoMarked))
    (SearchCircuit (Fin 2) 1) (Uniform (Fin 2))).2.2]
  simpa [SearchState, GroverState, SetOracle, SearchCircuit, twoMarked] using born_half (1 : Fin 2)

/-- The complementary actually observed address also has one-half mass. -/
theorem partial_bad : partialObsMass twoMarked 1 1 1 = 1/2 := by
  have h := (partialObsMass_sum_one (by decide : 0 < Fintype.card (Fin 2)) twoMarked 1 1).tsum_eq
  rw [tsum_fintype, Fin.sum_univ_two, partial_good] at h
  linarith

/-- A bounded real recurrence with geometric contraction has its unique constant solution. -/
private theorem bounded_unique (f : ℕ → ℝ) (K : ℝ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hrec : ∀ n, f n = (1/4) * f (n+1) + (3/4) * K) (n : ℕ) : f n = K := by
  have hi (k : ℕ) : f n - K = (1/4:ℝ)^k * (f (n+k)-K) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, hrec (n+k), pow_succ]
      simp only [Nat.add_assoc]
      ring
  have hb (k : ℕ) : |f n-K| ≤ (1/4:ℝ)^k := by
    rw [hi k, abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) k)]
    have he : |f (n+k)-K| ≤ 1 := abs_le.mpr ⟨by linarith [h0 (n+k)], by linarith [h1 (n+k)]⟩
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) k]
  have ht : Tendsto (fun _k : ℕ => |f n-K|) atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hb
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hz : |f n-K| = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- The actual source-call expectation of a unit-bounded payoff remains unit bounded. -/
private theorem call_bound (stage budget : ℕ) (G : CallResult 2 → ℝ≥0∞)
    (hG : ∀ x, G x ≤ 1) : sourceCallEval 2 (by decide) twoMarked stage budget G ≤ 1 := by
  rw [sourceCallEval_eq_expectation]
  exact expectation_le_one _ _ hG

/-- Every actually observed bad address has one-half probability at the one-query boundary. -/
private theorem partial_pmf : partialObsPMF (by decide : 0 < Fintype.card (Fin 2)) twoMarked 1 1 1 = 1/2 := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by norm_num)).mp
  rw [partialObsPMF_toReal, partial_bad]
  norm_num

/-- A terminal bad-address payoff has half expectation at that actual boundary observation. -/
private theorem partial_reward (G : CallResult 2 → ℝ≥0∞)
    (h0 : G (0,none) = 0) (h1 : G (1,none) = 1) :
    (∑' i : Fin 2, partialObsPMF (by decide) twoMarked 1 1 i * G (i,none)) = 1/2 := by
  rw [tsum_fintype, Fin.sum_univ_two, h0, h1]
  simpa using partial_pmf

/-- Positive rational reciprocals commute with the finite nonnegative embedding. -/
private theorem ofReal_frac (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (1/(n:ℝ)) = 1/(n:ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast]

/-- The exact positive-stage Bellman row comes from the actual Grover and interruption laws. -/
private theorem cap_row (stage budget : ℕ) (hs : 0 < stage) (hb : 0 < budget)
    (G : CallResult 2 → ℝ≥0∞) (hg : ∀ r, G (0,some r) = 0)
    (h0 : G (0,none) = 0) (h1 : G (1,none) = 1) :
    sourceCallEval 2 (by decide) twoMarked stage budget G =
      (1/4) * sourceCallEval 2 (by decide) twoMarked (stage+1) budget G +
      if budget = 1 then 1/4 else
        (1/4) * sourceCallEval 2 (by decide) twoMarked (stage+1) (budget-1) G := by
  rw [sourceCallEval_bellman 2 (by decide) twoMarked stage budget hb G]
  have hsize := schedule_two stage hs
  let z : Fin (ExponentialSizes 2 stage) := ⟨0, by omega⟩
  let o : Fin (ExponentialSizes 2 stage) := ⟨1, by omega⟩
  have hall : (Finset.univ : Finset (Fin (ExponentialSizes 2 stage))) = {z,o} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hz : i.val = 0
    · left; apply Fin.ext; exact hz
    · right; apply Fin.ext; dsimp [o]; have hi := i.isLt; omega
  rw [Fintype.sum_prod_type, hall, Finset.sum_insert (by simp [z,o]), Finset.sum_singleton]
  simp only [Fintype.sum_option, Fin.sum_univ_two, AttemptMass, z, o]
  rw [show CheckedRejectMass twoMarked 0 = 1/2 from reject_half (0:Fin 2),
    show CheckedRejectMass twoMarked 1 = 1/2 from reject_half (1:Fin 2),
    show CheckedOutputMass twoMarked 0 0 = 1/2 from checked_good (0:Fin 2),
    show CheckedOutputMass twoMarked 1 0 = 1/2 from checked_good (1:Fin 2),
    checked_bad, checked_bad]
  have hsizeR : (ExponentialSizes 2 stage : ℝ) = 2 := by exact_mod_cast hsize
  rw [hsizeR]
  have hfrac : ENNReal.ofReal (1/4:ℝ) = (1/4:ℝ≥0∞) := by
    simpa only [Nat.cast_ofNat] using ofReal_frac 4 (by decide)
  by_cases hbudget : budget = 1
  · subst budget
    norm_num [rawAttemptReward, hg, h0, h1, partial_pmf]
    rw [hfrac]
    simp only [one_div, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  · have hlarge : 1 < budget := by omega
    norm_num [rawAttemptReward, hb, hlarge, hbudget, hg]
    rw [hfrac]
    simp only [one_div]


/-- Unit-bounded finite masses admit addition and multiplication through the real projection. -/
private theorem real_quarters (u v : ℝ≥0∞) (hu : u ≤ 1) (hv : v ≤ 1) :
    ((1/4)*u + (1/4)*v).toReal = (1/4:ℝ)*u.toReal + (1/4:ℝ)*v.toReal := by
  have hu' : u ≠ ∞ := ne_of_lt (hu.trans_lt (by simp))
  have hv' : v ≠ ∞ := ne_of_lt (hv.trans_lt (by simp))
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

/-- The exact positive-stage bad-output expectation under the genuine source executor. -/
private theorem cap_exact (budget : ℕ) (hb : 0 < budget)
    (G : CallResult 2 → ℝ≥0∞) (hG : ∀ x, G x ≤ 1)
    (hg : ∀ r, G (0,some r) = 0) (h0 : G (0,none) = 0) (h1 : G (1,none) = 1) :
    ∀ stage : ℕ, 0 < stage →
      (sourceCallEval 2 (by decide) twoMarked stage budget G).toReal = (1/3:ℝ)^budget := by
  induction budget using Nat.strong_induction_on with
  | h b ih =>
    intro stage hs
    let K : ℝ := (1/3)^b
    let f : ℕ → ℝ := fun n => (sourceCallEval 2 (by decide) twoMarked (n+1) b G).toReal
    have hf0 : ∀ n, 0 ≤ f n := fun _ => ENNReal.toReal_nonneg
    have hf1 : ∀ n, f n ≤ 1 := by
      intro n
      exact (ENNReal.toReal_mono (by norm_num) (call_bound (n+1) b G hG)).trans_eq (by norm_num)
    have hK0 : 0 ≤ K := pow_nonneg (by norm_num) _
    have hK1 : K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hrec : ∀ n, f n = (1/4)*f (n+1) + (3/4)*K := by
      intro n
      have hr := congrArg ENNReal.toReal (cap_row (n+1) b (by omega) hb G hg h0 h1)
      by_cases hb1 : b = 1
      · simp only [hb1, ↓reduceIte] at hr
        have he : ((1/4:ℝ≥0∞) * sourceCallEval 2 (by decide) twoMarked (n+1+1) 1 G + 1/4).toReal =
            (1/4:ℝ) * (sourceCallEval 2 (by decide) twoMarked (n+1+1) 1 G).toReal + 1/4 := by
          simpa only [mul_one, ENNReal.toReal_one] using real_quarters
            (sourceCallEval 2 (by decide) twoMarked (n+1+1) 1 G) 1
            (call_bound _ _ G hG) le_rfl
        rw [he] at hr
        norm_num [f, K, hb1] at *
        exact hr
      · have hprev : 0 < b-1 := by omega
        simp only [ite_eq_right hb1] at hr
        rw [real_quarters _ _ (call_bound _ _ G hG) (call_bound _ _ G hG)] at hr
        rw [ih (b-1) (by omega) hprev (n+1+1) (by omega)] at hr
        have hpow : (1/3:ℝ)^(b-1) = 3*K := by
          dsimp [K]
          have he : b = (b-1)+1 := by omega
          conv_rhs => rw [he, pow_succ]
          ring
        rw [hpow] at hr
        dsimp only [f]
        rw [hr]
        ring
    have he := bounded_unique f K hf0 hf1 hK0 hK1 hrec (stage-1)
    simpa only [f, K, Nat.sub_add_cancel hs] using he

/-- The genuine first size-one BBHT attempt contributes another half factor. -/
private theorem zero_row (budget : ℕ) (hb : 0 < budget)
    (G : CallResult 2 → ℝ≥0∞) (hg : ∀ r, G (0,some r) = 0) :
    sourceCallEval 2 (by decide) twoMarked 0 budget G =
      (1/2) * sourceCallEval 2 (by decide) twoMarked 1 budget G := by
  rw [sourceCallEval_bellman 2 (by decide) twoMarked 0 budget hb G]
  have hsize : ExponentialSizes 2 0 = 1 := by norm_num [ExponentialSizes, ExponentialWidth]
  let z : Fin (ExponentialSizes 2 0) := ⟨0, by omega⟩
  have hall : (Finset.univ : Finset (Fin (ExponentialSizes 2 0))) = {z} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Fin.ext
    dsimp [z]
    have hi := i.isLt
    omega
  rw [Fintype.sum_prod_type, hall, Finset.sum_singleton]
  simp only [Fintype.sum_option, Fin.sum_univ_two, AttemptMass, z]
  rw [show CheckedRejectMass twoMarked 0 = 1/2 from reject_half (0:Fin 2),
    show CheckedOutputMass twoMarked 0 0 = 1/2 from checked_good (0:Fin 2),
    checked_bad]
  have hsizeR : (ExponentialSizes 2 0 : ℝ) = 1 := by exact_mod_cast hsize
  rw [hsizeR]
  norm_num [rawAttemptReward, hb, hg]
  have hfrac : ENNReal.ofReal (1/2:ℝ) = (1/2:ℝ≥0∞) := by
    simpa only [Nat.cast_ofNat] using ofReal_frac 2 (by decide)
  rw [hfrac]
  simp only [one_div]


/-- The bad-output indicator for the strictly ordered two-entry table. -/
def twoBad (i : Fin 2) : ℝ≥0∞ := if i = 1 then 1 else 0

/-- The indicator is a bounded actual output payoff. -/
private theorem two_bad_bound (i : Fin 2) : twoBad i ≤ 1 := by
  fin_cases i <;> norm_num [twoBad]

/-- Any observed address is the exact checked update from the larger threshold. -/
private theorem update_two (i : Fin 2) : checkedUpdate twoTable 1 i = i := by
  fin_cases i <;> simp [checkedUpdate, twoTable]

/-- An initial actual minimum can never contribute a bad-output reward. -/
private theorem good_min_eval (d : ℝ) :
    sourceMinimumEval twoTable (by decide) d 0 twoBad = 0 := by
  rw [sourceMinimumEval_eq_expectation,
    sourceMinimumPMF_preserves_minimum twoTable (by decide) d 0
      (by intro j; simp [twoTable]), expectation_pure]
  norm_num [twoBad]

/-- From the larger threshold, the actual source-clock executor has an exact geometric tail. -/
private theorem bad_min_eval (d : ℝ) (hd : 1 ≤ d) :
    (sourceMinimumEval twoTable (by decide) d 1 twoBad).toReal =
      (1/2:ℝ) * (1/3:ℝ)^(Nat.floor d) := by
  let b := queryBoundary (d-1)
  let G : CallResult 2 → ℝ≥0∞ := fun x =>
    match x.2 with
    | none => twoBad (checkedUpdate twoTable 1 x.1)
    | some r => outerEval twoTable (by decide) (Nat.floor d)
        (d-1-((b-r : ℕ):ℝ)) (checkedUpdate twoTable 1 x.1) twoBad
  have hb : 0 < b := by dsimp [b, queryBoundary]; omega
  have hbeq : b = Nat.floor d := by
    dsimp [b, queryBoundary]
    rw [Nat.floor_sub_one]
    have hh : 1 ≤ Nat.floor d := (Nat.le_floor_iff (by linarith : (0:ℝ) ≤ d)).mpr (by simpa only [Nat.cast_one] using hd)
    omega
  have he : sourceMinimumEval twoTable (by decide) d 1 twoBad =
      sourceCallEval 2 (by decide) twoMarked 0 b G := by
    simp only [sourceMinimumEval, show ¬(2:ℕ)=1 by decide, ↓reduceDIte]
    rw [outerEval]
    simp only [Nat.cast_ofNat, show ¬ d < 0 by linarith, log_two,
      show ¬ d-1 < 0 by linarith, marked_two, ↓reduceIte]
    rfl
  have hG : ∀ x, G x ≤ 1 := by
    rintro ⟨i,r⟩
    cases r with
    | none => exact two_bad_bound _
    | some r =>
      dsimp [G]
      rw [outerEval_eq_expectation]
      exact expectation_le_one _ _ two_bad_bound
  have hg : ∀ r, G (0,some r) = 0 := by
    intro r
    dsimp [G]
    rw [update_two, outerEval_of_minimum twoTable (by decide) _ _ 0
      (by intro j; simp [twoTable])]
    norm_num [twoBad]
  have h0 : G (0,none) = 0 := by simp [G, update_two, twoBad]
  have h1 : G (1,none) = 1 := by simp [G, update_two, twoBad]
  rw [he, zero_row b hb G hg, ENNReal.toReal_mul,
    cap_exact b hb G hG hg h0 h1 1 (by decide), hbeq]
  norm_num

/-- The event library and the executor use the same actual bad-output indicator. -/
private theorem bad_event_eval (p : PMF (Fin 2)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun i => i = 1) =
      expectation p twoBad := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation expectation
  apply tsum_congr
  intro i
  by_cases hi : i = 1 <;> simp [twoBad, hi]

/-- The uniformly initialized actual executor has a closed two-entry failure formula. -/
theorem source_failure (d : ℝ) (hd : 1 ≤ d) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (sourceInitialPMF twoTable (by decide) d) (fun i => i = 1)).toReal =
        (1/4:ℝ)*(1/3:ℝ)^(Nat.floor d) := by
  rw [bad_event_eval]
  rw [← sourceInitialEval_eq_expectation]
  unfold sourceInitialEval
  rw [tsum_fintype, Fin.sum_univ_two, good_min_eval, mul_zero, zero_add,
    ENNReal.toReal_mul, iterationPMF_toReal, bad_min_eval d hd]
  ring

/-- The printed two-entry deadline and its double lie in their exact integer clock intervals. -/
theorem timeout_two : 33 < sourceTimeout 2 ∧ sourceTimeout 2 < 67/2 := by
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hslo : (141/100:ℝ) < Real.sqrt 2 := by nlinarith
  have hshi : Real.sqrt (2:ℝ) < 142/100 := by nlinarith
  unfold sourceTimeout
  norm_num only [Nat.cast_ofNat, log_two, one_pow]
  constructor <;> linarith

/-- The source's literal deadline has floor 33; twice that deadline has floor 66. -/
theorem timeout_floors : Nat.floor (sourceTimeout 2) = 33 ∧
    Nat.floor (2*sourceTimeout 2) = 66 := by
  constructor
  · exact (Nat.floor_eq_iff (by linarith [timeout_two.1])).mpr
      ⟨by norm_num only [Nat.cast_ofNat]; linarith [timeout_two.1],
        by norm_num only [Nat.cast_ofNat]; linarith [timeout_two.2]⟩
  · exact (Nat.floor_eq_iff (by linarith [timeout_two.1])).mpr
      ⟨by norm_num only [Nat.cast_ofNat]; linarith [timeout_two.1],
        by norm_num only [Nat.cast_ofNat]; linarith [timeout_two.2]⟩


/-- On the actual two-entry table, failure is exactly the larger returned address. -/
private theorem not_minimum (i : Fin 2) : (¬ ∀ j, twoTable i ≤ twoTable j) ↔ i = 1 := by
  fin_cases i <;> simp [twoTable, Fin.forall_fin_two]

/-- Failure of a literal minimum-fold over two independent output laws multiplies exactly. -/
private theorem two_fold_bad (p q : PMF (Fin 2)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (Qatlib.Papers.QMinimum99.Amplification.sourceCombineRuns twoTable p q) (fun i => i = 1) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun i => i = 1) *
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun i => i = 1) := by
  simpa only [not_minimum] using
    Qatlib.Papers.QMinimum99.Amplification.sourceCombine_failure twoTable p q

/-- Exact failure of the literal two independent original-timeout executions. -/
theorem repeat_failure :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (Qatlib.Papers.QMinimum99.Amplification.sourceIndependentRuns twoTable (by decide) 2 (by decide))
      (fun i => i = 1)).toReal = (1/16:ℝ)*(1/3:ℝ)^66 := by
  simp only [Qatlib.Papers.QMinimum99.Amplification.sourceIndependentRuns,
    show (2:ℕ)-1=1 by decide, Qatlib.Papers.QMinimum99.Amplification.sourceRepeatedRuns,
    two_fold_bad, ENNReal.toReal_mul]
  unfold Qatlib.Papers.QMinimum99.Amplification.sourceSingleRun
  rw [source_failure (sourceTimeout 2) (by linarith [timeout_two.1]), timeout_floors.1]
  norm_num

/-- Exact failure of one genuine source-clock execution at the doubled original timeout. -/
theorem longer_failure :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (sourceInitialPMF twoTable (by decide) (2*sourceTimeout 2)) (fun i => i = 1)).toReal =
        (1/4:ℝ)*(1/3:ℝ)^66 := by
  rw [source_failure (2*sourceTimeout 2) (by linarith [timeout_two.1]), timeout_floors.2]

/-- The literal original-clock long execution has strictly more failure than independent repetition. -/
theorem failure_worse :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (Qatlib.Papers.QMinimum99.Amplification.sourceIndependentRuns twoTable (by decide) 2 (by decide))
      (fun i => i = 1)).toReal <
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (sourceInitialPMF twoTable (by decide) (2*sourceTimeout 2)) (fun i => i = 1)).toReal := by
  rw [repeat_failure, longer_failure]
  norm_num

/-- Success and actual bad-output mass partition every normalized two-entry output law. -/
private theorem success_total (p : PMF (Fin 2)) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p
      (fun i => ∀ j, twoTable i ≤ twoTable j)).toReal +
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun i => i = 1)).toReal = 1 := by
  have ht := congrArg ENNReal.toReal
    (Qatlib.Papers.QMinimum99.Amplification.source_event_total p (fun i => ∀ j, twoTable i ≤ twoTable j))
  have hsne := ne_of_lt ((Qatlib.Papers.QMinimum99.Amplification.source_event_le_one p
    (fun i => ∀ j, twoTable i ≤ twoTable j)).trans_lt (by simp : (1:ℝ≥0∞)<∞))
  have hfne := ne_of_lt ((Qatlib.Papers.QMinimum99.Amplification.source_event_le_one p
    (fun i => ¬∀ j, twoTable i ≤ twoTable j)).trans_lt (by simp : (1:ℝ≥0∞)<∞))
  rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at ht
  simpa only [not_minimum] using ht

/-- The public source-clock executor has less success at a doubled cutoff than two restarts. -/
theorem longer_worse :
    sourceSuccess twoTable (by decide) (2*sourceTimeout 2) <
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (Qatlib.Papers.QMinimum99.Amplification.sourceIndependentRuns twoTable (by decide) 2 (by decide))
        (fun i => ∀ j, twoTable i ≤ twoTable j)).toReal := by
  have hrepeat := success_total
    (Qatlib.Papers.QMinimum99.Amplification.sourceIndependentRuns twoTable (by decide) 2 (by decide))
  have hlong := success_total (sourceInitialPMF twoTable (by decide) (2*sourceTimeout 2))
  have he : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (sourceInitialPMF twoTable (by decide) (2*sourceTimeout 2))
      (fun i => ∀ j, twoTable i ≤ twoTable j)).toReal =
      sourceSuccess twoTable (by decide) (2*sourceTimeout 2) := by
    unfold sourceSuccess
    rw [sourceInitialEval_eq_expectation]
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation expectation
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : ∀ j, twoTable i ≤ twoTable j <;> simp [hi]
  rw [he] at hlong
  linarith [failure_worse]


end Qatlib.Papers.QMinimum99.Amplification
