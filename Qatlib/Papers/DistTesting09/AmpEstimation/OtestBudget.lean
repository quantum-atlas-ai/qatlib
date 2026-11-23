/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DistTesting09.AmpEstimation.QueryBudget
public import Qatlib.Papers.DistTesting09.AmpEstimation.OracleState

@[expose] public section

/-!
# Estimator budget of the orthogonality test

The proof of Lemma 7 of [BravyiHarrowHassidim2011] estimates the distinct-set mass `q_A`
and rejects when the estimate reaches half the Lemma 6 threshold.  With precision `δ = q_A / 2`
and failure probability `ω = 1/2`, Theorem 5 requires `K = O(1 / sqrt q_A)` queries; combined
with the Lemma 6 lower bound `q_A ≥ ε ^ 3 * M / (2 ^ 11 * N)` this gives the paper's
`K = O(sqrt (N / (ε ^ 3 * M)))`.

This module derives both bounds from the phase-estimation interface of `QueryBudget`.  The
only unproved input remains the cited amplitude-estimation tail; the query-count arithmetic is
fully explicit, with a single constant outside all quantifiers.  The Lemma 6 probability
statement itself is not proved here, so the second theorem takes its conclusion
`ε ^ 3 * M / (2 ^ 11 * N) ≤ q_A` as a hypothesis, exactly as the paper's proof does.

## Main statements

* `exists_otest_estimator_budget`: a uniform constant bounds the estimator queries by
  `C / sqrt q_A` while retaining success probability at least one half at precision `q_A / 2`.
* `exists_otest_estimator_budget_scaled`: a fixed budget bounded by
  `C * sqrt (N / (ε ^ 3 * M))` gives conditional rejection probability at least one half for
  every distinct outcome set meeting the Lemma 6 threshold.

## References

* [Bravyi et al., 2011][BravyiHarrowHassidim2011], Lemma 7 and its proof
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.DistTesting09.AmpEstimation

/-- Theorem 5 at precision `q_A / 2` and failure probability one half gives an estimator budget
`C / sqrt q_A` and success probability at least one half. -/
theorem exists_otest_estimator_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ qA : ℝ, 0 < qA → qA ≤ 1 →
      ∃ k n : ℕ, 2 ≤ k ∧ 0 < n ∧ 2 * (n : ℝ) ≤ C / Real.sqrt qA ∧
        (∀ (Ω : Type) [Fintype Ω] (Pr : FinDist Ω) (est : Ω → ℝ),
          eventMass Pr (fun x => ¬ (|est x - qA| ≤ phaseAccuracy qA (k : ℝ) (n : ℝ)))
            ≤ phaseFailure (k : ℝ) →
          1 / 2 ≤ eventMass Pr (fun x => |est x - qA| ≤ qA / 2)) := by
  obtain ⟨C₀, hC₀, hmain⟩ := exists_estprob_budget
  refine ⟨8 * C₀, by positivity, ?_⟩
  intro qA hqA hqA1
  have hqA2 : 0 < qA / 2 := by positivity
  have hqA2' : qA / 2 ≤ 1 := by linarith
  obtain ⟨k, n, hk2, hnpos, hn, hsucc⟩ :=
    hmain qA (qA / 2) (1 / 2) hqA.le hqA1 hqA2 hqA2' (by norm_num) (by norm_num)
  refine ⟨k, n, hk2, hnpos, ?_, ?_⟩
  have hsqrt : (0 : ℝ) < Real.sqrt qA := Real.sqrt_pos_of_pos hqA
  have hsq : Real.sqrt qA * Real.sqrt qA = qA := Real.mul_self_sqrt hqA.le
  have hterm1 : Real.sqrt qA / (1 / 2 * (qA / 2)) = 4 / Real.sqrt qA := by
    field_simp
    nlinarith
  have hterm2 : 1 / (1 / 2 * Real.sqrt (qA / 2)) ≤ 4 / Real.sqrt qA := by
    have hpos : 0 < Real.sqrt (qA / 2) := Real.sqrt_pos_of_pos hqA2
    rw [show (1 : ℝ) / (1 / 2 * Real.sqrt (qA / 2)) = 2 / Real.sqrt (qA / 2) by
      field_simp]
    rw [div_le_div_iff₀ hpos hsqrt]
    have hroot : Real.sqrt (qA / 2) * Real.sqrt 2 = Real.sqrt qA := by
      rw [← Real.sqrt_mul hqA2.le]
      congr 1
      field_simp
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    have hpos2 : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
    nlinarith
  have hsum : Real.sqrt qA / (1 / 2 * (qA / 2)) + 1 / (1 / 2 * Real.sqrt (qA / 2))
      ≤ 8 / Real.sqrt qA := by
    rw [hterm1]
    have hsplit : (8 : ℝ) / Real.sqrt qA = 4 / Real.sqrt qA + 4 / Real.sqrt qA := by ring
    rw [hsplit]
    linarith
  calc 2 * (n : ℝ) ≤ C₀ * (Real.sqrt qA / (1 / 2 * (qA / 2))
        + 1 / (1 / 2 * Real.sqrt (qA / 2))) := hn
    _ ≤ C₀ * (8 / Real.sqrt qA) := by
        exact mul_le_mul_of_nonneg_left hsum hC₀.le
    _ = 8 * C₀ / Real.sqrt qA := by ring
  · intro Ω _ Pr est h
    have := hsucc Ω Pr est h
    linarith

/-- Under a positive lower bound `T` on the accepted mass, a common budget works for every
mass at least `T`. This allows the budget to be set before the accepted outcomes are known. -/
theorem exists_otest_budget_of_threshold {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ 2 * (n : ℝ) ≤ 106 / Real.sqrt T ∧
      ∀ qA : ℝ, T ≤ qA → qA ≤ 1 → phaseAccuracy qA 2 (n : ℝ) ≤ qA / 2 := by
  have hsT := Real.sqrt_pos_of_pos hT
  let n : ℕ := ⌈52 / Real.sqrt T⌉₊
  have hn : 52 / Real.sqrt T ≤ (n : ℝ) := Nat.le_ceil _
  have hn' : (n : ℝ) < 52 / Real.sqrt T + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnpos : 0 < n := by
    have : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by positivity) hn
    exact_mod_cast this
  have hone : 1 ≤ 1 / Real.sqrt T := by
    rw [le_div_iff₀ hsT, one_mul]
    exact Real.sqrt_le_one.mpr hT1
  refine ⟨n, hnpos, ?_, ?_⟩
  · have hsum : (106 : ℝ) / Real.sqrt T =
        2 * (52 / Real.sqrt T + 1 / Real.sqrt T) := by ring
    rw [hsum]
    linarith
  intro qA hTq hqA1
  have hqA := hT.trans_le hTq
  have hqhalf : 0 < qA / 2 := by positivity
  have hsq := Real.sqrt_pos_of_pos hqA
  have hshalf := Real.sqrt_pos_of_pos hqhalf
  have hbudget : 52 / Real.sqrt qA ≤ (n : ℝ) :=
    (div_le_div_of_nonneg_left (by norm_num) hsT (Real.sqrt_le_sqrt hTq)).trans hn
  have hfirst : (13 : ℝ) * (2 : ℕ) * Real.sqrt qA / (qA / 2) =
      52 / Real.sqrt qA := by
    field_simp
    norm_num [Real.sq_sqrt hqA.le]; ring
  have hroot : Real.sqrt qA ≤ 2 * Real.sqrt (qA / 2) := calc
    Real.sqrt qA ≤ Real.sqrt ((2 * Real.sqrt (qA / 2)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sq_sqrt hqhalf.le]
    _ = 2 * Real.sqrt (qA / 2) := Real.sqrt_sq (by positivity)
  have hsecond : (5 : ℝ) * (2 : ℕ) / Real.sqrt (qA / 2) ≤ 52 / Real.sqrt qA := by
    rw [div_le_div_iff₀ hshalf hsq]
    nlinarith
  exact phaseAccuracy_le_delta 2 n hqA.le hqA1 hqhalf hnpos
    (hfirst.trans_le hbudget) (hsecond.trans hbudget)

/-- A single budget chosen from the parameters of Lemma 6 gives the conditional rejection
bound of Lemma 7 for every distinct outcome set meeting the threshold under the oracle
distribution. The hypothesis on the finite estimator law is the cited phase-estimation tail
at that budget. -/
theorem exists_otest_estimator_budget_scaled :
    ∃ C : ℝ, 0 < C ∧ ∀ (N M : ℕ) (ε : ℝ), 0 < N → 0 < M → 0 < ε →
      ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) ≤ 1 →
      ∃ n : ℕ, 0 < n ∧
        2 * (n : ℝ) ≤ C * Real.sqrt ((N : ℝ) / (ε ^ 3 * (M : ℝ))) ∧
        ∀ {S : ℕ} (O : Fin S → Fin N) (hS : 0 < S) (A : Finset (Fin N)),
          let qA := eventMass (oracleDist O hS) (· ∈ A)
          ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) ≤ qA →
          ∀ (Ω : Type) [Fintype Ω] (Pr : FinDist Ω) (est : Ω → ℝ),
            eventMass Pr (fun x => ¬ (|est x - qA| ≤ phaseAccuracy qA 2 (n : ℝ)))
              ≤ phaseFailure 2 →
            1 / 2 ≤ eventMass Pr (fun x => ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ)) ≤ est x) := by
  refine ⟨4876, by norm_num, ?_⟩
  intro N M ε hN hM hε hT1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  let T : ℝ := ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ))
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨n, hn, hbudget, hacc⟩ := exists_otest_budget_of_threshold hT hT1
  refine ⟨n, hn, ?_, ?_⟩
  · have hinv : T⁻¹ = (2 ^ 11 : ℝ) * ((N : ℝ) / (ε ^ 3 * (M : ℝ))) := by
      dsimp [T]
      field_simp
    have hroot : 1 / Real.sqrt T =
        Real.sqrt (2 ^ 11 : ℝ) * Real.sqrt ((N : ℝ) / (ε ^ 3 * (M : ℝ))) := by
      rw [one_div, ← Real.sqrt_inv, hinv, Real.sqrt_mul (by norm_num)]
    have hconst : Real.sqrt (2 ^ 11 : ℝ) ≤ 46 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    calc
      2 * (n : ℝ) ≤ 106 / Real.sqrt T := hbudget
      _ = 106 * (1 / Real.sqrt T) := by ring
      _ ≤ 4876 * Real.sqrt ((N : ℝ) / (ε ^ 3 * (M : ℝ))) := by
        rw [hroot]
        have h := mul_le_mul_of_nonneg_right hconst
          (Real.sqrt_nonneg ((N : ℝ) / (ε ^ 3 * (M : ℝ))))
        linarith
  · intro S O hS A qA hTq Ω _ Pr est htail
    have hδ := hacc qA hTq (eventMass_le_one _ _)
    have hreject : ∀ x, |est x - qA| ≤ phaseAccuracy qA 2 (n : ℝ) →
        ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ)) ≤ est x := by
      intro x hx
      have hhalf : ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ)) = T / 2 := by
        dsimp [T]
        field_simp [hNpos.ne']
      rw [hhalf]
      have hlow := (abs_le.mp (hx.trans hδ)).1
      change T ≤ qA at hTq
      linarith
    have hmono := eventMass_mono Pr hreject
    have hcompl := eventMass_compl Pr (fun x => |est x - qA| ≤ phaseAccuracy qA 2 (n : ℝ))
    rw [show phaseFailure (2 : ℝ) = 1 / 2 by norm_num [phaseFailure], hcompl] at htail
    linarith

end Qatlib.Papers.DistTesting09.AmpEstimation
