module

public import Qatlib.Papers.DistTesting09.AmpEstimation.QueryBudget
public import Qatlib.Papers.DistTesting09.AmpEstimation.OracleState
public import Qatlib.Papers.DistTesting09.AmpEstimation.OtestBudget

@[expose] public section

/-!
# Consumer regression for the DistTesting09 amplitude-estimation increment

The concrete instance is the two-outcome, four-input oracle that maps two inputs to each
outcome, with the single accepted outcome `0` and the non-degenerate domain `Fin 4`.  The
probability of `0` is `1 / 2`, the oracle state has Euclidean norm one, the projected squared
norm is `1 / 2`, and the projection has `L2Operator` norm one.  The probability-estimation
statements are instantiated at `p_A = 1 / 2`, `δ = 1 / 10` and `ω = 1 / 4` with the constant
estimator `1 / 2`, which satisfies the cited phase-estimation tail with zero failure.
-/

set_option autoImplicit false

namespace QatlibTests.DistTesting09AmplitudeRegression

open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.DistTesting09.AmpEstimation

/-- The four-input, two-outcome oracle with two inputs per outcome. -/
def twoTwo : Fin 4 → Fin 2 := fun s => if (s : ℕ) < 2 then 0 else 1

/-- The point mass on a one-point probability space. -/
def pointMass : FinDist (Fin 1) where
  prob _ := 1
  nonneg _ := by norm_num
  sum_one := by simp

/-- Both inputs `0` and `1` map to the accepted outcome, so the fiber has two elements. -/
theorem twoTwo_fiber : fiberCount twoTwo {0} = 2 := by
  decide

/-- The generated distribution assigns mass `1 / 2` to the accepted outcome. -/
theorem twoTwo_mass :
    (∑ i ∈ ({0} : Finset (Fin 2)), (oracleDist twoTwo (by norm_num : 0 < 4)).prob i)
      = 1 / 2 := by
  rw [oracleDist_mass, twoTwo_fiber]
  norm_num

/-- The concrete oracle state is a unit vector in the complex Euclidean space. -/
theorem twoTwo_state_norm :
    ‖oracleState (S := 4) (N := 2) twoTwo‖ = 1 :=
  norm_oracleState twoTwo (by norm_num)

/-- The projected state has squared Euclidean norm equal to the mass `1 / 2`. -/
theorem twoTwo_projected_norm_sq :
    ‖goodSubstate (S := 4) (N := 2) twoTwo {0}‖ ^ 2 = 1 / 2 := by
  rw [norm_sq_goodSubstate_eq_oracleMass twoTwo {0} (by norm_num), twoTwo_mass]

/-- The projector onto the accepted outcome has `L2Operator` norm one. -/
theorem twoTwo_projector_norm :
    ‖goodProjector (N := 2) 4 {0}‖ = 1 :=
  norm_goodProjector_eq_one (by norm_num) {0} ⟨0, by decide⟩

/-- The blank register is outside the outcome projector, even on an accepted input. -/
theorem twoTwo_projector_blank :
    goodProjector (N := 2) 4 {0} (0, 0) (0, 0) = 0 := by
  simp [goodProjector, regIncl]

/-- The uniform Theorem 5 constant instantiated at `p_A = 1/2`, `δ = 1/10`, `ω = 1/4`, with the
constant estimator `1/2` and the resulting success probability at least `3/4`. -/
theorem twoTwo_estprob_budget :
    ∃ (C : ℝ) (k n : ℕ), 0 < C ∧ 2 ≤ k ∧ 0 < n ∧
      2 * (n : ℝ) ≤ C * (Real.sqrt (1 / 2) / ((1 / 4) * (1 / 10))
        + 1 / ((1 / 4) * Real.sqrt (1 / 10))) ∧
      1 - 1 / 4 ≤ eventMass pointMass (fun _ => |(1 / 2 : ℝ) - 1 / 2| ≤ 1 / 10) := by
  obtain ⟨C, hC, h⟩ := exists_estprob_budget
  obtain ⟨k, n, hk, hn, hbound, hsucc⟩ :=
    h (1 / 2) (1 / 10) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  refine ⟨C, k, n, hC, hk, hn, hbound, ?_⟩
  have hacc : (0 : ℝ) ≤ phaseAccuracy (1 / 2) (k : ℝ) (n : ℝ) :=
    phaseAccuracy_nonneg _ _ _ (by positivity) (by positivity)
  have hbad : eventMass pointMass
      (fun (x : Fin 1) => ¬ (|(1 / 2 : ℝ) - 1 / 2| ≤ phaseAccuracy (1 / 2) (k : ℝ) (n : ℝ)))
      ≤ phaseFailure (k : ℝ) := by
    have hzero : ∀ (x : Fin 1),
        ¬ (¬ (|(1 / 2 : ℝ) - 1 / 2| ≤ phaseAccuracy (1 / 2) (k : ℝ) (n : ℝ))) := by
      intro x
      simpa using hacc
    rw [eventMass_false pointMass hzero]
    exact phaseFailure_nonneg hk
  have := hsucc (Fin 1) pointMass (fun _ => (1 / 2 : ℝ)) hbad
  simpa using this

/-- A zero estimate for `p_A = 0` succeeds with probability one. -/
theorem twoTwo_zero_certain :
    eventMass pointMass (fun _ => |(0 : ℝ) - 0| ≤ 1 / 10) = 1 :=
  estprob_zero_certain pointMass (fun _ => 0) (fun _ => rfl) (by norm_num)

/-- The orthogonality estimator budget at `q_A = 1/2` is bounded by a uniform constant over
`sqrt (1/2)`. -/
theorem twoTwo_otest_budget :
    ∃ (C : ℝ) (k n : ℕ), 0 < C ∧ 2 ≤ k ∧ 0 < n ∧ 2 * (n : ℝ) ≤ C / Real.sqrt (1 / 2) ∧
      1 / 2 ≤ eventMass pointMass (fun _ => |(1 / 2 : ℝ) - 1 / 2| ≤ 1 / 4) := by
  obtain ⟨C, hC, h⟩ := exists_otest_estimator_budget
  obtain ⟨k, n, hk, hn, hbound, hsucc⟩ := h (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, k, n, hC, hk, hn, hbound, ?_⟩
  have hacc : (0 : ℝ) ≤ phaseAccuracy (1 / 2) (k : ℝ) (n : ℝ) :=
    phaseAccuracy_nonneg _ _ _ (by positivity) (by positivity)
  have hbad : eventMass pointMass
      (fun (x : Fin 1) => ¬ (|(1 / 2 : ℝ) - 1 / 2| ≤ phaseAccuracy (1 / 2) (k : ℝ) (n : ℝ)))
      ≤ phaseFailure (k : ℝ) := by
    have hzero : ∀ (x : Fin 1),
        ¬ (¬ (|(1 / 2 : ℝ) - 1 / 2| ≤ phaseAccuracy (1 / 2) (k : ℝ) (n : ℝ))) := by
      intro x
      simpa using hacc
    rw [eventMass_false pointMass hzero]
    exact phaseFailure_nonneg hk
  have h := hsucc (Fin 1) pointMass (fun _ => (1 / 2 : ℝ)) hbad
  have hone : eventMass pointMass (fun _ : Fin 1 => |(1 / 2 : ℝ) - 1 / 2| ≤ 1 / 4) = 1 :=
    eventMass_true pointMass (fun _ => by norm_num)
  rw [hone]
  linarith

/-- A fixed scaled budget can be applied to the concrete two-outcome oracle and its
singleton accepted set. -/
theorem twoTwo_otest_scaled_budget :
    ∃ (C : ℝ) (n : ℕ), 0 < C ∧ 0 < n ∧ 2 * (n : ℝ) ≤ C * Real.sqrt 2 ∧
      1 / 2 ≤ eventMass pointMass (fun _ => (1 : ℝ) / (2 ^ 12 * 2) ≤ 1 / 2) := by
  obtain ⟨C, hC, h⟩ := exists_otest_estimator_budget_scaled
  obtain ⟨n, hn, hbudget, hscaled⟩ :=
    h 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmass : eventMass (oracleDist twoTwo (by norm_num)) (· ∈ ({0} : Finset (Fin 2))) =
      1 / 2 := by
    unfold eventMass
    rw [← twoTwo_mass, Fin.sum_univ_two]
    simp
  have hthreshold : (1 : ℝ) ^ 3 * (1 : ℕ) / (2 ^ 11 * (2 : ℕ)) ≤
      eventMass (oracleDist twoTwo (by norm_num)) (· ∈ ({0} : Finset (Fin 2))) := by
    rw [hmass]
    norm_num
  refine ⟨C, n, hC, hn, by simpa using hbudget, ?_⟩
  have htail :
      eventMass pointMass (fun _ => ¬ (|(1 / 2 : ℝ) -
        eventMass (oracleDist twoTwo (by norm_num)) (· ∈ ({0} : Finset (Fin 2)))|
          ≤ phaseAccuracy (eventMass (oracleDist twoTwo (by norm_num))
            (· ∈ ({0} : Finset (Fin 2)))) 2 (n : ℝ))) ≤ phaseFailure 2 := by
    rw [hmass, eventMass_false pointMass]
    · exact phaseFailure_nonneg (k := 2) (by decide)
    · intro x
      have hnonneg := phaseAccuracy_nonneg (1 / 2) 2 (n : ℝ) (by positivity) (by positivity)
      simpa using hnonneg
  simpa using hscaled twoTwo (by norm_num) {0} hthreshold (Fin 1) pointMass (fun _ => 1 / 2) htail

end QatlibTests.DistTesting09AmplitudeRegression
