/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.Postselection.FreshTrials
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.QsvtCore.LinearSystems.ConstructivePseudoinverse

/-!
# Fresh-trial amplification for pseudoinverse preparation

This module bounds repeated postselection failure and compiles fresh preparations into a unitary
program with explicit query counts. `preparedFresh_reliable` transfers a single-trial success
bound to a failure probability of at most one third after `32 * n` trials.

The constructive pseudoinverse results combine a spectral gap, reciprocal approximation, and
postselection to prepare approximate minimum-norm solution states, in the QSVT setting of
[GilyenSuLowWiebe2019].

## Main statements

* `failure_power_32n`: bounds the probability that all trials fail.
* `constructivePseudoinverse_wellFormed_output`: constructs a circuit with a postselection
  success bound and an approximate solution state.
* `constructivePseudoinverse_reliable_fresh`: combines the construction with fresh-trial
  amplification.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix Polynomial
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

/-- For a real p ≤ 1 and a natural k, the product (1 + kp)(1 - p)^k is at most one. -/
theorem failure_power_mul_bound {p : ℝ} (hp1 : p ≤ 1) (k : ℕ) :
    (1 + (k : ℝ) * p) * (1 - p) ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 0 ≤ (1 - p) ^ k := pow_nonneg (sub_nonneg.mpr hp1) _
    have hstep : (1 + ((k : ℝ) + 1) * p) * (1 - p) ≤ 1 + (k : ℝ) * p := by
      have ht := mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity) (sq_nonneg p)
      nlinarith
    calc
      _ = ((1 + ((k : ℝ) + 1) * p) * (1 - p)) * (1 - p) ^ k := by
        rw [Nat.cast_succ, pow_succ]
        ring
      _ ≤ (1 + (k : ℝ) * p) * (1 - p) ^ k := mul_le_mul_of_nonneg_right hstep hpow
      _ ≤ 1 := ih

/-- For p in [0, 1], bounds the failure power (1 - p)^k by 1 / (1 + kp). -/
theorem failure_power_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (1 - p) ^ k ≤ 1 / (1 + (k : ℝ) * p) := by
  have hd : 0 < 1 + (k : ℝ) * p := by positivity
  apply (le_div_iff₀ hd).2
  simpa only [mul_comm] using failure_power_mul_bound hp1 k

/-- If n is positive and p in [0, 1] is at least 1/(16n), then failure in all 32n trials has
probability at most one third. -/
theorem failure_power_32n {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 1 / (16 * (n : ℝ)) ≤ p) :
    (1 - p) ^ (32 * n) ≤ 1 / 3 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul : 2 ≤ ((32 * n : ℕ) : ℝ) * p := by
    calc
      2 = (32 * (n : ℝ)) * (1 / (16 * (n : ℝ))) := by field_simp; ring
      _ ≤ (32 * (n : ℝ)) * p := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by norm_cast
  refine (failure_power_le hp0 hp1 (32 * n)).trans ?_
  apply (div_le_iff₀ (show 0 < 1 + ((32 * n : ℕ) : ℝ) * p by positivity)).2
  nlinarith

/-- For an orthogonal projector and a normalized state, the mass of the all-failed fresh history
is the kth power of the single-trial failure probability. -/
theorem fresh_failure_eq {H : Type*} [Fintype H] [DecidableEq H]
    {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) (k : ℕ) :
    freshHistoryMass P ψ k (allFailed k) = (1 - ProjectiveBranchMass P true ψ) ^ k := by
  have he := projectiveBranchMass_add hP ψ
  rw [measureProb_univ hψ] at he
  have hf : ProjectiveBranchMass P false ψ = 1 - ProjectiveBranchMass P true ψ := by linarith
  rw [freshHistoryMass_allFailed, hf]

/-- If the single-trial success mass is at least 1/(16n) for positive n, the fresh measurement
law assigns mass at most one third to failure in all 32n trials. -/
theorem freshMeasurementLaw_failure_le {H : Type*} [Fintype H] [DecidableEq H]
    {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) {n : ℕ} (hn : 0 < n)
    (hp : 1 / (16 * (n : ℝ)) ≤ ProjectiveBranchMass P true ψ) :
    freshMeasurementLaw hP hψ (32 * n) (allFailed (32 * n)) ≤ ENNReal.ofReal (1 / 3) := by
  rw [freshMeasurementLaw_apply, fresh_failure_eq hP hψ]
  apply ENNReal.ofReal_le_ofReal
  have he := projectiveBranchMass_add hP ψ
  rw [measureProb_univ hψ] at he
  exact failure_power_32n hn (projectiveBranchMass_nonneg _ _ _) (by
    linarith [projectiveBranchMass_nonneg P false ψ]) hp

section GenericBridge
variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- Given a well-formed circuit, unitary state preparation, and single-trial success probability
at least 1/(16n), constructs a unitary 32n-trial program with failure mass at most one third
and explicit data and preparation query counts. Its outcome states are the fresh-trial
states, and the first successful trial selects the encoded postselection output. -/
theorem preparedFresh_reliable {U B : Matrix H H ℂ} {cs : List (AdjointStep H)}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (hcs : WellFormedAdjointCircuit cs) (zero : H)
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} (hL : IsIsometry L) (hR : IsIsometry R)
    {b : QState I} (hb : Normalized b)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ b)
    {n : ℕ} (hn : 0 < n)
    (hp : 1 / (16 * (n : ℝ)) ≤ postselectionProbability (evaluate U cs) L R b)
    {φ : QState O} (hφ : postselectionOutput (evaluate U cs) L R b = some φ) :
    let k := 32 * n
    let program := compileFresh (preparedTrial cs) k
    let finalState := ApplyGate (evaluateFresh U B program) (Ket (freshZero zero k))
    let ψ := ApplyGate (evaluate U cs) (R *ᵥ b)
    let P := rangeProjector L
    evaluateFresh U B program ∈ Matrix.unitaryGroup (FreshRegister H k) ℂ ∧
    freshDataQueries program = k * adjointQueryCount cs ∧
    freshInputQueries program = k ∧
    ProjectiveHistoryMass (freshProjectiveHistory P k (allFailed k)) finalState ≤ 1 / 3 ∧
    (∀ os : FreshOutcomes k,
      ProjectiveHistoryState (freshProjectiveHistory P k os) finalState = freshOutcomeState P ψ k os) ∧
    (∀ os : FreshOutcomes k, ∀ i : Fin k, firstFreshSuccess k os = some i →
      selectedFreshState P ψ k os = some (L *ᵥ φ)) := by
  (try dsimp only)
  have hw := hcs.evaluate_unitary hU
  have hψ :=
      normalized_applyGate hw
      (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.normalized_mulVec hR hb)
  have hP := rangeProjector_isOrthogonalProjector hL
  have hvalid := preparedTrial_valid hcs
  have hcounts := compileFresh_counts (preparedTrial cs) (32 * n)
  have hsingle := preparedTrial_counts cs
  refine ⟨evaluateFresh_compile_unitary hU hB hvalid _, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hsingle.1] using hcounts.1
  · simpa only [hsingle.2.1, mul_one] using hcounts.2.1
  · rw [preparedFresh_history_mass, preparedTrial_apply cs zero R b hprepare, fresh_failure_eq hP hψ]
    have hprob := postselectionProbability_mem_Icc hw hL hR hb
    exact failure_power_32n hn hprob.1 hprob.2 hp
  · intro os
    rw [evaluateFresh_apply_zero, preparedTrial_apply cs zero R b hprepare, freshHistory_state]
  · intro os i hi
    apply selectedFreshState_eq (i := i) _ hi
    rw [projectiveConditionalState_eq_postselection hL, hφ]
    rfl

end GenericBridge

section Constructive
variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- For a projected unitary encoding with a positive lower bound on nonzero singular values,
constructs a well-formed circuit encoding the scaled pseudoinverse within `inverseScale n *
η / 2`. The circuit uses `2 * n - 1` oracle queries and `2 * n` gates, with reciprocal error
at most `η / 2`. -/
theorem constructivePseudoinverse_wellFormed_encoding
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {δ η : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → δ ≤ matrixSingularValues A i)
    (hη : 0 < η) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × H))),
      0 < n ∧ reciprocalError (inverseEffectiveGap δ) n ≤ η / 2 ∧
      WellFormedAdjointCircuit cs ∧
      adjointQueryCount cs = 2 * n - 1 ∧ adjointGateCount cs = 2 * n ∧
      BlockEncoding ((inverseScale n : ℂ) • matrixPseudoinverse A)
        (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L)
        1 (inverseScale n * η / 2) := by
  obtain ⟨n, hn, hcut⟩ := exists_inverse_cutoff hδ hη
  obtain ⟨base, zs, hb, hzs, hlen, hre⟩ := exists_inverse_phases hn
  have hc := inverseScale_pos hn
  have hd : 0 < inverseEffectiveGap δ := lt_min hδ (by norm_num)
  have hodd : zs.length % 2 = 1 := by rw [hlen]; omega
  have happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(((responseP base zs).eval (matrixSingularValues A i : ℂ)).re : ℂ) -
        (inverseScale n : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤ inverseScale n * η / 2 := by
    intro i hi
    have hx : matrixSingularValues A i ∈ Set.Icc (inverseEffectiveGap δ) 1 :=
      ⟨(min_le_left δ 1).trans (hgap i hi), (encoded_singularValues_mem_unitInterval h i).2⟩
    have hs := scaledReciprocalPolynomial_error_le n (inverseScale n) hd hx
    rw [abs_of_pos hc] at hs
    have he : (((responseP base zs).eval (matrixSingularValues A i : ℂ)).re : ℂ) =
        (C (inverseScale n : ℂ) * complexReciprocalPolynomial n).eval (matrixSingularValues A i : ℂ) := by
      rw [hre]
      simp [complexReciprocalPolynomial_eval_real]
    rw [he]
    calc
      _ ≤ inverseScale n * reciprocalError (inverseEffectiveGap δ) n := hs
      _ ≤ inverseScale n * (η / 2) := mul_le_mul_of_nonneg_left hcut hc.le
      _ = inverseScale n * η / 2 := by ring
  have hW := realPart_pseudoinverse_approximation h hb zs hzs hodd
    (inverseScale n) (show 0 ≤ inverseScale n * η / 2 by positivity) happrox
  let cs := adjointCircuit (compileRealPartQSVT (rangeProjector R) (rangeProjector L) base zs)
  refine ⟨n, cs, hn, hcut, ?_, ?_, ?_, ?_⟩
  · exact compileRealPartQSVT_wellFormed_adjoint
      (rangeProjector_isOrthogonalProjector h.right_isometry)
      (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs
  · dsimp only [cs]
    rw [adjointQueryCount_adjointCircuit, (counts_compileRealPartQSVT _ _ _ _).1, hlen]
  · dsimp only [cs]
    rw [adjointGateCount_adjointCircuit, (counts_compileRealPartQSVT _ _ _ _).2, hlen]
    omega
  · dsimp only [cs]
    rw [evaluate_adjointCircuit, evaluate_compileRealPartQSVT]
    exact hW

/-- For a projected unitary encoding with a positive singular-value gap and 0 < η ≤ 1,
constructs a well-formed circuit using `2 * n - 1` queries and `2 * n` gates. Every
normalized input in the range has postselection probability at least 1/(16n) and a
postselected state satisfying `IsMinimumNormSolutionState` with tolerance η. -/
theorem constructivePseudoinverse_wellFormed_output
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {δ η : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → δ ≤ matrixSingularValues A i)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × H))),
      0 < n ∧ WellFormedAdjointCircuit cs ∧ adjointQueryCount cs = 2 * n - 1 ∧
      adjointGateCount cs = 2 * n ∧
      ∀ b : QState O, Normalized b → (∃ z : QState I, A *ᵥ z = b) →
        1 / (16 * (n : ℝ)) ≤ postselectionProbability
          (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L) b ∧
        ∃ φ : QState I, postselectionOutput
          (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L) b = some φ ∧
          IsMinimumNormSolutionState A b φ η := by
  obtain ⟨n, cs, hn, _, hcs, hqueries, hgates, hW⟩ :=
    constructivePseudoinverse_wellFormed_encoding h hδ hgap hη
  refine ⟨n, cs, hn, hcs, hqueries, hgates, ?_⟩
  intro b hb hrange
  have hc := inverseScale_pos hn
  have hehalf : inverseScale n * η / 2 ≤ inverseScale n / 2 := by nlinarith
  have hsmall : inverseScale n * η / 2 < inverseScale n := by linarith
  obtain ⟨hlower, _, φ, hout, hspec⟩ := scaledPseudoinverse_postselection
    (projectedEncoding_average_lift h) hW hb hrange hsmall
  refine ⟨?_, φ, hout, ?_⟩
  · calc
      1 / (16 * (n : ℝ)) = inverseScale n ^ 2 / 4 := (inverseScale_sq_div_four hn).symm
      _ = (inverseScale n / 2) ^ 2 := by ring
      _ ≤ (inverseScale n - inverseScale n * η / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ _ := hlower
  · have he : 2 * (inverseScale n * η / 2) / inverseScale n = η := by field_simp
    simpa only [he] using hspec

/-- Under a positive singular-value gap and 0 < η ≤ 1, constructs a pseudoinverse circuit whose
32n fresh preparations have failure mass at most one third. The resulting unitary program
has explicit query counts and selects an encoded approximate minimum-norm solution state at
the first success. -/
theorem constructivePseudoinverse_reliable_fresh
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {δ η : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → δ ≤ matrixSingularValues A i)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × H))),
      0 < n ∧ WellFormedAdjointCircuit cs ∧ adjointQueryCount cs = 2 * n - 1 ∧
      ∀ b : QState O, Normalized b → (∃ z : QState I, A *ᵥ z = b) →
      ∃ φ : QState I, IsMinimumNormSolutionState A b φ η ∧
      ∀ (zero : Bool × H) (B : Matrix (Bool × H) (Bool × H) ℂ),
        B ∈ Matrix.unitaryGroup (Bool × H) ℂ →
        ApplyGate B (Ket zero) = averageFrame L *ᵥ b →
        let k := 32 * n
        let program := compileFresh (preparedTrial cs) k
        let finalState :=
            ApplyGate (evaluateFresh (parallelOracle U) B program) (Ket (freshZero zero k))
        let ψ := ApplyGate (evaluate (parallelOracle U) cs) (averageFrame L *ᵥ b)
        let P := rangeProjector (averageFrame R)
        evaluateFresh (parallelOracle U) B program ∈ Matrix.unitaryGroup (FreshRegister (Bool × H) k) ℂ ∧
        freshDataQueries program = k * (2 * n - 1) ∧ freshInputQueries program = k ∧
        ProjectiveHistoryMass (freshProjectiveHistory P k (allFailed k)) finalState ≤ 1 / 3 ∧
        (∀ os : FreshOutcomes k,
          ProjectiveHistoryState (freshProjectiveHistory P k os) finalState = freshOutcomeState P ψ k os) ∧
        (∀ os : FreshOutcomes k, ∀ i : Fin k, firstFreshSuccess k os = some i →
          selectedFreshState P ψ k os = some (averageFrame R *ᵥ φ)) := by
  obtain ⟨n, cs, hn, hcs, hq, _, hout⟩ :=
    constructivePseudoinverse_wellFormed_output h hδ hgap hη hη1
  refine ⟨n, cs, hn, hcs, hq, ?_⟩
  intro b hb hrange
  obtain ⟨hp, φ, hφ, hspec⟩ := hout b hb hrange
  refine ⟨φ, hspec, ?_⟩
  intro zero B hB hprepare
  have he := preparedFresh_reliable (parallelOracle_unitary h.unitary) hB hcs zero
    (averageFrame_isIsometry h.right_isometry) (averageFrame_isIsometry h.left_isometry)
    hb hprepare hn hp hφ
  simpa only [hq] using he

end Constructive
end Qatlib.Concepts.QsvtCore.LinearSystems
