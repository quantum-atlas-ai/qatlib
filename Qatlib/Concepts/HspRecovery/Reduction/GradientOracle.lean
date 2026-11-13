/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.GradientOracleDefs
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Concepts.QspSimulation.Achievability.ComputedSignalConsumers

/-!
# From probability oracles to phase oracles

This module compresses an oracle-conjugated reflection to a diagonal operator with entries `1 -
2 * probabilityMass`. Under unitarity and preservation of input labels on the clean frame, it
constructs circuits approximating the phase `exp (I * probabilityMass)`.

The simulation and phase results include explicit query and gate counts and norm error bounds.
They use the projected encoding and signal processing framework of [GilyenSuLowWiebe2019].

## Main statements

* `probability_reflection_encoding`: constructs the projected unitary encoding.
* `probability_simulation_actual`: verifies the simulation word and its error bound.
* `clean_probability_phase_actual`: gives a clean-frame phase approximation with exact resource
  counts.
* `clean_probability_phase_tolerance`: chooses precision from a positive rational tolerance.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QspSimulation.JacobiAnger

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped BigOperators

/-- The clean frame fixing the ancillary register at `a₀` is an isometry. -/
theorem cleanFrame_isometry {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) : IsIsometry (cleanFrame (X := X) a₀) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cleanFrame]
  rw [Finset.sum_eq_single (x,a₀)]
  · simp [Matrix.one_apply]
  · intro xa _ hxa
    simp [hxa]
  · simp

/-- Multiplying an oracle matrix by the clean frame selects its columns indexed by `(x, a₀)`. -/
theorem oracle_cleanFrame {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ) (a₀ : A)
    (xa : X × A) (x : X) : (U * cleanFrame (X := X) a₀) xa x = U xa (x,a₀) := by
  simp [cleanFrame, Matrix.mul_apply]

/-- The diagonal reflection marking good ancillary values is self-adjoint. -/
theorem goodReflection_self_adjoint {X A : Type*} [DecidableEq X] [DecidableEq A]
    (good : Finset A) : (goodReflection (X := X) good)ᴴ = goodReflection (X := X) good := by
  simp only [goodReflection, Matrix.diagonal_conjTranspose]
  congr 1
  funext xa
  by_cases h : xa.2 ∈ good <;> simp [h]

/-- The diagonal reflection marking good ancillary values is unitary. -/
theorem goodReflection_unitary {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A) :
    goodReflection (X := X) good ∈ Matrix.unitaryGroup (X × A) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    goodReflection_self_adjoint, goodReflection, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext xa
  split_ifs <;> norm_num

/-- Evaluating the reflection word gives `Uᴴ * goodReflection good * U`. -/
theorem evaluate_reflectionWord {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ) (good : Finset A) :
    evaluate U (reflectionWord good) = Uᴴ * goodReflection (X := X) good * U := by
  simp [reflectionWord, evaluate, instructionMatrix, Matrix.mul_assoc]

/-- The reflection word is well formed and uses two adjoint queries and one gate. -/
theorem reflection_word_receipt {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A) :
    WellFormedAdjointCircuit (reflectionWord (X := X) good) ∧
      adjointQueryCount (reflectionWord (X := X) good) = 2 ∧
      adjointGateCount (reflectionWord (X := X) good) = 1 := by
  refine ⟨?_, rfl, rfl⟩
  simp [WellFormedAdjointCircuit, reflectionWord, goodReflection_unitary]

/-- The probability mass equals the Born probability of outcomes retaining label `x` with
ancillary value in `good`. -/
theorem probabilityMass_born {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (a₀ : A) (good : Finset A) (x : X) :
    probabilityMass U a₀ good x =
      MeasureProb (ApplyGate U (Ket (x,a₀)))
        (Finset.univ.filter (fun xa => xa.1 = x ∧ xa.2 ∈ good)) := by
  simp [probabilityMass, MeasureProb, BornProb, ApplyGate, Matrix.mulVec,
    dotProduct, Qatlib.Foundations.PureStateMath.Ket, Finset.sum_filter, Fintype.sum_prod_type,
    ite_and, Complex.normSq_eq_norm_sq]

/-- For a unitary oracle, every probability mass lies between zero and one. -/
theorem probabilityMass_bounds {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A) (x : X) :
    0 ≤ probabilityMass U a₀ good x ∧ probabilityMass U a₀ good x ≤ 1 := by
  rw [probabilityMass_born]
  exact ⟨measureProb_nonneg _ _, measureProb_le_one
    (normalized_applyGate hU (normalized_ket _)) _⟩

/-- For a unitary oracle preserving clean input labels, compression of the conjugated reflection
is diagonal with entries `1 - 2 * probabilityMass`. -/
theorem compressed_probability_reflection {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A)
    (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) :
    compress (cleanFrame (X := X) a₀) (evaluate U (reflectionWord good)) (cleanFrame (X := X) a₀) =
      Matrix.diagonal (fun x => (1 - 2 * probabilityMass U a₀ good x : ℝ) : X → ℂ) := by
  have hmass (x : X) : ∑ a : A, Complex.normSq (U (x,a) (x,a₀)) = 1 := by
    have h := congrArg (fun M : Matrix (X × A) (X × A) ℂ => M (x,a₀) (x,a₀))
      (Matrix.mem_unitaryGroup_iff'.mp hU)
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type] at h
    rw [Finset.sum_eq_single x (by
      intro z _ hz
      apply Finset.sum_eq_zero
      intro a _
      rw [hlabel z x a hz]
      simp) (by simp)] at h
    have hcs (z : ℂ) : star z * z = (Complex.normSq z : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    simp only [hcs] at h
    have hr := congrArg Complex.re h
    simpa using! hr
  rw [compress, evaluate_reflectionWord]
  have hprod : (cleanFrame (X := X) a₀)ᴴ * (Uᴴ * goodReflection (X := X) good * U) * cleanFrame (X := X) a₀ =
      (U * cleanFrame (X := X) a₀)ᴴ * goodReflection (X := X) good * (U * cleanFrame (X := X) a₀) := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hprod]
  ext x y
  change (((U * cleanFrame (X := X) a₀)ᴴ * Matrix.diagonal
    (fun xa : X × A => if xa.2 ∈ good then (-1 : ℂ) else 1)) *
      (U * cleanFrame (X := X) a₀)) x y = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, oracle_cleanFrame,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  swap
  · intro z _ hz
    apply Finset.sum_eq_zero
    intro a _
    rw [hlabel z x a hz]
    simp
  swap
  · simp
  by_cases hxy : x = y
  · subst y
    have hterm (a : A) :
        star (U (x,a) (x,a₀)) * (if a ∈ good then (-1 : ℂ) else 1) * U (x,a) (x,a₀) =
          (Complex.normSq (U (x,a) (x,a₀)) : ℂ) -
            2 * (if a ∈ good then (Complex.normSq (U (x,a) (x,a₀)) : ℂ) else 0) := by
      have hc : star (U (x,a) (x,a₀)) * U (x,a) (x,a₀) =
          (Complex.normSq (U (x,a) (x,a₀)) : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      split_ifs
      · rw [mul_neg_one, neg_mul, hc]
        ring
      · rw [mul_one, hc]
        ring
    simp_rw [hterm]
    simp only [Finset.sum_sub_distrib, ← Complex.ofReal_sum, hmass, Complex.ofReal_one,
      ← Finset.mul_sum, ← Finset.sum_filter, probabilityMass, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    simp
  · simp [hlabel x y _ hxy, hxy]

/-- A unitary oracle preserving clean input labels yields a projected unitary encoding of the
diagonal probability reflection. -/
theorem probability_reflection_encoding {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A)
    (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) :
    ProjectedUnitaryEncoding
      (Matrix.diagonal (fun x => (1 - 2 * probabilityMass U a₀ good x : ℝ) : X → ℂ))
      (evaluate U (reflectionWord good)) (cleanFrame a₀) (cleanFrame a₀) :=
  ⟨(reflection_word_receipt good).1.evaluate_unitary hU,
    cleanFrame_isometry a₀, cleanFrame_isometry a₀,
    compressed_probability_reflection U hU a₀ good hlabel⟩

/-- Expanding each query into a reflection word doubles the adjoint query count and adds one
gate per original query. -/
theorem expand_reflection_receipt {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A]
    (good : Finset A) (word : List (AdjointStep (X × A))) :
    adjointQueryCount (expandReflection good word) = 2 * adjointQueryCount word ∧
      adjointGateCount (expandReflection good word) =
        adjointGateCount word + adjointQueryCount word := by
  have h := substitute_adjoint_evaluate_cost (1 : Matrix (X × A) (X × A) ℂ)
    (reflectionWord good) word
  exact ⟨by simpa [expandReflection, reflectionWord, adjointQueryCount, mul_comm] using! h.2.1,
    by simpa [expandReflection, reflectionWord, adjointGateCount] using! h.2.2.1⟩

/-- Reflection substitution evaluates as the original word with oracle `Uᴴ * goodReflection good
* U`, and preserves well-formedness. -/
theorem expand_reflection_actual {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ) (good : Finset A)
    (word : List (AdjointStep (X × A))) (hw : WellFormedAdjointCircuit word) :
    evaluate U (expandReflection good word) = evaluate (Uᴴ * goodReflection (X := X) good * U) word ∧
      WellFormedAdjointCircuit (expandReflection good word) := by
  have h := substitute_adjoint_evaluate_cost U (reflectionWord good) word
  exact ⟨by simpa only [expandReflection, evaluate_reflectionWord] using! h.1,
    h.2.2.2 (reflection_word_receipt good).1 hw⟩

/-- Conjugating a controlled matrix by parallel copies of a unitary gives the controlled
conjugate matrix. -/
theorem controlled_sandwich {H : Type*} [Fintype H] [DecidableEq H]
    (U R : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    (parallelOracle (J := Bool) U)ᴴ * controlOracle R * parallelOracle (J := Bool) U =
      controlOracle (Uᴴ * R * U) := by
  rw [parallelOracle_adjoint, parallelOracle, parallelOracle, controlOracle,
    parallel_select_mul, parallel_select_mul, controlOracle]
  congr 1
  funext b
  cases b
  · simpa only [Bool.false_eq_true, if_false, Matrix.mul_one] using!
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  · simp

/-- The controlled reflection word evaluates to the controlled conjugated reflection and is well
formed with two queries and one gate. -/
theorem controlled_reflection_actual {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (good : Finset A) :
    evaluate (parallelOracle (J := Bool) U) (controlledReflectionWord good) =
        controlOracle (evaluate U (reflectionWord good)) ∧
      WellFormedAdjointCircuit (controlledReflectionWord (X := X) good) ∧
      adjointQueryCount (controlledReflectionWord (X := X) good) = 2 ∧
      adjointGateCount (controlledReflectionWord (X := X) good) = 1 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [controlledReflectionWord, evaluate, instructionMatrix, Matrix.mul_one,
      evaluate_reflectionWord]
    simpa only [Matrix.mul_assoc] using! controlled_sandwich U (goodReflection good) hU
  · simp [controlledReflectionWord, WellFormedAdjointCircuit,
      controlOracle_unitary, goodReflection_unitary]

/-- The probability simulation body evaluates to the controlled parallel reflection extended by
an identity register. -/
theorem probability_simulation_body_actual {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (good : Finset A) :
    evaluate (probabilityPrimitiveOracle U) (probabilitySimulationBody good) =
      TensorGate 1 (controlOracle (parallelOracle (J := Bool)
        (evaluate U (reflectionWord good)))) := by
  have hp : (parallelOracle (J := Bool) U)ᴴ *
      parallelOracle (J := Bool) (goodReflection (X := X) good) * parallelOracle (J := Bool) U =
      parallelOracle (J := Bool) (Uᴴ * goodReflection good * U) := by
    simp only [parallelOracle_eq_kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  simp only [probabilityPrimitiveOracle, probabilitySimulationBody, evaluate,
    instructionMatrix, Matrix.mul_one, tensorGate_conjTranspose, Matrix.conjTranspose_one]
  rw [tensorGate_mul, tensorGate_mul, Matrix.one_mul, Matrix.one_mul,
    ← Matrix.mul_assoc, controlled_sandwich _ _ (parallelOracle_unitary hU), hp,
    evaluate_reflectionWord]

/-- For a unitary oracle preserving clean labels, the simulation word is well formed with the
stated cutoff-dependent counts and approximates evolution of the diagonal probability
reflection with relative norm error at most `(1/2)^k`. -/
theorem probability_simulation_actual {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A)
    (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0)
    (t : ℚ) (k : ℕ) :
    let n := computedSignalCutoff t k
    let r := computedSignalSegments t
    let word := probabilitySimulationWord (X := X) a₀ good t k
    let F := scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀))
    let B := Matrix.diagonal (fun x => (1 - 2 * probabilityMass U a₀ good x : ℝ) : X → ℂ)
    WellFormedAdjointCircuit word ∧
      adjointQueryCount word = 2 * (r * (27 * (4*n+1))) ∧
      adjointGateCount word = r * (27*(4*n+6)+79) + r * (27*(4*n+1)) ∧
      ∀ ψ : QState X,
        ‖toEuclidean_fromVec (evaluate (probabilityPrimitiveOracle U) word *ᵥ (F *ᵥ ψ) -
          F *ᵥ (hamiltonianEvolution B (t : ℝ) *ᵥ ψ))‖ ≤
            (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖ := by
  (try dsimp only)
  let F := cleanFrame (X := X) a₀
  let B := Matrix.diagonal (fun x => (1 - 2 * probabilityMass U a₀ good x : ℝ) : X → ℂ)
  have hB : B.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro x
    exact RCLike.conj_ofReal _
  have henc := probability_reflection_encoding U hU a₀ good hlabel
  obtain ⟨hw,hq,hg,herr⟩ := computed_signal_full_segmented_program_and_cost
    (X × A) X B (evaluate U (reflectionWord good)) F t k hB henc
  have hs := substitute_adjoint_evaluate_cost (probabilityPrimitiveOracle U)
    (probabilitySimulationBody good) (computedSignalWord F t k)
  have hb : WellFormedAdjointCircuit (probabilitySimulationBody (X := X) good) := by
    have hm := tensorGate_unitary (one_mem (Matrix.unitaryGroup Bool ℂ))
      (controlOracle_unitary (parallelOracle_unitary (J := Bool)
        (goodReflection_unitary (X := X) good)))
    simpa [probabilitySimulationBody, WellFormedAdjointCircuit] using! hm
  refine ⟨hs.2.2.2 hb hw, ?_, ?_, ?_⟩
  · simpa [probabilitySimulationWord, probabilitySimulationBody, adjointQueryCount,
      hq, mul_comm] using! hs.2.1
  · simpa [probabilitySimulationWord, probabilitySimulationBody, adjointGateCount,
      hq, hg] using! hs.2.2.1
  · intro ψ
    rw [probabilitySimulationWord, hs.1, probability_simulation_body_actual U hU good]
    exact herr ψ

/-- At time one half, multiplying the evolution of the diagonal operator `1 - 2 * p` by `exp (I
/ 2)` gives the diagonal phases `exp (I * p)`. -/
theorem probability_half_time_phase {X : Type*} [Fintype X] [DecidableEq X] (p : X → ℝ) :
    Complex.exp (Complex.I/2) •
      hamiltonianEvolution (Matrix.diagonal (fun x => ((1 - 2*p x : ℝ) : ℂ))) (1/2) =
        Matrix.diagonal (fun x => Complex.exp (Complex.I * (p x : ℂ))) := by
  unfold hamiltonianEvolution
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def, ← Matrix.diagonal_smul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Complex.exp_eq_exp_ℂ, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The scalar phase correction `exp (I / 2)` has norm one. -/
private theorem phaseCorrection_norm : ‖Complex.exp (Complex.I/2)‖ = 1 := by
  rw [Complex.norm_exp]
  norm_num

/-- The scalar phase correction times the identity matrix is unitary. -/
private theorem phaseCorrection_unitary {H : Type*} [Fintype H] [DecidableEq H] :
    Complex.exp (Complex.I/2) • (1 : Matrix H H ℂ) ∈ Matrix.unitaryGroup H ℂ := by
  have hc : star (Complex.exp (Complex.I/2)) * Complex.exp (Complex.I/2) = 1 := by
    change (starRingEnd ℂ) _ * _ = _
    rw [Complex.conj_mul', phaseCorrection_norm]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [mul_comm, hc, one_smul]

/-- Under the oracle hypotheses, the probability phase word is well formed with explicit
cutoff-dependent counts and approximates the diagonal probability phase on the signal frame
with relative norm error at most `(1/2)^k`. -/
theorem probability_phase_clean_frame_bound {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A)
    (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) :
    let n := computedSignalCutoff (1/2) k
    let word := probabilityPhaseWord (X := X) a₀ good k
    let F := scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀))
    let D := Matrix.diagonal (fun x => Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ)))
    WellFormedAdjointCircuit word ∧
      adjointQueryCount word = 54 * (4*n+1) ∧
      adjointGateCount word = 1 + (27*(4*n+6)+79) + 27*(4*n+1) ∧
      ∀ ψ : QState X,
        ‖toEuclidean_fromVec (evaluate (probabilityPrimitiveOracle U) word *ᵥ (F *ᵥ ψ) -
          F *ᵥ (D *ᵥ ψ))‖ ≤ (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖ := by
  (try dsimp only)
  obtain ⟨hw,hq,hg,herr⟩ := probability_simulation_actual U hU a₀ good hlabel (1/2) k
  have hr : computedSignalSegments (1/2) = 1 := by norm_num [computedSignalSegments]
  rw [hr] at hq hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (WellFormedAdjointCircuit.gate_cons_iff _ _).mpr ⟨phaseCorrection_unitary,hw⟩
  · simp only [probabilityPhaseWord, adjointQueryCount, hq]
    ring
  · simp only [probabilityPhaseWord, adjointGateCount, hg]
    omega
  · intro ψ
    let c : ℂ := Complex.exp (Complex.I/2)
    let F := scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀))
    let B := Matrix.diagonal (fun x => ((1 - 2*probabilityMass U a₀ good x : ℝ) : ℂ))
    have he : evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord a₀ good k) *ᵥ (F *ᵥ ψ) -
        F *ᵥ (Matrix.diagonal (fun x => Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))) *ᵥ ψ) =
        c • (evaluate (probabilityPrimitiveOracle U) (probabilitySimulationWord a₀ good (1/2) k) *ᵥ
          (F *ᵥ ψ) - F *ᵥ (hamiltonianEvolution B (1/2) *ᵥ ψ)) := by
      rw [← probability_half_time_phase (probabilityMass U a₀ good)]
      simp only [probabilityPhaseWord, evaluate, instructionMatrix, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_sub]
      rfl
    have hwrap (v : QState (Bool × (Bool × (Bool × (X × A))))) :
        toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := rfl
    rw [he, hwrap, norm_smul]
    simp only [c, phaseCorrection_norm, one_mul]
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using! herr ψ

/-- Under the oracle hypotheses, the probability phase word uses `6912 * k + 110646` queries and
`6912 * k + 110861` gates. -/
theorem probability_phase_linear_resources {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A)
    (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) :
    adjointQueryCount (probabilityPhaseWord (X := X) a₀ good k) = 6912*k+110646 ∧
      adjointGateCount (probabilityPhaseWord (X := X) a₀ good k) = 6912*k+110861 := by
  have h := probability_phase_clean_frame_bound U hU a₀ good hlabel k
  have hq := h.2.1
  have hg := h.2.2.1
  norm_num [computedSignalCutoff, computedSignalSegments] at hq hg
  omega

/-- The Boolean average preparation matrix is unitary. -/
theorem averagePreparation_unitary : averagePreparation ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
      Matrix.one_apply, averagePreparation, realPartAmplitude, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im]
  all_goals norm_num [map_ofNat]

/-- Applying the average preparation gate to the flag of `scaleEightFrame F` gives `averageFrame
F`. -/
theorem averagePreparation_frame {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) :
    TensorGate averagePreparation (1 : Matrix H H ℂ) * scaleEightFrame F = averageFrame F := by
  ext ⟨b,h⟩ i
  simp [TensorGate, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, scaleEightFrame, averageFrame, prepareLift, averagePreparation]

/-- Lifting an operator by an identity flag commutes with its action on a scaled frame. -/
theorem flagFrame_lift {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) :
    TensorGate (1 : Matrix Bool Bool ℂ) U * scaleEightFrame F = scaleEightFrame (U*F) := by
  ext ⟨b,h⟩ i
  cases b <;> simp [scaleEightFrame, Matrix.mul_apply, tensorGate_apply,
    Fintype.sum_prod_type, Matrix.one_apply]

/-- The signal preparation word maps the zero signal frame to the scaled Hamiltonian frame. -/
theorem signalPreparation_frame {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A)
    (O : Matrix (Bool × (Bool × (Bool × (X × A))))
      (Bool × (Bool × (Bool × (X × A)))) ℂ) :
    evaluate O (signalPreparationWord (X × A)) * zeroSignalFrame (X := X) a₀ =
      scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀)) := by
  simp only [signalPreparationWord, evaluate, instructionMatrix, Matrix.mul_one,
    zeroSignalFrame, Matrix.mul_assoc, flagFrame_lift, averagePreparation_frame]
  rfl

/-- The signal preparation word is well formed and uses zero queries and two gates. -/
theorem signalPreparation_receipt (H : Type) [Fintype H] [DecidableEq H] :
    WellFormedAdjointCircuit (signalPreparationWord H) ∧
      adjointQueryCount (signalPreparationWord H) = 0 ∧
      adjointGateCount (signalPreparationWord H) = 2 := by
  refine ⟨?_,rfl,rfl⟩
  have ha := tensorGate_unitary averagePreparation_unitary (one_mem (Matrix.unitaryGroup H ℂ))
  have hb :=
      tensorGate_unitary averagePreparation_unitary (one_mem (Matrix.unitaryGroup (Bool × H) ℂ))
  simp only [signalPreparationWord, WellFormedAdjointCircuit.gate_cons_iff,
    WellFormedAdjointCircuit.nil, and_true]
  exact ⟨tensorGate_unitary (one_mem _) hb,
    tensorGate_unitary (one_mem _) (tensorGate_unitary (one_mem _) ha)⟩

/-- Under the oracle hypotheses, the clean probability phase word is well formed, uses `6912 * k
+ 110646` queries and `6912 * k + 110865` gates, and approximates the diagonal probability
phase on the zero signal frame with relative norm error at most `(1/2)^k`. -/
theorem clean_probability_phase_actual {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A)
    (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) :
    let word := cleanProbabilityPhaseWord (X := X) a₀ good k
    let Z := zeroSignalFrame (X := X) a₀
    let D := Matrix.diagonal (fun x => Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ)))
    WellFormedAdjointCircuit word ∧
      adjointQueryCount word = 6912*k+110646 ∧
      adjointGateCount word = 6912*k+110865 ∧
      ∀ ψ : QState X,
        ‖toEuclidean_fromVec (evaluate (probabilityPrimitiveOracle U) word *ᵥ (Z *ᵥ ψ) -
          Z *ᵥ (D *ᵥ ψ))‖ ≤ (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖ := by
  (try dsimp only)
  obtain ⟨hw,_,_,herr⟩ := probability_phase_clean_frame_bound U hU a₀ good hlabel k
  obtain ⟨hq,hg⟩ := probability_phase_linear_resources U hU a₀ good hlabel k
  obtain ⟨hp,hpq,hpg⟩ := signalPreparation_receipt (X × A)
  refine ⟨hp.adjointCircuit.append (hw.append hp), ?_, ?_, ?_⟩
  · simp only [cleanProbabilityPhaseWord, adjointQueryCount_append,
      adjointQueryCount_adjointCircuit, hpq, hq]
    omega
  · simp only [cleanProbabilityPhaseWord, adjointGateCount_append,
      adjointGateCount_adjointCircuit, hpg, hg]
    omega
  · intro ψ
    let O := probabilityPrimitiveOracle U
    let P := evaluate O (signalPreparationWord (X × A))
    let Z := zeroSignalFrame (X := X) a₀
    let F := scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀))
    let D := Matrix.diagonal (fun x => Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ)))
    have hO : O ∈ Matrix.unitaryGroup _ ℂ :=
      tensorGate_unitary (one_mem _) (parallelOracle_unitary (parallelOracle_unitary hU))
    have hP : P ∈ Matrix.unitaryGroup _ ℂ := hp.evaluate_unitary hO
    have hPP : Pᴴ * P = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hP
    have hframe : P * Z = F := signalPreparation_frame a₀ O
    have hundo : Pᴴ * F = Z := by
      rw [← hframe, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
    have hs (v : QState X) : P *ᵥ (Z *ᵥ v) = F *ᵥ v := by
      rw [Matrix.mulVec_mulVec, hframe]
    have hu (v : QState X) : Pᴴ *ᵥ (F *ᵥ v) = Z *ᵥ v := by
      rw [Matrix.mulVec_mulVec, hundo]
    have heval : evaluate O (cleanProbabilityPhaseWord a₀ good k) =
        Pᴴ * evaluate O (probabilityPhaseWord a₀ good k) * P := by
      simp only [cleanProbabilityPhaseWord, evaluate_append, evaluate_adjointCircuit,
        Matrix.mul_assoc]
      rfl
    have he : evaluate O (cleanProbabilityPhaseWord a₀ good k) *ᵥ (Z *ᵥ ψ) - Z *ᵥ (D *ᵥ ψ) =
        Pᴴ *ᵥ (evaluate O (probabilityPhaseWord a₀ good k) *ᵥ (F *ᵥ ψ) - F *ᵥ (D *ᵥ ψ)) := by
      rw [heval, Matrix.mulVec_sub]
      simp only [← Matrix.mulVec_mulVec, hs, hu]
    rw [he,
        computed_signal_unitary_vector_norm
        (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hP)]
    exact herr ψ

/-- For positive rational `ε`, the chosen phase precision ensures `(1/2)^(phasePrecision ε) ≤
ε`. -/
theorem phasePrecision_budget (ε : ℚ) (hε : 0 < ε) :
    (1/2 : ℝ)^phasePrecision ε ≤ (ε : ℝ) := by
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hceilQ : ε⁻¹ ≤ (max 1 ⌈ε⁻¹⌉₊ : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈ε⁻¹⌉₊)
  have hceilR : (ε : ℝ)⁻¹ ≤ (max 1 ⌈ε⁻¹⌉₊ : ℝ) := by exact_mod_cast hceilQ
  have hpow : (max 1 ⌈ε⁻¹⌉₊ : ℝ) ≤ (2 : ℝ)^phasePrecision ε := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (max 1 ⌈ε⁻¹⌉₊)
  have hmul : 1 ≤ (2 : ℝ)^phasePrecision ε * (ε : ℝ) :=
    (div_le_iff₀ hεR).mp (by simpa only [one_div] using! hceilR.trans hpow)
  have hd : (1 : ℝ) / (2 : ℝ)^phasePrecision ε ≤ (ε : ℝ) :=
    (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^phasePrecision ε)).mpr (by nlinarith)
  simpa [div_pow] using! hd

/-- Under the oracle hypotheses, choosing precision from positive rational `ε` bounds the clean
probability phase error by `ε` times the input norm. -/
theorem clean_probability_phase_tolerance {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ) (a₀ : A) (good : Finset A)
    (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0)
    (ε : ℚ) (hε : 0 < ε) (ψ : QState X) :
    let Z := zeroSignalFrame (X := X) a₀
    let D := Matrix.diagonal (fun x => Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ)))
    ‖toEuclidean_fromVec (evaluate (probabilityPrimitiveOracle U)
        (cleanProbabilityPhaseWord a₀ good (phasePrecision ε)) *ᵥ (Z *ᵥ ψ) - Z *ᵥ (D *ᵥ ψ))‖ ≤
      (ε : ℝ) * ‖toEuclidean_fromVec ψ‖ :=
  ((clean_probability_phase_actual U hU a₀ good hlabel (phasePrecision ε)).2.2.2 ψ).trans
    (mul_le_mul_of_nonneg_right (phasePrecision_budget ε hε) (norm_nonneg _))

end Qatlib.Concepts.HspRecovery.ReductionCore
