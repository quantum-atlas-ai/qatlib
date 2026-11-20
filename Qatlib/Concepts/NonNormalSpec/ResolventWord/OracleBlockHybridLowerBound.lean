/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponse

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline Qatlib.Concepts.NonNormalSpec.ResolventWord Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.FairRandomBits.FiniteCoinExecution Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Foundations.QueryWordCore.HamiltonianQuery Qatlib.Concepts.QueryWordCore.QueryMachinery Qatlib.Concepts.ReferenceError.MixturePaths

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QspSimulation.WordModel Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A real scalar multiple of the identity matrix is Hermitian. -/
private theorem real_smul_one_hermitian (W : Type) [Fintype W] [DecidableEq W]
    (z : ℝ) : ((z : ℂ) • (1 : Matrix W W ℂ)).IsHermitian := by
  change ((z : ℂ) • (1 : Matrix W W ℂ))ᴴ = (z : ℂ) • (1 : Matrix W W ℂ)
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    simp

/-- Scalar signal lifts are unitary exact encodings of the Hermitian scalar blocks and satisfy
the stated oracle distance bound. -/
theorem scalarBlockOraclePair_legal (W : Type) [Fintype W] [DecidableEq W]
    (x y : ℝ) (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    (scalarSignalLift W x ∈ Matrix.unitaryGroup (Bool × W) ℂ ∧
      scalarSignalLift W y ∈ Matrix.unitaryGroup (Bool × W) ℂ) ∧
    (ProjectedUnitaryEncoding ((x : ℂ) • (1 : Matrix W W ℂ)) (scalarSignalLift W x)
        (encodingFiber (I := W) false) (encodingFiber (I := W) false) ∧
      ProjectedUnitaryEncoding ((y : ℂ) • (1 : Matrix W W ℂ)) (scalarSignalLift W y)
        (encodingFiber (I := W) false) (encodingFiber (I := W) false)) ∧
    ((x : ℂ) • (1 : Matrix W W ℂ)).IsHermitian ∧
    ((y : ℂ) • (1 : Matrix W W ℂ)).IsHermitian ∧
    ‖scalarSignalLift W x - scalarSignalLift W y‖ ≤ scalarSignalDistance x y := by
  have hxU : scalarSignalLift W x ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
    tensorGate_unitary (scalar_signal_actual_encoding x hx).2.1 (Submonoid.one_mem _)
  have hyU : scalarSignalLift W y ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
    tensorGate_unitary (scalar_signal_actual_encoding y hy).2.1 (Submonoid.one_mem _)
  exact ⟨⟨hxU, hyU⟩,
    ⟨(scalar_signal_actual_encoding x hx).2.2.2 W,
      (scalar_signal_actual_encoding y hy).2.2.2 W⟩,
    real_smul_one_hermitian W x, real_smul_one_hermitian W y,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound.clause2_scalar_family_distance_le
      W x y hx hy⟩

/-- Every instruction of a well-formed scalar-lift circuit has norm at most one for both
admissible scalar signals. -/
private theorem lift_instruction_norms {W : Type} [Fintype W] [DecidableEq W]
    {x y : ℝ} (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1)
    {word : List (AdjointStep (Bool × W))} (hw : WellFormedAdjointCircuit word)
    {c : AdjointStep (Bool × W)} (hc : c ∈ word) :
    ‖instructionMatrix (scalarSignalLift W x) c‖ ≤ 1 ∧
      ‖instructionMatrix (scalarSignalLift W y) c‖ ≤ 1 := by
  have hxU : scalarSignalLift W x ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
    tensorGate_unitary (scalar_signal_actual_encoding x hx).2.1 (Submonoid.one_mem _)
  have hyU : scalarSignalLift W y ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
    tensorGate_unitary (scalar_signal_actual_encoding y hy).2.1 (Submonoid.one_mem _)
  cases c with
  | gate V =>
    have hV : V ∈ Matrix.unitaryGroup (Bool × W) ℂ := hw V hc
    exact ⟨l2_norm_unitary_le_one hV, l2_norm_unitary_le_one hV⟩
  | forward =>
    exact ⟨l2_norm_unitary_le_one hxU, l2_norm_unitary_le_one hyU⟩
  | backward =>
    constructor
    · simp only [instructionMatrix, Matrix.l2_opNorm_conjTranspose]
      exact l2_norm_unitary_le_one hxU
    · simp only [instructionMatrix, Matrix.l2_opNorm_conjTranspose]
      exact l2_norm_unitary_le_one hyU

/-- A real number of absolute value at most one half lies in the interval from negative one to
one. -/
private theorem abs_half_le_one {z : ℝ} (hz : |z| ≤ 1 / 2) : z ∈ Set.Icc (-1) 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hz
  exact ⟨by linarith, by linarith⟩

/-- On a nonempty index type, the norm of the difference of two real scalar identity matrices is
the absolute scalar difference. -/
private theorem scalar_target_norm (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : ℝ) :
    ‖(a : ℂ) • (1 : Matrix I I ℂ) - (b : ℂ) • (1 : Matrix I I ℂ)‖ = |a - b| := by
  rw [← sub_smul, ← Complex.ofReal_sub, norm_smul, l2_norm_one_eq, Complex.norm_real,
    Real.norm_eq_abs, mul_one]

/-- A circuit approximating two scalar function values obeys the hybrid query lower bound given
by their error-adjusted separation. -/
theorem scalarBlockFunctionValue_query_lower_bound :
    ∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
      (f : ℝ → ℝ) (x y eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → x ≠ y → 0 ≤ eps →
    ‖(f x : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
    ‖(f y : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
    (adjointQueryCount word : ℝ) ≥ max 0 (|f x - f y| - 2 * eps) / (2 * |x - y|) := by
  intro W I _ _ _ _ _ L R word f x y eps hL hR hWF hxhalf hyhalf hxy heps ha hb
  have hx : x ∈ Set.Icc (-1) 1 := abs_half_le_one hxhalf
  have hy : y ∈ Set.Icc (-1) 1 := abs_half_le_one hyhalf
  have hguard : ∀ c ∈ word,
      ‖instructionMatrix (scalarSignalLift W x) c‖ ≤ 1 ∧
        ‖instructionMatrix (scalarSignalLift W y) c‖ ≤ 1 :=
    fun c hc => lift_instruction_norms hx hy hWF hc
  have hgen := (Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponse.clause2_endpoint).1
    (Bool × W) I L R (scalarSignalLift W x) (scalarSignalLift W y) word
    ((f x : ℂ) • (1 : Matrix I I ℂ)) ((f y : ℂ) • (1 : Matrix I I ℂ)) eps
    hL hR hWF hguard heps ha hb
  rw [scalar_target_norm I (f x) (f y)] at hgen
  have hdist2 : ‖scalarSignalLift W x - scalarSignalLift W y‖ ≤ 2 * |x - y| :=
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound.clause2_scalar_family_distance_le
        W x y hx hy).trans
      ((scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.2 hxhalf hyhalf)
  have hle : max 0 (|f x - f y| - 2 * eps) ≤
      (adjointQueryCount word : ℝ) * (2 * |x - y|) :=
    hgen.trans (mul_le_mul_of_nonneg_left hdist2 (Nat.cast_nonneg _))
  have hpos : 0 < 2 * |x - y| :=
    mul_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hxy))
  exact (div_le_iff₀ hpos).mpr hle

/-- The scalar block query lower bound holds in every finite oracle dimension, together with
exact scalar block encodings. -/
theorem scalarBlock_lower_bound_every_dimension :
    ∀ (d : ℕ) (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix (Bool × Fin d) I ℂ) (word : List (AdjointStep (Bool × Fin d)))
      (f : ℝ → ℝ) (x y eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → x ≠ y → 0 ≤ eps →
    ‖(f x : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift (Fin d) x) word) R‖ ≤ eps →
    ‖(f y : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift (Fin d) y) word) R‖ ≤ eps →
    ((adjointQueryCount word : ℝ) ≥ max 0 (|f x - f y| - 2 * eps) / (2 * |x - y|) ∧
      ProjectedUnitaryEncoding ((x : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
        (scalarSignalLift (Fin d) x)
        (encodingFiber (I := Fin d) false) (encodingFiber (I := Fin d) false) ∧
      ProjectedUnitaryEncoding ((y : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
        (scalarSignalLift (Fin d) y)
        (encodingFiber (I := Fin d) false) (encodingFiber (I := Fin d) false)) := by
  intro d I _ _ _ L R word f x y eps hL hR hWF hxhalf hyhalf hxy heps ha hb
  have hx : x ∈ Set.Icc (-1) 1 := abs_half_le_one hxhalf
  have hy : y ∈ Set.Icc (-1) 1 := abs_half_le_one hyhalf
  exact ⟨scalarBlockFunctionValue_query_lower_bound (Fin d) I L R word f x y eps
      hL hR hWF hxhalf hyhalf hxy heps ha hb,
    (scalar_signal_actual_encoding x hx).2.2.2 (Fin d),
    (scalar_signal_actual_encoding y hy).2.2.2 (Fin d)⟩

/-- Under the additional range bounds, the scalar hybrid query lower bound also includes the
stated leakage separation term. -/
theorem scalarBlock_safe_leakage_lower_bound :
    ∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
      (f : ℝ → ℝ) (x y eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → x ≠ y → 0 ≤ eps →
    eps ≤ f x → f x ≤ 1 → 0 ≤ f y → f y + eps ≤ 1 →
    ‖(f x : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
    ‖(f y : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
    (adjointQueryCount word : ℝ) ≥
      max (max 0 (|f x - f y| - 2 * eps))
        (Real.sqrt (1 - (f y + eps)^2) - Real.sqrt (1 - (f x - eps)^2)) / (2 * |x - y|) := by
  intro W I _ _ _ _ _ L R word f x y eps hL hR hWF hxhalf hyhalf hxy heps
    haeps ha1 hb0 hbeps ha hb
  have hx : x ∈ Set.Icc (-1) 1 := abs_half_le_one hxhalf
  have hy : y ∈ Set.Icc (-1) 1 := abs_half_le_one hyhalf
  have hfroz := scalar_signal_safe_leakage_query_lower_bound_corrected W I L R word
    x y (f x) (f y) eps hL hR hWF hx hy hxy heps haeps ha1 hb0 hbeps ha hb
  have hD : 0 < scalarSignalDistance x y :=
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.1 hxy
  have hD2 : scalarSignalDistance x y ≤ 2 * |x - y| :=
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.2 hxhalf hyhalf
  have hX : 0 ≤ max (max 0 (|f x - f y| - 2 * eps))
      (Real.sqrt (1 - (f y + eps)^2) - Real.sqrt (1 - (f x - eps)^2)) :=
    le_max_of_le_left (le_max_left _ _)
  have hstep : max (max 0 (|f x - f y| - 2 * eps))
      (Real.sqrt (1 - (f y + eps)^2) - Real.sqrt (1 - (f x - eps)^2)) / (2 * |x - y|) ≤
      max (max 0 (|f x - f y| - 2 * eps))
        (Real.sqrt (1 - (f y + eps)^2) - Real.sqrt (1 - (f x - eps)^2)) /
      scalarSignalDistance x y :=
    div_le_div_of_nonneg_left hX hD hD2
  exact hstep.trans hfroz

/-- Collects the legal scalar block constructions, dimension-independent hybrid lower bounds,
and the strengthened leakage lower bound. -/
theorem scalar_oracle_block_hybrid_and_leakage_lower_bounds :
    (∀ (W : Type) [Fintype W] [DecidableEq W] (x y : ℝ),
      x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 →
      (scalarSignalLift W x ∈ Matrix.unitaryGroup (Bool × W) ℂ ∧
        scalarSignalLift W y ∈ Matrix.unitaryGroup (Bool × W) ℂ) ∧
      (ProjectedUnitaryEncoding ((x : ℂ) • (1 : Matrix W W ℂ)) (scalarSignalLift W x)
          (encodingFiber (I := W) false) (encodingFiber (I := W) false) ∧
        ProjectedUnitaryEncoding ((y : ℂ) • (1 : Matrix W W ℂ)) (scalarSignalLift W y)
          (encodingFiber (I := W) false) (encodingFiber (I := W) false)) ∧
      ((x : ℂ) • (1 : Matrix W W ℂ)).IsHermitian ∧
      ((y : ℂ) • (1 : Matrix W W ℂ)).IsHermitian ∧
      ‖scalarSignalLift W x - scalarSignalLift W y‖ ≤ scalarSignalDistance x y) ∧
    (∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Nonempty I]
        (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
        (f : ℝ → ℝ) (x y eps : ℝ),
      IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
      |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → x ≠ y → 0 ≤ eps →
      ‖(f x : ℂ) • (1 : Matrix I I ℂ) -
          compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
      ‖(f y : ℂ) • (1 : Matrix I I ℂ) -
          compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
      (adjointQueryCount word : ℝ) ≥ max 0 (|f x - f y| - 2 * eps) / (2 * |x - y|)) ∧
    (∀ (d : ℕ) (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
        (L R : Matrix (Bool × Fin d) I ℂ) (word : List (AdjointStep (Bool × Fin d)))
        (f : ℝ → ℝ) (x y eps : ℝ),
      IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
      |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → x ≠ y → 0 ≤ eps →
      ‖(f x : ℂ) • (1 : Matrix I I ℂ) -
          compress L (evaluate (scalarSignalLift (Fin d) x) word) R‖ ≤ eps →
      ‖(f y : ℂ) • (1 : Matrix I I ℂ) -
          compress L (evaluate (scalarSignalLift (Fin d) y) word) R‖ ≤ eps →
      ((adjointQueryCount word : ℝ) ≥ max 0 (|f x - f y| - 2 * eps) / (2 * |x - y|) ∧
        ProjectedUnitaryEncoding ((x : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
          (scalarSignalLift (Fin d) x)
          (encodingFiber (I := Fin d) false) (encodingFiber (I := Fin d) false) ∧
        ProjectedUnitaryEncoding ((y : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
          (scalarSignalLift (Fin d) y)
          (encodingFiber (I := Fin d) false) (encodingFiber (I := Fin d) false))) ∧
    (∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Nonempty I]
        (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
        (f : ℝ → ℝ) (x y eps : ℝ),
      IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
      |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → x ≠ y → 0 ≤ eps →
      eps ≤ f x → f x ≤ 1 → 0 ≤ f y → f y + eps ≤ 1 →
      ‖(f x : ℂ) • (1 : Matrix I I ℂ) -
          compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
      ‖(f y : ℂ) • (1 : Matrix I I ℂ) -
          compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
      (adjointQueryCount word : ℝ) ≥
        max (max 0 (|f x - f y| - 2 * eps))
          (Real.sqrt (1 - (f y + eps)^2) - Real.sqrt (1 - (f x - eps)^2)) /
          (2 * |x - y|)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun W _ _ x y hx hy => scalarBlockOraclePair_legal W x y hx hy
  · exact scalarBlockFunctionValue_query_lower_bound
  · exact scalarBlock_lower_bound_every_dimension
  · exact scalarBlock_safe_leakage_lower_bound

end Qatlib.Concepts.NonNormalSpec.ResolventWord
