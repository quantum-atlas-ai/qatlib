/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess

/-!
# Effective preparation and amplitude amplification

This module extends finite rational data access with inverse preparation words, controlled
selection, and quantitative linear-combination circuit bounds. `lcuTopBlock_exact` identifies
the exact control block with a normalized nonnegative weighted operator sum, while
`generalPrepare_exists` and `sparsePrepare_exists` extend preparation to complex and sparse
amplitude data. These constructions fit the block-encoding framework of [GilyenSuLowWiebe2019].

`groverRound` and `phaseRound` describe reflected circuit products. Under a scalar squared-block
hypothesis, their clean-subspace actions yield Chebyshev formulas, probability and collapse
estimates, and a two-round phase choice for oblivious amplitude amplification. The amplification
background is described in [BrassardEtAl2002].

## Main statements

* `prepareRoundTrip`: preparation followed by its inverse evaluates to the identity with
  explicit gate counts.
* `lcuTopBlock_error`: bounds the approximate weighted operator block.
* `groverPower_topBlock_chebT`: expresses the clean block of a Grover power by a Chebyshev
  polynomial under the scalar squared-block condition.
* `oaa_two_round_exact`: gives the exact clean-subspace action of two phase rounds.
* `cmplxLcuWord_collapse_exists`: provides rational-table approximations of normalized
  postselected outputs.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt

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
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator
open Qatlib

set_option autoImplicit false

/-- The conjugate of a complex number of norm one multiplied by that number equals one. -/
private theorem star_mul_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    starRingEnd ℂ z * z = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hz]
  norm_num

/-- The product of the conjugate of `a + b * I` with `a + b * I` is `a² + b²` for real `a` and
`b`. -/
private theorem star_ofReal_add_mul_I (a b : ℝ) :
    starRingEnd ℂ (Complex.ofReal a + Complex.ofReal b * Complex.I)
      * (Complex.ofReal a + Complex.ofReal b * Complex.I) = (a ^ 2 + b ^ 2 : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_apply]
  simp [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- A finite diagonal complex matrix is unitary when every diagonal entry has conjugate product
one. -/
private theorem diagonal_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℂ) (hd : ∀ i, starRingEnd ℂ (d i) * d i = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Finset.sum_eq_single x]
    · simpa [Matrix.star_apply, mul_comm] using! hd x
    · intro k _ hk
      simp [Matrix.star_apply, Ne.symm hk]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkx : k = x
    · subst hkx
      simp [Matrix.star_apply, Ne.symm hxy]
    · simp [Matrix.star_apply, Ne.symm hkx]

/-- The basis state indexed by `none` has Euclidean norm one. -/
private theorem stateVector_ket_none_norm {D : ℕ} :
    ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ = 1 := by
  have hsq : ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ ^ 2 = 1 := by
    rw [stateVector_norm_sq]
    simp [Qatlib.Foundations.PureStateMath.MeasureProb,
        Qatlib.Foundations.PureStateMath.BornProb, Qatlib.Foundations.PureStateMath.Ket]
  have hn :=
      norm_nonneg (stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
  nlinarith

/-- Applying a finite unitary matrix preserves the Euclidean norm of a state vector. -/
private theorem unitary_mulVec_stateVector_norm {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    ‖stateVector (U *ᵥ ψ)‖ = ‖stateVector ψ‖ := by
  have hUH : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff'.mp hU)
  have h1 : ‖stateVector (U *ᵥ ψ)‖ ≤ ‖stateVector ψ‖ := by
    have h := stateVector_mulVec_norm_le U ψ
    have hle := mul_le_mul_of_nonneg_right (l2_norm_unitary_le_one hU)
      (norm_nonneg (stateVector ψ))
    rw [one_mul] at hle
    exact h.trans hle
  have hback : Uᴴ *ᵥ (U *ᵥ ψ) = ψ := by
    rw [Matrix.mulVec_mulVec, hUH, Matrix.one_mulVec]
  have h2 : ‖stateVector ψ‖ ≤ ‖stateVector (U *ᵥ ψ)‖ := by
    have h := stateVector_mulVec_norm_le Uᴴ (U *ᵥ ψ)
    have hle := mul_le_mul_of_nonneg_right
      (l2_norm_unitary_le_one (adjoint_unitary hU)) (norm_nonneg (stateVector (U *ᵥ ψ)))
    rw [one_mul] at hle
    rw [hback] at h
    exact h.trans hle
  exact le_antisymm h1 h2

/-- The phase diagonal constructed at precision `k` is unitary. -/
theorem phaseDiagonal_unitary {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    phaseDiagonal k amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ := by
  have h : Matrix.diagonal (fun a => ratToComplex (phaseApprox (amp a) k))
      ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ := by
    refine diagonal_mem_unitaryGroup _ (fun a => ?_)
    rw [ratToComplex, star_ofReal_add_mul_I]
    exact_mod_cast (phaseApprox_unit (amp a) k)
  exact h

/-- The diagonal matrix of exact amplitude phases is unitary. -/
theorem exactPhaseDiagonal_unitary {D : ℕ} (amp : Option (Fin D) → RatComplex) :
    exactPhaseDiagonal amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ := by
  refine diagonal_mem_unitaryGroup _ (fun a => star_mul_self_of_norm_one ?_)
  by_cases hz : amp a = ratZero
  · rw [hz]
    exact exactPhase_zero
  · exact exactPhase_norm (amp a) hz

/-- The exact preparation matrix is unitary for nonnegative rational weights of positive total
mass. -/
theorem exactPrepareMatrix_unitary {D : ℕ} (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) :
    exactPrepareMatrix w amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ :=
  (Matrix.unitaryGroup (Option (Fin D)) ℂ).mul_mem (exactPhaseDiagonal_unitary amp)
    ((rational_weight_ideal_preparation_exact D w hw hm).1)

/-- The adjoint circuit word of `prepareWord`, used to reverse the preparation circuit. -/
noncomputable def prepareInverseWord {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) : List (AdjointStep (Option (Fin D))) :=
  adjointCircuit (prepareWord k w amp)

/-- The preparation word is well formed when all rational weights are nonnegative. -/
theorem prepareWord_wellFormed {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a) :
    WellFormedAdjointCircuit (prepareWord k w amp) := by
  have hphase : WellFormedAdjointCircuit (phaseWord k amp) := by
    simp only [phaseWord, WellFormedAdjointCircuit.gate_cons_iff,
      WellFormedAdjointCircuit.nil, and_true]
    exact phaseDiagonal_unitary k amp
  have hweight : WellFormedAdjointCircuit (rationalWeightWord w k) :=
    (rational_weight_numerical_word_unitary_and_error D k w hw).1
  rw [prepareWord]
  exact hphase.append hweight

/-- The inverse preparation word is well formed for nonnegative rational weights. -/
theorem prepareInverseWord_wellFormed {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a) :
    WellFormedAdjointCircuit (prepareInverseWord k w amp) :=
  (prepareWord_wellFormed k w amp hw).adjointCircuit

/-- The preparation matrix at precision `k` is unitary for nonnegative rational weights. -/
theorem prepareMatrix_unitary {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a) :
    prepareMatrix k w amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ := by
  have h := (prepareWord_wellFormed k w amp hw).evaluate_unitary
    (show (1 : Matrix (Option (Fin D)) (Option (Fin D)) ℂ)
        ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ by simp)
  rwa [prepareWord_eval] at h

/-- Evaluating the inverse preparation word with identity oracle gives the conjugate transpose
of the preparation matrix. -/
theorem prepareInverseWord_eval {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) :
    evaluate 1 (prepareInverseWord k w amp) = (prepareMatrix k w amp)ᴴ := by
  rw [prepareInverseWord, evaluate_adjointCircuit, prepareWord_eval]

/-- The inverse preparation word uses `D + 1` gates and zero oracle queries. -/
theorem prepareInverseWord_counts {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) :
    adjointGateCount (prepareInverseWord k w amp) = D + 1 ∧
      adjointQueryCount (prepareInverseWord k w amp) = 0 := by
  have h := prepareWord_counts k w amp
  simp only [prepareInverseWord, adjointGateCount_adjointCircuit,
    adjointQueryCount_adjointCircuit]
  exact h

/-- Preparation followed by its inverse is a well-formed identity circuit with `2 * (D + 1)`
gates and zero queries. -/
theorem prepareRoundTrip {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a) :
    WellFormedAdjointCircuit (prepareWord k w amp ++ prepareInverseWord k w amp) ∧
      evaluate 1 (prepareWord k w amp ++ prepareInverseWord k w amp) = 1 ∧
      adjointGateCount (prepareWord k w amp ++ prepareInverseWord k w amp) = 2 * (D + 1) ∧
      adjointQueryCount (prepareWord k w amp ++ prepareInverseWord k w amp) = 0 := by
  obtain ⟨hwf, hev, hq, hg⟩ := adjointCircuit_roundTrip 1 (prepareWord k w amp)
    (show (1 : Matrix (Option (Fin D)) (Option (Fin D)) ℂ)
        ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ by simp)
    (prepareWord_wellFormed k w amp hw)
  obtain ⟨hgW, hqW⟩ := prepareWord_counts k w amp
  simp only [prepareInverseWord]
  refine ⟨hwf, hev, ?_, ?_⟩
  · rw [hg, hgW]
  · rw [hq, hqW]

/-- Applying approximate preparation after the inverse exact preparation moves the `none` basis
state by at most `32 * (D + 1) / 2^k` in Euclidean norm. -/
theorem prepareUncompute_clean {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) :
    ‖stateVector ((prepareMatrix k w amp * (exactPrepareMatrix w amp)ᴴ) *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
        - stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖
      ≤ 32 * (D + 1) / 2 ^ k := by
  have hVU : exactPrepareMatrix w amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ :=
    exactPrepareMatrix_unitary w amp hw hm
  have hVHU : (exactPrepareMatrix w amp)ᴴ ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ :=
    adjoint_unitary hVU
  have hVV : exactPrepareMatrix w amp * (exactPrepareMatrix w amp)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff.mp hVU)
  have hkey : (prepareMatrix k w amp - exactPrepareMatrix w amp) *ᵥ
        ((exactPrepareMatrix w amp)ᴴ *ᵥ (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
      = (prepareMatrix k w amp * (exactPrepareMatrix w amp)ᴴ) *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))
          - Qatlib.Foundations.PureStateMath.Ket none := by
    rw [Matrix.mulVec_mulVec, Matrix.sub_mul, hVV, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hclean : ‖stateVector ((exactPrepareMatrix w amp)ᴴ *ᵥ
        (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))‖ = 1 := by
    rw [unitary_mulVec_stateVector_norm _ hVHU _, stateVector_ket_none_norm]
  have hnorm := stateVector_mulVec_norm_le
    (prepareMatrix k w amp - exactPrepareMatrix w amp)
    ((exactPrepareMatrix w amp)ᴴ *ᵥ (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
  rw [hclean, mul_one] at hnorm
  have hd : stateVector ((prepareMatrix k w amp * (exactPrepareMatrix w amp)ᴴ) *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
        - stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))
      = stateVector ((prepareMatrix k w amp * (exactPrepareMatrix w amp)ᴴ) *ᵥ
            (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))
            - (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))) := by
    simp [stateVector, WithLp.toLp_sub]
  rw [hd, ← hkey]
  exact hnorm.trans (prepareMatrix_error k w amp hw hm)

/-- Choosing `precisionFor D ε` bounds the preparation and exact-uncomputation error on the
`none` basis state by `ε`. -/
theorem prepareUncompute_clean_epsilon {D : ℕ} (ε : ℚ) (hε : 0 < ε)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w) :
    ‖stateVector ((prepareMatrix (precisionFor D ε) w amp
            * (exactPrepareMatrix w amp)ᴴ) *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
        - stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖
      ≤ (ε : ℝ) := by
  have h := prepareUncompute_clean (precisionFor D ε) w amp hw hm
  have hb := prepError_le_epsilon (D := D) ε hε
  linarith

/-- The conjugate transposes of approximate and exact preparation matrices differ in norm by at
most `32 * (D + 1) / 2^k`. -/
theorem prepareInverseMatrix_error {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) :
    ‖(prepareMatrix k w amp)ᴴ - (exactPrepareMatrix w amp)ᴴ‖
      ≤ 32 * (D + 1) / 2 ^ k := by
  have h : (prepareMatrix k w amp)ᴴ - (exactPrepareMatrix w amp)ᴴ
      = (prepareMatrix k w amp - exactPrepareMatrix w amp)ᴴ := by
    rw [Matrix.conjTranspose_sub]
  rw [h, Matrix.l2_opNorm_conjTranspose]
  exact prepareMatrix_error k w amp hw hm

/-- Collects inverse preparation semantics, gate counts, well-formedness, exact unitarity, and
quantitative uncomputation bounds. -/
theorem frontier1 :
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex),
      evaluate 1 (prepareInverseWord k w amp) = (prepareMatrix k w amp)ᴴ) ∧
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex),
      adjointGateCount (prepareInverseWord k w amp) = D + 1 ∧
        adjointQueryCount (prepareInverseWord k w amp) = 0) ∧
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
        (_hw : ∀ a, 0 ≤ w a),
      WellFormedAdjointCircuit (prepareWord k w amp) ∧
        WellFormedAdjointCircuit (prepareInverseWord k w amp) ∧
        evaluate 1 (prepareWord k w amp ++ prepareInverseWord k w amp) = 1 ∧
        adjointGateCount (prepareWord k w amp ++ prepareInverseWord k w amp) = 2 * (D + 1) ∧
        adjointQueryCount (prepareWord k w amp ++ prepareInverseWord k w amp) = 0) ∧
    (∀ {D : ℕ} (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
        (_hw : ∀ a, 0 ≤ w a) (_hm : 0 < rationalWeightMass w),
      exactPrepareMatrix w amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ) ∧
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
        (_hw : ∀ a, 0 ≤ w a) (_hm : 0 < rationalWeightMass w),
      ‖stateVector ((prepareMatrix k w amp * (exactPrepareMatrix w amp)ᴴ) *ᵥ
            (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
          - stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖
        ≤ 32 * (D + 1) / 2 ^ k) ∧
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
        (_hw : ∀ a, 0 ≤ w a) (_hm : 0 < rationalWeightMass w),
      ‖(prepareMatrix k w amp)ᴴ - (exactPrepareMatrix w amp)ᴴ‖
        ≤ 32 * (D + 1) / 2 ^ k) ∧
    (∀ {D : ℕ} (ε : ℚ) (_hε : 0 < ε) (w : Option (Fin D) → ℚ)
        (amp : Option (Fin D) → RatComplex)
        (_hw : ∀ a, 0 ≤ w a) (_hm : 0 < rationalWeightMass w),
      ‖stateVector ((prepareMatrix (precisionFor D ε) w amp
              * (exactPrepareMatrix w amp)ᴴ) *ᵥ
            (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
          - stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖
        ≤ (ε : ℝ)) := by
  refine ⟨fun {_} k w amp => prepareInverseWord_eval k w amp,
    fun {_} k w amp => prepareInverseWord_counts k w amp, ?_,
    fun {_} w amp hw hm => exactPrepareMatrix_unitary w amp hw hm,
    fun {_} k w amp hw hm => prepareUncompute_clean k w amp hw hm,
    fun {_} k w amp hw hm => prepareInverseMatrix_error k w amp hw hm,
    fun {_} ε hε w amp hw hm => prepareUncompute_clean_epsilon ε hε w amp hw hm⟩
  intro D k w amp hw
  simp only [prepareInverseWord]
  obtain ⟨hwf, hev, hq, hg⟩ := prepareRoundTrip k w amp hw
  exact ⟨prepareWord_wellFormed k w amp hw,
    (prepareWord_wellFormed k w amp hw).adjointCircuit, hev, hq, hg⟩

/-- Lifts an adjoint circuit step to a product register by tensoring gates with the identity and
retaining oracle directions. -/
noncomputable def liftAdjointStep {H X : Type*} [DecidableEq X] :
    AdjointStep H → AdjointStep (H × X)
  | .gate V => .gate (TensorGate V 1)
  | .forward => .forward
  | .backward => .backward

/-- Lifts every step of an adjoint circuit word to a product register. -/
noncomputable def liftAdjointWord {H X : Type*} [DecidableEq X]
    (cs : List (AdjointStep H)) :
    List (AdjointStep (H × X)) := cs.map liftAdjointStep

/-- Lifting an adjoint circuit word preserves its gate count. -/
theorem adjointGateCount_liftAdjointWord {H X : Type*} [DecidableEq X]
    (cs : List (AdjointStep H)) :
    adjointGateCount (liftAdjointWord (X := X) cs) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | gate V =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep, adjointGateCount]
        exact congrArg (· + 1) ih
    | forward =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep, adjointGateCount]
        exact ih
    | backward =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep, adjointGateCount]
        exact ih

/-- Lifting an adjoint circuit word preserves its oracle query count. -/
theorem adjointQueryCount_liftAdjointWord {H X : Type*} [DecidableEq X]
    (cs : List (AdjointStep H)) :
    adjointQueryCount (liftAdjointWord (X := X) cs) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | gate V =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep, adjointQueryCount]
        exact ih
    | forward =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep, adjointQueryCount]
        exact congrArg (· + 1) ih
    | backward =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep, adjointQueryCount]
        exact congrArg (· + 1) ih

/-- Taking the adjoint circuit commutes with lifting to a product register. -/
theorem adjointCircuit_liftAdjointWord {H X : Type*} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (cs : List (AdjointStep H)) :
    adjointCircuit (liftAdjointWord (X := X) cs) = liftAdjointWord (adjointCircuit cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | gate V =>
        have h1 : liftAdjointWord (X := X) (AdjointStep.gate V :: cs)
            = AdjointStep.gate (TensorGate V 1) :: liftAdjointWord (X := X) cs := rfl
        rw [h1, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit,
            Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, ih]
        simp only [liftAdjointWord, List.map_append, List.map_cons, List.map_nil,
          adjointInstruction, liftAdjointStep]
        rw [tensorGate_conjTranspose, Matrix.conjTranspose_one]
    | forward =>
        have h1 : liftAdjointWord (X := X) (AdjointStep.forward :: cs)
            = AdjointStep.forward :: liftAdjointWord (X := X) cs := rfl
        rw [h1, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit,
            Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, ih]
        simp only [liftAdjointWord, List.map_append, List.map_cons, List.map_nil,
          adjointInstruction, liftAdjointStep]
    | backward =>
        have h1 : liftAdjointWord (X := X) (AdjointStep.backward :: cs)
            = AdjointStep.backward :: liftAdjointWord (X := X) cs := rfl
        rw [h1, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit,
            Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, ih]
        simp only [liftAdjointWord, List.map_append, List.map_cons, List.map_nil,
          adjointInstruction, liftAdjointStep]

/-- Evaluating a lifted word with a lifted oracle tensors the original evaluation with the
identity. -/
theorem evaluate_liftAdjointWord {H X : Type*} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (U : Matrix H H ℂ)
    (cs : List (AdjointStep H)) :
    evaluate (TensorGate U 1) (liftAdjointWord (X := X) cs) = TensorGate (evaluate U cs) 1 := by
  induction cs with
  | nil => simp [evaluate, liftAdjointWord, tensorGate_one]
  | cons c cs ih =>
    have h1 : liftAdjointWord (X := X) (c :: cs)
        = liftAdjointStep c :: liftAdjointWord (X := X) cs := rfl
    cases c with
    | gate V =>
        rw [h1, evaluate, evaluate]
        simp only [liftAdjointStep, instructionMatrix]
        rw [ih, tensorGate_mul, Matrix.one_mul]
    | forward =>
        rw [h1, evaluate, evaluate]
        simp only [liftAdjointStep, instructionMatrix]
        rw [ih, tensorGate_mul, Matrix.one_mul]
    | backward =>
        rw [h1, evaluate, evaluate]
        simp only [liftAdjointStep, instructionMatrix]
        rw [ih, tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul,
          Matrix.one_mul]

/-- With identity oracle, evaluating a lifted word gives the tensor product of its original
evaluation with the identity. -/
theorem evaluate_liftAdjointWord_one {H X : Type*} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (cs : List (AdjointStep H)) :
    evaluate 1 (liftAdjointWord (X := X) cs) = TensorGate (evaluate 1 cs) 1 := by
  have h := evaluate_liftAdjointWord (X := X) (1 : Matrix H H ℂ) cs
  rwa [tensorGate_one] at h

/-- Lifting a well-formed adjoint circuit word preserves well-formedness. -/
theorem wellFormed_liftAdjointWord {H X : Type*} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] {cs : List (AdjointStep H)}
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (liftAdjointWord (X := X) cs) := by
  induction cs with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons c cs ih =>
    cases c with
    | gate V =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep,
          WellFormedAdjointCircuit.gate_cons_iff] at hcs ⊢
        exact ⟨tensorGate_unitary hcs.1
          (by simp : (1 : Matrix X X ℂ) ∈ Matrix.unitaryGroup X ℂ), ih hcs.2⟩
    | forward =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep,
          WellFormedAdjointCircuit.forward_cons_iff] at hcs ⊢
        exact ih hcs
    | backward =>
        simp only [liftAdjointWord, List.map_cons, liftAdjointStep,
          WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
        exact ih hcs

/-- The preparation, selection, and inverse-preparation word for a linear combination of
operators. -/
noncomputable def lcuBlockWord {D : ℕ} {X : Type*} [DecidableEq X] (k : ℕ)
    (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    List (AdjointStep (Option (Fin D) × X)) :=
  liftAdjointWord (prepareInverseWord k w amp) ++ [.gate S]
    ++ liftAdjointWord (prepareWord k w amp)

/-- The linear-combination word evaluates to the selector sandwiched between preparation and its
conjugate transpose. -/
theorem lcuBlockWord_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (lcuBlockWord k w amp S)
      = TensorGate (prepareMatrix k w amp)ᴴ 1 * S * TensorGate (prepareMatrix k w amp) 1 := by
  rw [lcuBlockWord, evaluate_append, evaluate_append, evaluate_liftAdjointWord_one,
    evaluate_liftAdjointWord_one, prepareInverseWord_eval, prepareWord_eval]
  simp [evaluate, instructionMatrix]

/-- The linear-combination word uses `2 * (D + 1) + 1` gates and zero queries. -/
theorem lcuBlockWord_counts {D : ℕ} {X : Type*} [DecidableEq X] (k : ℕ)
    (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    adjointGateCount (lcuBlockWord k w amp S) = 2 * (D + 1) + 1 ∧
      adjointQueryCount (lcuBlockWord k w amp S) = 0 := by
  obtain ⟨hgW, _⟩ := prepareWord_counts k w amp
  obtain ⟨hgI, _⟩ := prepareInverseWord_counts k w amp
  simp only [lcuBlockWord, adjointGateCount_append, adjointQueryCount_append,
    adjointGateCount_liftAdjointWord, adjointQueryCount_liftAdjointWord, adjointGateCount,
    adjointQueryCount]
  omega

/-- The linear-combination word is well formed for nonnegative weights and a unitary selector. -/
theorem lcuBlockWord_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (lcuBlockWord k w amp S) := by
  simp only [lcuBlockWord, WellFormedAdjointCircuit.append_iff,
    WellFormedAdjointCircuit.gate_cons_iff, and_assoc]
  exact ⟨wellFormed_liftAdjointWord (prepareInverseWord_wellFormed k w amp hw), hS,
    WellFormedAdjointCircuit.nil,
    wellFormed_liftAdjointWord (prepareWord_wellFormed k w amp hw)⟩

/-- The block diagonal selector whose block indexed by `a` is `U a`. -/
def blockSelect {D : ℕ} {X : Type*} (U : Option (Fin D) → Matrix X X ℂ) :
    Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ :=
  fun p q => if p.1 = q.1 then U p.1 p.2 q.2 else 0

/-- On a basis control state `a`, the selector applies `U a` to the data state and preserves the
control. -/
theorem blockSelect_mulVec_tensorState {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Option (Fin D) → Matrix X X ℂ) (a : Option (Fin D)) (φ : QState X) :
    blockSelect U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket a) φ = TensorState (Qatlib.Foundations.PureStateMath.Ket a) (U a *ᵥ φ) := by
  ext ⟨b, y⟩
  simp only [Matrix.mulVec, dotProduct, blockSelect, Fintype.sum_prod_type, TensorState,
    Matrix.mulVec, dotProduct]
  by_cases hba : b = a
  · subst hba
    rw [Finset.sum_eq_single b]
    · simp [Qatlib.Foundations.PureStateMath.Ket]
    · intro c _ hcb
      by_cases hbc : b = c
      · exact absurd hbc.symm hcb
      · simp [hbc]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · have key : ∀ c ∈ (Finset.univ : Finset (Option (Fin D))),
        ∑ z : X, (if b = c then U b y z else 0) * (Qatlib.Foundations.PureStateMath.Ket a c * φ z) = 0 := by
      intro c _
      by_cases hbc : b = c
      · have hca : ¬ c = a := fun h => hba (hbc ▸ h)
        simp [hbc, hca, Qatlib.Foundations.PureStateMath.Ket]
      · simp [hbc]
    rw [Finset.sum_eq_zero key]
    simp [hba, Qatlib.Foundations.PureStateMath.Ket]

/-- A block selector is unitary when every selected matrix is unitary. -/
theorem blockSelect_unitary {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {U : Option (Fin D) → Matrix X X ℂ} (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    blockSelect U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
  have hUb : ∀ a, (U a)ᴴ * U a = 1 := fun a => by
    simpa only [Matrix.star_eq_conjTranspose] using!
      (Matrix.mem_unitaryGroup_iff'.mp (hU a))
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext ⟨b, y⟩ ⟨c, z⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hbc : b = c
  · subst hbc
    rw [Finset.sum_eq_single b]
    · simp only [Matrix.conjTranspose_apply, blockSelect, if_true]
      have hentry : (∑ x : X, Star.star (U b x y) * U b x z)
          = ((U b)ᴴ * U b) y z := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Matrix.conjTranspose_apply]
      rw [hentry, hUb b]
      simp [Matrix.one_apply]
    · intro a _ hab
      simp only [Matrix.conjTranspose_apply, blockSelect, if_neg hab, star_zero,
        mul_zero, Finset.sum_const_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · rw [Finset.sum_eq_zero]
    · simp [hbc]
    · intro a _
      apply Finset.sum_eq_zero
      intro x _
      simp only [Matrix.conjTranspose_apply, blockSelect]
      by_cases hab : a = b
      · rw [if_pos hab, if_neg (fun h => hbc (hab ▸ h)), mul_zero]
      · rw [if_neg hab, star_zero, zero_mul]

/-- Approximate and exact preparation sandwiches around a unitary selector differ in norm by at
most `64 * (D + 1) / 2^k`. -/
theorem lcuBlock_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖TensorGate (prepareMatrix k w amp)ᴴ 1 * S * TensorGate (prepareMatrix k w amp) 1
        - TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1‖
      ≤ 64 * (D + 1) / 2 ^ k := by
  have honeX : ‖(1 : Matrix X X ℂ)‖ = 1 := l2_norm_one_eq
  have herr : ‖prepareMatrix k w amp - exactPrepareMatrix w amp‖
      ≤ 32 * (D + 1) / 2 ^ k := prepareMatrix_error k w amp hw hm
  have herrA : ‖(prepareMatrix k w amp)ᴴ - (exactPrepareMatrix w amp)ᴴ‖
      ≤ 32 * (D + 1) / 2 ^ k := prepareInverseMatrix_error k w amp hw hm
  have hterrA : ‖TensorGate (prepareMatrix k w amp)ᴴ (1 : Matrix X X ℂ)
        - TensorGate (exactPrepareMatrix w amp)ᴴ 1‖ ≤ 32 * (D + 1) / 2 ^ k := by
    rw [(l2_tensor_ancilla_error ((prepareMatrix k w amp)ᴴ)
        ((exactPrepareMatrix w amp)ᴴ)).1]
    exact herrA
  have hterr : ‖TensorGate (prepareMatrix k w amp) (1 : Matrix X X ℂ)
        - TensorGate (exactPrepareMatrix w amp) 1‖ ≤ 32 * (D + 1) / 2 ^ k := by
    rw [(l2_tensor_ancilla_error (prepareMatrix k w amp)
        (exactPrepareMatrix w amp)).1]
    exact herr
  have hnormS : ‖S‖ = 1 := l2_norm_unitary_eq_one hS
  have hnormTP : ‖TensorGate (prepareMatrix k w amp) (1 : Matrix X X ℂ)‖ = 1 := by
    rw [l2_norm_tensorGate, l2_norm_unitary_eq_one (prepareMatrix_unitary k w amp hw), honeX]
    norm_num
  have hnormTVA : ‖TensorGate (exactPrepareMatrix w amp)ᴴ (1 : Matrix X X ℂ)‖ = 1 := by
    rw [l2_norm_tensorGate, l2_norm_unitary_eq_one
      (adjoint_unitary (exactPrepareMatrix_unitary w amp hw hm)), honeX]
    norm_num
  have hdecomp :
      TensorGate (prepareMatrix k w amp)ᴴ 1 * S * TensorGate (prepareMatrix k w amp) 1
        - TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1
      = (TensorGate (prepareMatrix k w amp)ᴴ 1 - TensorGate (exactPrepareMatrix w amp)ᴴ 1) * S
          * TensorGate (prepareMatrix k w amp) 1
        + TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * (TensorGate (prepareMatrix k w amp) 1
                - TensorGate (exactPrepareMatrix w amp) 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hdecomp]
  have ht1 : ‖(TensorGate (prepareMatrix k w amp)ᴴ 1
        - TensorGate (exactPrepareMatrix w amp)ᴴ 1) * S
      * TensorGate (prepareMatrix k w amp) 1‖ ≤ 32 * (D + 1) / 2 ^ k := by
    calc ‖(TensorGate (prepareMatrix k w amp)ᴴ 1
            - TensorGate (exactPrepareMatrix w amp)ᴴ 1) * S
          * TensorGate (prepareMatrix k w amp) 1‖
        ≤ ‖(TensorGate (prepareMatrix k w amp)ᴴ 1
              - TensorGate (exactPrepareMatrix w amp)ᴴ 1) * S‖
            * ‖TensorGate (prepareMatrix k w amp) 1‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖TensorGate (prepareMatrix k w amp)ᴴ 1
              - TensorGate (exactPrepareMatrix w amp)ᴴ 1‖ * ‖S‖)
            * ‖TensorGate (prepareMatrix k w amp) 1‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = (‖TensorGate (prepareMatrix k w amp)ᴴ 1
              - TensorGate (exactPrepareMatrix w amp)ᴴ 1‖ * 1) * 1 := by
          rw [hnormS, hnormTP]
      _ = ‖TensorGate (prepareMatrix k w amp)ᴴ 1
            - TensorGate (exactPrepareMatrix w amp)ᴴ 1‖ := by norm_num
      _ ≤ 32 * (D + 1) / 2 ^ k := hterrA
  have ht2 : ‖TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
      * (TensorGate (prepareMatrix k w amp) 1
          - TensorGate (exactPrepareMatrix w amp) 1)‖
      ≤ 32 * (D + 1) / 2 ^ k := by
    calc ‖TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
          * (TensorGate (prepareMatrix k w amp) 1
              - TensorGate (exactPrepareMatrix w amp) 1)‖
        ≤ ‖TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S‖
            * ‖TensorGate (prepareMatrix k w amp) 1
                - TensorGate (exactPrepareMatrix w amp) 1‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖TensorGate (exactPrepareMatrix w amp)ᴴ 1‖ * ‖S‖)
            * ‖TensorGate (prepareMatrix k w amp) 1
                - TensorGate (exactPrepareMatrix w amp) 1‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = (1 * 1) * ‖TensorGate (prepareMatrix k w amp) 1
            - TensorGate (exactPrepareMatrix w amp) 1‖ := by rw [hnormTVA, hnormS]
      _ = ‖TensorGate (prepareMatrix k w amp) 1
            - TensorGate (exactPrepareMatrix w amp) 1‖ := by norm_num
      _ ≤ 32 * (D + 1) / 2 ^ k := hterr
  refine (norm_add_le _ _).trans ?_
  have hsplit : 32 * ((D : ℝ) + 1) / (2 ^ k : ℝ) + 32 * ((D : ℝ) + 1) / (2 ^ k : ℝ)
      = 64 * ((D : ℝ) + 1) / (2 ^ k : ℝ) := by
    rw [← add_div]
    congr 1
    ring
  linarith

/-- The preparation sandwich error is at most `64 * (D + 1) / 2^k` for a selector of unitary
blocks. -/
theorem lcuBlock_error_blockSelect {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖TensorGate (prepareMatrix k w amp)ᴴ 1 * blockSelect U
        * TensorGate (prepareMatrix k w amp) 1
        - TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
            * TensorGate (exactPrepareMatrix w amp) 1‖
      ≤ 64 * (D + 1) / 2 ^ k :=
  lcuBlock_error k w amp hw hm _ (blockSelect_unitary hU)

/-- Tensoring a normalized state with the `none` basis state produces a normalized state. -/
private theorem stateVector_ket_none_tensor_norm {D : ℕ} {X : Type*}
    [Fintype X] [DecidableEq X] (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
  have h : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
      = ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ * ‖stateVector ψ‖ :=
    tensorState_l2_norm _ _
  rw [stateVector_ket_none_norm, hψ, mul_one] at h
  exact h

/-- Approximate and exact linear-combination sandwiches applied to a normalized data state
differ by at most `64 * (D + 1) / 2^k`. -/
theorem lcuUncompute_clean {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ‖stateVector ((TensorGate (prepareMatrix k w amp)ᴴ 1 * S
            * TensorGate (prepareMatrix k w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
      ≤ 64 * (D + 1) / 2 ^ k := by
  have hsub : stateVector ((TensorGate (prepareMatrix k w amp)ᴴ 1 * S
          * TensorGate (prepareMatrix k w amp) 1) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      = stateVector ((TensorGate (prepareMatrix k w amp)ᴴ 1 * S
            * TensorGate (prepareMatrix k w amp) 1
            - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
              * TensorGate (exactPrepareMatrix w amp) 1)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ) := by
    simp [stateVector, WithLp.toLp_sub, Matrix.sub_mulVec]
  rw [hsub]
  have hn := stateVector_mulVec_norm_le
    (TensorGate (prepareMatrix k w amp)ᴴ 1 * S * TensorGate (prepareMatrix k w amp) 1
      - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
        * TensorGate (exactPrepareMatrix w amp) 1))
    (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
  rw [stateVector_ket_none_tensor_norm ψ hψ] at hn
  refine hn.trans ?_
  rw [mul_one]
  exact lcuBlock_error k w amp hw hm S hS

/-- Exact preparation and uncomputation cancel around an operator acting only on the data
register. -/
theorem exactLcuPipeline_dataSelect {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Matrix X X ℂ) :
    TensorGate (exactPrepareMatrix w amp)ᴴ 1 * TensorGate 1 U
        * TensorGate (exactPrepareMatrix w amp) 1
      = TensorGate 1 U := by
  have hV : exactPrepareMatrix w amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ :=
    exactPrepareMatrix_unitary w amp hw hm
  have hVHV : (exactPrepareMatrix w amp)ᴴ * exactPrepareMatrix w amp = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff'.mp hV)
  simp only [tensorGate_mul, one_mul, Matrix.mul_one, hVHV]

/-- The approximate sandwich for a unitary acting only on data differs from its clean-ancilla
output by at most `64 * (D + 1) / 2^k`. -/
theorem lcuUncompute_dataSelect_clean {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Matrix X X ℂ) (hU : U ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ‖stateVector ((TensorGate (prepareMatrix k w amp)ᴴ 1 * TensorGate 1 U
            * TensorGate (prepareMatrix k w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) (U *ᵥ ψ))‖
      ≤ 64 * (D + 1) / 2 ^ k := by
  have hTU : TensorGate (1 : Matrix (Option (Fin D)) (Option (Fin D)) ℂ) U
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) hU
  have h := lcuUncompute_clean k w amp hw hm _ hTU ψ hψ
  rw [exactLcuPipeline_dataSelect w amp hw hm U] at h
  have hact : TensorGate (1 : Matrix (Option (Fin D)) (Option (Fin D)) ℂ) U *ᵥ
      TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ
      = TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) (U *ᵥ ψ) := by
    have h0 := kronecker_mulVec_tensorState
      (1 : Matrix (Option (Fin D)) (Option (Fin D)) ℂ) U (Qatlib.Foundations.PureStateMath.Ket none) ψ
    rw [Matrix.one_mulVec] at h0
    exact h0
  rw [hact] at h
  exact h

/-- Precision `precisionFor D (ε / 2)` bounds the clean-ancilla error for a data-only unitary by
`ε`. -/
theorem lcuUncompute_dataSelect_clean_epsilon {D : ℕ} {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (ε : ℚ) (hε : 0 < ε)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Matrix X X ℂ) (hU : U ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ‖stateVector ((TensorGate (prepareMatrix (precisionFor D (ε / 2)) w amp)ᴴ 1
            * TensorGate 1 U
            * TensorGate (prepareMatrix (precisionFor D (ε / 2)) w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) (U *ᵥ ψ))‖
      ≤ (ε : ℝ) := by
  have h := lcuUncompute_dataSelect_clean (precisionFor D (ε / 2)) w amp hw hm U hU ψ hψ
  have hb := prepError_le_epsilon (D := D) (ε / 2) (half_pos hε)
  have hcast : ((ε / 2 : ℚ) : ℝ) = (ε : ℝ) / 2 := by push_cast; ring
  have hc : (0 : ℝ) < 2 ^ precisionFor D (ε / 2) := by positivity
  have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 2) : ℝ)
      = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 2) : ℝ)) := by
    field_simp
    ring
  linarith

/-- Evaluating the linear-combination word for a data-only unitary approximates its
clean-ancilla action within `64 * (D + 1) / 2^k`. -/
theorem lcuUncompute_word_clean {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Matrix X X ℂ) (hU : U ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ‖stateVector (evaluate 1 (lcuBlockWord k w amp (TensorGate 1 U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) (U *ᵥ ψ))‖
      ≤ 64 * (D + 1) / 2 ^ k := by
  rw [lcuBlockWord_eval]
  exact lcuUncompute_dataSelect_clean k w amp hw hm U hU ψ hψ

/-- The linear-combination word for a data-only unitary has clean-ancilla error at most `ε` at
precision `precisionFor D (ε / 2)`. -/
theorem lcuUncompute_word_clean_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Matrix X X ℂ) (hU : U ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ‖stateVector (evaluate 1
          (lcuBlockWord (precisionFor D (ε / 2)) w amp (TensorGate 1 U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) (U *ᵥ ψ))‖
      ≤ (ε : ℝ) := by
  rw [lcuBlockWord_eval]
  exact lcuUncompute_dataSelect_clean_epsilon ε hε w amp hw hm U hU ψ hψ

/-- The matrix block obtained by fixing both control indices to `none`. -/
def blockNone {D : ℕ} {X : Type*}
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    Matrix X X ℂ := fun x y => M (none, x) (none, y)

/-- Restricting a state to the control index `none` cannot increase its Euclidean norm. -/
private theorem stateVector_restrictNone_norm_le {D : ℕ} {X : Type*}
    [Fintype X] [DecidableEq X] (u : QState (Option (Fin D) × X)) :
    ‖stateVector (fun x => u (none, x))‖ ≤ ‖stateVector u‖ := by
  have hsub : ‖stateVector (fun x => u (none, x))‖ ^ 2 ≤ ‖stateVector u‖ ^ 2 := by
    rw [stateVector_norm_sq, stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb,
      Qatlib.Foundations.PureStateMath.MeasureProb]
    have h1 : ∑ p ∈ Finset.product ({none} : Finset (Option (Fin D)))
          (Finset.univ : Finset X), Qatlib.Foundations.PureStateMath.BornProb u p
        = ∑ a ∈ ({none} : Finset (Option (Fin D))), ∑ z ∈ (Finset.univ : Finset X),
            Qatlib.Foundations.PureStateMath.BornProb u (a, z) :=
      Finset.sum_product _ _ _
    calc ∑ x : X, Qatlib.Foundations.PureStateMath.BornProb (fun x => u (none, x)) x
        = ∑ p ∈ Finset.product ({none} : Finset (Option (Fin D)))
            (Finset.univ : Finset X), Qatlib.Foundations.PureStateMath.BornProb u p := by
          rw [h1, Finset.sum_singleton]
          simp [Qatlib.Foundations.PureStateMath.BornProb]
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Option (Fin D) × X)), Qatlib.Foundations.PureStateMath.BornProb u p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun p _ _ => sq_nonneg (‖u p‖))
  rw [← Real.sqrt_sq (norm_nonneg (stateVector (fun x => u (none, x)))),
    ← Real.sqrt_sq (norm_nonneg (stateVector u))]
  exact Real.sqrt_le_sqrt hsub

/-- Extracting the `none` control block cannot increase the matrix norm. -/
theorem blockNone_norm_le {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    ‖blockNone M‖ ≤ ‖M‖ := by
  refine l2_opNorm_le_of_mulVec_le (norm_nonneg M) _ fun v => ?_
  have hact : blockNone M *ᵥ v
      = (fun x => (M *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) v) (none, x)) := by
    funext x
    simp only [Matrix.mulVec, dotProduct, blockNone, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single none]
    · simp [Qatlib.Foundations.PureStateMath.TensorState,
        Qatlib.Foundations.PureStateMath.Ket]
    · intro a _ ha
      simp [Qatlib.Foundations.PureStateMath.TensorState,
          Qatlib.Foundations.PureStateMath.Ket, ha]
    · intro hn
      exact absurd (Finset.mem_univ none) hn
  rw [hact]
  calc ‖stateVector
        (fun x => (M *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) v) (none, x))‖
      ≤ ‖stateVector (M *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) v)‖ :=
        stateVector_restrictNone_norm_le _
    _ ≤ ‖M‖ * ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) v)‖ :=
        stateVector_mulVec_norm_le M _
    _ = ‖M‖ * ‖stateVector v‖ := by
        have hT : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) v)‖
            = ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ * ‖stateVector v‖ :=
          tensorState_l2_norm _ _
        rw [hT, stateVector_ket_none_norm, one_mul]

/-- The `none` column of the exact preparation matrix is the product of the exact phase and the
rational weight target. -/
theorem exactPrepareColumn {D : ℕ} (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) (a : Option (Fin D)) :
    (exactPrepareMatrix w amp) a none
      = exactPhase (amp a) * (rationalWeightTarget w a : ℂ) := by
  have hid : idealWeightPrepare w *ᵥ Qatlib.Foundations.PureStateMath.Ket none = rationalWeightTarget w :=
    (rational_weight_ideal_preparation_exact D w hw hm).2.1
  have hcol : (idealWeightPrepare w *ᵥ (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))) a
      = (idealWeightPrepare w) a none := by
    simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
    rw [Finset.sum_eq_single none]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hb
      exact absurd (Finset.mem_univ none) hb
  rw [hid] at hcol
  have hop : (exactPrepareMatrix w amp) a none
      = exactPhase (amp a) * (idealWeightPrepare w) a none := by
    simp only [exactPrepareMatrix, exactPhaseDiagonal, Matrix.diagonal_mul]
  exact hop.trans (congrArg _ hcol.symm)

/-- The squared modulus of each entry in the exact preparation column is its weight divided by
the total weight mass. -/
theorem exactPrepareColumn_sq {D : ℕ} (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) (a : Option (Fin D)) :
    starRingEnd ℂ ((exactPrepareMatrix w amp) a none)
      * (exactPrepareMatrix w amp) a none
      = ((w a / rationalWeightMass w : ℚ) : ℂ) := by
  have hphase : ‖exactPhase (amp a)‖ = 1 := by
    by_cases hz : amp a = ratZero
    · rw [hz]
      exact exactPhase_zero
    · exact exactPhase_norm (amp a) hz
  have hone : starRingEnd ℂ (exactPhase (amp a)) * exactPhase (amp a) = 1 :=
    star_mul_self_of_norm_one hphase
  have hnnsq : (0 : ℝ) ≤ ((w a / rationalWeightMass w : ℚ) : ℝ) := by
    exact_mod_cast div_nonneg (hw a) hm.le
  have hstar : starRingEnd ℂ ((rationalWeightTarget w a : ℂ))
      = (rationalWeightTarget w a : ℂ) := by
    have hdef : (rationalWeightTarget w a : ℂ)
        = Complex.ofReal (Real.sqrt ((w a / rationalWeightMass w : ℚ) : ℝ)) := rfl
    rw [hdef]
    exact Complex.conj_ofReal _
  have hsq : (rationalWeightTarget w a : ℂ) * (rationalWeightTarget w a : ℂ)
      = ((w a / rationalWeightMass w : ℚ) : ℂ) := by
    have hdef : (rationalWeightTarget w a : ℂ)
        = Complex.ofReal (Real.sqrt ((w a / rationalWeightMass w : ℚ) : ℝ)) := rfl
    rw [hdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hnnsq]
    exact Complex.ofReal_ratCast _
  rw [exactPrepareColumn w amp hw hm a, map_mul (starRingEnd ℂ), hstar]
  have rearr : starRingEnd ℂ (exactPhase (amp a)) * (rationalWeightTarget w a : ℂ)
      * (exactPhase (amp a) * (rationalWeightTarget w a : ℂ))
    = (starRingEnd ℂ (exactPhase (amp a)) * exactPhase (amp a))
      * ((rationalWeightTarget w a : ℂ) * (rationalWeightTarget w a : ℂ)) := by
    ring
  rw [rearr, hone, one_mul, hsq]

/-- Each entry of the extracted preparation-selector sandwich is the sum of selected entries
weighted by squared preparation-column amplitudes. -/
theorem lcuSandwich_entry {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix (Option (Fin D)) (Option (Fin D)) ℂ)
    (U : Option (Fin D) → Matrix X X ℂ) (x y : X) :
    blockNone (TensorGate Pᴴ 1 * blockSelect U * TensorGate P 1) x y
      = ∑ a, starRingEnd ℂ (P a none) * P a none * U a x y := by
  have hleft : ∀ (i k : Option (Fin D)) (z : X),
      (TensorGate Pᴴ (1 : Matrix X X ℂ)) (i, x) (k, z)
        = starRingEnd ℂ (P k i) * (if x = z then 1 else 0) := by
    intro i k z
    rw [Qatlib.Foundations.PureStateMath.tensorGate_apply, Matrix.one_apply,
        Matrix.conjTranspose_apply]
    rfl
  have hright : ∀ (b : Option (Fin D)) (t : X),
      (TensorGate P (1 : Matrix X X ℂ)) (b, t) (none, y)
        = P b none * (if t = y then 1 else 0) := by
    intro b t
    rw [Qatlib.Foundations.PureStateMath.tensorGate_apply, Matrix.one_apply]
  have hinner2 : ∀ (a : Option (Fin D)) (z : X),
      (∑ b : Option (Fin D), ∑ t : X,
          (starRingEnd ℂ (P b none) * (if x = t then 1 else 0))
            * (if b = a then U b t z else 0))
        = starRingEnd ℂ (P a none) * U a x z := by
    intro a z
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single x]
      · simp
      · intro t _ ht
        rw [if_neg (Ne.symm ht)]
        ring
      · intro hx
        exact absurd (Finset.mem_univ x) hx
    · intro b _ hb
      rw [Finset.sum_eq_zero]
      intro t _
      rw [if_neg hb]
      ring
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have hz : ∀ a : Option (Fin D),
      (∑ z : X, ((∑ b : Option (Fin D), ∑ t : X,
            (starRingEnd ℂ (P b none) * (if x = t then 1 else 0))
              * (if b = a then U b t z else 0))
          * (P a none * (if z = y then 1 else 0))))
        = starRingEnd ℂ (P a none) * P a none * U a x y := by
    intro a
    calc ∑ z : X, ((∑ b : Option (Fin D), ∑ t : X,
            (starRingEnd ℂ (P b none) * (if x = t then 1 else 0))
              * (if b = a then U b t z else 0))
          * (P a none * (if z = y then 1 else 0)))
        = ∑ z : X, (starRingEnd ℂ (P a none) * U a x z)
            * (P a none * (if z = y then 1 else 0)) :=
          Finset.sum_congr rfl fun z _ => by rw [hinner2 a z]
      _ = starRingEnd ℂ (P a none) * P a none * U a x y := by
          rw [Finset.sum_eq_single y]
          · rw [if_pos (rfl : y = y), mul_one]
            ring
          · intro z _ hzy
            rw [if_neg hzy]
            ring
          · intro hy
            exact absurd (Finset.mem_univ y) hy
  simp only [blockNone, Matrix.mul_apply, Fintype.sum_prod_type, blockSelect, hleft, hright]
  exact Finset.sum_congr rfl fun a _ => hz a

/-- The exact preparation-selector sandwich has `none` block equal to the sum of the selected
operators weighted by normalized rational weights. -/
theorem lcuTopBlock_exact {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) :
    blockNone (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)
      = ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a := by
  funext x y
  have hR : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) x y
      = ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) * U a x y := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [lcuSandwich_entry, hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [exactPrepareColumn_sq w amp hw hm a]

/-- The approximate sandwich block differs from the normalized weighted operator sum by at most
`64 * (D + 1) / 2^k`. -/
theorem lcuTopBlock_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (TensorGate (prepareMatrix k w amp)ᴴ 1 * blockSelect U
        * TensorGate (prepareMatrix k w amp) 1)
      - ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a‖
      ≤ 64 * (D + 1) / 2 ^ k := by
  have hsplit : blockNone (TensorGate (prepareMatrix k w amp)ᴴ 1 * blockSelect U
        * TensorGate (prepareMatrix k w amp) 1)
      - ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a
      = blockNone ((TensorGate (prepareMatrix k w amp)ᴴ 1 * blockSelect U
          * TensorGate (prepareMatrix k w amp) 1)
        - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
          * TensorGate (exactPrepareMatrix w amp) 1)) := by
    conv_lhs => rw [← lcuTopBlock_exact w amp hw hm U]
    funext x y
    simp [blockNone, Matrix.sub_apply]
  rw [hsplit]
  exact (blockNone_norm_le _).trans
    (lcuBlock_error k w amp hw hm _ (blockSelect_unitary hU))

/-- Precision `precisionFor D (ε / 2)` makes the approximate sandwich block error at most `ε`. -/
theorem lcuTopBlock_error_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (TensorGate (prepareMatrix (precisionFor D (ε / 2)) w amp)ᴴ 1
        * blockSelect U
        * TensorGate (prepareMatrix (precisionFor D (ε / 2)) w amp) 1)
      - ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a‖
      ≤ (ε : ℝ) := by
  have h := lcuTopBlock_error (precisionFor D (ε / 2)) w amp hw hm U hU
  have hb := prepError_le_epsilon (D := D) (ε / 2) (half_pos hε)
  have hcast : ((ε / 2 : ℚ) : ℝ) = (ε : ℝ) / 2 := by
    push_cast
    ring
  have hc : (0 : ℝ) < 2 ^ precisionFor D (ε / 2) := by positivity
  have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 2) : ℝ)
      = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 2) : ℝ)) := by
    field_simp
    ring
  linarith

/-- The `none` block of the evaluated linear-combination word approximates the normalized
weighted operator sum within `64 * (D + 1) / 2^k`. -/
theorem lcuWord_topBlock_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (evaluate 1 (lcuBlockWord k w amp (blockSelect U)))
      - ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a‖
      ≤ 64 * (D + 1) / 2 ^ k := by
  rw [lcuBlockWord_eval]
  exact lcuTopBlock_error k w amp hw hm U hU

/-- The evaluated linear-combination word has `none` block error at most `ε` at precision
`precisionFor D (ε / 2)`. -/
theorem lcuWord_topBlock_error_epsilon {D : ℕ} {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (ε : ℚ) (hε : 0 < ε)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (evaluate 1
          (lcuBlockWord (precisionFor D (ε / 2)) w amp (blockSelect U)))
      - ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a‖
      ≤ (ε : ℝ) := by
  rw [lcuBlockWord_eval]
  exact lcuTopBlock_error_epsilon ε hε w amp hw hm U hU

/-- The data state obtained by restricting the control register to `none`, without
renormalization. -/
def cleanBranch {D : ℕ} {X : Type*}
    (u : QState (Option (Fin D) × X)) : QState X := fun x => u (none, x)

/-- The probability weight of the `none` control branch equals the squared Euclidean norm of
`cleanBranch`. -/
theorem measureProb_none_branch {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (u : QState (Option (Fin D) × X)) :
    MeasureProb u (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      = ‖stateVector (cleanBranch u)‖ ^ 2 := by
  rw [stateVector_norm_sq]
  simp only [MeasureProb, BornProb, cleanBranch, Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single none]
  · exact Finset.sum_congr rfl fun x _ => by simp
  · intro a _ ha
    simp [ha]
  · intro hn
    exact absurd (Finset.mem_univ none) hn

/-- The clean branch of a matrix acting on a `none`-initialized control equals its `none` block
acting on the data state. -/
theorem lcuCleanBranch {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) (ψ : QState X) :
    cleanBranch (M *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      = blockNone M *ᵥ ψ := by
  funext x
  simp only [cleanBranch, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    blockNone, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.TensorState,
    Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single none]
  · simp
  · intro a _ ha
    simp [ha]
  · intro hn
    exact absurd (Finset.mem_univ none) hn

/-- The exact preparation sandwich of a selector of unitaries is unitary. -/
theorem lcuSandwichExact_unitary {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
  have h1 : (1 : Matrix X X ℂ) ∈ Matrix.unitaryGroup X ℂ := by simp
  have hE : exactPrepareMatrix w amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ :=
    exactPrepareMatrix_unitary w amp hw hm
  have hL : TensorGate (exactPrepareMatrix w amp)ᴴ (1 : Matrix X X ℂ)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
    have hAdj := adjoint_unitary (tensorGate_unitary hE h1)
    rwa [tensorGate_conjTranspose, Matrix.conjTranspose_one] at hAdj
  have hR : TensorGate (exactPrepareMatrix w amp) (1 : Matrix X X ℂ)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    tensorGate_unitary hE h1
  exact (Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem
    ((Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem hL (blockSelect_unitary hU)) hR

/-- The clean branch of the exact linear-combination sandwich is the normalized weighted
operator sum applied to the data state. -/
theorem lcuExact_apply {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (ψ : QState X) :
    cleanBranch ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      = (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ := by
  rw [lcuCleanBranch, lcuTopBlock_exact w amp hw hm U]

/-- The normalized nonnegative weighted sum of the selected unitaries has matrix norm at most
one. -/
theorem lcuCombination_norm_le {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a‖ ≤ 1 := by
  rw [← lcuTopBlock_exact w amp hw hm U]
  exact (blockNone_norm_le _).trans
    (le_of_eq (l2_norm_unitary_eq_one (lcuSandwichExact_unitary w amp hw hm U hU)))

/-- The clean branch of the evaluated linear-combination word approximates the weighted operator
action with error at most `64 * (D + 1) / 2^k` times the input norm. -/
theorem lcuWord_apply_state {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) :
    ‖stateVector (cleanBranch (evaluate 1 (lcuBlockWord k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)‖
      ≤ 64 * (D + 1) / 2 ^ k * ‖stateVector ψ‖ := by
  rw [lcuCleanBranch]
  have hsub : stateVector
        (blockNone (evaluate 1 (lcuBlockWord k w amp (blockSelect U))) *ᵥ ψ)
        - stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)
      = stateVector ((blockNone (evaluate 1 (lcuBlockWord k w amp (blockSelect U)))
            - ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ) := by
    simp [stateVector, WithLp.toLp_sub, Matrix.sub_mulVec]
  rw [hsub]
  have hn := stateVector_mulVec_norm_le
    (blockNone (evaluate 1 (lcuBlockWord k w amp (blockSelect U)))
      - ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) ψ
  refine hn.trans ?_
  exact mul_le_mul_of_nonneg_right (lcuWord_topBlock_error k w amp hw hm U hU)
    (norm_nonneg (stateVector ψ))

/-- For normalized input, precision `precisionFor D (ε / 2)` gives clean-branch state error at
most `ε`. -/
theorem lcuWord_apply_state_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) (U : Option (Fin D) → Matrix X X ℂ)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) (ψ : QState X)
    (hψ : ‖stateVector ψ‖ = 1) :
    ‖stateVector (cleanBranch (evaluate 1
          (lcuBlockWord (precisionFor D (ε / 2)) w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)‖
      ≤ (ε : ℝ) := by
  have h := lcuWord_apply_state (precisionFor D (ε / 2)) w amp hw hm U hU ψ
  have hb := prepError_le_epsilon (D := D) (ε / 2) (half_pos hε)
  rw [hψ, mul_one] at h
  have hcast : ((ε / 2 : ℚ) : ℝ) = (ε : ℝ) / 2 := by
    push_cast
    ring
  have hc : (0 : ℝ) < 2 ^ precisionFor D (ε / 2) := by positivity
  have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 2) : ℝ)
      = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 2) : ℝ)) := by
    field_simp
    ring
  linarith

/-- For normalized states at Euclidean distance at most `δ`, any specified basis-event
probabilities differ by at most `2 * δ`. -/
private theorem born_deviation {I : Type*} [Fintype I] [DecidableEq I]
    (v u : QState I) (S : Finset I)
    (hv : ‖stateVector v‖ = 1) (hu : ‖stateVector u‖ = 1)
    {δ : ℝ} (h : ‖stateVector v - stateVector u‖ ≤ δ) :
    |MeasureProb v S - MeasureProb u S| ≤ 2 * δ := by
  have hmp := measureProb_sub_le_l2 v u S
  have hE1 : ‖toEuclidean_fromVec v‖ = 1 := hv
  have hE2 : ‖toEuclidean_fromVec u‖ = 1 := hu
  have hE3 : ‖toEuclidean_fromVec (v - u)‖
      = ‖stateVector v - stateVector u‖ := by
    simp [toEuclidean_fromVec, stateVector, WithLp.toLp_sub]
  rw [hE1, hE2, hE3] at hmp
  rw [show (1 : ℝ) + 1 = 2 from by norm_num] at hmp
  exact hmp.trans (mul_le_mul_of_nonneg_left h (by norm_num))

/-- The `none`-branch probability of the linear-combination word differs from the ideal squared
output norm by at most `128 * (D + 1) / 2^k`. -/
theorem lcuBorn_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    |MeasureProb (evaluate 1 (lcuBlockWord k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)‖ ^ 2|
      ≤ 128 * (D + 1) / 2 ^ k := by
  rw [lcuBlockWord_eval]
  have hPu := measureProb_none_branch ((TensorGate (exactPrepareMatrix w amp)ᴴ 1
    * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
    TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
  rw [lcuCleanBranch, lcuTopBlock_exact w amp hw hm U] at hPu
  have hsandU : TensorGate (prepareMatrix k w amp)ᴴ (1 : Matrix X X ℂ) * blockSelect U
        * TensorGate (prepareMatrix k w amp) 1
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
    rw [← lcuBlockWord_eval]
    exact (lcuBlockWord_wellFormed k w amp hw _ (blockSelect_unitary hU)).evaluate_unitary
      (Submonoid.one_mem _)
  have hv1 : ‖stateVector ((TensorGate (prepareMatrix k w amp)ᴴ (1 : Matrix X X ℂ)
        * blockSelect U * TensorGate (prepareMatrix k w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    rw [unitary_mulVec_stateVector_norm _ hsandU _]
    have hT : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
        = ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ * ‖stateVector ψ‖ :=
      tensorState_l2_norm _ _
    rw [hT, stateVector_ket_none_norm, hψ, mul_one]
  have hu1 : ‖stateVector ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    rw [unitary_mulVec_stateVector_norm _ (lcuSandwichExact_unitary w amp hw hm U hU) _]
    have hT : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
        = ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ * ‖stateVector ψ‖ :=
      tensorState_l2_norm _ _
    rw [hT, stateVector_ket_none_norm, hψ, mul_one]
  have hvu : ‖stateVector ((TensorGate (prepareMatrix k w amp)ᴴ (1 : Matrix X X ℂ)
        * blockSelect U * TensorGate (prepareMatrix k w amp) 1) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      - stateVector ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
          * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
    ≤ 64 * (D + 1) / 2 ^ k :=
    lcuUncompute_clean k w amp hw hm (blockSelect U) (blockSelect_unitary hU) ψ hψ
  have hd := born_deviation
    ((TensorGate (prepareMatrix k w amp)ᴴ (1 : Matrix X X ℂ) * blockSelect U
      * TensorGate (prepareMatrix k w amp) 1) *ᵥ
      TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
    ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
      * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
      TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
    (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none)) hv1 hu1 hvu
  rw [← hPu]
  have hsplit : (2 : ℝ) * (64 * ((D : ℝ) + 1) / 2 ^ k)
      = 128 * ((D : ℝ) + 1) / 2 ^ k := by ring
  linarith

/-- Precision `precisionFor D (ε / 4)` bounds the `none`-branch probability error by `ε` for
normalized input. -/
theorem lcuBorn_none_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) (U : Option (Fin D) → Matrix X X ℂ)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) (ψ : QState X)
    (hψ : ‖stateVector ψ‖ = 1) :
    |MeasureProb (evaluate 1
          (lcuBlockWord (precisionFor D (ε / 4)) w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)‖ ^ 2|
      ≤ (ε : ℝ) := by
  have h := lcuBorn_none (precisionFor D (ε / 4)) w amp hw hm U hU ψ hψ
  have hb := prepError_le_epsilon (D := D) (ε / 4) (div_pos hε four_pos)
  have hcast : ((ε / 4 : ℚ) : ℝ) = (ε : ℝ) / 4 := by
    push_cast
    ring
  have hc : (0 : ℝ) < 2 ^ precisionFor D (ε / 4) := by positivity
  have hsplit : 128 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 4) : ℝ)
      = 4 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 4) : ℝ)) := by
    field_simp
    ring
  linarith

/-- The adjoint word of the preparation-selector-uncomputation circuit. -/
noncomputable def lcuBlockWordAdjoint {D : ℕ} {X : Type*} [DecidableEq X] (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    List (AdjointStep (Option (Fin D) × X)) :=
  adjointCircuit (lcuBlockWord k w amp S)

/-- The adjoint linear-combination word evaluates to the conjugate transpose of the preparation
sandwich. -/
theorem lcuBlockWordAdjoint_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (lcuBlockWordAdjoint k w amp S)
      = (TensorGate (prepareMatrix k w amp)ᴴ 1 * S
          * TensorGate (prepareMatrix k w amp) 1)ᴴ := by
  rw [lcuBlockWordAdjoint, evaluate_adjointCircuit, lcuBlockWord_eval]

/-- The adjoint linear-combination word is well formed for nonnegative weights and a unitary
selector. -/
theorem lcuBlockWordAdjoint_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (lcuBlockWordAdjoint k w amp S) :=
  (lcuBlockWord_wellFormed k w amp hw S hS).adjointCircuit

/-- The adjoint linear-combination word has `2 * (D + 1) + 1` gates and zero queries. -/
theorem lcuBlockWordAdjoint_counts {D : ℕ} {X : Type*} [DecidableEq X] (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    adjointGateCount (lcuBlockWordAdjoint k w amp S) = 2 * (D + 1) + 1 ∧
      adjointQueryCount (lcuBlockWordAdjoint k w amp S) = 0 := by
  simp only [lcuBlockWordAdjoint, adjointGateCount_adjointCircuit,
    adjointQueryCount_adjointCircuit]
  exact lcuBlockWord_counts k w amp S

/-- A linear-combination word followed by its adjoint is a well-formed identity circuit with
twice the original gate count and zero queries. -/
theorem lcuBlockWordRoundTrip {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (lcuBlockWord k w amp S
        ++ lcuBlockWordAdjoint k w amp S) ∧
      evaluate 1 (lcuBlockWord k w amp S ++ lcuBlockWordAdjoint k w amp S) = 1 ∧
      adjointGateCount (lcuBlockWord k w amp S ++ lcuBlockWordAdjoint k w amp S)
        = 2 * (2 * (D + 1) + 1) ∧
      adjointQueryCount (lcuBlockWord k w amp S ++ lcuBlockWordAdjoint k w amp S)
        = 0 := by
  obtain ⟨hwf, hev, hqc, hgc⟩ := adjointCircuit_roundTrip 1 (lcuBlockWord k w amp S)
    (show (1 : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
        ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ by simp)
    (lcuBlockWord_wellFormed k w amp hw S hS)
  obtain ⟨hgW, hqW⟩ := lcuBlockWord_counts k w amp S
  simp only [lcuBlockWordAdjoint]
  refine ⟨hwf, hev, ?_, ?_⟩
  · rw [hgc, hgW]
  · rw [hqc, hqW]

/-- The concatenation of `m` copies of the linear-combination circuit word. -/
noncomputable def lcuWordRepeat {D : ℕ} {X : Type*} [DecidableEq X] (m : ℕ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    List (AdjointStep (Option (Fin D) × X)) :=
  match m with
  | 0 => []
  | m + 1 => lcuWordRepeat m k w amp S ++ lcuBlockWord k w amp S

/-- Evaluating `m` repeated linear-combination words gives the `m`th power of the single-word
evaluation. -/
theorem lcuWordRepeat_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (lcuWordRepeat m k w amp S)
      = (evaluate 1 (lcuBlockWord k w amp S)) ^ m := by
  induction m with
  | zero => simp [lcuWordRepeat, evaluate]
  | succ m ih =>
      simp only [lcuWordRepeat, evaluate_append, ih, pow_succ]

/-- Repeating the linear-combination word `m` times uses `m * (2 * (D + 1) + 1)` gates and zero
queries. -/
theorem lcuWordRepeat_counts {D : ℕ} {X : Type*} [DecidableEq X] (m : ℕ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    adjointGateCount (lcuWordRepeat m k w amp S) = m * (2 * (D + 1) + 1) ∧
      adjointQueryCount (lcuWordRepeat m k w amp S) = 0 := by
  obtain ⟨hgW, hqW⟩ := lcuBlockWord_counts k w amp S
  induction m with
  | zero => simp [lcuWordRepeat, adjointGateCount, adjointQueryCount]
  | succ m ih =>
      obtain ⟨hg, hq⟩ := ih
      simp only [lcuWordRepeat, adjointGateCount_append, adjointQueryCount_append]
      refine ⟨by rw [hg, hgW]; ring, by rw [hq, hqW]⟩

/-- Repeated linear-combination words are well formed for nonnegative weights and a unitary
selector. -/
theorem lcuWordRepeat_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (lcuWordRepeat m k w amp S) := by
  induction m with
  | zero => exact WellFormedAdjointCircuit.nil
  | succ m ih =>
      simp only [lcuWordRepeat]
      exact ih.append (lcuBlockWord_wellFormed k w amp hw S hS)

/-- Left multiplication by a unitary matrix preserves the matrix norm. -/
private theorem unitary_mul_norm_eq {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
    (M : Matrix H H ℂ) (hM : M ∈ Matrix.unitaryGroup H ℂ) (N : Matrix H H ℂ) :
    ‖M * N‖ = ‖N‖ := by
  have h1 : ‖M * N‖ ≤ ‖N‖ := by
    have hle := Matrix.l2_opNorm_mul M N
    rwa [l2_norm_unitary_eq_one hM, one_mul] at hle
  have h2 : ‖N‖ ≤ ‖M * N‖ := by
    have hMM : Mᴴ * M = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hM
    calc ‖N‖ = ‖Mᴴ * (M * N)‖ := by rw [← Matrix.mul_assoc, hMM, one_mul]
      _ ≤ ‖Mᴴ‖ * ‖M * N‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖M * N‖ := by rw [l2_norm_unitary_eq_one (adjoint_unitary hM), one_mul]
  exact le_antisymm h1 h2

/-- Sandwiching a unitary selector between exact preparation and its inverse produces a unitary
matrix. -/
theorem lcuSandwich_unitary {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
        * TensorGate (exactPrepareMatrix w amp) 1
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
  have h1 : (1 : Matrix X X ℂ) ∈ Matrix.unitaryGroup X ℂ := by simp
  have hE : exactPrepareMatrix w amp ∈ Matrix.unitaryGroup (Option (Fin D)) ℂ :=
    exactPrepareMatrix_unitary w amp hw hm
  have hL : TensorGate (exactPrepareMatrix w amp)ᴴ (1 : Matrix X X ℂ)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
    have hAdj := adjoint_unitary (tensorGate_unitary hE h1)
    rwa [tensorGate_conjTranspose, Matrix.conjTranspose_one] at hAdj
  exact (Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem
    ((Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem hL hS)
    (tensorGate_unitary hE h1)

/-- The `m`th powers of the approximate and exact preparation sandwiches differ in norm by at
most `m * (64 * (D + 1) / 2^k)`. -/
theorem lcuWord_power_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (m : ℕ) (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖(evaluate 1 (lcuBlockWord k w amp S)) ^ m
        - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) ^ m‖
      ≤ m * (64 * (D + 1) / 2 ^ k) := by
  have hW : evaluate 1 (lcuBlockWord k w amp S)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (lcuBlockWord_wellFormed k w amp hw S hS).evaluate_unitary (Submonoid.one_mem _)
  have hE := lcuSandwich_unitary w amp hw hm S hS
  have honeshot0 := lcuBlock_error k w amp hw hm S hS
  rw [← lcuBlockWord_eval] at honeshot0
  set A : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ :=
    evaluate 1 (lcuBlockWord k w amp S) with hA
  set B : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ :=
    TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
      * TensorGate (exactPrepareMatrix w amp) 1 with hB
  have honeshot := honeshot0
  induction m with
  | zero => simp
  | succ m ih =>
      have hdecomp : A ^ (m + 1) - B ^ (m + 1)
          = A ^ m * (A - B) + (A ^ m - B ^ m) * B := by
        rw [pow_succ, pow_succ]
        simp only [Matrix.mul_sub, Matrix.sub_mul]
        abel
      rw [hdecomp]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖A ^ m * (A - B)‖ = ‖A - B‖ :=
        unitary_mul_norm_eq _ (Submonoid.pow_mem _ hW m) _
      have h2 : ‖(A ^ m - B ^ m) * B‖ ≤ ‖A ^ m - B ^ m‖ := by
        have hle := Matrix.l2_opNorm_mul (A ^ m - B ^ m) B
        rwa [l2_norm_unitary_eq_one hE, mul_one] at hle
      rw [h1]
      have hconv : ((m + 1 : ℕ) : ℝ) * (64 * (D + 1) / 2 ^ k)
          = (m : ℝ) * (64 * (D + 1) / 2 ^ k)
            + 64 * (D + 1) / 2 ^ k := by
        push_cast
        ring
      rw [hconv]
      have hsum := add_le_add honeshot (h2.trans ih)
      linarith

/-- The bound `c ≤ e / (2 * (n + 1))` implies `(n + 1) * (2 * c) ≤ e`. -/
private theorem mul_two_div_le {c e : ℝ} {n : ℕ}
    (hb : c ≤ e / (2 * ((n : ℝ) + 1))) :
    ((n : ℝ) + 1) * (2 * c) ≤ e := by
  have hne : (2 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  calc ((n : ℝ) + 1) * (2 * c)
      = (2 * ((n : ℝ) + 1)) * c := by ring
    _ ≤ (2 * ((n : ℝ) + 1)) * (e / (2 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = e := mul_div_cancel₀ e hne

/-- Precision `precisionFor D (ε / (2 * (m + 1)))` bounds the error between the `(m + 1)`st
powers of approximate and exact sandwiches by `ε`. -/
theorem lcuWord_power_error_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖(evaluate 1 (lcuBlockWord (precisionFor D (ε / (2 * (m + 1)))) w amp S)) ^ (m + 1)
        - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) ^ (m + 1)‖
      ≤ (ε : ℝ) := by
  have h := lcuWord_power_error (m + 1) (precisionFor D (ε / (2 * (m + 1)))) w amp hw hm S hS
  have hb := prepError_le_epsilon (D := D) (ε / (2 * (m + 1))) (by positivity)
  have hcastE : ((ε / (2 * (m + 1)) : ℚ) : ℝ) = (ε : ℝ) / (2 * ((m : ℝ) + 1)) := by
    push_cast
    ring
  rw [hcastE] at hb
  have hsplit : 64 * ((D : ℝ) + 1)
        / (2 ^ precisionFor D (ε / (2 * (m + 1))) : ℝ)
      = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / (2 * (m + 1))) : ℝ)) := by
    field_simp
    ring
  refine h.trans ?_
  rw [hsplit, Nat.cast_succ]
  exact mul_two_div_le hb

/-- The evaluated `m`-fold linear-combination word approximates the `m`th power of the exact
sandwich with error at most `m * (64 * (D + 1) / 2^k)`. -/
theorem lcuWordRepeat_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (m : ℕ) (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (lcuWordRepeat m k w amp S)
        - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) ^ m‖
      ≤ m * (64 * (D + 1) / 2 ^ k) := by
  set_option maxHeartbeats 400000 in
  simp only [lcuWordRepeat_eval]
  exact lcuWord_power_error m k w amp hw hm S hS

set_option maxHeartbeats 400000 in

/-- The `(m + 1)`-fold word has matrix error at most `ε` when the precision allocates `ε / (2 *
(m + 1))` to preparation. -/
theorem lcuWordRepeat_error_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (lcuWordRepeat (m + 1) (precisionFor D (ε / (2 * (m + 1)))) w amp S)
        - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) ^ (m + 1)‖
      ≤ (ε : ℝ) := by
  rw [lcuWordRepeat_eval]
  exact lcuWord_power_error_epsilon m ε hε w amp hw hm S hS

/-- On a state `φ`, the repeated-word error is at most `m * (64 * (D + 1) / 2^k)` times the
Euclidean norm of `φ`. -/
theorem lcuWordRepeat_state_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ)
    (φ : QState (Option (Fin D) × X)) :
    ‖stateVector (evaluate 1 (lcuWordRepeat m k w amp S) *ᵥ φ)
        - stateVector ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) ^ m *ᵥ φ)‖
      ≤ m * (64 * (D + 1) / 2 ^ k) * ‖stateVector φ‖ := by
  simp only [lcuWordRepeat_eval]
  have hsub : stateVector ((evaluate 1 (lcuBlockWord k w amp S)) ^ m *ᵥ φ)
        - stateVector ((TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1) ^ m *ᵥ φ)
      = stateVector (((evaluate 1 (lcuBlockWord k w amp S)) ^ m
            - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                * TensorGate (exactPrepareMatrix w amp) 1) ^ m) *ᵥ φ) := by
    simp [stateVector, WithLp.toLp_sub, Matrix.sub_mulVec]
  rw [hsub]
  have hn := stateVector_mulVec_norm_le
    ((evaluate 1 (lcuBlockWord k w amp S)) ^ m
      - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
          * TensorGate (exactPrepareMatrix w amp) 1) ^ m) φ
  refine hn.trans ?_
  exact mul_le_mul_of_nonneg_right (lcuWord_power_error m k w amp hw hm S hS)
    (norm_nonneg (stateVector φ))

/-- The diagonal reflection that fixes control index `none` and negates all other control
indices. -/
def reflectNone {D : ℕ} {X : Type*} [DecidableEq X] :
    Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ :=
  Matrix.diagonal fun p : Option (Fin D) × X => if p.1 = none then (1 : ℂ) else -1

/-- The reflection about the `none` control subspace is unitary. -/
theorem reflectNone_unitary {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] :
    reflectNone (D := D) (X := X) ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  by_cases h : p.1 = none
  · simp [h]
  · simp [h]

/-- The reflection about the `none` control subspace squares to the identity. -/
theorem reflectNone_sq {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] :
    reflectNone (D := D) (X := X) * reflectNone = 1 := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    by_cases h : p.1 = none
    · simp [reflectNone, h]
    · simp [reflectNone, h]
  · simp [reflectNone, hpq]

/-- The reflection multiplies a basis-controlled tensor state by one for control `none` and by
minus one otherwise. -/
theorem reflectNone_tensor_apply {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (a : Option (Fin D)) (φ : QState X) :
    reflectNone *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket a) φ
      = (if a = none then (1 : ℂ) else -1) • TensorState (Qatlib.Foundations.PureStateMath.Ket a) φ := by
  have hd : ∀ (v : QState (Option (Fin D) × X)) (b : Option (Fin D)) (y : X),
      (reflectNone *ᵥ v) (b, y) = (if b = none then (1 : ℂ) else -1) * v (b, y) := by
    intro v b y
    simp only [reflectNone, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (b, y)]
    · simp
    · intro q _ hq
      have hq' : (b, y) ≠ q := fun h => hq h.symm
      simp [hq']
    · intro hq
      exact absurd (Finset.mem_univ (b, y)) hq
  funext p
  obtain ⟨b, y⟩ := p
  rw [hd _ b y, Pi.smul_apply, smul_eq_mul]
  by_cases hba : b = a
  · rw [hba]
  · have hket : (TensorState (Qatlib.Foundations.PureStateMath.Ket a) φ) (b, y) = if b = a then φ y else 0 := by
      simp [Qatlib.Foundations.PureStateMath.TensorState,
          Qatlib.Foundations.PureStateMath.Ket]
    rw [hket, if_neg hba]
    simp

/-- The single-gate circuit word implementing `reflectNone`. -/
noncomputable def reflectNoneWord {D : ℕ} {X : Type*} [DecidableEq X] :
    List (AdjointStep (Option (Fin D) × X)) := [.gate reflectNone]

/-- The reflection word evaluates to `reflectNone`. -/
theorem reflectNoneWord_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] :
    evaluate 1 (reflectNoneWord (D := D) (X := X)) = reflectNone := by
  simp [reflectNoneWord, evaluate, instructionMatrix]

/-- The reflection word has one gate and zero queries. -/
theorem reflectNoneWord_counts {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] :
    adjointGateCount (reflectNoneWord (D := D) (X := X)) = 1 ∧
      adjointQueryCount (reflectNoneWord (D := D) (X := X)) = 0 := by
  simp [reflectNoneWord, adjointGateCount, adjointQueryCount]

/-- The single-gate reflection word is well formed. -/
theorem reflectNoneWord_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] :
    WellFormedAdjointCircuit (reflectNoneWord (D := D) (X := X)) := by
  simp [reflectNoneWord, reflectNone_unitary]

/-- The block of a matrix with output control `none` and input control `a`. -/
def rowBlock {D : ℕ} {X : Type*} (a : Option (Fin D))
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) : Matrix X X ℂ :=
  fun x z => M (none, x) (a, z)

/-- The block of a matrix with output control `a` and input control `none`. -/
def colBlock {D : ℕ} {X : Type*} (a : Option (Fin D))
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) : Matrix X X ℂ :=
  fun z y => M (a, z) (none, y)

/-- The `none` block of the identity matrix is the identity on the data register. -/
theorem blockNone_one {D : ℕ} {X : Type*} [DecidableEq X] :
    blockNone (1 : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) = 1 := by
  ext x y
  simp [blockNone, Matrix.one_apply]

/-- Extracting the `none` block commutes with conjugate transpose. -/
theorem blockNone_adjoint {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    blockNone Mᴴ = (blockNone M)ᴴ := by
  ext x y
  simp [blockNone, Matrix.conjTranspose_apply]

/-- A row block of a conjugate transpose is the conjugate transpose of the corresponding column
block. -/
theorem rowBlock_adjoint {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) (a : Option (Fin D)) :
    rowBlock a Mᴴ = (colBlock a M)ᴴ := by
  ext x y
  simp [rowBlock, colBlock, Matrix.conjTranspose_apply]

/-- The `none` block of a product is the product of its `none` blocks plus the sum over the
other intermediate control indices. -/
theorem blockNone_mul_expand {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M N : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    blockNone (M * N) = blockNone M * blockNone N
      + ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
          rowBlock a M * colBlock a N := by
  have hfilter : ∀ (F : Option (Fin D) → ℂ),
      ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none), F a
        = ∑ i : Fin D, F (some i) := by
    intro F
    have himg : (Finset.univ : Finset (Fin D)).image some
        = Finset.univ.filter (fun a : Option (Fin D) => a ≠ none) := by
      ext a
      cases a with
      | none => simp
      | some i => simp
    rw [← himg, Finset.sum_image (fun i _ j _ h => Option.some.inj h)]
  ext x y
  simp only [Matrix.add_apply, Matrix.sum_apply]
  have hL : blockNone (M * N) x y
      = ∑ a : Option (Fin D), ∑ z : X, M (none, x) (a, z) * N (a, z) (none, y) := by
    simp [blockNone, Matrix.mul_apply, Fintype.sum_prod_type]
  have hR1 : (blockNone M * blockNone N) x y
      = ∑ z : X, M (none, x) (none, z) * N (none, z) (none, y) := by
    simp [blockNone, Matrix.mul_apply]
  have hR2 : ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
      (rowBlock a M * colBlock a N) x y
      = ∑ i : Fin D, ∑ z : X, M (none, x) (some i, z) * N (some i, z) (none, y) := by
    rw [hfilter (fun a => (rowBlock a M * colBlock a N) x y)]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hL, hR1, hR2, Fintype.sum_option]

/-- For a unitary matrix, the squared column blocks associated with input control `none` sum to
the identity. -/
theorem unitary_noneCol_sum {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    blockNone Uᴴ * blockNone U
      + ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
          (colBlock a U)ᴴ * colBlock a U
      = 1 := by
  have hUU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  have hexp := blockNone_mul_expand Uᴴ U
  rw [hUU, blockNone_one] at hexp
  have hsum2 : ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
      (colBlock a U)ᴴ * colBlock a U
      = ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
          rowBlock a Uᴴ * colBlock a U :=
    Finset.sum_congr rfl fun a _ => by rw [← rowBlock_adjoint U a]
  rw [hsum2, hexp]

/-- Left multiplication by `reflectNone` preserves every matrix row with control index `none`. -/
theorem reflectNone_mul_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (q : Option (Fin D) × X) (x : X) :
    (reflectNone (D := D) (X := X) * M) (none, x) q = M (none, x) q := by
  simp only [Matrix.mul_apply, reflectNone, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (none, x)]
  · simp
  · intro s _ hs
    rw [if_neg (fun h => absurd h.symm hs)]
    simp
  · intro hs
    exact absurd (Finset.mem_univ (none, x)) hs

/-- Left multiplication by `reflectNone` preserves the `none` block. -/
theorem blockNone_reflectNone_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    blockNone (reflectNone (D := D) (X := X) * M) = blockNone M := by
  ext x y
  simp only [blockNone]
  rw [reflectNone_mul_noneRow]

/-- Left multiplication by `reflectNone` preserves each row block with output control `none`. -/
theorem reflectNone_rowBlock_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (a : Option (Fin D)) (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    rowBlock a (reflectNone (D := D) (X := X) * M) = rowBlock a M := by
  ext x z
  simp only [rowBlock]
  rw [reflectNone_mul_noneRow]

/-- Left multiplication by `reflectNone` negates column blocks whose output control index
differs from `none`. -/
theorem colBlock_reflectNone_mul {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (a : Option (Fin D)) (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (ha : a ≠ none) :
    colBlock a (reflectNone (D := D) (X := X) * M) = -colBlock a M := by
  ext z y
  have hd : ∀ p r, (reflectNone (D := D) (X := X) * M) p r
      = (if p.1 = none then (1 : ℂ) else -1) * M p r := by
    intro p r
    simp only [Matrix.mul_apply, reflectNone, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single p]
    · simp
    · intro s _ hs
      rw [if_neg (fun h => absurd h.symm hs)]
      simp
    · intro hs
      exact absurd (Finset.mem_univ p) hs
  simp only [colBlock, hd]
  rw [if_neg ha]
  simp [colBlock]

/-- For unitary `U`, the `none` block of `reflectNone * Uᴴ * reflectNone * U` equals `2 •
((blockNone U)ᴴ * blockNone U) - 1`. -/
theorem groverTopBlock_exact {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    blockNone (reflectNone (D := D) (X := X) * Uᴴ * reflectNone (D := D) (X := X) * U)
      = 2 • ((blockNone U)ᴴ * blockNone U) - 1 := by
  have hE : reflectNone (D := D) (X := X) * Uᴴ * reflectNone (D := D) (X := X) * U
      = (reflectNone (D := D) (X := X) * Uᴴ) * (reflectNone (D := D) (X := X) * U) := by rw [← Matrix.mul_assoc]
  rw [hE, blockNone_mul_expand, blockNone_reflectNone_noneRow Uᴴ,
    blockNone_reflectNone_noneRow U, blockNone_adjoint U]
  have hcol : ∀ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
      rowBlock a (reflectNone (D := D) (X := X) * Uᴴ) * colBlock a (reflectNone (D := D) (X := X) * U)
        = -((colBlock a U)ᴴ * colBlock a U) := by
    intro a ha
    rw [reflectNone_rowBlock_noneRow, rowBlock_adjoint,
      colBlock_reflectNone_mul a U (Finset.mem_filter.mp ha |>.2), Matrix.mul_neg]
  rw [Finset.sum_congr rfl hcol, Finset.sum_neg_distrib]
  have hsum := unitary_noneCol_sum U hU
  have hS : ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
      (colBlock a U)ᴴ * colBlock a U
      = 1 - blockNone Uᴴ * blockNone U := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum
  rw [hS]
  have h2 : blockNone Uᴴ * blockNone U + -(1 - blockNone Uᴴ * blockNone U)
      = 2 • (blockNone Uᴴ * blockNone U) - 1 := by
    rw [two_nsmul]
    abel
  exact h2

/-- The circuit word for one Grover round built from the linear-combination word, its adjoint,
and two control reflections. -/
noncomputable def groverWord {D : ℕ} {X : Type*} [DecidableEq X] (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    List (AdjointStep (Option (Fin D) × X)) :=
  reflectNoneWord ++ lcuBlockWordAdjoint k w amp S ++ reflectNoneWord
    ++ lcuBlockWord k w amp S

/-- The Grover word evaluates to the product of a control reflection, the adjoint
linear-combination evaluation, another reflection, and the original evaluation. -/
theorem groverWord_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (groverWord k w amp S)
      = reflectNone (D := D) (X := X) * (evaluate 1 (lcuBlockWord k w amp S))ᴴ * reflectNone
          * evaluate 1 (lcuBlockWord k w amp S) := by
  simp only [groverWord, evaluate_append, reflectNoneWord_eval,
    lcuBlockWordAdjoint_eval, lcuBlockWord_eval]

/-- One Grover word uses `2 * (2 * (D + 1) + 1) + 2` gates and zero queries. -/
theorem groverWord_counts {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    adjointGateCount (groverWord k w amp S) = 2 * (2 * (D + 1) + 1) + 2 ∧
      adjointQueryCount (groverWord k w amp S) = 0 := by
  obtain ⟨hgW, hqW⟩ := lcuBlockWord_counts k w amp S
  obtain ⟨hgI, hqI⟩ := lcuBlockWordAdjoint_counts k w amp S
  obtain ⟨hgR, hqR⟩ := reflectNoneWord_counts (D := D) (X := X)
  simp only [groverWord, adjointGateCount_append, adjointQueryCount_append]
  omega

/-- The Grover word is well formed for nonnegative weights and a unitary selector. -/
theorem groverWord_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (groverWord k w amp S) := by
  simp only [groverWord, WellFormedAdjointCircuit.append_iff]
  exact ⟨⟨⟨reflectNoneWord_wellFormed,
    lcuBlockWordAdjoint_wellFormed k w amp hw S hS⟩,
    reflectNoneWord_wellFormed⟩,
    lcuBlockWord_wellFormed k w amp hw S hS⟩

/-- The approximate Grover word differs from the exact-sandwich Grover round by at most `128 *
(D + 1) / 2^k` in matrix norm. -/
theorem grover_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (groverWord k w amp S)
        - reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
          * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
              * TensorGate (exactPrepareMatrix w amp) 1)‖
      ≤ 128 * (D + 1) / 2 ^ k := by
  have hR := reflectNone_unitary (D := D) (X := X)
  have hdiff : ‖evaluate 1 (lcuBlockWord k w amp S)
        - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)‖
      ≤ 64 * (D + 1) / 2 ^ k := by
    have h1 := lcuBlock_error k w amp hw hm S hS
    rw [← lcuBlockWord_eval] at h1
    exact h1
  have hUau : evaluate 1 (lcuBlockWord k w amp S)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (lcuBlockWord_wellFormed k w amp hw S hS).evaluate_unitary (Submonoid.one_mem _)
  have hUeu : TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
      * TensorGate (exactPrepareMatrix w amp) 1
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    lcuSandwich_unitary w amp hw hm S hS
  rw [groverWord_eval]
  have hdecomp :
      reflectNone (D := D) (X := X) * (evaluate 1 (lcuBlockWord k w amp S))ᴴ * reflectNone
          * evaluate 1 (lcuBlockWord k w amp S)
        - reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
          * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
              * TensorGate (exactPrepareMatrix w amp) 1)
      = reflectNone
          * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)
          * (reflectNone (D := D) (X := X) * evaluate 1 (lcuBlockWord k w amp S))
        + reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
          * (evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)) := by
    noncomm_ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖reflectNone
        * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
            - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)
        * (reflectNone (D := D) (X := X) * evaluate 1 (lcuBlockWord k w amp S))‖
      ≤ 64 * (D + 1) / 2 ^ k := by
    calc ‖reflectNone
          * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)
          * (reflectNone (D := D) (X := X) * evaluate 1 (lcuBlockWord k w amp S))‖
        ≤ ‖reflectNone
              * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
                  - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                      * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)‖
            * ‖reflectNone (D := D) (X := X) * evaluate 1 (lcuBlockWord k w amp S)‖ :=
            Matrix.l2_opNorm_mul _ _
      _ = ‖(evaluate 1 (lcuBlockWord k w amp S))ᴴ
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)ᴴ‖
            * ‖reflectNone (D := D) (X := X) * evaluate 1 (lcuBlockWord k w amp S)‖ := by
          rw [unitary_mul_norm_eq _ hR _]
      _ = ‖evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)‖
            * ‖reflectNone (D := D) (X := X) * evaluate 1 (lcuBlockWord k w amp S)‖ := by
          rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      _ = ‖evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)‖ * 1 := by
          rw [unitary_mul_norm_eq _ hR _, l2_norm_unitary_eq_one hUau]
      _ ≤ 64 * (D + 1) / 2 ^ k := by rw [mul_one]; exact hdiff
  have h2 : ‖reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
          * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
        * (evaluate 1 (lcuBlockWord k w amp S)
            - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                * TensorGate (exactPrepareMatrix w amp) 1))‖
      ≤ 64 * (D + 1) / 2 ^ k := by
    have hReU : reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
          * TensorGate (exactPrepareMatrix w amp) 1)ᴴ
        ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
      (Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem hR
        (adjoint_unitary hUeu)
    calc ‖reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
          * (evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1))‖
        ≤ ‖reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
              * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone‖
            * ‖evaluate 1 (lcuBlockWord k w amp S)
                - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                    * TensorGate (exactPrepareMatrix w amp) 1)‖ :=
            Matrix.l2_opNorm_mul _ _
      _ = 1 * ‖evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)‖ := by
          rw [unitary_mul_norm_eq _ hReU _, l2_norm_unitary_eq_one hR]
      _ ≤ 1 * (64 * (D + 1) / 2 ^ k) :=
          mul_le_mul_of_nonneg_left hdiff (by norm_num)
      _ ≤ 64 * (D + 1) / 2 ^ k := by norm_num
  have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ k : ℝ) + 64 * ((D : ℝ) + 1) / (2 ^ k : ℝ)
      = 128 * ((D : ℝ) + 1) / (2 ^ k : ℝ) := by
    rw [← add_div]
    congr 1
    ring
  linarith

/-- Precision `precisionFor D (ε / 4)` bounds the Grover word error by `ε`. -/
theorem grover_error_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (groverWord (precisionFor D (ε / 4)) w amp S)
        - reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
          * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
              * TensorGate (exactPrepareMatrix w amp) 1)‖
      ≤ (ε : ℝ) := by
  have h := grover_error (precisionFor D (ε / 4)) w amp hw hm S hS
  have hb := prepError_le_epsilon (D := D) (ε / 4) (by positivity)
  have hcastE : ((ε / 4 : ℚ) : ℝ) = (ε : ℝ) / 4 := by
    push_cast
    ring
  rw [hcastE] at hb
  refine h.trans ?_
  have hsplit : 128 * ((D : ℝ) + 1)
        / (2 ^ precisionFor D (ε / 4) : ℝ)
      = 4 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 4) : ℝ)) := by
    field_simp
    ring
  rw [hsplit]
  calc 4 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 4) : ℝ))
      ≤ 4 * ((ε : ℝ) / 4) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (ε : ℝ) := by ring

/-- The exact linear-combination Grover round has `none` block `2 • (Aᴴ * A) - 1`, where `A` is
the normalized weighted operator sum. -/
theorem lcuGroverTop_exact {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    blockNone (reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
      * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
          * TensorGate (exactPrepareMatrix w amp) 1))
      = 2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
          * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1 := by
  rw [groverTopBlock_exact _ (lcuSandwichExact_unitary w amp hw hm U hU),
    lcuTopBlock_exact w amp hw hm U]

/-- The `none` block of the approximate Grover word differs from `2 • (Aᴴ * A) - 1` by at most
`128 * (D + 1) / 2^k`. -/
theorem groverTop_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (evaluate 1 (groverWord k w amp (blockSelect U)))
        - (2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
              * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1)‖
      ≤ 128 * (D + 1) / 2 ^ k := by
  have hB := lcuGroverTop_exact w amp hw hm U hU
  have hsub :
      blockNone (evaluate 1 (groverWord k w amp (blockSelect U)))
          - (2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
              * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1)
        = blockNone (evaluate 1 (groverWord k w amp (blockSelect U))
            - (reflectNone (D := D) (X := X) * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
                * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectNone
              * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
                  * TensorGate (exactPrepareMatrix w amp) 1))) := by
    have hLin : ∀ M N : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ,
        blockNone (M - N) = blockNone M - blockNone N := by
      intro M N
      ext x y
      simp [blockNone, Matrix.sub_apply]
    rw [hLin, hB]
  rw [hsub]
  exact (blockNone_norm_le _).trans
    (grover_error k w amp hw hm (blockSelect U) (blockSelect_unitary hU))

/-- Precision `precisionFor D (ε / 4)` bounds the error in the Grover word's `none` block by
`ε`. -/
theorem groverTop_error_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) (U : Option (Fin D) → Matrix X X ℂ)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (evaluate 1 (groverWord (precisionFor D (ε / 4)) w amp (blockSelect U)))
        - (2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
              * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1)‖
      ≤ (ε : ℝ) := by
  have h := groverTop_error (precisionFor D (ε / 4)) w amp hw hm U hU
  have hb := prepError_le_epsilon (D := D) (ε / 4) (by positivity)
  have hcastE : ((ε / 4 : ℚ) : ℝ) = (ε : ℝ) / 4 := by
    push_cast
    ring
  rw [hcastE] at hb
  refine h.trans ?_
  have hsplit : 128 * ((D : ℝ) + 1)
        / (2 ^ precisionFor D (ε / 4) : ℝ)
      = 4 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 4) : ℝ)) := by
    field_simp
    ring
  rw [hsplit]
  calc 4 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 4) : ℝ))
      ≤ 4 * ((ε : ℝ) / 4) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (ε : ℝ) := by ring

/-- The clean branch of the Grover word approximates the action of `2 • (Aᴴ * A) - 1` with error
at most `128 * (D + 1) / 2^k` times the input norm. -/
theorem grover_state_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) :
    ‖stateVector (cleanBranch (evaluate 1 (groverWord k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - stateVector ((2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
              * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1) *ᵥ ψ)‖
      ≤ 128 * (D + 1) / 2 ^ k * ‖stateVector ψ‖ := by
  rw [lcuCleanBranch]
  have hsub : stateVector
        (blockNone (evaluate 1 (groverWord k w amp (blockSelect U))) *ᵥ ψ)
        - stateVector ((2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
              * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1) *ᵥ ψ)
      = stateVector ((blockNone (evaluate 1 (groverWord k w amp (blockSelect U)))
            - (2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
                * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1)) *ᵥ ψ) := by
    simp [stateVector, WithLp.toLp_sub, Matrix.sub_mulVec]
  rw [hsub]
  have hn := stateVector_mulVec_norm_le
    (blockNone (evaluate 1 (groverWord k w amp (blockSelect U)))
      - (2 • ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
          * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) - 1)) ψ
  refine hn.trans ?_
  exact mul_le_mul_of_nonneg_right (groverTop_error k w amp hw hm U hU)
    (norm_nonneg (stateVector ψ))

/-- The matrix embedding the data register into the control subspace indexed by `none`. -/
def cleanEmbed {D : ℕ} {X : Type*} [DecidableEq X] :
    Matrix (Option (Fin D) × X) X ℂ :=
  fun p y => if p = (none, y) then 1 else 0

/-- Right multiplication by `cleanEmbed` selects the columns whose control index is `none`. -/
theorem mul_cleanEmbed_apply {D : ℕ} {X Y : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix Y (Option (Fin D) × X) ℂ) (p : Y) (y : X) :
    (M * (cleanEmbed (D := D) (X := X))) p y = M p (none, y) := by
  simp only [Matrix.mul_apply, cleanEmbed]
  rw [Finset.sum_eq_single (none, y)]
  · simp
  · intro q _ hq
    rw [if_neg (fun h => hq h)]
    simp
  · intro h
    exact absurd (Finset.mem_univ (none, y)) h

/-- Left multiplication by `cleanEmbed` places a matrix in the rows with control index `none`
and fills the other rows with zero. -/
private theorem cleanEmbed_mul_apply {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (N : Matrix X X ℂ) (p : Option (Fin D) × X) (w : X) :
    ((cleanEmbed (D := D) (X := X)) * N) p w = if p.1 = none then N p.2 w else 0 := by
  simp only [Matrix.mul_apply, cleanEmbed]
  rcases p with ⟨a, b⟩
  cases a with
  | none =>
      rw [Finset.sum_eq_single b]
      · simp
      · intro z _ hz
        rw [if_neg (by simp [Ne.symm hz])]
        simp
      · intro h
        exact absurd (Finset.mem_univ b) h
  | some i =>
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [if_neg (by simp)]
      simp

/-- Left multiplication by the conjugate transpose of `cleanEmbed` selects the rows with control
index `none`. -/
theorem conjTranspose_cleanEmbed_mul_apply {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) X ℂ) (x y : X) :
    (((cleanEmbed (D := D) (X := X))ᴴ * M)) x y = M (none, x) y := by
  have hd : ∀ p : Option (Fin D) × X,
      (cleanEmbed (D := D) (X := X))ᴴ x p
        = if p = (none, x) then (1 : ℂ) else 0 := by
    intro p
    simp only [Matrix.conjTranspose_apply, cleanEmbed]
    by_cases hp : p = (none, x)
    · simp [hp]
    · simp [hp]
  simp only [Matrix.mul_apply, hd]
  rw [Finset.sum_eq_single (none, x)]
  · simp
  · intro p _ hp
    rw [if_neg (fun h => hp h)]
    simp
  · intro h
    exact absurd (Finset.mem_univ (none, x)) h

/-- The `none` block is the compression of a matrix by `cleanEmbed` and its conjugate transpose. -/
theorem blockNone_eq {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    blockNone M
      = (((cleanEmbed (D := D) (X := X))ᴴ * M) * (cleanEmbed (D := D) (X := X))) := by
  ext x y
  have h1 : ((((cleanEmbed (D := D) (X := X))ᴴ * M)
        * (cleanEmbed (D := D) (X := X)))) x y
      = ((cleanEmbed (D := D) (X := X))ᴴ * M) x (none, y) :=
    mul_cleanEmbed_apply (D := D) (X := X) (Y := X)
      ((cleanEmbed (D := D) (X := X))ᴴ * M) x y
  have h2 : ((cleanEmbed (D := D) (X := X))ᴴ * M) x (none, y)
      = M (none, x) (none, y) := by
    have hd : ∀ p : Option (Fin D) × X,
        (cleanEmbed (D := D) (X := X))ᴴ x p
          = if p = (none, x) then (1 : ℂ) else 0 := by
      intro p
      simp only [Matrix.conjTranspose_apply, cleanEmbed]
      by_cases hp : p = (none, x)
      · simp [hp]
      · simp [hp]
    simp only [Matrix.mul_apply, hd]
    rw [Finset.sum_eq_single (none, x)]
    · simp
    · intro p _ hp
      rw [if_neg (fun h => hp h)]
      simp
    · intro h
      exact absurd (Finset.mem_univ (none, x)) h
  rw [h1, h2]
  rfl

/-- The embedding `cleanEmbed` has conjugate-transpose product equal to the identity on the data
register. -/
theorem cleanEmbed_conjTranspose_mul {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] :
    ((cleanEmbed (D := D) (X := X))ᴴ * (cleanEmbed (D := D) (X := X)))
      = (1 : Matrix X X ℂ) := by
  ext x y
  rw [conjTranspose_cleanEmbed_mul_apply, cleanEmbed]
  by_cases hxy : x = y <;> simp [hxy, Matrix.one_apply]

/-- The control reflection fixes `cleanEmbed`. -/
theorem reflectNone_mul_cleanEmbed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] :
    ((reflectNone (D := D) (X := X)) * (cleanEmbed (D := D) (X := X)))
      = cleanEmbed (D := D) (X := X) := by
  ext p y
  obtain ⟨a, b⟩ := p
  have hd : ((reflectNone (D := D) (X := X)) * (cleanEmbed (D := D) (X := X))) (a, b) y
      = (if a = none then (1 : ℂ) else -1)
          * (cleanEmbed (D := D) (X := X)) (a, b) y := by
    simp only [Matrix.mul_apply, reflectNone, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (a, b)]
    · simp
    · intro q _ hq
      rw [if_neg (fun h => absurd h.symm hq)]
      simp
    · intro h
      exact absurd (Finset.mem_univ (a, b)) h
  rw [hd]
  cases a with
  | none => rw [if_pos rfl]; simp
  | some i =>
      rw [if_neg (by simp)]
      have hE : (cleanEmbed (D := D) (X := X)) (some i, b) y = 0 := by
        simp only [cleanEmbed]
        exact if_neg (by simp)
      rw [hE]
      simp

/-- The control reflection negates a matrix whose rows with control index `none` vanish. -/
theorem reflectNone_mul_of_noneRow_zero {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (Option (Fin D) × X) X ℂ)
    (hM : ∀ x y, M (none, x) y = 0) :
    ((reflectNone (D := D) (X := X)) * M) = -M := by
  ext p y
  obtain ⟨a, b⟩ := p
  have hd : ((reflectNone (D := D) (X := X)) * M) (a, b) y
      = (if a = none then (1 : ℂ) else -1) * M (a, b) y := by
    simp only [Matrix.mul_apply, reflectNone, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (a, b)]
    · simp
    · intro q _ hq
      rw [if_neg (fun h => absurd h.symm hq)]
      simp
    · intro h
      exact absurd (Finset.mem_univ (a, b)) h
  rw [hd]
  cases a with
  | none =>
      rw [if_pos rfl]
      simp [Matrix.neg_apply, hM b y]
  | some i =>
      rw [if_neg (by simp)]
      simp [Matrix.neg_apply]

/-- The matrix `reflectNone * Uᴴ * reflectNone * U` for a Grover round associated with `U`. -/
noncomputable def groverRound {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ :=
  (reflectNone (D := D) (X := X)) * Uᴴ * (reflectNone (D := D) (X := X)) * U

/-- A Grover round associated with a unitary matrix is unitary. -/
theorem groverRound_unitary {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    groverRound U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
  have hR := reflectNone_unitary (D := D) (X := X)
  exact (Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem
    ((Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem
      ((Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem hR (adjoint_unitary hU)) hR) hU

/-- The matrix `Uᴴ * (cleanEmbed * blockNone U) - sq • cleanEmbed` measuring leakage from the
clean embedding. -/
noncomputable def groverLeak {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) (sq : ℂ) :
    Matrix (Option (Fin D) × X) X ℂ :=
  Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U)
    - sq • (cleanEmbed (D := D) (X := X))

/-- The rows with control index `none` in `Uᴴ * (cleanEmbed * blockNone U)` form `(blockNone U)ᴴ
* blockNone U`. -/
private theorem adjointEmbed_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) (x y : X) :
    (Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U)) (none, x) y
      = ((blockNone U)ᴴ * blockNone U) x y := by
  have hsum : (Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U)) (none, x) y
      = ∑ z : X, Uᴴ (none, x) (none, z) * blockNone U z y := by
    rw [Matrix.mul_apply]
    simp only [cleanEmbed_mul_apply, Fintype.sum_prod_type, Fintype.sum_option]
    simp
  rw [hsum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Matrix.conjTranspose_apply, blockNone]

/-- If the squared `none` block equals `sq • 1`, every row of `groverLeak U sq` with control
index `none` vanishes. -/
theorem groverLeak_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) (x y : X) :
    groverLeak U sq (none, x) y = 0 := by
  rw [groverLeak, Matrix.sub_apply, adjointEmbed_noneRow U x y, hA, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.one_apply, cleanEmbed]
  by_cases hxy : x = y <;> simp [hxy]

/-- If the squared `none` block equals `sq • 1`, compressing the leakage matrix with the adjoint
clean embedding gives zero. -/
theorem cleanEmbed_conjTranspose_mul_groverLeak {D : ℕ} {X : Type*} [Fintype X]
    [DecidableEq X] (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    ((cleanEmbed (D := D) (X := X))ᴴ * groverLeak U sq) = 0 := by
  ext x y
  rw [conjTranspose_cleanEmbed_mul_apply, groverLeak_noneRow U sq hA]
  simp

/-- When `U` is unitary and its squared `none` block is `sq • 1`, one Grover round sends the
clean embedding to `(2 * sq - 1) • cleanEmbed - 2 • groverLeak U sq`. -/
theorem groverRound_mul_cleanEmbed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    (groverRound U) * (cleanEmbed (D := D) (X := X))
      = (2 * sq - 1) • (cleanEmbed (D := D) (X := X))
        - (2 : ℂ) • groverLeak U sq := by
  have hUhU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  have hRE : ((reflectNone (D := D) (X := X)) * (cleanEmbed (D := D) (X := X)))
      = cleanEmbed (D := D) (X := X) := reflectNone_mul_cleanEmbed
  have hREA : ((reflectNone (D := D) (X := X))
      * ((cleanEmbed (D := D) (X := X)) * blockNone U))
      = (cleanEmbed (D := D) (X := X)) * blockNone U := by
    rw [← Matrix.mul_assoc, hRE]
  have hUE : U * (cleanEmbed (D := D) (X := X))
      = ((cleanEmbed (D := D) (X := X)) * blockNone U)
        + (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    abel
  have hBadnone : ∀ x y : X,
      (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) (none, x) y = 0 := by
    intro x y
    rw [Matrix.sub_apply, mul_cleanEmbed_apply (D := D) (X := X)
      (Y := Option (Fin D) × X) U (none, x) y, cleanEmbed_mul_apply (D := D) (X := X)
      (blockNone U) (none, x) y]
    exact sub_self _
  have hRBad : ((reflectNone (D := D) (X := X))
      * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U))
      = -(U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) :=
    reflectNone_mul_of_noneRow_zero _ hBadnone
  have hRleak : ((reflectNone (D := D) (X := X)) * groverLeak U sq)
      = -groverLeak U sq :=
    reflectNone_mul_of_noneRow_zero _ (groverLeak_noneRow U sq hA)
  have hUhEA : Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U)
      = groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)) := by
    rw [groverLeak]
    abel
  have hUhBad : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq := by
    have h1 : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
        = Uᴴ * U * (cleanEmbed (D := D) (X := X))
          - Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h1, hUhU, Matrix.one_mul, hUhEA]
    module
  have hRUE : (reflectNone (D := D) (X := X))
          * (U * (cleanEmbed (D := D) (X := X)))
      = ((cleanEmbed (D := D) (X := X)) * blockNone U)
        - (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    rw [hUE, Matrix.mul_add, hREA, hRBad]
    abel
  have hQ : (groverRound U) * (cleanEmbed (D := D) (X := X))
      = (reflectNone (D := D) (X := X))
          * (Uᴴ * ((reflectNone (D := D) (X := X))
              * (U * (cleanEmbed (D := D) (X := X))))) := by
    rw [groverRound, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have hR1 : (reflectNone (D := D) (X := X))
      * (groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)))
      = sq • (cleanEmbed (D := D) (X := X)) - groverLeak U sq := by
    rw [Matrix.mul_add, Matrix.mul_smul, hRE, hRleak]
    module
  have hR2 : (reflectNone (D := D) (X := X))
      * ((1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) + groverLeak U sq := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hRE, hRleak, sub_neg_eq_add]
  rw [hQ, hRUE, Matrix.mul_sub, Matrix.mul_sub, hUhEA, hUhBad, hR1, hR2]
  module

/-- Under the scalar squared-block condition, one Grover round maps the leakage matrix into the
span of the clean embedding and leakage, with coefficients `2 * sq * (1 - sq)` and `2 * sq -
1`. -/
theorem groverRound_mul_groverLeak {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    (groverRound U) * groverLeak U sq
      = (2 * sq * (1 - sq)) • (cleanEmbed (D := D) (X := X))
        + (2 * sq - 1) • groverLeak U sq := by
  have hUUhU : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hU
  have hUhU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  have hRE : ((reflectNone (D := D) (X := X)) * (cleanEmbed (D := D) (X := X)))
      = cleanEmbed (D := D) (X := X) := reflectNone_mul_cleanEmbed
  have hREA : ((reflectNone (D := D) (X := X))
      * ((cleanEmbed (D := D) (X := X)) * blockNone U))
      = (cleanEmbed (D := D) (X := X)) * blockNone U := by
    rw [← Matrix.mul_assoc, hRE]
  have hUE : U * (cleanEmbed (D := D) (X := X))
      = ((cleanEmbed (D := D) (X := X)) * blockNone U)
        + (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    abel
  have hBadnone : ∀ x y : X,
      (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) (none, x) y = 0 := by
    intro x y
    rw [Matrix.sub_apply, mul_cleanEmbed_apply (D := D) (X := X)
      (Y := Option (Fin D) × X) U (none, x) y, cleanEmbed_mul_apply (D := D) (X := X)
      (blockNone U) (none, x) y]
    exact sub_self _
  have hRBad : ((reflectNone (D := D) (X := X))
      * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U))
      = -(U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) :=
    reflectNone_mul_of_noneRow_zero _ hBadnone
  have hRleak : ((reflectNone (D := D) (X := X)) * groverLeak U sq)
      = -groverLeak U sq :=
    reflectNone_mul_of_noneRow_zero _ (groverLeak_noneRow U sq hA)
  have hUhEA : Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U)
      = groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)) := by
    rw [groverLeak]
    abel
  have hUhBad : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq := by
    have h1 : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
        = Uᴴ * U * (cleanEmbed (D := D) (X := X))
          - Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h1, hUhU, Matrix.one_mul, hUhEA]
    module
  have hUL : U * groverLeak U sq
      = (1 - sq) • ((cleanEmbed (D := D) (X := X)) * blockNone U)
        - sq • (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    have h1 : U * groverLeak U sq
        = U * (Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U))
          - U * (sq • (cleanEmbed (D := D) (X := X))) := by
      rw [groverLeak, Matrix.mul_sub, Matrix.mul_smul]
    rw [h1, ← Matrix.mul_assoc, hUUhU, Matrix.one_mul, Matrix.mul_smul, hUE]
    module
  have hRUL : (reflectNone (D := D) (X := X))
      * ((1 - sq) • ((cleanEmbed (D := D) (X := X)) * blockNone U)
          - sq • (U * (cleanEmbed (D := D) (X := X))
              - (cleanEmbed (D := D) (X := X)) * blockNone U))
      = (1 - sq) • ((cleanEmbed (D := D) (X := X)) * blockNone U)
        + sq • (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hREA, hRBad,
      smul_neg, sub_neg_eq_add]
  have hQ : (groverRound U) * groverLeak U sq
      = (reflectNone (D := D) (X := X))
          * (Uᴴ * ((reflectNone (D := D) (X := X)) * (U * groverLeak U sq))) := by
    rw [groverRound, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have hR1 : (reflectNone (D := D) (X := X))
      * (groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)))
      = sq • (cleanEmbed (D := D) (X := X)) - groverLeak U sq := by
    rw [Matrix.mul_add, Matrix.mul_smul, hRE, hRleak]
    module
  have hR2 : (reflectNone (D := D) (X := X))
      * ((1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) + groverLeak U sq := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hRE, hRleak, sub_neg_eq_add]
  rw [hQ, hUL, hRUL, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    hUhEA, hUhBad, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hR1, hR2]
  module

/-- The two-by-two transition matrix with rows `(p, r)` and `(-2, p)`. -/
def groverStepMatrix (p r : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if (i, j) = (0, 0) then p else if (i, j) = (0, 1) then r
  else if (i, j) = (1, 0) then (-2 : ℂ) else p

/-- The powers of `groverStepMatrix p r`, defined recursively from the identity matrix. -/
noncomputable def groverAmp (p r : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | m + 1 => groverAmp p r m * groverStepMatrix p r

/-- The upper-left entry of `groverStepMatrix p r` is `p`. -/
private theorem gSM00 (p r : ℂ) : groverStepMatrix p r 0 0 = p := by
  simp [groverStepMatrix]

/-- The upper-right entry of `groverStepMatrix p r` is `r`. -/
private theorem gSM01 (p r : ℂ) : groverStepMatrix p r 0 1 = r := by
  simp [groverStepMatrix]

/-- The lower-left entry of `groverStepMatrix p r` is minus two. -/
private theorem gSM10 (p r : ℂ) : groverStepMatrix p r 1 0 = (-2 : ℂ) := by
  simp [groverStepMatrix]

/-- The lower-right entry of `groverStepMatrix p r` is `p`. -/
private theorem gSM11 (p r : ℂ) : groverStepMatrix p r 1 1 = p := by
  simp [groverStepMatrix]

/-- Scalar multiplication of a two-by-two complex matrix multiplies each entry by the scalar. -/
private theorem smulEntry (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ((c • M : Matrix (Fin 2) (Fin 2) ℂ)) i j = c * M i j := by
  simp [Matrix.smul_apply]

/-- The four entries of `groverAmp` satisfy the recurrences obtained by right multiplication by
`groverStepMatrix`. -/
private theorem groverAmp_succ_entries (p r : ℂ) (m : ℕ) :
    groverAmp p r (m + 1) 0 0 = groverAmp p r m 0 0 * p + groverAmp p r m 0 1 * (-2 : ℂ) ∧
    groverAmp p r (m + 1) 1 0 = groverAmp p r m 1 0 * p + groverAmp p r m 1 1 * (-2 : ℂ) ∧
    groverAmp p r (m + 1) 0 1 = groverAmp p r m 0 0 * r + groverAmp p r m 0 1 * p ∧
    groverAmp p r (m + 1) 1 1 = groverAmp p r m 1 0 * r + groverAmp p r m 1 1 * p := by
  have h : groverAmp p r (m + 1) = groverAmp p r m * groverStepMatrix p r := rfl
  constructor
  · rw [h, Matrix.mul_apply, Fin.sum_univ_two, gSM00, gSM10]
  · constructor
    · rw [h, Matrix.mul_apply, Fin.sum_univ_two, gSM00, gSM10]
    · constructor
      · rw [h, Matrix.mul_apply, Fin.sum_univ_two, gSM01, gSM11]
      · rw [h, Matrix.mul_apply, Fin.sum_univ_two, gSM01, gSM11]

/-- The complex Chebyshev polynomials of the first kind, defined by initial values one and `p`
and the recurrence `T_(m+2) = 2 * p * T_(m+1) - T_m`. -/
def groverChebT : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, p => p
  | m + 2, p => 2 * p * groverChebT (m + 1) p - groverChebT m p

/-- If `2 * r = 1 - p²`, the second transition power equals `2 * p` times the first power minus
the identity. -/
private theorem groverAmp_two {p r : ℂ} (h2r : 2 * r = 1 - p ^ 2) :
    groverAmp p r 2
      = ((2 * p : ℂ) • groverAmp p r 1 : Matrix (Fin 2) (Fin 2) ℂ) - groverAmp p r 0 := by
  have h1 : groverAmp p r 1 = groverStepMatrix p r := by simp [groverAmp]
  have h2 : groverAmp p r 2 = groverStepMatrix p r * groverStepMatrix p r := by
    simp [groverAmp]
  have h0 : (groverAmp p r 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
  have hfin : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    intro i
    have h : i.val = 0 ∨ i.val = 1 := by omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have e00 : (groverStepMatrix p r * groverStepMatrix p r) 0 0
      = p * p + r * (-2 : ℂ) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, gSM00, gSM01, gSM10]
  have e01 : (groverStepMatrix p r * groverStepMatrix p r) 0 1
      = p * r + r * p := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, gSM00, gSM01, gSM11]
  have e10 : (groverStepMatrix p r * groverStepMatrix p r) 1 0
      = (-2 : ℂ) * p + p * (-2 : ℂ) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, gSM10, gSM00, gSM11]
  have e11 : (groverStepMatrix p r * groverStepMatrix p r) 1 1
      = (-2 : ℂ) * r + p * p := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, gSM10, gSM01, gSM11]
  rw [h2, h1, h0]
  ext i j
  rcases hfin i with hi | hi <;> rcases hfin j with hj | hj <;> subst hi <;> subst hj
  · rw [Matrix.sub_apply, e00]
    simp only [smulEntry, gSM00]
    show p * p + r * (-2 : ℂ) = 2 * p * p - 1
    linear_combination h2r.symm
  · rw [Matrix.sub_apply, e01]
    simp only [smulEntry, gSM01]
    show p * r + r * p = 2 * p * r - 0
    ring
  · rw [Matrix.sub_apply, e10]
    simp only [smulEntry, gSM10]
    show (-2 : ℂ) * p + p * (-2 : ℂ) = 2 * p * (-2 : ℂ) - 0
    ring
  · rw [Matrix.sub_apply, e11]
    simp only [smulEntry, gSM11]
    show (-2 : ℂ) * r + p * p = 2 * p * p - 1
    linear_combination h2r.symm

/-- If `2 * r = 1 - p²`, the transition powers satisfy the Chebyshev recurrence. -/
private theorem groverAmp_succ_succ {p r : ℂ} (h2r : 2 * r = 1 - p ^ 2) (m : ℕ) :
    groverAmp p r (m + 2)
      = ((2 * p : ℂ) • groverAmp p r (m + 1) : Matrix (Fin 2) (Fin 2) ℂ) - groverAmp p r m := by
  induction m with
  | zero => simpa using! groverAmp_two h2r
  | succ m ih =>
      calc groverAmp p r (m + 3)
          = groverAmp p r (m + 2) * groverStepMatrix p r := rfl
        _ = ((2 * p : ℂ) • groverAmp p r (m + 1) - groverAmp p r m) * groverStepMatrix p r :=
            by rw [ih]
        _ = (2 * p : ℂ) • groverAmp p r (m + 2) - groverAmp p r (m + 1) := by
            ext i j
            simp only [Matrix.mul_apply, Matrix.sub_apply, smulEntry, Fin.sum_univ_two,
              groverAmp]
            ring

/-- Under `2 * r = 1 - p²`, the upper-left entry of `groverAmp p r m` equals `groverChebT m p`. -/
theorem groverAmp_apply_chebT {p r : ℂ} (h2r : 2 * r = 1 - p ^ 2) (m : ℕ) :
    groverAmp p r m 0 0 = groverChebT m p := by
  induction m using Nat.twoStepInduction with
  | zero => simp [groverAmp, groverChebT]
  | one => simp [groverAmp, groverChebT, gSM00]
  | more m ih1 ih2 =>
      have hrec := groverAmp_succ_succ h2r m
      rw [hrec, Matrix.sub_apply]
      simp only [smulEntry, ih2, ih1]
      simp [groverChebT]

/-- Under the scalar squared-block condition, every Grover power preserves the span of the clean
embedding and leakage, with coefficients given by `groverAmp`. -/
theorem groverPower_structure {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) (m : ℕ) :
    ((groverRound U) ^ m) * (cleanEmbed (D := D) (X := X))
      = (groverAmp (2 * sq - 1) (2 * sq * (1 - sq)) m 0 0) • (cleanEmbed (D := D) (X := X))
        + (groverAmp (2 * sq - 1) (2 * sq * (1 - sq)) m 1 0) • groverLeak U sq ∧
    ((groverRound U) ^ m) * groverLeak U sq
      = (groverAmp (2 * sq - 1) (2 * sq * (1 - sq)) m 0 1) • (cleanEmbed (D := D) (X := X))
        + (groverAmp (2 * sq - 1) (2 * sq * (1 - sq)) m 1 1) • groverLeak U sq := by
  have hQE := groverRound_mul_cleanEmbed U hU sq hA
  have hQL := groverRound_mul_groverLeak U hU sq hA
  induction m with
  | zero =>
      refine ⟨?_, ?_⟩ <;> simp [groverAmp]
  | succ m ih =>
      obtain ⟨ihE, ihL⟩ := ih
      obtain ⟨e00, e10, e01, e11⟩ := groverAmp_succ_entries (2 * sq - 1)
        (2 * sq * (1 - sq)) m
      have hpowE : ((groverRound U) ^ (m + 1)) * (cleanEmbed (D := D) (X := X))
          = ((groverRound U) ^ m) * ((2 * sq - 1) • (cleanEmbed (D := D) (X := X))
              - (2 : ℂ) • groverLeak U sq) := by
        rw [pow_succ, Matrix.mul_assoc, hQE]
      have hpowL : ((groverRound U) ^ (m + 1)) * groverLeak U sq
          = ((groverRound U) ^ m) * ((2 * sq * (1 - sq)) • (cleanEmbed (D := D) (X := X))
              + (2 * sq - 1) • groverLeak U sq) := by
        rw [pow_succ, Matrix.mul_assoc, hQL]
      refine ⟨?_, ?_⟩
      · rw [hpowE, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, ihE, ihL, e00, e10]
        module
      · rw [hpowL, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, ihE, ihL, e01, e11]
        module

/-- Under the scalar squared-block condition, the `none` block of a Grover power is the
upper-left transition coefficient times the identity. -/
theorem groverPower_topBlock {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) (m : ℕ) :
    blockNone ((groverRound U) ^ m)
      = (groverAmp (2 * sq - 1) (2 * sq * (1 - sq)) m 0 0) • (1 : Matrix X X ℂ) := by
  rw [blockNone_eq, Matrix.mul_assoc, (groverPower_structure U hU sq hA m).1,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, cleanEmbed_conjTranspose_mul,
    cleanEmbed_conjTranspose_mul_groverLeak U sq hA, smul_zero, add_zero]

/-- If `(blockNone U)ᴴ * blockNone U = sq • 1` and `U` is unitary, the `none` block of its `m`th
Grover power is `groverChebT m (2 * sq - 1) • 1`. -/
theorem groverPower_topBlock_chebT {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) (m : ℕ) :
    blockNone ((groverRound U) ^ m)
      = groverChebT m (2 * sq - 1) • (1 : Matrix X X ℂ) := by
  have h2r : 2 * (2 * sq * (1 - sq)) = 1 - (2 * sq - 1) ^ 2 := by ring
  rw [groverPower_topBlock U hU sq hA m, groverAmp_apply_chebT h2r m]

/-- If the weighted operator sum has squared modulus `sq • 1`, the exact linear-combination
Grover power has `none` block `groverChebT m (2 * sq - 1) • 1`. -/
theorem lcuGroverPower_topBlock {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1) (m : ℕ) :
    blockNone ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m)
      = groverChebT m (2 * sq - 1) • (1 : Matrix X X ℂ) := by
  have hUe : TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    lcuSandwichExact_unitary w amp hw hm U hU
  have htop : (blockNone (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1))ᴴ
      * blockNone (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
          * TensorGate (exactPrepareMatrix w amp) 1)
      = sq • 1 := by
    rw [lcuTopBlock_exact w amp hw hm U, hA]
  exact groverPower_topBlock_chebT _ hUe sq htop m

/-- The concatenation of `m` copies of the Grover circuit word. -/
noncomputable def groverWordRepeat {D : ℕ} {X : Type*} [DecidableEq X]
    (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    List (AdjointStep (Option (Fin D) × X)) :=
  match m with
  | 0 => []
  | m + 1 => groverWordRepeat m k w amp S ++ groverWord k w amp S

/-- Evaluating the repeated Grover word gives the `m`th power of the single-round evaluation. -/
theorem groverWordRepeat_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (groverWordRepeat m k w amp S)
      = (evaluate 1 (groverWord k w amp S)) ^ m := by
  induction m with
  | zero => simp [groverWordRepeat, evaluate]
  | succ m ih =>
      simp only [groverWordRepeat, evaluate_append, ih, pow_succ]

/-- The repeated Grover word has `m * (2 * (2 * (D + 1) + 1) + 2)` gates and zero queries. -/
theorem groverWordRepeat_counts {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    adjointGateCount (groverWordRepeat m k w amp S)
      = m * (2 * (2 * (D + 1) + 1) + 2) ∧
      adjointQueryCount (groverWordRepeat m k w amp S) = 0 := by
  obtain ⟨hgW, hqW⟩ := groverWord_counts k w amp S
  induction m with
  | zero => simp [groverWordRepeat, adjointGateCount, adjointQueryCount]
  | succ m ih =>
      obtain ⟨hg, hq⟩ := ih
      simp only [groverWordRepeat, adjointGateCount_append, adjointQueryCount_append]
      refine ⟨by rw [hg, hgW]; ring, by rw [hq, hqW]⟩

/-- Repeating a well-formed Grover construction preserves well-formedness. -/
theorem groverWordRepeat_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (groverWordRepeat m k w amp S) := by
  induction m with
  | zero => exact WellFormedAdjointCircuit.nil
  | succ m ih =>
      simp only [groverWordRepeat]
      exact ih.append (groverWord_wellFormed k w amp hw S hS)

/-- The difference of the `m`th powers of two unitaries has norm at most `m` times the norm of
their difference. -/
private theorem unitary_pow_sub_pow_norm_le {H : Type*} [Fintype H] [DecidableEq H]
    [Nonempty H] (A B : Matrix H H ℂ)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ) (m : ℕ) :
    ‖A ^ m - B ^ m‖ ≤ m * ‖A - B‖ := by
  have hdecomp : ∀ j : ℕ, A ^ (j + 1) - B ^ (j + 1)
      = A ^ j * (A - B) + (A ^ j - B ^ j) * B := by
    intro j
    rw [pow_succ, pow_succ]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : ‖A ^ m * (A - B)‖ = ‖A - B‖ :=
        unitary_mul_norm_eq _ (Submonoid.pow_mem _ hA m) _
      have h2 : ‖(A ^ m - B ^ m) * B‖ ≤ ‖A ^ m - B ^ m‖ := by
        have hle := Matrix.l2_opNorm_mul (A ^ m - B ^ m) B
        rwa [l2_norm_unitary_eq_one hB, mul_one] at hle
      rw [hdecomp m]
      refine (norm_add_le _ _).trans ?_
      rw [h1]
      have h3 := h2.trans ih
      have h4 : ‖A - B‖ + ‖(A ^ m - B ^ m) * B‖
          ≤ ‖A - B‖ + (m : ℝ) * ‖A - B‖ := add_le_add (le_refl _) h3
      have h5 : ((m + 1 : ℕ) : ℝ) * ‖A - B‖
          = ‖A - B‖ + (m : ℝ) * ‖A - B‖ := by
        push_cast
        ring
      rw [h5]
      exact h4

/-- The Grover word evaluates to `groverRound` of the evaluated linear-combination word. -/
theorem groverWord_eval_round {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (groverWord k w amp S)
      = groverRound (evaluate 1 (lcuBlockWord k w amp S)) := by
  rw [groverWord_eval, groverRound]

/-- The error after `m` approximate Grover rounds is at most `m * (128 * (D + 1) / 2^k)` in
matrix norm. -/
theorem groverPower_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖((evaluate 1 (groverWord k w amp S)) ^ m)
        - (groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)) ^ m‖
      ≤ m * (128 * (D + 1) / 2 ^ k) := by
  have hW : evaluate 1 (groverWord k w amp S)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (groverWord_wellFormed k w amp hw S hS).evaluate_unitary (Submonoid.one_mem _)
  have hE : groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
        * TensorGate (exactPrepareMatrix w amp) 1)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    groverRound_unitary (lcuSandwich_unitary w amp hw hm S hS)
  have hone := grover_error k w amp hw hm S hS
  exact (unitary_pow_sub_pow_norm_le _ _ hW hE m).trans
    (mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg m))

/-- The bound `c ≤ e / (4 * (n + 1))` implies `(n + 1) * (4 * c) ≤ e`. -/
private theorem mul_four_div_le {c e : ℝ} {n : ℕ}
    (hb : c ≤ e / (4 * ((n : ℝ) + 1))) :
    ((n : ℝ) + 1) * (4 * c) ≤ e := by
  have hne : (4 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  calc ((n : ℝ) + 1) * (4 * c)
      = (4 * ((n : ℝ) + 1)) * c := by ring
    _ ≤ (4 * ((n : ℝ) + 1)) * (e / (4 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = e := mul_div_cancel₀ e hne

/-- The evaluated repeated Grover word approximates the exact Grover power within `m * (128 * (D
+ 1) / 2^k)`. -/
theorem groverWordRepeat_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (groverWordRepeat m k w amp S)
        - (groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)) ^ m‖
      ≤ m * (128 * (D + 1) / 2 ^ k) := by
  rw [groverWordRepeat_eval]
  exact groverPower_error m k w amp hw hm S hS

/-- Precision `precisionFor D (ε / (4 * (m + 1)))` bounds the error after `m + 1` Grover rounds
by `ε`. -/
theorem groverWordRepeat_error_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (groverWordRepeat (m + 1)
          (precisionFor D (ε / (4 * (m + 1)))) w amp S)
        - (groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)) ^ (m + 1)‖
      ≤ (ε : ℝ) := by
  have h := groverWordRepeat_error (m + 1) (precisionFor D (ε / (4 * (m + 1)))) w amp
    hw hm S hS
  have hb := prepError_le_epsilon (D := D) (ε / (4 * (m + 1))) (by positivity)
  have hcastE : ((ε / (4 * (m + 1)) : ℚ) : ℝ) = (ε : ℝ) / (4 * ((m : ℝ) + 1)) := by
    push_cast
    ring
  rw [hcastE] at hb
  refine h.trans ?_
  have hsplit : (128 : ℝ) * ((D : ℝ) + 1)
        / (2 ^ precisionFor D (ε / (4 * (m + 1))) : ℝ)
      = 4 * (32 * ((D : ℝ) + 1)
          / (2 ^ precisionFor D (ε / (4 * (m + 1))) : ℝ)) := by
    field_simp
    ring
  rw [hsplit, Nat.cast_succ]
  exact mul_four_div_le hb

/-- Under the scalar squared-block condition, the repeated Grover word's `none` block
approximates the Chebyshev scalar times identity within `m * (128 * (D + 1) / 2^k)`. -/
theorem groverPowerTop_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1) :
    ‖blockNone (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)))
        - groverChebT m (2 * sq - 1) • (1 : Matrix X X ℂ)‖
      ≤ m * (128 * (D + 1) / 2 ^ k) := by
  have hsub : blockNone (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)))
        - groverChebT m (2 * sq - 1) • (1 : Matrix X X ℂ)
      = blockNone (evaluate 1 (groverWordRepeat m k w amp (blockSelect U))
          - (groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
              * TensorGate (exactPrepareMatrix w amp) 1)) ^ m) := by
    have hLin : ∀ M N : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ,
        blockNone (M - N) = blockNone M - blockNone N := by
      intro M N
      ext x y
      simp [blockNone, Matrix.sub_apply]
    rw [hLin, lcuGroverPower_topBlock w amp hw hm U hU sq hA m]
  rw [hsub]
  exact (blockNone_norm_le _).trans
    (groverWordRepeat_error m k w amp hw hm (blockSelect U) (blockSelect_unitary hU))

/-- Under the scalar squared-block condition, the specified precision gives error at most `ε` in
the Chebyshev formula for the `none` block. -/
theorem groverPowerTop_error_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) (U : Option (Fin D) → Matrix X X ℂ)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1) :
    ‖blockNone (evaluate 1 (groverWordRepeat (m + 1)
          (precisionFor D (ε / (4 * (m + 1)))) w amp (blockSelect U)))
        - groverChebT (m + 1) (2 * sq - 1) • (1 : Matrix X X ℂ)‖
      ≤ (ε : ℝ) := by
  have h := groverPowerTop_error (m + 1) (precisionFor D (ε / (4 * (m + 1)))) w amp
    hw hm U hU sq hA
  have hb := prepError_le_epsilon (D := D) (ε / (4 * (m + 1))) (by positivity)
  have hcastE : ((ε / (4 * (m + 1)) : ℚ) : ℝ) = (ε : ℝ) / (4 * ((m : ℝ) + 1)) := by
    push_cast
    ring
  rw [hcastE] at hb
  refine h.trans ?_
  have hsplit : (128 : ℝ) * ((D : ℝ) + 1)
        / (2 ^ precisionFor D (ε / (4 * (m + 1))) : ℝ)
      = 4 * (32 * ((D : ℝ) + 1)
          / (2 ^ precisionFor D (ε / (4 * (m + 1))) : ℝ)) := by
    field_simp
    ring
  rw [hsplit, Nat.cast_succ]
  exact mul_four_div_le hb

/-- Under the scalar squared-block condition, the exact Grover power has clean branch
`groverChebT m (2 * sq - 1) • ψ`. -/
theorem groverPower_state_exact {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (m : ℕ) (ψ : QState X) :
    cleanBranch ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      = groverChebT m (2 * sq - 1) • ψ := by
  rw [lcuCleanBranch, lcuGroverPower_topBlock w amp hw hm U hU sq hA m]
  funext x
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro z _ hz
    rw [if_neg (Ne.symm hz)]
    simp
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- Under the scalar squared-block condition, the repeated Grover word's clean branch differs
from the Chebyshev-scaled input by at most `m * (128 * (D + 1) / 2^k)` times the input norm. -/
theorem groverWordRepeat_state_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (ψ : QState X) :
    ‖stateVector (cleanBranch (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - stateVector (groverChebT m (2 * sq - 1) • ψ)‖
      ≤ m * (128 * (D + 1) / 2 ^ k) * ‖stateVector ψ‖ := by
  rw [lcuCleanBranch]
  have hsub : stateVector
        (blockNone (evaluate 1 (groverWordRepeat m k w amp (blockSelect U))) *ᵥ ψ)
        - stateVector (groverChebT m (2 * sq - 1) • ψ)
      = stateVector ((blockNone (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)))
            - groverChebT m (2 * sq - 1) • (1 : Matrix X X ℂ)) *ᵥ ψ) := by
    simp [stateVector, WithLp.toLp_sub, WithLp.toLp_smul, Matrix.sub_mulVec,
      Matrix.smul_mulVec]
  rw [hsub]
  have hn := stateVector_mulVec_norm_le
    (blockNone (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)))
      - groverChebT m (2 * sq - 1) • (1 : Matrix X X ℂ)) ψ
  refine hn.trans ?_
  exact mul_le_mul_of_nonneg_right (groverPowerTop_error m k w amp hw hm U hU sq hA)
    (norm_nonneg (stateVector ψ))

/-- Every polynomial `groverChebT m` takes the value one at one. -/
theorem groverChebT_eq_one (m : ℕ) : groverChebT m (1 : ℂ) = 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [groverChebT]
  | one => simp [groverChebT]
  | more m ih1 ih2 =>
      simp only [groverChebT]
      rw [ih2, ih1]
      ring

/-- The value of `groverChebT m` at minus one is `(-1)^m`. -/
theorem groverChebT_eq_neg_one_pow (m : ℕ) : groverChebT m (-1 : ℂ) = (-1 : ℂ) ^ m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [groverChebT]
  | one => simp [groverChebT]
  | more m ih1 ih2 =>
      have hpr : (-1 : ℂ) ^ (m + 2) = (-1 : ℂ) ^ m := by
        rw [pow_add]
        norm_num
      simp only [groverChebT]
      rw [ih2, ih1, pow_add, pow_one, hpr]
      ring

/-- The state error of a repeated Grover word is bounded by its matrix error bound times the
input state's Euclidean norm. -/
theorem groverWordRepeat_vec_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ)
    (φ : QState (Option (Fin D) × X)) :
    ‖stateVector (evaluate 1 (groverWordRepeat m k w amp S) *ᵥ φ)
        - stateVector ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ φ)‖
      ≤ m * (128 * (D + 1) / 2 ^ k) * ‖stateVector φ‖ := by
  have hsub : stateVector (evaluate 1 (groverWordRepeat m k w amp S) *ᵥ φ)
        - stateVector ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ φ)
      = stateVector ((evaluate 1 (groverWordRepeat m k w amp S)
            - (groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                * TensorGate (exactPrepareMatrix w amp) 1)) ^ m) *ᵥ φ) := by
    simp [stateVector, WithLp.toLp_sub, Matrix.sub_mulVec]
  rw [hsub]
  have hn := stateVector_mulVec_norm_le
    (evaluate 1 (groverWordRepeat m k w amp S)
      - (groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
          * TensorGate (exactPrepareMatrix w amp) 1)) ^ m) φ
  refine hn.trans ?_
  exact mul_le_mul_of_nonneg_right (groverWordRepeat_error m k w amp hw hm S hS)
    (norm_nonneg (stateVector φ))

/-- Under the scalar squared-block condition, the exact `none`-branch probability is the squared
Chebyshev modulus times the squared input norm. -/
theorem groverBorn_exact {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (m : ℕ) (ψ : QState X) :
    MeasureProb ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      = ‖groverChebT m (2 * sq - 1)‖ ^ 2 * ‖stateVector ψ‖ ^ 2 := by
  rw [measureProb_none_branch,
    groverPower_state_exact w amp hw hm U hU sq hA m ψ]
  have hsmul : stateVector (groverChebT m (2 * sq - 1) • ψ)
      = groverChebT m (2 * sq - 1) • stateVector ψ := by
    simp [stateVector, WithLp.toLp_smul]
  rw [hsmul, norm_smul, mul_pow]

/-- If the weighted operator sum has conjugate-transpose product equal to the identity, every
exact Grover power has clean branch equal to the input. -/
theorem groverPower_state_isometry {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = (1 : ℂ) • 1)
    (m : ℕ) (ψ : QState X) :
    cleanBranch ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      = ψ := by
  rw [groverPower_state_exact w amp hw hm U hU (1 : ℂ) hA m ψ]
  norm_num
  rw [groverChebT_eq_one]
  simp

/-- If the weighted operator sum has zero conjugate-transpose product, the exact `m`th Grover
power has clean branch `(-1)^m • ψ`. -/
theorem groverPower_state_reflecting {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = (0 : ℂ) • 1)
    (m : ℕ) (ψ : QState X) :
    cleanBranch ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      = (-1 : ℂ) ^ m • ψ := by
  rw [groverPower_state_exact w amp hw hm U hU (0 : ℂ) hA m ψ]
  norm_num
  rw [groverChebT_eq_neg_one_pow]

/-- When the weighted operator sum has conjugate-transpose product equal to the identity, the
exact Grover `none`-branch probability equals the squared input norm. -/
theorem groverBorn_exact_isometry {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = (1 : ℂ) • 1)
    (m : ℕ) (ψ : QState X) :
    MeasureProb ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      = ‖stateVector ψ‖ ^ 2 := by
  rw [groverBorn_exact w amp hw hm U hU (1 : ℂ) hA m ψ]
  norm_num
  rw [groverChebT_eq_one]
  simp

/-- When the weighted operator sum has zero conjugate-transpose product, the exact Grover
`none`-branch probability equals the squared input norm. -/
theorem groverBorn_exact_reflecting {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = (0 : ℂ) • 1)
    (m : ℕ) (ψ : QState X) :
    MeasureProb ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      = ‖stateVector ψ‖ ^ 2 := by
  rw [groverBorn_exact w amp hw hm U hU (0 : ℂ) hA m ψ]
  norm_num
  rw [groverChebT_eq_neg_one_pow]
  have hnorm : ‖((-1 : ℂ) ^ m)‖ = 1 := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Complex.norm_mul, ih]; simp
  rw [hnorm, one_pow, one_mul]

/-- For normalized input under the scalar squared-block condition, the repeated Grover word's
`none`-branch probability differs from the squared Chebyshev modulus by at most `2 * (m *
(128 * (D + 1) / 2^k))`. -/
theorem groverBorn_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    |MeasureProb (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖groverChebT m (2 * sq - 1)‖ ^ 2|
      ≤ 2 * (m * (128 * (D + 1) / 2 ^ k)) := by
  have hWU : evaluate 1 (groverWordRepeat m k w amp (blockSelect U))
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (groverWordRepeat_wellFormed m k w amp hw (blockSelect U)
      (blockSelect_unitary hU)).evaluate_unitary (Submonoid.one_mem _)
  have hEU : (groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1)) ^ m
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    Submonoid.pow_mem _
      (groverRound_unitary (lcuSandwich_unitary w amp hw hm (blockSelect U)
        (blockSelect_unitary hU))) m
  have hφ : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    have hT : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
        = ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ * ‖stateVector ψ‖ :=
      tensorState_l2_norm _ _
    rw [hT, stateVector_ket_none_norm, hψ, mul_one]
  have hv1 : ‖stateVector (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    rw [unitary_mulVec_stateVector_norm _ hWU _]
    exact hφ
  have hu1 : ‖stateVector ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1
        * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    rw [unitary_mulVec_stateVector_norm _ hEU _]
    exact hφ
  have hvu : ‖stateVector (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1
            * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
      ≤ m * (128 * (D + 1) / 2 ^ k) := by
    have h := groverWordRepeat_vec_error m k w amp hw hm (blockSelect U)
      (blockSelect_unitary hU)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
    rwa [hφ, mul_one] at h
  have hd := born_deviation
    (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)) *ᵥ
      TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
    ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
      * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
      TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
    (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none)) hv1 hu1 hvu
  have hPu := groverBorn_exact w amp hw hm U hU sq hA m ψ
  rw [hψ, one_pow, mul_one] at hPu
  rwa [hPu] at hd

/-- The bound `c ≤ e / (8 * (n + 1))` implies `2 * ((n + 1) * (4 * c)) ≤ e`. -/
private theorem born_eps_arith {c e n : ℝ} (hn : 0 ≤ n) (hb : c ≤ e / (8 * (n + 1))) :
    2 * ((n + 1) * (4 * c)) ≤ e := by
  have hne : (8 : ℝ) * (n + 1) ≠ 0 := by positivity
  calc 2 * ((n + 1) * (4 * c))
      = (8 * (n + 1)) * c := by ring
    _ ≤ (8 * (n + 1)) * (e / (8 * (n + 1))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = e := mul_div_cancel₀ e hne

/-- Under the scalar squared-block condition, precision `precisionFor D (ε / (8 * (m + 1)))`
bounds the `none`-branch probability error after `m + 1` rounds by `ε`. -/
theorem groverBorn_none_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) (U : Option (Fin D) → Matrix X X ℂ)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    |MeasureProb (evaluate 1
          (groverWordRepeat (m + 1) (precisionFor D (ε / (8 * (m + 1)))) w amp
            (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖groverChebT (m + 1) (2 * sq - 1)‖ ^ 2|
      ≤ (ε : ℝ) := by
  have h := groverBorn_none (m + 1) (precisionFor D (ε / (8 * (m + 1)))) w amp hw hm
    U hU sq hA ψ hψ
  have hb := prepError_le_epsilon (D := D) (ε / (8 * (m + 1))) (by positivity)
  have hcastE : ((ε / (8 * (m + 1)) : ℚ) : ℝ) = (ε : ℝ) / (8 * ((m : ℝ) + 1)) := by
    push_cast
    ring
  rw [hcastE] at hb
  refine h.trans ?_
  have hinner : (128 : ℝ) * ((D : ℝ) + 1)
        / (2 ^ precisionFor D (ε / (8 * (m + 1))) : ℝ)
      = 4 * (32 * ((D : ℝ) + 1)
          / (2 ^ precisionFor D (ε / (8 * (m + 1))) : ℝ)) := by
    field_simp
    ring
  rw [hinner, Nat.cast_succ]
  exact born_eps_arith (Nat.cast_nonneg m) hb

/-- The polynomial `groverChebT m` has parity `m`, so evaluating at `-x` multiplies its value by
`(-1)^m`. -/
theorem groverChebT_neg (m : ℕ) (x : ℂ) :
    groverChebT m (-x) = (-1 : ℂ) ^ m * groverChebT m x := by
  induction m using Nat.twoStepInduction with
  | zero => simp [groverChebT]
  | one => simp [groverChebT]
  | more m ih1 ih2 =>
      have hpr : (-1 : ℂ) ^ (m + 2) = (-1 : ℂ) ^ m := by
        rw [pow_add]
        norm_num
      simp only [groverChebT, ih2, ih1]
      rw [pow_succ, hpr]
      ring

/-- Evaluating `groverChebT m` at `cos θ` gives `cos (m * θ)`. -/
theorem groverChebT_cos (m : ℕ) (θ : ℝ) :
    groverChebT m (Real.cos θ : ℂ) = (Real.cos (((m : ℕ) : ℝ) * θ) : ℂ) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [groverChebT]
  | one => simp [groverChebT]
  | more m ih1 ih2 =>
      have key : ∀ a b : ℝ, 2 * Real.cos a * Real.cos b
          = Real.cos (a + b) + Real.cos (a - b) := by
        intro a b
        rw [Real.cos_add, Real.cos_sub]
        ring
      have eA : 2 * Real.cos θ * Real.cos ((((m : ℕ) + 1 : ℕ) : ℝ) * θ)
          - Real.cos (((m : ℕ) : ℝ) * θ)
          = Real.cos ((((m : ℕ) + 2 : ℕ) : ℝ) * θ) := by
        have hk := key θ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ)
        have h1 : θ + ((((m : ℕ) + 1 : ℕ) : ℝ) * θ)
            = ((((m : ℕ) + 2 : ℕ) : ℝ) * θ) := by
          push_cast
          ring
        have h2 : θ - ((((m : ℕ) + 1 : ℕ) : ℝ) * θ)
            = -(((m : ℕ) : ℝ) * θ) := by
          push_cast
          ring
        have hcn : Real.cos (-(((m : ℕ) : ℝ) * θ))
            = Real.cos (((m : ℕ) : ℝ) * θ) :=
          Real.cos_neg _
        rw [hk, h1, h2, hcn]
        ring
      simp only [groverChebT, ih2, ih1]
      push_cast
      exact_mod_cast eA

/-- If `sq = sin² θ`, the squared modulus of `groverChebT m (2 * sq - 1)` equals `cos² (m * (2 *
θ))`. -/
theorem groverChebT_sq_sin (m : ℕ) (sq θ : ℝ) (hsq : sq = Real.sin θ ^ 2) :
    ‖groverChebT m (2 * (sq : ℂ) - 1)‖ ^ 2
      = Real.cos (((m : ℕ) : ℝ) * (2 * θ)) ^ 2 := by
  have hc : (2 * (sq : ℂ) - 1) = (((2 * sq - 1 : ℝ) : ℂ)) := by
    push_cast
    ring
  have harg : (2 * sq - 1 : ℝ) = -Real.cos (2 * θ) := by
    rw [hsq, Real.cos_two_mul]
    linear_combination 2 * Real.cos_sq_add_sin_sq θ
  rw [hc, harg, Complex.ofReal_neg, groverChebT_neg, groverChebT_cos m (2 * θ)]
  rw [Complex.norm_mul]
  have hnorm1 : ‖((-1 : ℂ) ^ m)‖ = 1 := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Complex.norm_mul, ih]; simp
  rw [hnorm1, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- If `sq = sin² θ` and `m * (2 * θ) = π`, the squared Grover Chebyshev modulus equals one. -/
theorem groverChebT_sq_sin_hit (m : ℕ) (sq θ : ℝ) (hsq : sq = Real.sin θ ^ 2)
    (hθ : ((m : ℕ) : ℝ) * (2 * θ) = Real.pi) :
    ‖groverChebT m (2 * (sq : ℂ) - 1)‖ ^ 2 = 1 := by
  rw [groverChebT_sq_sin m sq θ hsq, hθ, Real.cos_pi]
  simp

/-- For `0 < sq < 1`, some positive round count has squared Grover Chebyshev modulus at least `1
- sq`. -/
private theorem groverOptimal_exists (sq : ℝ) (h0 : 0 < sq) (h1 : sq < 1) :
    ∃ m : ℕ, 1 ≤ m ∧ 1 - sq ≤ ‖groverChebT m (2 * (sq : ℂ) - 1)‖ ^ 2 := by
  have hr0 : 0 < Real.sqrt sq := Real.sqrt_pos.mpr h0
  have hr1 : Real.sqrt sq < 1 := by
    by_contra hc
    have hge : 1 ≤ Real.sqrt sq := le_of_not_gt hc
    have hs := Real.sq_sqrt h0.le
    have hge2 : 1 ≤ Real.sqrt sq ^ 2 := by nlinarith [hge]
    rw [hs] at hge2
    linarith
  set θ := Real.arcsin (Real.sqrt sq) with hθdef
  have hsin : Real.sin θ = Real.sqrt sq :=
    Real.sin_arcsin (by linarith) (by linarith)
  have hθnn : 0 ≤ θ := Real.arcsin_nonneg.mpr hr0.le
  have hθ0 : 0 < θ := by
    rcases lt_or_eq_of_le hθnn with hpos | hzero
    · exact hpos
    · rw [← hzero] at hsin
      simp at hsin
      linarith
  have hθ2 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsqθ : sq = Real.sin θ ^ 2 := by
    rw [hsin, Real.sq_sqrt h0.le]
  have hθne : (2 * θ) ≠ 0 := by positivity
  set x := Real.pi / (2 * θ) with hxdef
  have hx1 : 1 ≤ x := by
    rw [hxdef, le_div_iff₀ (show 0 < 2 * θ by positivity)]
    nlinarith [Real.pi_pos, hθ2]
  set n := Int.floor (x + 1 / 2) with hndef
  have hn1 : 1 ≤ n := by
    have hf := Int.floor_le_floor (show ((1 : ℝ) + 1 / 2) ≤ x + 1 / 2 by linarith)
    have hfl : Int.floor ((1 : ℝ) + 1 / 2) = 1 := by norm_num
    rw [hfl] at hf
    exact hf
  have hf1 : (n : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have hf2 : x + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hxn : |x - (n : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hnCast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by linarith)
  refine ⟨n.toNat, Nat.one_le_cast.mp (by rw [hnCast]; exact_mod_cast hn1), ?_⟩
  have hpx : 2 * θ * x = Real.pi := by
    rw [hxdef]
    field_simp
  have hdist : |2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi| ≤ θ := by
    rw [hnCast, ← hpx]
    have hfac : 2 * (n : ℝ) * θ - (2 * θ) * x = (2 * θ) * ((n : ℝ) - x) := by
      ring
    rw [hfac, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 * θ by positivity),
      abs_sub_comm]
    have hmul := mul_le_mul_of_nonneg_left hxn (show (0 : ℝ) ≤ 2 * θ by positivity)
    have hhalf : (2 * θ) * (1 / 2) = θ := by ring
    linarith
  rw [groverChebT_sq_sin (n.toNat) sq θ hsqθ]
  have hangle : ((n.toNat : ℕ) : ℝ) * (2 * θ)
      = 2 * ((n.toNat : ℕ) : ℝ) * θ := by ring
  rw [hangle]
  have hshift : Real.cos (2 * ((n.toNat : ℕ) : ℝ) * θ) ^ 2
      = Real.cos (2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi) ^ 2 := by
    have h1 : Real.cos (2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi)
        = -Real.cos (2 * ((n.toNat : ℕ) : ℝ) * θ) := by
      rw [Real.cos_sub_pi]
    rw [h1, neg_sq]
  rw [hshift]
  have hcosabs : ∀ u : ℝ, Real.cos |u| ^ 2 = Real.cos u ^ 2 := by
    intro u
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (by linarith : u < 0), Real.cos_neg]
  rw [← hcosabs]
  have hδθ : |2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi| ≤ θ := hdist
  have hδ0 : 0 ≤ |2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi| := abs_nonneg _
  have hδπ : |2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi| ≤ Real.pi :=
    le_trans hδθ (by linarith)
  have hcosmono : Real.cos θ
      ≤ Real.cos |2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi| :=
    Real.strictAntiOn_cos.antitoneOn
      (Set.mem_Icc.mpr ⟨hδ0, hδπ⟩)
      (Set.mem_Icc.mpr ⟨hθnn, le_trans hθ2 (by linarith)⟩) hδθ
  have hcθ : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr ⟨by linarith, hθ2⟩)
  have hcδ : 0 ≤ Real.cos |2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi| :=
    Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr ⟨by linarith, le_trans hδθ hθ2⟩)
  have hsquares : Real.cos θ ^ 2
      ≤ Real.cos |2 * ((n.toNat : ℕ) : ℝ) * θ - Real.pi| ^ 2 :=
    by nlinarith [hcosmono, hcθ, hcδ]
  have hcosθ : Real.cos θ ^ 2 = 1 - sq := by
    have h := Real.cos_sq_add_sin_sq θ
    rw [← hsqθ] at h
    linarith
  linarith

/-- For `0 < sq < 1`, there is a round count with squared Grover Chebyshev modulus at least `1 -
sq`. -/
theorem groverOptimal_rounds (sq : ℝ) (h0 : 0 < sq) (h1 : sq < 1) :
    ∃ m : ℕ, 1 - sq ≤ ‖groverChebT m (2 * (sq : ℂ) - 1)‖ ^ 2 := by
  obtain ⟨m, _, hm⟩ := groverOptimal_exists sq h0 h1
  exact ⟨m, hm⟩

/-- For `0 < sq < 1`, a round count of the form `m + 1` achieves squared Grover Chebyshev
modulus at least `1 - sq`. -/
theorem groverOptimal_rounds_succ (sq : ℝ) (h0 : 0 < sq) (h1 : sq < 1) :
    ∃ m : ℕ, 1 - sq ≤ ‖groverChebT (m + 1) (2 * (sq : ℂ) - 1)‖ ^ 2 := by
  obtain ⟨m, hm1, hm2⟩ := groverOptimal_exists sq h0 h1
  have hmp : m - 1 + 1 = m := Nat.sub_add_cancel hm1
  exact ⟨m - 1, by rwa [hmp]⟩

/-- Under the scalar squared-block condition with `0 < sq < 1`, some round count achieves
`none`-branch probability at least `1 - sq` minus the accumulated probability error. -/
theorem groverBorn_none_optimal {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℝ) (h0 : 0 < sq) (h1 : sq < 1)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = (sq : ℂ) • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ∃ m : ℕ, 1 - sq - 2 * (m * (128 * (D + 1) / 2 ^ k))
      ≤ MeasureProb (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none)) := by
  obtain ⟨m, hmopt⟩ := groverOptimal_rounds sq h0 h1
  refine ⟨m, ?_⟩
  have h := groverBorn_none m k w amp hw hm U hU (sq : ℂ) hA ψ hψ
  have hle := abs_le.mp h
  linarith

/-- Under the scalar squared-block condition with `0 < sq < 1`, a suitable positive round count
and the specified precision give `none`-branch probability at least `1 - sq - ε`. -/
theorem groverBorn_none_optimal_epsilon {D : ℕ} {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (ε : ℚ) (hε : 0 < ε)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℝ) (h0 : 0 < sq) (h1 : sq < 1)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = (sq : ℂ) • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    ∃ m : ℕ, 1 - sq - (ε : ℝ)
      ≤ MeasureProb (evaluate 1 (groverWordRepeat (m + 1)
          (precisionFor D (ε / (8 * (m + 1)))) w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none)) := by
  obtain ⟨m, hmopt⟩ := groverOptimal_rounds_succ sq h0 h1
  refine ⟨m, ?_⟩
  have h := groverBorn_none_epsilon m ε hε w amp hw hm U hU (sq : ℂ) hA ψ hψ
  have hle := abs_le.mp h
  linarith

/-- The data state obtained from `MeasureCollapse` on the event that the control register equals
`none`. -/
noncomputable def measureCollapse_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (u : QState (Option (Fin D) × X)) : QState X :=
  PostMeasure (cleanBranch u) Finset.univ

/-- The collapsed `none`-branch state vector is the normalization of the clean-branch state
vector. -/
theorem stateVector_measureCollapse_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (u : QState (Option (Fin D) × X)) :
    stateVector (measureCollapse_none u)
      = NormedSpace.normalize (stateVector (cleanBranch u)) := by
  rw [measureCollapse_none, stateVector_postMeasure_univ]

/-- If the clean branch is nonzero, its collapsed state has Euclidean norm one. -/
theorem measureCollapse_none_norm {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {u : QState (Option (Fin D) × X)} (hu : cleanBranch u ≠ 0) :
    ‖stateVector (measureCollapse_none u)‖ = 1 := by
  rw [stateVector_measureCollapse_none]
  exact NormedSpace.norm_normalize ((stateVector_eq_zero_iff _).not.mpr hu)

/-- Normalizing a nonzero scalar multiple of a unit vector extracts the scalar's unit complex
phase. -/
private theorem normalize_smul_cne {X : Type*} [Fintype X] [DecidableEq X] {c : ℂ}
    (_hc : c ≠ 0) {v : EuclideanSpace ℂ X} (hv : ‖v‖ = 1) :
    NormedSpace.normalize (c • v) = (c / ((‖c‖ : ℝ) : ℂ)) • v := by
  rw [NormedSpace.normalize, norm_smul, hv, mul_one, div_eq_inv_mul]
  ext i
  simp [Complex.real_smul]
  ring

/-- Collapsing the exact linear-combination output onto control `none` normalizes the weighted
operator sum applied to the input. -/
theorem lcuExact_collapse {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (ψ : QState X) :
    stateVector (measureCollapse_none ((TensorGate (exactPrepareMatrix w amp)ᴴ 1
        * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
      = NormedSpace.normalize
          (stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)) := by
  rw [stateVector_measureCollapse_none, lcuExact_apply w amp hw hm U ψ]

/-- If `p₀ > 0` bounds the ideal output norm from below and exceeds the approximation error, the
normalized linear-combination output error is at most `2 * (64 * (D + 1) / 2^k) / p₀`. -/
theorem lcuWord_collapse_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hpA : p₀ ≤ ‖stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)‖)
    (hk : 64 * (D + 1) / 2 ^ k < p₀) :
    ‖stateVector (measureCollapse_none (evaluate 1 (lcuBlockWord k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - NormedSpace.normalize
            (stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ))‖
      ≤ 2 * (64 * (D + 1) / 2 ^ k) / p₀ := by
  have hclose := lcuWord_apply_state k w amp hw hm U hU ψ
  rw [hψ, mul_one] at hclose
  rw [stateVector_measureCollapse_none]
  obtain ⟨_, hb⟩ := normalize_error_of_gap hclose (hk.trans_le hpA)
  exact hb.trans (div_le_div_of_nonneg_left (by positivity) hp₀ hpA)

/-- For `p > 0`, the inequality `δ ≤ p * e / 2` implies `2 * δ / p ≤ e`. -/
private theorem collapse_eps_arith {δ e p : ℝ} (hp : 0 < p)
    (hδ : δ ≤ p * e / 2) : 2 * δ / p ≤ e := by
  rw [div_le_iff₀ hp]
  linarith

/-- For `p > 0` and `e ≤ 1`, the quantity `p * e / 2` is strictly less than `p`. -/
private theorem half_budget_lt {p e : ℝ} (hp : 0 < p) (he : e ≤ 1) :
    p * e / 2 < p := by
  have h2 : p * e < p * 2 := by nlinarith [hp, he]
  exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr h2

/-- For `0 < ε ≤ 1` and a positive rational lower bound `p₀` on the ideal output norm, precision
`precisionFor D (p₀ * ε / 4)` gives collapsed-state error at most `ε`. -/
theorem lcuWord_collapse_none_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p₀ : ℚ) (hp₀ : 0 < p₀)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1)
    (hpA : ((p₀ : ℚ) : ℝ)
      ≤ ‖stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ)‖) :
    ‖stateVector (measureCollapse_none (evaluate 1
          (lcuBlockWord (precisionFor D (p₀ * ε / 4)) w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - NormedSpace.normalize
            (stateVector ((∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a) *ᵥ ψ))‖
      ≤ (ε : ℝ) := by
  have hb := prepError_le_epsilon (D := D) (p₀ * ε / 4) (by positivity)
  have hcast : ((p₀ * ε / 4 : ℚ) : ℝ) = ((p₀ : ℚ) : ℝ) * (ε : ℝ) / 4 := by
    push_cast
    ring
  rw [hcast] at hb
  have hδ : 64 * (D + 1) / 2 ^ precisionFor D (p₀ * ε / 4)
      ≤ ((p₀ : ℚ) : ℝ) * (ε : ℝ) / 2 := by
    have hsplit : 64 * ((D : ℝ) + 1)
          / (2 ^ precisionFor D (p₀ * ε / 4) : ℝ)
        = 2 * (32 * ((D : ℝ) + 1)
            / (2 ^ precisionFor D (p₀ * ε / 4) : ℝ)) := by
      field_simp
      ring
    rw [hsplit]
    linarith
  have h := lcuWord_collapse_none (precisionFor D (p₀ * ε / 4)) w amp hw hm U hU ψ hψ
    ((p₀ : ℚ) : ℝ) (by exact_mod_cast hp₀) hpA
    (hδ.trans_lt (half_budget_lt (by exact_mod_cast hp₀) (by exact_mod_cast hε1)))
  exact h.trans (collapse_eps_arith (by exact_mod_cast hp₀) hδ)

/-- When the Grover Chebyshev coefficient is nonzero, collapsing the exact Grover output gives
the normalized input multiplied by that coefficient's unit complex phase. -/
theorem groverCollapse_exact_phase {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (m : ℕ) (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1)
    (hT : groverChebT m (2 * sq - 1) ≠ 0) :
    stateVector (measureCollapse_none ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1
        * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
      = ((groverChebT m (2 * sq - 1) / ((‖groverChebT m (2 * sq - 1)‖ : ℝ) : ℂ))
          • stateVector ψ) := by
  rw [stateVector_measureCollapse_none,
    groverPower_state_exact w amp hw hm U hU sq hA m ψ]
  have hsm : stateVector (groverChebT m (2 * sq - 1) • ψ)
      = groverChebT m (2 * sq - 1) • stateVector ψ := by
    simp [stateVector, WithLp.toLp_smul]
  rw [hsm, normalize_smul_cne hT hψ]

/-- If `p₀ > 0` bounds the Chebyshev modulus from below and exceeds the accumulated
approximation error, the collapsed Grover output differs from the phase-scaled input by at
most twice that error divided by `p₀`. -/
theorem groverWord_collapse_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (m k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hpT : p₀ ≤ ‖groverChebT m (2 * sq - 1)‖)
    (hk : m * (128 * (D + 1) / 2 ^ k) < p₀) :
    ‖stateVector (measureCollapse_none
          (evaluate 1 (groverWordRepeat m k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - ((groverChebT m (2 * sq - 1) / ((‖groverChebT m (2 * sq - 1)‖ : ℝ) : ℂ))
            • stateVector ψ)‖
      ≤ 2 * (m * (128 * (D + 1) / 2 ^ k)) / p₀ := by
  have hT : groverChebT m (2 * sq - 1) ≠ 0 :=
    norm_pos_iff.mp (hp₀.trans_le hpT)
  have hclose := groverWordRepeat_state_error m k w amp hw hm U hU sq hA ψ
  rw [hψ, mul_one] at hclose
  rw [stateVector_measureCollapse_none]
  have hsm : stateVector (groverChebT m (2 * sq - 1) • ψ)
      = groverChebT m (2 * sq - 1) • stateVector ψ := by
    simp [stateVector, WithLp.toLp_smul]
  rw [hsm] at hclose
  have hnormT : ‖groverChebT m (2 * sq - 1) • stateVector ψ‖
      = ‖groverChebT m (2 * sq - 1)‖ := by
    rw [norm_smul, hψ, mul_one]
  obtain ⟨_, hb⟩ := normalize_error_of_gap hclose
    (by rw [hnormT]; exact hk.trans_le hpT)
  rw [normalize_smul_cne hT hψ] at hb
  refine hb.trans (div_le_div_of_nonneg_left (by positivity) hp₀ ?_)
  rw [hnormT]
  exact hpT

/-- For `0 < ε ≤ 1` and a positive rational lower bound on the Chebyshev modulus, the specified
precision makes the collapsed Grover output error at most `ε`. -/
theorem groverWord_collapse_none_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p₀ : ℚ) (hp₀ : 0 < p₀)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = sq • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1)
    (hpT : ((p₀ : ℚ) : ℝ) ≤ ‖groverChebT m (2 * sq - 1)‖) :
    ‖stateVector (measureCollapse_none (evaluate 1
          (groverWordRepeat m (precisionFor D (p₀ * ε / (8 * (m + 1)))) w amp
            (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
        - ((groverChebT m (2 * sq - 1) / ((‖groverChebT m (2 * sq - 1)‖ : ℝ) : ℂ))
            • stateVector ψ)‖
      ≤ (ε : ℝ) := by
  have hb := prepError_le_epsilon (D := D) (p₀ * ε / (8 * (m + 1))) (by positivity)
  have hcast : ((p₀ * ε / (8 * (m + 1)) : ℚ) : ℝ)
      = ((p₀ : ℚ) : ℝ) * (ε : ℝ) / (8 * ((m : ℝ) + 1)) := by
    push_cast
    ring
  rw [hcast] at hb
  have hδ : m * (128 * (D + 1) / 2 ^ precisionFor D (p₀ * ε / (8 * (m + 1))))
      ≤ ((p₀ : ℚ) : ℝ) * (ε : ℝ) / 2 := by
    have hsplit : ((m : ℝ)) * (128 * ((D : ℝ) + 1)
          / (2 ^ precisionFor D (p₀ * ε / (8 * (m + 1))) : ℝ))
        = (4 * (m : ℝ)) * (32 * ((D : ℝ) + 1)
            / (2 ^ precisionFor D (p₀ * ε / (8 * (m + 1))) : ℝ)) := by
      field_simp
      ring
    rw [hsplit]
    have h4 : (4 * (m : ℝ)) * (32 * ((D : ℝ) + 1)
          / (2 ^ precisionFor D (p₀ * ε / (8 * (m + 1))) : ℝ))
        ≤ (4 * (m : ℝ)) * (((p₀ : ℚ) : ℝ) * (ε : ℝ) / (8 * ((m : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    refine h4.trans ?_
    have hkey : (4 * (m : ℝ)) * (((p₀ : ℚ) : ℝ) * (ε : ℝ) / (8 * ((m : ℝ) + 1)))
        = ((m : ℝ) / ((m : ℝ) + 1)) * ((((p₀ : ℚ) : ℝ) * (ε : ℝ)) / 2) := by
      field_simp
      ring
    have hmM : ((m : ℝ) / ((m : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      linarith
    rw [hkey]
    have hq : (0 : ℝ) ≤ ((p₀ : ℚ) : ℝ) * (ε : ℝ) := by
      have h1 : (0 : ℝ) ≤ ((p₀ : ℚ) : ℝ) := by exact_mod_cast hp₀.le
      have h2 : (0 : ℝ) ≤ ((ε : ℚ) : ℝ) := by exact_mod_cast hε.le
      exact mul_nonneg h1 h2
    refine (mul_le_mul_of_nonneg_right hmM
      (div_nonneg hq (by norm_num : (0 : ℝ) ≤ 2))).trans ?_
    exact le_of_eq (by ring)
  have h := groverWord_collapse_none m
    (precisionFor D (p₀ * ε / (8 * (m + 1)))) w amp hw hm U hU sq hA ψ hψ
    ((p₀ : ℚ) : ℝ) (by exact_mod_cast hp₀) hpT
    (hδ.trans_lt (half_budget_lt (by exact_mod_cast hp₀) (by exact_mod_cast hε1)))
  exact h.trans (collapse_eps_arith (by exact_mod_cast hp₀) hδ)

/-- Under `sq = sin² θ` and `m * (2 * θ) = π`, the exact collapsed Grover output equals the
input multiplied by the Grover Chebyshev coefficient. -/
theorem groverCollapse_hit {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (m : ℕ) (sq θ : ℝ) (hsq : sq = Real.sin θ ^ 2)
    (hθ : ((m : ℕ) : ℝ) * (2 * θ) = Real.pi)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = (sq : ℂ) • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    stateVector (measureCollapse_none ((groverRound (TensorGate (exactPrepareMatrix w amp)ᴴ 1
        * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ m *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ))
      = groverChebT m (2 * (sq : ℂ) - 1) • stateVector ψ := by
  have hsq1 : ‖groverChebT m (2 * (sq : ℂ) - 1)‖ ^ 2 = 1 :=
    groverChebT_sq_sin_hit m sq θ hsq hθ
  have hn : ‖groverChebT m (2 * (sq : ℂ) - 1)‖ = 1 := by
    have hnn := norm_nonneg (groverChebT m (2 * (sq : ℂ) - 1))
    nlinarith [hsq1, hnn]
  have hT : groverChebT m (2 * (sq : ℂ) - 1) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [groverCollapse_exact_phase w amp hw hm U hU (sq : ℂ) hA m ψ hψ hT, hn]
  norm_num

/-- The diagonal matrix that fixes control `none` and multiplies all other control components by
`z`. -/
def reflectPhase {D : ℕ} {X : Type*} [DecidableEq X] (z : ℂ) :
    Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ :=
  Matrix.diagonal fun p : Option (Fin D) × X => if p.1 = none then (1 : ℂ) else z

/-- The phase reflection with phase minus one is `reflectNone`. -/
theorem reflectPhase_neg_one {D : ℕ} {X : Type*} [DecidableEq X] :
    reflectPhase (D := D) (X := X) (-1) = reflectNone (D := D) (X := X) := by
  ext p q
  simp [reflectPhase, reflectNone]

/-- The phase reflection is unitary when `z` has norm one. -/
theorem reflectPhase_unitary {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] {z : ℂ}
    (hz : ‖z‖ = 1) :
    reflectPhase (D := D) (X := X) z ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  by_cases h : p.1 = none
  · simp only [if_pos h]
    norm_num
  · simp only [if_neg h]
    exact star_mul_self_of_norm_one hz

/-- The single-gate circuit word implementing `reflectPhase z`. -/
def reflectPhaseWord {D : ℕ} {X : Type*} [DecidableEq X] (z : ℂ) :
    List (AdjointStep (Option (Fin D) × X)) := [.gate (reflectPhase z)]

/-- The phase reflection word evaluates to `reflectPhase z`. -/
theorem reflectPhaseWord_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ) :
    evaluate 1 (reflectPhaseWord (D := D) (X := X) z) = reflectPhase z := by
  simp [reflectPhaseWord, evaluate, instructionMatrix]

/-- The phase reflection word has one gate and zero queries. -/
theorem reflectPhaseWord_counts {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ) :
    adjointGateCount (reflectPhaseWord (D := D) (X := X) z) = 1 ∧
      adjointQueryCount (reflectPhaseWord (D := D) (X := X) z) = 0 := by
  simp [reflectPhaseWord, adjointGateCount, adjointQueryCount]

/-- A phase reflection word is well formed when its phase has norm one. -/
theorem reflectPhaseWord_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {z : ℂ} (hz : ‖z‖ = 1) :
    WellFormedAdjointCircuit (reflectPhaseWord (D := D) (X := X) z) := by
  simp [reflectPhaseWord, reflectPhase_unitary hz]

/-- Left multiplication by a phase reflection preserves the rows with control index `none`. -/
theorem reflectPhase_mul_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (q : Option (Fin D) × X) (x : X) :
    (reflectPhase (D := D) (X := X) z * M) (none, x) q = M (none, x) q := by
  simp only [Matrix.mul_apply, reflectPhase, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (none, x)]
  · simp
  · intro s _ hs
    rw [if_neg (fun h => absurd h.symm hs)]
    simp
  · intro hs
    exact absurd (Finset.mem_univ (none, x)) hs

/-- Left multiplication by a phase reflection preserves the `none` block. -/
theorem blockNone_reflectPhase_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (z : ℂ) (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    blockNone (reflectPhase (D := D) (X := X) z * M) = blockNone M := by
  ext x y
  simp only [blockNone]
  rw [reflectPhase_mul_noneRow]

/-- Left multiplication by a phase reflection preserves each row block with output control
`none`. -/
theorem reflectPhase_rowBlock_noneRow {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (z : ℂ) (a : Option (Fin D)) (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    rowBlock a (reflectPhase (D := D) (X := X) z * M) = rowBlock a M := by
  ext x z'
  simp only [rowBlock]
  rw [reflectPhase_mul_noneRow]

/-- Left multiplication by `reflectPhase z` multiplies a column block with output control
different from `none` by `z`. -/
theorem colBlock_reflectPhase_mul {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (a : Option (Fin D)) (M : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (ha : a ≠ none) :
    colBlock a (reflectPhase (D := D) (X := X) z * M) = z • colBlock a M := by
  ext z' y
  have hd : ∀ p r, (reflectPhase (D := D) (X := X) z * M) p r
      = (if p.1 = none then (1 : ℂ) else z) * M p r := by
    intro p r
    simp only [Matrix.mul_apply, reflectPhase, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single p]
    · simp
    · intro s _ hs
      rw [if_neg (fun h => absurd h.symm hs)]
      simp
    · intro hs
      exact absurd (Finset.mem_univ p) hs
  simp only [colBlock, hd]
  rw [if_neg ha]
  simp [colBlock]

/-- Every phase reflection fixes the clean embedding. -/
theorem reflectPhase_mul_cleanEmbed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ) :
    ((reflectPhase (D := D) (X := X) z) * (cleanEmbed (D := D) (X := X)))
      = cleanEmbed (D := D) (X := X) := by
  ext p y
  obtain ⟨a, b⟩ := p
  have hd : ((reflectPhase (D := D) (X := X) z)
      * (cleanEmbed (D := D) (X := X))) (a, b) y
      = (if a = none then (1 : ℂ) else z)
          * (cleanEmbed (D := D) (X := X)) (a, b) y := by
    simp only [Matrix.mul_apply, reflectPhase, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (a, b)]
    · simp
    · intro q _ hq
      rw [if_neg (fun h => absurd h.symm hq)]
      simp
    · intro hq
      exact absurd (Finset.mem_univ (a, b)) hq
  rw [hd]
  cases a with
  | none => rw [if_pos rfl]; simp
  | some i =>
      rw [if_neg (by simp)]
      have hE : (cleanEmbed (D := D) (X := X)) (some i, b) y = 0 := by
        simp only [cleanEmbed]
        exact if_neg (by simp)
      rw [hE]
      simp

/-- Left multiplication by `reflectPhase z` scales a matrix by `z` when its rows with control
index `none` vanish. -/
theorem reflectPhase_mul_of_noneRow_zero {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (z : ℂ) (M : Matrix (Option (Fin D) × X) X ℂ)
    (hM : ∀ x y, M (none, x) y = 0) :
    ((reflectPhase (D := D) (X := X) z) * M) = z • M := by
  ext p y
  obtain ⟨a, b⟩ := p
  have hd : ((reflectPhase (D := D) (X := X) z) * M) (a, b) y
      = (if a = none then (1 : ℂ) else z) * M (a, b) y := by
    simp only [Matrix.mul_apply, reflectPhase, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (a, b)]
    · simp
    · intro q _ hq
      rw [if_neg (fun h => absurd h.symm hq)]
      simp
    · intro hq
      exact absurd (Finset.mem_univ (a, b)) hq
  rw [hd]
  cases a with
  | none =>
      rw [if_pos rfl]
      simp [Matrix.smul_apply, hM b y]
  | some i =>
      rw [if_neg (by simp)]
      simp [Matrix.smul_apply, smul_eq_mul]

/-- The matrix `reflectPhase z * Uᴴ * reflectPhase z * U` for a phase-modified Grover round. -/
noncomputable def phaseRound {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ :=
  reflectPhase z * Uᴴ * reflectPhase z * U

/-- A phase-modified round with phase minus one equals `groverRound`. -/
theorem phaseRound_neg_one {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    phaseRound (-1) U = groverRound U := by
  rw [phaseRound, groverRound, reflectPhase_neg_one]

/-- A phase-modified round is unitary when the phase has norm one and `U` is unitary. -/
theorem phaseRound_unitary {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] {z : ℂ}
    (hz : ‖z‖ = 1)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    phaseRound z U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ := by
  have hR := reflectPhase_unitary (D := D) (X := X) hz
  exact (Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem
    ((Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem
      ((Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem hR (adjoint_unitary hU)) hR) hU

/-- For unitary `U`, the `none` block of the phase round is `1 + (z - 1) • (1 - (blockNone U)ᴴ *
blockNone U)`. -/
theorem phaseRound_topBlock_exact {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    blockNone (phaseRound z U)
      = 1 + (z - 1) • (1 - (blockNone U)ᴴ * blockNone U) := by
  have hE : reflectPhase z * Uᴴ * reflectPhase z * U
      = (reflectPhase (D := D) (X := X) z * Uᴴ)
        * (reflectPhase (D := D) (X := X) z * U) := by rw [← Matrix.mul_assoc]
  rw [phaseRound, hE, blockNone_mul_expand, blockNone_reflectPhase_noneRow,
    blockNone_reflectPhase_noneRow, blockNone_adjoint U]
  have hcol : ∀ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
      rowBlock a (reflectPhase (D := D) (X := X) z * Uᴴ)
        * colBlock a (reflectPhase (D := D) (X := X) z * U)
        = z • ((colBlock a U)ᴴ * colBlock a U) := by
    intro a ha
    rw [reflectPhase_rowBlock_noneRow, rowBlock_adjoint,
      colBlock_reflectPhase_mul z a U (Finset.mem_filter.mp ha |>.2), Matrix.mul_smul]
  rw [Finset.sum_congr rfl hcol, ← Finset.smul_sum]
  have hsum := unitary_noneCol_sum U hU
  have hS : ∑ a ∈ Finset.univ.filter (fun a : Option (Fin D) => a ≠ none),
      (colBlock a U)ᴴ * colBlock a U
      = 1 - blockNone Uᴴ * blockNone U := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum
  rw [hS, smul_sub]
  have hfin : (blockNone U)ᴴ * blockNone U + (z • (1 : Matrix X X ℂ)
        - z • ((blockNone U)ᴴ * blockNone U))
      = 1 + (z - 1) • (1 - (blockNone U)ᴴ * blockNone U) := by
    module
  exact hfin

/-- If the squared `none` block is `sq • 1`, the phase round has `none` block `(sq + z * (1 -
sq)) • 1`. -/
theorem phaseRound_topBlock_step {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    blockNone (phaseRound z U) = (sq + z * (1 - sq)) • (1 : Matrix X X ℂ) := by
  rw [phaseRound_topBlock_exact z U hU, hA]
  have h1 : (1 : Matrix X X ℂ) - sq • (1 : Matrix X X ℂ) = (1 - sq) • 1 := by module
  rw [h1, smul_smul]
  have hfin : (1 : Matrix X X ℂ) + ((z - 1) * (1 - sq)) • (1 : Matrix X X ℂ)
      = (sq + z * (1 - sq)) • (1 : Matrix X X ℂ) := by module
  rw [hfin]

/-- Under the scalar squared-block condition, the phase-round and Grover-round `none` blocks
differ by `((1 + z) * (1 - sq)) • 1`. -/
theorem phaseRound_mismatch {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    blockNone (phaseRound z U) - blockNone (groverRound U)
      = ((1 + z) * (1 - sq)) • (1 : Matrix X X ℂ) := by
  have hsign : blockNone (groverRound U) = (2 * sq - 1) • (1 : Matrix X X ℂ) := by
    have h1 := phaseRound_topBlock_step (-1) U hU sq hA
    rw [phaseRound_neg_one U] at h1
    have hrw : sq + (-1 : ℂ) * (1 - sq) = 2 * sq - 1 := by ring
    rw [hrw] at h1
    exact h1
  rw [phaseRound_topBlock_step z U hU sq hA, hsign, ← sub_smul]
  have hsc : (sq + z * (1 - sq)) - (2 * sq - 1) = (1 + z) * (1 - sq) := by ring
  rw [hsc]

/-- The norm of a complex scalar times the identity matrix is at most the norm of the scalar. -/
private theorem smul_one_opNorm_le {X : Type*} [Fintype X] [DecidableEq X] (c : ℂ) :
    ‖c • (1 : Matrix X X ℂ)‖ ≤ ‖c‖ := by
  have hdiag : c • (1 : Matrix X X ℂ) = Matrix.diagonal (fun _ : X => c) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hdiag, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (norm_nonneg c)]
  exact fun _ => le_refl _

/-- Under the scalar squared-block condition, the `none`-block mismatch between phase and Grover
rounds is at most `‖1 + z‖ * ‖1 - sq‖`. -/
theorem phaseRound_mismatch_norm {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    ‖blockNone (phaseRound z U) - blockNone (groverRound U)‖
      ≤ ‖1 + z‖ * ‖1 - sq‖ := by
  rw [phaseRound_mismatch z U hU sq hA]
  calc ‖((1 + z) * (1 - sq)) • (1 : Matrix X X ℂ)‖
      ≤ ‖(1 + z) * (1 - sq)‖ := smul_one_opNorm_le _
    _ = ‖1 + z‖ * ‖1 - sq‖ := Complex.norm_mul _ _

/-- Under the scalar squared-block condition, the phase round maps the clean embedding to the
linear combination of clean embedding and leakage with coefficients `sq + z * (1 - sq)` and
`z * (1 - z)`. -/
theorem phaseRound_mul_cleanEmbed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    (phaseRound z U) * (cleanEmbed (D := D) (X := X))
      = (sq + z * (1 - sq)) • (cleanEmbed (D := D) (X := X))
        + (z * (1 - z)) • groverLeak U sq := by
  have hUhU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  have hRE : ((reflectPhase (D := D) (X := X) z) * (cleanEmbed (D := D) (X := X)))
      = cleanEmbed (D := D) (X := X) := reflectPhase_mul_cleanEmbed z
  have hREA : ((reflectPhase (D := D) (X := X) z)
      * ((cleanEmbed (D := D) (X := X)) * blockNone U))
      = (cleanEmbed (D := D) (X := X)) * blockNone U := by
    rw [← Matrix.mul_assoc, hRE]
  have hUE : U * (cleanEmbed (D := D) (X := X))
      = ((cleanEmbed (D := D) (X := X)) * blockNone U)
        + (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    abel
  have hBadnone : ∀ x y : X,
      (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) (none, x) y = 0 := by
    intro x y
    rw [Matrix.sub_apply, mul_cleanEmbed_apply (D := D) (X := X)
      (Y := Option (Fin D) × X) U (none, x) y, cleanEmbed_mul_apply (D := D) (X := X)
      (blockNone U) (none, x) y]
    exact sub_self _
  have hRBad : ((reflectPhase (D := D) (X := X) z)
      * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U))
      = z • (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) :=
    reflectPhase_mul_of_noneRow_zero z _ hBadnone
  have hRleak : ((reflectPhase (D := D) (X := X) z) * groverLeak U sq)
      = z • groverLeak U sq :=
    reflectPhase_mul_of_noneRow_zero z _ (groverLeak_noneRow U sq hA)
  have hUhEA : Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U)
      = groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)) := by
    rw [groverLeak]
    abel
  have hUhBad : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq := by
    have h1 : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
        = Uᴴ * U * (cleanEmbed (D := D) (X := X))
          - Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h1, hUhU, Matrix.one_mul, hUhEA]
    module
  have hRUE : (reflectPhase (D := D) (X := X) z)
          * (U * (cleanEmbed (D := D) (X := X)))
      = ((cleanEmbed (D := D) (X := X)) * blockNone U)
        + z • (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    rw [hUE, Matrix.mul_add, hREA, hRBad]
    module
  have hQ : (phaseRound z U) * (cleanEmbed (D := D) (X := X))
      = (reflectPhase (D := D) (X := X) z)
          * (Uᴴ * ((reflectPhase (D := D) (X := X) z)
              * (U * (cleanEmbed (D := D) (X := X))))) := by
    rw [phaseRound, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have hR1 : (reflectPhase (D := D) (X := X) z)
      * (groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)))
      = sq • (cleanEmbed (D := D) (X := X)) + z • groverLeak U sq := by
    rw [Matrix.mul_add, Matrix.mul_smul, hRE, hRleak]
    abel
  have hR2 : (reflectPhase (D := D) (X := X) z)
      * ((1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) - z • groverLeak U sq := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hRE, hRleak]
  rw [hQ, hRUE, Matrix.mul_add, Matrix.mul_smul, hUhEA, hUhBad, Matrix.mul_add,
    Matrix.mul_smul, hR1, hR2]
  module

/-- Under the scalar squared-block condition, the phase round maps leakage to the linear
combination with coefficients `sq * (1 - sq) * (1 - z)` and `z * (1 - sq + sq * z)`. -/
theorem phaseRound_mul_groverLeak {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ)
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) (sq : ℂ)
    (hA : (blockNone U)ᴴ * blockNone U = sq • 1) :
    (phaseRound z U) * groverLeak U sq
      = (sq * (1 - sq) * (1 - z)) • (cleanEmbed (D := D) (X := X))
        + (z * (1 - sq + sq * z)) • groverLeak U sq := by
  have hUUhU : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hU
  have hUhU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  have hRE : ((reflectPhase (D := D) (X := X) z) * (cleanEmbed (D := D) (X := X)))
      = cleanEmbed (D := D) (X := X) := reflectPhase_mul_cleanEmbed z
  have hREA : ((reflectPhase (D := D) (X := X) z)
      * ((cleanEmbed (D := D) (X := X)) * blockNone U))
      = (cleanEmbed (D := D) (X := X)) * blockNone U := by
    rw [← Matrix.mul_assoc, hRE]
  have hUE : U * (cleanEmbed (D := D) (X := X))
      = ((cleanEmbed (D := D) (X := X)) * blockNone U)
        + (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    abel
  have hBadnone : ∀ x y : X,
      (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) (none, x) y = 0 := by
    intro x y
    rw [Matrix.sub_apply, mul_cleanEmbed_apply (D := D) (X := X)
      (Y := Option (Fin D) × X) U (none, x) y, cleanEmbed_mul_apply (D := D) (X := X)
      (blockNone U) (none, x) y]
    exact sub_self _
  have hRBad : ((reflectPhase (D := D) (X := X) z)
      * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U))
      = z • (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U) :=
    reflectPhase_mul_of_noneRow_zero z _ hBadnone
  have hRleak : ((reflectPhase (D := D) (X := X) z) * groverLeak U sq)
      = z • groverLeak U sq :=
    reflectPhase_mul_of_noneRow_zero z _ (groverLeak_noneRow U sq hA)
  have hUhEA : Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U)
      = groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)) := by
    rw [groverLeak]
    abel
  have hUhBad : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq := by
    have h1 : Uᴴ * (U * (cleanEmbed (D := D) (X := X))
          - (cleanEmbed (D := D) (X := X)) * blockNone U)
        = Uᴴ * U * (cleanEmbed (D := D) (X := X))
          - Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h1, hUhU, Matrix.one_mul, hUhEA]
    module
  have hUL : U * groverLeak U sq
      = (1 - sq) • ((cleanEmbed (D := D) (X := X)) * blockNone U)
        - sq • (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    have h1 : U * groverLeak U sq
        = U * (Uᴴ * ((cleanEmbed (D := D) (X := X)) * blockNone U))
          - U * (sq • (cleanEmbed (D := D) (X := X))) := by
      rw [groverLeak, Matrix.mul_sub, Matrix.mul_smul]
    rw [h1, ← Matrix.mul_assoc, hUUhU, Matrix.one_mul, Matrix.mul_smul, hUE]
    module
  have hRUL : (reflectPhase (D := D) (X := X) z)
      * ((1 - sq) • ((cleanEmbed (D := D) (X := X)) * blockNone U)
          - sq • (U * (cleanEmbed (D := D) (X := X))
              - (cleanEmbed (D := D) (X := X)) * blockNone U))
      = (1 - sq) • ((cleanEmbed (D := D) (X := X)) * blockNone U)
        - (sq * z) • (U * (cleanEmbed (D := D) (X := X))
            - (cleanEmbed (D := D) (X := X)) * blockNone U) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hREA, hRBad, smul_smul]
  have hQ : (phaseRound z U) * groverLeak U sq
      = (reflectPhase (D := D) (X := X) z)
          * (Uᴴ * ((reflectPhase (D := D) (X := X) z) * (U * groverLeak U sq))) := by
    rw [phaseRound, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have hR1 : (reflectPhase (D := D) (X := X) z)
      * (groverLeak U sq + sq • (cleanEmbed (D := D) (X := X)))
      = sq • (cleanEmbed (D := D) (X := X)) + z • groverLeak U sq := by
    rw [Matrix.mul_add, Matrix.mul_smul, hRE, hRleak]
    abel
  have hR2 : (reflectPhase (D := D) (X := X) z)
      * ((1 - sq) • (cleanEmbed (D := D) (X := X)) - groverLeak U sq)
      = (1 - sq) • (cleanEmbed (D := D) (X := X)) - z • groverLeak U sq := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hRE, hRleak]
  rw [hQ, hUL, hRUL, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    hUhEA, hUhBad, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hR1, hR2]
  module

/-- The complex phase `(-(1 - s) + I * sqrt (2 * s - 1)) / s` used for two-round oblivious
amplitude amplification. -/
noncomputable def oaaPhase (s : ℝ) : ℂ :=
  (-(1 - (s : ℂ)) + Complex.I * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ)) / (s : ℂ)

/-- The phase `oaaPhase s` has norm one for `s > 1 / 2`. -/
theorem oaaPhase_norm {s : ℝ} (hs : 1 / 2 < s) : ‖oaaPhase s‖ = 1 := by
  have hs0 : s ≠ 0 := by linarith
  have h2 : 0 ≤ 2 * s - 1 := by linarith
  have htsq : Real.sqrt (2 * s - 1) * Real.sqrt (2 * s - 1) = 2 * s - 1 := by
    rw [← sq]
    exact Real.sq_sqrt h2
  have hns : Complex.normSq (oaaPhase s) = 1 := by
    have hco : -(1 - (s : ℂ)) = ((-(1 - s) : ℝ) : ℂ) := by
      push_cast
      ring
    have hnum : Complex.normSq (-(1 - (s : ℂ))
        + Complex.I * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ)) = s * s := by
      rw [hco, mul_comm (Complex.I) ((Real.sqrt (2 * s - 1) : ℝ) : ℂ),
        Complex.normSq_add_mul_I, Real.sq_sqrt h2]
      ring
    have hden : Complex.normSq ((s : ℝ) : ℂ) = s * s := by
      simp [Complex.normSq]
    rw [oaaPhase, Complex.normSq_div, hnum, hden]
    field_simp
  have hp : ‖oaaPhase s‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  rcases sq_eq_one_iff.mp hp with h | h
  · exact h
  · linarith [norm_nonneg (oaaPhase s)]

/-- For `s ≥ 1 / 2`, the phase `oaaPhase s` satisfies `s * z² + 2 * (1 - s) * z + s = 0`. -/
theorem oaaPhase_quad {s : ℝ} (hs : 1 / 2 ≤ s) :
    (s : ℂ) * (oaaPhase s) ^ 2 + 2 * (1 - (s : ℂ)) * oaaPhase s + (s : ℂ) = 0 := by
  have hs0 : s ≠ 0 := by linarith
  have h2 : 0 ≤ 2 * s - 1 := by linarith
  have ht : ((Real.sqrt (2 * s - 1) : ℝ) : ℂ) * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ)
      = ((2 * s - 1 : ℝ) : ℂ) := by
    have h1 : Real.sqrt (2 * s - 1) * Real.sqrt (2 * s - 1) = 2 * s - 1 := by
      rw [← sq]
      exact Real.sq_sqrt h2
    exact_mod_cast h1
  have hco : ((2 * s - 1 : ℝ) : ℂ) = 2 * (s : ℂ) - 1 := by
    push_cast
    ring
  have hsz : (s : ℂ) * oaaPhase s
      = -(1 - (s : ℂ)) + Complex.I * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ) := by
    rw [oaaPhase, mul_div_cancel₀ _ (by exact_mod_cast hs0)]
  have hmul : ((s : ℂ)) * ((s : ℂ) * (oaaPhase s) ^ 2
        + 2 * (1 - (s : ℂ)) * oaaPhase s + (s : ℂ)) = 0 := by
    have e1 : (s : ℂ) * (s : ℂ) * (oaaPhase s) ^ 2
        = ((s : ℂ) * oaaPhase s) ^ 2 := by ring
    have e2 : (s : ℂ) * (2 * (1 - (s : ℂ)) * oaaPhase s)
        = 2 * (1 - (s : ℂ)) * ((s : ℂ) * oaaPhase s) := by ring
    calc ((s : ℂ)) * ((s : ℂ) * (oaaPhase s) ^ 2
            + 2 * (1 - (s : ℂ)) * oaaPhase s + (s : ℂ))
        = ((s : ℂ) * (s : ℂ)) * (oaaPhase s) ^ 2
            + (s : ℂ) * (2 * (1 - (s : ℂ)) * oaaPhase s) + (s : ℂ) * (s : ℂ) := by
            ring
      _ = ((s : ℂ) * oaaPhase s) ^ 2
            + 2 * (1 - (s : ℂ)) * ((s : ℂ) * oaaPhase s) + (s : ℂ) * (s : ℂ) := by
            rw [e1, e2]
      _ = (-(1 - (s : ℂ)) + Complex.I * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ)) ^ 2
            + 2 * (1 - (s : ℂ)) * (-(1 - (s : ℂ))
              + Complex.I * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ))
            + (s : ℂ) * (s : ℂ) := by rw [hsz]
      _ = 0 := by
            linear_combination Complex.I_mul_I * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ)
              * ((Real.sqrt (2 * s - 1) : ℝ) : ℂ) - ht - hco
  exact (mul_eq_zero.mp hmul).resolve_left (by exact_mod_cast hs0)

/-- The scalar clean-subspace coefficient produced by two phase rounds using `oaaPhase s`. -/
noncomputable def oaaGamma (s : ℝ) : ℂ :=
  ((s : ℂ) + oaaPhase s * (1 - (s : ℂ))) ^ 2
    + (s : ℂ) * (1 - (s : ℂ)) * oaaPhase s * (1 - oaaPhase s) ^ 2

/-- For unitary `U` with squared `none` block `s • 1` and `s > 1 / 2`, two rounds with `oaaPhase
s` map the clean embedding to `oaaGamma s • cleanEmbed`. -/
theorem oaa_two_round_exact {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) {s : ℝ}
    (hs : 1 / 2 < s)
    (hA : (blockNone U)ᴴ * blockNone U = ((s : ℝ) : ℂ) • 1) :
    (phaseRound (oaaPhase s) U) ^ 2 * (cleanEmbed (D := D) (X := X))
      = oaaGamma s • (cleanEmbed (D := D) (X := X)) := by
  have hq := oaaPhase_quad (s := s) (by linarith : 1 / 2 ≤ s)
  have hQE := phaseRound_mul_cleanEmbed (oaaPhase s) U hU _ hA
  have hQL := phaseRound_mul_groverLeak (oaaPhase s) U hU _ hA
  have hαε : ((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
      + (oaaPhase s * (1 - (s : ℂ) + (s : ℂ) * oaaPhase s)) = 0 := by
    linear_combination hq
  have hL0 : (((s : ℂ) + oaaPhase s * (1 - (s : ℂ))) * (oaaPhase s * (1 - oaaPhase s))
      + (oaaPhase s * (1 - oaaPhase s))
        * (oaaPhase s * (1 - (s : ℂ) + (s : ℂ) * oaaPhase s))) = 0 := by
    linear_combination hαε * (oaaPhase s * (1 - oaaPhase s))
  have hpow2 : (phaseRound (oaaPhase s) U) ^ 2 * (cleanEmbed (D := D) (X := X))
      = (phaseRound (oaaPhase s) U)
          * ((((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
            • (cleanEmbed (D := D) (X := X))))
        + (phaseRound (oaaPhase s) U)
          * ((oaaPhase s * (1 - oaaPhase s)) • groverLeak U ((s : ℝ) : ℂ)) := by
    rw [pow_succ, Matrix.mul_assoc, hQE, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      pow_one, Matrix.mul_smul, Matrix.mul_smul]
  have hfinal : (((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
          * ((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
        + (oaaPhase s * (1 - oaaPhase s))
          * ((s : ℂ) * (1 - (s : ℂ)) * (1 - oaaPhase s)))
      = oaaGamma s := by
    rw [oaaGamma]
    ring
  rw [hpow2, Matrix.mul_smul, Matrix.mul_smul, hQE, hQL, smul_add, smul_add,
    smul_smul, smul_smul, smul_smul, smul_smul]
  have hreorder : ((((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
          * ((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))) • (cleanEmbed (D := D) (X := X))
        + (((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
            * (oaaPhase s * (1 - oaaPhase s))) • groverLeak U ((s : ℝ) : ℂ))
        + (((oaaPhase s * (1 - oaaPhase s))
            * ((s : ℂ) * (1 - (s : ℂ)) * (1 - oaaPhase s)))
            • (cleanEmbed (D := D) (X := X))
        + ((oaaPhase s * (1 - oaaPhase s))
            * (oaaPhase s * (1 - (s : ℂ) + (s : ℂ) * oaaPhase s)))
            • groverLeak U ((s : ℝ) : ℂ))
      = ((((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
              * ((s : ℂ) + oaaPhase s * (1 - (s : ℂ))))
            • (cleanEmbed (D := D) (X := X))
          + ((oaaPhase s * (1 - oaaPhase s))
              * ((s : ℂ) * (1 - (s : ℂ)) * (1 - oaaPhase s)))
              • (cleanEmbed (D := D) (X := X)))
        + ((((s : ℂ) + oaaPhase s * (1 - (s : ℂ)))
              * (oaaPhase s * (1 - oaaPhase s))) • groverLeak U ((s : ℝ) : ℂ)
          + ((oaaPhase s * (1 - oaaPhase s))
              * (oaaPhase s * (1 - (s : ℂ) + (s : ℂ) * oaaPhase s)))
              • groverLeak U ((s : ℝ) : ℂ)) := by
    module
  rw [hreorder, ← add_smul, ← add_smul, hL0, zero_smul, add_zero, hfinal]

/-- If a unitary on a nonempty data register has squared `none` block `s • 1` with `s > 1 / 2`,
then `oaaGamma s` has norm one. -/
theorem oaaGamma_norm {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) {s : ℝ}
    (hs : 1 / 2 < s)
    (hA : (blockNone U)ᴴ * blockNone U = ((s : ℝ) : ℂ) • 1) :
    ‖oaaGamma s‖ = 1 := by
  have hQ2 : (phaseRound (oaaPhase s) U) ^ 2
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    Submonoid.pow_mem _
      (phaseRound_unitary (oaaPhase_norm hs) U hU) 2
  have hUhU : ((phaseRound (oaaPhase s) U) ^ 2)ᴴ
      * (phaseRound (oaaPhase s) U) ^ 2 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hQ2
  have hkey : ((oaaGamma s) • (cleanEmbed (D := D) (X := X)))ᴴ
      * ((oaaGamma s) • (cleanEmbed (D := D) (X := X)))
      = (1 : Matrix X X ℂ) := by
    have hE : (oaaGamma s) • (cleanEmbed (D := D) (X := X))
        = (phaseRound (oaaPhase s) U) ^ 2 * (cleanEmbed (D := D) (X := X)) :=
      (oaa_two_round_exact U hU hs hA).symm
    have hassoc : (cleanEmbed (D := D) (X := X))ᴴ * ((phaseRound (oaaPhase s) U) ^ 2)ᴴ
          * ((phaseRound (oaaPhase s) U) ^ 2 * (cleanEmbed (D := D) (X := X)))
        = (cleanEmbed (D := D) (X := X))ᴴ
          * ((((phaseRound (oaaPhase s) U) ^ 2)ᴴ * (phaseRound (oaaPhase s) U) ^ 2)
            * (cleanEmbed (D := D) (X := X))) := by
      simp only [Matrix.mul_assoc]
    rw [hE, Matrix.conjTranspose_mul, hassoc, hUhU, Matrix.one_mul,
      cleanEmbed_conjTranspose_mul]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    cleanEmbed_conjTranspose_mul] at hkey
  obtain ⟨x0⟩ := ‹Nonempty X›
  have hentry : starRingEnd ℂ (oaaGamma s) * oaaGamma s = 1 := by
    have h2 := congrArg (fun M : Matrix X X ℂ => M x0 x0) hkey
    simpa using! h2
  have hp : ‖oaaGamma s‖ ^ 2 = 1 := by
    have hc : (Complex.normSq (oaaGamma s) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hentry
    have hreal : Complex.normSq (oaaGamma s) = 1 := by
      exact_mod_cast hc
    rw [← Complex.normSq_eq_norm_sq]
    exact hreal
  rcases sq_eq_one_iff.mp hp with h | h
  · exact h
  · linarith [norm_nonneg (oaaGamma s)]

/-- Applying `cleanEmbed` to a data state tensors it with the `none` control basis state. -/
private theorem cleanEmbed_mulVec_state {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (ψ : QState X) :
    (cleanEmbed (D := D) (X := X)) *ᵥ ψ
      = TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ := by
  funext p
  obtain ⟨b, y⟩ := p
  have hL : ((cleanEmbed (D := D) (X := X)) *ᵥ ψ) (b, y)
      = ∑ z : X, (if (b, y) = (none, z) then (1 : ℂ) else 0) * ψ z := by
    simp only [Matrix.mulVec, dotProduct, cleanEmbed]
  have hR : (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ) (b, y)
      = if b = none then ψ y else 0 := by
    simp [Qatlib.Foundations.PureStateMath.TensorState,
        Qatlib.Foundations.PureStateMath.Ket]
  rw [hL, hR]
  cases b with
  | none =>
      rw [Finset.sum_eq_single y]
      · simp
      · intro z _ hz
        have hne : (none (α := Fin D), y) ≠ (none, z) := by
          simp [Ne.symm hz]
        rw [if_neg hne]
        simp
      · intro h
        exact absurd (Finset.mem_univ y) h
  | some i =>
      rw [if_neg (by simp : ¬(some i : Option (Fin D)) = none)]
      exact Finset.sum_eq_zero fun z _ => by
        have hne : ((some i : Option (Fin D)), y) ≠ (none, z) := by simp
        rw [if_neg hne]
        simp

/-- For squared `none` block `s • 1` with `s > 1 / 2`, two exact phase rounds preserve a
clean-ancilla input up to the scalar `oaaGamma s`. -/
theorem oaa_two_round_state {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) {s : ℝ}
    (hs : 1 / 2 < s)
    (hA : (blockNone U)ᴴ * blockNone U = ((s : ℝ) : ℂ) • 1) (ψ : QState X) :
    (phaseRound (oaaPhase s) U) ^ 2 *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ
      = oaaGamma s • TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ := by
  rw [← cleanEmbed_mulVec_state ψ, Matrix.mulVec_mulVec,
    oaa_two_round_exact U hU hs hA, Matrix.smul_mulVec, cleanEmbed_mulVec_state]

/-- The circuit word for a phase-modified round using the linear-combination word and its
adjoint. -/
noncomputable def phaseWord {D : ℕ} {X : Type*} [DecidableEq X] (z : ℂ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    List (AdjointStep (Option (Fin D) × X)) :=
  reflectPhaseWord z ++ lcuBlockWordAdjoint k w amp S ++ reflectPhaseWord z
    ++ lcuBlockWord k w amp S

/-- The phase word evaluates to `phaseRound z` of the evaluated linear-combination word. -/
theorem phaseWord_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (phaseWord z k w amp S)
      = phaseRound z (evaluate 1 (lcuBlockWord k w amp S)) := by
  simp only [phaseWord, evaluate_append, reflectPhaseWord_eval,
    lcuBlockWordAdjoint_eval, lcuBlockWord_eval, phaseRound]

/-- The phase word uses `2 * (2 * (D + 1) + 1) + 2` gates and zero queries. -/
theorem phaseWord_counts {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    adjointGateCount (phaseWord z k w amp S) = 2 * (2 * (D + 1) + 1) + 2 ∧
      adjointQueryCount (phaseWord z k w amp S) = 0 := by
  obtain ⟨hgW, hqW⟩ := lcuBlockWord_counts k w amp S
  obtain ⟨hgI, hqI⟩ := lcuBlockWordAdjoint_counts k w amp S
  obtain ⟨hgR, hqR⟩ := reflectPhaseWord_counts (D := D) (X := X) z
  simp only [phaseWord, adjointGateCount_append, adjointQueryCount_append]
  omega

/-- The phase word is well formed for a unit-norm phase, nonnegative weights, and a unitary
selector. -/
theorem phaseWord_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] {z : ℂ}
    (hz : ‖z‖ = 1) (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (phaseWord z k w amp S) := by
  simp only [phaseWord, WellFormedAdjointCircuit.append_iff]
  exact ⟨⟨⟨reflectPhaseWord_wellFormed hz,
    lcuBlockWordAdjoint_wellFormed k w amp hw S hS⟩,
    reflectPhaseWord_wellFormed hz⟩,
    lcuBlockWord_wellFormed k w amp hw S hS⟩

/-- For a unit-norm phase and unitary selector, the approximate phase word has matrix error at
most `128 * (D + 1) / 2^k` relative to the exact preparation sandwich. -/
theorem phaseWord_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (phaseWord z k w amp S)
        - phaseRound z (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)‖
      ≤ 128 * (D + 1) / 2 ^ k := by
  have hR := reflectPhase_unitary (D := D) (X := X) hz
  have hdiff : ‖evaluate 1 (lcuBlockWord k w amp S)
        - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)‖
      ≤ 64 * (D + 1) / 2 ^ k := by
    have h1 := lcuBlock_error k w amp hw hm S hS
    rw [← lcuBlockWord_eval] at h1
    exact h1
  have hUau : evaluate 1 (lcuBlockWord k w amp S)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (lcuBlockWord_wellFormed k w amp hw S hS).evaluate_unitary (Submonoid.one_mem _)
  have hUeu : TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
      * TensorGate (exactPrepareMatrix w amp) 1
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    lcuSandwich_unitary w amp hw hm S hS
  rw [phaseWord_eval]
  have hdecomp :
      phaseRound z (evaluate 1 (lcuBlockWord k w amp S))
        - phaseRound z (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)
      = reflectPhase z
          * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)
          * (reflectPhase z * evaluate 1 (lcuBlockWord k w amp S))
        + reflectPhase z * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectPhase z
          * (evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)) := by
    rw [phaseRound, phaseRound]
    noncomm_ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖reflectPhase z
        * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
            - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)
        * (reflectPhase z * evaluate 1 (lcuBlockWord k w amp S))‖
      ≤ 64 * (D + 1) / 2 ^ k := by
    calc ‖reflectPhase z
          * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)
          * (reflectPhase z * evaluate 1 (lcuBlockWord k w amp S))‖
        ≤ ‖reflectPhase z
              * ((evaluate 1 (lcuBlockWord k w amp S))ᴴ
                  - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                      * TensorGate (exactPrepareMatrix w amp) 1)ᴴ)‖
            * ‖reflectPhase z * evaluate 1 (lcuBlockWord k w amp S)‖ :=
            Matrix.l2_opNorm_mul _ _
      _ = ‖(evaluate 1 (lcuBlockWord k w amp S))ᴴ
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)ᴴ‖
            * ‖reflectPhase z * evaluate 1 (lcuBlockWord k w amp S)‖ := by
          rw [unitary_mul_norm_eq _ hR _]
      _ = ‖evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)‖
            * ‖reflectPhase z * evaluate 1 (lcuBlockWord k w amp S)‖ := by
          rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      _ = ‖evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)‖ * 1 := by
          rw [unitary_mul_norm_eq _ hR _, l2_norm_unitary_eq_one hUau]
      _ ≤ 64 * (D + 1) / 2 ^ k := by rw [mul_one]; exact hdiff
  have h2 : ‖reflectPhase z * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
          * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectPhase z
        * (evaluate 1 (lcuBlockWord k w amp S)
            - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                * TensorGate (exactPrepareMatrix w amp) 1))‖
      ≤ 64 * (D + 1) / 2 ^ k := by
    have hReU : reflectPhase z * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
          * TensorGate (exactPrepareMatrix w amp) 1)ᴴ
        ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
      (Matrix.unitaryGroup (Option (Fin D) × X) ℂ).mul_mem hR
        (adjoint_unitary hUeu)
    calc ‖reflectPhase z * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectPhase z
          * (evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1))‖
        ≤ ‖reflectPhase z * (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
              * TensorGate (exactPrepareMatrix w amp) 1)ᴴ * reflectPhase z‖
            * ‖evaluate 1 (lcuBlockWord k w amp S)
                - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                    * TensorGate (exactPrepareMatrix w amp) 1)‖ :=
            Matrix.l2_opNorm_mul _ _
      _ = 1 * ‖evaluate 1 (lcuBlockWord k w amp S)
              - (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
                  * TensorGate (exactPrepareMatrix w amp) 1)‖ := by
          rw [unitary_mul_norm_eq _ hReU _, l2_norm_unitary_eq_one hR]
      _ ≤ 1 * (64 * (D + 1) / 2 ^ k) :=
          mul_le_mul_of_nonneg_left hdiff (by norm_num)
      _ ≤ 64 * (D + 1) / 2 ^ k := by norm_num
  have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ k : ℝ) + 64 * ((D : ℝ) + 1) / (2 ^ k : ℝ)
      = 128 * ((D : ℝ) + 1) / (2 ^ k : ℝ) := by
    rw [← add_div]
    congr 1
    ring
  linarith

/-- The concatenation of two copies of the phase word for oblivious amplitude amplification. -/
noncomputable def oaaWord {D : ℕ} {X : Type*} [DecidableEq X] (z : ℂ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    List (AdjointStep (Option (Fin D) × X)) :=
  phaseWord z k w amp S ++ phaseWord z k w amp S

/-- The two-round amplification word evaluates to the square of the phase-word evaluation. -/
theorem oaaWord_eval {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    evaluate 1 (oaaWord z k w amp S)
      = (evaluate 1 (phaseWord z k w amp S)) ^ 2 := by
  rw [oaaWord, evaluate_append, sq]

/-- The two-round amplification word uses `2 * (2 * (2 * (D + 1) + 1) + 2)` gates and zero
queries. -/
theorem oaaWord_counts {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (z : ℂ) (k : ℕ)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ) :
    adjointGateCount (oaaWord z k w amp S) = 2 * (2 * (2 * (D + 1) + 1) + 2) ∧
      adjointQueryCount (oaaWord z k w amp S) = 0 := by
  obtain ⟨hgW, hqW⟩ := phaseWord_counts z k w amp S
  simp only [oaaWord, adjointGateCount_append, adjointQueryCount_append]
  exact ⟨by rw [hgW]; ring, by rw [hqW]⟩

/-- The two-round amplification word is well formed for a unit-norm phase, nonnegative weights,
and a unitary selector. -/
theorem oaaWord_wellFormed {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] {z : ℂ}
    (hz : ‖z‖ = 1) (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    WellFormedAdjointCircuit (oaaWord z k w amp S) :=
  (phaseWord_wellFormed hz k w amp hw S hS).append (phaseWord_wellFormed hz k w amp hw S hS)

/-- The two-round amplification word differs from two exact phase rounds by at most `2 * (128 *
(D + 1) / 2^k)` in matrix norm. -/
theorem oaaWord_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (S : Matrix (Option (Fin D) × X) (Option (Fin D) × X) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ) :
    ‖evaluate 1 (oaaWord z k w amp S)
        - (phaseRound z (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
            * TensorGate (exactPrepareMatrix w amp) 1)) ^ 2‖
      ≤ 2 * (128 * (D + 1) / 2 ^ k) := by
  have hWU : evaluate 1 (phaseWord z k w amp S)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (phaseWord_wellFormed hz k w amp hw S hS).evaluate_unitary (Submonoid.one_mem _)
  have hQU : phaseRound z (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * S
        * TensorGate (exactPrepareMatrix w amp) 1)
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    phaseRound_unitary hz _ (lcuSandwich_unitary w amp hw hm S hS)
  have h1 := phaseWord_error hz k w amp hw hm S hS
  rw [oaaWord_eval]
  exact (unitary_pow_sub_pow_norm_le _ _ hWU hQU 2).trans
    (mul_le_mul_of_nonneg_left h1 (by norm_num))

/-- Under the scalar squared-block condition with `s > 1 / 2`, the two-round word approximates
the `oaaGamma s`-scaled clean input with error at most `2 * (128 * (D + 1) / 2^k)` times its
norm. -/
theorem oaaWord_state {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    {s : ℝ} (hs : 1 / 2 < s)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = ((s : ℝ) : ℂ) • 1)
    (ψ : QState X) :
    ‖stateVector (evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        - stateVector (oaaGamma s • TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
      ≤ 2 * (128 * (D + 1) / 2 ^ k) * ‖stateVector ψ‖ := by
  have hA' : (blockNone (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1))ᴴ
      * blockNone (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
          * TensorGate (exactPrepareMatrix w amp) 1)
      = ((s : ℝ) : ℂ) • 1 := by
    rw [lcuTopBlock_exact w amp hw hm U, hA]
  have hexact := oaa_two_round_state (TensorGate (exactPrepareMatrix w amp)ᴴ 1
    * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)
    (lcuSandwichExact_unitary w amp hw hm U hU) hs hA' ψ
  have hW := oaaWord_error (oaaPhase_norm hs) k w amp hw hm (blockSelect U)
    (blockSelect_unitary hU)
  have hsub : stateVector (evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U)) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      - stateVector (oaaGamma s • TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      = stateVector ((evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U))
            - (phaseRound (oaaPhase s) (TensorGate (exactPrepareMatrix w amp)ᴴ 1
                * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ 2) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ) := by
    simp [stateVector, WithLp.toLp_sub, Matrix.sub_mulVec, hexact]
  rw [hsub]
  have hv : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
      = ‖stateVector ψ‖ := by
    have hT : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
        = ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ * ‖stateVector ψ‖ :=
      tensorState_l2_norm _ _
    rw [hT, stateVector_ket_none_norm, one_mul]
  calc ‖stateVector ((evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U))
            - (phaseRound (oaaPhase s) (TensorGate (exactPrepareMatrix w amp)ᴴ 1
                * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ 2) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
      ≤ ‖evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U))
            - (phaseRound (oaaPhase s) (TensorGate (exactPrepareMatrix w amp)ᴴ 1
                * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ 2‖
          * ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ :=
        stateVector_mulVec_norm_le _ _
    _ = ‖evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U))
            - (phaseRound (oaaPhase s) (TensorGate (exactPrepareMatrix w amp)ᴴ 1
                * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ 2‖
          * ‖stateVector ψ‖ := by rw [hv]
    _ ≤ 2 * (128 * (D + 1) / 2 ^ k) * ‖stateVector ψ‖ :=
        mul_le_mul_of_nonneg_right hW (norm_nonneg _)

/-- For normalized input and scalar squared block `s • 1` with `s > 1 / 2`, the two-round word's
clean-branch probability differs from one by at most `2 * (2 * (128 * (D + 1) / 2^k))`. -/
theorem oaaWord_born {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    {s : ℝ} (hs : 1 / 2 < s)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = ((s : ℝ) : ℂ) • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    |MeasureProb (evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - 1|
      ≤ 2 * (2 * (128 * (D + 1) / 2 ^ k)) := by
  have hA' : (blockNone (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
        * TensorGate (exactPrepareMatrix w amp) 1))ᴴ
      * blockNone (TensorGate (exactPrepareMatrix w amp)ᴴ 1 * blockSelect U
          * TensorGate (exactPrepareMatrix w amp) 1)
      = ((s : ℝ) : ℂ) • 1 := by
    rw [lcuTopBlock_exact w amp hw hm U, hA]
  have hWU : evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U))
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (oaaWord_wellFormed (oaaPhase_norm hs) k w amp hw (blockSelect U)
      (blockSelect_unitary hU)).evaluate_unitary (Submonoid.one_mem _)
  have hEU : (phaseRound (oaaPhase s) (TensorGate (exactPrepareMatrix w amp)ᴴ 1
        * blockSelect U * TensorGate (exactPrepareMatrix w amp) 1)) ^ 2
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    Submonoid.pow_mem _
      (phaseRound_unitary (oaaPhase_norm hs) _
        (lcuSandwichExact_unitary w amp hw hm U hU)) 2
  have hφ : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    have hT : ‖stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖
        = ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ * ‖stateVector ψ‖ :=
      tensorState_l2_norm _ _
    rw [hT, stateVector_ket_none_norm, hψ, mul_one]
  have hv1 : ‖stateVector (evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U)) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    rw [unitary_mulVec_stateVector_norm _ hWU _]
    exact hφ
  have hG : ‖oaaGamma s‖ = 1 :=
    oaaGamma_norm _ (lcuSandwichExact_unitary w amp hw hm U hU) hs hA'
  have hu1 : ‖stateVector (oaaGamma s •
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)‖ = 1 := by
    have hsm : stateVector (oaaGamma s
          • TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        = oaaGamma s • stateVector (TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ) := by
      simp [stateVector, WithLp.toLp_smul]
    rw [hsm, norm_smul, hφ, hG, mul_one]
  have hstate := oaaWord_state k w amp hw hm U hU hs hA ψ
  rw [hψ, mul_one] at hstate
  have hd := born_deviation
    (evaluate 1 (oaaWord (oaaPhase s) k w amp (blockSelect U)) *ᵥ
      TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
    (oaaGamma s • TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
    (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none)) hv1 hu1 hstate
  have hPideal : MeasureProb (oaaGamma s •
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
      (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      = 1 := by
    rw [measureProb_none_branch]
    have hcb : cleanBranch (oaaGamma s •
        TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        = oaaGamma s • ψ := by
      funext x
      simp [cleanBranch]
    have hsm2 : stateVector (oaaGamma s • ψ) = oaaGamma s • stateVector ψ := by
      simp [stateVector, WithLp.toLp_smul]
    rw [hcb, hsm2, norm_smul, hψ, hG, mul_one]
    norm_num
  rwa [hPideal] at hd

/-- Under the two-round amplification hypotheses, precision `precisionFor D (ε / 16)` bounds the
clean-branch probability's deviation from one by `ε`. -/
theorem oaaWord_born_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (ε : ℚ) (hε : 0 < ε) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    {s : ℝ} (hs : 1 / 2 < s)
    (hA : (∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((w a / rationalWeightMass w : ℚ) : ℂ) • U a = ((s : ℝ) : ℂ) • 1)
    (ψ : QState X) (hψ : ‖stateVector ψ‖ = 1) :
    |MeasureProb (evaluate 1 (oaaWord (oaaPhase s)
          (precisionFor D (ε / 16)) w amp (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) ψ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - 1|
      ≤ (ε : ℝ) := by
  have h := oaaWord_born (precisionFor D (ε / 16)) w amp hw hm U hU hs hA ψ hψ
  have hb := prepError_le_epsilon (D := D) (ε / 16) (by positivity)
  have hcastE : ((ε / 16 : ℚ) : ℝ) = (ε : ℝ) / 16 := by
    push_cast
    ring
  rw [hcastE] at hb
  refine h.trans ?_
  have hsplit : 2 * (2 * (128 * ((D : ℝ) + 1)
        / (2 ^ precisionFor D (ε / 16) : ℝ)))
      = 16 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 16) : ℝ)) := by
    field_simp
    ring
  rw [hsplit]
  calc 16 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 16) : ℝ))
      ≤ 16 * ((ε : ℝ) / 16) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (ε : ℝ) := by ring

/-- The complex state obtained by converting each rational complex table entry with
`ratToComplex`. -/
def ratVec {D : ℕ} (zs : Option (Fin D) → RatComplex) :
    QState (Option (Fin D)) := fun a => ratToComplex (zs a)

/-- The sum of squared norms of the complex amplitudes, including the control index `none`. -/
noncomputable def cmplxMass {D : ℕ} (c : Option (Fin D) → ℂ) : ℝ := ∑ a, ‖c a‖ ^ 2

/-- The amplitude vector divided by the square root of its total squared-norm mass. -/
noncomputable def cmplxTarget {D : ℕ} (c : Option (Fin D) → ℂ) :
    QState (Option (Fin D)) :=
  fun a => c a / Real.sqrt (cmplxMass c : ℝ)

/-- The complex rational-table vector divided by the square root of its rational
squared-amplitude mass. -/
noncomputable def ratTarget {D : ℕ} (zs : Option (Fin D) → RatComplex) :
    QState (Option (Fin D)) :=
  fun a => ratToComplex (zs a)
    / Real.sqrt (rationalWeightMass (fun a => ratSq (zs a)) : ℝ)

/-- The sum of the operators `U a` weighted by the squared amplitude norms `‖ψ a‖²`. -/
noncomputable def stateCombination {D : ℕ} {X : Type*} (ψ : QState (Option (Fin D)))
    (U : Option (Fin D) → Matrix X X ℂ) : Matrix X X ℂ :=
  ∑ a, ((‖ψ a‖ ^ 2 : ℝ) : ℂ) • U a

/-- The squared complex norm of a rational complex value is its rational squared modulus coerced
to the reals. -/
private theorem ratToComplex_norm_sq (z : RatComplex) :
    ‖ratToComplex z‖ ^ 2 = (ratSq z : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [ratToComplex, ratSq, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  push_cast
  ring

/-- The squared Euclidean norm of `ratVec zs` equals the total rational squared-amplitude mass. -/
private theorem ratVec_norm_sq {D : ℕ} (zs : Option (Fin D) → RatComplex) :
    ‖stateVector (ratVec zs)‖ ^ 2
      = (rationalWeightMass (fun a => ratSq (zs a)) : ℝ) := by
  rw [stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb]
  have h : ∀ a : Option (Fin D), Qatlib.Foundations.PureStateMath.BornProb (ratVec zs) a
      = ((ratSq (zs a) : ℚ) : ℝ) := by
    intro a
    rw [Qatlib.Foundations.PureStateMath.BornProb, ratVec, ratToComplex_norm_sq]
  rw [Finset.sum_congr rfl fun a _ => h a, rationalWeightMass]
  exact (Rat.cast_sum _ _).symm

/-- The Euclidean norm of `ratVec zs` is the square root of its rational squared-amplitude mass. -/
private theorem ratVec_norm {D : ℕ} (zs : Option (Fin D) → RatComplex) :
    ‖stateVector (ratVec zs)‖
      = Real.sqrt (rationalWeightMass (fun a => ratSq (zs a)) : ℝ) :=
  (Real.sqrt_sq (norm_nonneg _)).symm.trans
    (congrArg Real.sqrt (ratVec_norm_sq zs))

/-- Each amplitude norm is bounded by the Euclidean norm of the whole state vector. -/
private theorem stateVector_entry_norm_le {D : ℕ} (u : QState (Option (Fin D)))
    (a : Option (Fin D)) : ‖u a‖ ≤ ‖stateVector u‖ := by
  have hsq : ‖u a‖ ^ 2 ≤ ‖stateVector u‖ ^ 2 := by
    rw [stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb]
    exact Finset.single_le_sum (fun b _ => sq_nonneg (‖u b‖)) (Finset.mem_univ a)
  calc ‖u a‖ = Real.sqrt (‖u a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖stateVector u‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖stateVector u‖ := Real.sqrt_sq (norm_nonneg _)

/-- A pointwise amplitude error at most `η` gives Euclidean error at most `sqrt (D + 1) * η`. -/
private theorem stateVector_sub_l2_le {D : ℕ} (u w : QState (Option (Fin D)))
    {η : ℝ} (hη : ∀ a, ‖u a - w a‖ ≤ η) :
    ‖stateVector u - stateVector w‖ ≤ Real.sqrt ((D + 1 : ℝ)) * η := by
  have hη0 : 0 ≤ η := le_trans (norm_nonneg _) (hη none)
  have hsub : ‖stateVector u - stateVector w‖ ^ 2 ≤ ((D + 1 : ℝ)) * η ^ 2 := by
    have heq : stateVector u - stateVector w
        = stateVector (fun a => u a - w a) := rfl
    rw [heq, stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb]
    have hle : ∀ a : Option (Fin D),
        Qatlib.Foundations.PureStateMath.BornProb (fun a => u a - w a) a ≤ η ^ 2 := by
      intro a
      rw [Qatlib.Foundations.PureStateMath.BornProb]
      nlinarith [hη a, norm_nonneg (u a - w a), hη0]
    calc ∑ a, Qatlib.Foundations.PureStateMath.BornProb (fun a => u a - w a) a
        ≤ ∑ _ : Option (Fin D), η ^ 2 := Finset.sum_le_sum fun a _ => hle a
      _ = ((D + 1 : ℝ)) * η ^ 2 := by
          simp [Finset.sum_const, Fintype.card_option, Fintype.card_fin]
  calc ‖stateVector u - stateVector w‖
      = Real.sqrt (‖stateVector u - stateVector w‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((D + 1 : ℝ)) * η ^ 2) := Real.sqrt_le_sqrt hsub
    _ = Real.sqrt ((D + 1 : ℝ)) * η := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (D + 1 : ℝ)),
          Real.sqrt_sq hη0]

/-- Every complex amplitude table vanishing at `none` has a rational complex approximation with
any positive pointwise tolerance that also vanishes at `none`. -/
theorem ratTable_exists {D : ℕ} (φ : Option (Fin D) → ℂ) (hφ0 : φ none = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ zs : Option (Fin D) → RatComplex, zs none = ratZero ∧
      ∀ a, ‖ratToComplex (zs a) - φ a‖ ≤ η := by
  have hex : ∀ a : Option (Fin D), ∃ p : RatComplex,
      (a = none → p = ratZero) ∧ ‖ratToComplex p - φ a‖ ≤ η := by
    intro a
    by_cases ha : a = none
    · refine ⟨ratZero, fun _ => rfl, ?_⟩
      rw [ha, hφ0]
      simpa [ratZero, ratToComplex] using! hη.le
    · obtain ⟨q1, h1⟩ := exists_rat_near (φ a).re (by linarith : 0 < η / 2)
      obtain ⟨q2, h2⟩ := exists_rat_near (φ a).im (by linarith : 0 < η / 2)
      refine ⟨(q1, q2), fun he => absurd he ha, ?_⟩
      have hnorm : ‖ratToComplex (q1, q2) - φ a‖ ^ 2
          = ((q1 : ℝ) - (φ a).re) ^ 2 + ((q2 : ℝ) - (φ a).im) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [ratToComplex, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, pow_two]
        ring
      have hle : ‖ratToComplex (q1, q2) - φ a‖ ^ 2 ≤ η ^ 2 := by
        rw [hnorm]
        have h1' : ((q1 : ℝ) - (φ a).re) ^ 2 < (η / 2) ^ 2 := by
          obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
          nlinarith [h1a, h1b, hη, sq_nonneg ((q1 : ℝ) - (φ a).re)]
        have h2' : ((q2 : ℝ) - (φ a).im) ^ 2 < (η / 2) ^ 2 := by
          obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
          nlinarith [h2a, h2b, hη, sq_nonneg ((q2 : ℝ) - (φ a).im)]
        nlinarith [h1', h2', hη]
      calc ‖ratToComplex (q1, q2) - φ a‖
          = Real.sqrt (‖ratToComplex (q1, q2) - φ a‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt hle
        _ = η := Real.sqrt_sq (le_of_lt hη)
  classical
  choose zs hzs0 hzs using hex
  exact ⟨zs, hzs0 none rfl, hzs⟩

/-- The state vector of `ratTarget zs` is the normalization of `ratVec zs`. -/
private theorem ratTarget_eq_normalize {D : ℕ} (zs : Option (Fin D) → RatComplex) :
    stateVector (ratTarget zs)
      = NormedSpace.normalize (stateVector (ratVec zs)) := by
  have hfun : PostMeasure (ratVec zs) Finset.univ = ratTarget zs := by
    rw [postMeasure_univ_eq_smul, ratVec_norm]
    funext a
    simp only [ratTarget, ratVec, Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv,
      div_eq_inv_mul]
  rw [← hfun, stateVector_postMeasure_univ]

/-- Normalizing a state vector of norm one leaves it unchanged. -/
private theorem normalize_self {D : ℕ} (ψ : QState (Option (Fin D)))
    (hψ : ‖stateVector ψ‖ = 1) :
    NormedSpace.normalize (stateVector ψ) = stateVector ψ := by
  rw [show NormedSpace.normalize (stateVector ψ)
      = ((‖stateVector ψ‖⁻¹ : ℝ) • stateVector ψ) from rfl, hψ, inv_one, one_smul]

/-- A rational table of positive squared-amplitude mass has normalized target of Euclidean norm
one. -/
theorem ratTarget_norm {D : ℕ} (zs : Option (Fin D) → RatComplex)
    (hm : 0 < rationalWeightMass (fun a => ratSq (zs a))) :
    ‖stateVector (ratTarget zs)‖ = 1 := by
  have hcast : (0 : ℝ) < (rationalWeightMass (fun a => ratSq (zs a)) : ℝ) := by
    exact_mod_cast hm
  have hne : stateVector (ratVec zs) ≠ 0 := by
    intro h0
    have hz : ‖stateVector (ratVec zs)‖ = 0 := by rw [h0, norm_zero]
    rw [ratVec_norm, Real.sqrt_eq_zero (by positivity)] at hz
    exact absurd hz (ne_of_gt hcast)
  rw [ratTarget_eq_normalize, NormedSpace.norm_normalize hne]

/-- A complex amplitude table of positive mass has normalized target of Euclidean norm one. -/
theorem cmplxTarget_norm {D : ℕ} (c : Option (Fin D) → ℂ) (hcm : 0 < cmplxMass c) :
    ‖stateVector (cmplxTarget c)‖ = 1 := by
  have hsq : ‖stateVector (cmplxTarget c)‖ ^ 2 = 1 := by
    rw [stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb]
    have h : ∀ a : Option (Fin D), Qatlib.Foundations.PureStateMath.BornProb (cmplxTarget c) a
        = ‖c a‖ ^ 2 / cmplxMass c := by
      intro a
      rw [Qatlib.Foundations.PureStateMath.BornProb, cmplxTarget]
      have hden : ‖(Real.sqrt (cmplxMass c : ℝ) : ℂ)‖ = Real.sqrt (cmplxMass c) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [Complex.norm_div, div_pow, hden, Real.sq_sqrt hcm.le]
    rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_div, ← cmplxMass]
    exact div_self (ne_of_gt hcm)
  have hn := norm_nonneg (stateVector (cmplxTarget c))
  nlinarith

/-- If a complex amplitude table vanishes at `none`, its normalized target also vanishes there. -/
theorem cmplxTarget_none {D : ℕ} (c : Option (Fin D) → ℂ) (hc0 : c none = 0) :
    (cmplxTarget c) none = 0 := by
  simp only [cmplxTarget, hc0, zero_div]

/-- For a unit target and pointwise error `η` with `sqrt (D + 1) * η < 1`, rational-table
normalization gives state error at most `2 * sqrt (D + 1) * η`. -/
theorem ratTarget_near {D : ℕ} (ψ : QState (Option (Fin D)))
    (hψ : ‖stateVector ψ‖ = 1) (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1) :
    ‖stateVector (ratTarget zs) - stateVector ψ‖
      ≤ 2 * Real.sqrt ((D + 1 : ℝ)) * η := by
  have ht : ‖stateVector (ratVec zs) - stateVector ψ‖
      ≤ Real.sqrt ((D + 1 : ℝ)) * η :=
    stateVector_sub_l2_le (ratVec zs) ψ (fun a => by simpa only [ratVec] using! hη a)
  obtain ⟨_, hb⟩ := normalize_error_of_gap
    (x := stateVector ψ) (y := stateVector (ratVec zs))
    (η := Real.sqrt ((D + 1 : ℝ)) * η)
    ht (by rw [hψ]; exact hgap)
  rw [hψ, div_one, normalize_self ψ hψ] at hb
  rw [ratTarget_eq_normalize zs]
  exact hb.trans_eq (by ring)

/-- When `zs none = ratZero`, loading its remaining entries gives weights equal to the squared
moduli of `zs`. -/
private theorem ratZs_loadedWeights {D : ℕ} (zs : Option (Fin D) → RatComplex)
    (hz0 : zs none = ratZero) :
    (LoadedInput.mk (fun i => zs (some i)) 0 0).weights = fun a => ratSq (zs a) := by
  funext a
  cases a with
  | none => simp [LoadedInput.weights, hz0, ratSq, ratZero]
  | some i => rfl

/-- When `zs none = ratZero`, loading the table's finite entries reconstructs the full amplitude
table `zs`. -/
private theorem ratZs_loadedAmp {D : ℕ} (zs : Option (Fin D) → RatComplex)
    (hz0 : zs none = ratZero) :
    (LoadedInput.mk (fun i => zs (some i)) 0 0).amp = zs := by
  funext a
  cases a with
  | none => simp [LoadedInput.amp, hz0]
  | some i => rfl

/-- When `zs none = ratZero`, the loaded target agrees with `ratTarget zs`. -/
private theorem ratZs_loadedTarget {D : ℕ} (zs : Option (Fin D) → RatComplex)
    (hz0 : zs none = ratZero) :
    loadedTarget (LoadedInput.mk (fun i => zs (some i)) 0 0) = ratTarget zs := by
  have hmass : (LoadedInput.mk (fun i => zs (some i)) 0 0).mass
      = rationalWeightMass (fun a => ratSq (zs a)) := by
    rw [← LoadedInput.mass_eq, ratZs_loadedWeights zs hz0]
  funext a
  cases a with
  | none => simp [loadedTarget, ratTarget, hz0, ratZero, ratToComplex]
  | some i => simp only [loadedTarget, ratTarget, hmass]

/-- For a unit target approximated pointwise within `η` by a rational table vanishing at `none`,
with `sqrt (D + 1) * η < 1`, preparation error is at most `32 * (D + 1) / 2^k + 2 * sqrt (D
+ 1) * η`. -/
theorem generalPrepare_state_error {D : ℕ} (k : ℕ) (ψ : QState (Option (Fin D)))
    (hψ : ‖stateVector ψ‖ = 1) (zs : Option (Fin D) → RatComplex)
    (hz0 : zs none = ratZero) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1) :
    ‖stateVector (prepareMatrix k (fun a => ratSq (zs a)) zs *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector ψ‖
      ≤ 32 * (D + 1) / 2 ^ k + 2 * Real.sqrt ((D + 1 : ℝ)) * η := by
  have ht : ‖stateVector (ratVec zs) - stateVector ψ‖
      ≤ Real.sqrt ((D + 1 : ℝ)) * η :=
    stateVector_sub_l2_le (ratVec zs) ψ (fun a => by simpa only [ratVec] using! hη a)
  have hrev : 1 - Real.sqrt ((D + 1 : ℝ)) * η ≤ ‖stateVector (ratVec zs)‖ := by
    have habs := abs_norm_sub_norm_le (stateVector (ratVec zs)) (stateVector ψ)
    rw [hψ] at habs
    obtain ⟨_, h2⟩ := abs_le.mp habs
    linarith
  have hpos : 0 < rationalWeightMass (fun a => ratSq (zs a)) := by
    have hnormpos : (0 : ℝ) < ‖stateVector (ratVec zs)‖ := by linarith
    have hsq := ratVec_norm_sq zs
    have hcast : (0 : ℝ) < ((rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) := by
      rw [← hsq]; positivity
    exact_mod_cast hcast
  have hw : ∀ a, 0 ≤ (fun a => ratSq (zs a)) a := fun a => ratSq_nonneg (zs a)
  have hLmass : 0 < (LoadedInput.mk (fun i => zs (some i)) 0 0).mass := by
    rw [← LoadedInput.mass_eq, ratZs_loadedWeights zs hz0]
    exact hpos
  have hword := prepareMatrix_state_error k (LoadedInput.mk (fun i => zs (some i)) 0 0)
    hLmass
  rw [ratZs_loadedWeights zs hz0, ratZs_loadedAmp zs hz0, ratZs_loadedTarget zs hz0] at hword
  have hnear := ratTarget_near ψ hψ zs hη hgap
  rw [show stateVector (prepareMatrix k (fun a => ratSq (zs a)) zs *ᵥ Qatlib.Foundations.PureStateMath.Ket none) - stateVector ψ
      = (stateVector (prepareMatrix k (fun a => ratSq (zs a)) zs *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (ratTarget zs))
        + (stateVector (ratTarget zs) - stateVector ψ) from by abel]
  exact (norm_add_le _ _).trans (by linarith [hword, hnear])

/-- For `0 < ε ≤ 1`, pointwise error at most `ε / (8 * sqrt (D + 1))` and precision
`precisionFor D (ε / 2)` give preparation error at most `ε`. -/
theorem generalPrepare_state_error_epsilon {D : ℕ} (ε : ℚ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) (hz0 : zs none = ratZero)
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖
      ≤ (ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ)))) :
    ‖stateVector (prepareMatrix (precisionFor D (ε / 2))
          (fun a => ratSq (zs a)) zs *ᵥ Qatlib.Foundations.PureStateMath.Ket none) - stateVector ψ‖ ≤ (ε : ℝ) := by
  have hs : 0 < Real.sqrt ((D + 1 : ℝ)) := by positivity
  have hgap : Real.sqrt ((D + 1 : ℝ))
      * ((ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ)))) < 1 := by
    have hcalc : Real.sqrt ((D + 1 : ℝ))
        * ((ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ)))) = (ε : ℝ) / 8 := by
      field_simp
    rw [hcalc]
    have hεr := (by exact_mod_cast hε1 : (ε : ℝ) ≤ 1)
    linarith
  have h := generalPrepare_state_error (precisionFor D (ε / 2)) ψ hψ zs hz0 hη hgap
  have hb := prepError_le_epsilon (D := D) (ε / 2) (by linarith : 0 < ε / 2)
  have hterm : 2 * Real.sqrt ((D + 1 : ℝ))
      * ((ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ)))) ≤ (ε : ℝ) / 4 := by
    have hcalc : 2 * Real.sqrt ((D + 1 : ℝ))
        * ((ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ)))) = (ε : ℝ) / 4 := by
      field_simp
      norm_num
    rw [hcalc]
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hbcast : ((ε / 2 : ℚ) : ℝ) = (ε : ℝ) / 2 := by
    push_cast
    ring
  linarith

/-- Every normalized state vanishing at `none` can be approximated to any positive Euclidean
tolerance by preparing a suitable rational complex table. -/
theorem generalPrepare_exists {D : ℕ} (ψ : QState (Option (Fin D)))
    (hψ : ‖stateVector ψ‖ = 1) (hψ0 : ψ none = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      ‖stateVector (prepareMatrix k (fun a => ratSq (zs a)) zs *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector ψ‖ ≤ ε := by
  obtain ⟨ℓ, hℓ0, hℓlt⟩ := exists_pos_rat_lt (x := ε / 2) (by linarith)
  have hs : 0 < Real.sqrt ((D + 1 : ℝ)) := by positivity
  have hmin : 0 < min (ε / (8 * Real.sqrt ((D + 1 : ℝ))))
      (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) :=
    lt_min (div_pos hε (by positivity)) (div_pos one_pos (by positivity))
  obtain ⟨zs, hz0, hz⟩ := ratTable_exists ψ hψ0 hmin
  refine ⟨zs, precisionFor D ℓ, hz0, ?_⟩
  have hgap : Real.sqrt ((D + 1 : ℝ))
      * (min (ε / (8 * Real.sqrt ((D + 1 : ℝ))))
          (1 / (8 * Real.sqrt ((D + 1 : ℝ))))) < 1 := by
    have hle : Real.sqrt ((D + 1 : ℝ))
        * (min (ε / (8 * Real.sqrt ((D + 1 : ℝ))))
            (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ Real.sqrt ((D + 1 : ℝ)) * (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hs)
    have hcalc : Real.sqrt ((D + 1 : ℝ))
        * (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) = 1 / 8 := by
      field_simp
    rw [hcalc] at hle
    linarith
  have hword := generalPrepare_state_error (precisionFor D ℓ) ψ hψ zs hz0 hz hgap
  have hb : (32 * (D + 1) : ℝ) / 2 ^ precisionFor D ℓ ≤ (ℓ : ℝ) :=
    prepError_le_epsilon ℓ hℓ0
  have hterm : 2 * Real.sqrt ((D + 1 : ℝ))
      * (min (ε / (8 * Real.sqrt ((D + 1 : ℝ))))
          (1 / (8 * Real.sqrt ((D + 1 : ℝ))))) ≤ ε / 4 := by
    have hle : 2 * Real.sqrt ((D + 1 : ℝ))
        * (min (ε / (8 * Real.sqrt ((D + 1 : ℝ))))
            (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ 2 * Real.sqrt ((D + 1 : ℝ)) * (ε / (8 * Real.sqrt ((D + 1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _)
        (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt ((D + 1 : ℝ)))
    have hcalc : 2 * Real.sqrt ((D + 1 : ℝ))
        * (ε / (8 * Real.sqrt ((D + 1 : ℝ)))) = ε / 4 := by
      field_simp
      norm_num
    rw [hcalc] at hle
    exact hle
  linarith

/-- The difference of squared complex norms is bounded by the sum of the norms times the norm of
the difference. -/
private theorem norm_sq_sub_abs_le (x y : ℂ) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  rw [sq_sub_sq, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The sum of amplitude norms is at most `sqrt (D + 1)` times the state's Euclidean norm. -/
private theorem sum_norm_le {D : ℕ} (u : QState (Option (Fin D))) :
    ∑ a, ‖u a‖ ≤ Real.sqrt ((D + 1 : ℝ)) * ‖stateVector u‖ := by
  have hone : (∑ _ : Option (Fin D), ((1 : ℝ) ^ 2)) = ((D + 1 : ℝ)) := by
    simp [Finset.sum_const, Fintype.card_option, Fintype.card_fin]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset _))
    (f := fun a => ‖u a‖) (g := fun _ => (1 : ℝ))
  simp only [mul_one] at hcs
  rw [hone] at hcs
  have hnormsq : ∑ a, ‖u a‖ ^ 2 = ‖stateVector u‖ ^ 2 := by
    rw [stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb]
    exact Finset.sum_congr rfl fun a _ => rfl
  rw [hnormsq] at hcs
  have ha : (0 : ℝ) ≤ ∑ a, ‖u a‖ :=
    Finset.sum_nonneg fun a _ => norm_nonneg (u a)
  have hb : (0 : ℝ) ≤ Real.sqrt ((D + 1 : ℝ)) * ‖stateVector u‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  calc ∑ a, ‖u a‖ = Real.sqrt ((∑ a, ‖u a‖) ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt ((Real.sqrt ((D + 1 : ℝ)) * ‖stateVector u‖) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ (D + 1 : ℝ) by positivity)]
        exact hcs.trans_eq (by ring)
    _ = Real.sqrt ((D + 1 : ℝ)) * ‖stateVector u‖ :=
        Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-- Applying a finite weighted sum of matrices to a vector equals the corresponding weighted sum
of matrix-vector products. -/
private theorem sum_smul_mulVec {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (g : Option (Fin D) → ℂ) (U : Option (Fin D) → Matrix X X ℂ) (v : QState X) :
    (∑ a, g a • U a) *ᵥ v = ∑ a, g a • (U a *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_apply, Finset.mul_sum, mul_assoc, Finset.sum_mul,
    Pi.smul_apply]
  rw [Finset.sum_comm]

/-- A linear combination of unitaries has matrix norm at most the sum of the norms of its
coefficients. -/
private theorem combination_norm_le {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (g : Option (Fin D) → ℂ) (U : Option (Fin D) → Matrix X X ℂ)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖∑ a, g a • U a‖ ≤ ∑ a, ‖g a‖ := by
  refine l2_opNorm_le_of_mulVec_le (Finset.sum_nonneg fun a _ => norm_nonneg _) _ fun v => ?_
  show ‖stateVector ((∑ a, g a • U a) *ᵥ v)‖
      ≤ (∑ a, ‖g a‖) * ‖stateVector v‖
  rw [sum_smul_mulVec g U v]
  have hsum : ‖stateVector (∑ a, g a • (U a *ᵥ v))‖
      ≤ ∑ a, ‖stateVector (g a • (U a *ᵥ v))‖ := by
    rw [show stateVector (∑ a, g a • (U a *ᵥ v))
          = ∑ a, stateVector (g a • (U a *ᵥ v)) from by
        simp only [stateVector, WithLp.toLp_sum]]
    exact norm_sum_le _ _
  refine hsum.trans ?_
  calc ∑ a, ‖stateVector (g a • (U a *ᵥ v))‖
      = ∑ a, ‖g a‖ * ‖stateVector (U a *ᵥ v)‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [show stateVector (g a • (U a *ᵥ v))
              = g a • stateVector (U a *ᵥ v) from by
            simp only [stateVector, WithLp.toLp_smul], norm_smul]
    _ ≤ ∑ a, ‖g a‖ * ‖stateVector v‖ := by
        refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 : ‖stateVector (U a *ᵥ v)‖ ≤ ‖U a‖ * ‖stateVector v‖ :=
          stateVector_mulVec_norm_le (U a) v
        rw [l2_norm_unitary_eq_one (hU a), one_mul] at h1
        exact h1
    _ = (∑ a, ‖g a‖) * ‖stateVector v‖ := (Finset.sum_mul _ _ _).symm

/-- Each squared amplitude norm of a positive-mass rational target equals its squared modulus
divided by the total rational mass. -/
private theorem ratTarget_entry_norm_sq {D : ℕ} (zs : Option (Fin D) → RatComplex)
    (hm : 0 < rationalWeightMass (fun a => ratSq (zs a))) (a : Option (Fin D)) :
    (‖ratTarget zs a‖ ^ 2 : ℝ)
      = ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) := by
  have hden : ‖(Real.sqrt (rationalWeightMass (fun a => ratSq (zs a)) : ℝ) : ℂ)‖ ^ 2
      = (rationalWeightMass (fun a => ratSq (zs a)) : ℝ) := by
    have hmR : (0 : ℝ) ≤ (rationalWeightMass (fun a => ratSq (zs a)) : ℝ) := by
      exact_mod_cast hm.le
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hmR]
  have hentry : ‖ratTarget zs a‖ ^ 2
      = ‖ratToComplex (zs a)‖ ^ 2
        / (rationalWeightMass (fun a => ratSq (zs a)) : ℝ) := by
    rw [ratTarget, Complex.norm_div, div_pow, hden]
  rw [hentry, ratToComplex_norm_sq]
  push_cast [Rat.cast_div]
  ring

/-- For rational amplitudes approximating a unit target pointwise within `η` and satisfying the
normalization gap, the linear-combination block error is at most `64 * (D + 1) / 2^k + 4 *
(D + 1) * η`. -/
theorem cmplxLcuWord_topBlock_error {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)))
        - stateCombination ψ U‖
      ≤ 64 * (D + 1) / 2 ^ k + 4 * ((D + 1 : ℝ)) * η := by
  have ht : ‖stateVector (ratVec zs) - stateVector ψ‖
      ≤ Real.sqrt ((D + 1 : ℝ)) * η :=
    stateVector_sub_l2_le (ratVec zs) ψ (fun a => by simpa only [ratVec] using! hη a)
  have hrev : 1 - Real.sqrt ((D + 1 : ℝ)) * η ≤ ‖stateVector (ratVec zs)‖ := by
    have habs := abs_norm_sub_norm_le (stateVector (ratVec zs)) (stateVector ψ)
    rw [hψ] at habs
    obtain ⟨_, h2⟩ := abs_le.mp habs
    linarith
  have hpos : 0 < rationalWeightMass (fun a => ratSq (zs a)) := by
    have hnormpos : (0 : ℝ) < ‖stateVector (ratVec zs)‖ := by linarith
    have hsq := ratVec_norm_sq zs
    have hcast : (0 : ℝ) < ((rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) := by
      rw [← hsq]; positivity
    exact_mod_cast hcast
  have hw : ∀ a, 0 ≤ (fun a => ratSq (zs a)) a := fun a => ratSq_nonneg (zs a)
  have hword := lcuWord_topBlock_error k (fun a => ratSq (zs a)) zs hw hpos U hU
  have hnear := ratTarget_near ψ hψ zs hη hgap
  have hmassroot : ‖stateVector (ratTarget zs)‖ = 1 := ratTarget_norm zs hpos
  have hentry : ∀ a : Option (Fin D),
      |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        - (‖ψ a‖ ^ 2 : ℝ)| ≤ 2 * ‖ratTarget zs a - ψ a‖ := by
    intro a
    have hcoeffz : ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        = ‖ratTarget zs a‖ ^ 2 := (ratTarget_entry_norm_sq zs hpos a).symm
    rw [hcoeffz]
    have hle := norm_sq_sub_abs_le (ratTarget zs a) (ψ a)
    have hb1 : ‖ratTarget zs a‖ ≤ 1 := by
      have hb := stateVector_entry_norm_le (ratTarget zs) a
      rwa [hmassroot] at hb
    have hb2 : ‖ψ a‖ ≤ 1 := by
      have hb := stateVector_entry_norm_le ψ a
      rwa [hψ] at hb
    have hbound : (‖ratTarget zs a‖ + ‖ψ a‖) * ‖ratTarget zs a - ψ a‖
        ≤ 2 * ‖ratTarget zs a - ψ a‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    exact hle.trans hbound
  have hsum : ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        - (‖ψ a‖ ^ 2 : ℝ)| ≤ 4 * ((D + 1 : ℝ)) * η := by
    have h1 : ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
          - (‖ψ a‖ ^ 2 : ℝ)|
        ≤ ∑ a, 2 * ‖ratTarget zs a - ψ a‖ :=
      Finset.sum_le_sum fun a _ => hentry a
    have h2 : ∑ a, 2 * ‖ratTarget zs a - ψ a‖
        ≤ 2 * (Real.sqrt ((D + 1 : ℝ))
            * ‖stateVector (fun a => ratTarget zs a - ψ a)‖) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_norm_le (fun a => ratTarget zs a - ψ a))
        (by norm_num)
    have h3 : ‖stateVector (fun a => ratTarget zs a - ψ a)‖
        ≤ 2 * Real.sqrt ((D + 1 : ℝ)) * η := by
      rw [show stateVector (fun a => ratTarget zs a - ψ a)
          = stateVector (ratTarget zs) - stateVector ψ from rfl]
      exact hnear
    have hcalc : 2 * (Real.sqrt ((D + 1 : ℝ)) * (2 * Real.sqrt ((D + 1 : ℝ)) * η))
        = 4 * ((D + 1 : ℝ)) * η := by
      have hsq : Real.sqrt ((D + 1 : ℝ)) * Real.sqrt ((D + 1 : ℝ)) = (D + 1 : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hexp : 2 * (Real.sqrt ((D + 1 : ℝ)) * (2 * Real.sqrt ((D + 1 : ℝ)) * η))
          = 4 * (Real.sqrt ((D + 1 : ℝ)) * Real.sqrt ((D + 1 : ℝ))) * η := by ring
      rw [hexp, hsq]
    calc ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
          - (‖ψ a‖ ^ 2 : ℝ)|
        ≤ ∑ a, 2 * ‖ratTarget zs a - ψ a‖ := h1
      _ ≤ 2 * (Real.sqrt ((D + 1 : ℝ))
          * ‖stateVector (fun a => ratTarget zs a - ψ a)‖) := h2
      _ ≤ 2 * (Real.sqrt ((D + 1 : ℝ)) * (2 * Real.sqrt ((D + 1 : ℝ)) * η)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h3 (by positivity)) (by norm_num)
      _ = 4 * ((D + 1 : ℝ)) * η := hcalc
  have hsplit : blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs
          (blockSelect U))) - stateCombination ψ U
      = (blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs
            (blockSelect U)))
          - ∑ a, (((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ)) • U a)
        + (∑ a, (((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ)) • U a
          - stateCombination ψ U) := by
    abel
  have hcsum : (∑ a, (((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ)) • U a)
        - stateCombination ψ U
      = ∑ a, ((((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) : ℂ)
            - ((‖ψ a‖ ^ 2 : ℝ) : ℂ)) • U a := by
    rw [stateCombination, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (sub_smul _ _ _).symm
  have hdiff : ‖∑ a, ((((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) : ℂ)
            - ((‖ψ a‖ ^ 2 : ℝ) : ℂ)) • U a‖
      ≤ ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        - (‖ψ a‖ ^ 2 : ℝ)| := by
    refine (combination_norm_le _ U hU).trans ?_
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hsecond : ‖(∑ a, (((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ)) • U a)
        - stateCombination ψ U‖ ≤ 4 * ((D + 1 : ℝ)) * η := by
    rw [hcsum]
    exact hdiff.trans hsum
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hword hsecond)

/-- For `0 < ε ≤ 1`, pointwise error at most `ε / (32 * (D + 1))` and precision `precisionFor D
(ε / 4)` give linear-combination block error at most `ε`. -/
theorem cmplxLcuWord_topBlock_error_epsilon {D : ℕ} {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex)
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖
      ≤ (ε : ℝ) / (32 * ((D + 1 : ℝ))))
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖blockNone (evaluate 1 (lcuBlockWord (precisionFor D (ε / 4))
          (fun a => ratSq (zs a)) zs (blockSelect U)))
        - stateCombination ψ U‖ ≤ (ε : ℝ) := by
  have hs : 0 < Real.sqrt ((D + 1 : ℝ)) := by positivity
  have hD1 : (1 : ℝ) ≤ ((D + 1 : ℝ)) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le D))
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((D + 1 : ℝ)) := by
    nlinarith [hs, Real.mul_self_sqrt (show (0 : ℝ) ≤ (D + 1 : ℝ) by positivity), hD1]
  have hgap : Real.sqrt ((D + 1 : ℝ))
      * ((ε : ℝ) / (32 * ((D + 1 : ℝ)))) < 1 := by
    have hcalc : Real.sqrt ((D + 1 : ℝ)) * ((ε : ℝ) / (32 * ((D + 1 : ℝ))))
        = (ε : ℝ) / (32 * Real.sqrt ((D + 1 : ℝ))) := by
      field_simp
      exact Real.sq_sqrt (by positivity)
    rw [hcalc]
    have hεr := (by exact_mod_cast hε1 : (ε : ℝ) ≤ 1)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 32 * Real.sqrt ((D + 1 : ℝ)))]
    linarith
  have h := cmplxLcuWord_topBlock_error (precisionFor D (ε / 4)) ψ hψ zs hη hgap U hU
  have hb := prepError_le_epsilon (D := D) (ε / 4) (by linarith : 0 < ε / 4)
  have hbcast : ((ε / 4 : ℚ) : ℝ) = (ε : ℝ) / 4 := by
    push_cast
    ring
  have hwordterm : 64 * ((D + 1 : ℝ)) / 2 ^ precisionFor D (ε / 4)
      ≤ (ε : ℝ) / 2 := by
    have heq : 64 * ((D + 1 : ℝ)) / 2 ^ precisionFor D (ε / 4)
        = 2 * (32 * ((D + 1 : ℝ)) / 2 ^ precisionFor D (ε / 4)) := by ring
    rw [heq]
    linarith
  have hterm : 4 * ((D + 1 : ℝ)) * ((ε : ℝ) / (32 * ((D + 1 : ℝ)))) ≤ (ε : ℝ) / 8 := by
    have hcalc : 4 * ((D + 1 : ℝ)) * ((ε : ℝ) / (32 * ((D + 1 : ℝ))))
        = (ε : ℝ) / 8 := by
      field_simp
      norm_num
    rw [hcalc]
  have hεr0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  linarith

/-- For a normalized control state vanishing at `none` and unitary selected operators, suitable
rational amplitudes and precision approximate `stateCombination ψ U` to any positive
matrix-norm tolerance. -/
theorem cmplxLcu_exists {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1) (hψ0 : ψ none = 0)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      ‖blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)))
          - stateCombination ψ U‖ ≤ ε := by
  obtain ⟨ℓ, hℓ0, hℓlt⟩ := exists_pos_rat_lt (x := ε / 4) (by linarith)
  have hs : 0 < Real.sqrt ((D + 1 : ℝ)) := by positivity
  have hmin : 0 < min (ε / (64 * ((D + 1 : ℝ))))
      (1 / (4 * Real.sqrt ((D + 1 : ℝ)))) := by
    positivity
  obtain ⟨zs, hz0, hz⟩ := ratTable_exists ψ hψ0 hmin
  refine ⟨zs, precisionFor D ℓ, hz0, ?_⟩
  have hgap : Real.sqrt ((D + 1 : ℝ))
      * (min (ε / (64 * ((D + 1 : ℝ)))) (1 / (4 * Real.sqrt ((D + 1 : ℝ))))) < 1 := by
    have hle : Real.sqrt ((D + 1 : ℝ))
        * (min (ε / (64 * ((D + 1 : ℝ)))) (1 / (4 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ Real.sqrt ((D + 1 : ℝ)) * (1 / (4 * Real.sqrt ((D + 1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hs)
    have hcalc : Real.sqrt ((D + 1 : ℝ))
        * (1 / (4 * Real.sqrt ((D + 1 : ℝ)))) = 1 / 4 := by
      field_simp
    rw [hcalc] at hle
    linarith
  have hword := cmplxLcuWord_topBlock_error (precisionFor D ℓ) ψ hψ zs hz hgap U hU
  have hb : (32 * (D + 1) : ℝ) / 2 ^ precisionFor D ℓ ≤ (ℓ : ℝ) :=
    prepError_le_epsilon ℓ hℓ0
  have hwordterm : 64 * ((D + 1 : ℝ)) / 2 ^ precisionFor D ℓ
      ≤ 2 * ((ℓ : ℝ)) := by
    have heq : 64 * ((D + 1 : ℝ)) / 2 ^ precisionFor D ℓ
        = 2 * (32 * ((D + 1 : ℝ)) / 2 ^ precisionFor D ℓ) := by ring
    rw [heq]
    linarith
  have hterm : 4 * ((D + 1 : ℝ))
      * (min (ε / (64 * ((D + 1 : ℝ)))) (1 / (4 * Real.sqrt ((D + 1 : ℝ)))))
      ≤ ε / 16 := by
    have hle : 4 * ((D + 1 : ℝ))
        * (min (ε / (64 * ((D + 1 : ℝ)))) (1 / (4 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ 4 * ((D + 1 : ℝ)) * (ε / (64 * ((D + 1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _)
        (by positivity : (0 : ℝ) ≤ 4 * ((D + 1 : ℝ)))
    have hcalc : 4 * ((D + 1 : ℝ)) * (ε / (64 * ((D + 1 : ℝ)))) = ε / 16 := by
      field_simp
      norm_num
    rw [hcalc] at hle
    exact hle
  linarith

/-- The amplitude function of a finite list of indexed complex entries, summing repeated indices
and assigning zero to `none`. -/
def sparseAmp {D : ℕ} : List (Fin D × ℂ) → Option (Fin D) → ℂ
  | [], _ => 0
  | e :: L, a => (if a = some e.1 then e.2 else 0) + sparseAmp L a

/-- The sparse amplitude function vanishes at `none`. -/
theorem sparseAmp_none {D : ℕ} : ∀ (L : List (Fin D × ℂ)),
    sparseAmp L none = 0 := by
  intro L
  induction L with
  | nil => simp [sparseAmp]
  | cons e L ih => simp [sparseAmp, ih]

/-- Two entries at the same sparse index contribute the sum of their amplitudes. -/
theorem sparseAmp_dup {D : ℕ} (p : Fin D) (v w : ℂ) :
    sparseAmp [(p, v), (p, w)] (some p) = v + w := by
  simp [sparseAmp]

/-- Adding a sparse entry adds its amplitude at its index and zero at other indices. -/
theorem sparseAmp_cons {D : ℕ} (e : Fin D × ℂ) (L : List (Fin D × ℂ))
    (a : Option (Fin D)) :
    sparseAmp (e :: L) a = (if a = some e.1 then e.2 else 0) + sparseAmp L a := by
  simp [sparseAmp]

/-- The sparse amplitude at an index absent from the list of indices is zero. -/
theorem sparseAmp_eq_zero {D : ℕ} {p : Fin D} : ∀ L : List (Fin D × ℂ),
    p ∉ L.map Prod.fst → sparseAmp L (some p) = 0 := by
  intro L
  induction L with
  | nil => simp [sparseAmp]
  | cons e L ih =>
    intro hp
    have hne : p ≠ e.1 := by
      intro h
      apply hp
      rw [List.map_cons, List.mem_cons]
      exact Or.inl h
    have htail : p ∉ L.map Prod.fst := by
      intro hmem
      apply hp
      rw [List.map_cons, List.mem_cons]
      exact Or.inr hmem
    simp [sparseAmp, hne, ih htail]

/-- If the list of sparse indices has no duplicates, a listed entry gives the amplitude at that
index. -/
theorem sparseAmp_mem {D : ℕ} {p : Fin D} {v : ℂ} :
    ∀ (L : List (Fin D × ℂ)), (L.map Prod.fst).Nodup → (p, v) ∈ L →
      sparseAmp L (some p) = v := by
  intro L
  induction L with
  | nil => intro _ hmem; simp at hmem
  | cons e L ih =>
    intro hnd hmem
    obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hmem with hmem' | hmem'
    · subst hmem'
      have hz : sparseAmp L (some p) = 0 := sparseAmp_eq_zero L (by simpa using! hhead)
      simp [sparseAmp, hz, add_zero]
    · have hne : p ≠ e.1 := by
        intro h
        apply hhead
        have hm := List.mem_map_of_mem (f := Prod.fst) hmem'
        rwa [show (p, v).1 = e.1 from by simp [h]] at hm
      simp [sparseAmp, hne, ih htail hmem']

/-- For a sparse list without repeated indices, the total amplitude mass equals the sum of
squared norms of its listed values. -/
theorem sparseMass {D : ℕ} : ∀ (L : List (Fin D × ℂ)), (L.map Prod.fst).Nodup →
    cmplxMass (sparseAmp L) = (L.map (fun e => ‖e.2‖ ^ 2)).sum := by
  intro L
  induction L with
  | nil => intro _; simp [cmplxMass, sparseAmp]
  | cons e L ih =>
    intro hnd
    obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnd
    have hz : sparseAmp L (some e.1) = 0 := sparseAmp_eq_zero L hhead
    have hpull : ∀ (x : Option (Fin D)) (f : Option (Fin D) → ℝ),
        f x + ∑ a ∈ Finset.univ.erase x, f a = ∑ a : Option (Fin D), f a := by
      intro x f
      rw [add_comm, Finset.sum_erase_add Finset.univ f (Finset.mem_univ x)]
    have hcenter : ‖sparseAmp (e :: L) (some e.1)‖ ^ 2 = ‖e.2‖ ^ 2 := by
      rw [sparseAmp_cons, if_pos rfl, hz, add_zero]
    have hoff : ∀ a : Option (Fin D), a ≠ some e.1 →
        ‖sparseAmp (e :: L) a‖ ^ 2 = ‖sparseAmp L a‖ ^ 2 := by
      intro a ha
      rw [sparseAmp_cons, if_neg ha, zero_add]
    calc cmplxMass (sparseAmp (e :: L))
        = ‖sparseAmp (e :: L) (some e.1)‖ ^ 2
            + ∑ a ∈ Finset.univ.erase (some e.1), ‖sparseAmp (e :: L) a‖ ^ 2 :=
          (hpull _ _).symm
      _ = ‖e.2‖ ^ 2 + ∑ a ∈ Finset.univ.erase (some e.1), ‖sparseAmp L a‖ ^ 2 := by
          rw [hcenter]
          exact congrArg (‖e.2‖ ^ 2 + ·)
            (Finset.sum_congr rfl fun a ha =>
              hoff a (fun h => (Finset.mem_erase.mp ha).1 h))
      _ = ‖e.2‖ ^ 2 + cmplxMass (sparseAmp L) := by
          have hz0 : ‖sparseAmp L (some e.1)‖ ^ 2 = 0 := by
            rw [hz, Complex.sq_norm, Complex.normSq_apply]; norm_num
          have hpull2 : ‖sparseAmp L (some e.1)‖ ^ 2
                + ∑ a ∈ Finset.univ.erase (some e.1), ‖sparseAmp L a‖ ^ 2
              = ∑ a : Option (Fin D), ‖sparseAmp L a‖ ^ 2 :=
            hpull (some e.1) (fun a => ‖sparseAmp L a‖ ^ 2)
          rw [hz0, zero_add] at hpull2
          rw [show cmplxMass (sparseAmp L)
                = ∑ a : Option (Fin D), ‖sparseAmp L a‖ ^ 2 from rfl,
            ← hpull2]
      _ = (List.map (fun e => ‖e.2‖ ^ 2) (e :: L)).sum := by
          rw [List.map_cons, List.sum_cons, ih htail]

/-- A sparse list without repeated indices and containing a nonzero amplitude has positive total
mass. -/
theorem sparseMass_pos {D : ℕ} (L : List (Fin D × ℂ))
    (hnd : (L.map Prod.fst).Nodup) {p : Fin D} {v : ℂ}
    (hmem : (p, v) ∈ L) (hv : v ≠ 0) :
    0 < cmplxMass (sparseAmp L) := by
  have hs : ‖sparseAmp L (some p)‖ ^ 2 ≤ cmplxMass (sparseAmp L) :=
    Finset.single_le_sum (fun a _ => sq_nonneg (‖sparseAmp L a‖))
      (Finset.mem_univ (some p))
  rw [sparseAmp_mem L hnd hmem] at hs
  have h2 : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  linarith

/-- For a sparse list without repeated indices, a listed amplitude is divided by the square root
of the total mass in the normalized target. -/
theorem cmplxTarget_sparse_mem {D : ℕ} (L : List (Fin D × ℂ))
    (hnd : (L.map Prod.fst).Nodup) {p : Fin D} {v : ℂ}
    (hmem : (p, v) ∈ L) :
    (cmplxTarget (sparseAmp L)) (some p)
      = v / Real.sqrt (cmplxMass (sparseAmp L) : ℝ) := by
  simp only [cmplxTarget]
  rw [sparseAmp_mem L hnd hmem]

/-- The normalized sparse target vanishes at an index absent from the sparse list. -/
theorem cmplxTarget_sparse_eq_zero {D : ℕ} (L : List (Fin D × ℂ)) {p : Fin D}
    (hp : p ∉ L.map Prod.fst) :
    (cmplxTarget (sparseAmp L)) (some p) = 0 := by
  simp only [cmplxTarget, sparseAmp_eq_zero L hp, zero_div]

/-- A sparse complex amplitude list of positive mass has a normalized target that can be
approximated to any positive tolerance by rational-table preparation. -/
theorem sparsePrepare_exists {D : ℕ} (L : List (Fin D × ℂ))
    (hmass : 0 < cmplxMass (sparseAmp L)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      ‖stateVector (prepareMatrix k (fun a => ratSq (zs a)) zs *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (cmplxTarget (sparseAmp L))‖ ≤ ε :=
  generalPrepare_exists _ (cmplxTarget_norm _ hmass)
    (by rw [cmplxTarget_none (sparseAmp L) (sparseAmp_none L)]) ε hε

/-- For a sparse list of positive mass and unitary selected operators, a rational-table circuit
approximates the operator combination weighted by the normalized sparse target to any
positive tolerance. -/
theorem sparseLcu_exists {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (L : List (Fin D × ℂ)) (hmass : 0 < cmplxMass (sparseAmp L))
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      ‖blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)))
          - stateCombination (cmplxTarget (sparseAmp L)) U‖ ≤ ε :=
  cmplxLcu_exists _ (cmplxTarget_norm _ hmass)
    (by rw [cmplxTarget_none (sparseAmp L) (sparseAmp_none L)]) U hU ε hε

/-- For Euclidean vectors of norm at most one, the difference of squared norms is at most twice
the distance between the vectors. -/
private theorem vec_norm_sq_sub_abs_le {X : Type*} [Fintype X] [DecidableEq X]
    (u v : EuclideanSpace ℂ X) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * ‖u - v‖ := by
  rw [sq_sub_sq, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v))]
  have h2 : ‖u‖ + ‖v‖ ≤ 2 := by linarith
  calc (‖u‖ + ‖v‖) * |‖u‖ - ‖v‖| ≤ (‖u‖ + ‖v‖) * ‖u - v‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le u v)
          (add_nonneg (norm_nonneg u) (norm_nonneg v))
    _ ≤ 2 * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg (u - v))

/-- A rational amplitude table approximating a unit state pointwise within `η` has positive mass
when `sqrt (D + 1) * η < 1`. -/
theorem ratMass_pos_of_near {D : ℕ} (ψ : QState (Option (Fin D)))
    (hψ : ‖stateVector ψ‖ = 1) (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1) :
    0 < rationalWeightMass (fun a => ratSq (zs a)) := by
  have ht : ‖stateVector (ratVec zs) - stateVector ψ‖
      ≤ Real.sqrt ((D + 1 : ℝ)) * η :=
    stateVector_sub_l2_le (ratVec zs) ψ (fun a => by simpa only [ratVec] using! hη a)
  have hrev : 1 - Real.sqrt ((D + 1 : ℝ)) * η ≤ ‖stateVector (ratVec zs)‖ := by
    have habs := abs_norm_sub_norm_le (stateVector (ratVec zs)) (stateVector ψ)
    rw [hψ] at habs
    obtain ⟨_, h2⟩ := abs_le.mp habs
    linarith
  have hnormpos : (0 : ℝ) < ‖stateVector (ratVec zs)‖ := by linarith
  have hsq := ratVec_norm_sq zs
  have hcast : (0 : ℝ) < ((rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) := by
    rw [← hsq]; positivity
  exact_mod_cast hcast

/-- For a normalized control state and unitary selected matrices, `stateCombination ψ U` has
norm at most one. -/
theorem stateCombination_norm_le {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖stateCombination ψ U‖ ≤ 1 := by
  have h1 : ∀ a : Option (Fin D), ‖(((‖ψ a‖ ^ 2 : ℝ) : ℂ))‖ = ‖ψ a‖ ^ 2 := by
    intro a
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hmass : ∑ a : Option (Fin D), ‖ψ a‖ ^ 2 = ‖stateVector ψ‖ ^ 2 := by
    rw [stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb]
    exact Finset.sum_congr rfl fun a _ => rfl
  refine (combination_norm_le (fun a => ((‖ψ a‖ ^ 2 : ℝ) : ℂ)) U hU).trans ?_
  calc ∑ a, ‖(((‖ψ a‖ ^ 2 : ℝ) : ℂ))‖ = ∑ a, ‖ψ a‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => h1 a
    _ = ‖stateVector ψ‖ ^ 2 := hmass
    _ ≤ (1 : ℝ) := by rw [hψ, one_pow]

/-- Under the rational-table approximation and normalization-gap hypotheses, clean-branch state
error is at most `(64 * (D + 1) / 2^k + 4 * (D + 1) * η)` times the data input norm. -/
theorem cmplxLcuWord_apply_state {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) :
    ‖stateVector (cleanBranch (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs
            (blockSelect U)) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ))
        - stateVector (stateCombination ψ U *ᵥ φ)‖
      ≤ (64 * (D + 1) / 2 ^ k + 4 * ((D + 1 : ℝ)) * η) * ‖stateVector φ‖ := by
  rw [lcuCleanBranch]
  have hsub : stateVector (blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs
            (blockSelect U))) *ᵥ φ) - stateVector (stateCombination ψ U *ᵥ φ)
      = stateVector ((blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs
            (blockSelect U))) - stateCombination ψ U) *ᵥ φ) := by
    simp [stateVector, WithLp.toLp_sub, Matrix.sub_mulVec]
  rw [hsub]
  have hn := stateVector_mulVec_norm_le
    (blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)))
      - stateCombination ψ U) φ
  refine hn.trans ?_
  exact mul_le_mul_of_nonneg_right
    (cmplxLcuWord_topBlock_error k ψ hψ zs hη hgap U hU) (norm_nonneg _)

/-- For normalized control and data states under the table-approximation hypotheses, the
clean-branch probability differs from the squared ideal output norm by at most twice `64 *
(D + 1) / 2^k + 4 * (D + 1) * η`. -/
theorem cmplxLcuBorn_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) :
    |MeasureProb (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖stateVector (stateCombination ψ U *ᵥ φ)‖ ^ 2|
      ≤ 2 * (64 * (D + 1) / 2 ^ k + 4 * ((D + 1 : ℝ)) * η) := by
  have hpos := ratMass_pos_of_near ψ hψ zs hη hgap
  have hw : ∀ a, (0 : ℚ) ≤ (fun a => ratSq (zs a)) a := fun a => ratSq_nonneg (zs a)
  have hWU : evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U))
      ∈ Matrix.unitaryGroup (Option (Fin D) × X) ℂ :=
    (lcuBlockWord_wellFormed k _ zs hw _ (blockSelect_unitary hU)).evaluate_unitary
      (Submonoid.one_mem _)
  have hclose := cmplxLcuWord_apply_state k ψ hψ zs hη hgap U hU φ
  rw [hφ, mul_one, lcuCleanBranch] at hclose
  have hx : ‖stateVector (blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs
        (blockSelect U))) *ᵥ φ)‖ ≤ 1 := by
    have h1 := stateVector_mulVec_norm_le
      (blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)))) φ
    rw [hφ, mul_one] at h1
    refine h1.trans ?_
    calc ‖blockNone (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)))‖
        ≤ ‖evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U))‖ :=
          blockNone_norm_le _
      _ = 1 := l2_norm_unitary_eq_one hWU
  have hy : ‖stateVector (stateCombination ψ U *ᵥ φ)‖ ≤ 1 := by
    have h1 := stateVector_mulVec_norm_le (stateCombination ψ U) φ
    rw [hφ, mul_one] at h1
    exact h1.trans (stateCombination_norm_le ψ hψ U hU)
  rw [measureProb_none_branch, lcuCleanBranch]
  exact (vec_norm_sq_sub_abs_le _ _ hx hy).trans
    (mul_le_mul_of_nonneg_left hclose (by norm_num))

/-- For `0 < ε ≤ 1`, pointwise table error at most `ε / (16 * (D + 1))` and precision
`precisionFor D (ε / 8)` give clean-branch probability error at most `ε`. -/
theorem cmplxLcuBorn_none_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex)
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ (ε : ℝ) / (16 * ((D + 1 : ℝ))))
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) :
    |MeasureProb (evaluate 1 (lcuBlockWord (precisionFor D (ε / 8))
            (fun a => ratSq (zs a)) zs (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖stateVector (stateCombination ψ U *ᵥ φ)‖ ^ 2| ≤ (ε : ℝ) := by
  have hD1 : (1 : ℝ) ≤ Real.sqrt ((D + 1 : ℝ)) := by
    have hs : (0 : ℝ) ≤ Real.sqrt ((D + 1 : ℝ)) := Real.sqrt_nonneg _
    have hD : (1 : ℝ) ≤ ((D + 1 : ℝ)) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le D))
    nlinarith [hs, Real.mul_self_sqrt (show (0 : ℝ) ≤ (D + 1 : ℝ) by positivity), hD]
  have hgap : Real.sqrt ((D + 1 : ℝ)) * ((ε : ℝ) / (16 * ((D + 1 : ℝ)))) < 1 := by
    have hcalc : Real.sqrt ((D + 1 : ℝ)) * ((ε : ℝ) / (16 * ((D + 1 : ℝ))))
        = (ε : ℝ) / (16 * Real.sqrt ((D + 1 : ℝ))) := by
      field_simp
      exact Real.sq_sqrt (by positivity)
    rw [hcalc]
    have hεr := (by exact_mod_cast hε1 : (ε : ℝ) ≤ 1)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * Real.sqrt ((D + 1 : ℝ)))]
    nlinarith
  have h := cmplxLcuBorn_none (precisionFor D (ε / 8)) ψ hψ zs hη hgap U hU φ hφ
  have hb := prepError_le_epsilon (D := D) (ε / 8) (by linarith : 0 < ε / 8)
  have hbcast : ((ε / 8 : ℚ) : ℝ) = (ε : ℝ) / 8 := by
    push_cast
    ring
  have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 8) : ℝ)
      = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (ε / 8) : ℝ)) := by
    ring
  have hterm : 4 * ((D + 1 : ℝ)) * ((ε : ℝ) / (16 * ((D + 1 : ℝ)))) ≤ (ε : ℝ) / 4 := by
    have hcalc : 4 * ((D + 1 : ℝ)) * ((ε : ℝ) / (16 * ((D + 1 : ℝ))))
        = (ε : ℝ) / 4 := by
      field_simp
      norm_num
    rw [hcalc]
  have hεr0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  linarith

/-- For normalized control and data states, with the control vanishing at `none`, rational
amplitudes and a precision exist that approximate the ideal clean-branch probability to any
positive tolerance. -/
theorem cmplxLcuBorn_exists {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1) (hψ0 : ψ none = 0)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      |MeasureProb (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
          (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
        - ‖stateVector (stateCombination ψ U *ᵥ φ)‖ ^ 2| ≤ ε := by
  obtain ⟨ℓ, hℓ0, hℓlt⟩ := exists_pos_rat_lt (x := ε / 8) (by linarith)
  have hs : 0 < Real.sqrt ((D + 1 : ℝ)) := by positivity
  have hmin : 0 < min (ε / (16 * ((D + 1 : ℝ))))
      (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) := by
    positivity
  obtain ⟨zs, hz0, hz⟩ := ratTable_exists ψ hψ0 hmin
  refine ⟨zs, precisionFor D ℓ, hz0, ?_⟩
  have hgap : Real.sqrt ((D + 1 : ℝ))
      * (min (ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ))))) < 1 := by
    have hle : Real.sqrt ((D + 1 : ℝ))
        * (min (ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ Real.sqrt ((D + 1 : ℝ)) * (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hs)
    have hcalc : Real.sqrt ((D + 1 : ℝ))
        * (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) = 1 / 8 := by
      field_simp
    rw [hcalc] at hle
    linarith
  have h := cmplxLcuBorn_none (precisionFor D ℓ) ψ hψ zs hz hgap U hU φ hφ
  have hb : (32 * (D + 1) : ℝ) / 2 ^ precisionFor D ℓ ≤ (ℓ : ℝ) :=
    prepError_le_epsilon ℓ hℓ0
  have hwordterm : 2 * (64 * ((D : ℝ) + 1) / (2 ^ precisionFor D ℓ : ℝ))
      ≤ 2 * (2 * ((ℓ : ℝ))) := by
    have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ precisionFor D ℓ : ℝ)
        = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D ℓ : ℝ)) := by ring
    rw [hsplit]
    linarith
  have hterm : 2 * (4 * ((D + 1 : ℝ))
      * (min (ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))) ≤ ε / 2 := by
    have hle : 4 * ((D + 1 : ℝ))
        * (min (ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ 4 * ((D + 1 : ℝ)) * (ε / (16 * ((D + 1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _)
        (by positivity : (0 : ℝ) ≤ 4 * ((D + 1 : ℝ)))
    have hcalc : 4 * ((D + 1 : ℝ)) * (ε / (16 * ((D + 1 : ℝ)))) = ε / 4 := by
      field_simp
      norm_num
    rw [hcalc] at hle
    have h2 : (2 : ℝ) * (ε / 4) = ε / 2 := by ring
    linarith
  linarith

/-- If `p₀ > 0` bounds the ideal output norm and exceeds the combined preparation and table
error, the collapsed-state error is at most twice that combined error divided by `p₀`. -/
theorem cmplxLcuWord_collapse_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hpA : p₀ ≤ ‖stateVector (stateCombination ψ U *ᵥ φ)‖)
    (hk : 64 * (D + 1) / 2 ^ k + 4 * ((D + 1 : ℝ)) * η < p₀) :
    ‖stateVector (measureCollapse_none (evaluate 1
          (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ))
        - NormedSpace.normalize (stateVector (stateCombination ψ U *ᵥ φ))‖
      ≤ 2 * (64 * (D + 1) / 2 ^ k + 4 * ((D + 1 : ℝ)) * η) / p₀ := by
  have hclose := cmplxLcuWord_apply_state k ψ hψ zs hη hgap U hU φ
  rw [hφ, mul_one] at hclose
  have hηnn : (0 : ℝ) ≤ η := le_trans (norm_nonneg _) (hη none)
  have hδnn : (0 : ℝ) ≤ 2 * (64 * (D + 1) / 2 ^ k + 4 * ((D + 1 : ℝ)) * η) :=
    mul_nonneg (by norm_num)
      (add_nonneg (by positivity) (mul_nonneg (by positivity) hηnn))
  rw [stateVector_measureCollapse_none]
  obtain ⟨_, hb⟩ := normalize_error_of_gap hclose (hk.trans_le hpA)
  exact hb.trans (div_le_div_of_nonneg_left hδnn hp₀ hpA)

/-- For `0 < ε ≤ 1` and a positive rational lower bound on the ideal output norm, the specified
table tolerance and precision `precisionFor D (p₀ * ε / 8)` give collapsed-state error at
most `ε`. -/
theorem cmplxLcuWord_collapse_none_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p₀ : ℚ) (hp₀ : 0 < p₀)
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex)
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖
      ≤ ((p₀ : ℚ) : ℝ) * (ε : ℝ) / (16 * ((D + 1 : ℝ))))
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1)
    (hpA : ((p₀ : ℚ) : ℝ) ≤ ‖stateVector (stateCombination ψ U *ᵥ φ)‖) :
    ‖stateVector (measureCollapse_none (evaluate 1
          (lcuBlockWord (precisionFor D (p₀ * ε / 8)) (fun a => ratSq (zs a)) zs
            (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ))
        - NormedSpace.normalize (stateVector (stateCombination ψ U *ᵥ φ))‖
      ≤ (ε : ℝ) := by
  have hD1 : (1 : ℝ) ≤ Real.sqrt ((D + 1 : ℝ)) := by
    have hs : (0 : ℝ) ≤ Real.sqrt ((D + 1 : ℝ)) := Real.sqrt_nonneg _
    have hD : (1 : ℝ) ≤ ((D + 1 : ℝ)) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le D))
    nlinarith [hs, Real.mul_self_sqrt (show (0 : ℝ) ≤ (D + 1 : ℝ) by positivity), hD]
  have hp₁ : ((p₀ : ℚ) : ℝ) ≤ 1 := by
    have h1 := stateVector_mulVec_norm_le (stateCombination ψ U) φ
    rw [hφ, mul_one] at h1
    exact hpA.trans (h1.trans (stateCombination_norm_le ψ hψ U hU))
  have hεr : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hp0nn : (0 : ℝ) ≤ ((p₀ : ℚ) : ℝ) := by exact_mod_cast hp₀.le
  have hεnn : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε.le
  have hgap : Real.sqrt ((D + 1 : ℝ))
      * (((p₀ : ℚ) : ℝ) * (ε : ℝ) / (16 * ((D + 1 : ℝ)))) < 1 := by
    have hcalc : Real.sqrt ((D + 1 : ℝ))
        * (((p₀ : ℚ) : ℝ) * (ε : ℝ) / (16 * ((D + 1 : ℝ))))
        = ((p₀ : ℚ) : ℝ) * (ε : ℝ) / (16 * Real.sqrt ((D + 1 : ℝ))) := by
      field_simp
      exact Real.sq_sqrt (by positivity)
    have hprod : ((p₀ : ℚ) : ℝ) * (ε : ℝ) ≤ (1 : ℝ) * 1 := by
      nlinarith [hp₁, hεr, hp0nn, hεnn]
    have hs16 : (16 : ℝ) ≤ 1 * (16 * Real.sqrt ((D + 1 : ℝ))) := by
      nlinarith [hD1]
    rw [hcalc, div_lt_iff₀ (show (0 : ℝ) < 16 * Real.sqrt ((D + 1 : ℝ)) by positivity)]
    nlinarith [hprod, hs16]
  have hb := prepError_le_epsilon (D := D) (p₀ * ε / 8) (by positivity)
  have hbcast : ((p₀ * ε / 8 : ℚ) : ℝ) = ((p₀ : ℚ) : ℝ) * (ε : ℝ) / 8 := by
    push_cast
    ring
  have hδ : 64 * (D + 1) / 2 ^ precisionFor D (p₀ * ε / 8)
        + 4 * ((D + 1 : ℝ)) * (((p₀ : ℚ) : ℝ) * (ε : ℝ) / (16 * ((D + 1 : ℝ))))
      ≤ ((p₀ : ℚ) : ℝ) * (ε : ℝ) / 2 := by
    have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ precisionFor D (p₀ * ε / 8) : ℝ)
        = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D (p₀ * ε / 8) : ℝ)) := by
      ring
    have hterm : 4 * ((D + 1 : ℝ))
        * (((p₀ : ℚ) : ℝ) * (ε : ℝ) / (16 * ((D + 1 : ℝ))))
        = ((p₀ : ℚ) : ℝ) * (ε : ℝ) / 4 := by
      field_simp
      norm_num
    rw [hterm]
    linarith
  have h := cmplxLcuWord_collapse_none (precisionFor D (p₀ * ε / 8)) ψ hψ zs hη hgap U hU φ hφ
    ((p₀ : ℚ) : ℝ) (by exact_mod_cast hp₀) hpA
    (hδ.trans_lt (half_budget_lt (by exact_mod_cast hp₀) (by exact_mod_cast hε1)))
  exact h.trans (collapse_eps_arith (by exact_mod_cast hp₀) hδ)

/-- For normalized inputs with control amplitude zero at `none` and a positive lower bound on
the ideal output norm, rational-table circuits achieve any collapsed-state tolerance `0 < ε
≤ 1`. -/
theorem cmplxLcuWord_collapse_exists {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (hψ0 : ψ none = 0) (U : Option (Fin D) → Matrix X X ℂ)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hpA : p₀ ≤ ‖stateVector (stateCombination ψ U *ᵥ φ)‖)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      ‖stateVector (measureCollapse_none (evaluate 1
            (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)) *ᵥ
            TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ))
          - NormedSpace.normalize (stateVector (stateCombination ψ U *ᵥ φ))‖ ≤ ε := by
  obtain ⟨ℓ, hℓ0, hℓlt⟩ := exists_pos_rat_lt (x := p₀ * ε / 8) (by positivity)
  have hs : 0 < Real.sqrt ((D + 1 : ℝ)) := by positivity
  have hmin : 0 < min (p₀ * ε / (16 * ((D + 1 : ℝ))))
      (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) := by
    positivity
  obtain ⟨zs, hz0, hz⟩ := ratTable_exists ψ hψ0 hmin
  refine ⟨zs, precisionFor D ℓ, hz0, ?_⟩
  have hgap : Real.sqrt ((D + 1 : ℝ))
      * (min (p₀ * ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ))))) < 1 := by
    have hle : Real.sqrt ((D + 1 : ℝ))
        * (min (p₀ * ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ Real.sqrt ((D + 1 : ℝ)) * (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hs)
    have hcalc : Real.sqrt ((D + 1 : ℝ))
        * (1 / (8 * Real.sqrt ((D + 1 : ℝ)))) = 1 / 8 := by
      field_simp
    rw [hcalc] at hle
    linarith
  have hb : (32 * (D + 1) : ℝ) / 2 ^ precisionFor D ℓ ≤ (ℓ : ℝ) :=
    prepError_le_epsilon ℓ hℓ0
  have hδ : 64 * (D + 1) / 2 ^ precisionFor D ℓ
        + 4 * ((D + 1 : ℝ))
          * (min (p₀ * ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
      ≤ p₀ * ε / 2 := by
    have hsplit : 64 * ((D : ℝ) + 1) / (2 ^ precisionFor D ℓ : ℝ)
        = 2 * (32 * ((D : ℝ) + 1) / (2 ^ precisionFor D ℓ : ℝ)) := by ring
    have hterm : 4 * ((D + 1 : ℝ))
        * (min (p₀ * ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
        ≤ p₀ * ε / 4 := by
      have hle : 4 * ((D + 1 : ℝ))
          * (min (p₀ * ε / (16 * ((D + 1 : ℝ)))) (1 / (8 * Real.sqrt ((D + 1 : ℝ)))))
          ≤ 4 * ((D + 1 : ℝ)) * (p₀ * ε / (16 * ((D + 1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _)
          (by positivity : (0 : ℝ) ≤ 4 * ((D + 1 : ℝ)))
      have hcalc : 4 * ((D + 1 : ℝ)) * (p₀ * ε / (16 * ((D + 1 : ℝ)))) = p₀ * ε / 4 := by
        field_simp
        norm_num
      rw [hcalc] at hle
      exact hle
    have hℓ' : 2 * ((ℓ : ℝ)) ≤ p₀ * ε / 4 := by linarith
    have h2 : 2 * ((ℓ : ℝ)) + p₀ * ε / 4 ≤ p₀ * ε / 2 := by linarith
    linarith
  have h := cmplxLcuWord_collapse_none (precisionFor D ℓ) ψ hψ zs hz hgap U hU φ hφ p₀ hp₀ hpA
    (hδ.trans_lt (half_budget_lt hp₀ hε1))
  exact h.trans (collapse_eps_arith hp₀ hδ)

/-- For a sparse control table of positive mass and normalized data input, a rational-table
circuit approximates the ideal clean-branch probability to any positive tolerance. -/
theorem sparseLcuBorn_exists {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (L : List (Fin D × ℂ)) (hmass : 0 < cmplxMass (sparseAmp L))
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      |MeasureProb (evaluate 1 (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
          (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
        - ‖stateVector (stateCombination (cmplxTarget (sparseAmp L)) U *ᵥ φ)‖ ^ 2| ≤ ε :=
  cmplxLcuBorn_exists _ (cmplxTarget_norm _ hmass)
    (by rw [cmplxTarget_none (sparseAmp L) (sparseAmp_none L)]) U hU φ hφ ε hε

/-- For a positive-mass sparse control table and normalized data input with a positive lower
bound on the ideal output norm, a rational-table circuit achieves any collapsed-state
tolerance `0 < ε ≤ 1`. -/
theorem sparseLcuWord_collapse_exists {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (L : List (Fin D × ℂ)) (hmass : 0 < cmplxMass (sparseAmp L))
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hpA : p₀ ≤ ‖stateVector (stateCombination (cmplxTarget (sparseAmp L)) U *ᵥ φ)‖)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (zs : Option (Fin D) → RatComplex) (k : ℕ), zs none = ratZero ∧
      ‖stateVector (measureCollapse_none (evaluate 1
            (lcuBlockWord k (fun a => ratSq (zs a)) zs (blockSelect U)) *ᵥ
            TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ))
          - NormedSpace.normalize
              (stateVector (stateCombination (cmplxTarget (sparseAmp L)) U *ᵥ φ))‖ ≤ ε :=
  cmplxLcuWord_collapse_exists _ (cmplxTarget_norm _ hmass)
    (by rw [cmplxTarget_none (sparseAmp L) (sparseAmp_none L)]) U hU φ hφ p₀ hp₀ hpA ε hε hε1

/-- A rational table approximating a unit state pointwise within `η` under the normalization-gap
condition changes the associated weighted unitary combination by at most `4 * (D + 1) * η`. -/
theorem cmplxLcuCombination_near {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖(∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a)
        - stateCombination ψ U‖ ≤ 4 * ((D + 1 : ℝ)) * η := by
  have hpos := ratMass_pos_of_near ψ hψ zs hη hgap
  have hnear := ratTarget_near ψ hψ zs hη hgap
  have hmassroot : ‖stateVector (ratTarget zs)‖ = 1 := ratTarget_norm zs hpos
  have hentry : ∀ a : Option (Fin D),
      |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        - (‖ψ a‖ ^ 2 : ℝ)| ≤ 2 * ‖ratTarget zs a - ψ a‖ := by
    intro a
    have hcoeffz : ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        = ‖ratTarget zs a‖ ^ 2 := (ratTarget_entry_norm_sq zs hpos a).symm
    rw [hcoeffz]
    have hle := norm_sq_sub_abs_le (ratTarget zs a) (ψ a)
    have hb1 : ‖ratTarget zs a‖ ≤ 1 := by
      have hb := stateVector_entry_norm_le (ratTarget zs) a
      rwa [hmassroot] at hb
    have hb2 : ‖ψ a‖ ≤ 1 := by
      have hb := stateVector_entry_norm_le ψ a
      rwa [hψ] at hb
    have hbound : (‖ratTarget zs a‖ + ‖ψ a‖) * ‖ratTarget zs a - ψ a‖
        ≤ 2 * ‖ratTarget zs a - ψ a‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    exact hle.trans hbound
  have hsum : ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        - (‖ψ a‖ ^ 2 : ℝ)| ≤ 4 * ((D + 1 : ℝ)) * η := by
    have h1 : ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
          - (‖ψ a‖ ^ 2 : ℝ)|
        ≤ ∑ a, 2 * ‖ratTarget zs a - ψ a‖ :=
      Finset.sum_le_sum fun a _ => hentry a
    have h2 : ∑ a, 2 * ‖ratTarget zs a - ψ a‖
        ≤ 2 * (Real.sqrt ((D + 1 : ℝ))
            * ‖stateVector (fun a => ratTarget zs a - ψ a)‖) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_norm_le (fun a => ratTarget zs a - ψ a))
        (by norm_num)
    have h3 : ‖stateVector (fun a => ratTarget zs a - ψ a)‖
        ≤ 2 * Real.sqrt ((D + 1 : ℝ)) * η := by
      rw [show stateVector (fun a => ratTarget zs a - ψ a)
          = stateVector (ratTarget zs) - stateVector ψ from rfl]
      exact hnear
    have hcalc : 2 * (Real.sqrt ((D + 1 : ℝ)) * (2 * Real.sqrt ((D + 1 : ℝ)) * η))
        = 4 * ((D + 1 : ℝ)) * η := by
      have hsq : Real.sqrt ((D + 1 : ℝ)) * Real.sqrt ((D + 1 : ℝ)) = (D + 1 : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hexp : 2 * (Real.sqrt ((D + 1 : ℝ)) * (2 * Real.sqrt ((D + 1 : ℝ)) * η))
          = 4 * (Real.sqrt ((D + 1 : ℝ)) * Real.sqrt ((D + 1 : ℝ))) * η := by ring
      rw [hexp, hsq]
    calc ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
          - (‖ψ a‖ ^ 2 : ℝ)|
        ≤ ∑ a, 2 * ‖ratTarget zs a - ψ a‖ := h1
      _ ≤ 2 * (Real.sqrt ((D + 1 : ℝ))
          * ‖stateVector (fun a => ratTarget zs a - ψ a)‖) := h2
      _ ≤ 2 * (Real.sqrt ((D + 1 : ℝ)) * (2 * Real.sqrt ((D + 1 : ℝ)) * η)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h3 (by positivity)) (by norm_num)
      _ = 4 * ((D + 1 : ℝ)) * η := hcalc
  have hcsum : (∑ a, (((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ)) • U a)
        - stateCombination ψ U
      = ∑ a, ((((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) : ℂ)
            - ((‖ψ a‖ ^ 2 : ℝ) : ℂ)) • U a := by
    rw [stateCombination, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (sub_smul _ _ _).symm
  have hdiff : ‖∑ a, ((((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ) : ℂ)
            - ((‖ψ a‖ ^ 2 : ℝ) : ℂ)) • U a‖
      ≤ ∑ a, |((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℝ)
        - (‖ψ a‖ ^ 2 : ℝ)| := by
    refine (combination_norm_le _ U hU).trans ?_
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hcsum]
  exact hdiff.trans hsum

/-- The unitary combination weighted by normalized squared rational amplitudes of positive total
mass has norm at most one. -/
theorem loadedCombination_norm_le {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (zs : Option (Fin D) → RatComplex)
    (hm : 0 < rationalWeightMass (fun a => ratSq (zs a)))
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ) :
    ‖∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a‖
      ≤ 1 :=
  lcuCombination_norm_le (fun a => ratSq (zs a)) zs (fun a => ratSq_nonneg (zs a)) hm U hU

/-- For matrices of norm at most one, the distance between their conjugate-transpose products is
at most twice their matrix distance. -/
theorem opNorm_moment_transport {X : Type*} [Fintype X] [DecidableEq X]
    (A B : Matrix X X ℂ) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖Aᴴ * A - Bᴴ * B‖ ≤ 2 * ‖A - B‖ := by
  have hident : Aᴴ * A - Bᴴ * B = (A - B)ᴴ * A + Bᴴ * (A - B) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hident]
  calc ‖(A - B)ᴴ * A + Bᴴ * (A - B)‖
      ≤ ‖(A - B)ᴴ * A‖ + ‖Bᴴ * (A - B)‖ := norm_add_le _ _
    _ ≤ ‖(A - B)ᴴ‖ * ‖A‖ + ‖Bᴴ‖ * ‖A - B‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = ‖A - B‖ * ‖A‖ + ‖B‖ * ‖A - B‖ := by
        rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    _ ≤ ‖A - B‖ * 1 + 1 * ‖A - B‖ := by
        refine add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
    _ = 2 * ‖A - B‖ := by ring

/-- If the normalized rational-table combination has squared modulus `sq • 1`, the squared
modulus of the target state combination differs from `sq • 1` by at most `8 * (D + 1) * η`. -/
theorem cmplxLcu_moment_transport {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a
        = sq • 1) :
    ‖(stateCombination ψ U)ᴴ * stateCombination ψ U - sq • 1‖
      ≤ 8 * ((D + 1 : ℝ)) * η := by
  have hnear := cmplxLcuCombination_near ψ hψ zs hη hgap U hU
  have hB := loadedCombination_norm_le zs (ratMass_pos_of_near ψ hψ zs hη hgap) U hU
  have hA' := stateCombination_norm_le ψ hψ U hU
  have htrans := opNorm_moment_transport (stateCombination ψ U)
    (∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a) hA' hB
  rw [← hA]
  refine htrans.trans ?_
  have hflip : ‖stateCombination ψ U
      - ∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a‖
      = ‖∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a
        - stateCombination ψ U‖ := by
    rw [← neg_sub, norm_neg]
  rw [hflip]
  linarith

/-- For unitaries satisfying `Pᴴ * Q + Qᴴ * P = 0`, a real linear combination `c • P + d • Q`
has conjugate-transpose product `(c² + d²) • 1`. -/
theorem twoFiber_isometry {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : Matrix X X ℂ) (hP : P ∈ Matrix.unitaryGroup X ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup X ℂ)
    (hanti : Pᴴ * Q + Qᴴ * P = 0) (c d : ℝ) :
    ((c : ℂ) • P + (d : ℂ) • Q)ᴴ * ((c : ℂ) • P + (d : ℂ) • Q)
      = ((c ^ 2 + d ^ 2 : ℝ) : ℂ) • (1 : Matrix X X ℂ) := by
  have hPP : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hP
    rwa [Matrix.star_eq_conjTranspose] at h
  have hQQ : Qᴴ * Q = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hQ
    rwa [Matrix.star_eq_conjTranspose] at h
  have hexp : ((c : ℂ) • P + (d : ℂ) • Q)ᴴ * ((c : ℂ) • P + (d : ℂ) • Q)
      = ((c : ℂ) ^ 2) • (Pᴴ * P) + ((c : ℂ) * (d : ℂ)) • (Pᴴ * Q + Qᴴ * P)
        + ((d : ℂ) ^ 2) • (Qᴴ * Q) := by
    have hc : (((c : ℝ) : ℂ) • P)ᴴ = ((c : ℝ) : ℂ) • Pᴴ := by
      rw [Matrix.conjTranspose_smul]
      congr 1
      exact Complex.conj_ofReal _
    have hd : (((d : ℝ) : ℂ) • Q)ᴴ = ((d : ℝ) : ℂ) • Qᴴ := by
      rw [Matrix.conjTranspose_smul]
      congr 1
      exact Complex.conj_ofReal _
    rw [Matrix.conjTranspose_add, hc, hd]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, smul_add]
    module
  rw [hexp, hPP, hQQ, hanti, smul_zero, add_zero]
  have hsum : ((c : ℂ) ^ 2 + (d : ℂ) ^ 2) • (1 : Matrix X X ℂ)
      = ((c ^ 2 + d ^ 2 : ℝ) : ℂ) • (1 : Matrix X X ℂ) := by
    have hscalar : ((c : ℂ) ^ 2 + (d : ℂ) ^ 2) = ((c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hscalar]
  rw [← add_smul, hsum]

/-- Under the scalar squared-modulus condition on the rational-table combination, the repeated
Grover word's clean-branch probability differs from the squared Chebyshev modulus by at most
`2 * (m * (128 * (D + 1) / 2^k))`. -/
theorem cmplxGroverBorn_none {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (m k : ℕ) (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a
        = sq • 1)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) :
    |MeasureProb (evaluate 1 (groverWordRepeat m k (fun a => ratSq (zs a)) zs
          (blockSelect U)) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖groverChebT m (2 * sq - 1)‖ ^ 2|
      ≤ 2 * (m * (128 * (D + 1) / 2 ^ k)) :=
  groverBorn_none m k (fun a => ratSq (zs a)) zs (fun a => ratSq_nonneg (zs a))
    (ratMass_pos_of_near ψ hψ zs hη hgap) U hU sq hA φ hφ

/-- Under the scalar squared-modulus condition on the rational-table combination, the specified
precision gives clean-branch probability error at most `ε` after `m + 1` Grover rounds. -/
theorem cmplxGroverBorn_none_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (m : ℕ) (ε : ℚ) (hε : 0 < ε)
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℂ)
    (hA : (∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a
        = sq • 1)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) :
    |MeasureProb (evaluate 1 (groverWordRepeat (m + 1)
          (precisionFor D (ε / (8 * (m + 1)))) (fun a => ratSq (zs a)) zs
          (blockSelect U)) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - ‖groverChebT (m + 1) (2 * sq - 1)‖ ^ 2|
      ≤ (ε : ℝ) :=
  groverBorn_none_epsilon m ε hε (fun a => ratSq (zs a)) zs (fun a => ratSq_nonneg (zs a))
    (ratMass_pos_of_near ψ hψ zs hη hgap) U hU sq hA φ hφ

/-- If the rational-table combination has scalar squared modulus `sq` with `0 < sq < 1`, a
positive round count and the specified precision achieve clean-branch probability at least
`1 - sq - ε`. -/
theorem cmplxGroverBorn_none_optimal_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε)
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    (sq : ℝ) (h0 : 0 < sq) (h1 : sq < 1)
    (hA : (∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a
        = ((sq : ℝ) : ℂ) • 1)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) :
    ∃ m : ℕ, 1 - sq - (ε : ℝ)
      ≤ MeasureProb (evaluate 1 (groverWordRepeat (m + 1)
          (precisionFor D (ε / (8 * (m + 1)))) (fun a => ratSq (zs a)) zs
          (blockSelect U)) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none)) :=
  groverBorn_none_optimal_epsilon ε hε (fun a => ratSq (zs a)) zs
    (fun a => ratSq_nonneg (zs a))
    (ratMass_pos_of_near ψ hψ zs hη hgap) U hU sq h0 h1 hA φ hφ

/-- For a rational-table combination with scalar squared modulus `s > 1 / 2`, the two-round
amplification word has clean-branch probability within `2 * (2 * (128 * (D + 1) / 2^k))` of
one. -/
theorem cmplxOaaWord_born {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (k : ℕ) (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    {s : ℝ} (hs : 1 / 2 < s)
    (hA : (∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a
        = ((s : ℝ) : ℂ) • 1)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) :
    |MeasureProb (evaluate 1 (oaaWord (oaaPhase s) k (fun a => ratSq (zs a)) zs
          (blockSelect U)) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - 1|
      ≤ 2 * (2 * (128 * (D + 1) / 2 ^ k)) :=
  oaaWord_born k (fun a => ratSq (zs a)) zs (fun a => ratSq_nonneg (zs a))
    (ratMass_pos_of_near ψ hψ zs hη hgap) U hU hs hA φ hφ

/-- For a rational-table combination with scalar squared modulus `s > 1 / 2`, precision
`precisionFor D (ε / 16)` makes the two-round clean-branch probability differ from one by at
most `ε`. -/
theorem cmplxOaaWord_born_epsilon {D : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] (ε : ℚ) (hε : 0 < ε)
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1)
    (zs : Option (Fin D) → RatComplex) {η : ℝ}
    (hη : ∀ a, ‖ratToComplex (zs a) - ψ a‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1)
    (U : Option (Fin D) → Matrix X X ℂ) (hU : ∀ a, U a ∈ Matrix.unitaryGroup X ℂ)
    {s : ℝ} (hs : 1 / 2 < s)
    (hA : (∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a)ᴴ
        * ∑ a, ((ratSq (zs a) / rationalWeightMass (fun a => ratSq (zs a)) : ℚ) : ℂ) • U a
        = ((s : ℝ) : ℂ) • 1)
    (φ : QState X) (hφ : ‖stateVector φ‖ = 1) :
    |MeasureProb (evaluate 1 (oaaWord (oaaPhase s)
          (precisionFor D (ε / 16)) (fun a => ratSq (zs a)) zs
          (blockSelect U)) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))) φ)
        (Finset.univ.filter (fun p : Option (Fin D) × X => p.1 = none))
      - 1|
      ≤ (ε : ℝ) :=
  oaaWord_born_epsilon ε hε (fun a => ratSq (zs a)) zs (fun a => ratSq_nonneg (zs a))
    (ratMass_pos_of_near ψ hψ zs hη hgap) U hU hs hA φ hφ

end Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt
