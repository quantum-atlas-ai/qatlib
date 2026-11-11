/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.CoherentSim.CoherentOAA.ObliviousAmplification
import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.SharedAncilla.AncillaProduct.SharedAncillaUnitaryProduct
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.BlockEncoding.Basic

/-!
# Robust coherent implementation by cubic amplification

This module compiles the cubic oblivious amplitude amplification word for a shared input and
output frame. From a scale-two block encoding of a unitary, it bounds the amplified compressed
error, the full framed-state error, and leakage outside the frame.

The analysis makes the circuit and resource costs explicit, including substituted subroutines
and repeated applications. It develops the amplitude amplification construction of
[BrassardEtAl2002] with the error budget `coherentOAAError`.

## Main statements

* `coherent_oaa_word_correct`: the word is well formed, uses three queries and four fixed gates,
  and has the cubic compression.
* `coherent_oaa_clean_workspace_error`: compressed accuracy controls the full framed-state
  error.
* `coherent_oaa_leakage_and_success`: the amplified circuit has explicit leakage and success
  bounds.
* `coherent_oaa_expanded_repeat_error_and_cost`: expanded repetitions have explicit counts and a
  linear accumulated state-error bound.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

/-- A unitary matrix preserves the Euclidean norm of a state vector. -/
private theorem norm_toEuclidean_mulVec_of_unitary {I : Type} [Fintype I] [DecidableEq I]
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    ‖toEuclidean_fromVec (U *ᵥ ψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
  norm_applyGate_of_mem_unitaryGroup hU ψ

/-- The Euclidean norm of a matrix-vector product is at most the operator norm times the
vector's Euclidean norm. -/
private theorem norm_toEuclidean_mulVec_le {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState I) :
    ‖toEuclidean_fromVec (U *ᵥ ψ)‖ ≤ ‖U‖ * ‖toEuclidean_fromVec ψ‖ :=
  norm_applyGate_le U ψ

/-- An isometry preserves the Euclidean norm of a state vector. -/
private theorem norm_toEuclidean_mulVec_of_isometry {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] {V : Matrix H I ℂ} (hV : IsIsometry V) (ψ : QState I) :
    ‖toEuclidean_fromVec (V *ᵥ ψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
  Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.stateVector_norm hV ψ

/-- Real scalar multiplication of a complex matrix agrees with multiplication by the
corresponding complex scalar. -/
private theorem real_smul_matrix_eq {H I : Type} [Fintype H] [Fintype I] (r : ℝ)
    (M : Matrix H I ℂ) : (r • M) = ((r : ℂ)) • M := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Conversion from a state vector to Euclidean space preserves addition. -/
private theorem toEuclidean_fromVec_add {I : Type} [Fintype I] (ψ φ : QState I) :
    toEuclidean_fromVec (ψ + φ) = toEuclidean_fromVec ψ + toEuclidean_fromVec φ :=
  rfl

/-- Conversion from a state vector to Euclidean space preserves subtraction. -/
private theorem toEuclidean_fromVec_sub {I : Type} [Fintype I] (ψ φ : QState I) :
    toEuclidean_fromVec (ψ - φ) = toEuclidean_fromVec ψ - toEuclidean_fromVec φ :=
  rfl

/-- The total measurement mass of a state vector equals its squared Euclidean norm. -/
private theorem measureProb_univ_eq_norm_sq {I : Type} [Fintype I] [DecidableEq I]
    (φ : QState I) :
    MeasureProb φ Finset.univ = ‖toEuclidean_fromVec φ‖ ^ 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  rfl

/-- The compiled cubic amplification word with both signal projectors equal to the range
projector of `R`. -/
noncomputable def coherentOAAWord {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (R : Matrix H I ℂ) : List (AdjointStep H) :=
  compileQSVT (rangeProjector R) (rangeProjector R) (-Complex.I) cubicPhases

/-- The matrix evaluation of the shared-frame cubic amplification word with oracle `U`. -/
noncomputable def coherentOAAOperator {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (U : Matrix H H ℂ) (R : Matrix H I ℂ) : Matrix H H ℂ :=
  evaluate U (coherentOAAWord R)

/-- The amplified compression error budget `(3 + (3 / 2) * ε + (1 / 2) * ε ^ 2) * ε`. -/
noncomputable def coherentOAAError (ε : ℝ) : ℝ := (3 + (3 / 2) * ε + (1 / 2) * ε ^ 2) * ε

/-- For an isometric frame and unitary oracle, the amplification word is well formed, has three
queries and four fixed gates, and evaluates to a unitary. Its compression is the cubic
expression `3 • A - 4 • (A * Aᴴ * A)` in the original compressed block. -/
theorem coherent_oaa_word_correct {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    WellFormedAdjointCircuit (coherentOAAWord R) ∧ adjointQueryCount (coherentOAAWord R) = 3 ∧
      adjointGateCount (coherentOAAWord R) = 4 ∧
      coherentOAAOperator U R ∈ Matrix.unitaryGroup H ℂ ∧
      (let A := compress R U R
       compress R (coherentOAAOperator U R) R = (3:ℂ)•A-(4:ℂ)•(A*Aᴴ*A)) := by
  have hP : IsOrthogonalProjector (rangeProjector R) := rangeProjector_isOrthogonalProjector hR
  have hb : IsPhase (-Complex.I) := by norm_num [IsPhase]
  have hzs : ∀ z ∈ cubicPhases, IsPhase z := by simp [cubicPhases, IsPhase]
  have hPUE : ProjectedUnitaryEncoding (compress R U R) U R R := ⟨hU, hR, hR, rfl⟩
  have hcubic := cubic_projectedEncoding hPUE
  have hwf : WellFormedAdjointCircuit (coherentOAAWord R) :=
    compileQSVT_wellFormed hP hP hb cubicPhases hzs
  refine ⟨hwf, ?_, ?_, hwf.evaluate_unitary hU, ?_⟩
  · simp [coherentOAAWord, queryCount_compileQSVT, cubicPhases]
  · simp [coherentOAAWord, gateCount_compileQSVT, cubicPhases]
  · have hev : coherentOAAOperator U R =
        phasedAlternating U (rangeProjector R) (rangeProjector R) (-Complex.I) cubicPhases :=
      evaluate_compileQSVT U _ _ _ _
    show compress R (coherentOAAOperator U R) R =
      (3:ℂ) • compress R U R - (4:ℂ) • (compress R U R * (compress R U R)ᴴ * compress R U R)
    rw [hev]
    exact hcubic.encoded

/-- For a scale-two block encoding of a unitary, `coherentOAAError ε` is nonnegative and bounds
the amplified compression error. -/
theorem coherent_oaa_compressed_error {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (V : Matrix I I ℂ) (U : Matrix H H ℂ) (R : Matrix H I ℂ) (ε : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V U R R 2 ε) :
    0 ≤ coherentOAAError ε ∧ ‖compress R (coherentOAAOperator U R) R - V‖ ≤ coherentOAAError ε := by
  have hR : IsIsometry R := h.right_isometry
  have hcubic : compress R (coherentOAAOperator U R) R =
      (3:ℂ) • compress R U R - (4:ℂ) • (compress R U R * (compress R U R)ᴴ * compress R U R) :=
    (coherent_oaa_word_correct U R hR h.unitary).2.2.2.2
  set A := compress R U R with hAdef
  set X := (2 : ℝ) • A with hXdef
  have hε : ‖X - V‖ ≤ ε := by
    have he : (2 : ℝ) • A - V = -(V - (2 : ℝ) • A) := by abel
    calc ‖X - V‖ = ‖(2 : ℝ) • A - V‖ := by rw [hXdef]
      _ = ‖V - (2 : ℝ) • A‖ := by rw [he, norm_neg]
      _ ≤ ε := h.error_le
  have hcast : (2 : ℝ) • A = ((2 : ℝ) : ℂ) • A := real_smul_matrix_eq 2 A
  have hA : A = ((1 / 2 : ℝ) : ℂ) • X := by
    rw [hXdef, hcast, smul_smul, show ((1 / 2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) = 1 by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_one, Complex.ofReal_inj]; norm_num,
      one_smul]
  have hstar : star (((1 / 2 : ℝ) : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hcX : compress R (coherentOAAOperator U R) R =
      ((3 / 2 : ℝ) : ℂ) • X - ((1 / 2 : ℝ) : ℂ) • (X * Xᴴ * X) := by
    rw [hcubic, hA, Matrix.conjTranspose_smul, hstar]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (3 : ℂ) * ((1 / 2 : ℝ) : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_cast; norm_num,
      show (4 : ℂ) * (((1 / 2 : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ))) =
        ((1 / 2 : ℝ) : ℂ) by norm_cast; norm_num]
  have hbound := l2_norm_scaled_cubic_sub_unitary_le hV hε ((3 / 2 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ)
  have ha : ‖((3 / 2 : ℝ) : ℂ)‖ = 3 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  have hb2 : ‖((1 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  have hab : ‖((3 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) - 1‖ = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
      show (3 / 2 - 1 / 2 - 1 : ℝ) = 0 by norm_num, Complex.ofReal_zero, norm_zero]
  refine ⟨?_, ?_⟩
  · have hε0 : 0 ≤ ε := h.error_nonneg
    unfold coherentOAAError
    positivity
  · calc ‖compress R (coherentOAAOperator U R) R - V‖
        = ‖((3 / 2 : ℝ) : ℂ) • X - ((1 / 2 : ℝ) : ℂ) • (X * Xᴴ * X) - V‖ := by rw [hcX]
      _ ≤ (‖((3 / 2 : ℝ) : ℂ)‖ + ‖((1 / 2 : ℝ) : ℂ)‖ * (3 + 3 * ε + ε ^ 2)) * ε +
          ‖((3 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) - 1‖ := hbound
      _ = coherentOAAError ε := by
        rw [ha, hb2, hab, add_zero, coherentOAAError]
        ring

/-- For a scale-two block encoding of a unitary, the amplified output differs from the ideal
framed output by at most `sqrt (2 * coherentOAAError ε)` times the input norm. -/
theorem coherent_oaa_clean_workspace_error {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (V : Matrix I I ℂ) (U : Matrix H H ℂ) (R : Matrix H I ℂ) (ε : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V U R R 2 ε) :
    ∀ ψ : QState I, ‖toEuclidean_fromVec ((coherentOAAOperator U R)*ᵥ(R*ᵥψ)-R*ᵥ(V*ᵥψ))‖ ≤
      Real.sqrt (2*coherentOAAError ε)*‖toEuclidean_fromVec ψ‖ := by
  intro ψ
  have hR : IsIsometry R := h.right_isometry
  have hW : coherentOAAOperator U R ∈ Matrix.unitaryGroup H ℂ :=
    (coherent_oaa_word_correct U R hR h.unitary).2.2.2.1
  obtain ⟨heta, herr⟩ := coherent_oaa_compressed_error V U R ε hV h
  have hc : BlockEncoding V (coherentOAAOperator U R) R R 1 (coherentOAAError ε) := by
    refine ⟨hW, hR, hR, by norm_num, heta, ?_⟩
    simpa only [one_smul, norm_sub_rev] using herr
  have hb := shared_frame_defect V (coherentOAAOperator U R) R (coherentOAAError ε) hV hc
  simpa only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec] using
    (l2_norm_mulVec_fromVec_le (coherentOAAOperator U R * R - R * V) ψ).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- The unsuccessful branch norm is at most `sqrt (2 * coherentOAAError ε)` times the input
norm. If the error budget is below one, every normalized input has successful branch mass at
least `(1 - coherentOAAError ε) ^ 2`. -/
theorem coherent_oaa_leakage_and_success {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (V : Matrix I I ℂ) (U : Matrix H H ℂ) (R : Matrix H I ℂ) (ε : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V U R R 2 ε) :
    (∀ ψ : QState I, ‖toEuclidean_fromVec (ProjectiveBranch (rangeProjector R) false
        ((coherentOAAOperator U R)*ᵥ(R*ᵥψ)))‖ ≤
      Real.sqrt (2*coherentOAAError ε)*‖toEuclidean_fromVec ψ‖) ∧
    (coherentOAAError ε < 1 → ∀ ψ : QState I, Normalized ψ →
      (1-coherentOAAError ε)^2 ≤ ProjectiveBranchMass (rangeProjector R) true
        ((coherentOAAOperator U R)*ᵥ(R*ᵥψ))) := by
  have hR : IsIsometry R := h.right_isometry
  have hP : IsOrthogonalProjector (rangeProjector R) := rangeProjector_isOrthogonalProjector hR
  set W := coherentOAAOperator U R with hWdef
  have h6 := coherent_oaa_clean_workspace_error V U R ε hV h
  have herr := (coherent_oaa_compressed_error V U R ε hV h).2
  have hRR : Rᴴ * R = 1 := hR
  refine ⟨?_, ?_⟩
  · intro ψ
    have hkill : (1 - rangeProjector R) *ᵥ (R *ᵥ (V *ᵥ ψ)) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      have hfix : (rangeProjector R) *ᵥ (R *ᵥ (V *ᵥ ψ)) = R *ᵥ (V *ᵥ ψ) := by
        show (R * Rᴴ) *ᵥ (R *ᵥ (V *ᵥ ψ)) = R *ᵥ (V *ᵥ ψ)
        rw [← Matrix.mulVec_mulVec (R *ᵥ (V *ᵥ ψ)) R Rᴴ,
          Matrix.mulVec_mulVec (V *ᵥ ψ) Rᴴ R, hRR, Matrix.one_mulVec]
      rw [hfix, sub_self]
    have hbranch : ProjectiveBranch (rangeProjector R) false (W *ᵥ (R *ᵥ ψ)) =
        (1 - rangeProjector R) *ᵥ (W *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ)) := by
      show (1 - rangeProjector R) *ᵥ (W *ᵥ (R *ᵥ ψ)) = _
      rw [Matrix.mulVec_sub, hkill, sub_zero]
    calc ‖toEuclidean_fromVec (ProjectiveBranch (rangeProjector R) false (W *ᵥ (R *ᵥ ψ)))‖
        = ‖toEuclidean_fromVec ((1 - rangeProjector R) *ᵥ
            (W *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ)))‖ := by rw [hbranch]
      _ ≤ ‖1 - rangeProjector R‖ *
          ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ))‖ :=
        norm_toEuclidean_mulVec_le _ _
      _ ≤ 1 * ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ))‖ :=
        mul_le_mul_of_nonneg_right
          (orthogonalProjector_spectralNorm_le_one (isOrthogonalProjector_compl hP))
          (norm_nonneg _)
      _ = ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ))‖ := one_mul _
      _ ≤ Real.sqrt (2 * coherentOAAError ε) * ‖toEuclidean_fromVec ψ‖ := h6 ψ
  · intro heta1 ψ hψ
    have hact : (rangeProjector R) *ᵥ (W *ᵥ (R *ᵥ ψ)) = R *ᵥ ((compress R W R) *ᵥ ψ) := by
      show (R * Rᴴ) *ᵥ (W *ᵥ (R *ᵥ ψ)) = R *ᵥ ((Rᴴ * W * R) *ᵥ ψ)
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hmass : ProjectiveBranchMass (rangeProjector R) true (W *ᵥ (R *ᵥ ψ)) =
        ‖toEuclidean_fromVec ((compress R W R) *ᵥ ψ)‖ ^ 2 := by
      show MeasureProb (ApplyGate (rangeProjector R) (W *ᵥ (R *ᵥ ψ))) Finset.univ = _
      rw [measureProb_univ_eq_norm_sq]
      show ‖toEuclidean_fromVec ((rangeProjector R) *ᵥ (W *ᵥ (R *ᵥ ψ)))‖ ^ 2 = _
      rw [hact, norm_toEuclidean_mulVec_of_isometry hR]
    have hVψ : ‖toEuclidean_fromVec (V *ᵥ ψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
      norm_toEuclidean_mulVec_of_unitary hV ψ
    have hdiff : ‖toEuclidean_fromVec ((compress R W R - V) *ᵥ ψ)‖ ≤
        coherentOAAError ε * ‖toEuclidean_fromVec ψ‖ :=
      (norm_toEuclidean_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right herr (norm_nonneg _))
    have hVe : toEuclidean_fromVec (V *ᵥ ψ) =
        toEuclidean_fromVec ((compress R W R) *ᵥ ψ) -
          toEuclidean_fromVec ((compress R W R - V) *ᵥ ψ) := by
      have hvv : (V *ᵥ ψ) = (compress R W R) *ᵥ ψ - (compress R W R - V) *ᵥ ψ := by
        rw [Matrix.sub_mulVec]
        abel
      rw [hvv, toEuclidean_fromVec_sub]
    have hnsl : ‖toEuclidean_fromVec (V *ᵥ ψ)‖ -
        ‖toEuclidean_fromVec ((compress R W R - V) *ᵥ ψ)‖ ≤
        ‖toEuclidean_fromVec ((compress R W R) *ᵥ ψ)‖ := by
      have hle := norm_sub_le (toEuclidean_fromVec ((compress R W R) *ᵥ ψ))
        (toEuclidean_fromVec ((compress R W R - V) *ᵥ ψ))
      rw [hVe]
      linarith [norm_nonneg (toEuclidean_fromVec ((compress R W R - V) *ᵥ ψ))]
    have hψnorm : ‖toEuclidean_fromVec ψ‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
    have hlb : 1 - coherentOAAError ε ≤ ‖toEuclidean_fromVec ((compress R W R) *ᵥ ψ)‖ := by
      rw [hVψ, hψnorm] at hnsl
      have hdiff1 : ‖toEuclidean_fromVec ((compress R W R - V) *ᵥ ψ)‖ ≤
          coherentOAAError ε := by
        have hle := hdiff
        rw [hψnorm, mul_one] at hle
        exact hle
      linarith
    have hnn : 0 ≤ 1 - coherentOAAError ε := by linarith
    calc (1 - coherentOAAError ε) ^ 2 ≤ ‖toEuclidean_fromVec ((compress R W R) *ᵥ ψ)‖ ^ 2 :=
        pow_le_pow_left₀ hnn hlb 2
      _ = ProjectiveBranchMass (rangeProjector R) true (W *ᵥ (R *ᵥ ψ)) := hmass.symm

/-- After `n` amplified applications, the full framed-state error is at most `n * sqrt (2 *
coherentOAAError ε)` times the input norm. -/
theorem coherent_oaa_repeated_workspace_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (V : Matrix I I ℂ) (U : Matrix H H ℂ) (R : Matrix H I ℂ)
    (ε : ℝ) (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V U R R 2 ε) :
    ∀ (n : ℕ) (ψ : QState I),
      ‖toEuclidean_fromVec (((coherentOAAOperator U R)^n)*ᵥ(R*ᵥψ)-R*ᵥ((V^n)*ᵥψ))‖ ≤
        (n:ℝ)*Real.sqrt (2*coherentOAAError ε)*‖toEuclidean_fromVec ψ‖ := by
  have hR : IsIsometry R := h.right_isometry
  have hW : coherentOAAOperator U R ∈ Matrix.unitaryGroup H ℂ :=
    (coherent_oaa_word_correct U R hR h.unitary).2.2.2.1
  have h6 := coherent_oaa_clean_workspace_error V U R ε hV h
  set W := coherentOAAOperator U R with hWdef
  intro n
  induction n with
  | zero =>
    intro ψ
    have h0 : (W ^ 0) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ 0) *ᵥ ψ) = 0 := by
      rw [pow_zero, pow_zero, Matrix.one_mulVec, Matrix.one_mulVec, sub_self]
    rw [h0, show toEuclidean_fromVec (0 : QState H) = 0 from rfl, norm_zero]
    positivity
  | succ n ih =>
    intro ψ
    have hsplit : (W ^ (n + 1)) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ (n + 1)) *ᵥ ψ) =
        W *ᵥ ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ)) +
          (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ))) := by
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec (R *ᵥ ψ) W (W ^ n),
        ← Matrix.mulVec_mulVec ψ V (V ^ n), Matrix.mulVec_sub]
      abel
    have hVn : V ^ n ∈ Matrix.unitaryGroup I ℂ := pow_mem hV n
    have hstep := h6 ((V ^ n) *ᵥ ψ)
    rw [norm_toEuclidean_mulVec_of_unitary hVn ψ] at hstep
    calc ‖toEuclidean_fromVec ((W ^ (n + 1)) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ (n + 1)) *ᵥ ψ))‖
        = ‖toEuclidean_fromVec (W *ᵥ ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ)) +
            (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ))))‖ := by rw [hsplit]
      _ ≤ ‖toEuclidean_fromVec (W *ᵥ ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ)))‖ +
          ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ)))‖ := by
        rw [toEuclidean_fromVec_add]
        exact norm_add_le _ _
      _ = ‖toEuclidean_fromVec ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ))‖ +
          ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ)))‖ := by
        rw [norm_toEuclidean_mulVec_of_unitary hW]
      _ ≤ (n : ℝ) * Real.sqrt (2 * coherentOAAError ε) * ‖toEuclidean_fromVec ψ‖ +
          Real.sqrt (2 * coherentOAAError ε) * ‖toEuclidean_fromVec ψ‖ :=
        add_le_add (ih ψ) hstep
      _ = ((n + 1 : ℕ) : ℝ) * Real.sqrt (2 * coherentOAAError ε) * ‖toEuclidean_fromVec ψ‖ := by
        push_cast
        ring

/-- Substituting a well-formed body into the amplification word realizes its amplification
operator and preserves well-formedness. The expanded word has three times the body query
count and `4 + 3 * adjointGateCount body` fixed gates. -/
theorem coherent_oaa_expanded_subroutine {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (O : Matrix H H ℂ) (body : List (AdjointStep H)) (R : Matrix H I ℂ)
    (hbody : WellFormedAdjointCircuit body) (hR : IsIsometry R) :
    evaluate O (substituteAdjointCircuit body (coherentOAAWord R)) =
        coherentOAAOperator (evaluate O body) R ∧
      adjointQueryCount (substituteAdjointCircuit body (coherentOAAWord R)) =
        3 * adjointQueryCount body ∧
      adjointGateCount (substituteAdjointCircuit body (coherentOAAWord R)) =
        4 + 3 * adjointGateCount body ∧
      WellFormedAdjointCircuit (substituteAdjointCircuit body (coherentOAAWord R)) := by
  have hP : IsOrthogonalProjector (rangeProjector R) := rangeProjector_isOrthogonalProjector hR
  have hb : IsPhase (-Complex.I) := by norm_num [IsPhase]
  have hzs : ∀ z ∈ cubicPhases, IsPhase z := by simp [cubicPhases, IsPhase]
  have hwf : WellFormedAdjointCircuit (coherentOAAWord R) :=
    compileQSVT_wellFormed hP hP hb cubicPhases hzs
  have hqc : adjointQueryCount (coherentOAAWord R) = 3 := by
    simp [coherentOAAWord, queryCount_compileQSVT, cubicPhases]
  have hgc : adjointGateCount (coherentOAAWord R) = 4 := by
    simp [coherentOAAWord, gateCount_compileQSVT, cubicPhases]
  obtain ⟨he, hq, hg, hw⟩ := substitute_adjoint_evaluate_cost O body (coherentOAAWord R)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    rfl
  · rw [hq, hqc]
  · rw [hg, hqc, hgc]
  · exact hw hbody hwf

/-- Repeating the expanded amplification body `n` times uses `3 * n * adjointQueryCount body`
queries and `n * (4 + 3 * adjointGateCount body)` fixed gates. Its full framed-state error
is at most `n * sqrt (2 * coherentOAAError ε)` times the input norm. -/
theorem coherent_oaa_expanded_repeat_error_and_cost {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (body : List (AdjointStep H))
    (V : Matrix I I ℂ) (R : Matrix H I ℂ) (ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hbody : WellFormedAdjointCircuit body)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V (evaluate O body) R R 2 ε) :
    ∀ (n : ℕ) (ψ : QState I),
      let cs := repeatAdjointWord (substituteAdjointCircuit body (coherentOAAWord R)) n
      adjointQueryCount cs = 3 * n * adjointQueryCount body ∧
        adjointGateCount cs = n * (4 + 3 * adjointGateCount body) ∧
        ‖toEuclidean_fromVec ((evaluate O cs)*ᵥ(R*ᵥψ)-R*ᵥ((V^n)*ᵥψ))‖ ≤
          (n:ℝ)*Real.sqrt (2*coherentOAAError ε)*‖toEuclidean_fromVec ψ‖ := by
  intro n ψ
  have hU : evaluate O body ∈ Matrix.unitaryGroup H ℂ := hbody.evaluate_unitary hO
  obtain ⟨he, hq, hg, hw⟩ := coherent_oaa_expanded_subroutine O body R hbody h.right_isometry
  obtain ⟨re, rq, rg, rwf⟩ :=
    repeat_adjoint_word_semantics_cost O (substituteAdjointCircuit body (coherentOAAWord R)) n
  have h8 := coherent_oaa_repeated_workspace_error V (evaluate O body) R ε hV h
  show adjointQueryCount (repeatAdjointWord (substituteAdjointCircuit body (coherentOAAWord R)) n) =
      3 * n * adjointQueryCount body ∧
    adjointGateCount (repeatAdjointWord (substituteAdjointCircuit body (coherentOAAWord R)) n) =
      n * (4 + 3 * adjointGateCount body) ∧
    ‖toEuclidean_fromVec ((evaluate O (repeatAdjointWord (substituteAdjointCircuit body
        (coherentOAAWord R)) n))*ᵥ(R*ᵥψ)-R*ᵥ((V^n)*ᵥψ))‖ ≤
      (n:ℝ)*Real.sqrt (2*coherentOAAError ε)*‖toEuclidean_fromVec ψ‖
  refine ⟨?_, ?_, ?_⟩
  · rw [rq, hq]
    ring
  · rw [rg, hg]
  · rw [re, he]
    exact h8 n ψ

end Qatlib.Concepts.CoherentSim.CoherentOAA
