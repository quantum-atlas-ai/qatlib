/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.QueryCostBridge
import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Mathlib.Analysis.Matrix.Order

/-!
# Sample encodings from separate matrix oracles

This module constructs exact block encodings of `L + s • H` from separate encodings of `L` and
`H`, for nonnegative `s`. It supplies the normalized spectral bounds and coherent sample
circuits used in the second-order algorithms of [WangEtAl2026].

## Main statements

* `separate_oracles_sample_counted`: gives the sample encoding and its explicit circuit costs.
* `separate_oracles_max_condition_spectrum`: bounds the normalized spectrum using the larger of
  the two condition estimates.
* `coherentSeparateSampleWord_evaluate`: implements the selected family of sample unitaries.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

/-- The two LCU coefficients, equal to one on `false` and `(s : ℂ)` on `true`. -/
def separateSampleCoefficients (s : ℝ) : Bool → ℂ :=
  fun b => if b then (s : ℂ) else 1

/-- The branch normalization scales, equal to `βL` on `false` and `βH` on `true`. -/
def separateSampleScales (βL βH : ℝ) : Bool → ℝ :=
  fun b => if b then βH else βL

/-- The Boolean-indexed oracle family selecting `UL` on `false` and `UH` on `true`. -/
def separateOraclePair (UL UH : Matrix W W ℂ) : Bool → Matrix W W ℂ :=
  fun b => if b then UH else UL

/-- The coefficient LCU matrix for the separate oracle pair, using the scaled coefficients for
the sample `L + s • H`. -/
def separateSampleUnitary (UL UH : Matrix W W ℂ) (βL βH s : ℝ) :
    Matrix (Bool × W) (Bool × W) ℂ :=
  coefficientLCUUnitary
    (scaledLCUCoefficients (separateSampleCoefficients s) (separateSampleScales βL βH))
    (separateOraclePair UL UH) false

/-- For positive branch scales and nonnegative `s`, the scaled coefficient mass is `βL + s *
βH`. -/
theorem separate_sample_mass (βL βH s : ℝ)
    (hL : 0 < βL) (hH : 0 < βH) (hs : 0 ≤ s) :
    coefficientMass
      (scaledLCUCoefficients (separateSampleCoefficients s) (separateSampleScales βL βH)) =
      βL + s * βH := by
  rw [(scaled_lcu_coefficient_mass (separateSampleCoefficients s)
    (separateSampleScales βL βH) (by intro b; cases b <;> assumption)).1]
  simp [separateSampleCoefficients, separateSampleScales,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, add_comm]

/-- Exact separate block encodings of `L` and `H` give an exact encoding of `L + (s : ℂ) • H`
with normalization `βL + s * βH` for `s ≥ 0`. -/
theorem separate_oracles_sample_blockEncoding
    (L H : Matrix I I ℂ) (UL UH : Matrix W W ℂ) (F : Matrix W I ℂ)
    (βL βH s : ℝ) (hs : 0 ≤ s)
    (hL : BlockEncoding L UL F F βL 0) (hH : BlockEncoding H UH F F βH 0) :
    BlockEncoding (L + (s : ℂ) • H) (separateSampleUnitary UL UH βL βH s)
      (tagFrame false F) (tagFrame false F) (βL + s * βH) 0 := by
  have hmass : 0 < coefficientMass
      (scaledLCUCoefficients (separateSampleCoefficients s) (separateSampleScales βL βH)) := by
    rw [separate_sample_mass βL βH s hL.normalization_pos hH.normalization_pos hs]
    exact add_pos_of_pos_of_nonneg hL.normalization_pos
      (mul_nonneg hs hH.normalization_pos.le)
  have hpair : ∀ b : Bool, BlockEncoding (if b then H else L)
      (separateOraclePair UL UH b) F F (separateSampleScales βL βH b) 0 := by
    intro b
    cases b
    · exact hL
    · exact hH
  have hh := scaled_approximate_lcu_encoding false (fun b : Bool => if b then H else L)
    (separateOraclePair UL UH) F F (separateSampleCoefficients s)
    (separateSampleScales βL βH) (fun _ => 0) hpair hmass
  simpa [Fintype.sum_bool, separateSampleCoefficients, separateSampleScales,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, separateSampleUnitary, add_comm] using hh

/-- An exact block encoding with normalization `β` is a projected unitary encoding of `β⁻¹ • A`. -/
theorem exact_blockEncoding_normalized {A : Matrix I I ℂ} {U : Matrix W W ℂ}
    {F : Matrix W I ℂ} {β : ℝ} (h : BlockEncoding A U F F β 0) :
    ProjectedUnitaryEncoding (β⁻¹ • A) U F F := by
  have he : A = β • compress F U F := by
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h.error_le)
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, ?_⟩
  rw [he, smul_smul, inv_mul_cancel₀ h.normalization_pos.ne', one_smul]

/-- The separate sample unitary is a projected unitary encoding of the normalized sample `(βL +
s * βH)⁻¹ • (L + (s : ℂ) • H)`. -/
theorem separate_oracles_sample_projectedEncoding
    (L H : Matrix I I ℂ) (UL UH : Matrix W W ℂ) (F : Matrix W I ℂ)
    (βL βH s : ℝ) (hs : 0 ≤ s)
    (hL : BlockEncoding L UL F F βL 0) (hH : BlockEncoding H UH F F βH 0) :
    ProjectedUnitaryEncoding ((βL + s * βH)⁻¹ • (L + (s : ℂ) • H))
      (separateSampleUnitary UL UH βL βH s) (tagFrame false F) (tagFrame false F) :=
  exact_blockEncoding_normalized (separate_oracles_sample_blockEncoding
    L H UL UH F βL βH s hs hL hH)

/-- The prepared circuit word implementing a sample LCU using the two controlled matrix oracles
and coefficient preparation gates. -/
def separateSampleWord (βL βH s : ℝ) : List (PreparedStep (Bool × W)) :=
  let d := scaledLCUCoefficients (separateSampleCoefficients s) (separateSampleScales βL βH)
  [.gate (prepareRegister (I := W) (coefficientPrepare d false))ᴴ,
   .gate (coefficientLabelPhase d), .dataForward, .gate controlFlip,
   .prepareForward, .gate controlFlip,
   .gate (prepareRegister (coefficientPrepare d false))]

/-- The separate sample word evaluates against the controlled `H` and `L` oracles to
`separateSampleUnitary`. -/
theorem separateSampleWord_evaluate (UL UH : Matrix W W ℂ) (βL βH s : ℝ) :
    evaluatePrepared (controlOracle UH) (controlOracle UL) (separateSampleWord βL βH s) =
      separateSampleUnitary UL UH βL βH s := by
  let d := scaledLCUCoefficients (separateSampleCoefficients s) (separateSampleScales βL βH)
  have hphase : coefficientLabelPhase d * select (separateOraclePair UL UH) =
      select (phaseAbsorbed d (separateOraclePair UL UH)) := by
    rw [coefficientLabelPhase, parallel_select_mul]
    congr 1
    funext b
    simp [phaseAbsorbed]
  have hselect : controlOracle UH * controlFlip * controlOracle UL * controlFlip =
      select (separateOraclePair UL UH) := by
    calc
      _ = controlOracle UH * (controlFlip * controlOracle UL * controlFlip) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        simp only [controlOracle]
        rw [controlFlip_select, parallel_select_mul]
        congr 1
        funext b
        cases b <;> simp [separateOraclePair]
  change (prepareRegister (coefficientPrepare d false))ᴴ *
    (coefficientLabelPhase d * (controlOracle UH * (controlFlip *
      (controlOracle UL * (controlFlip * (prepareRegister (coefficientPrepare d false) * 1)))))) = _
  simp only [Matrix.mul_one]
  rw [← Matrix.mul_assoc (controlOracle UH), ← Matrix.mul_assoc
    (controlOracle UH * controlFlip), ← Matrix.mul_assoc
    (controlOracle UH * controlFlip * controlOracle UL), hselect,
    ← Matrix.mul_assoc (coefficientLabelPhase d), hphase]
  exact (Matrix.mul_assoc _ _ _).symm

omit [Fintype W] in

/-- The separate sample word uses one data query, one input query, and five fixed gates. -/
theorem separateSampleWord_cost (βL βH s : ℝ) :
    preparedDataQueries (separateSampleWord (W := W) βL βH s) = 1 ∧
    preparedInputQueries (separateSampleWord (W := W) βL βH s) = 1 ∧
    preparedFixedGates (separateSampleWord (W := W) βL βH s) = 5 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Positive branch normalizations and a nonnegative sample parameter make the separate sample
circuit valid. -/
theorem separateSampleWord_valid (βL βH s : ℝ)
    (hL : 0 < βL) (hH : 0 < βH) (hs : 0 ≤ s) :
    PreparedCircuitValid (separateSampleWord (W := W) βL βH s) := by
  let d := scaledLCUCoefficients (separateSampleCoefficients s) (separateSampleScales βL βH)
  have hmass : 0 < coefficientMass d := by
    rw [separate_sample_mass βL βH s hL hH hs]
    exact add_pos_of_pos_of_nonneg hL (mul_nonneg hs hH.le)
  have hp := prepareRegister_unitary (I := W) (coefficientPrepare_unitary d false hmass)
  intro c hc
  simp only [separateSampleWord, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact adjoint_unitary hp
  · exact coefficientLabelPhase_unitary d
  · trivial
  · exact controlFlip_unitary
  · trivial
  · exact controlFlip_unitary
  · exact hp

omit [Fintype I] in

/-- A positive lower spectral bound `μ` and the condition estimate `β / μ ≤ κ` imply the lower
spectral bound `β / κ` when `κ > 0`. -/
theorem lower_bound_of_condition_upper
    (A : Matrix I I ℂ) (β μ κ : ℝ) (hμ : 0 < μ) (hκ : 0 < κ)
    (hcondition : β / μ ≤ κ) (hlower : (A - μ • (1 : Matrix I I ℂ)).PosSemidef) :
    (A - (β / κ) • (1 : Matrix I I ℂ)).PosSemidef := by
  have hb : β / κ ≤ μ := (div_le_iff₀ hκ).mpr (by
    have hh := (div_le_iff₀ hμ).mp hcondition
    nlinarith)
  have hadd := hlower.add ((Matrix.PosSemidef.one (n := I) (R := ℂ)).smul
    (sub_nonneg.mpr hb))
  convert hadd using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, Complex.ofReal_sub]
  ring

omit [Fintype I] in

/-- Lower bounds `βL / κ` and `βH / κ` for the two matrices imply the lower bound `κ⁻¹` for
their normalized nonnegative sample combination. -/
theorem normalized_separate_sample_lower
    (L H : Matrix I I ℂ) (βL βH s κ : ℝ)
    (hβL : 0 < βL) (hβH : 0 < βH) (hs : 0 ≤ s)
    (hL : (L - (βL / κ) • (1 : Matrix I I ℂ)).PosSemidef)
    (hH : (H - (βH / κ) • (1 : Matrix I I ℂ)).PosSemidef) :
    ((βL + s * βH)⁻¹ • (L + (s : ℂ) • H) -
      κ⁻¹ • (1 : Matrix I I ℂ)).PosSemidef := by
  have hβ : 0 < βL + s * βH :=
    add_pos_of_pos_of_nonneg hβL (mul_nonneg hs hβH.le)
  have hsum : (L + (s : ℂ) • H -
      ((βL + s * βH) / κ) • (1 : Matrix I I ℂ)).PosSemidef := by
    convert hL.add (hH.smul hs) using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Complex.real_smul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul]
    ring
  have hnorm := hsum.smul (inv_nonneg.mpr hβ.le)
  have hscale : (βL + s * βH)⁻¹ * ((βL + s * βH) / κ) = κ⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
  rwa [smul_sub, smul_smul, hscale] at hnorm

/-- If `A - δ • 1` is positive semidefinite, every ordered eigenvalue of the Hermitian matrix
`A` is at least `δ`. -/
theorem orderedHermitianValues_lower_of_posSemidef
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (δ : ℝ)
    (hlower : (A - δ • (1 : Matrix I I ℂ)).PosSemidef)
    (i : Fin (Fintype.card I)) : δ ≤ orderedHermitianValues hA i := by
  let v := orderedHermitianBasis hA i
  have hv : star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v = (1 : ℂ) := by
    rw [dotProduct_comm]
    change inner ℂ v v = 1
    rw [inner_self_eq_norm_sq_to_K, (orderedHermitianBasis hA).norm_eq_one]
    norm_num
  have heig : A *ᵥ WithLp.ofLp v =
      (orderedHermitianValues hA i : ℂ) • WithLp.ofLp v := by
    exact congrArg WithLp.ofLp (orderedHermitianBasis_action hA i)
  have hp := hlower.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, hv] at hp
  have hr := Complex.re_le_re hp
  simpa only [smul_eq_mul, mul_one, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_one, mul_one, Complex.sub_re, Complex.ofReal_re, Complex.zero_re,
    sub_nonneg] using hr

/-- Under the exact encoding, positive lower-bound, and condition-estimate hypotheses, every
ordered eigenvalue of the Hermitian normalized sample lies in `[κ⁻¹, 1]`. -/
theorem separate_oracles_normalized_spectrum
    (L H : Matrix I I ℂ)
    (UL UH : Matrix W W ℂ) (F : Matrix W I ℂ) (βL βH s μL μH κ : ℝ)
    (hs : 0 ≤ s) (hμL : 0 < μL) (hμH : 0 < μH) (hκ : 0 < κ)
    (hκL : βL / μL ≤ κ) (hκH : βH / μH ≤ κ)
    (hLlow : (L - μL • (1 : Matrix I I ℂ)).PosSemidef)
    (hHlow : (H - μH • (1 : Matrix I I ℂ)).PosSemidef)
    (hL : BlockEncoding L UL F F βL 0) (hH : BlockEncoding H UH F F βH 0)
    (hA : ((βL + s * βH)⁻¹ • (L + (s : ℂ) • H)).IsHermitian)
    (i : Fin (Fintype.card I)) :
    orderedHermitianValues hA i ∈ Set.Icc κ⁻¹ 1 := by
  have hlower := normalized_separate_sample_lower L H βL βH s κ
    hL.normalization_pos hH.normalization_pos hs
    (lower_bound_of_condition_upper L βL μL κ hμL hκ hκL hLlow)
    (lower_bound_of_condition_upper H βH μH κ hμH hκ hκH hHlow)
  have hproj := separate_oracles_sample_projectedEncoding L H UL UH F βL βH s hs hL hH
  exact ⟨orderedHermitianValues_lower_of_posSemidef _ hA _ hlower i,
    (hermitian_encoding_spectrum_interval _ hA _ _ hproj i).2⟩

/-- A projected unitary encoding of `β⁻¹ • A` gives an exact block encoding of `A` with positive
normalization `β`. -/
theorem normalized_projected_to_blockEncoding
    (A : Matrix I I ℂ) (U : Matrix W W ℂ) (F : Matrix W I ℂ) (β : ℝ)
    (hβ : 0 < β) (h : ProjectedUnitaryEncoding (β⁻¹ • A) U F F) :
    BlockEncoding A U F F β 0 := by
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, hβ, le_rfl, ?_⟩
  rw [h.encoded, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul, sub_self, norm_zero]

omit [Fintype I] [DecidableEq I] in

/-- A real-normalized real linear combination of the Hermitian matrices `L` and `H` is
Hermitian. -/
theorem normalized_separate_sample_isHermitian
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (βL βH s : ℝ) :
    ((βL + s * βH)⁻¹ • (L + (s : ℂ) • H)).IsHermitian := by
  exact (hL.add (hH.smul (by simp [IsSelfAdjoint]))).smul (by simp [IsSelfAdjoint])

/-- Every ordered eigenvalue of the normalized sample lies between the reciprocal of `max (βL /
μL) (βH / μH)` and one under the separate exact encoding and positive spectral lower-bound
hypotheses. -/
theorem separate_oracles_max_condition_spectrum
    (L H : Matrix I I ℂ) (hLH : L.IsHermitian) (hHH : H.IsHermitian)
    (UL UH : Matrix W W ℂ) (F : Matrix W I ℂ) (βL βH s μL μH : ℝ)
    (hs : 0 ≤ s) (hμL : 0 < μL) (hμH : 0 < μH)
    (hLlow : (L - μL • (1 : Matrix I I ℂ)).PosSemidef)
    (hHlow : (H - μH • (1 : Matrix I I ℂ)).PosSemidef)
    (hL : BlockEncoding L UL F F βL 0) (hH : BlockEncoding H UH F F βH 0)
    (i : Fin (Fintype.card I)) :
    orderedHermitianValues (normalized_separate_sample_isHermitian L H hLH hHH βL βH s) i ∈
      Set.Icc (max (βL / μL) (βH / μH))⁻¹ 1 := by
  exact separate_oracles_normalized_spectrum L H UL UH F βL βH s μL μH _ hs hμL hμH
    ((div_pos hL.normalization_pos hμL).trans_le (le_max_left _ _))
    (le_max_left _ _) (le_max_right _ _) hLlow hHlow hL hH _ i

/-- Separate exact block encodings produce a valid sample circuit with unitary controlled
oracles and exact sample encoding. It uses one query to each oracle and five fixed gates. -/
theorem separate_oracles_sample_counted
    (L H : Matrix I I ℂ) (UL UH : Matrix W W ℂ) (F : Matrix W I ℂ)
    (βL βH s : ℝ) (hs : 0 ≤ s)
    (hL : BlockEncoding L UL F F βL 0) (hH : BlockEncoding H UH F F βH 0) :
    PreparedCircuitValid (separateSampleWord (W := W) βL βH s) ∧
    controlOracle UH ∈ Matrix.unitaryGroup (Bool × W) ℂ ∧
    controlOracle UL ∈ Matrix.unitaryGroup (Bool × W) ℂ ∧
    BlockEncoding (L + (s : ℂ) • H)
      (evaluatePrepared (controlOracle UH) (controlOracle UL) (separateSampleWord βL βH s))
      (tagFrame false F) (tagFrame false F) (βL + s * βH) 0 ∧
    preparedDataQueries (separateSampleWord (W := W) βL βH s) = 1 ∧
    preparedInputQueries (separateSampleWord (W := W) βL βH s) = 1 ∧
    preparedFixedGates (separateSampleWord (W := W) βL βH s) = 5 := by
  refine ⟨separateSampleWord_valid βL βH s hL.normalization_pos hH.normalization_pos hs,
    controlOracle_unitary hH.unitary, controlOracle_unitary hL.unitary, ?_,
    separateSampleWord_cost βL βH s⟩
  rw [separateSampleWord_evaluate]
  exact separate_oracles_sample_blockEncoding L H UL UH F βL βH s hs hL hH

section Coherent
variable {J : Type} [Fintype J] [DecidableEq J]

/-- The sample circuit with coefficient gates selected coherently by the label `j`, sharing the
two parallel controlled matrix oracles. -/
def coherentSeparateSampleWord (βL βH : ℝ) (s : J → ℝ) :
    List (PreparedStep (J × (Bool × W))) :=
  let d := fun j => scaledLCUCoefficients (separateSampleCoefficients (s j))
    (separateSampleScales βL βH)
  [.gate (select (fun j => (prepareRegister (I := W) (coefficientPrepare (d j) false))ᴴ)),
   .gate (select (fun j => coefficientLabelPhase (W := W) (d j))),
   .dataForward, .gate (parallelOracle (J := J) (controlFlip (H := W))),
   .prepareForward, .gate (parallelOracle (J := J) (controlFlip (H := W))),
   .gate (select (fun j => prepareRegister (I := W) (coefficientPrepare (d j) false)))]

/-- The coherent sample word evaluates to the selected family `j ↦ separateSampleUnitary UL UH
βL βH (s j)`. -/
theorem coherentSeparateSampleWord_evaluate
    (UL UH : Matrix W W ℂ) (βL βH : ℝ) (s : J → ℝ) :
    evaluatePrepared (parallelOracle (J := J) (controlOracle UH))
      (parallelOracle (J := J) (controlOracle UL)) (coherentSeparateSampleWord βL βH s) =
    select (fun j => separateSampleUnitary UL UH βL βH (s j)) := by
  simp only [coherentSeparateSampleWord, evaluatePrepared, preparedInstruction,
    Matrix.mul_one, parallelOracle, parallel_select_mul]
  congr 1
  funext j
  simpa only [separateSampleWord, evaluatePrepared, preparedInstruction, Matrix.mul_one] using
    separateSampleWord_evaluate UL UH βL βH (s j)

omit [Fintype J] [Fintype W] in

/-- The coherent sample word uses one query to each oracle and five fixed gates, independently
of the label set. -/
theorem coherentSeparateSampleWord_cost (βL βH : ℝ) (s : J → ℝ) :
    preparedDataQueries (coherentSeparateSampleWord (W := W) βL βH s) = 1 ∧
    preparedInputQueries (coherentSeparateSampleWord (W := W) βL βH s) = 1 ∧
    preparedFixedGates (coherentSeparateSampleWord (W := W) βL βH s) = 5 :=
  ⟨rfl, rfl, rfl⟩

/-- The coherent sample word is valid when both branch scales are positive and every sample
parameter is nonnegative. -/
theorem coherentSeparateSampleWord_valid (βL βH : ℝ) (s : J → ℝ)
    (hL : 0 < βL) (hH : 0 < βH) (hs : ∀ j, 0 ≤ s j) :
    PreparedCircuitValid (coherentSeparateSampleWord (W := W) βL βH s) := by
  let d := fun j => scaledLCUCoefficients (separateSampleCoefficients (s j))
    (separateSampleScales βL βH)
  have hmass (j : J) : 0 < coefficientMass (d j) := by
    rw [separate_sample_mass βL βH (s j) hL hH (hs j)]
    exact add_pos_of_pos_of_nonneg hL (mul_nonneg (hs j) hH.le)
  have hp := fun j => prepareRegister_unitary (I := W)
    (coefficientPrepare_unitary (d j) false (hmass j))
  intro c hc
  simp only [coherentSeparateSampleWord, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact select_unitary _ (fun j => adjoint_unitary (hp j))
  · exact select_unitary _ (fun j => coefficientLabelPhase_unitary (d j))
  · trivial
  · exact parallelOracle_unitary controlFlip_unitary
  · trivial
  · exact parallelOracle_unitary controlFlip_unitary
  · exact select_unitary _ hp

end Coherent

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
