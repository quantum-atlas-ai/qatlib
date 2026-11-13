/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Approximate scaled LCU and fixed-point postselection

`scaledLCUCoefficients` incorporates the normalization of each input block encoding into its
complex coefficient. `scaled_approximate_lcu_encoding` combines encodings with shared frames,
with normalization and error given by coefficient-weighted sums, as in the block-encoding
calculus of [GilyenSuLowWiebe2019].

`LCUFixedPoint.word` implements the recursive phase-shift construction of [Grover2005]. Its
failure probability is raised to `3^r`, and the decoded conditional output is preserved up to a
global phase; the module records exact query and fixed-gate counts and relative output-error
bounds.

## Main statements

* `scaled_approximate_lcu_encoding`: combine approximate block encodings with complex weights.
* `lcu_postselection_amplification`: certify recursive amplification and its costs.
* `lcu_relative_postselected_output_error`: control normalized output error up to phase.
* `scaled_lcu_fixed_point_consumer`: specialize amplification to the scaled LCU circuit.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
* [Grover, 2005][Grover2005]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Concepts.LcuPostselect.ScaledLCU

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open scoped Matrix.Norms.L2Operator

variable {J H O I : Type*} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- Rescales each complex coefficient `c j` by the real block-encoding normalization `α j`. -/
def scaledLCUCoefficients {J : Type*} [Fintype J] (c : J → ℂ) (α : J → ℝ) : J → ℂ :=
  fun j => c j * (α j : ℂ)

omit [DecidableEq J] [DecidableEq H] [DecidableEq O] [DecidableEq I] in

/-- For positive normalizations, the rescaled coefficient mass is `∑ j, ‖c j‖ * α j`, and it
vanishes exactly when every coefficient vanishes. -/
theorem scaled_lcu_coefficient_mass (c : J → ℂ) (α : J → ℝ)
    (hα : ∀ j, 0 < α j) :
    coefficientMass (scaledLCUCoefficients c α) = ∑ j, ‖c j‖ * α j ∧
      (coefficientMass (scaledLCUCoefficients c α) = 0 ↔ ∀ j, c j = 0) := by
  have hmass : coefficientMass (scaledLCUCoefficients c α) = ∑ j, ‖c j‖ * α j := by
    simp only [coefficientMass, scaledLCUCoefficients]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hα j)]
  refine ⟨hmass, ?_⟩
  constructor
  · intro h0
    rw [hmass] at h0
    intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (norm_nonneg _) (le_of_lt (hα j))).mp h0 j (Finset.mem_univ j)
    have hnorm : ‖c j‖ = 0 := by
      rcases mul_eq_zero.mp hj with h | h
      · exact h
      · exact absurd h (ne_of_gt (hα j))
    exact norm_eq_zero.mp hnorm
  · intro hc
    rw [hmass]
    exact Finset.sum_eq_zero fun j _ => by rw [hc j, norm_zero, zero_mul]

/-- Embeds the frame `L` into the label sector `j₀` of the product space. -/
def tagFrame (j₀ : J) (L : Matrix H O ℂ) : Matrix (J × H) O ℂ :=
  Matrix.of fun p i => (if p.1 = j₀ then 1 else 0) * L p.2 i

omit [Fintype J] [Fintype O] [DecidableEq O] in

/-- Expresses the tagged frame as basis-state preparation followed by `L`. -/
theorem tagFrame_eq (j₀ : J) (L : Matrix H O ℂ) :
    tagFrame j₀ L = prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀) * L := by
  ext p i
  show (if p.1 = j₀ then (1 : ℂ) else 0) * L p.2 i
      = ∑ h : H, prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀) p h * L h i
  rw [Finset.sum_eq_single p.2]
  · simp [Qatlib.Foundations.PureStateMath.Ket, prepareLift]
  · intro b _ hb
    have hne : ¬(p.2 = b) := fun h => hb h.symm
    simp [hne, prepareLift]
  · simp

/-- Tagging an isometric frame preserves its isometry property. -/
theorem tagFrame_isIsometry (j₀ : J) (L : Matrix H O ℂ) (hL : IsIsometry L) :
    IsIsometry (tagFrame j₀ L) := by
  rw [tagFrame_eq]
  exact IsIsometry.mul (prepareLift_isIsometry (I := H) (Qatlib.Foundations.PureStateMath.Ket j₀)
    (by simp [Qatlib.Foundations.PureStateMath.Ket])) hL

omit [Fintype J] [Fintype H] in

/-- Tagging the identity frame gives the encoding fiber at `j₀`. -/
theorem tagFrame_one (j₀ : J) :
    tagFrame j₀ (1 : Matrix H H ℂ) = encodingFiber (I := H) j₀ := by
  ext p i
  by_cases h : p.2 = i <;> by_cases h2 : p.1 = j₀ <;>
    simp [tagFrame, encodingFiber, h, h2, Matrix.one_apply]

/-- Factors compression between tagged frames through the basis-label preparation lifts. -/
theorem compress_tagFrame (j₀ : J) (L : Matrix H O ℂ) (M : Matrix (J × H) (J × H) ℂ)
    (R : Matrix H I ℂ) :
    compress (tagFrame j₀ L) M (tagFrame j₀ R)
      = Lᴴ * compress (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) M
          (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) * R := by
  let _ := (inferInstance : Fintype O)
  let _ := (inferInstance : DecidableEq O)
  let _ := (inferInstance : Fintype I)
  let _ := (inferInstance : DecidableEq I)
  rw [tagFrame_eq j₀ L, tagFrame_eq j₀ R, compress, compress]
  set PL : Matrix (J × H) H ℂ := prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀) with hPL
  calc (PL * L)ᴴ * M * (PL * R) = (Lᴴ * PLᴴ) * (M * (PL * R)) := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc (Lᴴ * PLᴴ) M (PL * R)]
    _ = Lᴴ * (PLᴴ * (M * (PL * R))) := by
        rw [Matrix.mul_assoc Lᴴ PLᴴ (M * (PL * R))]
    _ = Lᴴ * ((PLᴴ * M) * (PL * R)) := by
        rw [Matrix.mul_assoc PLᴴ M (PL * R)]
    _ = Lᴴ * (((PLᴴ * M) * PL) * R) := by
        rw [Matrix.mul_assoc (PLᴴ * M) PL R]
    _ = (Lᴴ * ((PLᴴ * M) * PL)) * R := by
        rw [Matrix.mul_assoc Lᴴ ((PLᴴ * M) * PL) R]

/-- Combines approximate block encodings into an encoding of `∑ j, c j • A j`, with
normalization `∑ j, ‖c j‖ * α j` and error `∑ j, ‖c j‖ * ε j` [GilyenSuLowWiebe2019]. -/
theorem scaled_approximate_lcu_encoding (j₀ : J) (A : J → Matrix O I ℂ)
    (U : J → Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) (c : J → ℂ) (α ε : J → ℝ)
    (henc : ∀ j, BlockEncoding (A j) (U j) L R (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α)) :
    BlockEncoding (∑ j, c j • A j)
      (coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀)
      (tagFrame j₀ L) (tagFrame j₀ R) (∑ j, ‖c j‖ * α j) (∑ j, ‖c j‖ * ε j) := by
  obtain ⟨j', hdj'⟩ := (coefficientMass_pos_iff (scaledLCUCoefficients c α)).mp hmass
  have hL : IsIsometry L := (henc j').left_isometry
  have hR : IsIsometry R := (henc j').right_isometry
  have hα : ∀ j, 0 < α j := fun j => (henc j).normalization_pos
  have hmasseq := (scaled_lcu_coefficient_mass c α hα).1
  set d := scaledLCUCoefficients c α with hd
  have hmass' : 0 < coefficientMass d := hmass
  have hcU : compress (tagFrame j₀ L) (coefficientLCUUnitary d U j₀) (tagFrame j₀ R)
      = ∑ j, (d j / (coefficientMass d : ℂ)) • (compress L (U j) R) := by
    rw [compress_tagFrame, coefficientLCUUnitary_compress d U j₀ hmass']
    calc Lᴴ * (∑ j, (d j / (coefficientMass d : ℂ)) • U j) * R
        = (∑ j, Lᴴ * ((d j / (coefficientMass d : ℂ)) • U j)) * R := by rw [Matrix.mul_sum]
      _ = ∑ j, Lᴴ * ((d j / (coefficientMass d : ℂ)) • U j) * R :=
          Matrix.sum_mul _ _ _
      _ = ∑ j, (d j / (coefficientMass d : ℂ)) • (Lᴴ * U j * R) := by
          exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
  have key : (∑ j, ‖c j‖ * α j) • compress (tagFrame j₀ L) (coefficientLCUUnitary d U j₀)
      (tagFrame j₀ R) = ∑ j, c j • (α j • compress L (U j) R) := by
    rw [hcU, Finset.smul_sum, ← hmasseq]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hne : (coefficientMass (scaledLCUCoefficients c α) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hmass)
    ext o i
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, hd,
      scaledLCUCoefficients]
    rw [← mul_assoc]
    field_simp
  refine ⟨coefficientLCUUnitary_unitary d U j₀ hmass (fun j => (henc j).unitary),
    tagFrame_isIsometry j₀ L hL, tagFrame_isIsometry j₀ R hR, ?_, ?_, ?_⟩
  · rw [← hmasseq]
    exact hmass
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (henc j).error_nonneg
  · have hsplit : (∑ j, c j • A j)
        - (∑ j, ‖c j‖ * α j) • compress (tagFrame j₀ L) (coefficientLCUUnitary d U j₀)
          (tagFrame j₀ R)
        = ∑ j, c j • (A j - α j • compress L (U j) R) := by
      rw [key, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_sub]
    calc ‖(∑ j, c j • A j)
          - (∑ j, ‖c j‖ * α j) • compress (tagFrame j₀ L) (coefficientLCUUnitary d U j₀)
            (tagFrame j₀ R)‖
        = ‖∑ j, c j • (A j - α j • compress L (U j) R)‖ := by rw [hsplit]
      _ ≤ ∑ j, ‖c j • (A j - α j • compress L (U j) R)‖ := norm_sum_le _ _
      _ = ∑ j, ‖(c j : ℂ)‖ * ‖A j - α j • compress L (U j) R‖ := by
          exact Finset.sum_congr rfl fun j _ => by rw [norm_smul]
      _ ≤ ∑ j, ‖c j‖ * ε j :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (henc j).error_le (norm_nonneg _)

omit [DecidableEq J] in

/-- When all coefficients vanish, orthogonal Boolean tags give an exact encoding of the zero sum
using the identity unitary. -/
theorem zero_scaled_lcu_encoding (A : J → Matrix O I ℂ) (c : J → ℂ) (L : Matrix H O ℂ)
    (R : Matrix H I ℂ) (hc : ∀ j, c j = 0) (hL : IsIsometry L) (hR : IsIsometry R) :
    BlockEncoding (∑ j, c j • A j) (1 : Matrix (Bool × H) (Bool × H) ℂ)
      (tagFrame false L) (tagFrame true R) 1 0 := by
  have hsum : (∑ j, c j • A j) = 0 := by
    exact Finset.sum_eq_zero fun j _ => by rw [hc j, zero_smul]
  have hcomp : compress (tagFrame false L) (1 : Matrix (Bool × H) (Bool × H) ℂ)
      (tagFrame true R) = 0 := by
    ext o i
    rw [compress, Matrix.mul_one]
    simp only [Matrix.mul_apply, conjTranspose_apply, tagFrame, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]
    simp
  refine ⟨(Matrix.unitaryGroup (Bool × H) ℂ).one_mem, tagFrame_isIsometry false L hL,
    tagFrame_isIsometry true R hR, by norm_num, le_rfl, ?_⟩
  rw [hsum, hcomp, smul_zero, sub_zero, norm_zero]

/-- The prepare-select-unprepare circuit for the coefficient-weighted LCU construction. -/
noncomputable def scaledLCUCircuit (d : J → ℂ) (j₀ : J) : Circuit (J × I) :=
  [Step.gate (prepareRegister (coefficientPrepare d j₀)), Step.query,
    Step.gate ((prepareRegister (coefficientPrepare d j₀))ᴴ)]

/-- The scaled LCU circuit evaluates to `coefficientLCUUnitary`, uses one oracle query and two
fixed gates, and is unitary when the coefficient mass is positive and all selected matrices
are unitary. -/
theorem scaled_lcu_run_and_cost (j₀ : J) (d : J → ℂ) (U : J → Matrix I I ℂ)
    (ψ : QState (J × I)) :
    Run (select (phaseAbsorbed d U)) (scaledLCUCircuit d j₀) ψ
      = ApplyGate (coefficientLCUUnitary d U j₀) ψ ∧
    QueryCount (scaledLCUCircuit (I := I) d j₀) = 1 ∧
    GateCount (scaledLCUCircuit (I := I) d j₀) = 2 ∧
    (0 < coefficientMass d → (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) →
      IsUnitaryCircuit (scaledLCUCircuit (I := I) d j₀)) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · show ApplyGate ((prepareRegister (coefficientPrepare d j₀))ᴴ)
      (ApplyGate (select (phaseAbsorbed d U)) (ApplyGate (prepareRegister
        (coefficientPrepare d j₀)) ψ)) = ApplyGate (coefficientLCUUnitary d U j₀) ψ
    simp only [ApplyGate, coefficientLCUUnitary]
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  · intro hα hU
    simp only [scaledLCUCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_query]
    exact ⟨prepareRegister_unitary (coefficientPrepare_unitary d j₀ hα),
      adjoint_unitary (prepareRegister_unitary (coefficientPrepare_unitary d j₀ hα)),
      isUnitaryCircuit_nil⟩

end Qatlib.Concepts.LcuPostselect.ScaledLCU

noncomputable section
namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

/-- The phase `1 / 2 + i * √3 / 2` used in fixed-point amplification. -/
def omega : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

/-- The matrix `1 + (omega - 1) • P`, which applies the phase `omega` on the range of a
projector. -/
def phase {H : Type*} [Fintype H] [DecidableEq H] (P : Matrix H H ℂ) : Matrix H H ℂ :=
  1 + (omega - 1) • P

/-- Reverses a prepared instruction by taking the adjoint of a fixed gate or swapping its
forward and backward query. -/
def inverseStep {H : Type*} : PreparedStep H → PreparedStep H
  | .gate V => .gate Vᴴ
  | .dataForward => .dataBackward
  | .dataBackward => .dataForward
  | .prepareForward => .prepareBackward
  | .prepareBackward => .prepareForward

/-- Forms the formal inverse of a prepared word by reversing its instructions and inverting each
step. -/
def inverseWord {H : Type*} (cs : List (PreparedStep H)) : List (PreparedStep H) :=
  cs.reverse.map inverseStep

/-- The recursive fixed-point amplification word, starting from `preparedTrial` and inserting
source and target phase shifts [Grover2005]. -/
def word {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    (L : Matrix H O ℂ) (j₀ : H) (cs : List (AdjointStep H)) : ℕ → List (PreparedStep H)
  | 0 => preparedTrial cs
  | r + 1 =>
      let z := word L j₀ cs r
      z ++ [.gate (phase (outerProduct (Qatlib.Foundations.PureStateMath.Ket j₀)))] ++ inverseWord z ++
        [.gate (phase (rangeProjector L))] ++ z

/-- The phase `omega` has conjugate product equal to one. -/
theorem omega_star_mul : star omega * omega = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext
  · simp [omega, Complex.mul_re]
    nlinarith
  · simp [omega, Complex.mul_im]
    ring

/-- The fixed-point phase satisfies `(omega - 1)^2 = -omega`. -/
theorem omega_sub_sq : (omega - 1) ^ 2 = -omega := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext
  · simp [omega, pow_two, Complex.mul_re]
    nlinarith
  · simp [omega, pow_two, Complex.mul_im]
    ring

/-- The phase shift of an orthogonal projector is unitary. -/
theorem phase_unitary {H : Type*} [Fintype H] [DecidableEq H]
    {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) :
    phase P ∈ Matrix.unitaryGroup H ℂ := by
  have hc : star (omega-1) + (omega-1) + star (omega-1)*(omega-1) = 0 := by
    calc
      _ = star omega * omega - 1 := by simp only [star_sub, star_one]; ring
      _ = 0 := by rw [omega_star_mul]; ring
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hid : P * P = P := hP.1
  have hstar : Pᴴ = P := hP.2
  simp only [phase, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, hstar, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hid]
  calc
    _ = 1 + (star (omega-1) + (omega-1) + star (omega-1)*(omega-1)) • P := by module
    _ = 1 := by rw [hc]; simp

/-- Evaluating an inverse word gives the conjugate transpose of the original evaluation. -/
theorem inverseWord_evaluate {H : Type*} [Fintype H] [DecidableEq H]
    (V B : Matrix H H ℂ) (cs : List (PreparedStep H)) :
    evaluatePrepared V B (inverseWord cs) = (evaluatePrepared V B cs)ᴴ := by
  induction cs with
  | nil => simp [inverseWord, evaluatePrepared]
  | cons c cs ih =>
    simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      evaluatePrepared_append, evaluatePrepared, Matrix.conjTranspose_mul]
    change evaluatePrepared V B (inverseWord cs) *
      (preparedInstruction V B (inverseStep c) * 1) =
      (evaluatePrepared V B cs)ᴴ * (preparedInstruction V B c)ᴴ
    rw [ih, Matrix.mul_one]
    cases c <;> simp [inverseStep, preparedInstruction]

/-- Formal inversion preserves validity of a prepared circuit. -/
theorem inverseWord_valid {H : Type*} [Fintype H] [DecidableEq H]
    {cs : List (PreparedStep H)} (hcs : PreparedCircuitValid cs) :
    PreparedCircuitValid (inverseWord cs) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hv := hcs d (List.mem_reverse.mp hd)
  cases d <;> simp only [inverseStep, PreparedInstructionValid] at *
  exact adjoint_unitary hv

/-- Evaluating the next amplification stage gives the current unitary, source phase, adjoint,
target phase, and current unitary in that order. -/
theorem word_evaluate_succ {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    (V B : Matrix H H ℂ) (L : Matrix H O ℂ) (j₀ : H) (cs : List (AdjointStep H)) (r : ℕ) :
    evaluatePrepared V B (word L j₀ cs (r+1)) =
      evaluatePrepared V B (word L j₀ cs r) * phase (outerProduct (Qatlib.Foundations.PureStateMath.Ket j₀)) *
      (evaluatePrepared V B (word L j₀ cs r))ᴴ * phase (rangeProjector L) *
      evaluatePrepared V B (word L j₀ cs r) := by
  simp [word, evaluatePrepared_append, evaluatePrepared, preparedInstruction,
    inverseWord_evaluate, Matrix.mul_assoc]

/-- Data-query counts add under concatenation of prepared words. -/
@[simp] theorem data_append {H : Type*} (cs ds : List (PreparedStep H)) :
    preparedDataQueries (cs++ds) = preparedDataQueries cs + preparedDataQueries ds :=
  (preparedCounts_append cs ds).1

/-- Input-preparation query counts add under concatenation of prepared words. -/
@[simp] theorem input_append {H : Type*} (cs ds : List (PreparedStep H)) :
    preparedInputQueries (cs++ds) = preparedInputQueries cs + preparedInputQueries ds :=
  (preparedCounts_append cs ds).2.1

/-- Fixed-gate counts add under concatenation of prepared words. -/
@[simp] theorem gates_append {H : Type*} (cs ds : List (PreparedStep H)) :
    preparedFixedGates (cs++ds) = preparedFixedGates cs + preparedFixedGates ds :=
  (preparedCounts_append cs ds).2.2

/-- Formal inversion preserves data-query, input-query, and fixed-gate counts. -/
theorem inverseWord_counts {H : Type*} (cs : List (PreparedStep H)) :
    preparedDataQueries (inverseWord cs) = preparedDataQueries cs ∧
    preparedInputQueries (inverseWord cs) = preparedInputQueries cs ∧
    preparedFixedGates (inverseWord cs) = preparedFixedGates cs := by
  induction cs with
  | nil => simp [inverseWord, preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | cons c cs ih =>
    have hr : inverseWord (c::cs) = inverseWord cs ++ [inverseStep c] := by
      simp [inverseWord]
    rw [hr]
    simp only [data_append, input_append, gates_append, ih.1, ih.2.1, ih.2.2]
    cases c <;> simp [inverseStep, preparedDataQueries, preparedInputQueries, preparedFixedGates]

/-- At stage `r`, amplification uses `3^r` times the base data queries, `3^r` input queries, and
`3^r` times the base fixed gates plus `3^r - 1`. -/
theorem word_counts {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    (L : Matrix H O ℂ) (j₀ : H) (cs : List (AdjointStep H)) (r : ℕ) :
    preparedDataQueries (word L j₀ cs r) = 3^r * adjointQueryCount cs ∧
    preparedInputQueries (word L j₀ cs r) = 3^r ∧
    preparedFixedGates (word L j₀ cs r) = 3^r * adjointGateCount cs + (3^r-1) := by
  induction r with
  | zero => simpa [word] using preparedTrial_counts cs
  | succ r ih =>
    simp only [word, data_append, input_append, gates_append,
      (inverseWord_counts _).1, (inverseWord_counts _).2.1, (inverseWord_counts _).2.2,
      preparedDataQueries, preparedInputQueries, preparedFixedGates, ih.1, ih.2.1, ih.2.2]
    have hp : 0 < 3^r := by positivity
    rw [pow_succ]
    constructor
    · ring
    constructor
    · ring
    · have hg : 3^r * 3 * adjointGateCount cs = 3 * (3^r * adjointGateCount cs) := by ring
      rw [hg]
      omega

/-- An isometric target frame and unitary fixed gates make every amplification stage a valid
prepared circuit. -/
theorem word_valid {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
    (L : Matrix H O ℂ) (j₀ : H) (cs : List (AdjointStep H))
    (hL : IsIsometry L) (hcs : ∀ G, AdjointStep.gate G ∈ cs → G ∈ Matrix.unitaryGroup H ℂ)
    (r : ℕ) : PreparedCircuitValid (word L j₀ cs r) := by
  induction r with
  | zero => exact preparedTrial_valid hcs
  | succ r ih =>
    intro c hc
    simp only [word, List.mem_append, List.mem_singleton] at hc
    rcases hc with (((hc|hc)|hc)|hc)|hc
    · exact ih c hc
    · subst c
      exact phase_unitary (isOrthogonalProjector_outerProduct (normalized_ket j₀))
    · exact inverseWord_valid ih c hc
    · subst c
      exact phase_unitary (rangeProjector_isOrthogonalProjector hL)
    · exact ih c hc

section Geometry
variable {H : Type*} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in

/-- Conjugating an outer product by `W` gives the outer product of the vector transformed by
`W`. -/
theorem outerProduct_conj (W : Matrix H H ℂ) (a : QState H) :
    W * outerProduct a * Wᴴ = outerProduct (W *ᵥ a) := by
  ext i j
  simp only [outerProduct, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    starRingEnd_apply, Matrix.mulVec, dotProduct]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [star_mul]
  ring

/-- Expands the action of a projector phase as the original vector plus `(omega - 1)` times its
projected component. -/
theorem phase_action (P : Matrix H H ℂ) (a : QState H) :
    phase P *ᵥ a = a + (omega-1) • (P *ᵥ a) := by
  simp [phase, Matrix.add_mulVec, Matrix.smul_mulVec]

omit [DecidableEq H] in

/-- The pure-state inner product is additive in its second argument. -/
theorem inner_add_right (a b c : QState H) :
    Qatlib.Foundations.PureStateMath.Inner a (b+c) = Qatlib.Foundations.PureStateMath.Inner a b + Qatlib.Foundations.PureStateMath.Inner a c := by
  simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct, mul_add, Finset.sum_add_distrib]

omit [DecidableEq H] in

/-- The pure-state inner product is complex-linear in its second argument. -/
theorem inner_smul_right (a b : QState H) (z : ℂ) :
    Qatlib.Foundations.PureStateMath.Inner a (z • b) = z * Qatlib.Foundations.PureStateMath.Inner a b := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The inner product of a vector with its orthogonal projection equals the corresponding
projective branch mass. -/
theorem inner_projector_mass {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (a : QState H) :
    Qatlib.Foundations.PureStateMath.Inner a (P *ᵥ a) = (ProjectiveBranchMass P true a : ℂ) := by
  have hPP : Pᴴ * P = P := by rw [show Pᴴ = P from hP.2]; exact hP.1
  have hi : Qatlib.Foundations.PureStateMath.Inner (P *ᵥ a) (P *ᵥ a) = Qatlib.Foundations.PureStateMath.Inner a (P *ᵥ a) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hPP,
      Matrix.dotProduct_mulVec]
  rw [← hi, Qatlib.Foundations.PureStateMath.inner_self, ← Complex.ofReal_sum]
  rfl

/-- One fixed-point amplification step built from `W`, its adjoint, and source and target phase
shifts. -/
def step (W P : Matrix H H ℂ) (j₀ : H) : Matrix H H ℂ :=
  W * phase (outerProduct (Qatlib.Foundations.PureStateMath.Ket j₀)) * Wᴴ * phase P * W

/-- A fixed-point step is unitary when `W` is unitary and `P` is an orthogonal projector. -/
theorem step_unitary {W P : Matrix H H ℂ} (j₀ : H)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) :
    step W P j₀ ∈ Matrix.unitaryGroup H ℂ := by
  exact (Matrix.unitaryGroup H ℂ).mul_mem
    ((Matrix.unitaryGroup H ℂ).mul_mem
      ((Matrix.unitaryGroup H ℂ).mul_mem
        ((Matrix.unitaryGroup H ℂ).mul_mem hW
          (phase_unitary (isOrthogonalProjector_outerProduct (normalized_ket j₀))))
        (adjoint_unitary hW)) (phase_unitary hP)) hW

/-- Expresses the amplified state as `omega * (1 - p)` times the initial state plus `omega - 1`
times its target projection, where `p` is the initial success mass. -/
theorem step_action {W P : Matrix H H ℂ} (j₀ : H)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) :
    let a := W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀
    let p := ProjectiveBranchMass P true a
    step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ =
      (omega * (1 - (p : ℂ))) • a + (omega-1) • (P *ᵥ a) := by
  (try dsimp only)
  let a := W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀
  let p := ProjectiveBranchMass P true a
  have hWW : W * Wᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using hW
  have hc : W * phase (outerProduct (Qatlib.Foundations.PureStateMath.Ket j₀)) * Wᴴ = phase (outerProduct a) := by
    simp only [phase, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hWW]
    rw [outerProduct_conj]
  have ha : Normalized a := normalized_applyGate hW (normalized_ket j₀)
  have hcoeff : 1 + (omega-1) * (1 + (omega-1)*(p : ℂ)) = omega*(1-(p : ℂ)) := by
    calc
      _ = omega + (omega-1)^2 * (p : ℂ) := by ring
      _ = _ := by rw [omega_sub_sq]; ring
  change (W * phase (outerProduct (Qatlib.Foundations.PureStateMath.Ket j₀)) * Wᴴ * phase P * W) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = _
  rw [hc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change phase (outerProduct a) *ᵥ (phase P *ᵥ a) = _
  rw [phase_action, phase_action, outerProduct_mulVec, inner_add_right, inner_smul_right,
    inner_self_eq_one ha, inner_projector_mass hP]
  change a + (omega-1) • (P *ᵥ a) +
    (omega-1) • ((1 + (omega-1)*(p : ℂ)) • a) = _
  rw [smul_smul]
  calc
    _ = (1 + (omega-1)*(1+(omega-1)*(p : ℂ))) • a + (omega-1) • (P *ᵥ a) := by module
    _ = _ := by rw [hcoeff]

/-- The scalar `omega * (2 - p) - 1` multiplying the successful component after one
amplification step. -/
def goodCoeff (p : ℝ) : ℂ := omega * (2 - (p : ℂ)) - 1

/-- The squared norm of `omega` is one. -/
theorem omega_norm_sq : ‖omega‖ ^ 2 = 1 := by
  rw [← Complex.normSq_eq_norm_sq]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp [omega, Complex.normSq_apply]
  nlinarith

/-- The successful-component multiplier `goodCoeff p` is nonzero for every real `p`. -/
theorem goodCoeff_ne_zero (p : ℝ) : goodCoeff p ≠ 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : Complex.normSq (goodCoeff p) = p^2 - 3*p + 3 := by
    simp [goodCoeff, omega, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring_nf
    rw [hs]
    ring
  intro hz
  rw [hz, Complex.normSq_zero] at hc
  nlinarith [sq_nonneg (p - 3/2)]

/-- The successful component after one amplification step is `goodCoeff p` times its initial
value. -/
theorem step_good {W P : Matrix H H ℂ} (j₀ : H)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) :
    P *ᵥ (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) =
      goodCoeff (ProjectiveBranchMass P true (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) • (P *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) := by
  have hid : P *ᵥ (P *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) = P *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) := by
    rw [Matrix.mulVec_mulVec, hP.1]
  rw [step_action j₀ hW hP]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hid, goodCoeff]
  module

/-- The unsuccessful component after one amplification step is multiplied by `omega * (1 - p)`. -/
theorem step_bad {W P : Matrix H H ℂ} (j₀ : H)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) :
    (1-P) *ᵥ (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) =
      (omega * (1 - (ProjectiveBranchMass P true (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) : ℂ))) •
        ((1-P) *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) := by
  have hgg : P *ᵥ (P *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) = P *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) := by
    rw [Matrix.mulVec_mulVec, hP.1]
  have hid : (1-P) *ᵥ (P *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hgg, sub_self]
  rw [step_action j₀ hW hP]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hid, smul_zero, add_zero]

/-- One fixed-point step cubes the failure probability [Grover2005]. -/
theorem step_failure {W P : Matrix H H ℂ} (j₀ : H)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) :
    1 - ProjectiveBranchMass P true (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) =
      (1 - ProjectiveBranchMass P true (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) ^ 3 := by
  let a := W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀
  let p := ProjectiveBranchMass P true a
  have ha : Normalized a := normalized_applyGate hW (normalized_ket j₀)
  have hb : Normalized (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) :=
    normalized_applyGate (step_unitary j₀ hW hP) (normalized_ket j₀)
  have hm := projectiveBranchMass_add hP a
  rw [measureProb_univ ha] at hm
  have hm' :=
      projectiveBranchMass_add hP (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)
  rw [measureProb_univ hb] at hm'
  have hn : ‖omega*(1-(p : ℂ))‖^2 = (1-p)^2 := by
    rw [show 1-(p : ℂ) = ((1-p : ℝ) : ℂ) by push_cast; rfl,
      norm_mul, mul_pow, omega_norm_sq, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hbad : ProjectiveBranchMass P false (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) = (1-p)^3 := by
    change MeasureProb
        ((1-P) *ᵥ (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) Finset.univ = _
    rw [step_bad j₀ hW hP, measureProb_smul]
    change ‖omega*(1-(p : ℂ))‖^2 * MeasureProb ((1-P) *ᵥ a) Finset.univ = _
    rw [hn]
    have hc : MeasureProb ((1-P) *ᵥ a) Finset.univ = 1-p := by
      change ProjectiveBranchMass P false a = 1-p
      dsimp only [p]
      linarith
    rw [hc]
    ring
  change 1 - ProjectiveBranchMass P true
      (step W P j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) = (1-p)^3
  linarith

end Geometry

/-- For `0 < b ≤ 1` and positive tolerance `η`, some stage satisfies `(1 - b^2)^(3^r) ≤ η`. -/
theorem exists_stage (b η : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hη : 0 < η) :
    ∃ r : ℕ, (1-b^2)^(3^r) ≤ η := by
  have hq0 : 0 ≤ 1-b^2 := by nlinarith
  have hq1 : 1-b^2 < 1 := by nlinarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1-b^2)^n < η := exists_pow_lt_of_lt_one hη hq1
  have hpow : ∀ r : ℕ, r ≤ 3^r := by
    intro r
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [pow_succ]
      have hp : 0 < 3^r := by positivity
      nlinarith
  exact ⟨n, (pow_le_pow_of_le_one hq0 hq1.le (hpow n)).trans hn.le⟩

section Iteration
variable {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]

/-- Decoding through an isometric target frame multiplies the initial decoded vector by
`goodCoeff p` after one amplification step. -/
theorem step_decoded {W : Matrix H H ℂ} (L : Matrix H O ℂ) (j₀ : H)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (hL : IsIsometry L) :
    Lᴴ *ᵥ (step W (rangeProjector L) j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) =
      goodCoeff (ProjectiveBranchMass (rangeProjector L) true (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) •
        (Lᴴ *ᵥ (W *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) := by
  have hLP : Lᴴ * rangeProjector L = Lᴴ := by
    rw [rangeProjector, ← Matrix.mul_assoc, show Lᴴ*L=1 from hL, Matrix.one_mul]
  have hv (a : QState H) : Lᴴ *ᵥ (rangeProjector L *ᵥ a) = Lᴴ *ᵥ a := by
    rw [Matrix.mulVec_mulVec, hLP]
  have hg := congrArg (fun a : QState H => Lᴴ *ᵥ a)
    (step_good j₀ hW (rangeProjector_isOrthogonalProjector hL))
  simpa only [hv, Matrix.mulVec_smul] using hg

/-- After `r` valid amplification stages, the failure probability is the initial failure
probability raised to `3^r`. -/
theorem word_failure (V B : Matrix H H ℂ) (L : Matrix H O ℂ) (j₀ : H)
    (cs : List (AdjointStep H)) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hB : B ∈ Matrix.unitaryGroup H ℂ) (hL : IsIsometry L)
    (hcs : ∀ G, AdjointStep.gate G ∈ cs → G ∈ Matrix.unitaryGroup H ℂ) (r : ℕ) :
    1-ProjectiveBranchMass (rangeProjector L) true
      (evaluatePrepared V B (word L j₀ cs r) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) =
    (1-ProjectiveBranchMass (rangeProjector L) true
      (evaluatePrepared V B (preparedTrial cs) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀))^(3^r) := by
  induction r with
  | zero => simp [word]
  | succ r ih =>
    have hW := (word_valid L j₀ cs hL hcs r).evaluate_unitary hV hB
    rw [word_evaluate_succ]
    change 1-ProjectiveBranchMass (rangeProjector L) true
      (step (evaluatePrepared V B (word L j₀ cs r)) (rangeProjector L) j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) = _
    rw [step_failure j₀ hW (rangeProjector_isOrthogonalProjector hL), ih,
      ← pow_mul, pow_succ]

/-- Every amplification stage preserves the decoded vector up to a nonzero complex scalar. -/
theorem word_decoded_scalar (V B : Matrix H H ℂ) (L : Matrix H O ℂ) (j₀ : H)
    (cs : List (AdjointStep H)) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hB : B ∈ Matrix.unitaryGroup H ℂ) (hL : IsIsometry L)
    (hcs : ∀ G, AdjointStep.gate G ∈ cs → G ∈ Matrix.unitaryGroup H ℂ) (r : ℕ) :
    ∃ z : ℂ, z ≠ 0 ∧
      Lᴴ *ᵥ (evaluatePrepared V B (word L j₀ cs r) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) =
        z • (Lᴴ *ᵥ (evaluatePrepared V B (preparedTrial cs) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) := by
  induction r with
  | zero => exact ⟨1, one_ne_zero, by simp [word]⟩
  | succ r ih =>
    obtain ⟨z, hz, he⟩ := ih
    have hW := (word_valid L j₀ cs hL hcs r).evaluate_unitary hV hB
    let q := ProjectiveBranchMass (rangeProjector L) true
      (evaluatePrepared V B (word L j₀ cs r) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)
    refine ⟨goodCoeff q * z, mul_ne_zero (goodCoeff_ne_zero q) hz, ?_⟩
    rw [word_evaluate_succ]
    change Lᴴ *ᵥ (step (evaluatePrepared V B (word L j₀ cs r))
      (rangeProjector L) j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) = _
    rw [step_decoded L j₀ hW hL, he, smul_smul]

end Iteration

end Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint

open Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint

namespace Qatlib.Concepts.LcuPostselect.ScaledLCU
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Matrix.Norms.L2Operator
universe u v w

/-- Provides fixed-point stage existence, a block-encoding lower bound on initial success, exact
circuit costs, and failure probability `(1 - p)^(3^r)` [Grover2005]. -/
theorem lcu_postselection_amplification :
(∀ (b η : ℝ), 0 < b → b ≤ 1 → 0 < η → η < 1 →
    ∃ r : ℕ, (1 - b ^ 2) ^ (3 ^ r) ≤ η) ∧
  ∀ {H : Type u} {I : Type v} {O : Type w}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (V B : Matrix H H ℂ) (cs : List (AdjointStep H))
    (A : Matrix O I ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (α δ : ℝ) (ψ : QState I) (j₀ : H),
    V ∈ Matrix.unitaryGroup H ℂ → B ∈ Matrix.unitaryGroup H ℂ →
    (∀ c ∈ cs, match c with
      | .gate G => G ∈ Matrix.unitaryGroup H ℂ
      | _ => True) →
    BlockEncoding A (evaluate V cs) L R α δ → Normalized ψ →
    B *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = R *ᵥ ψ →
    let p := postselectionProbability (evaluate V cs) L R ψ
    let s := ‖stateVector (A *ᵥ ψ)‖
    (δ ≤ s → ((s - δ) / α) ^ 2 ≤ p) ∧
    ∀ r : ℕ,
      PreparedCircuitValid (word L j₀ cs r) ∧
      preparedDataQueries (word L j₀ cs r) = 3 ^ r * adjointQueryCount cs ∧
      preparedInputQueries (word L j₀ cs r) = 3 ^ r ∧
      preparedFixedGates (word L j₀ cs r) =
        3 ^ r * adjointGateCount cs + (3 ^ r - 1) ∧
      1 - postselectionProbability (evaluatePrepared V B (word L j₀ cs r))
        L (1 : Matrix H H ℂ) (Qatlib.Foundations.PureStateMath.Ket j₀) = (1 - p) ^ (3 ^ r) ∧
      (∀ (b η : ℝ), 0 < b → b ≤ 1 → b ^ 2 ≤ p →
        (1 - b ^ 2) ^ (3 ^ r) ≤ η →
        1 - η ≤ postselectionProbability (evaluatePrepared V B (word L j₀ cs r))
          L (1 : Matrix H H ℂ) (Qatlib.Foundations.PureStateMath.Ket j₀)) := by
  constructor
  · intro b η hb hb1 hη _
    exact LCUFixedPoint.exists_stage b η hb hb1 hη
  · intro H I O _ _ _ _ _ _ V B cs A L R α δ ψ j₀ hV hB hcs henc hψ hprepare
    (try dsimp only)
    have hfixed : ∀ G, AdjointStep.gate G ∈ cs → G ∈ Matrix.unitaryGroup H ℂ :=
      fun G hG => hcs (.gate G) hG
    refine ⟨fun hgap => (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower henc) hψ hgap, ?_⟩
    intro r
    let p := postselectionProbability (evaluate V cs) L R ψ
    have hbase : ProjectiveBranchMass (rangeProjector L) true
        (evaluatePrepared V B (preparedTrial cs) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) = p := by
      rw [evaluate_preparedTrial, ← Matrix.mulVec_mulVec, hprepare]
      rfl
    have hfail : 1-postselectionProbability (evaluatePrepared V B (word L j₀ cs r))
        L (1 : Matrix H H ℂ) (Qatlib.Foundations.PureStateMath.Ket j₀) = (1-p)^(3^r) := by
      change 1-ProjectiveBranchMass (rangeProjector L) true
        (evaluatePrepared V B (word L j₀ cs r) *ᵥ ((1 : Matrix H H ℂ) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀)) = _
      rw [Matrix.one_mulVec, word_failure V B L j₀ cs hV hB henc.left_isometry hfixed r, hbase]
    have hc := word_counts L j₀ cs r
    refine ⟨word_valid L j₀ cs henc.left_isometry hfixed r, hc.1, hc.2.1, hc.2.2, hfail, ?_⟩
    intro b η _ _ hbp hbudget
    have hp := postselectionProbability_mem_Icc henc.unitary henc.left_isometry
      henc.right_isometry hψ
    have he := pow_le_pow_left₀ (by linarith [hp.2] : 0 ≤ 1-p)
      (sub_le_sub_left hbp 1) (3^r)
    rw [← hfail] at he
    linarith

end Qatlib.Concepts.LcuPostselect.ScaledLCU

namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

/-- Conditioning a nonzero scalar multiple of a nonzero vector gives its normalized state up to
a unit-modulus scalar, which can be removed by conjugate phase correction. -/
theorem conditional_scalar {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℂ) (x : QState I) (hc : c ≠ 0) (hx : x ≠ 0) :
    ∃ (y : QState I) (z : ℂ), ConditionalState (c • x) = some y ∧
      ‖z‖ = 1 ∧ y = z • PostMeasure x Finset.univ ∧ Normalized y ∧
      (star z) • y = PostMeasure x Finset.univ := by
  let z : ℂ := (‖c‖ : ℂ)⁻¹ * c
  have hn : ‖stateVector (c • x)‖ = ‖c‖ * ‖stateVector x‖ := by
    change ‖c • stateVector x‖ = _
    exact norm_smul c _
  have hnorm : ‖z‖ = 1 := by
    dsimp only [z]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc)]
  have hstar : star z * z = 1 := by
    change (starRingEnd ℂ z) * z = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hcx : c • x ≠ 0 := smul_ne_zero hc hx
  have hout : ConditionalState (c • x) = some (z • PostMeasure x Finset.univ) := by
    rw [conditionalState_eq_some_of_ne_zero hcx]
    congr 1
    rw [postMeasure_univ_eq_smul, postMeasure_univ_eq_smul, hn]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, _root_.mul_inv_rev, z]
    push_cast
    ring
  refine ⟨z • PostMeasure x Finset.univ, z, hout, hnorm, rfl,
    normalized_of_conditionalState_eq_some hout, ?_⟩
  rw [smul_smul, hstar, one_smul]

end Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint

namespace Qatlib.Concepts.LcuPostselect.ScaledLCU
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Matrix.Norms.L2Operator
universe u v w

/-- Bounds the relative unnormalized output error and the normalized output error by `δ / ‖Aψ‖`
and `2 * δ / ‖Aψ‖`, respectively, with the latter preserved under amplification after phase
correction. -/
theorem lcu_relative_postselected_output_error :
∀ {H : Type u} {I : Type v} {O : Type w}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (V B : Matrix H H ℂ) (cs : List (AdjointStep H))
    (A : Matrix O I ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (α δ : ℝ) (ψ : QState I) (j₀ : H),
    V ∈ Matrix.unitaryGroup H ℂ → B ∈ Matrix.unitaryGroup H ℂ →
    (∀ c ∈ cs, match c with
      | .gate G => G ∈ Matrix.unitaryGroup H ℂ
      | _ => True) →
    BlockEncoding A (evaluate V cs) L R α δ → Normalized ψ →
    B *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = R *ᵥ ψ →
    let U := evaluate V cs
    let y := postselectionVector U L R ψ
    let t := A *ᵥ ψ
    let s := ‖stateVector t‖
    δ < s →
    ‖stateVector y - α⁻¹ • stateVector t‖ ≤ δ / α ∧
    ‖stateVector t - α • stateVector y‖ / s ≤ δ / s ∧
    ∃ φ : QState O,
      postselectionOutput U L R ψ = some φ ∧ Normalized φ ∧
      ‖stateVector φ - NormedSpace.normalize (stateVector t)‖ ≤ 2 * δ / s ∧
      ∀ r : ℕ, ∃ (φr : QState O) (z : ℂ),
        postselectionOutput (evaluatePrepared V B (word L j₀ cs r))
          L (1 : Matrix H H ℂ) (Qatlib.Foundations.PureStateMath.Ket j₀) = some φr ∧
        ‖z‖ = 1 ∧ φr = z • φ ∧ Normalized φr ∧
        ‖stateVector ((star z) • φr) - NormedSpace.normalize (stateVector t)‖ ≤
          2 * δ / s ∧
        (∀ ε : ℝ, 0 ≤ ε → δ ≤ ε * s / 2 →
          ‖stateVector ((star z) • φr) - NormedSpace.normalize (stateVector t)‖ ≤ ε) := by
  intro H I O _ _ _ _ _ _ V B cs A L R α δ ψ j₀ hV hB hcs henc hψ hprepare
  (try dsimp only)
  intro hgap
  let y := postselectionVector (evaluate V cs) L R ψ
  let t := A *ᵥ ψ
  let s := ‖stateVector t‖
  have hs : 0 < s := lt_of_le_of_lt henc.error_nonneg hgap
  have herr :=
      (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_error henc) hψ
  change ‖stateVector t - α • stateVector y‖ ≤ δ at herr
  have hfirst : ‖stateVector y - α⁻¹ • stateVector t‖ ≤ δ/α := by
    have he : stateVector y - α⁻¹ • stateVector t =
        α⁻¹ • (α • stateVector y - stateVector t) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ henc.normalization_pos.ne', one_smul]
    rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr henc.normalization_pos.le)]
    calc
      _ ≤ α⁻¹ * δ := mul_le_mul_of_nonneg_left
        (by simpa only [norm_sub_rev] using herr) (inv_nonneg.mpr henc.normalization_pos.le)
      _ = _ := by ring
  refine ⟨hfirst, div_le_div_of_nonneg_right herr hs.le, ?_⟩
  obtain ⟨_, φ, hout, _, hφ, hφerr⟩ :=
      (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap henc) hψ hgap
  change ConditionalState y = some φ at hout
  have hy : y ≠ 0 := by
    intro hz
    rw [hz, conditionalState_zero] at hout
    cases hout
  have hφeq : PostMeasure y Finset.univ = φ :=
    Option.some.inj ((conditionalState_eq_some_of_ne_zero hy).symm.trans hout)
  refine ⟨φ, hout, hφ, hφerr, ?_⟩
  intro r
  have hfixed : ∀ G, AdjointStep.gate G ∈ cs → G ∈ Matrix.unitaryGroup H ℂ :=
    fun G hG => hcs (.gate G) hG
  obtain ⟨c, hc, hdecode⟩ := word_decoded_scalar V B L j₀ cs hV hB henc.left_isometry hfixed r
  have hbase : Lᴴ *ᵥ (evaluatePrepared V B (preparedTrial cs) *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀) = y := by
    rw [evaluate_preparedTrial, ← Matrix.mulVec_mulVec, hprepare]
    simp only [y, postselectionVector, compress, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hactual : postselectionVector (evaluatePrepared V B (word L j₀ cs r))
      L (1 : Matrix H H ℂ) (Qatlib.Foundations.PureStateMath.Ket j₀) = c • y := by
    rw [hbase] at hdecode
    simpa only [postselectionVector, compress, Matrix.mul_one, Matrix.mulVec_mulVec] using hdecode
  obtain ⟨φr, z, hrout, hznorm, hrphase, hrnorm, halign⟩ := conditional_scalar c y hc hy
  rw [hφeq] at hrphase halign
  refine ⟨φr, z, ?_, hznorm, hrphase, hrnorm, ?_, ?_⟩
  · change ConditionalState (postselectionVector _ _ _ _) = some φr
    rw [hactual]
    exact hrout
  · rw [halign]
    exact hφerr
  · intro ε _ hδ
    rw [halign]
    apply hφerr.trans
    apply (div_le_iff₀ hs).mpr
    nlinarith

end Qatlib.Concepts.LcuPostselect.ScaledLCU

namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Matrix.Norms.L2Operator

/-- Packages circuit validity, success probability at least `1 - η`, unnormalized error bounds,
and phase-corrected normalized output accuracy for an amplification stage. -/
def Result {H I O : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (V B : Matrix H H ℂ) (cs : List (AdjointStep H))
    (A : Matrix O I ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (α δ : ℝ) (ψ : QState I) (j₀ : H) (η : ℝ) (r : ℕ) : Prop :=
  PreparedCircuitValid (word L j₀ cs r) ∧
  1-η ≤ postselectionProbability (evaluatePrepared V B (word L j₀ cs r)) L 1 (Qatlib.Foundations.PureStateMath.Ket j₀) ∧
  ‖stateVector (postselectionVector (evaluate V cs) L R ψ) -
    α⁻¹ • stateVector (A *ᵥ ψ)‖ ≤ δ/α ∧
  ‖stateVector (A *ᵥ ψ) - α • stateVector (postselectionVector (evaluate V cs) L R ψ)‖ /
    ‖stateVector (A *ᵥ ψ)‖ ≤ δ / ‖stateVector (A *ᵥ ψ)‖ ∧
  ∃ (φ φr : QState O) (z : ℂ),
    postselectionOutput (evaluate V cs) L R ψ = some φ ∧
    postselectionOutput (evaluatePrepared V B (word L j₀ cs r)) L 1 (Qatlib.Foundations.PureStateMath.Ket j₀) = some φr ∧
    ‖z‖ = 1 ∧ φr = z • φ ∧ Normalized φ ∧ Normalized φr ∧
    ‖stateVector ((star z) • φr) - NormedSpace.normalize (stateVector (A *ᵥ ψ))‖ ≤
      2*δ / ‖stateVector (A *ᵥ ψ)‖

/-- A positive lower bound on the initial success amplitude and a strict output-error gap yield
a stage satisfying `Result`, with exact data, input, and fixed-gate counts. -/
theorem result_of_lower {H I O : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (V B : Matrix H H ℂ) (cs : List (AdjointStep H))
    (A : Matrix O I ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (α δ : ℝ) (ψ : QState I) (j₀ : H) (b η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (hfixed : ∀ G, AdjointStep.gate G ∈ cs → G ∈ Matrix.unitaryGroup H ℂ)
    (henc : BlockEncoding A (evaluate V cs) L R α δ) (hψ : Normalized ψ)
    (hprepare : B *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = R *ᵥ ψ)
    (hb : 0 < b) (hb1 : b ≤ 1) (hη : 0 < η) (_hη1 : η < 1)
    (hgap : δ < ‖stateVector (A *ᵥ ψ)‖)
    (hlower : b ≤ (‖stateVector (A *ᵥ ψ)‖-δ)/α) :
    ∃ r : ℕ, Result V B cs A L R α δ ψ j₀ η r ∧
      preparedDataQueries (word L j₀ cs r) = 3^r * adjointQueryCount cs ∧
      preparedInputQueries (word L j₀ cs r) = 3^r ∧
      preparedFixedGates (word L j₀ cs r) = 3^r * adjointGateCount cs + (3^r-1) := by
  have hcs : ∀ c ∈ cs, match c with
      | .gate G => G ∈ Matrix.unitaryGroup H ℂ
      | _ => True := by
    intro c hc
    cases c with
    | gate G => exact hfixed G hc
    | forward => trivial
    | backward => trivial
  obtain ⟨r, hr⟩ := exists_stage b η hb hb1 hη
  have ha := lcu_postselection_amplification.2 V B cs A L R α δ ψ j₀
    hV hB hcs henc hψ hprepare
  have hsquare := pow_le_pow_left₀ hb.le hlower 2
  have hp := hsquare.trans (ha.1 hgap.le)
  rcases ha.2 r with ⟨hv, hq, hi, hg, _, hsuccess⟩
  rcases lcu_relative_postselected_output_error V B cs A L R α δ ψ j₀
      hV hB hcs henc hψ hprepare hgap with ⟨habs, hrel, φ, hφout, hφ, _, houtputs⟩
  obtain ⟨φr, z, hrout, hz, hphase, hφr, herr, _⟩ := houtputs r
  exact ⟨r, ⟨hv, hsuccess b η hb hb1 hp hr, habs, hrel,
    φ, φr, z, hφout, hrout, hz, hphase, hφ, hφr, herr⟩, hq, hi, hg⟩

end Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint

namespace Qatlib.Concepts.LcuPostselect.ScaledLCU
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Matrix.Norms.L2Operator

/-- The adjoint-query word consisting of coefficient unpreparation, one forward query, and
coefficient preparation. -/
def scaledLCUAdjointWord {J H : Type*} [Fintype J] [DecidableEq J] [Fintype H]
    [DecidableEq H] (d : J → ℂ) (j₀ : J) : List (AdjointStep (J×H)) :=
  [.gate (prepareRegister (coefficientPrepare d j₀))ᴴ, .forward,
    .gate (prepareRegister (coefficientPrepare d j₀))]

/-- Under the output-gap and success-amplitude lower bounds, scaled LCU has an amplified stage
satisfying `LCUFixedPoint.Result`, with `3^r` data queries, `3^r` input queries, and `3 *
3^r - 1` fixed gates. -/
theorem scaled_lcu_fixed_point_consumer {J H I O : Type*}
    [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (jtag : J) (A : J → Matrix O I ℂ) (U : J → Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (c : J → ℂ) (α ε : J → ℝ)
    (B : Matrix (J×H) (J×H) ℂ) (ψ : QState I) (j₀ : J×H) (b η : ℝ)
    (henc : ∀ j, BlockEncoding (A j) (U j) L R (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α))
    (hB : B ∈ Matrix.unitaryGroup (J×H) ℂ) (hψ : Normalized ψ)
    (hprepare : B *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = tagFrame jtag R *ᵥ ψ)
    (hb : 0 < b) (hb1 : b ≤ 1) (hη : 0 < η) (hη1 : η < 1)
    (hgap : (∑ j, ‖c j‖*ε j) < ‖stateVector ((∑ j, c j • A j) *ᵥ ψ)‖)
    (hlower : b ≤ (‖stateVector ((∑ j, c j • A j) *ᵥ ψ)‖-(∑ j, ‖c j‖*ε j)) /
      (∑ j, ‖c j‖*α j)) :
    let d := scaledLCUCoefficients c α
    let V := select (phaseAbsorbed d U)
    let cs := scaledLCUAdjointWord (H := H) d jtag
    ∃ r : ℕ,
      LCUFixedPoint.Result V B cs (∑ j, c j • A j) (tagFrame jtag L) (tagFrame jtag R)
        (∑ j, ‖c j‖*α j) (∑ j, ‖c j‖*ε j) ψ j₀ η r ∧
      preparedDataQueries (LCUFixedPoint.word (tagFrame jtag L) j₀ cs r) = 3^r ∧
      preparedInputQueries (LCUFixedPoint.word (tagFrame jtag L) j₀ cs r) = 3^r ∧
      preparedFixedGates (LCUFixedPoint.word (tagFrame jtag L) j₀ cs r) = 3*3^r-1 := by
  (try dsimp only)
  let d := scaledLCUCoefficients c α
  let V := select (phaseAbsorbed d U)
  let cs := scaledLCUAdjointWord (H := H) d jtag
  have hP := prepareRegister_unitary (I := H) (coefficientPrepare_unitary d jtag hmass)
  have hV : V ∈ Matrix.unitaryGroup (J×H) ℂ :=
    select_unitary _ (phaseAbsorbed_unitary d U (fun j => (henc j).unitary))
  have hfixed : ∀ G, AdjointStep.gate G ∈ cs → G ∈ Matrix.unitaryGroup (J×H) ℂ := by
    intro G hG
    simp [cs, scaledLCUAdjointWord] at hG
    rcases hG with rfl|rfl
    · exact adjoint_unitary hP
    · exact hP
  have heval : evaluate V cs = coefficientLCUUnitary d U jtag := by
    simp [cs, scaledLCUAdjointWord, V, evaluate, instructionMatrix,
      coefficientLCUUnitary, Matrix.mul_assoc]
  have hE : BlockEncoding (∑ j, c j • A j) (evaluate V cs) (tagFrame jtag L)
      (tagFrame jtag R) (∑ j, ‖c j‖*α j) (∑ j, ‖c j‖*ε j) := by
    rw [heval]
    exact scaled_approximate_lcu_encoding jtag A U L R c α ε henc hmass
  obtain ⟨r, hresult, hq, hi, hg⟩ := LCUFixedPoint.result_of_lower V B cs _ _ _ _ _ ψ j₀ b η
    hV hB hfixed hE hψ hprepare hb hb1 hη hη1 hgap hlower
  refine ⟨r, hresult, ?_, hi, ?_⟩
  · simpa [cs, scaledLCUAdjointWord, adjointQueryCount] using hq
  · have hcount : adjointGateCount cs = 2 := rfl
    rw [hcount] at hg
    apply hg.trans
    have hp : 0 < 3^r := by positivity
    omega

end Qatlib.Concepts.LcuPostselect.ScaledLCU
