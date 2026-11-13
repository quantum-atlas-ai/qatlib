/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.ClusterPatterns.WireComposition.PauliMixtureTwirling

/-!
# A counted coherent phase-oracle example

The explicit auxiliary rotation and input frame define `coherentPhaseOracle ζ`, whose compressed
block is one half of a phase-scaled Pauli matrix. `coherent_phase_oracle_counted_consumer` gives
exact repeated amplified-circuit semantics, counts its queries and gates, and bounds the
accumulated phase error. For background, see [BerryEtAl2015Taylor].

## Main statements

* `coherent_phase_oracle_data`: projected unitary encoding for the explicit oracle.
* `coherent_phase_oracle_counted_consumer`: repeated circuit action, query counts, and vector
  errors.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

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

/-- An isometric matrix preserves the Euclidean norm of a state vector. -/
private theorem norm_toEuclidean_mulVec_of_isometry {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] {V : Matrix H I ℂ} (hV : IsIsometry V) (ψ : QState I) :
    ‖toEuclidean_fromVec (V *ᵥ ψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
  Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.stateVector_norm hV ψ

/-- Real scalar multiplication of a complex matrix equals multiplication by the same scalar
coerced to `ℂ`. -/
private theorem real_smul_matrix_eq {H I : Type} [Fintype H] [Fintype I] (r : ℝ)
    (M : Matrix H I ℂ) : (r • M) = ((r : ℂ)) • M := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- A complex number of norm one satisfies `IsPhase`. -/
private theorem isPhase_of_complex_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) : IsPhase ζ := by
  rw [IsPhase, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    hζ, one_pow, Complex.ofReal_one]

/-- For a unit-modulus complex number, `‖ζ ^ n - 1‖` is at most `n * ‖ζ - 1‖`. -/
private theorem complex_norm_pow_sub_one_le (ζ : ℂ) (hζ : ‖ζ‖ = 1) (n : ℕ) :
    ‖ζ ^ n - 1‖ ≤ (n : ℝ) * ‖ζ - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1) := by
      rw [pow_succ']
      ring
    rw [h, Nat.cast_succ, add_mul, one_mul]
    exact (norm_add_le _ _).trans
      (add_le_add (by rw [norm_mul, hζ, one_mul]; exact ih) le_rfl)

/-- The real planar rotation matrix with diagonal entries `1 / 2` and off-diagonal entries `-√3
/ 2` and `√3 / 2`. -/
noncomputable def coherentAuxRotation : Operator 2 :=
  !![1 / 2, -Real.sqrt 3 / 2; Real.sqrt 3 / 2, 1 / 2]

/-- The basis embedding of a qubit into the joint register with auxiliary label zero. -/
noncomputable def coherentInputFrame : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  Matrix.of fun p j => if p = (0, j) then 1 else 0

/-- The tensor product of `coherentAuxRotation` with the phase-scaled matrix `ζ • pauliXChoice
true`. -/
noncomputable def coherentPhaseOracle (ζ : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  TensorGate coherentAuxRotation (ζ • pauliXChoice true)

/-- The explicit auxiliary rotation is unitary. -/
private theorem coherentAuxRotation_unitary :
    coherentAuxRotation ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coherentAuxRotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.conj_ofNat] <;>
    first
    | (rw [div_mul_div_comm, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num)
    | (rw [div_mul_div_comm, neg_mul_neg, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num)
    | ring

/-- The input frame embedding into auxiliary label zero is isometric. -/
private theorem coherentInputFrame_isometry : IsIsometry coherentInputFrame := by
  show coherentInputFrameᴴ * coherentInputFrame = 1
  ext j j'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (0, j)]
  · simp [coherentInputFrame, Matrix.one_apply]
  · intro p _ hp
    simp [coherentInputFrame, hp]
  · simp

/-- Compression through `coherentInputFrame` selects the auxiliary-zero block of the joint
matrix. -/
private theorem compress_coherentInputFrame (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    compress coherentInputFrame M coherentInputFrame =
      Matrix.of fun j j' => M (0, j) (0, j') := by
  ext j j'
  simp only [compress, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (0, j')]
  · rw [Finset.sum_eq_single (0, j)]
    · simp [coherentInputFrame]
    · intro p _ hp
      simp [coherentInputFrame, hp]
    · simp
  · intro q _ hq
    simp [coherentInputFrame, hq]
  · simp

/-- For unit-modulus `ζ`, the auxiliary rotation is unitary, the input frame is isometric, and
the oracle encodes `(1/2) • (ζ • pauliXChoice true)`. -/
theorem coherent_phase_oracle_data (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    coherentAuxRotation ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ IsIsometry coherentInputFrame ∧
      ProjectedUnitaryEncoding ((1/2:ℂ)•(ζ•pauliXChoice true)) (coherentPhaseOracle ζ)
        coherentInputFrame coherentInputFrame := by
  have hζp : IsPhase ζ := isPhase_of_complex_norm_eq_one hζ
  have hζu : ζ ∈ unitary ℂ := ⟨hζp, by simpa only [IsPhase, mul_comm] using hζp⟩
  refine ⟨coherentAuxRotation_unitary, coherentInputFrame_isometry, ?_,
    coherentInputFrame_isometry, coherentInputFrame_isometry, ?_⟩
  · exact tensorGate_unitary coherentAuxRotation_unitary
      (Unitary.smul_mem_of_mem hζu (pauliXChoice_unitary true))
  · rw [compress_coherentInputFrame]
    ext j j'
    simp only [Matrix.of_apply, coherentPhaseOracle, TensorGate, Matrix.kronecker_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [show coherentAuxRotation (0 : Fin 2) (0 : Fin 2) = 1 / 2 by
      norm_num [coherentAuxRotation]]

/-- A unit-modulus phase within `δ` of one gives a scale-two block encoding; `n` amplified
repetitions use `3 * n` queries and `4 * n` gates and implement the embedded Pauli power
with phase `ζ ^ n`. The vector error satisfies both stated linear-in-`n` bounds
[BerryEtAl2015Taylor]. -/
theorem coherent_phase_oracle_counted_consumer (ζ : ℂ) (δ : ℝ) (hζ : ‖ζ‖ = 1)
    (hδ : ‖ζ - 1‖ ≤ δ) :
    BlockEncoding (pauliXChoice true) (coherentPhaseOracle ζ) coherentInputFrame
        coherentInputFrame 2 δ ∧
      (∀ (n : ℕ) (ψ : QState (Fin 2)),
        let cs := repeatAdjointWord (substituteAdjointCircuit [.forward]
          (coherentOAAWord coherentInputFrame)) n
        adjointQueryCount cs = 3 * n ∧ adjointGateCount cs = 4 * n ∧
        (evaluate (coherentPhaseOracle ζ) cs)*ᵥ(coherentInputFrame*ᵥψ) =
          coherentInputFrame*ᵥ(ζ^n • (((pauliXChoice true)^n)*ᵥψ)) ∧
        ‖toEuclidean_fromVec ((evaluate (coherentPhaseOracle ζ) cs)*ᵥ(coherentInputFrame*ᵥψ) -
            coherentInputFrame*ᵥ(((pauliXChoice true)^n)*ᵥψ))‖ ≤
          (n:ℝ)*δ*‖toEuclidean_fromVec ψ‖ ∧
        ‖toEuclidean_fromVec ((evaluate (coherentPhaseOracle ζ) cs)*ᵥ(coherentInputFrame*ᵥψ) -
            coherentInputFrame*ᵥ(((pauliXChoice true)^n)*ᵥψ))‖ ≤
          (n:ℝ)*Real.sqrt (2*coherentOAAError δ)*‖toEuclidean_fromVec ψ‖) := by
  obtain ⟨hrot, hframe, hPUE⟩ := coherent_phase_oracle_data ζ hζ
  have hζp : IsPhase ζ := isPhase_of_complex_norm_eq_one hζ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hXu : pauliXChoice true ∈ Matrix.unitaryGroup (Fin 2) ℂ := pauliXChoice_unitary true
  have horacle : coherentPhaseOracle ζ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := hPUE.unitary
  have h2 : (2 : ℝ) • ((1 / 2 : ℂ) • (ζ • pauliXChoice true)) = ζ • pauliXChoice true := by
    rw [real_smul_matrix_eq, smul_smul, show ((2 : ℝ) : ℂ) * (1 / 2 : ℂ) = 1 by norm_num,
      one_smul]
  have h3 : pauliXChoice true - ζ • pauliXChoice true = (1 - ζ) • pauliXChoice true := by
    rw [sub_smul, one_smul]
  have herr2 : ‖pauliXChoice true - (2 : ℝ) • compress coherentInputFrame
        (coherentPhaseOracle ζ) coherentInputFrame‖ ≤ δ := by
    rw [hPUE.encoded, h2, h3, norm_smul,
      CStarRing.norm_of_mem_unitary (pauliXChoice_unitary true), mul_one, norm_sub_rev]
    exact hδ
  have hBE : BlockEncoding (pauliXChoice true) (coherentPhaseOracle ζ) coherentInputFrame
      coherentInputFrame 2 δ :=
    ⟨horacle, hframe, hframe, by norm_num, hδ0, herr2⟩
  refine ⟨hBE, ?_⟩
  intro n ψ
  have hXiso : IsIsometry (ζ • pauliXChoice true) := by
    show (ζ • pauliXChoice true)ᴴ * (ζ • pauliXChoice true) = 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hζp]
    have hX : (pauliXChoice true)ᴴ * pauliXChoice true = 1 := by
      rw [← Matrix.star_eq_conjTranspose, ← Matrix.mem_unitaryGroup_iff']
      exact pauliXChoice_unitary true
    rw [hX]
    simp
  have haction : coherentOAAOperator (coherentPhaseOracle ζ) coherentInputFrame *
      coherentInputFrame = coherentInputFrame * (ζ • pauliXChoice true) := by
    have hev : coherentOAAOperator (coherentPhaseOracle ζ) coherentInputFrame =
        phasedAlternating (coherentPhaseOracle ζ) (rangeProjector coherentInputFrame)
          (rangeProjector coherentInputFrame) (-Complex.I) cubicPhases :=
      evaluate_compileQSVT _ _ _ _ _
    rw [hev]
    exact oblivious_half_isometry_action hPUE hXiso
  have hpow : ∀ m : ℕ,
      (coherentOAAOperator (coherentPhaseOracle ζ) coherentInputFrame)^m * coherentInputFrame =
        coherentInputFrame * (ζ • pauliXChoice true)^m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, haction,
        Matrix.mul_assoc]
  have hsmulpow : ∀ m : ℕ, (ζ • pauliXChoice true)^m = ζ^m • (pauliXChoice true)^m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ,
        ← pow_succ]
  have heval : evaluate (coherentPhaseOracle ζ) [.forward] = coherentPhaseOracle ζ := by
    simp [evaluate, instructionMatrix]
  have hwf1 : WellFormedAdjointCircuit ([.forward] : List (AdjointStep (Fin 2 × Fin 2))) := by
    intro V hV
    simp at hV
  have hBE2 : BlockEncoding (pauliXChoice true) (evaluate (coherentPhaseOracle ζ) [.forward])
      coherentInputFrame coherentInputFrame 2 δ := by
    rw [heval]
    exact hBE
  have h10 := coherent_oaa_expanded_repeat_error_and_cost (coherentPhaseOracle ζ) [.forward]
    (pauliXChoice true) coherentInputFrame δ horacle hwf1 hXu hBE2 n ψ
  obtain ⟨h9e, _, _, _⟩ := coherent_oaa_expanded_subroutine (coherentPhaseOracle ζ) [.forward]
    coherentInputFrame hwf1 hframe
  rw [heval] at h9e
  obtain ⟨h3e, _, _, _⟩ := repeat_adjoint_word_semantics_cost (coherentPhaseOracle ζ)
    (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n
  have hWn : evaluate (coherentPhaseOracle ζ) (repeatAdjointWord
        (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n) =
      (coherentOAAOperator (coherentPhaseOracle ζ) coherentInputFrame)^n := by
    rw [h3e, h9e]
  have hExact : (evaluate (coherentPhaseOracle ζ) (repeatAdjointWord
        (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n)) *ᵥ
        (coherentInputFrame *ᵥ ψ) =
      coherentInputFrame *ᵥ (ζ^n • (((pauliXChoice true)^n) *ᵥ ψ)) := by
    calc (evaluate (coherentPhaseOracle ζ) (repeatAdjointWord
            (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n)) *ᵥ
            (coherentInputFrame *ᵥ ψ)
        = ((coherentOAAOperator (coherentPhaseOracle ζ) coherentInputFrame)^n *
            coherentInputFrame) *ᵥ ψ := by
          rw [hWn, Matrix.mulVec_mulVec]
      _ = (coherentInputFrame * (ζ • pauliXChoice true)^n) *ᵥ ψ := by rw [hpow n]
      _ = coherentInputFrame *ᵥ ((ζ^n • (pauliXChoice true)^n) *ᵥ ψ) := by
          rw [hsmulpow n, ← Matrix.mulVec_mulVec]
      _ = coherentInputFrame *ᵥ (ζ^n • (((pauliXChoice true)^n) *ᵥ ψ)) := by
          rw [Matrix.smul_mulVec]
  have hvec : ζ^n • (((pauliXChoice true)^n) *ᵥ ψ) - ((pauliXChoice true)^n) *ᵥ ψ =
      (ζ^n - 1) • (((pauliXChoice true)^n) *ᵥ ψ) := by
    rw [sub_smul, one_smul]
  have hdiff : (evaluate (coherentPhaseOracle ζ) (repeatAdjointWord
        (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n)) *ᵥ
        (coherentInputFrame *ᵥ ψ) - coherentInputFrame *ᵥ (((pauliXChoice true)^n) *ᵥ ψ) =
      coherentInputFrame *ᵥ ((ζ^n - 1) • (((pauliXChoice true)^n) *ᵥ ψ)) := by
    rw [hExact, ← Matrix.mulVec_sub, hvec]
  show adjointQueryCount (repeatAdjointWord (substituteAdjointCircuit [.forward]
        (coherentOAAWord coherentInputFrame)) n) = 3 * n ∧
    adjointGateCount (repeatAdjointWord (substituteAdjointCircuit [.forward]
        (coherentOAAWord coherentInputFrame)) n) = 4 * n ∧
    (evaluate (coherentPhaseOracle ζ) (repeatAdjointWord (substituteAdjointCircuit [.forward]
        (coherentOAAWord coherentInputFrame)) n))*ᵥ(coherentInputFrame*ᵥψ) =
      coherentInputFrame*ᵥ(ζ^n • (((pauliXChoice true)^n)*ᵥψ)) ∧
    ‖toEuclidean_fromVec ((evaluate (coherentPhaseOracle ζ) (repeatAdjointWord
        (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n))*ᵥ
        (coherentInputFrame*ᵥψ) - coherentInputFrame*ᵥ(((pauliXChoice true)^n)*ᵥψ))‖ ≤
      (n:ℝ)*δ*‖toEuclidean_fromVec ψ‖ ∧
    ‖toEuclidean_fromVec ((evaluate (coherentPhaseOracle ζ) (repeatAdjointWord
        (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n))*ᵥ
        (coherentInputFrame*ᵥψ) - coherentInputFrame*ᵥ(((pauliXChoice true)^n)*ᵥψ))‖ ≤
      (n:ℝ)*Real.sqrt (2*coherentOAAError δ)*‖toEuclidean_fromVec ψ‖
  refine ⟨?_, ?_, hExact, ?_, ?_⟩
  · rw [h10.1, show adjointQueryCount [.forward] = 1 from rfl, mul_one]
  · rw [h10.2.1, show adjointGateCount [.forward] = 0 from rfl]
    ring
  · calc ‖toEuclidean_fromVec ((evaluate (coherentPhaseOracle ζ) (repeatAdjointWord
            (substituteAdjointCircuit [.forward] (coherentOAAWord coherentInputFrame)) n))*ᵥ
            (coherentInputFrame*ᵥψ) - coherentInputFrame*ᵥ(((pauliXChoice true)^n)*ᵥψ))‖
        = ‖toEuclidean_fromVec (coherentInputFrame *ᵥ
            ((ζ^n - 1) • (((pauliXChoice true)^n) *ᵥ ψ)))‖ := by rw [hdiff]
      _ = ‖toEuclidean_fromVec ((ζ^n - 1) • (((pauliXChoice true)^n) *ᵥ ψ))‖ :=
          norm_toEuclidean_mulVec_of_isometry hframe _
      _ = ‖ζ^n - 1‖ * ‖toEuclidean_fromVec (((pauliXChoice true)^n) *ᵥ ψ)‖ := by
          rw [show toEuclidean_fromVec ((ζ^n - 1) • (((pauliXChoice true)^n) *ᵥ ψ)) =
            (ζ^n - 1) • toEuclidean_fromVec (((pauliXChoice true)^n) *ᵥ ψ) from rfl,
            norm_smul]
      _ = ‖ζ^n - 1‖ * ‖toEuclidean_fromVec ψ‖ := by
          rw [norm_toEuclidean_mulVec_of_unitary (pow_mem hXu n) ψ]
      _ ≤ ((n : ℝ) * δ) * ‖toEuclidean_fromVec ψ‖ :=
          mul_le_mul_of_nonneg_right ((complex_norm_pow_sub_one_le ζ hζ n).trans
            (mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg n))) (norm_nonneg _)
      _ = (n : ℝ) * δ * ‖toEuclidean_fromVec ψ‖ := by ring
  · exact h10.2.2

end Qatlib.Concepts.TrotterFormula.GeneralOrder
