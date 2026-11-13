/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Noisy value phase kickback

This module studies the value-oracle phase-kickback construction described in
[NielsenChuang2010]. The circuit `valueAccessWord` uses two queries and one phase gate, and
`valueAccessWord_executed` identifies its operator exactly. A zero value register is returned to
zero while the data register receives the table phase.

`TablePhaseError` measures phase error modulo integers. The module bounds the resulting operator
and state errors, extends the estimates to adjoint and Boolean-controlled access, and identifies
the construction with the gradient-grid continuation.

## Main statements

* `valueAccessWord_resources`: exact query and gate counts.
* `noisyValueKickbackOperatorError`: operator error at most `2πη`.
* `noisyValueKickbackStateError`: Euclidean state error with a clean value register.
* `frontier1`: the combined kickback specification.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SignalPrimitive.GridGradient

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.ReferenceError.RefTraceError

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate

/-- The value phase coefficient on `ZMod Q` equals the standard additive character. -/
theorem valuePhaseCoeff_eq_stdAddChar (Q : ℕ) [NeZero Q] (a : ZMod Q) :
    valuePhaseCoeff Q a = ZMod.stdAddChar a := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, valuePhaseCoeff]
  congr 1
  push_cast
  field_simp

/-- Expresses the value phase coefficient as `exp (2πi a.val / Q)`. -/
theorem valuePhaseCoeff_exp_form (Q : ℕ) [NeZero Q] (a : ZMod Q) :
    valuePhaseCoeff Q a
      = Complex.exp (2 * Real.pi * Complex.I
          * (Complex.ofReal (((a.val : ℝ) / (Q : ℝ))))) := by
  rw [valuePhaseCoeff]
  congr 1
  push_cast
  ring

/-- The value phase coefficient sends addition in `ZMod Q` to multiplication in `ℂ`. -/
theorem valuePhaseCoeff_add (Q : ℕ) [NeZero Q] (a b : ZMod Q) :
    valuePhaseCoeff Q (a + b) = valuePhaseCoeff Q a * valuePhaseCoeff Q b := by
  rw [valuePhaseCoeff_eq_stdAddChar, valuePhaseCoeff_eq_stdAddChar, valuePhaseCoeff_eq_stdAddChar,
    AddChar.map_add_eq_mul]

/-- The diagonal value phase gate is unitary. -/
theorem valuePhaseGate_unitary (Q : ℕ) [NeZero Q] :
    valuePhaseGate Q ∈ Matrix.unitaryGroup (ZMod Q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [valuePhaseGate, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext y
  have hconj : conj (valuePhaseCoeff Q y)
      = Complex.exp (-(((2 * Real.pi * ((y.val : ℝ) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
    rw [valuePhaseCoeff, ← Complex.exp_conj]
    congr 1
    rw [map_mul conj, Complex.conj_ofReal, Complex.conj_I]
    ring
  show conj (valuePhaseCoeff Q y) * valuePhaseCoeff Q y = 1
  rw [hconj, valuePhaseCoeff, ← Complex.exp_add]
  have hz : -(((2 * Real.pi * ((y.val : ℝ) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I)
      + (((2 * Real.pi * ((y.val : ℝ) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I) = 0 := by ring
  rw [hz, Complex.exp_zero]

/-- The diagonal operator with entry `exp (2πi φ x)` at each basis index `x`. -/
noncomputable def dataPhaseOperator {X : Type} [DecidableEq X] (φ : X → ℝ) : Matrix X X ℂ :=
  Matrix.diagonal (fun x => Complex.exp (2 * Real.pi * Complex.I * (φ x : ℂ)))

/-- The adjoint-query circuit word consisting of a backward query, a value phase gate, and a
forward query. -/
noncomputable def valueAccessWord (X : Type) [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q] :
    List (AdjointStep (X × ZMod Q)) :=
  [.backward,
   .gate (TensorGate (1 : Matrix X X ℂ) (valuePhaseGate Q)),
   .forward]

/-- The tensor product of the data phase operator for `φ` and the value-register phase gate. -/
noncomputable def idealKickbackOperator {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (φ : X → ℝ) : Matrix (X × ZMod Q) (X × ZMod Q) ℂ :=
  TensorGate (dataPhaseOperator φ) (valuePhaseGate Q)

/-- Requires the table phase and `φ` to differ pointwise by at most `η` after subtracting a
suitable integer. -/
def TablePhaseError {X : Type} (Q : ℕ) [NeZero Q] (v : X → ZMod Q) (φ : X → ℝ) (η : ℝ) : Prop :=
  ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ η

/-- Extends a value table to a Boolean control, returning zero on the false branch. -/
def controlledValueTable {X : Type} (Q : ℕ) [NeZero Q] (v : X → ZMod Q) :
    Bool × X → ZMod Q :=
  fun p => if p.1 then v p.2 else 0

/-- Extends a real phase function to a Boolean control, returning zero on the false branch. -/
def controlledPhase {X : Type} (φ : X → ℝ) : Bool × X → ℝ :=
  fun p => if p.1 then φ p.2 else 0

/-- Applying a matrix product is the same as applying the right factor followed by the left
factor. -/
private theorem applyGate_mul' {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (ψ : QState I) :
    ApplyGate (A * B) ψ = ApplyGate A (ApplyGate B ψ) := by
  simp [ApplyGate, Matrix.mulVec_mulVec]

/-- Matrix application commutes with complex scalar multiplication of a state. -/
private theorem applyGate_smul' {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (c : ℂ) (ψ : QState I) : ApplyGate A (c • ψ) = c • ApplyGate A ψ := by
  funext i
  show (∑ j, A i j * (c * ψ j)) = c * (∑ j, A i j * ψ j)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A diagonal matrix acts on a basis ket by its corresponding diagonal entry. -/
private theorem applyGate_diagonal_ket {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → ℂ) (x : I) : ApplyGate (Matrix.diagonal d) (Ket x) = d x • Ket x := by
  funext i
  simp only [ApplyGate, Matrix.mulVec_diagonal, Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply,
    smul_eq_mul]
  by_cases h : i = x <;> simp [h]

/-- Tensoring two scalar multiples multiplies their scalars. -/
private theorem tensorState_smul_smul {I J : Type*} [Fintype I] [Fintype J] (a b : ℂ)
    (ψ : QState I) (φ : QState J) :
    TensorState (a • ψ) (b • φ) = (a * b) • TensorState ψ φ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

/-- The tensor product of the identity and a diagonal gate scales a basis ket by the second
register's diagonal entry. -/
private theorem tensorGate_one_diag_ket {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (d : J → ℂ) (x : I) (y : J) :
    ApplyGate (TensorGate (1 : Matrix I I ℂ) (Matrix.diagonal d))
      (Ket (x, y)) = d y • Ket (x, y) := by
  rw [← tensorState_ket_ket, applyGate_tensorGate, applyGate_one, applyGate_diagonal_ket]
  funext p
  rcases p with ⟨i, j⟩
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = x <;> by_cases hj : j = y
  <;> simp [Qatlib.Foundations.PureStateMath.Ket, hi, hj]

/-- The gradient value oracle is the additive oracle for the same table. -/
private theorem gradientValueOracle_eq_addOracle' {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (v : X → ZMod Q) : gradientValueOracle Q v = AddOracle v := by
  rw [addOracle_eq_permMatrix]
  ext x y
  simp [gradientValueOracle, permMatrix, addOracleEquiv, Prod.ext_iff]

/-- Matrices are equal if they act identically on every basis ket. -/
private theorem matrix_eq_of_forall_mulVec_ket {I : Type*} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (h : ∀ j, A *ᵥ (Ket j) = B *ᵥ (Ket j)) : A = B := by
  have hentry : ∀ (M : Matrix I I ℂ) (i j : I), (M *ᵥ Ket j) i = M i j := by
    intro M i j
    show ∑ k, M i k * Qatlib.Foundations.PureStateMath.Ket j k = M i j
    simp [Qatlib.Foundations.PureStateMath.Ket]
  ext i j
  have hij : (A *ᵥ Ket j) i = (B *ᵥ Ket j) i := congrFun (h j) i
  rw [hentry A i j, hentry B i j] at hij
  exact hij

/-- A basis ket has Euclidean norm one. -/
theorem toEuclidean_fromVec_ket_norm {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    ‖toEuclidean_fromVec (Ket i)‖ = 1 := by
  have hsq : ‖toEuclidean_fromVec (Ket i)‖ ^ 2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq, Finset.sum_eq_single i]
    · simp [Qatlib.Foundations.PureStateMath.Ket]
    · intro j _ hj
      simp [Qatlib.Foundations.PureStateMath.Ket, hj]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

/-- The value phase gate fixes the zero basis ket. -/
private theorem valuePhaseGate_ket_zero (Q : ℕ) [NeZero Q] :
    ApplyGate (valuePhaseGate Q) (Ket (0 : ZMod Q)) = Ket (0 : ZMod Q) := by
  rw [valuePhaseGate, applyGate_diagonal_ket]
  have h0 : valuePhaseCoeff Q (0 : ZMod Q) = 1 := by
    simp [valuePhaseCoeff]
  rw [h0, one_smul]

/-- The diagonal data phase operator associated with any real phase function is unitary. -/
theorem dataPhaseOperator_unitary {X : Type} [Fintype X] [DecidableEq X] (φ : X → ℝ) :
    dataPhaseOperator φ ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dataPhaseOperator,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext z
  change (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (φ z : ℂ)))
    * Complex.exp (2 * Real.pi * Complex.I * (φ z : ℂ)) = 1
  rw [Complex.conj_mul', norm_exp_two_pi_I]
  norm_num

/-- Evaluating the value-access word gives the tensor product of the table's data phase operator
and the value phase gate. -/
theorem valueAccessWord_executed {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) :
    evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
      = TensorGate (dataPhaseOperator (gradientValuePhase Q v)) (valuePhaseGate Q) := by
  have hcomp : evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
      = (gradientValueOracle Q v)ᴴ *
        (TensorGate (1 : Matrix X X ℂ) (valuePhaseGate Q) * (gradientValueOracle Q v)) := by
    simp [evaluate, instructionMatrix, valueAccessWord, Matrix.mul_one]
  rw [hcomp, gradientValueOracle_eq_addOracle', addOracle_conjTranspose]
  apply matrix_eq_of_forall_mulVec_ket
  rintro ⟨x, y⟩
  have h1 : ApplyGate (AddOracle v) (Ket (x, y)) = Ket (x, y + v x) :=
    applyGate_addOracle_ket v x y
  have h2 : ApplyGate (AddOracle (-v)) (Ket (x, y + v x)) = Ket (x, y) := by
    rw [applyGate_addOracle_ket]
    congr 1
    simp
  have h3 : ApplyGate (TensorGate (1 : Matrix X X ℂ) (valuePhaseGate Q)) (Ket (x, y + v x))
      = valuePhaseCoeff Q (y + v x) • Ket (x, y + v x) :=
    tensorGate_one_diag_ket (valuePhaseCoeff Q) x (y + v x)
  have hR : TensorGate (dataPhaseOperator (gradientValuePhase Q v)) (valuePhaseGate Q)
      *ᵥ (Ket (x, y))
      = (valuePhaseCoeff Q (v x) * valuePhaseCoeff Q y) • Ket (x, y) := by
    show ApplyGate _ _ = _
    rw [dataPhaseOperator, valuePhaseGate, ← tensorState_ket_ket, applyGate_tensorGate,
      applyGate_diagonal_ket _ x, applyGate_diagonal_ket _ y, tensorState_smul_smul,
      gradientValuePhase, ← valuePhaseCoeff_exp_form Q (v x)]
  show ApplyGate (AddOracle (-v) * (TensorGate (1 : Matrix X X ℂ) (valuePhaseGate Q)
      * AddOracle v)) (Ket (x, y)) = _
  rw [applyGate_mul', applyGate_mul', h1, h3, applyGate_smul', h2,
    valuePhaseCoeff_add Q y (v x), hR]
  congr 1
  ring

/-- The evaluated value-access word is unitary. -/
theorem valueAccessWord_unitary {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) :
    evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
      ∈ Matrix.unitaryGroup (X × ZMod Q) ℂ := by
  have hD : dataPhaseOperator (gradientValuePhase Q v)
      ∈ Matrix.unitaryGroup X ℂ := dataPhaseOperator_unitary _
  rw [valueAccessWord_executed]
  exact tensorGate_unitary hD (valuePhaseGate_unitary Q)

/-- The evaluated value-access word scales `Ket (x, y)` by the product of the phase coefficients
of `v x` and `y`. -/
theorem valueAccessWord_ket_clean {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) (x : X) (y : ZMod Q) :
    (evaluate (gradientValueOracle Q v) (valueAccessWord X Q)) *ᵥ (Ket (x, y))
      = (valuePhaseCoeff Q (v x) * valuePhaseCoeff Q y) • Ket (x, y) := by
  rw [valueAccessWord_executed]
  show ApplyGate (TensorGate (dataPhaseOperator (gradientValuePhase Q v)) (valuePhaseGate Q))
      (Ket (x, y)) = _
  rw [dataPhaseOperator, valuePhaseGate, ← tensorState_ket_ket, applyGate_tensorGate,
    applyGate_diagonal_ket _ x, applyGate_diagonal_ket _ y, tensorState_smul_smul,
    gradientValuePhase, ← valuePhaseCoeff_exp_form Q (v x)]

/-- On a zero value register, the value-access word applies the table's data phase operator and
returns that register to zero. -/
theorem valueAccessWord_data_clean {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) (ψ : QState X) :
    ApplyGate (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))
        (TensorState ψ (Ket (0 : ZMod Q)))
      = TensorState (ApplyGate (dataPhaseOperator (gradientValuePhase Q v)) ψ)
          (Ket (0 : ZMod Q)) := by
  rw [valueAccessWord_executed, applyGate_tensorGate, valuePhaseGate_ket_zero]

/-- The value-access word is well formed and uses exactly two oracle queries and one gate. -/
theorem valueAccessWord_resources {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q] :
    WellFormedAdjointCircuit (valueAccessWord X Q)
      ∧ adjointQueryCount (valueAccessWord X Q) = 2
      ∧ adjointGateCount (valueAccessWord X Q) = 1 := by
  refine ⟨?_, rfl, rfl⟩
  rw [valueAccessWord, WellFormedAdjointCircuit.backward_cons_iff,
    WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff]
  exact ⟨tensorGate_unitary (one_mem (Matrix.unitaryGroup _ ℂ)) (valuePhaseGate_unitary Q),
    WellFormedAdjointCircuit.nil⟩

/-- Adding an integer-valued function to the phase leaves the data phase operator unchanged. -/
theorem dataPhaseOperator_int_shift {X : Type} [DecidableEq X] (φ : X → ℝ) (k : X → ℤ) :
    dataPhaseOperator (fun x => φ x + (k x : ℝ)) = dataPhaseOperator φ := by
  unfold dataPhaseOperator
  congr 1
  funext x
  (try simp only [])
  rw [Complex.ofReal_add, mul_add, Complex.exp_add, exp_two_pi_I_int, mul_one]

/-- A pointwise phase difference bounded by a nonnegative `B` gives an operator norm difference
at most `2πB`. -/
theorem dataPhaseOperator_sub_norm_le {X : Type} [Fintype X] [DecidableEq X] (φ ψ : X → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (herror : ∀ x, |φ x - ψ x| ≤ B) :
    ‖dataPhaseOperator φ - dataPhaseOperator ψ‖ ≤ 2 * Real.pi * B := by
  rw [dataPhaseOperator, dataPhaseOperator, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * B)]
  intro z
  have he (t : ℝ) : (2 * Real.pi * Complex.I * (t : ℂ) : ℂ)
      = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, he]
  calc
    _ ≤ |2 * Real.pi * φ z - 2 * Real.pi * ψ z| := norm_exp_mul_I_sub_le _ _
    _ = 2 * Real.pi * |φ z - ψ z| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    _ ≤ 2 * Real.pi * B := mul_le_mul_of_nonneg_left (herror z) (by positivity)

/-- A table phase error at most a nonnegative `η` bounds the operator norm error of value
kickback by `2πη`. -/
theorem noisyValueKickbackOperatorError {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) (φ : X → ℝ) (η : ℝ) (hη : 0 ≤ η) (herr : TablePhaseError Q v φ η) :
    ‖evaluate (gradientValueOracle Q v) (valueAccessWord X Q) - idealKickbackOperator Q φ‖
      ≤ 2 * Real.pi * η := by
  classical
  set ψ : X → ℝ := fun x => gradientValuePhase Q v x
      + ↑(-((Classical.choose (herr x) : ℤ))) with hψ
  have hpoint : ∀ x, |ψ x - φ x| ≤ η := by
    intro x
    have h := abs_le.mp (Classical.choose_spec (herr x))
    rw [hψ]
    show |gradientValuePhase Q v x + ↑(-((Classical.choose (herr x) : ℤ))) - φ x| ≤ η
    simp only [Int.cast_neg]
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  have hshift : dataPhaseOperator ψ
      = dataPhaseOperator (gradientValuePhase Q v) := by
    rw [hψ]
    exact dataPhaseOperator_int_shift (gradientValuePhase Q v)
      (fun x => -(Classical.choose (herr x)))
  rw [valueAccessWord_executed]
  simp only [idealKickbackOperator]
  rw [tensorGate_sub_left, ← hshift, l2_norm_tensorGate]
  haveI : Nonempty (ZMod Q) := ⟨0⟩
  rw [l2_norm_unitary_eq_one (valuePhaseGate_unitary Q), mul_one]
  exact dataPhaseOperator_sub_norm_le ψ φ η hη hpoint

/-- On an input with a zero value register, value kickback has Euclidean state error at most
`2πη` times the Euclidean norm of the data state. -/
theorem noisyValueKickbackStateError {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) (φ : X → ℝ) (η : ℝ) (hη : 0 ≤ η) (herr : TablePhaseError Q v φ η)
    (ψ : QState X) :
    ‖toEuclidean_fromVec (ApplyGate (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))
          (TensorState ψ (Ket (0 : ZMod Q)))
        - ApplyGate (idealKickbackOperator Q φ) (TensorState ψ (Ket (0 : ZMod Q))))‖
      ≤ 2 * Real.pi * η * ‖toEuclidean_fromVec ψ‖ := by
  have hvec : ApplyGate (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))
        (TensorState ψ (Ket (0 : ZMod Q)))
      - ApplyGate (idealKickbackOperator Q φ) (TensorState ψ (Ket (0 : ZMod Q)))
      = (evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
          - idealKickbackOperator Q φ) *ᵥ (TensorState ψ (Ket (0 : ZMod Q))) := by
    rw [Matrix.sub_mulVec]
    rfl
  rw [hvec]
  have h1 := l2_norm_mulVec_fromVec_le
    (evaluate (gradientValueOracle Q v) (valueAccessWord X Q) - idealKickbackOperator Q φ)
    (TensorState ψ (Ket (0 : ZMod Q)))
  rw [tensorState_l2_norm, toEuclidean_fromVec_ket_norm, mul_one] at h1
  have hop := noisyValueKickbackOperatorError Q v φ η hη herr
  calc
    ‖toEuclidean_fromVec ((evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
          - idealKickbackOperator Q φ) *ᵥ (TensorState ψ (Ket (0 : ZMod Q))))‖
        ≤ ‖evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
            - idealKickbackOperator Q φ‖ * ‖toEuclidean_fromVec ψ‖ := h1
    _ ≤ 2 * Real.pi * η * ‖toEuclidean_fromVec ψ‖ :=
        mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- The adjoint value-access word is well formed and uses exactly two queries and one gate. -/
theorem valueAccessWord_adjoint_resources {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] :
    WellFormedAdjointCircuit (adjointCircuit (valueAccessWord X Q))
      ∧ adjointQueryCount (adjointCircuit (valueAccessWord X Q)) = 2
      ∧ adjointGateCount (adjointCircuit (valueAccessWord X Q)) = 1 := by
  have hgate : (TensorGate (1 : Matrix X X ℂ) (valuePhaseGate Q))ᴴ
      ∈ Matrix.unitaryGroup (X × ZMod Q) ℂ :=
    Unitary.star_mem (tensorGate_unitary (one_mem (Matrix.unitaryGroup _ ℂ))
      (valuePhaseGate_unitary Q))
  refine ⟨?_, ?_, ?_⟩
  · have hlist : adjointCircuit (valueAccessWord X Q)
        = [AdjointStep.backward,
           AdjointStep.gate ((TensorGate (1 : Matrix X X ℂ) (valuePhaseGate Q))ᴴ),
           AdjointStep.forward] := by
      simp [valueAccessWord,
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit,
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointInstruction]
    rw [hlist, WellFormedAdjointCircuit.backward_cons_iff,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff]
    exact ⟨hgate, WellFormedAdjointCircuit.nil⟩
  · rw [adjointQueryCount_adjointCircuit]
    rfl
  · rw [adjointGateCount_adjointCircuit]
    rfl

/-- Evaluating the adjoint word gives the conjugate transpose of the evaluated word, with
operator norm error at most `2πη` from the ideal adjoint. -/
theorem noisyValueKickbackAdjointAccess {X : Type} [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) (φ : X → ℝ) (η : ℝ) (hη : 0 ≤ η) (herr : TablePhaseError Q v φ η) :
    evaluate (gradientValueOracle Q v) (adjointCircuit (valueAccessWord X Q))
      = (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))ᴴ
      ∧ ‖evaluate (gradientValueOracle Q v) (adjointCircuit (valueAccessWord X Q))
          - (idealKickbackOperator Q φ)ᴴ‖ ≤ 2 * Real.pi * η := by
  have h1 : evaluate (gradientValueOracle Q v) (adjointCircuit (valueAccessWord X Q))
      = (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))ᴴ :=
    evaluate_adjointCircuit _ _
  refine ⟨h1, ?_⟩
  rw [h1, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  exact noisyValueKickbackOperatorError Q v φ η hη herr

/-- Adding a Boolean control preserves the table phase error bound when `η` is nonnegative. -/
theorem controlled_table_error {X : Type} (Q : ℕ) [NeZero Q] (v : X → ZMod Q) (φ : X → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (herr : TablePhaseError Q v φ η) :
    TablePhaseError Q (controlledValueTable Q v) (controlledPhase φ) η := by
  intro p
  rcases p with ⟨b, x⟩
  cases b
  · refine ⟨0, ?_⟩
    have h0 : gradientValuePhase Q (controlledValueTable Q v) (false, x)
        = controlledPhase φ (false, x) := by
      simp [controlledValueTable, controlledPhase, gradientValuePhase]
    rw [h0]
    norm_num
    exact hη
  · exact herr x

/-- The controlled value oracle fixes every basis ket on the false control branch. -/
theorem controlledValueOracle_uncontrolled_ket {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (v : X → ZMod Q) (x : X) (y : ZMod Q) :
    ApplyGate (gradientValueOracle Q (controlledValueTable Q v)) (Ket ((false, x), y))
      = Ket ((false, x), y) := by
  rw [gradientValueOracle_eq_addOracle', applyGate_addOracle_ket]
  simp [controlledValueTable]

/-- The controlled data phase operator has diagonal entry one on the false branch and the
original phase entry on the true branch. -/
theorem controlled_data_phase_entries {X : Type} [DecidableEq X] (Q : ℕ) [NeZero Q]
    (φ : X → ℝ) (x : X) :
    dataPhaseOperator (controlledPhase φ) (false, x) (false, x) = 1
      ∧ dataPhaseOperator (controlledPhase φ) (true, x) (true, x)
        = dataPhaseOperator φ x x := by
  constructor
  · simp [dataPhaseOperator, Matrix.diagonal_apply, controlledPhase]
  · simp [dataPhaseOperator, Matrix.diagonal_apply, controlledPhase]

/-- The Boolean-controlled value-access word approximates the ideal controlled kickback operator
with operator norm error at most `2πη`. -/
theorem noisyValueKickbackControlledAccess {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (v : X → ZMod Q) (φ : X → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (herr : TablePhaseError Q v φ η) :
    ‖evaluate (gradientValueOracle Q (controlledValueTable Q v))
        (valueAccessWord (Bool × X) Q)
      - idealKickbackOperator Q (controlledPhase φ)‖ ≤ 2 * Real.pi * η :=
  noisyValueKickbackOperatorError Q (controlledValueTable Q v) (controlledPhase φ) η hη
    (controlled_table_error Q v φ η hη herr)

/-- On the gradient grid, the value-access word agrees with the compute-kickback-uncompute word. -/
theorem valueAccessWord_eq_continuation (d M : ℕ) (Q : ℕ) [NeZero Q] :
    valueAccessWord (GradientGrid d M) Q
      = valueComputeKickbackUncomputeWord d M Q := rfl

/-- On the gradient grid, the data phase operator equals `gradientPhase`. -/
theorem dataPhaseOperator_eq_gradientPhase (d M : ℕ) (φ : GradientGrid d M → ℝ) :
    dataPhaseOperator φ = Qatlib.Concepts.SignalPrimitive.GridGradient.gradientPhase d M φ := rfl

/-- Collects exact value kickback, clean-register behavior, query and gate counts, phase-error
estimates, adjoint and controlled access, and the gradient-grid identifications. -/
def noisy_value_phase_kickback_spec : Prop :=
  (∀ (X : Type) [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q] (v : X → ZMod Q),
      evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
        ∈ Matrix.unitaryGroup (X × ZMod Q) ℂ
      ∧ (∀ (x : X) (y : ZMod Q),
          (evaluate (gradientValueOracle Q v) (valueAccessWord X Q)) *ᵥ (Ket (x, y))
            = (valuePhaseCoeff Q (v x) * valuePhaseCoeff Q y) • Ket (x, y))
      ∧ (∀ ψ : QState X,
          ApplyGate (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))
              (TensorState ψ (Ket (0 : ZMod Q)))
            = TensorState (ApplyGate (dataPhaseOperator (gradientValuePhase Q v)) ψ)
                (Ket (0 : ZMod Q)))
      ∧ WellFormedAdjointCircuit (valueAccessWord X Q)
      ∧ adjointQueryCount (valueAccessWord X Q) = 2
      ∧ adjointGateCount (valueAccessWord X Q) = 1) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q] (v : X → ZMod Q)
      (φ : X → ℝ) (η : ℝ), 0 ≤ η → TablePhaseError Q v φ η →
      ‖evaluate (gradientValueOracle Q v) (valueAccessWord X Q)
        - idealKickbackOperator Q φ‖ ≤ 2 * Real.pi * η) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q] (v : X → ZMod Q)
      (φ : X → ℝ) (η : ℝ) (ψ : QState X), 0 ≤ η → TablePhaseError Q v φ η →
      ‖toEuclidean_fromVec (ApplyGate (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))
            (TensorState ψ (Ket (0 : ZMod Q)))
          - ApplyGate (idealKickbackOperator Q φ) (TensorState ψ (Ket (0 : ZMod Q))))‖
        ≤ 2 * Real.pi * η * ‖toEuclidean_fromVec ψ‖) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q] (v : X → ZMod Q)
      (φ : X → ℝ) (η : ℝ), 0 ≤ η → TablePhaseError Q v φ η →
      evaluate (gradientValueOracle Q v) (adjointCircuit (valueAccessWord X Q))
        = (evaluate (gradientValueOracle Q v) (valueAccessWord X Q))ᴴ
      ∧ ‖evaluate (gradientValueOracle Q v) (adjointCircuit (valueAccessWord X Q))
          - (idealKickbackOperator Q φ)ᴴ‖ ≤ 2 * Real.pi * η
      ∧ WellFormedAdjointCircuit (adjointCircuit (valueAccessWord X Q))
      ∧ adjointQueryCount (adjointCircuit (valueAccessWord X Q)) = 2
      ∧ adjointGateCount (adjointCircuit (valueAccessWord X Q)) = 1) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q] (v : X → ZMod Q)
      (φ : X → ℝ) (η : ℝ), 0 ≤ η → TablePhaseError Q v φ η →
      TablePhaseError Q (controlledValueTable Q v) (controlledPhase φ) η
      ∧ ‖evaluate (gradientValueOracle Q (controlledValueTable Q v))
          (valueAccessWord (Bool × X) Q)
        - idealKickbackOperator Q (controlledPhase φ)‖ ≤ 2 * Real.pi * η
      ∧ (∀ (x : X) (y : ZMod Q),
          ApplyGate (gradientValueOracle Q (controlledValueTable Q v)) (Ket ((false, x), y))
            = Ket ((false, x), y))
      ∧ (∀ x : X, dataPhaseOperator (controlledPhase φ) (false, x) (false, x) = 1
          ∧ dataPhaseOperator (controlledPhase φ) (true, x) (true, x)
            = dataPhaseOperator φ x x)) ∧
  (∀ (d M : ℕ) (Q : ℕ) [NeZero Q],
      valueAccessWord (GradientGrid d M) Q = valueComputeKickbackUncomputeWord d M Q
    ∧ ∀ (φ : GradientGrid d M → ℝ),
        dataPhaseOperator φ = Qatlib.Concepts.SignalPrimitive.GridGradient.gradientPhase d M φ)

/-- Establishes `noisy_value_phase_kickback_spec`, including exact execution and resource counts
together with noisy, adjoint, and controlled error bounds. -/
theorem frontier1 : noisy_value_phase_kickback_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ Q _ v
    exact ⟨valueAccessWord_unitary Q v, valueAccessWord_ket_clean Q v,
      valueAccessWord_data_clean Q v, (valueAccessWord_resources Q).1,
      (valueAccessWord_resources Q).2.1, (valueAccessWord_resources Q).2.2⟩
  · intro X _ _ Q _ v φ η hη herr
    exact noisyValueKickbackOperatorError Q v φ η hη herr
  · intro X _ _ Q _ v φ η ψ hη herr
    exact noisyValueKickbackStateError Q v φ η hη herr ψ
  · intro X _ _ Q _ v φ η hη herr
    exact ⟨(noisyValueKickbackAdjointAccess Q v φ η hη herr).1,
      (noisyValueKickbackAdjointAccess Q v φ η hη herr).2,
      (valueAccessWord_adjoint_resources Q).1,
      (valueAccessWord_adjoint_resources Q).2.1,
      (valueAccessWord_adjoint_resources Q).2.2⟩
  · intro X _ _ Q _ v φ η hη herr
    exact ⟨controlled_table_error Q v φ η hη herr,
      noisyValueKickbackControlledAccess Q v φ η hη herr,
      fun x y => controlledValueOracle_uncontrolled_ket Q v x y,
      fun x => controlled_data_phase_entries Q φ x⟩
  · intro d M Q _
    exact ⟨valueAccessWord_eq_continuation d M Q,
      fun φ => dataPhaseOperator_eq_gradientPhase d M φ⟩

end Qatlib.Concepts.ReferenceError.RefTraceError
