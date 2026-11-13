/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCoreDefs
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.SchattenDiamondDefs
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.MarkovBrothers
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ScopedOracleWorkspace
import Qatlib.Concepts.SharedAncilla.AncillaProduct.SharedAncillaUnitaryProduct
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Native padded phase programs

This module realizes scalar and wire-controlled dyadic phases using `LocalQFTGate` instructions
with one extra wire initialized to false. `paddedNativeFrame` embeds the data register, and the
seven-instruction words return the extra wire to its initial state while applying the desired
phase, using elementary phase-gate identities from [NielsenChuang2010].

The module proves execution, matrix, compression, and adjoint formulas for individual phases and
finite sequences, with exact gate counts. It also bounds frame error by scalar phase error and
records the absence of native instructions on a zero-width register.

## Main statements

* `padded_scalar_phase_compress` and `padded_controlled_phase_compress`: exact compressed phase
  implementations.
* `padded_scalar_sequence_cost` and `padded_controlled_sequence_cost`: zero queries and seven
  gates per phase, also for adjoints.
* `padded_scalar_sequence_frame_error` and `padded_controlled_sequence_frame_error`: frame error
  controlled by the phase-product error.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexInnerProductSpace

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Polynomial
open Polynomial in

/-- There is no local gate instruction on a zero-width register. -/
theorem zero_gate_impossible (g : LocalQFTGate 0) : False := by
  cases g with
  | h i => exact Fin.elim0 i
  | cp i _ _ _ => exact Fin.elim0 i
  | swap i _ => exact Fin.elim0 i
open Polynomial
open Polynomial in
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

/-- The register equivalence identifying a leading Boolean wire and an `n`-bit data register
with an `(n + 1)`-bit register. -/
def paddedNativeEquiv (n : ℕ) : (Bool × Reg n) ≃ Reg (n + 1) :=
  Fin.consEquiv (fun _ : Fin (n + 1) => Bool)

/-- The allocation frame embedding an `n`-bit data register into an `(n + 1)`-bit register with
a leading false wire. -/
noncomputable def paddedNativeFrame (n : ℕ) : Matrix (Reg (n + 1)) (Reg n) ℂ :=
  (scopedAllocationFrame n).submatrix (paddedNativeEquiv n).symm id

/-- The padded native allocation frame is an isometry. -/
theorem paddedNativeFrame_isometry (n : ℕ) : IsIsometry (paddedNativeFrame n) := by
  unfold IsIsometry paddedNativeFrame
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    scoped_allocationFrame_conjTranspose_mul, Matrix.submatrix_id_id]

/-- Applying the padded frame equals tensoring the input with a false basis state and relabeling
the resulting register. -/
theorem paddedNativeFrame_mulVec (n : ℕ) (ψ : QState (Reg n)) :
    paddedNativeFrame n *ᵥ ψ =
      relabelState (paddedNativeEquiv n) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) := by
  funext x
  exact congrFun (scoped_allocationFrame_mulVec ψ) ((paddedNativeEquiv n).symm x)

/-- The padded state has the original data amplitude when the leading bit is false and zero
amplitude when it is true. -/
theorem paddedNativeFrame_mulVec_cons (n : ℕ) (ψ : QState (Reg n)) (b : Bool) (x : Reg n) :
    (paddedNativeFrame n *ᵥ ψ) (Fin.cons b x) = if b then 0 else ψ x := by
  rw [paddedNativeFrame_mulVec]
  cases b <;> simp [relabelState, paddedNativeEquiv, Fin.consEquiv, TensorState,
      Qatlib.Foundations.PureStateMath.Ket]

/-- The padded native allocation frame preserves normalization of states. -/
theorem paddedNativeFrame_normalized (n : ℕ) {ψ : QState (Reg n)} (hψ : Normalized ψ) :
    Normalized (paddedNativeFrame n *ᵥ ψ) := by
  rw [paddedNativeFrame_mulVec]
  exact normalized_relabelState _ (normalized_tensorState (normalized_ket false) hψ)

/-- The three-instruction Hadamard-phase-Hadamard word implementing a bit flip on the leading
wire. -/
def nativeHeadX (n : ℕ) : List (LocalQFTGate (n + 1)) :=
  [.h 0, .cp 0 0 1 false, .h 0]

/-- The seven-instruction word placing a dyadic phase on the leading wire between two
leading-wire bit-flip words. -/
def paddedScalarPhaseWord (n k : ℕ) (neg : Bool) : List (LocalQFTGate (n + 1)) :=
  nativeHeadX n ++ [.cp 0 0 k neg] ++ nativeHeadX n

/-- The seven-instruction word placing a dyadic phase controlled by data wire `a` between two
leading-wire bit-flip words. -/
def paddedControlledPhaseWord (n : ℕ) (a : Fin n) (k : ℕ) (neg : Bool) :
    List (LocalQFTGate (n + 1)) :=
  nativeHeadX n ++ [.cp 0 a.succ k neg] ++ nativeHeadX n

/-- The local Hadamard on the leading wire equals the relabeled tensor product of a Hadamard and
the data identity. -/
private theorem native_head_h (n : ℕ) :
    localGateMatrix (LocalQFTGate.h (0 : Fin (n + 1))) =
      relabelGate (paddedNativeEquiv n)
        (TensorGate Hadamard (1 : Matrix (Reg n) (Reg n) ℂ)) := by
  ext x y
  have ht : (∀ k : Fin (n + 1), k ≠ 0 → x k = y k) ↔ Fin.tail x = Fin.tail y := by
    constructor
    · intro h; funext j; exact h j.succ (Fin.succ_ne_zero j)
    · intro h k hk
      cases k using Fin.cases with
      | zero => exact (hk rfl).elim
      | succ j => exact congrFun h j
  change (if ∀ k : Fin (n + 1), k ≠ 0 → x k = y k then Hadamard (x 0) (y 0) else 0) =
    Hadamard (x 0) (y 0) * (if Fin.tail x = Fin.tail y then 1 else 0)
  by_cases h : Fin.tail x = Fin.tail y <;> simp [ht, h]

/-- The dyadic phase with both wire labels zero equals the relabeled tensor product of the
corresponding ancilla phase and the data identity. -/
private theorem native_head_cp (n k : ℕ) (neg : Bool) :
    localGateMatrix (LocalQFTGate.cp (0 : Fin (n + 1)) 0 k neg) =
      relabelGate (paddedNativeEquiv n)
        (TensorGate (scopedAncillaPhase (Complex.exp (dyadicPhaseAngle k neg * Complex.I)))
          (1 : Matrix (Reg n) (Reg n) ℂ)) := by
  ext x y
  rw [localGateMatrix_cp]
  have hxy : x = y ↔ x 0 = y 0 ∧ Fin.tail x = Fin.tail y := by
    constructor
    · intro h; subst y; exact ⟨rfl,rfl⟩
    · intro h
      exact (paddedNativeEquiv n).symm.injective (Prod.ext h.1 h.2)
  by_cases hh : x 0 = y 0 <;> by_cases ht : Fin.tail x = Fin.tail y <;>
    simp [relabelGate, paddedNativeEquiv, Fin.consEquiv, TensorGate,
      scopedAncillaPhase, Matrix.diagonal, hxy, hh, ht, Bool.and_self]

/-- The positive dyadic phase of denominator two on the leading wire equals the relabeled
Pauli-Z tensor identity. -/
private theorem native_head_z (n : ℕ) :
    localGateMatrix (LocalQFTGate.cp (0 : Fin (n + 1)) 0 1 false) =
      relabelGate (paddedNativeEquiv n) (TensorGate PauliZ (1 : Matrix (Reg n) (Reg n) ℂ)) := by
  rw [native_head_cp]
  have hangle : dyadicPhaseAngle 1 false = Real.pi := by norm_num [dyadicPhaseAngle]
  rw [hangle, Complex.exp_pi_mul_I]
  rfl

/-- Conjugating Pauli-Z by the Hadamard matrix gives Pauli-X. -/
private theorem native_hzh : Hadamard * PauliZ * Hadamard = PauliX := by
  ext i j
  simp only [Hadamard, PauliZ, PauliX, permMatrix, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.of_apply, Fintype.sum_bool]
  cases i <;> cases j <;> simp <;> ring_nf <;> norm_num [sqrt2_sq]

/-- Running `nativeHeadX` flips the leading basis bit and preserves the data state under the
padded register relabeling. -/
private theorem nativeHeadX_run (n : ℕ) (b : Bool) (ψ : QState (Reg n)) :
    Run 1 (localProgramCircuit (nativeHeadX n))
      (relabelState (paddedNativeEquiv n) (TensorState (Qatlib.Foundations.PureStateMath.Ket b) ψ)) =
    relabelState (paddedNativeEquiv n) (TensorState (Qatlib.Foundations.PureStateMath.Ket (!b)) ψ) := by
  simp only [nativeHeadX, localProgramCircuit, List.map_cons, List.map_nil, run_gate, run_nil]
  rw [native_head_h, native_head_z]
  simp only [applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  rw [← applyGate_mul, ← applyGate_mul, native_hzh, applyGate_pauliX_ket]

/-- On a leading true basis state, the leading-wire dyadic phase multiplies the data state by
its scalar phase factor. -/
private theorem native_head_cp_true (n k : ℕ) (neg : Bool) (ψ : QState (Reg n)) :
    ApplyGate (localGateMatrix (.cp (0 : Fin (n + 1)) 0 k neg))
      (relabelState (paddedNativeEquiv n) (TensorState (Qatlib.Foundations.PureStateMath.Ket true) ψ)) =
    relabelState (paddedNativeEquiv n) (TensorState (Qatlib.Foundations.PureStateMath.Ket true)
      (Complex.exp (dyadicPhaseAngle k neg * Complex.I) • ψ)) := by
  rw [native_head_cp, applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  funext x
  cases h : ((paddedNativeEquiv n).symm x).1 <;>
    simp [ApplyGate, scopedAncillaPhase, Matrix.mulVec_diagonal, TensorState, Qatlib.Foundations.PureStateMath.Ket,
      relabelState, Pi.smul_apply, smul_eq_mul, h]

/-- On a leading true basis state, the dyadic phase between the leading wire and data wire `a`
applies the corresponding scoped phase to the data. -/
private theorem native_control_cp_true (n : ℕ) (a : Fin n) (k : ℕ) (neg : Bool)
    (ψ : QState (Reg n)) :
    ApplyGate (localGateMatrix (.cp (0 : Fin (n + 1)) a.succ k neg))
      (relabelState (paddedNativeEquiv n) (TensorState (Qatlib.Foundations.PureStateMath.Ket true) ψ)) =
    relabelState (paddedNativeEquiv n) (TensorState (Qatlib.Foundations.PureStateMath.Ket true)
      (ApplyGate (scopedPhaseGate (fun x => x a)
        (Complex.exp (dyadicPhaseAngle k neg * Complex.I))) ψ)) := by
  funext x
  simp only [ApplyGate, localGateMatrix, Matrix.mulVec_diagonal, relabelState,
    paddedNativeEquiv, Fin.consEquiv, TensorState, Qatlib.Foundations.PureStateMath.Ket, Function.comp_apply,
    scopedPhaseGate]
  cases h : x 0 <;> simp [h, Fin.tail]

/-- Running a singleton local instruction program applies its instruction matrix. -/
private theorem native_singleton_run {n : ℕ} (g : LocalQFTGate n) (ψ : QState (Reg n)) :
    Run 1 (localProgramCircuit [g]) ψ = ApplyGate (localGateMatrix g) ψ := by
  simp [localProgramCircuit]

/-- On a padded input, the scalar phase word applies the dyadic scalar to the data state and
restores the padding. -/
theorem padded_scalar_phase_run (n k : ℕ) (neg : Bool) (ψ : QState (Reg n)) :
    Run 1 (localProgramCircuit (paddedScalarPhaseWord n k neg)) (paddedNativeFrame n *ᵥ ψ) =
    paddedNativeFrame n *ᵥ (Complex.exp (dyadicPhaseAngle k neg * Complex.I) • ψ) := by
  rw [paddedNativeFrame_mulVec, paddedNativeFrame_mulVec]
  simp only [paddedScalarPhaseWord, localProgramCircuit_append, run_append]
  rw [nativeHeadX_run]
  simp only [Bool.not_false]
  rw [native_singleton_run, native_head_cp_true]
  exact nativeHeadX_run n true _

/-- On a padded input, the controlled phase word applies the dyadic scoped phase on data wire
`a` and restores the padding. -/
theorem padded_controlled_phase_run (n : ℕ) (a : Fin n) (k : ℕ) (neg : Bool)
    (ψ : QState (Reg n)) :
    Run 1 (localProgramCircuit (paddedControlledPhaseWord n a k neg))
      (paddedNativeFrame n *ᵥ ψ) =
    paddedNativeFrame n *ᵥ (ApplyGate (scopedPhaseGate (fun x => x a)
      (Complex.exp (dyadicPhaseAngle k neg * Complex.I))) ψ) := by
  rw [paddedNativeFrame_mulVec, paddedNativeFrame_mulVec]
  simp only [paddedControlledPhaseWord, localProgramCircuit_append, run_append]
  rw [nativeHeadX_run]
  simp only [Bool.not_false]
  rw [native_singleton_run, native_control_cp_true]
  exact nativeHeadX_run n true _

/-- Agreement of a local program with `V` on every padded state implies the matrix relation
intertwining the program with the padded frame. -/
private theorem native_frame_matrix_of_run (n : ℕ) (gs : List (LocalQFTGate (n + 1)))
    (V : Matrix (Reg n) (Reg n) ℂ)
    (h : ∀ ψ : QState (Reg n),
      Run 1 (localProgramCircuit gs) (paddedNativeFrame n *ᵥ ψ) =
        paddedNativeFrame n *ᵥ (V *ᵥ ψ)) :
    localProgramMatrix gs * paddedNativeFrame n = paddedNativeFrame n * V := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hh := h ψ
  rw [(localDyadicProgram_run_adjoint_cost (n + 1) gs (paddedNativeFrame n *ᵥ ψ)).1] at hh
  exact hh

/-- The scalar phase program intertwines the padded frame with the corresponding scalar multiple
of identity. -/
theorem padded_scalar_phase_matrix (n k : ℕ) (neg : Bool) :
    localProgramMatrix (paddedScalarPhaseWord n k neg) * paddedNativeFrame n =
      paddedNativeFrame n *
        (Complex.exp (dyadicPhaseAngle k neg * Complex.I) • (1 : Matrix (Reg n) (Reg n) ℂ)) := by
  apply native_frame_matrix_of_run
  intro ψ
  simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using padded_scalar_phase_run n k neg ψ

/-- The controlled phase program intertwines the padded frame with the corresponding scoped data
phase. -/
theorem padded_controlled_phase_matrix (n : ℕ) (a : Fin n) (k : ℕ) (neg : Bool) :
    localProgramMatrix (paddedControlledPhaseWord n a k neg) * paddedNativeFrame n =
      paddedNativeFrame n * scopedPhaseGate (fun x => x a)
        (Complex.exp (dyadicPhaseAngle k neg * Complex.I)) := by
  exact native_frame_matrix_of_run n _ _ (padded_controlled_phase_run n a k neg)

/-- If a local program intertwines the padded frame with `V` and `V * Vᴴ = 1`, its adjoint
program intertwines the frame with `Vᴴ`. -/
private theorem native_frame_adjoint_matrix {n : ℕ} (gs : List (LocalQFTGate (n + 1)))
    (V : Matrix (Reg n) (Reg n) ℂ) (hV : V * Vᴴ = 1)
    (h : localProgramMatrix gs * paddedNativeFrame n = paddedNativeFrame n * V) :
    localProgramMatrix (localProgramAdjoint gs) * paddedNativeFrame n = paddedNativeFrame n * Vᴴ := by
  obtain ⟨_, hadj, _, _, hU, _⟩ :=
    localDyadicProgram_run_adjoint_cost (n + 1) gs (0 : QState (Reg (n + 1)))
  rw [hadj]
  have hM : (localProgramMatrix gs)ᴴ * localProgramMatrix gs = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    _ = (localProgramMatrix gs)ᴴ * paddedNativeFrame n * (V * Vᴴ) := by rw [hV, Matrix.mul_one]
    _ = ((localProgramMatrix gs)ᴴ * (paddedNativeFrame n * V)) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    _ = paddedNativeFrame n * Vᴴ := by
      rw [← h, ← Matrix.mul_assoc, hM, Matrix.one_mul]

/-- A dyadic phase factor multiplied by its complex conjugate equals one. -/
private theorem native_dyadic_mul_star (k : ℕ) (neg : Bool) :
    Complex.exp (dyadicPhaseAngle k neg * Complex.I) *
      star (Complex.exp (dyadicPhaseAngle k neg * Complex.I)) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- If `z * star z = 1`, the matrix `z • 1` multiplied by its adjoint equals identity. -/
private theorem native_scalar_mul_star (n : ℕ) (z : ℂ) (hz : z * star z = 1) :
    (z • (1 : Matrix (Reg n) (Reg n) ℂ)) * (z • (1 : Matrix (Reg n) (Reg n) ℂ))ᴴ = 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_assoc, mul_smul_comm,
    Matrix.one_mul, smul_smul, hz, one_smul]

/-- If `z * star z = 1`, the scoped phase controlled by data wire `a` multiplied by its adjoint
equals identity. -/
private theorem native_control_mul_star (n : ℕ) (a : Fin n) (z : ℂ) (hz : z * star z = 1) :
    let V := scopedPhaseGate (fun x => x a) z
    V * Vᴴ = 1 := by
  (try dsimp only)
  rw [scopedPhaseGate, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    cases hx : x a <;> simp [Matrix.diagonal, hx]
    exact hz
  · simp [Matrix.diagonal, hxy]

/-- The adjoint scalar phase program intertwines the padded frame with the adjoint scalar
identity matrix. -/
theorem padded_scalar_phase_adjoint_matrix (n k : ℕ) (neg : Bool) :
    localProgramMatrix (localProgramAdjoint (paddedScalarPhaseWord n k neg)) * paddedNativeFrame n =
      paddedNativeFrame n *
        (Complex.exp (dyadicPhaseAngle k neg * Complex.I) • (1 : Matrix (Reg n) (Reg n) ℂ))ᴴ :=
  native_frame_adjoint_matrix _ _ (native_scalar_mul_star n _ (native_dyadic_mul_star k neg)) (padded_scalar_phase_matrix n k neg)

/-- The adjoint controlled phase program intertwines the padded frame with the adjoint scoped
phase matrix. -/
theorem padded_controlled_phase_adjoint_matrix (n : ℕ) (a : Fin n) (k : ℕ) (neg : Bool) :
    localProgramMatrix (localProgramAdjoint (paddedControlledPhaseWord n a k neg)) * paddedNativeFrame n =
      paddedNativeFrame n *
        (scopedPhaseGate (fun x => x a) (Complex.exp (dyadicPhaseAngle k neg * Complex.I)))ᴴ :=
  native_frame_adjoint_matrix _ _ (native_control_mul_star n a _ (native_dyadic_mul_star k neg))
    (padded_controlled_phase_matrix n a k neg)

/-- Compressing the padded scalar phase program along the padded frame gives the dyadic phase
factor times identity. -/
theorem padded_scalar_phase_compress (n k : ℕ) (neg : Bool) :
    compress (paddedNativeFrame n) (localProgramMatrix (paddedScalarPhaseWord n k neg))
      (paddedNativeFrame n) =
        Complex.exp (dyadicPhaseAngle k neg * Complex.I) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  unfold compress
  rw [Matrix.mul_assoc, padded_scalar_phase_matrix, ← Matrix.mul_assoc,
    show (paddedNativeFrame n)ᴴ * paddedNativeFrame n = 1 from paddedNativeFrame_isometry n,
    Matrix.one_mul]

/-- Compressing the padded controlled phase program along the padded frame gives the scoped
dyadic phase on data wire `a`. -/
theorem padded_controlled_phase_compress (n : ℕ) (a : Fin n) (k : ℕ) (neg : Bool) :
    compress (paddedNativeFrame n) (localProgramMatrix (paddedControlledPhaseWord n a k neg))
      (paddedNativeFrame n) =
        scopedPhaseGate (fun x => x a) (Complex.exp (dyadicPhaseAngle k neg * Complex.I)) := by
  unfold compress
  rw [Matrix.mul_assoc, padded_controlled_phase_matrix, ← Matrix.mul_assoc,
    show (paddedNativeFrame n)ᴴ * paddedNativeFrame n = 1 from paddedNativeFrame_isometry n,
    Matrix.one_mul]

/-- The padded scalar phase word has length seven and defines a unitary zero-query circuit with
seven gates in both the forward and adjoint programs. -/
theorem padded_phase_cost (n k : ℕ) (neg : Bool) :
    (paddedScalarPhaseWord n k neg).length = 7 ∧
    QueryCount (localProgramCircuit (paddedScalarPhaseWord n k neg)) = 0 ∧
    GateCount (localProgramCircuit (paddedScalarPhaseWord n k neg)) = 7 ∧
    GateCount (localProgramCircuit (localProgramAdjoint (paddedScalarPhaseWord n k neg))) = 7 ∧
    IsUnitaryCircuit (localProgramCircuit (paddedScalarPhaseWord n k neg)) := by
  obtain ⟨_, _, _, hu, _, hq, hg, hgi, _⟩ :=
    localDyadicProgram_run_adjoint_cost (n + 1) (paddedScalarPhaseWord n k neg) 0
  have hl : (paddedScalarPhaseWord n k neg).length = 7 := by
    simp [paddedScalarPhaseWord, nativeHeadX]
  exact ⟨hl, hq, hg.trans hl, hgi.trans hl, hu⟩

/-- The padded controlled phase word has length seven and defines a unitary zero-query circuit
with seven gates in both the forward and adjoint programs. -/
theorem padded_controlled_phase_cost (n : ℕ) (a : Fin n) (k : ℕ) (neg : Bool) :
    (paddedControlledPhaseWord n a k neg).length = 7 ∧
    QueryCount (localProgramCircuit (paddedControlledPhaseWord n a k neg)) = 0 ∧
    GateCount (localProgramCircuit (paddedControlledPhaseWord n a k neg)) = 7 ∧
    GateCount (localProgramCircuit (localProgramAdjoint (paddedControlledPhaseWord n a k neg))) = 7 ∧
    IsUnitaryCircuit (localProgramCircuit (paddedControlledPhaseWord n a k neg)) := by
  obtain ⟨_, _, _, hu, _, hq, hg, hgi, _⟩ :=
    localDyadicProgram_run_adjoint_cost (n + 1) (paddedControlledPhaseWord n a k neg) 0
  have hl : (paddedControlledPhaseWord n a k neg).length = 7 := by
    simp [paddedControlledPhaseWord, nativeHeadX]
  exact ⟨hl, hq, hg.trans hl, hgi.trans hl, hu⟩

/-- Every instruction of the padded minus-one scalar word is either the leading Hadamard or the
positive denominator-two phase on the leading wire. -/
theorem padded_neg_one_fixed_labels (n : ℕ) :
    ∀ g ∈ paddedScalarPhaseWord n 1 false,
      g = LocalQFTGate.h 0 ∨ g = LocalQFTGate.cp 0 0 1 false := by
  intro g hg
  simp [paddedScalarPhaseWord, nativeHeadX] at hg
  aesop

/-- Every instruction of the padded controlled minus-one word is a leading Hadamard or a
positive denominator-two phase on the leading wire or its pair with data wire `a`. -/
theorem padded_controlled_neg_one_fixed_labels (n : ℕ) (a : Fin n) :
    ∀ g ∈ paddedControlledPhaseWord n a 1 false,
      g = LocalQFTGate.h 0 ∨ g = LocalQFTGate.cp 0 0 1 false ∨
        g = LocalQFTGate.cp 0 a.succ 1 false := by
  intro g hg
  simp [paddedControlledPhaseWord, nativeHeadX] at hg
  aesop

/-- The positive denominator-two scalar phase program compresses to minus identity on the data
register. -/
theorem padded_neg_one_compress (n : ℕ) :
    compress (paddedNativeFrame n) (localProgramMatrix (paddedScalarPhaseWord n 1 false))
      (paddedNativeFrame n) = -(1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [padded_scalar_phase_compress]
  have hangle : dyadicPhaseAngle 1 false = Real.pi := by norm_num [dyadicPhaseAngle]
  rw [hangle, Complex.exp_pi_mul_I, neg_one_smul]

/-- Every local instruction list on a zero-width register is empty. -/
theorem native_zero_word_nil (gs : List (LocalQFTGate 0)) : gs = [] := by
  cases gs with
  | nil => rfl
  | cons g _ => exact (zero_gate_impossible g).elim

/-- Concatenates padded scalar phase words for a list of dyadic denominator and sign pairs. -/
def paddedScalarPhaseSequenceWord (n : ℕ) : List (ℕ × Bool) → List (LocalQFTGate (n + 1))
  | [] => []
  | p :: ps => paddedScalarPhaseWord n p.1 p.2 ++ paddedScalarPhaseSequenceWord n ps
/-- Concatenates padded phase words controlled by the same data wire for a list of dyadic
denominator and sign pairs. -/
def paddedControlledPhaseSequenceWord (n : ℕ) (a : Fin n) :
    List (ℕ × Bool) → List (LocalQFTGate (n + 1))
  | [] => []
  | p :: ps => paddedControlledPhaseWord n a p.1 p.2 ++ paddedControlledPhaseSequenceWord n a ps
/-- The product of the complex dyadic phase factors specified by a list of denominator and sign
pairs. -/
noncomputable def paddedPhaseProduct (ps : List (ℕ × Bool)) : ℂ :=
  (ps.map fun p => Complex.exp (dyadicPhaseAngle p.1 p.2 * Complex.I)).prod

/-- Multiplying two scoped phase matrices with the same Boolean predicate multiplies their phase
parameters. -/
private theorem native_phase_gate_mul (n : ℕ) (f : Reg n → Bool) (z w : ℂ) :
    scopedPhaseGate f z * scopedPhaseGate f w = scopedPhaseGate f (z * w) := by
  unfold scopedPhaseGate
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  cases hx : f x <;> simp

/-- On a padded state, the scalar phase sequence multiplies the data state by
`paddedPhaseProduct ps` and restores the padding. -/
theorem padded_scalar_sequence_run (n : ℕ) (ps : List (ℕ × Bool)) (ψ : QState (Reg n)) :
    Run 1 (localProgramCircuit (paddedScalarPhaseSequenceWord n ps)) (paddedNativeFrame n *ᵥ ψ) =
      paddedNativeFrame n *ᵥ (paddedPhaseProduct ps • ψ) := by
  induction ps generalizing ψ with
  | nil => simp [paddedScalarPhaseSequenceWord, paddedPhaseProduct, localProgramCircuit]
  | cons p ps ih =>
    rw [paddedScalarPhaseSequenceWord, localProgramCircuit_append, run_append,
      padded_scalar_phase_run, ih]
    simp only [paddedPhaseProduct, List.map_cons, List.prod_cons, smul_smul]
    congr 2
    ring

/-- On a padded state, the controlled phase sequence applies the scoped phase with parameter
`paddedPhaseProduct ps` and restores the padding. -/
theorem padded_controlled_sequence_run (n : ℕ) (a : Fin n) (ps : List (ℕ × Bool))
    (ψ : QState (Reg n)) :
    Run 1 (localProgramCircuit (paddedControlledPhaseSequenceWord n a ps))
      (paddedNativeFrame n *ᵥ ψ) =
    paddedNativeFrame n *ᵥ (ApplyGate (scopedPhaseGate (fun x => x a) (paddedPhaseProduct ps)) ψ) := by
  induction ps generalizing ψ with
  | nil =>
    have h1 : scopedPhaseGate (fun x : Reg n => x a) 1 = 1 := by
      ext x y
      simp [scopedPhaseGate, Matrix.diagonal, Matrix.one_apply]
    simp [paddedControlledPhaseSequenceWord, paddedPhaseProduct, localProgramCircuit, h1,
        applyGate_one]
  | cons p ps ih =>
    rw [paddedControlledPhaseSequenceWord, localProgramCircuit_append, run_append,
      padded_controlled_phase_run, ih, ← applyGate_mul, native_phase_gate_mul]
    simp only [paddedPhaseProduct, List.map_cons, List.prod_cons]
    congr 3
    ring

/-- The scalar phase sequence intertwines the padded frame with `paddedPhaseProduct ps` times
identity. -/
theorem padded_scalar_sequence_matrix (n : ℕ) (ps : List (ℕ × Bool)) :
    localProgramMatrix (paddedScalarPhaseSequenceWord n ps) * paddedNativeFrame n =
      paddedNativeFrame n * (paddedPhaseProduct ps • (1 : Matrix (Reg n) (Reg n) ℂ)) := by
  apply native_frame_matrix_of_run
  intro ψ
  simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using padded_scalar_sequence_run n ps ψ

/-- The controlled phase sequence intertwines the padded frame with the scoped phase of
parameter `paddedPhaseProduct ps`. -/
theorem padded_controlled_sequence_matrix (n : ℕ) (a : Fin n) (ps : List (ℕ × Bool)) :
    localProgramMatrix (paddedControlledPhaseSequenceWord n a ps) * paddedNativeFrame n =
      paddedNativeFrame n * scopedPhaseGate (fun x => x a) (paddedPhaseProduct ps) :=
  native_frame_matrix_of_run n _ _ (padded_controlled_sequence_run n a ps)

/-- Both scalar and controlled padded phase sequences have length seven times the number of
phase specifications. -/
theorem padded_phase_sequence_lengths (n : ℕ) (ps : List (ℕ × Bool)) :
    (paddedScalarPhaseSequenceWord n ps).length = 7 * ps.length ∧
      ∀ a : Fin n, (paddedControlledPhaseSequenceWord n a ps).length = 7 * ps.length := by
  induction ps with
  | nil => simp [paddedScalarPhaseSequenceWord, paddedControlledPhaseSequenceWord]
  | cons p ps ih =>
    constructor
    · simp only [paddedScalarPhaseSequenceWord, List.length_append, List.length_cons,
        (padded_phase_cost n p.1 p.2).1, ih.1]
      omega
    · intro a
      simp only [paddedControlledPhaseSequenceWord, List.length_append, List.length_cons,
        (padded_controlled_phase_cost n a p.1 p.2).1, ih.2 a]
      omega

/-- The product of dyadic phase factors multiplied by its conjugate equals one. -/
private theorem paddedPhaseProduct_mul_star (ps : List (ℕ × Bool)) :
    paddedPhaseProduct ps * star (paddedPhaseProduct ps) = 1 := by
  induction ps with
  | nil => simp [paddedPhaseProduct]
  | cons p ps ih =>
    change (_ * paddedPhaseProduct ps) * star (_ * paddedPhaseProduct ps) = 1
    rw [star_mul]
    calc
      _ = Complex.exp (dyadicPhaseAngle p.1 p.2 * Complex.I) *
          (paddedPhaseProduct ps * star (paddedPhaseProduct ps)) *
          star (Complex.exp (dyadicPhaseAngle p.1 p.2 * Complex.I)) := by ring
      _ = 1 := by rw [ih, mul_one, native_dyadic_mul_star]

/-- The adjoint scalar phase sequence intertwines the padded frame with the adjoint of its
scalar identity matrix. -/
theorem padded_scalar_sequence_adjoint_matrix (n : ℕ) (ps : List (ℕ × Bool)) :
    localProgramMatrix (localProgramAdjoint (paddedScalarPhaseSequenceWord n ps)) * paddedNativeFrame n =
      paddedNativeFrame n * (paddedPhaseProduct ps • (1 : Matrix (Reg n) (Reg n) ℂ))ᴴ :=
  native_frame_adjoint_matrix _ _ (native_scalar_mul_star n _ (paddedPhaseProduct_mul_star ps))
    (padded_scalar_sequence_matrix n ps)

/-- The adjoint controlled phase sequence intertwines the padded frame with the adjoint scoped
phase matrix. -/
theorem padded_controlled_sequence_adjoint_matrix (n : ℕ) (a : Fin n) (ps : List (ℕ × Bool)) :
    localProgramMatrix (localProgramAdjoint (paddedControlledPhaseSequenceWord n a ps)) * paddedNativeFrame n =
      paddedNativeFrame n * (scopedPhaseGate (fun x => x a) (paddedPhaseProduct ps))ᴴ :=
  native_frame_adjoint_matrix _ _ (native_control_mul_star n a _ (paddedPhaseProduct_mul_star ps))
    (padded_controlled_sequence_matrix n a ps)

/-- A matrix intertwining the padded frame with `V` compresses along that frame to `V`. -/
private theorem native_frame_compression (n : ℕ) (M : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
    (V : Matrix (Reg n) (Reg n) ℂ) (h : M * paddedNativeFrame n = paddedNativeFrame n * V) :
    compress (paddedNativeFrame n) M (paddedNativeFrame n) = V := by
  unfold compress
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc,
    show (paddedNativeFrame n)ᴴ * paddedNativeFrame n = 1 from paddedNativeFrame_isometry n,
    Matrix.one_mul]

/-- Compressing a padded scalar phase sequence gives `paddedPhaseProduct ps` times identity. -/
theorem padded_scalar_sequence_compress (n : ℕ) (ps : List (ℕ × Bool)) :
    compress (paddedNativeFrame n) (localProgramMatrix (paddedScalarPhaseSequenceWord n ps))
      (paddedNativeFrame n) = paddedPhaseProduct ps • (1 : Matrix (Reg n) (Reg n) ℂ) :=
  native_frame_compression n _ _ (padded_scalar_sequence_matrix n ps)

/-- Compressing a padded controlled phase sequence gives the scoped phase with parameter
`paddedPhaseProduct ps`. -/
theorem padded_controlled_sequence_compress (n : ℕ) (a : Fin n) (ps : List (ℕ × Bool)) :
    compress (paddedNativeFrame n) (localProgramMatrix (paddedControlledPhaseSequenceWord n a ps))
      (paddedNativeFrame n) = scopedPhaseGate (fun x => x a) (paddedPhaseProduct ps) :=
  native_frame_compression n _ _ (padded_controlled_sequence_matrix n a ps)

/-- A local program of length `L` defines a unitary zero-query circuit with `L` gates in both
its forward and adjoint programs. -/
private theorem native_program_cost {n : ℕ} (gs : List (LocalQFTGate n)) (L : ℕ) (hl : gs.length = L) :
    QueryCount (localProgramCircuit gs) = 0 ∧ GateCount (localProgramCircuit gs) = L ∧
    GateCount (localProgramCircuit (localProgramAdjoint gs)) = L ∧
    IsUnitaryCircuit (localProgramCircuit gs) := by
  obtain ⟨_, _, _, hu, _, hq, hg, hgi, _⟩ := localDyadicProgram_run_adjoint_cost n gs 0
  exact ⟨hq, hg.trans hl, hgi.trans hl, hu⟩

/-- A padded scalar phase sequence is a unitary zero-query circuit with `7 * ps.length` gates in
both its forward and adjoint programs. -/
theorem padded_scalar_sequence_cost (n : ℕ) (ps : List (ℕ × Bool)) :
    QueryCount (localProgramCircuit (paddedScalarPhaseSequenceWord n ps)) = 0 ∧
    GateCount (localProgramCircuit (paddedScalarPhaseSequenceWord n ps)) = 7 * ps.length ∧
    GateCount (localProgramCircuit (localProgramAdjoint (paddedScalarPhaseSequenceWord n ps))) = 7 * ps.length ∧
    IsUnitaryCircuit (localProgramCircuit (paddedScalarPhaseSequenceWord n ps)) :=
  native_program_cost _ _ (padded_phase_sequence_lengths n ps).1

/-- A padded controlled phase sequence is a unitary zero-query circuit with `7 * ps.length`
gates in both its forward and adjoint programs. -/
theorem padded_controlled_sequence_cost (n : ℕ) (a : Fin n) (ps : List (ℕ × Bool)) :
    QueryCount (localProgramCircuit (paddedControlledPhaseSequenceWord n a ps)) = 0 ∧
    GateCount (localProgramCircuit (paddedControlledPhaseSequenceWord n a ps)) = 7 * ps.length ∧
    GateCount (localProgramCircuit (localProgramAdjoint (paddedControlledPhaseSequenceWord n a ps))) = 7 * ps.length ∧
    IsUnitaryCircuit (localProgramCircuit (paddedControlledPhaseSequenceWord n a ps)) :=
  native_program_cost _ _ ((padded_phase_sequence_lengths n ps).2 a)

/-- The padded scalar sequence's frame error relative to target scalar `z` is at most
`‖paddedPhaseProduct ps - z‖`. -/
theorem padded_scalar_sequence_frame_error (n : ℕ) (ps : List (ℕ × Bool)) (z : ℂ) :
    ‖localProgramMatrix (paddedScalarPhaseSequenceWord n ps) * paddedNativeFrame n -
      paddedNativeFrame n * (z • (1 : Matrix (Reg n) (Reg n) ℂ))‖ ≤
      ‖paddedPhaseProduct ps - z‖ := by
  rw [padded_scalar_sequence_matrix, ← Matrix.mul_sub, ← sub_smul, Matrix.mul_smul,
    Matrix.mul_one, norm_smul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (isometry_norm_le (paddedNativeFrame_isometry n))
      (norm_nonneg (paddedPhaseProduct ps - z))

/-- The padded controlled sequence's frame error relative to the scoped phase with parameter `z`
is at most `‖paddedPhaseProduct ps - z‖`. -/
theorem padded_controlled_sequence_frame_error (n : ℕ) (a : Fin n)
    (ps : List (ℕ × Bool)) (z : ℂ) :
    ‖localProgramMatrix (paddedControlledPhaseSequenceWord n a ps) * paddedNativeFrame n -
      paddedNativeFrame n * scopedPhaseGate (fun x => x a) z‖ ≤ ‖paddedPhaseProduct ps - z‖ := by
  let P : Matrix (Reg n) (Reg n) ℂ := Matrix.diagonal fun x => if x a then 1 else 0
  have hP : IsOrthogonalProjector P := by
    constructor
    · change P * P = P
      dsimp [P]
      rw [Matrix.diagonal_mul_diagonal]
      ext x y
      by_cases hxy : x = y
      · subst y; cases hx : x a <;> simp [Matrix.diagonal, hx]
      · simp [Matrix.diagonal, hxy]
    · change Pᴴ = P
      ext x y
      by_cases hxy : x = y
      · subst y; cases hx : x a <;> simp [P, Matrix.diagonal, Matrix.conjTranspose_apply, hx]
      · simp [P, Matrix.diagonal, Matrix.conjTranspose_apply, hxy, Ne.symm hxy]
  have hd : scopedPhaseGate (fun x => x a) (paddedPhaseProduct ps) - scopedPhaseGate (fun x => x a) z =
      (paddedPhaseProduct ps - z) • P := by
    ext x y
    by_cases hxy : x = y
    · subst y; cases hx : x a <;>
        simp [P, scopedPhaseGate, Matrix.diagonal, Matrix.smul_apply, hx]
    · simp [P, scopedPhaseGate, Matrix.diagonal, Matrix.smul_apply, hxy]
  rw [padded_controlled_sequence_matrix, ← Matrix.mul_sub, hd, Matrix.mul_smul, norm_smul]
  have hf : ‖paddedNativeFrame n * P‖ ≤ 1 :=
    (Matrix.l2_opNorm_mul _ _).trans (by
      calc
        ‖paddedNativeFrame n‖ * ‖P‖ ≤ 1 * 1 :=
          mul_le_mul (isometry_norm_le (paddedNativeFrame_isometry n))
            (shared_projector_norm_le_one hP) (norm_nonneg P) (by norm_num)
        _ = 1 := by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (norm_nonneg (paddedPhaseProduct ps - z))
end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
