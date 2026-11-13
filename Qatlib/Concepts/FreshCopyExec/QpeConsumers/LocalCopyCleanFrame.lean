/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl
import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyLayout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyWordSemantics

/-!
# Clean-Frame Controlled Partial-Swap Semantics

The diagonal sign `localCopyBellSign` and projector `localCopyCleanProjector` describe the
parity computation on initialized scratch. Bell basis conjugation converts the resulting
spectral phase into a polynomial in the register-swap matrix, using standard quantum circuit
identities as in [NielsenChuang2010].

The main intertwining theorem identifies the complete local word with `controlledSwapRawGate` on
the image of `localCopyFrame`, so the logical interaction returns its scratch qubits clean.

## Main statements

- `localCopyPhaseUncompute_clean_projector` identifies the computed phase on the clean subspace.
- `localCopyBell_spectral_conjugation` expresses that phase using the register-swap matrix.
* `local_controlled_partial_swap_clean_intertwining` gives the exact clean frame semantics of
  the local controlled partial swap.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators
set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers

/-- The sign given by the parity of the bitwise ANDs between corresponding data and fresh
register bits. -/
noncomputable def localCopyBellSign (n : ℕ) (x : Reg (3*n+2)) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin n, if x (localCopyDataWire n i) &&
    x (localCopyFreshWire n i) then (1 : ℕ) else 0)

/-- A Boolean choice between one and `e` is an affine function of the corresponding sign in
`{1,-1}`. -/
private theorem localCopyPhase_affine (b : Bool) (e : ℂ) :
    (if b then e else 1) = (1+e)/2 + (1-e)/2 *
      (-1 : ℂ) ^ (if b then (1 : ℕ) else 0) := by
  cases b <;> norm_num <;> ring

/-- On a basis state with zero AND and parity scratch, computing parity, applying the controlled
phase, and uncomputing restores that basis state up to its control dependent Bell sign
phase. -/
theorem localCopyPhaseUncompute_clean_basis (n : ℕ) (θ : ℝ)
    (x : Reg (3*n+2)) (ha : ∀ i, x (localCopyAndWire n i) = false)
    (hp : x (localCopyParityWire n) = false) :
    ApplyGate (reflectionProgramMatrix (reflectionAdjoint (localCopyComputeAndParity n)) *
        reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) *
        reflectionProgramMatrix (localCopyComputeAndParity n)) (Qatlib.Foundations.PureStateMath.Ket x) =
      (if x (localCopyControlWire n) then
        (1 + Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 +
        (1 - Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 * localCopyBellSign n x
        else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  let y := (List.finRange n).foldl (fun y i => localCopyComputeBasisStep n i y) x
  let e := Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I)
  have hs := localCopyComputeAndParity_sign n x ha hp
  have hc := localCopyComputeAndParity_control n x
  have he : (if y (localCopyControlWire n) && y (localCopyParityWire n) then e else 1) =
      (if x (localCopyControlWire n) then (1+e)/2 + (1-e)/2 * localCopyBellSign n x else 1) := by
    change (-1 : ℂ) ^ (if y (localCopyParityWire n) then (1 : ℕ) else 0) =
      localCopyBellSign n x at hs
    change y (localCopyControlWire n) = x (localCopyControlWire n) at hc
    rw [hc]
    cases h : x (localCopyControlWire n)
    · simp
    · simp only [Bool.true_and, if_true]
      rw [localCopyPhase_affine, hs]
  have hu := reflectionProgramMatrix_unitary (localCopyComputeAndParity n)
    (localCopyComputeAndParity_legal n)
  have hi : (reflectionProgramMatrix (localCopyComputeAndParity n))ᴴ *
      reflectionProgramMatrix (localCopyComputeAndParity n) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hu
  rw [reflectionAdjoint_matrix _ (localCopyComputeAndParity_legal n),
    mul_assoc, applyGate_mul, applyGate_mul, localCopyComputeAndParity_basis,
    localCopyControlledPhaseSteps_diagonal, applyGate_diagonal_ket]
  change ApplyGate _ ((if y (localCopyControlWire n) && y (localCopyParityWire n)
    then e else 1) • Qatlib.Foundations.PureStateMath.Ket y) = _
  rw [he]
  rw [← localCopyComputeAndParity_basis n x]
  simp only [ApplyGate, Matrix.mulVec_smul]
  rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]

/-- The diagonal projector onto basis states whose AND scratch bits and parity scratch bit are
all zero. -/
noncomputable def localCopyCleanProjector (n : ℕ) : Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ :=
  Matrix.diagonal (fun x => if (∀ i, x (localCopyAndWire n i) = false) ∧
    x (localCopyParityWire n) = false then 1 else 0)

/-- The clean subspace projector acts as the identity on the image of the clean frame. -/
theorem localCopyCleanProjector_frame (n : ℕ) :
    localCopyCleanProjector n * localCopyFrame n = localCopyFrame n := by
  ext x p
  simp only [localCopyCleanProjector,Matrix.diagonal_mul,localCopyFrame]
  by_cases he : localCopySplit n x = (p,((fun _ => false),false))
  · have ha : ∀ i, x (localCopyAndWire n i) = false :=
      fun i => congrFun (congrArg (fun q => q.2.1) he) i
    have hp : x (localCopyParityWire n) = false := congrArg (fun q => q.2.2) he
    simp [he,ha,hp]
  · simp [he]

/-- A diagonal matrix depending only on the spectator registers commutes with every lifted
product of data and fresh pair matrices. -/
theorem localCopyPairLift_spectator_commute (n : ℕ)
    (A : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (d : Bool × (Reg n × Bool) → ℂ) :
    Matrix.diagonal (fun x => d ((localCopyPairSplit n x).1)) * localCopyPairLift n A =
      localCopyPairLift n A * Matrix.diagonal (fun x => d ((localCopyPairSplit n x).1)) := by
  ext x y
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,localCopyPairLift,relabelGate,
    Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,TensorGate,
    Matrix.kroneckerMap_apply,Matrix.one_apply]
  by_cases h : (localCopyPairSplit n x).1 = (localCopyPairSplit n y).1
  · rw [if_pos h,h]
    ring
  · rw [if_neg h]
    simp

/-- The Bell basis word commutes with the clean scratch projector. -/
theorem localCopyBell_clean_commute (n : ℕ) :
    localCopyCleanProjector n * reflectionProgramMatrix (localCopyBellSteps n) =
      reflectionProgramMatrix (localCopyBellSteps n) * localCopyCleanProjector n := by
  rw [localCopyBellSteps_eq_pairLift]
  exact localCopyPairLift_spectator_commute n _
    (fun p => if (∀ i, p.2.1 i = false) ∧ p.2.2 = false then 1 else 0)

/-- The diagonal phase determined by the control bit and Bell sign, equal to one when the
control is false. -/
noncomputable def localCopySpectralPhase (n : ℕ) (θ : ℝ) :
    Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ :=
  Matrix.diagonal (fun x => if x (localCopyControlWire n) then
    (1 + Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 +
    (1 - Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 * localCopyBellSign n x else 1)

/-- On the clean scratch subspace, the parity compute, phase, and uncompute word equals the Bell
sign spectral phase. -/
theorem localCopyPhaseUncompute_clean_projector (n : ℕ) (θ : ℝ) :
    (reflectionProgramMatrix (reflectionAdjoint (localCopyComputeAndParity n)) *
      reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) *
      reflectionProgramMatrix (localCopyComputeAndParity n)) * localCopyCleanProjector n =
      localCopySpectralPhase n θ * localCopyCleanProjector n := by
  have he : ∀ y : Reg (3*n+2),
      ApplyGate ((reflectionProgramMatrix (reflectionAdjoint (localCopyComputeAndParity n)) *
        reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) *
        reflectionProgramMatrix (localCopyComputeAndParity n)) * localCopyCleanProjector n)
          (Qatlib.Foundations.PureStateMath.Ket y) = ApplyGate (localCopySpectralPhase n θ * localCopyCleanProjector n) (Qatlib.Foundations.PureStateMath.Ket y) := by
    intro y
    conv_lhs => rw [applyGate_mul]
    conv_rhs => rw [applyGate_mul]
    unfold localCopyCleanProjector
    rw [applyGate_diagonal_ket]
    by_cases h : (∀ i, y (localCopyAndWire n i) = false) ∧ y (localCopyParityWire n) = false
    · rw [if_pos h,one_smul,localCopyPhaseUncompute_clean_basis n θ y h.1 h.2]
      unfold localCopySpectralPhase
      rw [applyGate_diagonal_ket]
    · rw [if_neg h,zero_smul]
      simp [ApplyGate]
  ext x y
  simpa only [ApplyGate,Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] using! congrFun (he y) x

/-- The physical diagonal matrix whose entry depends only on the control wire through the
function `a`. -/
noncomputable def localCopyControlDiagonal (n : ℕ) (a : Bool → ℂ) :
    Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ :=
  Matrix.diagonal (fun x => a (x (localCopyControlWire n)))

/-- The Bell basis word commutes with every control dependent diagonal matrix. -/
theorem localCopyBell_control_commute (n : ℕ) (a : Bool → ℂ) :
    localCopyControlDiagonal n a * reflectionProgramMatrix (localCopyBellSteps n) =
      reflectionProgramMatrix (localCopyBellSteps n) * localCopyControlDiagonal n a := by
  rw [localCopyBellSteps_eq_pairLift]
  exact localCopyPairLift_spectator_commute n _ (fun p => a p.1)

/-- The spectral phase decomposes into a control dependent diagonal term and a second such term
multiplied by the Bell sign diagonal. -/
private theorem localCopySpectralPhase_decompose (n : ℕ) (θ : ℝ) :
    localCopySpectralPhase n θ =
      localCopyControlDiagonal n (fun b => if b then
        (1+Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 else 1) +
      localCopyControlDiagonal n (fun b => if b then
        (1-Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 else 0) *
        Matrix.diagonal (localCopyBellSign n) := by
  ext x y
  simp only [localCopySpectralPhase,localCopyControlDiagonal,Matrix.add_apply,
    Matrix.diagonal_mul,Matrix.diagonal_apply]
  by_cases h : x = y
  · subst y
    cases x (localCopyControlWire n) <;> simp
  · simp [h]

/-- Conjugating the spectral phase by the Bell basis matrix replaces the Bell sign diagonal with
the physical register-swap matrix. -/
theorem localCopyBell_spectral_conjugation (n : ℕ) (θ : ℝ) :
    reflectionProgramMatrix (localCopyBellSteps n) * localCopySpectralPhase n θ *
      (reflectionProgramMatrix (localCopyBellSteps n))ᴴ =
    localCopyControlDiagonal n (fun b => if b then
      (1+Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 else 1) +
    localCopyControlDiagonal n (fun b => if b then
      (1-Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 else 0) * localCopyRegisterSwap n := by
  let B := reflectionProgramMatrix (localCopyBellSteps n)
  let D := Matrix.diagonal (localCopyBellSign n)
  have hu := reflectionProgramMatrix_unitary (localCopyBellSteps n) (localCopyBellSteps_legal n)
  have hi : B * Bᴴ = 1 := by
    simpa only [B,Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hu
  have hd : D = Bᴴ * localCopyRegisterSwap n * B :=
    (local_bell_basis_register_swap_parity n).symm
  have hconj : B * D * Bᴴ = localCopyRegisterSwap n := by
    rw [hd]
    simp only [← mul_assoc,hi,one_mul]
    rw [mul_assoc,hi,mul_one]
  have hc (a : Bool → ℂ) : B * localCopyControlDiagonal n a =
      localCopyControlDiagonal n a * B := (localCopyBell_control_commute n a).symm
  rw [localCopySpectralPhase_decompose,Matrix.mul_add,Matrix.add_mul]
  change B * _ * Bᴴ + B * (_ * D) * Bᴴ = _
  rw [hc, mul_assoc,hi,mul_one]
  rw [← mul_assoc B, hc]
  simp only [mul_assoc]
  rw [← mul_assoc B D Bᴴ,hconj]

/-- The adjoint Bell basis matrix commutes with the clean scratch projector. -/
theorem localCopyBell_adjoint_clean_commute (n : ℕ) :
    localCopyCleanProjector n * (reflectionProgramMatrix (localCopyBellSteps n))ᴴ =
      (reflectionProgramMatrix (localCopyBellSteps n))ᴴ * localCopyCleanProjector n := by
  rw [localCopyBellSteps_eq_pairLift,localCopyPairLift_adjoint]
  exact localCopyPairLift_spectator_commute n _
    (fun p => if (∀ i, p.2.1 i = false) ∧ p.2.2 = false then 1 else 0)

/-- After Bell basis conjugation and restriction to the clean frame, the parity compute, phase,
and uncompute word can be replaced by its spectral-phase matrix. -/
theorem localCopyBell_phase_clean_frame (n : ℕ) (θ : ℝ) :
    reflectionProgramMatrix (localCopyBellSteps n) *
      (reflectionProgramMatrix (reflectionAdjoint (localCopyComputeAndParity n)) *
        reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) *
        reflectionProgramMatrix (localCopyComputeAndParity n)) *
      (reflectionProgramMatrix (localCopyBellSteps n))ᴴ * localCopyFrame n =
    (reflectionProgramMatrix (localCopyBellSteps n) * localCopySpectralPhase n θ *
      (reflectionProgramMatrix (localCopyBellSteps n))ᴴ) * localCopyFrame n := by
  let B := reflectionProgramMatrix (localCopyBellSteps n)
  let K := reflectionProgramMatrix (reflectionAdjoint (localCopyComputeAndParity n)) *
    reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) *
    reflectionProgramMatrix (localCopyComputeAndParity n)
  let P := localCopyCleanProjector n
  have hp : P * (Bᴴ * localCopyFrame n) = Bᴴ * localCopyFrame n := by
    rw [← Matrix.mul_assoc,localCopyBell_adjoint_clean_commute,Matrix.mul_assoc,localCopyCleanProjector_frame]
  change B * K * Bᴴ * localCopyFrame n = _
  calc
    B * K * Bᴴ * localCopyFrame n = B * (K * (P * (Bᴴ * localCopyFrame n))) := by
      rw [hp]
      simp only [Matrix.mul_assoc]
    _ = B * ((K * P) * (Bᴴ * localCopyFrame n)) := by rw [Matrix.mul_assoc K P]
    _ = B * ((localCopySpectralPhase n θ * P) * (Bᴴ * localCopyFrame n)) := by
      rw [localCopyPhaseUncompute_clean_projector]
    _ = _ := by rw [Matrix.mul_assoc, hp]; simp only [Matrix.mul_assoc]; rfl

/-- The rotation on the physical control wire is the control dependent diagonal with phase
`exp(θ*I)` on the true branch and one on the false branch. -/
theorem localCopyControlRz_matrix (n : ℕ) (θ : ℝ) :
    wireGate (3*n+2) (localCopyControlWire n) (Rz θ) =
      localCopyControlDiagonal n (fun b => if b then Complex.exp ((θ : ℂ)*Complex.I) else 1) := by
  have he : TensorGate (Rz θ) (1 : Matrix Bool Bool ℂ) = Matrix.diagonal
      (fun p : Bool × Bool => if p.1 then Complex.exp ((θ : ℂ)*Complex.I) else 1) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [TensorGate,Matrix.kroneckerMap_apply,Rz]
  have hw := localCopyPhaseWireGate n true (Rz θ)
  simp only [if_true] at hw
  rw [hw,he,localCopyPhaseLift_diagonal]
  rfl

/-- Multiplying the symmetric and antisymmetric phase coefficients by `exp(-θ*I)` yields `cos θ`
and `-I*sin θ`, respectively. -/
private theorem localCopyPhase_coefficients (θ : ℝ) :
    Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) *
        ((1+Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2) = (Real.cos θ : ℂ) ∧
    Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) *
        ((1-Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2) = -Complex.I*(Real.sin θ : ℂ) := by
  have he : Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) *
      Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I) = Complex.exp ((θ : ℂ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn := Complex.exp_ofReal_mul_I (-θ)
  have ht := Complex.exp_ofReal_mul_I θ
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg] at hn
  constructor
  · calc
      _ = (Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) +
        Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) * Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 := by ring
      _ = _ := by rw [he]; simp only [Complex.ofReal_neg]; rw [hn,ht]; ring
  · calc
      _ = (Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) -
        Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) * Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 := by ring
      _ = _ := by rw [he]; simp only [Complex.ofReal_neg]; rw [hn,ht]; ring

/-- The logical diagonal matrix depending only on the Boolean control, with both logical data
registers as spectators. -/
noncomputable def localCopyLogicalControlDiagonal (n : ℕ) (a : Bool → ℂ) :
    Matrix (Bool × (Fin (2^n) × Fin (2^n))) (Bool × (Fin (2^n) × Fin (2^n))) ℂ :=
  Matrix.diagonal (fun p => a p.1)

/-- The clean frame intertwines physical and logical control dependent diagonal matrices. -/
theorem localCopyControlDiagonal_frame (n : ℕ) (a : Bool → ℂ) :
    localCopyControlDiagonal n a * localCopyFrame n =
      localCopyFrame n * localCopyLogicalControlDiagonal n a := by
  ext x p
  simp only [localCopyControlDiagonal,localCopyLogicalControlDiagonal,
    Matrix.diagonal_mul,Matrix.mul_diagonal,localCopyFrame]
  by_cases h : localCopySplit n x = (p,((fun _ => false),false))
  · have hc : x (localCopyControlWire n) = p.1 := congrArg (fun q => q.1.1) h
    simp [h,hc]
  · simp [h]

/-- Left multiplication by an involutive permutation matrix reindexes the rows by that
permutation. -/
private theorem localCopy_perm_mul {I J : Type} [Fintype I] [DecidableEq I]
    (σ : I → I) (hσ : Function.Involutive σ) (A : Matrix I J ℂ) (x : I) (p : J) :
    (permMatrix σ * A) x p = A (σ x) p := by
  have he : ∀ y, x = σ y ↔ y = σ x := by
    intro y
    constructor
    · intro h
      rw [h,hσ]
    · intro h
      rw [h,hσ]
  simp [Matrix.mul_apply,permMatrix,he]

/-- Right multiplication by `permMatrix σ` reindexes columns by `σ`, for any function on the
finite column index type. -/
private theorem localCopy_mul_perm {I J : Type} [Fintype J] [DecidableEq J]
    (σ : J → J) (A : Matrix I J ℂ) (x : I) (p : J) :
    (A * permMatrix σ) x p = A x (σ p) := by
  simp [Matrix.mul_apply,permMatrix]

/-- The logical permutation matrix exchanging the data and fresh registers while preserving the
Boolean control. -/
noncomputable def localCopyLogicalSwap (n : ℕ) :
    Matrix (Bool × (Fin (2^n) × Fin (2^n))) (Bool × (Fin (2^n) × Fin (2^n))) ℂ :=
  permMatrix (fun p => (p.1,p.2.swap))

/-- The clean frame intertwines the physical data and fresh register swap with the corresponding
logical swap. -/
theorem localCopyRegisterSwap_frame (n : ℕ) :
    localCopyRegisterSwap n * localCopyFrame n = localCopyFrame n * localCopyLogicalSwap n := by
  have hs : Function.Involutive (localCopySwapBasis n) := by
    intro x
    apply (localCopySplit n).injective
    simp [localCopySwapBasis]
  ext x p
  rw [localCopyRegisterSwap,localCopy_perm_mul _ hs,localCopyLogicalSwap,localCopy_mul_perm]
  simp only [localCopyFrame,localCopySwapBasis,Equiv.apply_symm_apply]
  have he : (((localCopySplit n x).1.1,((localCopySplit n x).1.2.2,
        (localCopySplit n x).1.2.1)),(localCopySplit n x).2) =
      (p,((fun _ => false),false)) ↔
      localCopySplit n x = ((p.1,p.2.swap),((fun _ => false),false)) := by
    rcases h : localCopySplit n x with ⟨⟨b,d,f⟩,a,q⟩
    rcases p with ⟨c,i,j⟩
    simp [Prod.ext_iff,and_assoc,and_left_comm,and_comm]
  simp only [he]

/-- The logical controlled partial swap decomposes into the identity and logical swap with the
appropriate control dependent cosine and negative-imaginary sine coefficients. -/
private theorem localCopyControlledSwap_decompose (n : ℕ) (θ : ℝ) :
    controlledSwapRawGate (2^n) θ =
      localCopyLogicalControlDiagonal n (fun b => if b then (Real.cos θ : ℂ) else 1) +
      localCopyLogicalControlDiagonal n (fun b => if b then -Complex.I*(Real.sin θ : ℂ) else 0) *
        localCopyLogicalSwap n := by
  ext ⟨b,i,j⟩ ⟨c,k,l⟩
  cases b <;> cases c <;>
    simp [controlledSwapRawGate,select,partialSwapMatrix,localCopyLogicalControlDiagonal,
      localCopyLogicalSwap,Matrix.diagonal_mul,Matrix.diagonal_apply,permMatrix,Matrix.one_apply,
      swapRegisterMatrix_apply,Prod.ext_iff,sub_eq_add_neg]
  split_ifs <;> ring

/-- Multiplying two control dependent diagonal matrices multiplies their defining functions
pointwise. -/
private theorem localCopyControlDiagonal_mul (n : ℕ) (a b : Bool → ℂ) :
    localCopyControlDiagonal n a * localCopyControlDiagonal n b =
      localCopyControlDiagonal n (fun c => a c * b c) := by
  exact Matrix.diagonal_mul_diagonal _ _

/-- After the final negative angle control rotation, the Bell-conjugated spectral phase is the
physical swap polynomial with cosine and negative-imaginary sine coefficients. -/
private theorem localCopyFinalPhase_polynomial (n : ℕ) (θ : ℝ) :
    wireGate (3*n+2) (localCopyControlWire n) (Rz (-θ)) *
      (reflectionProgramMatrix (localCopyBellSteps n) * localCopySpectralPhase n θ *
        (reflectionProgramMatrix (localCopyBellSteps n))ᴴ) =
    localCopyControlDiagonal n (fun b => if b then (Real.cos θ : ℂ) else 1) +
      localCopyControlDiagonal n (fun b => if b then -Complex.I*(Real.sin θ : ℂ) else 0) *
        localCopyRegisterSwap n := by
  rw [localCopyBell_spectral_conjugation,localCopyControlRz_matrix,Matrix.mul_add,
    ← Matrix.mul_assoc,localCopyControlDiagonal_mul,localCopyControlDiagonal_mul]
  have h0 : (fun b : Bool => (if b then Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) else 1) *
      (if b then (1+Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 else 1)) =
      (fun b => if b then (Real.cos θ : ℂ) else 1) := by
    funext b
    cases b
    · simp
    · exact (localCopyPhase_coefficients θ).1
  have h1 : (fun b : Bool => (if b then Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) else 1) *
      (if b then (1-Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I))/2 else 0)) =
      (fun b => if b then -Complex.I*(Real.sin θ : ℂ) else 0) := by
    funext b
    cases b
    · simp
    · exact (localCopyPhase_coefficients θ).2
  rw [h0,h1]

/-- The local controlled partial swap word implements the logical controlled partial swap
through the clean frame for every register size and real angle. -/
theorem local_controlled_partial_swap_clean_intertwining :
    ∀ (n : ℕ) (θ : ℝ), reflectionProgramMatrix (localControlledSwapSteps n θ) *
      localCopyFrame n = localCopyFrame n * controlledSwapRawGate (2^n) θ := by
  intro n θ
  have hw : reflectionProgramMatrix (localControlledSwapSteps n θ) * localCopyFrame n =
      wireGate (3*n+2) (localCopyControlWire n) (Rz (-θ)) *
      (reflectionProgramMatrix (localCopyBellSteps n) *
        (reflectionProgramMatrix (reflectionAdjoint (localCopyComputeAndParity n)) *
          reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) *
          reflectionProgramMatrix (localCopyComputeAndParity n)) *
        (reflectionProgramMatrix (localCopyBellSteps n))ᴴ * localCopyFrame n) := by
    simp only [localControlledSwapSteps,reflectionProgramMatrix_append,
      reflectionProgramMatrix,reflectionGateMatrix,Matrix.one_mul,
      reflectionAdjoint_matrix _ (localCopyBellSteps_legal n)]
    simp only [Matrix.mul_assoc]
  rw [hw,localCopyBell_phase_clean_frame,← Matrix.mul_assoc,localCopyFinalPhase_polynomial,
    Matrix.add_mul,Matrix.mul_assoc,localCopyRegisterSwap_frame,
    ← Matrix.mul_assoc,localCopyControlDiagonal_frame,localCopyControlDiagonal_frame,
    Matrix.mul_assoc,← Matrix.mul_add,← localCopyControlledSwap_decompose]
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
