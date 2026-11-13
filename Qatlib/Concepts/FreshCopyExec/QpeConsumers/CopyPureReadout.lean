/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout

/-!
# Exact Readout for a Rank One Copy State

This module specializes the fresh copy phase estimation implementation to the two dimensional
density operator `copyPureDensity`, the projector onto the zero basis state. On matrices with
this fixed data factor, each controlled copy step acts exactly as the control phase gate
`copyPureControlPhase`, so a positive number of steps reproduces the ideal query exactly.

The concrete four label circuit therefore has exact actual readout, refining the general
approximation guarantee for density matrix exponentiation in [LloydMohseniRebentrost2014]. The
phase label interpretation uses the phase estimation setting of [NielsenChuang2010].

## Main statements

* `controlledCopyRawMap_pure_data` identifies one raw step with conjugation on the control
  factor.
* `copyPureProgram_exact` proves exact actual and ideal execution for circuits whose gates
  preserve the embedded matrix family.
* `copy_qpe_rank_one_actual_readout_consumer` gives label two mass one and the resource tuple
  `(3 * n, 3 * n, 3 * n, 0)` for every positive `n`.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014], Quantum principal component analysis.
* [Nielsen and Chuang, 2010][NielsenChuang2010], Quantum Computation and Quantum Information.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical ComplexOrder

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open scoped Classical ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000
section CopyPureReadout

open scoped Classical ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

/-- Defines the two dimensional pure density matrix given by the outer product of the zero basis
state. -/
private noncomputable def copyPureDensity : Operator 2 :=
    outerProduct (Qatlib.Foundations.PureStateMath.Ket 0)

/-- The projector onto the zero basis state is a density operator. -/
private theorem copyPureDensity_density : IsDensityOperator copyPureDensity :=
  outerProduct_density (normalized_ket (0 : Fin 2))

/-- The pure data density matrix `copyPureDensity` is idempotent. -/
private theorem copyPureDensity_sq : copyPureDensity * copyPureDensity = copyPureDensity :=
  (isOrthogonalProjector_outerProduct (normalized_ket (0 : Fin 2))).1

/-- A partial swap using `copyPureDensity` as both the fresh copy state and the input leaves
this density matrix unchanged for every real angle. -/
private theorem copyPureDensity_fixed (θ : ℝ) :
    partialSwapOutput copyPureDensity θ copyPureDensity = copyPureDensity := by
  rw [partial_swap_actual_output_formula, copyPureDensity_density.2, one_smul,
    sub_self, smul_zero, sub_zero, ← add_smul]
  have ht : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [ht, one_smul]

/-- Defines a diagonal Boolean control gate with phase one on false and `exp (-I * theta)` on
true. -/
private noncomputable def copyPureControlPhase (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if b then Complex.exp (-Complex.I * (θ : ℂ)) else 1)

/-- Expresses `exp (-I * theta)` as `cos theta - I * sin theta` for a real angle. -/
private theorem copyPurePhase_exp (θ : ℝ) :
    Complex.exp (-Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
  have h := Complex.exp_mul_I (((-θ : ℝ) : ℂ))
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg] at h
  have he : -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.ofReal_neg, h]
  ring

/-- Expresses the complex conjugate of `exp (-I * theta)` as `cos theta + I * sin theta` for a
real angle. -/
private theorem copyPurePhase_exp_star (θ : ℝ) :
    star (Complex.exp (-Complex.I * (θ : ℂ))) =
      (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
  rw [copyPurePhase_exp]
  simp only [star_sub, star_mul, RCLike.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- On an arbitrary control matrix tensored with `copyPureDensity`, one raw controlled copy step
conjugates the control matrix by `copyPureControlPhase` and leaves the data factor
unchanged. -/
theorem controlledCopyRawMap_pure_data (θ : ℝ) (B : Matrix Bool Bool ℂ) :
    controlledCopyRawMap copyPureDensity θ (TensorGate B copyPureDensity) =
      TensorGate (MatrixMap.conj (copyPureControlPhase θ) B) copyPureDensity := by
  have hblock (b c : Bool) :
      (TensorGate B copyPureDensity).submatrix (fun i => (b,i)) (fun j => (c,j)) =
        (B b c) • copyPureDensity := by ext i j; rfl
  have hout (b c : Bool) :
      MatrixMap.conj (copyPureControlPhase θ) B b c =
        (if b then Complex.exp (-Complex.I * (θ : ℂ)) else 1) * B b c *
          star (if c then Complex.exp (-Complex.I * (θ : ℂ)) else 1) := by
    cases b <;> cases c <;>
      simp [conjMap_apply, copyPureControlPhase, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.conjTranspose_apply, Fintype.sum_bool, RCLike.star_def]
  ext ⟨b,i⟩ ⟨c,j⟩
  cases b <;> cases c
  · rw [controlledCopyRawMap_ff 2 _ θ _ i j copyPureDensity_density.2]
    simp only [tensorGate_apply]
    rw [hout]
    simp
  · have h := controlledCopyRawMap_ft copyPureDensity θ (TensorGate B copyPureDensity)
      i j copyPureDensity_density.2
    change _ = (Real.cos θ) • _ + (Complex.I * (Real.sin θ : ℂ)) •
      (((TensorGate B copyPureDensity).submatrix (fun i => (false,i))
        (fun j => (true,j))) * copyPureDensity) i j at h
    rw [hblock, Matrix.smul_mul, copyPureDensity_sq] at h
    rw [h]
    simp only [tensorGate_apply, hout, Bool.false_eq_true, ↓reduceIte, one_mul,
      copyPurePhase_exp_star, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  · have h := controlledCopyRawMap_tf_entry copyPureDensity θ (TensorGate B copyPureDensity)
      i j copyPureDensity_density.2
    change _ = (Real.cos θ) • _ - (Complex.I * (Real.sin θ : ℂ)) •
      (copyPureDensity * ((TensorGate B copyPureDensity).submatrix (fun i => (true,i))
        (fun j => (false,j)))) i j at h
    rw [hblock, Matrix.mul_smul, copyPureDensity_sq] at h
    rw [h]
    simp only [tensorGate_apply, hout, Bool.false_eq_true, ↓reduceIte, star_one, mul_one,
      copyPurePhase_exp, Matrix.smul_apply, smul_eq_mul, Complex.real_smul, AFtf,
      Matrix.submatrix_apply]
    ring
  · have h := controlledCopyRawMap_tt copyPureDensity θ (TensorGate B copyPureDensity) i j
    change _ = partialSwapOutput copyPureDensity θ
      ((TensorGate B copyPureDensity).submatrix (fun i => (true,i)) (fun j => (true,j))) i j at h
    rw [hblock] at h
    have hl : partialSwapOutput copyPureDensity θ ((B true true) • copyPureDensity) =
        (B true true) • copyPureDensity := by
      rw [← partialSwapChannel_map _ copyPureDensity_density,
        map_smul, partialSwapChannel_map, copyPureDensity_fixed]
    rw [hl] at h
    rw [h]
    have he : Complex.exp (-Complex.I * (θ : ℂ)) *
        star (Complex.exp (-Complex.I * (θ : ℂ))) = 1 := by
      rw [copyPurePhase_exp_star, copyPurePhase_exp]
      have ht : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq θ
      have hI := Complex.I_mul_I
      linear_combination ht - (Real.sin θ : ℂ) ^ 2 * hI
    simp only [tensorGate_apply, hout, ↓reduceIte, Matrix.smul_apply, smul_eq_mul]
    rw [show Complex.exp (-Complex.I * (θ : ℂ)) * B true true *
      star (Complex.exp (-Complex.I * (θ : ℂ))) = B true true from by
      rw [mul_comm (Complex.exp _) (B true true), mul_assoc, he, mul_one]]

/-- Embeds a matrix on the phase and control registers by tensoring it with `copyPureDensity`
and reassociating the registers into phase, control, and data coordinates. -/
private noncomputable def copyPureEmbed (M : ℕ) (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    Matrix (Fin M × (Bool × Fin 2)) (Fin M × (Bool × Fin 2)) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin M) Bool (Fin 2)) (TensorGate A copyPureDensity)

/-- An entry of `copyPureEmbed M A` is the corresponding phase and control entry of `A`
multiplied by the data entry of `copyPureDensity`. -/
private theorem copyPureEmbed_apply (M : ℕ) (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ)
    (a c : Fin M) (b d : Bool) (i j : Fin 2) :
    copyPureEmbed M A (a,(b,i)) (c,(d,j)) = A (a,b) (c,d) * copyPureDensity i j := rfl

/-- Relabels the pure data embedding into a phase register paired with the finite four
dimensional control and data register. -/
private noncomputable def copyPureFinEmbed (M : ℕ) (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    Matrix (Fin M × Fin 4) (Fin M × Fin 4) ℂ :=
  relabelGate (copyQPERegisterEquiv 2 M) (copyPureEmbed M A)

/-- Each fixed pair of phase register indices in conjugation by identity tensored with a control
matrix is obtained by conjugating the corresponding control block alone. -/
private theorem copyPureSpectatorConj (M : ℕ) (P : Matrix Bool Bool ℂ)
    (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) (a c : Fin M) :
    (MatrixMap.conj (TensorGate (1 : Operator M) P) A).submatrix
      (fun b => (a,b)) (fun d => (c,d)) =
      MatrixMap.conj P (A.submatrix (fun b => (a,b)) (fun d => (c,d))) := by
  ext b d
  simp [conjMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, tensorGate_apply,
    Matrix.one_apply, Matrix.submatrix_apply, Fintype.sum_prod_type, apply_ite,
    mul_ite, ite_mul, Finset.sum_mul, Finset.mul_sum]

/-- On the embedded pure data matrix family in finite coordinates, the amplified controlled copy
channel acts exactly as conjugation by the control phase gate with identity on the phase
register. -/
private theorem copyPureStep_fin (M : ℕ) (θ : ℝ)
    (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    ChannelAmplification (controlledCopyChannelMap copyPureDensity θ) M (copyPureFinEmbed M A) =
      copyPureFinEmbed M (MatrixMap.conj (TensorGate (1 : Operator M) (copyPureControlPhase θ)) A) := by
  ext ⟨a,k⟩ ⟨c,l⟩
  obtain ⟨⟨b,i⟩, rfl⟩ := (controlDataEquiv 2).surjective k
  obtain ⟨⟨d,j⟩, rfl⟩ := (controlDataEquiv 2).surjective l
  simp only [ChannelAmplification, copyPureFinEmbed, relabelGate_apply',
    copyQPERegisterEquiv, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Prod.map, Equiv.symm_apply_apply]
  let B : Matrix Bool Bool ℂ := fun b d => A (a,b) (c,d)
  have hb : (fun x y : Fin 4 => copyPureEmbed M A
      (a,(controlDataEquiv 2).symm x) (c,(controlDataEquiv 2).symm y)) =
      relabelGate (controlDataEquiv 2) (TensorGate B copyPureDensity) := by
    ext x y
    rfl
  rw [hb, controlledCopyChannelMap_relabel, controlledCopyRawMap_pure_data]
  simp only [relabelGate_apply', Equiv.symm_apply_apply, tensorGate_apply, copyPureEmbed_apply]
  have hc := copyPureSpectatorConj M (copyPureControlPhase θ) A a c
  exact congrArg (fun T : Matrix Bool Bool ℂ => T b d * copyPureDensity i j) hc.symm

/-- The `n`th power of the pure data control phase gate at angle `theta` equals the gate at
angle `n * theta`. -/
private theorem copyPureControlPhase_pow (θ : ℝ) (n : ℕ) :
    (copyPureControlPhase θ) ^ n = copyPureControlPhase ((n : ℝ) * θ) := by
  rw [copyPureControlPhase, Matrix.diagonal_pow, copyPureControlPhase]
  apply congrArg (Matrix.diagonal : (Bool → ℂ) → Matrix Bool Bool ℂ)
  funext b
  cases b
  · simp
  · simp only [Pi.pow_apply, ↓reduceIte]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- Taking a natural power of identity on the phase register tensored with a control matrix
equals tensoring that identity with the same power of the control matrix. -/
private theorem copyPureSpectator_pow (M : ℕ) (P : Matrix Bool Bool ℂ) (n : ℕ) :
    (TensorGate (1 : Operator M) P) ^ n = TensorGate (1 : Operator M) (P ^ n) := by
  induction n with
  | zero => simp [tensorGate_one]
  | succ n ih => rw [pow_succ, ih, tensorGate_mul, Matrix.one_mul, pow_succ]

/-- On embedded pure data matrices in finite coordinates, `n` amplified controlled copy steps
equal conjugation of the phase and control matrix by the `n`th power of the spectator
control phase gate. -/
private theorem copyPureRun_fin (M : ℕ) (θ : ℝ) (n : ℕ)
    (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    ChannelAmplification (copyMapPower (controlledCopyChannelMap copyPureDensity θ) n) M
      (copyPureFinEmbed M A) =
      copyPureFinEmbed M (MatrixMap.conj
        ((TensorGate (1 : Operator M) (copyPureControlPhase θ)) ^ n) A) := by
  induction n with
  | zero =>
    have hid : ChannelAmplification (LinearMap.id : Operator 4 →ₗ[ℂ] Operator 4) M
        (copyPureFinEmbed M A) = copyPureFinEmbed M A := by ext p q; rfl
    simp only [copyMapPower, pow_zero, conjMap_apply, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
    exact hid
  | succ n ih =>
    have he : ChannelAmplification (copyMapPower (controlledCopyChannelMap copyPureDensity θ) (n+1)) M
        (copyPureFinEmbed M A) = ChannelAmplification (controlledCopyChannelMap copyPureDensity θ) M
          (ChannelAmplification (copyMapPower (controlledCopyChannelMap copyPureDensity θ) n) M
            (copyPureFinEmbed M A)) := by ext p q; rfl
    rw [he, ih, copyPureStep_fin]
    apply congrArg (copyPureFinEmbed M)
    simp only [conjMap_apply, pow_succ', Matrix.conjTranspose_mul]
    noncomm_ring

/-- For positive `n`, the actual time pi copy query on the pure data matrix family equals
conjugation of its phase and control matrix by the time pi control phase gate, followed by
the pure data embedding. -/
private theorem copyPureQuery_actual (M n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    copyQPEQuery 2 M n copyPureDensity (copyPureEmbed M A) =
      copyPureEmbed M (MatrixMap.conj
        (TensorGate (1 : Operator M) (copyPureControlPhase Real.pi)) A) := by
  unfold copyQPEQuery controlledCopyRunMap
  change relabelGate (copyQPERegisterEquiv 2 M).symm
    (ChannelAmplification (copyMapPower
      (controlledCopyChannelMap copyPureDensity (Real.pi / (n : ℝ))) n) M
      (copyPureFinEmbed M A)) = _
  rw [copyPureRun_fin, copyPureSpectator_pow, copyPureControlPhase_pow, nat_mul_div_self hn Real.pi]
  exact relabelGate_relabelGate (copyQPERegisterEquiv 2 M) _

/-- Hamiltonian evolution under `copyPureDensity` is diagonal, applying `exp (-I * theta)` to
the zero data basis state and phase one to the other basis state. -/
private theorem copyPureEvolution_data (θ : ℝ) :
    hamiltonianEvolution copyPureDensity θ =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then Complex.exp (-Complex.I * (θ : ℂ)) else 1) := by
  have hd : copyPureDensity = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [copyPureDensity, outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket, Matrix.diagonal_apply]
  unfold hamiltonianEvolution
  rw [hd]
  have he : (-Complex.I * (θ : ℂ)) •
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0) =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then -Complex.I * (θ : ℂ) else 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  rw [he, Matrix.exp_diagonal]
  apply congrArg (Matrix.diagonal : (Fin 2 → ℂ) → Operator 2)
  funext i
  rw [Pi.coe_exp]
  by_cases hi : i = 0 <;> simp [hi, ← Complex.exp_eq_exp_ℂ]

/-- Ideal controlled evolution on a control matrix tensored with `copyPureDensity` conjugates
only the control factor by `copyPureControlPhase`. -/
private theorem copyPureIdeal_raw (θ : ℝ) (B : Matrix Bool Bool ℂ) :
    MatrixMap.conj (controlOracle (hamiltonianEvolution copyPureDensity θ))
      (TensorGate B copyPureDensity) =
      TensorGate (MatrixMap.conj (copyPureControlPhase θ) B) copyPureDensity := by
  rw [copyPureEvolution_data]
  ext ⟨b,i⟩ ⟨c,j⟩
  cases b <;> cases c <;> fin_cases i <;> fin_cases j <;>
    simp [conjMap_apply, controlOracle, select, copyPureControlPhase, copyPureDensity,
      outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, tensorGate_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      RCLike.star_def] <;> ring

/-- For any finite auxiliary index type, each fixed phase block of conjugation by identity
tensored with an auxiliary matrix equals conjugation of that block by the auxiliary matrix. -/
private theorem copyPureFullSpectatorConj {J : Type*} [Fintype J] [DecidableEq J]
    (M : ℕ) (P : Matrix J J ℂ) (A : Matrix (Fin M × J) (Fin M × J) ℂ) (a c : Fin M) :
    (MatrixMap.conj (TensorGate (1 : Operator M) P) A).submatrix
      (fun b => (a,b)) (fun d => (c,d)) =
      MatrixMap.conj P (A.submatrix (fun b => (a,b)) (fun d => (c,d))) := by
  ext b d
  simp [conjMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, tensorGate_apply,
    Matrix.one_apply, Matrix.submatrix_apply, Fintype.sum_prod_type, apply_ite,
    mul_ite, ite_mul, Finset.sum_mul, Finset.mul_sum]

/-- The ideal time pi query on the pure data embedding acts exactly as conjugation of its phase
and control matrix by the time pi control phase gate. -/
private theorem copyPureQuery_ideal (M : ℕ)
    (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    MatrixMap.conj (TensorGate (1 : Operator M)
      (controlOracle (hamiltonianEvolution copyPureDensity Real.pi))) (copyPureEmbed M A) =
      copyPureEmbed M (MatrixMap.conj
        (TensorGate (1 : Operator M) (copyPureControlPhase Real.pi)) A) := by
  ext ⟨a,b,i⟩ ⟨c,d,j⟩
  let B : Matrix Bool Bool ℂ := fun b d => A (a,b) (c,d)
  have hb : (copyPureEmbed M A).submatrix (fun p => (a,p)) (fun q => (c,q)) =
      TensorGate B copyPureDensity := by ext p q; rfl
  have ht := copyPureFullSpectatorConj M (controlOracle
    (hamiltonianEvolution copyPureDensity Real.pi)) (copyPureEmbed M A) a c
  rw [hb, copyPureIdeal_raw] at ht
  have hx := congrArg (fun T : Matrix (Bool × Fin 2) (Bool × Fin 2) ℂ => T (b,i) (d,j)) ht
  simp only [Matrix.submatrix_apply, tensorGate_apply] at hx
  rw [copyPureEmbed_apply]
  have hs := copyPureSpectatorConj M (copyPureControlPhase Real.pi) A a c
  exact hx.trans (congrArg (fun T : Matrix Bool Bool ℂ => T b d * copyPureDensity i j) hs.symm)

/-- Relabeling a matrix conjugation equals conjugation of the relabeled input by the relabeled
gate. -/
private theorem copyPureConj_relabel {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (U X : Matrix I I ℂ) :
    relabelGate e (MatrixMap.conj U X) =
      MatrixMap.conj (relabelGate e U) (relabelGate e X) := by
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  have hs : f Uᴴ = (f U)ᴴ := by ext i j; rfl
  change f (U * X * Uᴴ) = f U * f X * (f U)ᴴ
  rw [map_mul, map_mul, hs]

/-- A gate acting only on the phase and control registers, tensored with identity on the data
register and reassociated, preserves the family of pure data embedded matrices. -/
private theorem copyPure_gate_closed (M : ℕ) (U : Matrix (Fin M × Bool) (Fin M × Bool) ℂ)
    (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    ∃ B, MatrixMap.conj
      (relabelGate (Equiv.prodAssoc (Fin M) Bool (Fin 2)) (TensorGate U (1 : Operator 2)))
      (copyPureEmbed M A) = copyPureEmbed M B := by
  refine ⟨MatrixMap.conj U A, ?_⟩
  rw [copyPureEmbed, ← copyPureConj_relabel, copyPureEmbed]
  apply congrArg (relabelGate (Equiv.prodAssoc (Fin M) Bool (Fin 2)))
  rw [conjMap_apply, tensorGate_conjTranspose, Matrix.conjTranspose_one,
    tensorGate_mul, tensorGate_mul, Matrix.one_mul, Matrix.mul_one]
  rfl

/-- Rewrites a gate on the phase register with identity on control and data as the reassociated
tensor product of a phase and control gate with identity on data. -/
private theorem copyPurePhaseGate_lift (M : ℕ) (G : Operator M) :
    TensorGate G (1 : Matrix (Bool × Fin 2) (Bool × Fin 2) ℂ) =
      relabelGate (Equiv.prodAssoc (Fin M) Bool (Fin 2))
        (TensorGate (TensorGate G (1 : Matrix Bool Bool ℂ)) (1 : Operator 2)) := by
  rw [relabelGate_prodAssoc, tensorGate_one]

/-- Rewrites the phase threshold flip permutation as a phase and control permutation tensored
with identity on the data register, after reassociation. -/
private theorem copyPureThreshold_lift (M k : ℕ) :
    permMatrix (phaseThresholdFlip (I := Fin 2) M k) =
      relabelGate (Equiv.prodAssoc (Fin M) Bool (Fin 2))
        (TensorGate (permMatrix (fun p : Fin M × Bool =>
          (p.1, if k < p.1.val then !p.2 else p.2))) (1 : Operator 2)) := by
  ext ⟨a,b,i⟩ ⟨c,d,j⟩
  change (if (a,(b,i)) = (c,(if k < c.val then !d else d,j)) then (1 : ℂ) else 0) =
    (if (a,b) = (c,if k < c.val then !d else d) then 1 else 0) * (if i = j then 1 else 0)
  simp only [Prod.mk.injEq, ite_and, ite_mul]
  split_ifs <;> simp_all

/-- States that every gate step of a circuit maps every pure data embedded matrix to another
matrix in the same embedded family under conjugation. -/
private def copyPureClosed (M : ℕ) (C : Circuit (Fin M × (Bool × Fin 2))) : Prop :=
  ∀ U, Step.gate U ∈ C → ∀ A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ,
    ∃ B, MatrixMap.conj U (copyPureEmbed M A) = copyPureEmbed M B

/-- Every gate in the counted phase estimation circuit with four phase labels preserves the pure
data embedded matrix family. -/
private theorem copyPureCounted4_closed : copyPureClosed 4 (countedPhaseCircuit 4) := by
  intro U hU A
  have hne (W : Matrix (Fin 4 × (Bool × Fin 2)) (Fin 4 × (Bool × Fin 2)) ℂ) :
      Step.gate W ≠ (Step.query : Step (Fin 4 × (Bool × Fin 2))) := by intro h; cases h
  simp only [countedPhaseCircuit, phaseThresholdLoop, phaseThresholdBlock,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false, false_or, or_assoc, Step.gate.injEq, hne] at hU
  rcases hU with hU | hU | hU | hU | hU | hU | hU | hU
  all_goals subst U
  all_goals first
    | (rw [copyPurePhaseGate_lift]; exact copyPure_gate_closed 4 _ A)
    | (rw [copyPureThreshold_lift]; exact copyPure_gate_closed 4 _ A)

/-- For positive `n`, actual and ideal copy programs agree on all pure data embedded matrices
whenever each circuit gate preserves that matrix family. -/
private theorem copyPureProgram_exact (M n : ℕ) (hn : 0 < n)
    (C : Circuit (Fin M × (Bool × Fin 2))) (hC : copyPureClosed M C)
    (A : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) :
    copyQPEProgram 2 M n copyPureDensity C (copyPureEmbed M A) =
      copyQPEIdealProgram 2 M copyPureDensity C (copyPureEmbed M A) := by
  induction C generalizing A with
  | nil => rfl
  | cons s C ih =>
    have ht : copyPureClosed M C := fun U hU => hC U (List.mem_cons_of_mem _ hU)
    cases s with
    | gate U =>
      obtain ⟨B, hB⟩ := hC U List.mem_cons_self A
      simp only [copyQPEProgram, copyQPEIdealProgram, hB]
      exact ih ht B
    | query =>
      simp only [copyQPEProgram, copyQPEIdealProgram, copyPureQuery_actual M n hn,
        copyPureQuery_ideal M]
      exact ih ht _

/-- For every positive step count, the actual and ideal copy phase estimation outputs agree
exactly for `copyPureDensity` and four phase labels. -/
private theorem copyPureOutput_exact (n : ℕ) (hn : 0 < n) :
    copyQPEOutput 2 4 n copyPureDensity = copyQPEIdealOutput 2 4 copyPureDensity := by
  let A :=
      outerProduct
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 4)) (Qatlib.Foundations.PureStateMath.Ket false))
  have he : copyQPEInput 2 4 copyPureDensity = copyPureEmbed 4 A := by
    rw [copyQPEInput, dif_pos (by decide : 0 < 4)]
    dsimp [A, copyPureEmbed]
    rw [outerProduct_tensorState, relabelGate_prodAssoc]
  rw [copyQPEOutput, copyQPEIdealOutput, he]
  exact copyPureProgram_exact 4 n hn _ copyPureCounted4_closed A

/-- For the two dimensional projector onto the zero basis state and any positive `n`, actual
copy phase estimation with four labels assigns mass one to label two. This concrete density
matrix exponentiation example in the setting of [LloydMohseniRebentrost2014] has resource
tuple exactly `(3 * n, 3 * n, 3 * n, 0)`. -/
theorem copy_qpe_rank_one_actual_readout_consumer (n : ℕ) (hn : 0 < n) :
    let ρ : Operator 2 := outerProduct (Qatlib.Foundations.PureStateMath.Ket 0)
    copyQPELabelMass 2 4 (copyQPEOutput 2 4 n ρ) (2 : Fin 4) = 1 ∧
      copyQPEResources 2 4 n = (3 * n, 3 * n, 3 * n, 0) := by
  change copyQPELabelMass 2 4 (copyQPEOutput 2 4 n copyPureDensity) (2 : Fin 4) = 1 ∧ _
  refine ⟨?_, ?_⟩
  · rw [copyPureOutput_exact n hn]
    have hs : copyPureDensity = (1 : Operator 2) *
        Matrix.diagonal (fun i : Fin 2 => ((if i = 0 then 1 else 0 : ℝ) : ℂ)) * (1 : Operator 2)ᴴ := by
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [copyPureDensity, outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket, Matrix.diagonal_apply]
    have h := copyQPEIdealOutput_spectral_label 2 4 (by decide) copyPureDensity 1
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) (Submonoid.one_mem _) hs (2 : Fin 4)
    norm_num [Fin.sum_univ_two] at h
    have hg :=
        (offgrid_phase_geometric_and_periodic 4 (-1/2) (2 : Fin 4) (by decide)).2.2 (2 : Fin 4)
    norm_num [Qatlib.Foundations.PureStateMath.Ket] at hg
    have hp := (offgrid_phase_geometric_and_periodic 4 (-1/2) (2 : Fin 4) (by decide)).1
    norm_num at hp
    have hk : qpeKernel 4 (-(1/2)) (2 : Fin 4) = 1 := hp.symm.trans hg
    rw [hk] at h
    simpa using h
  · simpa using copy_qpe_same_path_fresh_resource_counts 2 4 n (by decide) hn

end CopyPureReadout
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
