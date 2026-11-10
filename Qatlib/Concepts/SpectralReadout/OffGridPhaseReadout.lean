/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Slope
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

set_option autoImplicit false

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def phaseDistance (x y : ℝ) : ℝ :=
  |x - y - ((⌊x - y + 1/2⌋ : ℤ) : ℝ)|

noncomputable def offGridPhase (M : ℕ) (φ : ℝ) : QState (Fin M) :=
  fun y => (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ))

noncomputable def qpeKernel (M : ℕ) (φ : ℝ) (z : Fin M) : ℂ :=
  ApplyGate (QFTMatrix M)ᴴ (offGridPhase M φ) z

theorem offGridPhase_apply (M : ℕ) (φ : ℝ) (y : Fin M) :
    offGridPhase M φ y = (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ)) := rfl

theorem qpeKernel_apply (M : ℕ) (φ : ℝ) (z : Fin M) :
    qpeKernel M φ z = ApplyGate (QFTMatrix M)ᴴ (offGridPhase M φ) z := rfl

theorem offGridPhase_int_add (M : ℕ) (φ : ℝ) (c : ℤ) (y : Fin M) :
    offGridPhase M (φ + (c : ℝ)) y = offGridPhase M φ y := by
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ + (c : ℝ))))
      = Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ)) := by
    calc
      _ = Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ)
            + 2 * Real.pi * Complex.I * ((y.val : ℝ) * (c : ℝ))) := by
          congr 1
          ring
      _ = Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ))
            * Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * (c : ℝ))) :=
        Complex.exp_add _ _
      _ = _ := by
          rw [exp_two_pi_I_nat_int y.val c, mul_one]
  rw [offGridPhase_apply, offGridPhase_apply]
  congr 1
  convert! hexp using 1
  simp

theorem offgrid_phase_kernel_formula (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 0 < M) :
    ApplyGate (QFTMatrix M)ᴴ (offGridPhase M φ) z = qpeKernel M φ z ∧
    qpeKernel M φ z = (M : ℂ)⁻¹ * ∑ y : Fin M,
      Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ - (z.val : ℝ)/(M : ℝ)))) ∧
    Normalized (offGridPhase M φ) := by
  have hconjentry : ∀ a b : Fin M,
      (starRingEnd ℂ) (QFTMatrix M a b)
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((a.val : ℤ) * (b.val : ℤ))) := by
    intro a b
    rw [qftMatrix_apply, map_mul, map_inv₀, Complex.conj_ofReal, primRoot_conj_zpow]
  have hterm : ∀ y : Fin M,
      ((starRingEnd ℂ) (QFTMatrix M y z) * offGridPhase M φ y)
        = (M : ℂ)⁻¹ * Complex.exp
            (2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ - (z.val : ℝ)/(M : ℝ)))) := by
    intro y
    rw [offGridPhase_apply, hconjentry y z, primRoot_zpow_eq_exp]
    have hreassoc : (Real.sqrt (M : ℝ) : ℂ)⁻¹
          * Complex.exp (2 * Real.pi * Complex.I *
              (((-((y.val : ℤ) * (z.val : ℤ)) : ℤ) : ℝ) / (M : ℝ)))
          * ((Real.sqrt (M : ℝ) : ℂ)⁻¹
              * Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ)))
        = (M : ℂ)⁻¹ * (Complex.exp (2 * Real.pi * Complex.I *
              (((-((y.val : ℤ) * (z.val : ℤ)) : ℤ) : ℝ) / (M : ℝ)))
            * Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ))) := by
      have hre : (Real.sqrt (M : ℝ) : ℂ)⁻¹
            * Complex.exp (2 * Real.pi * Complex.I *
                (((-((y.val : ℤ) * (z.val : ℤ)) : ℤ) : ℝ) / (M : ℝ)))
            * ((Real.sqrt (M : ℝ) : ℂ)⁻¹
                * Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ)))
          = ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (M : ℝ) : ℂ)⁻¹) *
              (Complex.exp (2 * Real.pi * Complex.I *
                  (((-((y.val : ℤ) * (z.val : ℤ)) : ℤ) : ℝ) / (M : ℝ)))
                * Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ))) := by ring
      rw [hre, inv_sqrt_mul_inv_sqrt hM]
    rw [hreassoc]
    have hexp : 2 * Real.pi * Complex.I *
            (((-((y.val : ℤ) * (z.val : ℤ)) : ℤ) : ℝ) / (M : ℝ))
          + 2 * Real.pi * Complex.I * ((y.val : ℝ) * φ)
        = 2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ - (z.val : ℝ)/(M : ℝ))) := by
      push_cast
      ring
    have hexp' : Complex.exp (2 * Real.pi * Complex.I *
            (((-((y.val : ℤ) * (z.val : ℤ)) : ℤ) : ℝ) / (M : ℝ))) *
          Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ))
        = Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ - (z.val : ℝ)/(M : ℝ)))) := by
      calc
        _ = Complex.exp (2 * Real.pi * Complex.I *
                (((-((y.val : ℤ) * (z.val : ℤ)) : ℤ) : ℝ) / (M : ℝ)) +
              2 * Real.pi * Complex.I * ((y.val : ℝ) * φ)) := by
                rw [Complex.exp_add]
        _ = _ := by
                convert! congrArg Complex.exp hexp using 1
    rw [hexp']
  refine ⟨(qpeKernel_apply M φ z).symm, ?_, ?_⟩
  · simp only [qpeKernel_apply, ApplyGate, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, RCLike.star_def]
    rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum]
  · unfold Normalized offGridPhase
    have hnorm : ∀ y : Fin M, ‖(Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ))‖ ^ 2 = (M : ℝ)⁻¹ := by
      intro y
      have h1 : ((Real.sqrt (M : ℝ) : ℂ)⁻¹) = ((Real.sqrt (M : ℝ))⁻¹ : ℝ) := by
        rw [Complex.ofReal_inv]
      have hre : (2 * Real.pi * Complex.I * ((y.val : ℝ) * φ) : ℂ).re = 0 := by
        simp only [Complex.mul_re]
        ring_nf
        simp [Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re]
      rw [norm_mul, mul_pow, norm_exp_of_re_zero hre, one_pow, h1,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
        Real.sq_sqrt (by exact_mod_cast hM.le), mul_one]
    rw [Finset.sum_congr rfl (fun y _ => hnorm y), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hM.ne' : (M : ℝ) ≠ 0)]

theorem qpeKernel_int_add (M : ℕ) (φ : ℝ) (z : Fin M) (c : ℤ) :
    qpeKernel M (φ + (c : ℝ)) z = qpeKernel M φ z := by
  unfold qpeKernel
  congr 1
  funext i
  exact offGridPhase_int_add M φ c i

private theorem kernel_pow (M : ℕ) (φ : ℝ) (z : Fin M) (y : Fin M) :
    Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ - (z.val : ℝ)/(M : ℝ)))) =
      (Complex.exp (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ)))) ^ y.val := by
  rw [← Complex.exp_nat_mul]
  have hexp : 2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ - (z.val : ℝ)/(M : ℝ)))
      = ((y.val : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ))) := by
    push_cast
    ring
  rw [hexp]

private theorem ratio_pow_eq (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 0 < M) :
    (Complex.exp (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ)))) ^ M
      = Complex.exp (2 * Real.pi * Complex.I * ((M : ℝ) * φ)) := by
  have hz : Complex.exp (2 * Real.pi * Complex.I * ((z.val : ℕ) : ℂ)) = 1 := by
    simpa using! exp_two_pi_I_nat_int z.val 1
  have hexp : ((M : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ)))
      = 2 * Real.pi * Complex.I * ((M : ℝ) * φ)
        - 2 * Real.pi * Complex.I * ((z.val : ℕ) : ℂ) := by
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    push_cast
    field_simp
  rw [← Complex.exp_nat_mul, hexp, Complex.exp_sub, hz, div_one]

theorem offgrid_phase_geometric_and_periodic (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 0 < M) :
    qpeKernel M (φ + 1) z = qpeKernel M φ z ∧
    (Complex.exp (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ))) ≠ 1 →
      qpeKernel M φ z = (M : ℂ)⁻¹ *
        (Complex.exp (2 * Real.pi * Complex.I * ((M : ℝ) * φ)) - 1) /
        (Complex.exp (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ))) - 1)) ∧
    (∀ j : Fin M, qpeKernel M ((j.val : ℝ)/(M : ℝ)) z = Ket j z) := by
  have hsum := (offgrid_phase_kernel_formula M φ z hM).2.1
  have hgrid (j : Fin M) : offGridPhase M ((j.val : ℝ)/(M : ℝ)) = PhaseState M j.val := by
    funext y
    rw [offGridPhase_apply, phaseState_apply, primRoot_zpow_eq_exp]
    congr 1
    congr 1
    push_cast
    ring
  refine ⟨by simpa using! qpeKernel_int_add M φ z 1, ?_, ?_⟩
  · intro hne
    rw [hsum]
    have hterm : ∀ y : Fin M,
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℝ) * (φ - (z.val : ℝ)/(M : ℝ))))
          = (Complex.exp (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ)))) ^ y.val :=
      kernel_pow M φ z
    rw [Finset.sum_congr rfl (fun y _ => hterm y),
      Fin.sum_univ_eq_sum_range (fun i => (Complex.exp
        (2 * Real.pi * Complex.I * (φ - (z.val : ℝ)/(M : ℝ)))) ^ i) M,
      geom_sum_eq hne M, ratio_pow_eq M φ z hM]
    ring
  · intro j
    rw [qpeKernel_apply, hgrid j, qftMatrix_conjTranspose_mulVec_phaseState hM j]

noncomputable def qpeOutput (M : ℕ) (U : Matrix I I ℂ) (ψ : QState I) :
    QState (Fin M × I) :=
  ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
    (ControlledPowers U M *ᵥ
      TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)

theorem controlledPowers_offgrid_kickback (M : ℕ) (U : Matrix I I ℂ)
    (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    ControlledPowers U M *ᵥ
        TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ =
      TensorState (offGridPhase M φ) ψ := by
  have hev := mulVec_pow_of_eigen hψ
  funext p
  obtain ⟨x, i⟩ := p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ControlledPowers,
    Matrix.of_apply, TensorState, offGridPhase]
  rw [Finset.sum_eq_single x]
  · have hsum : (∑ j : I, (U ^ x.val) i j *
          ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * ψ j)) =
        (Real.sqrt (M : ℝ) : ℂ)⁻¹ * ((U ^ x.val) *ᵥ ψ) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [if_true]
    rw [hsum, hev, Pi.smul_apply, smul_eq_mul, ← Complex.exp_nat_mul]
    have he : (x.val : ℂ) * (2 * Real.pi * Complex.I * φ) =
        2 * Real.pi * Complex.I * ((x.val : ℝ) * φ) := by push_cast; ring
    rw [he]
    ring
  · intro y _ hy
    simp [show x ≠ y from fun e => hy e.symm]
  · simp

theorem qpeOutput_eigen (M : ℕ) (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    qpeOutput M U ψ = TensorState (qpeKernel M φ) ψ := by
  rw [qpeOutput, controlledPowers_offgrid_kickback M U ψ φ hψ,
    applyGate_tensorGate, applyGate_one]
  rfl

theorem qpeOutput_sum (M : ℕ) (U : Matrix I I ℂ) {J : Type} [Fintype J]
    (v : J → QState I) (c : J → ℂ) :
    qpeOutput M U (∑ j, c j • v j) = ∑ j, c j • qpeOutput M U (v j) := by
  have ht : TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹)
      (∑ j, c j • v j) =
      ∑ j, c j • TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (v j) := by
    funext p
    simp only [TensorState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold qpeOutput ApplyGate
  rw [ht, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]

theorem offgrid_qpe_eigen_and_spectral_law (M : ℕ) (U : Matrix I I ℂ)
    (ψ : QState I) (φ : ℝ) (_hM : 0 < M) :
    (ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ →
      qpeOutput M U ψ = TensorState (qpeKernel M φ) ψ) ∧
    (∀ (J : Type) [Fintype J] (v : J → QState I) (c : J → ℂ) (p : J → ℝ),
      (∀ j k, Inner (v j) (v k) = if j = k then 1 else 0) →
      (∀ j, ApplyGate U (v j) = Complex.exp (2 * Real.pi * Complex.I * p j) • v j) →
      ∀ z : Fin M,
        MarginalProbLeft (qpeOutput M U (∑ j, c j • v j)) {z} =
          ∑ j, ‖c j‖ ^ 2 * ‖qpeKernel M (p j) z‖ ^ 2) := by
  refine ⟨qpeOutput_eigen M U ψ φ, ?_⟩
  intro J _ v c p hv he z
  rw [qpeOutput_sum]
  simp_rw [qpeOutput_eigen M U (v _) (p _) (he _)]
  have hz : (fun i => (∑ j, c j • TensorState (qpeKernel M (p j)) (v j)) (z, i)) =
      ∑ j, (c j * qpeKernel M (p j) z) • v j := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, TensorState, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [MarginalProbLeft, MeasureProb, Finset.sum_product, Finset.sum_singleton, BornProb]
  change (∑ i, ‖(fun i => (∑ j, c j • TensorState (qpeKernel M (p j)) (v j)) (z, i)) i‖^2) = _
  rw [hz, sum_norm_sq_orthonormal v _ hv]
  simp only [norm_mul, mul_pow]

def phaseThresholdFlip (M k : ℕ) (p : Fin M × (Bool × I)) : Fin M × (Bool × I) :=
  (p.1, (if k < p.1.val then !p.2.1 else p.2.1, p.2.2))

omit [Fintype I] [DecidableEq I] in

theorem phaseThresholdFlip_involutive (M k : ℕ) :
    Function.Involutive (phaseThresholdFlip (I := I) M k) := by
  rintro ⟨x, b, i⟩
  by_cases h : k < x.val <;> simp [phaseThresholdFlip, h]

def phaseThresholdBlock (M k : ℕ) : Circuit (Fin M × (Bool × I)) :=
  [.gate (permMatrix (phaseThresholdFlip M k)), .query,
    .gate (permMatrix (phaseThresholdFlip M k))]

def phaseThresholdLoop (M : ℕ) : ℕ → Circuit (Fin M × (Bool × I))
  | 0 => []
  | n + 1 => phaseThresholdLoop M n ++ phaseThresholdBlock M n

noncomputable def countedPhaseCircuit (M : ℕ) : Circuit (Fin M × (Bool × I)) :=
  [.gate (TensorGate (QFTMatrix M) (1 : Matrix (Bool × I) (Bool × I) ℂ))] ++
    phaseThresholdLoop M (M-1) ++
    [.gate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))]

def phaseFlagEmbed (M : ℕ) (ψ : QState (Fin M × I)) : QState (Fin M × (Bool × I)) :=
  fun p => if p.2.1 then 0 else ψ (p.1, p.2.2)

theorem phaseControlledOracle_apply (M : ℕ) (U : Matrix I I ℂ)
    (ψ : QState (Fin M × (Bool × I))) (x : Fin M) (b : Bool) (i : I) :
    ApplyGate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
        (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle U)) ψ (x,b,i) =
      ApplyGate (if b then U else 1) (fun j => ψ (x,b,j)) i := by
  cases b <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      TensorGate, Matrix.one_apply, Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select]

theorem phaseThresholdBlock_action (M k : ℕ) (U : Matrix I I ℂ)
    (ψ : QState (Fin M × I)) :
    Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
        (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle U)) (phaseThresholdBlock M k) (phaseFlagEmbed M ψ) =
      phaseFlagEmbed M (fun p => if k < p.1.val then
        ApplyGate U (fun i => ψ (p.1, i)) p.2 else ψ p) := by
  funext p
  obtain ⟨x, b, i⟩ := p
  simp only [phaseThresholdBlock, Run]
  rw [applyGate_permMatrix (phaseThresholdFlip_involutive M k)]
  rw [phaseControlledOracle_apply]
  simp_rw [applyGate_permMatrix (phaseThresholdFlip_involutive M k)]
  by_cases hx : k < x.val <;> cases b <;>
    simp [phaseThresholdFlip, phaseFlagEmbed, hx, ApplyGate, Matrix.mulVec, dotProduct,
        Matrix.one_apply]

theorem phaseThresholdLoop_action (M n : ℕ) (U : Matrix I I ℂ)
    (ψ : QState (Fin M × I)) :
    Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
        (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle U)) (phaseThresholdLoop M n) (phaseFlagEmbed M ψ) =
      phaseFlagEmbed M (fun p => ApplyGate (U ^ min n p.1.val)
        (fun i => ψ (p.1, i)) p.2) := by
  induction n with
  | zero => simp [phaseThresholdLoop, applyGate_one]
  | succ n ih =>
    rw [phaseThresholdLoop, run_append, ih, phaseThresholdBlock_action]
    congr 1
    funext p
    (try dsimp only)
    by_cases h : n < p.1.val
    · rw [if_pos h, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega),
        ← applyGate_mul, ← pow_succ']
    · rw [if_neg h, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

theorem phaseFlagEmbed_phaseGate (M : ℕ) (T : Matrix (Fin M) (Fin M) ℂ)
    (ψ : QState (Fin M × I)) :
    ApplyGate (TensorGate T (1 : Matrix (Bool × I) (Bool × I) ℂ)) (phaseFlagEmbed M ψ) =
      phaseFlagEmbed M (ApplyGate (TensorGate T (1 : Matrix I I ℂ)) ψ) := by
  funext p
  obtain ⟨x, b, i⟩ := p
  cases b <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, TensorGate,
      Fintype.sum_prod_type, Matrix.one_apply, phaseFlagEmbed]

theorem phaseThresholdLoop_resources (M n : ℕ) :
    QueryCount (phaseThresholdLoop (I := I) M n) = n ∧
    GateCount (phaseThresholdLoop (I := I) M n) = 2*n ∧
    IsUnitaryCircuit (phaseThresholdLoop (I := I) M n) := by
  induction n with
  | zero => simp [phaseThresholdLoop]
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · simp [phaseThresholdLoop, queryCount_append, phaseThresholdBlock, ih.1]
    · simp [phaseThresholdLoop, gateCount_append, phaseThresholdBlock, ih.2.1]
      omega
    · apply (isUnitaryCircuit_append _ _).mpr
      refine ⟨ih.2.2, ?_⟩
      simp [phaseThresholdBlock, permMatrix_unitary (phaseThresholdFlip_involutive (I := I) M n)]

theorem counted_offgrid_qpe_clean_flag (M : ℕ) (hM : 0 < M)
    (U : Matrix I I ℂ) (ψ : QState I) :
    Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle U))
      (countedPhaseCircuit M)
      (TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) ψ)) =
        (fun p => if p.2.1 then 0 else qpeOutput M U ψ (p.1,p.2.2)) ∧
    QueryCount (countedPhaseCircuit (I := I) M) = M-1 ∧
    GateCount (countedPhaseCircuit (I := I) M) = 2*(M-1)+2 ∧
    IsUnitaryCircuit (countedPhaseCircuit (I := I) M) := by
  have hinput : TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) ψ) =
      phaseFlagEmbed M (TensorState (Ket (⟨0,hM⟩ : Fin M)) ψ) := by
    funext p
    obtain ⟨x, b, i⟩ := p
    cases b <;> simp [TensorState, phaseFlagEmbed, Ket]
  have hpower : (fun p : Fin M × I =>
      ApplyGate (U ^ min (M-1) p.1.val)
        (fun i => TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ (p.1,i)) p.2) =
      ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ := by
    funext p
    obtain ⟨x, i⟩ := p
    rw [Nat.min_eq_right (by omega)]
    simp [ApplyGate, Matrix.mulVec, dotProduct, ControlledPowers, Fintype.sum_prod_type]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [countedPhaseCircuit, run_append, run_append, hinput]
    simp only [Run]
    rw [phaseFlagEmbed_phaseGate, applyGate_tensorGate, applyGate_one,
      qftMatrix_ket_zero M hM, phaseThresholdLoop_action, hpower, phaseFlagEmbed_phaseGate]
    rfl
  · simp [countedPhaseCircuit, queryCount_append, (phaseThresholdLoop_resources (I := I) M (M-1)).1]
  · simp [countedPhaseCircuit, gateCount_append,
      (phaseThresholdLoop_resources (I := I) M (M-1)).2.1]
  · simp only [countedPhaseCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate,
      isUnitaryCircuit_nil, and_true]
    exact ⟨⟨tensorGate_unitary (qftMatrix_unitary hM) (by simp),
      (phaseThresholdLoop_resources M (M-1)).2.2⟩,
      tensorGate_unitary (conjTranspose_mem_unitaryGroup (qftMatrix_unitary hM)) (by simp)⟩

private theorem sine_ratio_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ Real.pi) : Real.sin b / b ≤ Real.sin a / a := by
  have hc : ConvexOn ℝ (Icc 0 Real.pi) (fun x => -Real.sin x) :=
    neg_convexOn_iff.mpr strictConcaveOn_sin_Icc.concaveOn
  have h := hc.secant_mono
    (a := 0) (x := a) (y := b) (by simp [Real.pi_pos.le])
    ⟨ha.le, hab.trans hb⟩ ⟨ha.le.trans hab, hb⟩ ha.ne' (ne_of_gt (ha.trans_le hab)) hab
  simpa only [Real.sin_zero, neg_zero, sub_zero, neg_div, neg_le_neg_iff] using! h

private theorem cosine_square_tangent {a x : ℝ} (ha : 0 < a)
    (ha1 : a ≤ Real.pi / 2) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi / 2) :
    Real.cos a + Real.sin a / (2*a) * (a^2-x^2) ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t => Real.cos t + Real.sin a / (2*a) * t^2
  have hd (t : ℝ) : HasDerivAt f (-Real.sin t + Real.sin a/a*t) t := by
    convert! (Real.hasDerivAt_cos t).add
      (((hasDerivAt_id t).pow 2).const_mul (Real.sin a / (2*a))) using 1
    dsimp [f]
    ring
  have hl : AntitoneOn f (Icc 0 a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 a) (by fun_prop)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have h := sine_ratio_antitone ht.1 ht.2.le (by linarith [Real.pi_pos])
    have h' := (le_div_iff₀ ht.1).mp h
    linarith
  have hr : MonotoneOn f (Icc a (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a (Real.pi/2)) (by fun_prop)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have ht0 := ha.trans ht.1
    have h := sine_ratio_antitone ha ht.1.le (by linarith [ht.2, Real.pi_pos])
    have h' := (div_le_iff₀ ht0).mp h
    linarith
  have h : f a ≤ f x := by
    rcases le_total x a with h | h
    · exact hl ⟨hx0,h⟩ ⟨ha.le,le_rfl⟩ h
    · exact hr ⟨le_rfl,ha1⟩ ⟨h,hx1⟩ h
  dsimp [f] at h
  linarith

private theorem cosine_two_neighbour_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1-s^2)^2 ≤ (Real.cos (Real.pi/2*s))^2*(1+s^2) := by
  have ht0 : 0 ≤ s^2 := sq_nonneg s
  have ht1 : s^2 ≤ 1 := by nlinarith
  have hx0 : 0 ≤ Real.pi/2*s := by positivity
  have hx1 : Real.pi/2*s ≤ Real.pi/2 := by nlinarith [Real.pi_pos]
  have hcos0 : 0 ≤ Real.cos (Real.pi/2*s) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hx1⟩
  rcases le_or_gt (s^2) (1/4) with ht | ht
  · have hp : Real.pi^2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi/2*s)
    have hps := mul_nonneg ht0 (show 0 ≤ 10-Real.pi^2 by linarith)
    have hlow : 1-5/4*s^2 ≤ Real.cos (Real.pi/2*s) := by nlinarith
    have hlow0 : 0 ≤ 1-5/4*s^2 := by linarith
    have hsquare : (1-5/4*s^2)^2 ≤ (Real.cos (Real.pi/2*s))^2 := by
      nlinarith [sq_nonneg (Real.cos (Real.pi/2*s)-(1-5/4*s^2))]
    have hprod := mul_le_mul_of_nonneg_right hsquare (by positivity : 0 ≤ 1+s^2)
    have hpoly : 0 ≤ (1-5/4*s^2)^2*(1+s^2)-(1-s^2)^2 := by
      have h1 : 0 ≤ 1/2-31/16*s^2 := by linarith
      have h := add_nonneg (mul_nonneg ht0 h1)
        (show 0 ≤ 25/16*(s^2)^3 by positivity)
      nlinarith only [h]
    linarith
  · rcases le_or_gt (s^2) (2/3) with ht' | ht'
    · have hroot : (173/100 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 26/15 := by
        have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
        have := Real.sqrt_nonneg 3
        constructor <;> nlinarith
      let c : ℝ := 3*Real.pi*Real.sqrt 3/16
      have hc0 : 81/80 ≤ c := by
        dsimp [c]
        have h := mul_le_mul_of_nonneg_left hroot.1 Real.pi_pos.le
        have h' := mul_le_mul_of_nonneg_right Real.pi_gt_d2.le (by norm_num : 0 ≤ (173/100 : ℝ))
        nlinarith
      have hc1 : c ≤ 41/40 := by
        dsimp [c]
        have h := mul_le_mul_of_nonneg_left hroot.2 Real.pi_pos.le
        have h' := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le (by norm_num : 0 ≤ (26/15 : ℝ))
        nlinarith
      have hc := cosine_square_tangent (a := Real.pi/3) (x := Real.pi/2*s)
        (by positivity) (by linarith [Real.pi_pos]) hx0 hx1
      rw [Real.cos_pi_div_three, Real.sin_pi_div_three] at hc
      have he : Real.sqrt 3 / 2 / (2 * (Real.pi / 3)) *
          ((Real.pi / 3)^2 - (Real.pi/2*s)^2) = c*(4/9-s^2) := by
        dsimp [c]
        field_simp
        ring
      rw [he] at hc
      have hlow : 19/20-41/40*s^2 ≤ Real.cos (Real.pi/2*s) := by
        have h := mul_nonneg ht0 (show 0 ≤ 41/40-c by linarith)
        nlinarith
      have hlow0 : 0 ≤ 19/20-41/40*s^2 := by linarith
      have hsquare : (19/20-41/40*s^2)^2 ≤ (Real.cos (Real.pi/2*s))^2 := by
        nlinarith [sq_nonneg (Real.cos (Real.pi/2*s)-(19/20-41/40*s^2))]
      have hprod := mul_le_mul_of_nonneg_right hsquare (by positivity : 0 ≤ 1+s^2)
      have hpoly : 0 ≤ (19/20-41/40*s^2)^2*(1+s^2)-(1-s^2)^2 := by
        have hl : 0 ≤ s^2-1/4 := by linarith
        have hr : 0 ≤ 2/3-s^2 := by linarith
        calc
          _ = (21627/40000)*(2/3-s^2)^3 +
              (5589/2000)*(s^2-1/4)*(2/3-s^2)^2 +
              (816/625)*(s^2-1/4)^2*(2/3-s^2) +
              (64/625)*(s^2-1/4)^3 := by ring
          _ ≥ 0 := by positivity
      linarith
    · have hc := cosine_square_tangent (a := Real.pi/2) (x := Real.pi/2*s)
        (by positivity) le_rfl hx0 hx1
      rw [Real.cos_pi_div_two, Real.sin_pi_div_two] at hc
      have he : 0 + 1 / (2*(Real.pi/2))*
          ((Real.pi/2)^2-(Real.pi/2*s)^2) = Real.pi/4*(1-s^2) := by
        field_simp
        ring
      rw [he] at hc
      have hlow : 39/50*(1-s^2) ≤ Real.cos (Real.pi/2*s) := by
        have h := mul_nonneg (show 0 ≤ Real.pi-78/25 by linarith [Real.pi_gt_d2])
          (show 0 ≤ 1-s^2 by linarith)
        nlinarith
      have hlow0 : 0 ≤ 39/50*(1-s^2) := by positivity
      have hsquare : (39/50*(1-s^2))^2 ≤ (Real.cos (Real.pi/2*s))^2 := by
        nlinarith [sq_nonneg (Real.cos (Real.pi/2*s)-39/50*(1-s^2))]
      have hprod := mul_le_mul_of_nonneg_right hsquare (by positivity : 0 ≤ 1+s^2)
      have hp : 0 ≤ (39/50)^2*(1+s^2)-1 := by linarith
      have h := mul_nonneg hp (sq_nonneg (1-s^2))
      nlinarith only [hprod,h]

theorem qpe_two_neighbour_scalar_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    8 ≤ (Real.sin (Real.pi*δ))^2 * (1/δ^2 + 1/(1-δ)^2) := by
  have hs0 : 0 ≤ |2*δ-1| := abs_nonneg _
  have hs1 : |2*δ-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h := cosine_two_neighbour_bound hs0 hs1
  have hc : Real.cos (Real.pi/2*|2*δ-1|) = Real.sin (Real.pi*δ) := by
    calc
      _ = Real.cos |Real.pi/2*(2*δ-1)| := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)]
      _ = _ := by
        rw [Real.cos_abs, show Real.pi/2*(2*δ-1) = Real.pi*δ-Real.pi/2 by ring,
          Real.cos_sub_pi_div_two]

  have he : (Real.sin (Real.pi*δ))^2*(1/δ^2+1/(1-δ)^2) =
      (Real.sin (Real.pi*δ))^2*(δ^2+(1-δ)^2)/(δ^2*(1-δ)^2) := by
    have hD : 1-δ ≠ 0 := by linarith
    field_simp [hδ0.ne', hD]
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < δ^2*(1-δ)^2)).mpr
  rw [hc, sq_abs] at h
  nlinarith only [h]

theorem qpeKernel_geometric_identity (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 0 < M) :
    (M : ℂ) * qpeKernel M φ z *
        (Complex.exp (2*Real.pi*Complex.I*(φ-(z.val : ℝ)/(M : ℝ)))-1) =
      Complex.exp (2*Real.pi*Complex.I*((M : ℝ)*φ))-1 := by
  rw [(offgrid_phase_kernel_formula M φ z hM).2.1]
  have hterm (y : Fin M) :
      Complex.exp (2*Real.pi*Complex.I*((y.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) =
        (Complex.exp (2*Real.pi*Complex.I*(φ-(z.val : ℝ)/(M : ℝ))))^y.val := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y),
    Fin.sum_univ_eq_sum_range, mul_inv_cancel_left₀ (by exact_mod_cast hM.ne' : (M : ℂ) ≠ 0),
    geom_sum_mul, ← Complex.exp_nat_mul]
  have he : (M : ℂ)*(2*Real.pi*Complex.I*(φ-(z.val : ℝ)/(M : ℝ))) =
      2*Real.pi*Complex.I*((M : ℝ)*φ)-2*Real.pi*Complex.I*(z.val : ℝ) := by
    push_cast
    field_simp [show (M : ℂ) ≠ 0 by exact_mod_cast hM.ne']
  rw [he, Complex.exp_sub]
  have hi : Complex.exp (2*Real.pi*Complex.I*(z.val : ℝ)) = 1 := by
    simpa using! exp_two_pi_I_int (z.val : ℤ)
  rw [hi, div_one]

private theorem norm_exp_two_pi_sub_one (t : ℝ) :
    ‖Complex.exp (2*Real.pi*Complex.I*t)-1‖ = 2*|Real.sin (Real.pi*t)| := by
  have he : (2*Real.pi*Complex.I*t : ℂ) = Complex.I*((2*Real.pi*t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2*Real.pi*t)/2 = Real.pi*t by ring, Real.norm_eq_abs, abs_mul]
  norm_num

theorem qpeKernel_neighbour_lower (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 0 < M) (n c : ℤ) (δ r : ℝ)
    (hn : (M : ℝ)*φ = (n : ℝ)+δ)
    (hr : φ-(z.val : ℝ)/(M : ℝ) = (c : ℝ)+r/(M : ℝ)) (hr0 : r ≠ 0) :
    (Real.sin (Real.pi*δ))^2/(Real.pi^2*r^2) ≤ ‖qpeKernel M φ z‖^2 := by
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast hM
  have hi (t : ℝ) (k : ℤ) :
      Complex.exp (2*Real.pi*Complex.I*((k : ℝ)+t)) =
        Complex.exp (2*Real.pi*Complex.I*t) := by
    rw [show (2*Real.pi*Complex.I*((k : ℝ)+t) : ℂ) =
        2*Real.pi*Complex.I*(k : ℝ)+2*Real.pi*Complex.I*t by push_cast; ring,
      Complex.exp_add, exp_two_pi_I_int, one_mul]
  have hg := qpeKernel_geometric_identity M φ z hM
  have hnC : (M : ℂ)*(φ : ℂ) = (n : ℂ)+(δ : ℂ) := by exact_mod_cast hn
  have hrC : (φ : ℂ)-(z.val : ℂ)/(M : ℂ) = (c : ℂ)+(r : ℂ)/(M : ℂ) := by
    have h := congrArg Complex.ofReal hr
    push_cast at h
    exact h
  push_cast at hg
  rw [hnC, hrC] at hg
  have hiδ := hi δ n
  have hir := hi (r/(M : ℝ)) c
  push_cast at hiδ hir
  rw [hiδ, hir] at hg
  have hb := congrArg norm hg
  rw [norm_mul, norm_mul, Complex.norm_natCast,
    norm_exp_two_pi_sub_one] at hb
  have hnormr := norm_exp_two_pi_sub_one (r/(M : ℝ))
  push_cast at hnormr
  rw [hnormr] at hb
  have hsin := Real.abs_sin_le_abs (x := Real.pi*(r/(M : ℝ)))
  rw [abs_mul, abs_of_pos Real.pi_pos, abs_div, abs_of_pos hM0] at hsin
  have hsin' : (M : ℝ)*|Real.sin (Real.pi*(r/(M : ℝ)))| ≤ Real.pi*|r| := by
    have h := (le_div_iff₀ hM0).mp (show |Real.sin (Real.pi*(r/(M : ℝ)))| ≤
        (Real.pi*|r|)/(M : ℝ) by simpa only [mul_div_assoc] using! hsin)
    nlinarith only [h]
  have hs : |Real.sin (Real.pi*δ)| ≤ Real.pi*|r| *‖qpeKernel M φ z‖ := by
    have h := mul_nonneg (norm_nonneg (qpeKernel M φ z))
      (show 0 ≤ Real.pi*|r|-(M : ℝ)*|Real.sin (Real.pi*(r/(M : ℝ)))| by linarith)
    nlinarith only [hb,h]
  apply (div_le_iff₀ (by positivity : 0 < Real.pi^2*r^2)).mpr
  have h := pow_le_pow_left₀ (abs_nonneg (Real.sin (Real.pi*δ))) hs 2
  simpa only [mul_pow, sq_abs, mul_assoc, mul_comm, mul_left_comm] using! h

theorem phaseDistance_le_integer_distance (x y : ℝ) (c : ℤ) : phaseDistance x y ≤ |x-y-(c : ℝ)| := by
  let n : ℤ := ⌊x-y+1/2⌋
  have hn0 : -(1/2 : ℝ) ≤ x-y-(n : ℝ) := by
    have := Int.floor_le (x-y+1/2)
    dsimp [n]
    linarith
  have hn1 : x-y-(n : ℝ) ≤ 1/2 := by
    have := Int.lt_floor_add_one (x-y+1/2)
    dsimp [n]
    linarith
  change |x-y-(n : ℝ)| ≤ _
  rcases lt_trichotomy c n with hc | hc | hc
  · have hcn : (c : ℝ)+1 ≤ n := by exact_mod_cast (show c+1 ≤ n by omega)
    apply le_trans (abs_le.mpr ⟨hn0,hn1⟩)
    have := le_abs_self (x-y-(c : ℝ))
    linarith
  · rw [hc]
  · have hcn : (n : ℝ)+1 ≤ c := by exact_mod_cast (show n+1 ≤ c by omega)
    apply le_trans (abs_le.mpr ⟨hn0,hn1⟩)
    have := neg_le_abs (x-y-(c : ℝ))
    linarith

private def integerPhaseLabel (M : ℕ) (hM : 0 < M) (n : ℤ) : Fin M :=
  ⟨(n % (M : ℤ)).toNat, by
    have := Int.emod_nonneg n (show (M : ℤ) ≠ 0 by omega)
    have := Int.emod_lt_of_pos n (show (0 : ℤ) < M by omega)
    omega⟩

private theorem integerPhaseLabel_representative (M : ℕ) (hM : 0 < M) (n : ℤ) :
    (n : ℝ) = ((integerPhaseLabel M hM n).val : ℝ)+(M : ℝ)*((n / (M : ℤ) : ℤ) : ℝ) := by
  have hn := Int.emod_nonneg n (show (M : ℤ) ≠ 0 by omega)
  have he := Int.emod_add_ediv_mul n (M : ℤ)
  have hz : ((integerPhaseLabel M hM n).val : ℤ) = n % (M : ℤ) := by
    exact Int.toNat_of_nonneg hn
  rw [← hz, mul_comm] at he
  exact_mod_cast he.symm

private theorem integerPhaseLabel_ne_succ (M : ℕ) (hM : 2 ≤ M) (n : ℤ) :
    integerPhaseLabel M (by omega) n ≠ integerPhaseLabel M (by omega) (n+1) := by
  intro he
  have hn := Int.emod_nonneg n (show (M : ℤ) ≠ 0 by omega)
  have hn1 := Int.emod_nonneg (n+1) (show (M : ℤ) ≠ 0 by omega)
  have hval := congrArg Fin.val he
  dsimp [integerPhaseLabel] at hval
  have hmod : n % (M : ℤ) = (n+1) % (M : ℤ) := by omega
  have h1 := Int.emod_add_ediv_mul n (M : ℤ)
  have h2 := Int.emod_add_ediv_mul (n+1) (M : ℤ)
  have hd : (M : ℤ) ∣ (1 : ℤ) := by
    refine ⟨(n+1)/(M : ℤ)-n/(M : ℤ), ?_⟩
    nlinarith
  have := Int.natAbs_le_of_dvd_ne_zero hd (by norm_num)
  simp at this
  omega

private theorem integerPhaseLabel_offset (M : ℕ) (hM : 0 < M) (φ : ℝ) (n : ℤ) :
    φ-((integerPhaseLabel M hM n).val : ℝ)/(M : ℝ) =
      ((n/(M : ℤ) : ℤ) : ℝ) + ((M : ℝ)*φ-(n : ℝ))/(M : ℝ) := by
  have he := integerPhaseLabel_representative M hM n
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hM0]
  nlinarith only [he]

theorem offgrid_phase_window_probability (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      phaseDistance φ ((z.val : ℝ)/(M : ℝ)) ≤ 1/(M : ℝ)),
      ‖qpeKernel M φ z‖^2 ≥ 8/Real.pi^2 := by
  have hMp : 0 < M := by omega
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hMp
  let n : ℤ := ⌊(M : ℝ)*φ⌋
  let δ : ℝ := (M : ℝ)*φ-(n : ℝ)
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Int.floor_le _)
  have hδ1 : δ < 1 :=
    sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using! (Int.lt_floor_add_one ((M : ℝ)*φ)))
  have hn : (M : ℝ)*φ = (n : ℝ)+δ := by dsimp [δ]; ring
  let z₀ := integerPhaseLabel M hMp n
  let z₁ := integerPhaseLabel M hMp (n+1)
  let c₀ : ℤ := n/(M : ℤ)
  let c₁ : ℤ := (n+1)/(M : ℤ)
  have hr₀ : φ-(z₀.val : ℝ)/(M : ℝ) = (c₀ : ℝ)+δ/(M : ℝ) :=
    integerPhaseLabel_offset M hMp φ n
  have hr₁ : φ-(z₁.val : ℝ)/(M : ℝ) = (c₁ : ℝ)+(δ-1)/(M : ℝ) := by
    simpa only [Int.cast_add, Int.cast_one, sub_add_eq_sub_sub] using!
      integerPhaseLabel_offset M hMp φ (n+1)
  have hmem₀ : z₀ ∈ Finset.univ.filter (fun z : Fin M =>
      phaseDistance φ ((z.val : ℝ)/(M : ℝ)) ≤ 1/(M : ℝ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    calc
      _ ≤ |φ-(z₀.val : ℝ)/(M : ℝ)-(c₀ : ℝ)| :=
        phaseDistance_le_integer_distance _ _ c₀
      _ = δ/(M : ℝ) := by
        rw [hr₀, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      _ ≤ 1/(M : ℝ) := div_le_div_of_nonneg_right hδ1.le hMr.le
  have hmem₁ : z₁ ∈ Finset.univ.filter (fun z : Fin M =>
      phaseDistance φ ((z.val : ℝ)/(M : ℝ)) ≤ 1/(M : ℝ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    calc
      _ ≤ |φ-(z₁.val : ℝ)/(M : ℝ)-(c₁ : ℝ)| :=
        phaseDistance_le_integer_distance _ _ c₁
      _ = (1-δ)/(M : ℝ) := by
        rw [hr₁, add_sub_cancel_left, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
          (by linarith : δ-1 ≤ 0) hMr.le)]
        ring
      _ ≤ 1/(M : ℝ) := div_le_div_of_nonneg_right (by linarith) hMr.le
  by_cases hgrid : δ = 0
  · have hφ : φ = (z₀.val : ℝ)/(M : ℝ)+(c₀ : ℝ) := by
      rw [hgrid, zero_div, add_zero] at hr₀
      linarith
    have hk : qpeKernel M φ z₀ = 1 := by
      rw [hφ, qpeKernel_int_add,
        (offgrid_phase_geometric_and_periodic M 0 z₀ hMp).2.2 z₀]
      simp [Ket]
    have hsum := Finset.single_le_sum
      (fun z _ => sq_nonneg (‖qpeKernel M φ z‖)) hmem₀
    rw [hk, norm_one, one_pow] at hsum
    have hp : 8/Real.pi^2 ≤ 1 := by
      apply (div_le_one (sq_pos_of_pos Real.pi_pos)).mpr
      nlinarith [Real.pi_gt_three]
    exact hp.trans hsum
  · have hδp : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hgrid)
    have hlo₀ := qpeKernel_neighbour_lower M φ z₀ hMp n c₀ δ δ hn hr₀ hgrid
    have hlo₁ := qpeKernel_neighbour_lower M φ z₁ hMp n c₁ δ (δ-1) hn hr₁
      (by linarith)
    have hscalar := div_le_div_of_nonneg_right
      (qpe_two_neighbour_scalar_bound hδp hδ1) (sq_nonneg Real.pi)
    have hlo : 8/Real.pi^2 ≤ ‖qpeKernel M φ z₀‖^2+‖qpeKernel M φ z₁‖^2 := by
      calc
        _ ≤ (Real.sin (Real.pi*δ))^2*(1/δ^2+1/(1-δ)^2)/Real.pi^2 := hscalar
        _ = (Real.sin (Real.pi*δ))^2/(Real.pi^2*δ^2)+
            (Real.sin (Real.pi*δ))^2/(Real.pi^2*(δ-1)^2) := by
          field_simp [hδp.ne', show 1-δ ≠ 0 by linarith,
            show δ-1 ≠ 0 by linarith, Real.pi_ne_zero]
          ring
        _ ≤ _ := add_le_add hlo₀ hlo₁
    have hne : z₀ ≠ z₁ := integerPhaseLabel_ne_succ M hM n
    have hsub : {z₀,z₁} ⊆ Finset.univ.filter (fun z : Fin M =>
        phaseDistance φ ((z.val : ℝ)/(M : ℝ)) ≤ 1/(M : ℝ)) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hmem₀
      · exact hmem₁
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z _ _ => sq_nonneg (‖qpeKernel M φ z‖))
    rw [Finset.sum_pair hne] at hsum
    exact hlo.trans hsum

end Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
