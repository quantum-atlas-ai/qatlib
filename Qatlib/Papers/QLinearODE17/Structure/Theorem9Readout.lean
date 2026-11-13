/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.Structure.Theorem9QLS
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Quan

/-!
# Block normalization and Taylor success mass

This module relates normalization of Taylor-system states to normalization and norms of their
label blocks. It expresses the success-set mass as the sum of the squared norms of the final and
padding blocks and bounds block errors by the full state error.

The final estimate turns uniform lower bounds on successful block norms into a lower bound on
normalized success mass, as needed for the ODE readout in [BerryEtAl2017ODE].

## Main statements

* `taylor_success_mass_blocks`: Success mass as a sum over final and padding blocks.
* `taylor_block_error_le`: Block projection contracts state error.
* `taylor_normalized_success_mass`: A lower bound from the norms of all successful blocks.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.StructureCore
open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

/-- Embedding a real scalar in the complex numbers before scaling a state agrees with real
scalar multiplication of its state vector. -/
theorem taylor_state_real_smul {I : Type} (r : ℝ) (u : QState I) :
    stateVector ((r : ℂ) • u)=r • stateVector u := by
  have he : (r : ℂ) • u=r • u := by ext i; simp [Complex.real_smul]
  rw [he,stateVector_real_smul]

/-- Scaling a state by the complex reciprocal of its state-vector norm gives the normalized
state vector. -/
theorem taylor_state_inv_norm {I : Type} [Fintype I] (x : QState I) :
    stateVector (((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x)=NormedSpace.normalize (stateVector x) := by
  rw [← Complex.ofReal_inv,taylor_state_real_smul]
  rfl

variable {N : Type} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in

/-- The Taylor success-set mass is the sum of the squared norms of the final time block and its
p padding blocks. -/
theorem taylor_success_mass_blocks (m k p : ℕ)
    (ψ : QState (Fin (m*(k+1)+p+1) × N)) :
    MeasureProb ψ (taylorSuccessSet m k p) =
      ∑ j : Fin (p+1),‖stateVector (taylorBlock ψ (taylorFinalLabel m k p j.val (Nat.le_of_lt_succ j.isLt)))‖^2 := by
  have he : MeasureProb ψ (taylorSuccessSet m k p) =
      ∑ l∈Finset.univ.filter (fun l : Fin (m*(k+1)+p+1) => m*(k+1) ≤ l.val),
        ‖stateVector (taylorBlock ψ l)‖^2 := by
    simp [MeasureProb,taylorSuccessSet,BornProb,stateVector_norm_sq,taylorBlock,
      Fintype.sum_prod_type,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : m*(k+1) ≤ l.val <;> simp [hl]
  rw [he]
  refine Finset.sum_bij (fun l hl => (⟨l.val-m*(k+1),by
    have hlow := (Finset.mem_filter.mp hl).2
    have := l.isLt
    omega⟩ : Fin (p+1))) ?_ ?_ ?_ ?_
  · intro l hl; exact Finset.mem_univ _
  · intro l hl r hr heq
    have hll := (Finset.mem_filter.mp hl).2
    have hrl := (Finset.mem_filter.mp hr).2
    apply Fin.ext
    have heq' := congrArg Fin.val heq
    (try dsimp only at heq')
    omega
  · intro j _
    refine ⟨taylorFinalLabel m k p j.val (Nat.le_of_lt_succ j.isLt),?_,?_⟩
    · simp [taylorFinalLabel]
    · apply Fin.ext
      simp [taylorFinalLabel]
  · intro l hl
    congr 3
    apply congrArg (taylorBlock ψ)
    apply Fin.ext
    have hlow := (Finset.mem_filter.mp hl).2
    dsimp only [taylorFinalLabel]
    omega

omit [DecidableEq N] in

/-- The norm of the difference between corresponding label blocks is at most the norm of the
difference between the full state vectors. -/
theorem taylor_block_error_le {d : ℕ} (φ ψ : QState (Fin d × N)) (l : Fin d) :
    ‖stateVector (taylorBlock φ l)-stateVector (taylorBlock ψ l)‖ ≤
      ‖stateVector φ-stateVector ψ‖ := by
  have he : stateVector (taylorBlock φ l)-stateVector (taylorBlock ψ l)=
      stateVector (taylorBlock (φ-ψ) l) := rfl
  have hf : stateVector φ-stateVector ψ=stateVector (φ-ψ) := rfl
  rw [he,hf]
  have hs : ‖stateVector (taylorBlock (φ-ψ) l)‖^2 ≤ ‖stateVector (φ-ψ)‖^2 := by
    simp only [stateVector_norm_sq,MeasureProb,BornProb,Fintype.sum_prod_type,taylorBlock]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin d => ∑ n : N,‖(φ-ψ) (j,n)‖^2)
      (fun j _ => Finset.sum_nonneg (fun _ _ => by positivity))
      (Finset.mem_univ l)
  nlinarith [norm_nonneg (stateVector (taylorBlock (φ-ψ) l)),norm_nonneg (stateVector (φ-ψ))]

omit [DecidableEq N] in

/-- If a block norm is at least a times the positive full-state norm, then after full-state
normalization its block norm is at least a. -/
theorem taylor_normalized_block_lower {d : ℕ} (x : QState (Fin d × N))
    (hx : 0 < ‖stateVector x‖) (l : Fin d) (a : ℝ)
    (ha : a*‖stateVector x‖ ≤ ‖stateVector (taylorBlock x l)‖) :
    a ≤ ‖stateVector (taylorBlock (((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x) l)‖ := by
  have he : taylorBlock (((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x) l=
      ((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • taylorBlock x l := rfl
  rw [he,← Complex.ofReal_inv,taylor_state_real_smul,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hx.le),inv_mul_eq_div]
  exact (le_div_iff₀ hx).mpr ha

omit [DecidableEq N] in

/-- Scaling a nonzero full state by the reciprocal of its norm preserves the normalized
direction of each block. -/
theorem taylor_normalized_block_direction {d : ℕ} (x : QState (Fin d × N))
    (hx : 0 < ‖stateVector x‖) (l : Fin d) :
    NormedSpace.normalize (stateVector (taylorBlock (((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x) l))=
      NormedSpace.normalize (stateVector (taylorBlock x l)) := by
  have he : taylorBlock (((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x) l=
      ((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • taylorBlock x l := rfl
  rw [he,← Complex.ofReal_inv,taylor_state_real_smul,NormedSpace.normalize_smul_of_pos (inv_pos.mpr hx)]

omit [DecidableEq N] in

/-- If each of the p + 1 successful blocks has norm at least ‖x‖/√D with D > 0 and ‖x‖ > 0, then
the square root of the normalized success mass is at least √((p + 1)/D). -/
theorem taylor_normalized_success_mass (m k p : ℕ) (D : ℝ) (hD : 0 < D)
    (x : QState (Fin (m*(k+1)+p+1) × N)) (hx : 0 < ‖stateVector x‖)
    (hb : ∀ j : Fin (p+1),
      (1/Real.sqrt D)*‖stateVector x‖ ≤
        ‖stateVector (taylorBlock x (taylorFinalLabel m k p j.val (Nat.le_of_lt_succ j.isLt)))‖) :
    Real.sqrt ((p+1 : ℕ)/D) ≤
      Real.sqrt (MeasureProb (((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x) (taylorSuccessSet m k p)) := by
  apply Real.sqrt_le_sqrt
  rw [taylor_success_mass_blocks]
  have hpoint (j : Fin (p+1)) : ((1 : ℝ)/Real.sqrt D)^2 ≤
      ‖stateVector (taylorBlock (((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x)
        (taylorFinalLabel m k p j.val (Nat.le_of_lt_succ j.isLt)))‖^2 := by
    have hlo := taylor_normalized_block_lower x hx _ ((1 : ℝ)/Real.sqrt D) (hb j)
    exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 : ℝ)/Real.sqrt D) hlo 2
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
  have he : (1/Real.sqrt D)^2=1/D := by rw [div_pow,one_pow,Real.sq_sqrt hD.le]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,he,
    mul_one_div] using! hs

end Qatlib.Papers.QLinearODE17.StructureCore
