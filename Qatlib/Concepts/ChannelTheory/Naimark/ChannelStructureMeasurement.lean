/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Pure-state measurement updates and instrument statistics

Outer-product identities relate pure-state collapse and normalization to projected density
matrices, including zero-mass events. A two-dimensional reset channel supplies
`instrument_pair_same_stats`, exhibiting instruments with identical outcome probabilities and
different state updates.

The mathematical background is described in [Kraus1983].

## Main statements

* `postMeasure_outerProduct`: the density matrix of a positive-mass conditional pure state.
* `postMeasure_zero_mass`: vanishing state and density branch for zero mass.
* `instrument_pair_same_stats`: equal statistics can accompany different branch maps.

## References

* [Kraus, 1983][Kraus1983]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false

open Matrix
open Qatlib
open scoped Classical ComplexOrder BigOperators

variable {D E : ℕ}

namespace Qatlib.Concepts.ChannelTheory.Naimark

/-- Scaling a state by `c` scales its outer product by `c * star c`. -/
theorem outerProduct_smul {D : ℕ} (c : ℂ) (ψ : QState (Fin D)) :
    outerProduct (c • ψ) = (c * starRingEnd ℂ c) • outerProduct ψ := by
  ext i j
  show (c • ψ) i * starRingEnd ℂ ((c • ψ) j)
    = (c * starRingEnd ℂ c) * (ψ i * starRingEnd ℂ (ψ j))
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- The outer product of `Pψ` is `P * outerProduct ψ * Pᴴ`. -/
theorem outerProduct_mulVec {D E : ℕ} (P : Matrix (Fin D) (Fin E) ℂ) (ψ : QState (Fin E)) :
    outerProduct (P *ᵥ ψ) = P * outerProduct ψ * P.conjTranspose := by
  have hmv : ∀ i : Fin D, (P *ᵥ ψ) i = ∑ x : Fin E, P i x * ψ x := by
    intro i
    simp [Matrix.mulVec, dotProduct]
  ext i j
  simp only [outerProduct_apply, hmv, map_sum, map_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, starRingEnd_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Projecting both sides of a pure-state outer product gives the outer product of the collapsed
vector. -/
theorem projector_outerProduct_projector {D : ℕ} (S : Finset (Fin D)) (ψ : QState (Fin D)) :
    Projector S * outerProduct ψ * Projector S = outerProduct (Collapse ψ S) := by
  have hP : (Projector S).conjTranspose = Projector S := projector_conjTranspose S
  have h : outerProduct (Collapse ψ S)
      = Projector S * outerProduct ψ * (Projector S).conjTranspose := by
    unfold Collapse ApplyGate
    exact outerProduct_mulVec (Projector S) ψ
  rw [hP] at h
  exact h.symm

/-- For a positive-mass event, the outer product of the postmeasurement state is the projected
outer product divided by the event mass. -/
theorem postMeasure_outerProduct {D : ℕ} (S : Finset (Fin D)) (ψ : QState (Fin D))
    (h : 0 < MeasureProb ψ S) :
    outerProduct (PostMeasure ψ S)
      = (((MeasureProb ψ S : ℝ) : ℂ)⁻¹) • (Projector S * outerProduct ψ * Projector S) := by
  have hform : PostMeasure ψ S
      = ((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ)⁻¹ • Collapse ψ S := by
    funext i
    simp [PostMeasure, Pi.smul_apply]
  rw [hform, outerProduct_smul, projector_outerProduct_projector]
  have hne : ((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ) ≠ 0 := by
    have := Real.sqrt_pos_of_pos h
    exact_mod_cast this.ne'
  have hsq : ((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ) *
      ((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ) = (((MeasureProb ψ S : ℝ) : ℂ)) :=
    by exact_mod_cast Real.mul_self_sqrt (le_of_lt h)
  have hinv : (((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ))⁻¹ *
      starRingEnd ℂ (((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ))⁻¹
      = (((MeasureProb ψ S : ℝ) : ℂ))⁻¹ := by
    have hi : starRingEnd ℂ (((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ))⁻¹
        = (((Real.sqrt (MeasureProb ψ S) : ℝ) : ℂ))⁻¹ := by simp
    rw [hi, ← mul_inv, hsq]
  rw [hinv]

/-- For a zero-mass event, both the postmeasurement state and the projected outer product
vanish. -/
theorem postMeasure_zero_mass {D : ℕ} (S : Finset (Fin D)) (ψ : QState (Fin D))
    (h : MeasureProb ψ S = 0) :
    PostMeasure ψ S = 0 ∧ Projector S * outerProduct ψ * Projector S = 0 := by
  refine ⟨postMeasure_eq_zero_of_measureProb_eq_zero h, ?_⟩
  rw [projector_outerProduct_projector]
  have hcol : Collapse ψ S = 0 := by
    funext i
    by_cases hi : i ∈ S
    · have hsum : BornProb ψ i ≤ MeasureProb ψ S :=
        Finset.single_le_sum (fun j _ => bornProb_nonneg ψ j) hi
      have hbi : BornProb ψ i = 0 := by
        unfold BornProb at hsum ⊢
        rw [h] at hsum
        exact le_antisymm hsum (sq_nonneg _)
      have hzi : ψ i = 0 := by
        unfold BornProb at hbi
        have hnn : ‖ψ i‖ * ‖ψ i‖ = 0 := by
          rw [← pow_two]
          exact hbi
        exact norm_eq_zero.mp (mul_self_eq_zero.mp hnn)
      simp [collapse_apply, hi, hzi]
    · simp [collapse_apply, hi]
  rw [hcol]
  ext i j
  simp [outerProduct]

/-- The two Kraus matrices mapping each computational basis state of a qubit to basis state
zero. -/
noncomputable def kDrop : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![matrixUnit 0 0, matrixUnit 0 1]

/-- The two reset Kraus matrices satisfy the Kraus completeness relation. -/
theorem krausDrop_complete : KrausComplete (n := 2) kDrop := by
  show ∑ k : Fin 2, (kDrop k).conjTranspose * kDrop k = 1
  rw [Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kDrop, matrixUnit, Matrix.single, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, ite_and, mul_ite]

/-- The reset Kraus sum sends an operator `A` to its trace times the projector onto basis state
zero. -/
theorem krausDrop_apply (A : Operator 2) :
    (∑ k : Fin 2, kDrop k * A * (kDrop k).conjTranspose)
      = Matrix.trace A • matrixUnit 0 0 := by
  rw [Fin.sum_univ_two]
  simp only [kDrop]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixUnit, Matrix.single, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two,
      ite_and, mul_ite]

/-- There exist two one-outcome qubit instruments with equal probabilities on every operator but
different branch outputs on some operator. -/
theorem instrument_pair_same_stats :
    ∃ (I₁ I₂ : Instrument (Fin 1) 2 2) (ρ : Operator 2) (o : Fin 1),
      (∀ (ρ' : Operator 2) (o' : Fin 1),
        instrumentProb I₁ ρ' o' = instrumentProb I₂ ρ' o') ∧
      I₁.branch o ρ ≠ I₂.branch o ρ := by
  classical
  let B₁ : Fin 1 → (Operator 2 →ₗ[ℂ] Operator 2) := fun _ => conjBranch (1 : Operator 2)
  let B₂ : Fin 1 → (Operator 2 →ₗ[ℂ] Operator 2) :=
    fun _ => conjBranch (kDrop 0) + conjBranch (kDrop 1)
  have hCP₁ : ∀ o, CompletelyPositive (B₁ o) := fun o => completelyPositive_conjBranch 1
  have hCP₂ : ∀ o, CompletelyPositive (B₂ o) := by
    intro o
    show CompletelyPositive (conjBranch (kDrop 0) + conjBranch (kDrop 1))
    exact CompletelyPositive.add (completelyPositive_conjBranch (kDrop 0))
      (completelyPositive_conjBranch (kDrop 1))
  have hTP₁ : ∀ A : Operator 2, Matrix.trace (∑ o : Fin 1, B₁ o A) = Matrix.trace A := by
    intro A
    rw [Fin.sum_univ_one]
    simp [B₁, conjBranch]
  have hTP₂ : ∀ A : Operator 2, Matrix.trace (∑ o : Fin 1, B₂ o A) = Matrix.trace A := by
    intro A
    rw [Fin.sum_univ_one]
    show Matrix.trace (conjBranch (kDrop 0) A + conjBranch (kDrop 1) A) = Matrix.trace A
    have h : conjBranch (kDrop 0) A + conjBranch (kDrop 1) A
        = ∑ k : Fin 2, kDrop k * A * (kDrop k).conjTranspose := by
      rw [Fin.sum_univ_two]
      simp [conjBranch_apply]
    rw [h, krausDrop_apply]
    simp [matrixUnit, Matrix.single, Matrix.trace, Fin.sum_univ_two]
  refine ⟨Instrument.ofBranches B₁ hCP₁ hTP₁, Instrument.ofBranches B₂ hCP₂ hTP₂,
      (1 : Operator 2), 0, ?_, ?_⟩
  · intro ρ' o'
    simp only [instrumentProb, Instrument.ofBranches]
    have h1 : Matrix.trace (B₁ o' ρ') = Matrix.trace ρ' := by
      simp [B₁, conjBranch]
    have h2 : Matrix.trace (B₂ o' ρ') = Matrix.trace ρ' := by
      show Matrix.trace (conjBranch (kDrop 0) ρ' + conjBranch (kDrop 1) ρ') = Matrix.trace ρ'
      have h : conjBranch (kDrop 0) ρ' + conjBranch (kDrop 1) ρ'
          = ∑ k : Fin 2, kDrop k * ρ' * (kDrop k).conjTranspose := by
        rw [Fin.sum_univ_two]
        simp [conjBranch_apply]
      rw [h, krausDrop_apply]
      simp [matrixUnit, Matrix.single, Matrix.trace, Fin.sum_univ_two]
    rw [h1, h2]
  · intro hEq
    have h1 : (Instrument.ofBranches B₁ hCP₁ hTP₁).branch 0 (1 : Operator 2) = 1 := by
      simp [Instrument.ofBranches, B₁, conjBranch]
    have h2 : (Instrument.ofBranches B₂ hCP₂ hTP₂).branch 0 (1 : Operator 2)
        = (2 : ℂ) • matrixUnit 0 0 := by
      show conjBranch (kDrop 0) (1 : Operator 2) + conjBranch (kDrop 1) 1
        = (2 : ℂ) • matrixUnit 0 0
      have h : conjBranch (kDrop 0) (1 : Operator 2) + conjBranch (kDrop 1) 1
          = ∑ k : Fin 2, kDrop k * (1 : Operator 2) * (kDrop k).conjTranspose := by
        rw [Fin.sum_univ_two]
        simp [conjBranch_apply]
      rw [h, krausDrop_apply]
      simp [matrixUnit, Matrix.single, Matrix.trace, Fin.sum_univ_two]
    rw [h1, h2] at hEq
    have hne : (1 : Operator 2) ≠ (2 : ℂ) • matrixUnit 0 0 := by
      intro h
      have := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
      simp [matrixUnit, Matrix.single, Matrix.smul_apply] at this
    exact hne hEq
end Qatlib.Concepts.ChannelTheory.Naimark
