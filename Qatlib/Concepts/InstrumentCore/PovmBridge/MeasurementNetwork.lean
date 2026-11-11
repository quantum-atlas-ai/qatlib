/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PovmBridge.MeasurementNetworkDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

/-!
# POVM instruments and pure-state measurement

This module connects the instrument associated with a POVM to vector-state measurement formulas.
It proves the Born probability rule, normalization for normalized inputs, vanishing of zero-mass
branches, and the projected-vector formula for conditional states when the effect is a
projection.

The same identities are established with an untouched reference system, and `part4_clause1`
collects the resulting measurement contract. The projective measurement conventions used in
[Itakura2005] are covered as a special case of the instrument framework described in
[Watrous2018].

## Main statements

* `povm_pure_probability`: pure-state branch probabilities are effect expectations.
* `povm_projective_pure_conditional`: conditional states for projective effects.
* `part4_clause1`: the combined measurement and reference-system laws.

## References

* [Itakura, 2005][Itakura2005]
* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
universe u

namespace Qatlib.Concepts.InstrumentCore.PovmBridge

open Matrix
open scoped BigOperators ComplexOrder

/-- The trace of `A * outerProduct ψ` equals the inner product of `ψ` with `A *ᵥ ψ`. -/
theorem trace_mul_outerProduct {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (ψ : QState I) :
    Matrix.trace (A * outerProduct ψ) = Qatlib.Foundations.PureStateMath.Inner ψ (A *ᵥ ψ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct_apply,
    inner_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The branch probability of a POVM instrument on `outerProduct ψ` is the real expectation of
its effect in `ψ` [Itakura2005]. -/
theorem povm_pure_probability {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D)) (o : O) :
    instrumentProb (Instrument.ofPOVM Λ) (outerProduct ψ) o =
      (Qatlib.Foundations.PureStateMath.Inner ψ ((Λ.mats o).mat *ᵥ ψ)).re := by
  rw [instrumentProb_ofPOVM, trace_mul_outerProduct]

/-- The outcome probabilities of a POVM instrument sum to one on a normalized pure state
[Itakura2005]. -/
theorem povm_pure_pmf_total {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D)) (hψ : Normalized ψ) :
    (∑ o, instrumentPMF (Instrument.ofPOVM Λ) (isDensityOperator_outerProduct hψ) o) = 1 := by
  simpa only [tsum_fintype] using
    (instrumentPMF (Instrument.ofPOVM Λ) (isDensityOperator_outerProduct hψ)).tsum_coe

/-- A zero-probability outcome of a POVM instrument on a pure input has zero branch operator
[Itakura2005]. -/
theorem povm_pure_zero_branch {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D)) (o : O)
    (hzero : instrumentProb (Instrument.ofPOVM Λ) (outerProduct ψ) o = 0) :
    (Instrument.ofPOVM Λ).branch o (outerProduct ψ) = 0 :=
  (instrumentProb_eq_zero_iff _ (outerProduct_posSemidef ψ) o).mp hzero

/-- Each effect of `binaryProjectivePOVM P hP` is idempotent. -/
theorem binaryProjectivePOVM_projection {D : ℕ} (P : HermitianMat (Fin D) ℂ)
    (hP : P.mat * P.mat = P.mat) (o : Bool) :
    ((binaryProjectivePOVM P hP).mats o).mat *
      ((binaryProjectivePOVM P hP).mats o).mat =
        ((binaryProjectivePOVM P hP).mats o).mat := by
  cases o
  · exact complement_projection P hP
  · exact hP

/-- For an idempotent POVM effect, the instrument branch on a pure input is the outer product of
the projected vector. -/
theorem povm_projective_pure_branch {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D)) (o : O)
    (hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat) :
    (Instrument.ofPOVM Λ).branch o (outerProduct ψ) =
      outerProduct ((Λ.mats o).mat *ᵥ ψ) := by
  rw [Instrument.ofPOVM_branch, hermitian_projection_half _ hproj]
  simpa only [conjBranch_apply, HermitianMat.conjTranspose_mat] using
    conjBranch_outerProduct (Λ.mats o).mat ψ

/-- For an idempotent POVM effect, the branch probability equals the total squared norm of the
projected vector. -/
theorem povm_projective_pure_mass {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D)) (o : O)
    (hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat) :
    instrumentProb (Instrument.ofPOVM Λ) (outerProduct ψ) o =
      MeasureProb ((Λ.mats o).mat *ᵥ ψ) Finset.univ := by
  unfold instrumentProb
  rw [povm_projective_pure_branch Λ ψ o hproj, trace_outerProduct]
  rfl

/-- When the total squared norm of `φ` is positive, the outer product of its normalized
post-measurement vector is its outer product scaled by the inverse mass. -/
theorem outerProduct_postMeasure_univ {I : Type*} [Fintype I] [DecidableEq I]
    (φ : QState I) (hφ : 0 < MeasureProb φ Finset.univ) :
    outerProduct (PostMeasure φ Finset.univ) =
      ((MeasureProb φ Finset.univ : ℝ) : ℂ)⁻¹ • outerProduct φ := by
  have hsq : ((Real.sqrt (MeasureProb φ Finset.univ) : ℂ)⁻¹) *
      ((Real.sqrt (MeasureProb φ Finset.univ) : ℂ)⁻¹) =
      ((MeasureProb φ Finset.univ : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hφ.le]
  ext i j
  simp only [outerProduct_apply, PostMeasure, collapse_apply, Finset.mem_univ, if_true,
    map_mul, map_inv₀, Complex.conj_ofReal, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = (((Real.sqrt (MeasureProb φ Finset.univ) : ℂ)⁻¹) *
      ((Real.sqrt (MeasureProb φ Finset.univ) : ℂ)⁻¹)) *
        (φ i * (starRingEnd ℂ) (φ j)) := by ring
    _ = _ := by rw [hsq]

/-- For an idempotent effect with positive branch probability, the conditional instrument state
is the outer product of the normalized projected vector [Itakura2005]. -/
theorem povm_projective_pure_conditional {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D)) (o : O)
    (hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat)
    (hprob : 0 < instrumentProb (Instrument.ofPOVM Λ) (outerProduct ψ) o) :
    (Instrument.ofPOVM Λ).conditionalState (outerProduct ψ) o hprob =
      outerProduct (PostMeasure ((Λ.mats o).mat *ᵥ ψ) Finset.univ) := by
  have hm := povm_projective_pure_mass Λ ψ o hproj
  rw [Instrument.conditionalState, povm_projective_pure_branch Λ ψ o hproj,
    outerProduct_postMeasure_univ _ (by simpa only [← hm] using hprob), hm]

/-- A positive-probability binary projective outcome has a vector conditional state whose outer
product equals the conditional POVM instrument state. -/
theorem binary_projective_conditional {D : ℕ} (P : HermitianMat (Fin D) ℂ)
    (hP : P.mat * P.mat = P.mat) (ψ : QState (Fin D)) (o : Bool)
    (hp : 0 < instrumentProb (Instrument.ofPOVM (binaryProjectivePOVM P hP))
      (outerProduct ψ) o) :
    ∃ φ, ProjectiveConditionalState P.mat o ψ = some φ ∧
      (Instrument.ofPOVM (binaryProjectivePOVM P hP)).conditionalState
        (outerProduct ψ) o hp = outerProduct φ := by
  have hm := povm_projective_pure_mass (binaryProjectivePOVM P hP) ψ o
    (binaryProjectivePOVM_projection P hP o)
  have hb : ((binaryProjectivePOVM P hP).mats o).mat *ᵥ ψ =
      ProjectiveBranch P.mat o ψ := by
    cases o <;> simp [binaryProjectivePOVM, ProjectiveBranch, ApplyGate]
  refine ⟨PostMeasure (ProjectiveBranch P.mat o ψ) Finset.univ, ?_, ?_⟩
  · unfold ProjectiveConditionalState ConditionalState
    rw [if_pos (by simpa only [← hb, ← hm] using hp)]
  · simpa only [hb] using povm_projective_pure_conditional
      (binaryProjectivePOVM P hP) ψ o (binaryProjectivePOVM_projection P hP o) hp

/-- Conjugating a vector's outer product by `M` gives the outer product of `M *ᵥ ψ`. -/
theorem conjugate_outerProduct {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix J I ℂ) (ψ : QState I) :
    M * outerProduct ψ * Mᴴ = outerProduct (M *ᵥ ψ) := by
  change M * Matrix.vecMulVec ψ (fun i => star (ψ i)) * M.conjTranspose =
    Matrix.vecMulVec (M *ᵥ ψ) (fun i => star ((M *ᵥ ψ) i))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  funext j
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_comm]

/-- Extending a POVM branch by a reference identity gives conjugation by the square root of its
effect tensored with that identity. -/
theorem povm_reference_branch {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (o : O)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ =
      TensorGate (Λ.mats o ^ (1 / 2 : ℝ)).mat (1 : Operator R) * ρ *
        (TensorGate (Λ.mats o ^ (1 / 2 : ℝ)).mat (1 : Operator R))ᴴ := by
  exact tensorLeft_conjBranch _ ρ

/-- For an idempotent effect, its reference-extended branch on a pure input is the outer product
of the vector projected on the measured subsystem. -/
theorem povm_projective_reference_pure_branch
    {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D × Fin R)) (o : O)
    (hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat) :
    tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ) =
      outerProduct (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ) := by
  rw [povm_reference_branch, hermitian_projection_half _ hproj, conjugate_outerProduct]

/-- For an idempotent effect, the real trace mass of the reference-extended pure branch is the
total squared norm of the projected vector. -/
theorem povm_projective_reference_mass
    {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D × Fin R)) (o : O)
    (hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat) :
    (Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ))).re =
      MeasureProb (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ) Finset.univ := by
  rw [povm_projective_reference_pure_branch Λ ψ o hproj, trace_outerProduct]
  rfl

/-- For an idempotent effect with positive projected mass, normalizing the reference-extended
pure branch gives the outer product of the normalized projected vector. -/
theorem povm_projective_reference_conditional
    {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D × Fin R)) (o : O)
    (hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat)
    (hprob : 0 < MeasureProb
      (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ) Finset.univ) :
    (((Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o)
        (outerProduct ψ))).re : ℂ)⁻¹) •
        tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ) =
      outerProduct (PostMeasure
        (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ) Finset.univ) := by
  rw [povm_projective_reference_mass Λ ψ o hproj,
    povm_projective_reference_pure_branch Λ ψ o hproj,
    outerProduct_postMeasure_univ _ hprob]

/-- A reference-extended POVM branch on a pure input is the outer product obtained by applying
the effect's square root on the measured subsystem. -/
theorem povm_reference_pure_branch {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D × Fin R)) (o : O) :
    tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ) =
      outerProduct (TensorGate (Λ.mats o ^ (1/2 : ℝ)).mat (1 : Operator R) *ᵥ ψ) := by
  rw [povm_reference_branch, conjugate_outerProduct]

/-- The real trace of a reference-extended pure POVM branch is the expectation of the effect
tensored with the reference identity [Itakura2005]. -/
theorem povm_reference_pure_probability {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D × Fin R)) (o : O) :
    (Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ))).re =
      (Qatlib.Foundations.PureStateMath.Inner ψ (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ)).re := by
  have hm :
      (TensorGate (Λ.mats o ^ (1/2 : ℝ)).mat (1 : Operator R))ᴴ *
        TensorGate (Λ.mats o ^ (1/2 : ℝ)).mat (1 : Operator R) =
          TensorGate (Λ.mats o).mat (1 : Operator R) := by
    rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul,
      HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg o), Matrix.one_mul]
  rw [povm_reference_branch, Matrix.trace_mul_cycle, hm, trace_mul_outerProduct]

/-- The real trace masses of all reference-extended POVM branches sum to one on a normalized
pure input. -/
theorem povm_reference_total_pure {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D × Fin R)) (hψ : Normalized ψ) :
    (∑ o, (Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ))).re) = 1 := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, Instrument.tensorLeft_total]
  simpa only [trace_outerProduct, Complex.ofReal_re] using! hψ

/-- A reference-extended POVM branch on a positive semidefinite input is zero whenever its real
trace mass is zero. -/
theorem povm_reference_zero_mass {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : ρ.PosSemidef) (o : O)
    (hz : (Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ)).re = 0) :
    tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ = 0 := by
  have hp := tensorLeft_posSemidef ((Instrument.ofPOVM Λ).cp o) hρ
  apply (Matrix.PosSemidef.trace_eq_zero_iff hp).mp
  apply Complex.ext
  · exact hz
  · exact (RCLike.nonneg_iff.mp hp.trace_nonneg).2

/-- A zero POVM effect gives the zero reference-extended branch on every input operator. -/
theorem povm_reference_zero_effect {O : Type*} [Fintype O] [DecidableEq O] {D R : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (o : O)
    (ho : Λ.mats o = 0) : tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ = 0 := by
  rw [Instrument.ofPOVM_zero_effect_map Λ ho]
  ext i j
  simp [tensorLeft]

/-- Collect the pure-state Born rules, normalization, zero-branch laws, conditional projective
states, and reference-system positivity and trace laws for POVM instruments. The contract
also identifies binary projective conditional vectors and reference-extended projective pure
branches. -/
theorem part4_clause1 :
  (∀ (O : Type u) [Fintype O] [DecidableEq O] (D : ℕ) (Λ : POVM O (Fin D)),
    (∀ (ψ : QState (Fin D)) (o : O),
      instrumentProb (Instrument.ofPOVM Λ) (outerProduct ψ) o =
        (Qatlib.Foundations.PureStateMath.Inner ψ ((Λ.mats o).mat *ᵥ ψ)).re) ∧
    (∀ (ψ : QState (Fin D)) (hψ : Normalized ψ),
      (∑ o, instrumentPMF (Instrument.ofPOVM Λ) (isDensityOperator_outerProduct hψ) o) = 1) ∧
    (∀ (ψ : QState (Fin D)) (o : O),
      instrumentProb (Instrument.ofPOVM Λ) (outerProduct ψ) o = 0 →
        (Instrument.ofPOVM Λ).branch o (outerProduct ψ) = 0) ∧
    (∀ o : O, Λ.mats o = 0 → (Instrument.ofPOVM Λ).branch o = 0) ∧
    (∀ (ψ : QState (Fin D)) (o : O)
      (_hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat)
      (hp : 0 < instrumentProb (Instrument.ofPOVM Λ) (outerProduct ψ) o),
      (Instrument.ofPOVM Λ).conditionalState (outerProduct ψ) o hp =
        outerProduct (PostMeasure ((Λ.mats o).mat *ᵥ ψ) Finset.univ)) ∧
    (∀ (R : ℕ) (ψ : QState (Fin D × Fin R)) (o : O),
      tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ) =
        outerProduct (TensorGate (Λ.mats o ^ (1/2 : ℝ)).mat (1 : Operator R) *ᵥ ψ) ∧
      (Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ))).re =
        (Qatlib.Foundations.PureStateMath.Inner ψ (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ)).re) ∧
    (∀ (R : ℕ) (ψ : QState (Fin D × Fin R)), Normalized ψ →
      (∑ o, (Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ))).re) = 1) ∧
    (∀ (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (o : O),
      ρ.PosSemidef →
      (tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ).PosSemidef ∧
      (Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ)).re ≤ (Matrix.trace ρ).re ∧
      ((Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ)).re = 0 →
        tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ = 0)) ∧
    (∀ (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      Matrix.trace (∑ o, tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ) = Matrix.trace ρ) ∧
    (∀ (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (o : O),
      Λ.mats o = 0 → tensorLeft ((Instrument.ofPOVM Λ).branch o) ρ = 0)) ∧
  (∀ (D : ℕ) (P : HermitianMat (Fin D) ℂ) (hP : P.mat * P.mat = P.mat)
    (ψ : QState (Fin D)) (o : Bool)
    (hp : 0 < instrumentProb (Instrument.ofPOVM (binaryProjectivePOVM P hP)) (outerProduct ψ) o),
    ∃ φ, ProjectiveConditionalState P.mat o ψ = some φ ∧
      (Instrument.ofPOVM (binaryProjectivePOVM P hP)).conditionalState
        (outerProduct ψ) o hp = outerProduct φ) ∧
  (∀ (O : Type u) [Fintype O] [DecidableEq O] (D R : ℕ)
    (Λ : POVM O (Fin D)) (ψ : QState (Fin D × Fin R)) (o : O)
    (_hproj : (Λ.mats o).mat * (Λ.mats o).mat = (Λ.mats o).mat),
    tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ) =
      outerProduct (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ) ∧
    ∀ _hp : 0 < MeasureProb (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ) Finset.univ,
      (((Matrix.trace (tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ))).re : ℂ)⁻¹) •
        tensorLeft ((Instrument.ofPOVM Λ).branch o) (outerProduct ψ) =
      outerProduct (PostMeasure (TensorGate (Λ.mats o).mat (1 : Operator R) *ᵥ ψ) Finset.univ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro O _ _ D Λ
    refine ⟨povm_pure_probability Λ, povm_pure_pmf_total Λ, povm_pure_zero_branch Λ,
      (fun o ho => Instrument.ofPOVM_zero_effect_map Λ ho),
      povm_projective_pure_conditional Λ, ?_, ?_, ?_, ?_, ?_⟩
    · intro R ψ o
      exact ⟨povm_reference_pure_branch Λ ψ o, povm_reference_pure_probability Λ ψ o⟩
    · intro R ψ hψ
      exact povm_reference_total_pure Λ ψ hψ
    · intro R ρ o hρ
      exact ⟨tensorLeft_posSemidef ((Instrument.ofPOVM Λ).cp o) hρ,
        Instrument.tensorLeft_tni (Instrument.ofPOVM Λ) hρ o,
        povm_reference_zero_mass Λ ρ hρ o⟩
    · intro R ρ
      exact Instrument.tensorLeft_total (Instrument.ofPOVM Λ) ρ
    · intro R ρ o ho
      exact povm_reference_zero_effect Λ ρ o ho
  · intro D P hP ψ o hp
    exact binary_projective_conditional P hP ψ o hp
  · intro O _ _ D R Λ ψ o hproj
    exact ⟨povm_projective_reference_pure_branch Λ ψ o hproj,
      povm_projective_reference_conditional Λ ψ o hproj⟩

end Qatlib.Concepts.InstrumentCore.PovmBridge
