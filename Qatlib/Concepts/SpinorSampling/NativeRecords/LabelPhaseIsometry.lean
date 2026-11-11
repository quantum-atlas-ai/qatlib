/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Label Phase Isometry

Label Phase Isometry constructions and identities for Spinor Sampling.
-/

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase
noncomputable section
open scoped BigOperators Matrix

variable {I A : Type*} [Fintype I] [Nonempty I] [Fintype A] [DecidableEq A]

/-- Construction for orbit Coefficient in the label phase isometry model. -/
def orbitCoefficient : ℂ := ((1/Real.sqrt (Fintype.card I : ℝ) : ℝ) : ℂ)

/-- Construction for controlled Embedding in the label phase isometry model. -/
def controlledEmbedding (U : I → Matrix A A ℂ) : Matrix (I × A) A ℂ :=
  fun z a => orbitCoefficient (I := I)*U z.1 z.2 a

omit [Fintype A] [DecidableEq A] in
/-- Complete original `orbit_coefficient_normalization` guarantee for `LabelPhaseIsometry`; all source hypotheses and output obligations are retained. -/
theorem orbit_coefficient_normalization :
    (Fintype.card I : ℂ)*(star (orbitCoefficient (I := I))*orbitCoefficient (I := I))=1 := by
  have hN : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : (Fintype.card I : ℝ)*
      ((1/Real.sqrt (Fintype.card I : ℝ))*(1/Real.sqrt (Fintype.card I : ℝ)))=1 := by
    calc
      _ = (Fintype.card I : ℝ)/(Real.sqrt (Fintype.card I : ℝ))^2 := by ring
      _ = 1 := by rw [Real.sq_sqrt hN.le, div_self hN.ne']
  unfold orbitCoefficient
  simpa using (congrArg (fun x : ℝ => (x : ℂ)) hr)

/-- Complete original `controlled_embedding_isometry` guarantee for `LabelPhaseIsometry`; all source hypotheses and output obligations are retained. -/
theorem controlled_embedding_isometry (U : I → Matrix A A ℂ)
    (hU : ∀ i, (U i).conjTranspose*U i=1) :
    (controlledEmbedding U).conjTranspose*controlledEmbedding U=1 := by
  let c := orbitCoefficient (I := I)
  have hrow (i : I) (a b : A) :
      (∑ x : A, star (c*U i x a)*(c*U i x b))=
        (star c*c)*((U i).conjTranspose*U i) a b := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [Matrix.conjTranspose_apply, star_mul]
    ring
  ext a b
  change (∑ z : I × A, star (c*U z.1 z.2 a)*(c*U z.1 z.2 b))=(1 : Matrix A A ℂ) a b
  rw [Fintype.sum_prod_type]
  simp_rw [hrow, hU]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = ((Fintype.card I : ℂ)*(star c*c))*(1 : Matrix A A ℂ) a b := by ring
    _ = (1 : Matrix A A ℂ) a b := by rw [orbit_coefficient_normalization]; ring

omit [Nonempty I] in
/-- Complete original `permutation_isometry` guarantee for `LabelPhaseIsometry`; all source hypotheses and output obligations are retained. -/
theorem permutation_isometry (e : Equiv.Perm A) :
    (e.permMatrix ℂ).conjTranspose*e.permMatrix ℂ=1 := by
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- Complete original `controlled_permutation_isometry` guarantee for `LabelPhaseIsometry`; all source hypotheses and output obligations are retained. -/
theorem controlled_permutation_isometry (e : I → Equiv.Perm A) :
    (controlledEmbedding (fun i => (e i).permMatrix ℂ)).conjTranspose*
      controlledEmbedding (fun i => (e i).permMatrix ℂ)=1 :=
  controlled_embedding_isometry _ (fun i => permutation_isometry (e i))

omit [Nonempty I] [DecidableEq A] in
/-- Complete original `controlled_embedding_apply` guarantee for `LabelPhaseIsometry`; all source hypotheses and output obligations are retained. -/
theorem controlled_embedding_apply (U : I → Matrix A A ℂ) (v : A → ℂ) (i : I) (a : A) :
    ((controlledEmbedding U)*ᵥ v) (i,a)=orbitCoefficient (I := I)*((U i)*ᵥ v) a := by
  simp only [Matrix.mulVec, dotProduct, controlledEmbedding]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Complete original `controlled_embedding_trace` guarantee for `LabelPhaseIsometry`; all source hypotheses and output obligations are retained. -/
theorem controlled_embedding_trace (U : I → Matrix A A ℂ)
    (hU : ∀ i, (U i).conjTranspose*U i=1) (ρ : Matrix A A ℂ) :
    Matrix.trace (controlledEmbedding U*ρ*(controlledEmbedding U).conjTranspose)=Matrix.trace ρ := by
  rw [Matrix.trace_mul_cycle, controlled_embedding_isometry U hU, Matrix.one_mul]

end
end Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase

#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase.orbit_coefficient_normalization
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase.controlled_embedding_isometry
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase.controlled_permutation_isometry
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase.controlled_embedding_apply
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase.controlled_embedding_trace
