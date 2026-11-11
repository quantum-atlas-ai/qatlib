/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.Entanglement.BellWitness.Product

/-!
# A Bell-state witness for separable states

This module defines `IsSeparableState` as a finite convex mixture of outer products of
normalized product vectors. It extends the Bell overlap bound from pure product vectors to
separable two-qubit states and proves trace normalization.

The theorem `bell_state_witness` combines the overlap bound with a trace-norm distance of at
least one from the Bell projector. For separable states and entanglement witnesses, see
[NielsenChuang2010].

## Main statements

* `IsSeparableState`: A bipartite matrix is separable when it is a finite convex combination of
  outer products of normalized product vectors.
* `separable_overlap_le`: The real trace overlap of the Bell projector with a separable
  two-qubit state is at most one half.
* `bell_state_witness`: Every separable two-qubit state has Bell-projector overlap at most one
  half and trace-norm distance at least one from the Bell projector.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.Entanglement.BellWitness
noncomputable section

/-- A bipartite matrix is separable when it is a finite convex combination of outer products of
normalized product vectors. -/
def IsSeparableState {D E : ℕ} (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (a : Fin n → QState (Fin D)) (b : Fin n → QState (Fin E)),
    (∀i,0≤p i) ∧ (∑i,p i=1) ∧ (∀i,Normalized (a i)) ∧ (∀i,Normalized (b i)) ∧
      ρ=∑i,(p i : ℂ) • outerProduct (TensorState (a i) (b i))

/-- The outer product of a normalized vector has trace one. -/
theorem pure_trace_one {I : Type*} [Fintype I] [DecidableEq I] (v : QState I)
    (hv : Normalized v) : (outerProduct v).trace = 1 := by
  have htr : (outerProduct v).trace = (∑ i, ‖v i‖^2 : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply, outerProduct_apply, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_sum]
  rw [htr,hv,Complex.ofReal_one]

/-- The real trace overlap of the Bell projector with a separable two-qubit state is at most one
half. -/
theorem separable_overlap_le (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : IsSeparableState ρ) : (outerProduct phi * ρ).trace.re ≤ 1/2 := by
  obtain ⟨n,w,a,b,hw,hs,ha,hb,rfl⟩ := hρ
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, projector_trace, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ ∑ i, w i * (1/2) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (product_overlap_le (a i) (b i) (ha i) (hb i)) (hw i))
    _ = 1/2 := by rw [← Finset.sum_mul,hs,one_mul]

/-- A separable two-qubit state has trace one. -/
theorem separable_trace_one (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : IsSeparableState ρ) : ρ.trace = 1 := by
  obtain ⟨n,w,a,b,_hw,hs,ha,hb,rfl⟩ := hρ
  simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    pure_trace_one _ (normalized_tensorState (ha _) (hb _)), mul_one]
  exact_mod_cast hs

/-- Every separable two-qubit state has Bell-projector overlap at most one half and trace-norm
distance at least one from the Bell projector. -/
theorem bell_state_witness (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : IsSeparableState ρ) :
    (outerProduct phi * ρ).trace.re ≤ 1/2 ∧
      1 ≤ Matrix.traceNorm (outerProduct phi - ρ) := by
  have ht : (outerProduct phi - ρ).trace = 0 := by
    rw [Matrix.trace_sub,pure_trace_one phi phi_normalized,separable_trace_one ρ hρ,sub_self]
  have hb := abs_quadratic_re_le_half_traceNorm (outerProduct phi - ρ) ht phi phi_normalized
  rw [← trace_outerProduct_mul_eq_quadratic, Matrix.mul_sub, Matrix.trace_sub,
    projector_trace, (normalized_iff_inner_self phi).mp phi_normalized] at hb
  norm_num at hb
  have h := separable_overlap_le ρ hρ
  exact ⟨h, by linarith [le_abs_self (1 - (outerProduct phi*ρ).trace.re)]⟩

end
end Qatlib.Foundations.Entanglement.BellWitness
