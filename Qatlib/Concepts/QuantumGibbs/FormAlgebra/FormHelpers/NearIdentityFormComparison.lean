/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.FormHelpers.BlockFormPerturbation
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.NearIdentityFormComparison
open BlockFormPerturbation
open scoped BigOperators
variable {N d : ℕ}

/-- The quadratic form of the identity is the complex embedding of the sum of squared coordinate
norms. -/
private theorem qForm_one (v : Fin N × Fin d → ℂ) :
    qForm (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) v =
      ∑ i, ((‖v i‖^2 : ℝ) : ℂ) := by
  rw [← Qatlib.Foundations.PureStateMath.inner_self]
  simp [qForm, Matrix.one_apply, mul_ite, ite_mul, Qatlib.Foundations.PureStateMath.Inner,
      dotProduct]

/-- The identity matrix is block diagonal. -/
private theorem identity_block : BlockDiagonal
    (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) := by
  intro p q hp a b
  have h : (p,a) ≠ (q,b) := fun he => hp (congrArg Prod.fst he)
  simp [h]

/-- The identity matrix has a real quadratic form. -/
private theorem identity_real : RealForm
    (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) := by
  intro v
  rw [qForm_one]
  simp only [Complex.im_sum, Complex.ofReal_im, Finset.sum_const_zero]

/-- If both identity perturbations have the stated small entrywise bound, the real part of their
quadratic-form quotient is at most three halves whenever its denominator is nonzero. -/
theorem quotient_bound (EG EM : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ)
    (eps : ℝ) (heps : 0 ≤ eps) (hEG : EntrywiseBound EG eps)
    (hEM : EntrywiseBound EM eps) (hbudget : (N : ℝ)*(d : ℝ)*eps ≤ 1/6)
    (v : Fin N × Fin d → ℂ) (hv : qForm (1+EM) v ≠ 0) :
    (qForm (1+EG) v / qForm (1+EM) v).re ≤ 3/2 := by
  have hpos : PositiveForm (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) := by
    intro w
    rw [qForm_one]
    simp only [Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcoe : Coercive (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) 1 := by
    intro w
    rw [qForm_one]
    simp only [Complex.re_sum, Complex.ofReal_re, one_mul]
    exact le_refl _
  have hsec : SectorBound (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) 1 2 1 := by
    intro w
    norm_num
  have h := BlockFormPerturbation.quotient_bound (Λ := 2) (m := 1) (μ := 1)
    (ε := eps) (G := 1+EG) (M := 1+EM) (G_blk := 1) (M_blk := 1)
    rfl rfl identity_block identity_block identity_real identity_real hpos
    hEG hEM hcoe hsec (by norm_num) (by norm_num) heps (by norm_num) (by norm_num)
    (by norm_num; exact hbudget) v hv
  norm_num at h
  exact h

end Qatlib.Concepts.QuantumGibbs.FormAlgebra.NearIdentityFormComparison
