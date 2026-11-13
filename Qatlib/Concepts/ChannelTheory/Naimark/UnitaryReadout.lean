/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Measurements.POVM

/-!
# Computational basis readout after unitary evolution

This module defines the computational basis measurement `basisPOVM` and connects its
probabilities on `MState` inputs to matrix entries. For a basis state evolved by
`CPTPMap.ofUnitary`, the resulting probabilities are squared amplitude norms, as in the Born
rule [NielsenChuang2010].

## Main statements

* `unitary_matrix`: unitary evolution acts by conjugation on the density matrix.
* `basis_probability`: a basis outcome has probability equal to the real part of the
  corresponding diagonal entry.
* `unitary_basis_event`: an event probability is the sum of squared evolved amplitudes.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout

open Matrix
open scoped BigOperators ComplexOrder RealInnerProductSpace

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The density matrix of a state evolved by `CPTPMap.ofUnitary U` is `U * ρ.m * Uᴴ`. -/
theorem unitary_matrix (U : Matrix.unitaryGroup I ℂ) (ρ : MState I) :
    (CPTPMap.ofUnitary U ρ).m = (U : Matrix I I ℂ) * ρ.m * (U : Matrix I I ℂ)ᴴ := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  rfl

/-- Unitary evolution of a pure basis state produces the outer product of its evolved amplitude
vector with its conjugate. -/
theorem unitary_basis_matrix (U : Matrix.unitaryGroup I ℂ) (seed : I) :
    (CPTPMap.ofUnitary U (MState.pure (_root_.Ket.basis seed))).m =
      fun i j => ((U : Matrix I I ℂ) *ᵥ (_root_.Ket.basis seed : I → ℂ)) i *
        star (((U : Matrix I I ℂ) *ᵥ (_root_.Ket.basis seed : I → ℂ)) j) := by
  rw [unitary_matrix]
  ext i j
  simp [MState.pure_apply, _root_.Ket.basis, _root_.Ket.coe_fun_eq,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    mul_ite, ite_mul]

/-- The computational basis POVM, whose effects are the pure basis state projectors. -/
def basisPOVM (I : Type) [Fintype I] [DecidableEq I] : _root_.POVM I I where
  mats i := (MState.pure (_root_.Ket.basis i)).M
  nonneg i := (MState.pure (_root_.Ket.basis i)).nonneg
  normalized := by
    apply HermitianMat.ext
    simp only [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
    ext i j
    simp only [Matrix.sum_apply]
    change (∑ x : I, (MState.pure (_root_.Ket.basis x)).m i j) = (1 : Matrix I I ℂ) i j
    simp [MState.pure_apply, _root_.Ket.basis, _root_.Ket.coe_fun_eq,
      Matrix.one_apply, eq_comm]

/-- The probability of a computational basis outcome is the real part of the corresponding
diagonal entry of the density matrix. -/
theorem basis_probability (ρ : MState I) (i : I) :
    (((basisPOVM I).measure ρ) i : ℝ) = (ρ.m i i).re := by
  change inner ℝ (MState.pure (_root_.Ket.basis i)).M ρ.M = _
  rw [HermitianMat.inner_eq_re_trace]
  change (Matrix.trace ((MState.pure (_root_.Ket.basis i)).m * ρ.m)).re = _
  simp [Matrix.trace, Matrix.mul_apply, MState.pure_apply,
    _root_.Ket.basis, _root_.Ket.coe_fun_eq]

/-- Measuring a unitarily evolved basis state in the computational basis gives the squared norm
of the corresponding evolved amplitude. -/
theorem unitary_basis_probability (U : Matrix.unitaryGroup I ℂ) (seed i : I) :
    (((basisPOVM I).measure
      (CPTPMap.ofUnitary U (MState.pure (_root_.Ket.basis seed)))) i : ℝ) =
      ‖((U : Matrix I I ℂ) *ᵥ (_root_.Ket.basis seed : I → ℂ)) i‖ ^ 2 := by
  rw [basis_probability, unitary_basis_matrix]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The probability of a finite set of basis outcomes after unitary evolution is the sum of
their squared amplitude norms. -/
theorem unitary_basis_event (U : Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I) :
    (∑ i ∈ S, (((basisPOVM I).measure
      (CPTPMap.ofUnitary U (MState.pure (_root_.Ket.basis seed)))) i : ℝ)) =
      ∑ i ∈ S, ‖((U : Matrix I I ℂ) *ᵥ (_root_.Ket.basis seed : I → ℂ)) i‖ ^ 2 := by
  simp only [unitary_basis_probability]

end Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout
