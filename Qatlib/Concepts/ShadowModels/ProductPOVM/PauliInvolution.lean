/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliOrbitPOVM

/-!
# Pauli involutions and traces

This module shows that the matrix of `pauliObservable` squares to the identity and that every
nonidentity Pauli word has trace zero. The tensor trace argument reduces the global statement to
the trace of a nonidentity single-qubit Pauli matrix. See [NielsenChuang2010] for background.

## Main statements

* `pauliObservable_square`: Pauli observables are involutions.
* `pauliObservable_trace_zero`: nonidentity Pauli words are traceless.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

/-- The matrix of a Pauli word observable squares to the identity. -/
theorem pauliObservable_square (n : ℕ) (w : PauliWord n) :
    (pauliObservable n w).mat*(pauliObservable n w).mat=1 := by
  have h := (pauliUnitary n w).property.1
  simpa only [pauliUnitary,Matrix.star_eq_conjTranspose,pauliWordOp_herm,pauliObservable] using! h

/-- A nonidentity single-qubit Pauli matrix has trace zero. -/
theorem one_pauli_trace_zero (p : Pauli1) (hp : p≠.I) : (P1 p).trace=0 := by
  cases p <;> simp_all [P1,Matrix.trace]

/-- A Pauli word observable has trace zero whenever its word is not identically the identity. -/
theorem pauliObservable_trace_zero (n : ℕ) (w : PauliWord n) (hw : w≠fun _ => .I) :
    (pauliObservable n w).trace=0 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hw
  have ht : (pauliWordOp n w).trace=0 := by
    rw [pauliWordOp_eq,productMatrix_trace]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (one_pauli_trace_zero (w i) hi)
  rw [HermitianMat.trace_eq_re_trace]
  change Complex.re (pauliWordOp n w).trace=0
  rw [ht]
  rfl

end Qatlib.Concepts.ShadowModels.ProductPOVM
