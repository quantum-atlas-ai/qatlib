/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliOrbitPOVM
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

theorem pauliObservable_square (n : ℕ) (w : PauliWord n) :
    (pauliObservable n w).mat*(pauliObservable n w).mat=1 := by
  have h := (pauliUnitary n w).property.1
  simpa only [pauliUnitary,Matrix.star_eq_conjTranspose,pauliWordOp_herm,pauliObservable] using! h

theorem one_pauli_trace_zero (p : Pauli1) (hp : p≠.I) : (P1 p).trace=0 := by
  cases p <;> simp_all [P1,Matrix.trace]

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
