/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpoofedXEB24.MainResults.PauliTrace
import Qatlib.Papers.SpoofedXEB24.MainResults.CycleTrace
import Mathlib.Logic.Equiv.Fin.Rotate

open Matrix
set_option autoImplicit false

/-!
# Lemma 1 of `SpoofedXEB24`: verified instances

The paper's Lemma 1 (Tanggara–Gu–Bharti, arXiv:2405.00789v2, lines 1101–1122) asserts that
`Tr (W_π (Q_1 ⊗ ⋯ ⊗ Q_k))` vanishes unless the Pauli product along every cycle of `π` is the
identity, and equals `4^{c_π}` if all of them are.

The complete cyclic-partition factorisation for arbitrary `π` is not yet formalised.  This
module records the instances that are proved from `PauliTrace` and `CycleTrace`:

* `lemma_one_transposition_pauli`: the two-block transposition, with the exact phase-corrected
  trace value;
* `lemma_one_transposition_pauli_eq_four`: the literal `4^{c_π}` value when the two Paulis
  multiply to the identity matrix.

Both are genuine instances of the lemma's conclusion, not weakenings of it: the general
statement remains open.
-/

namespace Qatlib.Papers.SpoofedXEB24.MainResults

/-- **Lemma 1 for a transposition of two two-qubit Paulis, exact value.**  If the ordered
product of the two Paulis is the nonzero scalar multiple `c • P(lbl)`, then the permutation
trace is `4 c` when `lbl` is the two-qubit identity and `0` otherwise. -/
theorem lemma_one_transposition_pauli (p q : Pauli2) (c : ℂ) (lbl : Pauli2)
    (h : Pauli2.toMat p * Pauli2.toMat q = c • Pauli2.toMat lbl) :
    ((permOp (d := Fin 2 × Fin 2) (Equiv.swap (0 : Fin 2) 1) *
        tensorAll ![Pauli2.toMat p, Pauli2.toMat q] :
      Matrix (Fin 2 → Fin 2 × Fin 2) (Fin 2 → Fin 2 × Fin 2) ℂ)).trace
      = if lbl = (Pauli1.I, Pauli1.I) then 4 * c else 0 := by
  have h2 : (List.map Pauli2.toMat [p, q]).prod = Pauli2.toMat p * Pauli2.toMat q := by simp
  rw [trace_permOp_swap_mul_tensorAll, ← h2]
  exact trace_prod_toMat [p, q] c lbl (by simpa using h)

/-- **Lemma 1 for a transposition of two two-qubit Paulis whose product is the identity.**
The permutation trace is `4`, the `c_π = 1` value of the paper's lemma. -/
theorem lemma_one_transposition_pauli_eq_four (p q : Pauli2)
    (h : Pauli2.toMat p * Pauli2.toMat q = 1) :
    ((permOp (d := Fin 2 × Fin 2) (Equiv.swap (0 : Fin 2) 1) *
        tensorAll ![Pauli2.toMat p, Pauli2.toMat q] :
      Matrix (Fin 2 → Fin 2 × Fin 2) (Fin 2 → Fin 2 × Fin 2) ℂ)).trace = 4 := by
  have h' : Pauli2.toMat p * Pauli2.toMat q = (1 : ℂ) • Pauli2.toMat (Pauli1.I, Pauli1.I) := by
    rw [h, Pauli2.toMat_identity]
    simp
  have hmain := lemma_one_transposition_pauli p q (1 : ℂ) (Pauli1.I, Pauli1.I) h'
  simpa using hmain

end Qatlib.Papers.SpoofedXEB24.MainResults
