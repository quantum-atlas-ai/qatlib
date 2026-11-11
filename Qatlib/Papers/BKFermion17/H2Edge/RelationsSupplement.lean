/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.H2Edge.Defs
import Qatlib.Papers.BKFermion17.H2Edge.Relations

/-!
# BKFermion17 — qubit edge-operator relations (arXiv:1712.00446v3, Eq. (22), p. 5)

Claim `c002`, qubit half.  Eq. (24)–(25), p. 6, replace the fermionic edge
operators by qubit Pauli operators `B̃_i`, `Ã_ij` acting on one qubit per edge.
Eq. (26)–(31), pp. 6–7, show that these satisfy the *same* relations as
`B_i, A_ij` (Eq. (22)) with a single exception: the product around a closed loop
is not the identity (`i^p ∏A ≠ 1`); imposing the loop stabilizers defines the
physical subspace, on which the representation is faithful.

Here we formalize, for the hydrogen-molecule instance of Eq. (40) (Fig. 3,
p. 9; `h2B`, `h2A` in `SourceModel`), the *word/phase-level* statement:

* `B̃_i² = 1`, `B̃_i B̃_j = B̃_j B̃_i`;
* `Ã_ij² = 1`, `Ã_ji = -Ã_ij` on edges;
* `Ã_ij B̃_k = (-1)^{δ_ik+δ_jk} B̃_k Ã_ij`;
* `Ã_ij Ã_kl = (-1)^{δ_ik+δ_il+δ_jk+δ_jl} Ã_kl Ã_ij`;
* the loop exception: the unique independent loop `C_L = Ã₁₂Ã₂₃Ã₃₄Ã₄₁` of
  Eq. (45)–(46) equals `i² · X⊗Y⊗Y⊗X ≠ 1`, and is an involution.

The correspondence with actual operators is `i^phase • pauliWordOp` (see
`PauliElem`); all assertions are graded by that phase, so they lift to matrix
identities through `op_mul`.  The "restricting to the subspace restores
completeness" half of the claim is the stabilizer-code construction of
Eq. (27)/(46); it is recorded here only through the loop stabilizer `C_L`
being an nonidentity involution (`h2Loop_sq`), not formalized as a codespace
identity at this layer.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BKFermion17.H2Edge

open Qatlib.Papers.BKFermion17.H2Edge

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Papers.BKFermion17.H2Edge

/-! ## §1 Decidability of word/phase equality -/

/-! The phase-level sign flip has an exact operator semantics.  Keeping this
bridge next to the oriented edge relations lets matrix consumers transport
the conditional minus signs from Eq. (22), rather than re-proving the phase
calculation at each use site. -/

/-- The phase-shifted Pauli element is the negative of the original operator. -/
theorem op_pauliNeg {n : ℕ} (p : PauliElem n) : op (pauliNeg p) = -op p := by
  unfold pauliNeg op
  rw [I_pow_val_add]
  change (Complex.I ^ p.phase.val * Complex.I ^ (2 : ZMod 4).val) •
      pauliWordOp n p.word = _
  rw [show (2 : ZMod 4).val = 2 by rfl, I_pow_two]
  rw [← neg_smul]
  congr 1
  ring

/-! ## §2 The relations of Eq. (22) at the qubit level (Eqs. (24)-(25)) -/

/-! ## §3 The loop exception (Eqs. (26), (28)-(31), (45)-(46)) -/

/-- The loop stabilizer's Pauli relation lifts to an actual operator
involution through the Frozen `op_mul` bridge. -/
theorem h2Loop_op_sq : op h2Loop * op h2Loop = 1 := by
  rw [← op_mul, h2Loop_sq, op_one]

/-- Every concrete H2 edge/vertex relation has the corresponding operator
product bridge, so the phase-level model can be consumed by matrix semantics. -/
theorem h2A_op_mul_h2B (i j k : Fin 4) (_h : h2Edge i j) :
    op (PauliElem.mul (h2A i j) (h2B k)) = op (h2A i j) * op (h2B k) :=
  op_mul _ _

/-- The full edge-edge relation transports to actual operator products,
including the conditional sign from endpoint coincidence. -/
theorem h2A_op_mul_h2A (i j k l : Fin 4) (hij : h2Edge i j) (hkl : h2Edge k l) :
    op (h2A i j) * op (h2A k l) =
      if edgeCoincidence i j k l % 2 = 1
      then -(op (h2A k l) * op (h2A i j))
      else op (h2A k l) * op (h2A i j) := by
  rw [← op_mul, ← op_mul, h2A_mul_h2A i j k l hij hkl]
  split <;> simp [op_pauliNeg]

end Qatlib.Papers.BKFermion17.H2Edge
