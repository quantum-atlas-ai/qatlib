/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsDefs
import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsConsumers

/-!
# Pauli matrix laws and Clifford conjugation

This module collects the definitions, matrix proofs, and circuit applications of the Pauli and
Clifford formalism. The interpretation `op` retains the fourth-root-of-unity phase of each Pauli
element, and `verifiedCliffordAction` includes the phase correction needed for CNOT conjugation,
in the binary framework of [DehaeneDeMoor2003].

The imported results establish multiplication, adjoints, unitarity, and symplectic commutation
for Pauli matrices. They extend conjugation to legal gate lists through `Uword_conj` and verify
the state and stabilizers produced by the standard Bell preparation circuit.

## Main statements

* `PauliCliffordLawsProofs.pauli_matrix_laws`: matrix interpretation of Pauli multiplication,
  adjoints, unitarity, and commutation.
* `PauliCliffordLawsProofs.legal_clifford_conjugacy`: conjugation laws for legal H, S, and CNOT
  gates, with explicit phase examples.
* `Uword_conj`: matrix conjugation agrees with the accumulated Pauli action of a legal circuit.
* `actual_word_and_bell_consumers`: circuit laws and explicit Bell and Hadamard state
  applications.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
