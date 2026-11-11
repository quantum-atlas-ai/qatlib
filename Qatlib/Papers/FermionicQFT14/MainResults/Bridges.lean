/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrder

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults: paper-layer bridges to reusable Frozen theorems

Claims `c001` and `c002` bind four reusable library components.  Three of them
are fully proved in the Frozen library and only need a paper-layer reference at
the statement the paper uses:

* `QuantumAlgorithm.Concepts.FermionAlgebra.CarJordanWigner.g1`
  (Frozen module `QuantumAlgorithm.Concepts.FermionAlgebra.CarJordanWigner.Fermion.Fermion`,
  module docstring "g1（G6）拼装"): the complete fermionic CAR contract — the
  anticommutation relations, the adjoint identity `c_i† = (c_i)ᴴ`, the number
  operator, parity, the exact Jordan–Wigner isomorphism and the vacuum rule.
  This is the encoding layer that the paper's §3.1 (Bravyi–Kitaev / Jordan–Wigner
  representation of the lattice fermions) relies on.
* `QuantumAlgorithm.Concepts.TrotterFormula.SuzukiFourth.suzuki_fourth_order_local_error`
  (Frozen module `QuantumAlgorithm.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrder.SuzukiFourthOrder`):
  a fifth-order local error bound `‖W₄(t) - e^{-i(A+B)t}‖ ≤ 100 (‖A‖+‖B‖)⁵ |t|⁵`
  for the symmetric fifteen-exponential fourth-order Suzuki word.  This is the
  Suzuki–Trotter subroutine used in steps 2, 3 and 5 of the algorithm.

Each bridge below restates the paper-relevant part verbatim and cites the
Frozen fully-qualified name.  All bridge theorems are proved by projection from
the Frozen contract; there is no `sorry`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.FermionicQFT14.MainResults

/-! ## 1. Fermionic CAR layer (Bravyi–Kitaev / Jordan–Wigner encoding) -/

/-- Paper-layer reference to
`QuantumAlgorithm.Concepts.FermionAlgebra.CarJordanWigner.g1` (a): the canonical
anticommutation relation `{cᵢ, cⱼ†} = δᵢⱼ` of the lattice fermions, which is
what licenses the Jordan–Wigner encoding of the Gross–Neveu lattice fields
(arXiv:1404.7115v1, §3.1). -/
theorem fermion_anticommutation (n : ℕ) (i j : Fin n) :
    annihilation i * creation j + creation j * annihilation i
      = (if i = j then (1 : Matrix (Reg n) (Reg n) ℂ) else 0) :=
  ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).1 i j).1

/-- Paper-layer reference to `g1` (b): the creation operator is the adjoint of
the annihilation operator. -/
theorem fermion_creation_adjoint (n : ℕ) (i : Fin n) :
    creation i = (annihilation i)ᴴ :=
  ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2).1 i

/-- Paper-layer reference to `g1` (c): the number operator factorizes as
`nᵢ = cᵢ† cᵢ`. -/
theorem fermion_numberOp_eq (n : ℕ) (i : Fin n) :
    numberOp i = creation i * annihilation i :=
  (((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2).1 i).1

/-- Paper-layer reference to `g1` (e): the exact Jordan–Wigner isomorphism
`cᵢ = σ⁻ᵢ` (with the `Z` prefix string), preserving the adjoint; this is the
Bravyi–Kitaev/Jordan–Wigner map used to place the fermions on the qubit
register. -/
theorem fermion_jordanWigner (n : ℕ) (i : Fin n) :
    annihilation i = jwPauliWord i ∧ creation i = (jwPauliWord i)ᴴ :=
  (((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.2.2).1) i

/-- Paper-layer reference to `g1` (f): the vacuum rule
`cᵢ |0…0⟩ = 0`, used for step 1 of the algorithm (the free-theory ground state
is the product state on the qubit register). -/
theorem fermion_vacuum (n : ℕ) (i : Fin n) :
    annihilation i *ᵥ Ket (ZeroStr n) = 0 :=
  ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.2.2).2 i

/-! ## 2. Suzuki–Trotter local error -/

/-- Paper-layer reference to
`QuantumAlgorithm.Concepts.TrotterFormula.SuzukiFourth.suzuki_fourth_order_local_error`:
the fourth-order Suzuki–Trotter word approximates the exact evolution with local
error `100 (‖A‖ + ‖B‖)⁵ |t|⁵`.  This is the subroutine behind the adiabatic
simulations of steps 2, 3 and the time evolution of step 5 (arXiv:1404.7115v1,
§3.3 and Eqs. (15)–(18)). -/
theorem suzukiFourthOrder_localError {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖(suzuki4Word A B t).prod - hamiltonianEvolution (A + B) t‖ ≤
      100 * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 :=
  Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki_fourth_order_local_error
    I A B t hA hB

end Qatlib.Papers.FermionicQFT14.MainResults
