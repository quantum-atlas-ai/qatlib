/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

/-!
# Explicit circuits for the parity oracle

This module defines the binary parity character `bvCharBit`, gates acting separately on the main
and target registers, and two explicit oracle circuits. The Hadamard–query–Hadamard circuit
`bvOneCallCircuit` and the query–Z–query word `bvTwoCallWord` provide syntax for the
parity-oracle analysis of [BernsteinVazirani1997].

## Main statements

* `bvCharBit`: the parity of coordinatewise conjunction with the secret.
* `bvOneCallCircuit`: applies Hadamards to the main register before and after one query.
* `bvTwoCallWord`: places target Z between two oracle queries.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib

namespace Qatlib.Concepts.UniformBqp.BvParityBound

/-- The Boolean parity of the number of coordinates where both `k` and `x` are true. -/
def bvCharBit {n : ℕ} (k x : Reg n) : Bool :=
  decide ((Finset.univ.filter fun i => k i && x i).card % 2 = 1)

/-- Extends the main-register matrix `U` by the identity on the Boolean target register. -/
noncomputable def bvMainGate (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg n × Bool) (Reg n × Bool) ℂ :=
  TensorGate U (1 : Matrix Bool Bool ℂ)

/-- Extends the target-qubit matrix `V` by the identity on the main register. -/
noncomputable def bvTgtGate (n : ℕ) (V : Matrix Bool Bool ℂ) :
    Matrix (Reg n × Bool) (Reg n × Bool) ℂ :=
  TensorGate (1 : Matrix (Reg n) (Reg n) ℂ) V

/-- The circuit consisting of an oracle query, target Pauli Z, and a second oracle query. -/
noncomputable def bvTwoCallWord (n : ℕ) : Circuit (Reg n × Bool) :=
  [Step.query, Step.gate (bvTgtGate n PauliZ), Step.query]

/-- The circuit applying `HadamardN n` to the main register, making one oracle query, and
applying `HadamardN n` again. -/
noncomputable def bvOneCallCircuit (n : ℕ) : Circuit (Reg n × Bool) :=
  [Step.gate (bvMainGate n (HadamardN n)), Step.query,
    Step.gate (bvMainGate n (HadamardN n))]
end Qatlib.Concepts.UniformBqp.BvParityBound
