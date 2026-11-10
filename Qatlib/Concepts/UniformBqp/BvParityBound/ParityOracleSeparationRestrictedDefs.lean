/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib

namespace Qatlib.Concepts.UniformBqp.BvParityBound

def bvCharBit {n : ℕ} (k x : Reg n) : Bool :=
  decide ((Finset.univ.filter fun i => k i && x i).card % 2 = 1)

noncomputable def bvMainGate (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg n × Bool) (Reg n × Bool) ℂ :=
  TensorGate U (1 : Matrix Bool Bool ℂ)

noncomputable def bvTgtGate (n : ℕ) (V : Matrix Bool Bool ℂ) :
    Matrix (Reg n × Bool) (Reg n × Bool) ℂ :=
  TensorGate (1 : Matrix (Reg n) (Reg n) ℂ) V

noncomputable def bvTwoCallWord (n : ℕ) : Circuit (Reg n × Bool) :=
  [Step.query, Step.gate (bvTgtGate n PauliZ), Step.query]

noncomputable def bvOneCallCircuit (n : ℕ) : Circuit (Reg n × Bool) :=
  [Step.gate (bvMainGate n (HadamardN n)), Step.query,
    Step.gate (bvMainGate n (HadamardN n))]
end Qatlib.Concepts.UniformBqp.BvParityBound
