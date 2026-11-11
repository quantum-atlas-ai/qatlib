/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversal

/-!
# Circuit reversal laws and resource counts

Proves that `ReverseCircuit` reverses concatenation order and that reversing twice returns the
original circuit. `run_and_counts` combines the restoration identity for a Hermitian unitary
oracle with exact doubled gate and query counts.

These identities formalize elementary reversible-circuit manipulations in the quantum circuit
framework of [NielsenChuang2010].

## Main statements

* `reverse_append`: Circuit reversal reverses the order of concatenation.
* `reverse_involution`: Reversing a circuit twice returns the original circuit.
* `run_and_counts`: For a Hermitian unitary oracle and a unitary circuit, appending its reverse
  restores every input state and doubles both query and fixed-gate counts.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.CircuitReversal.ReversalAlgebra

open Matrix

/-- Applying `reverseStep` twice returns the original step. -/
theorem reverseStep_involution {I : Type*} (s : Step I) :
    reverseStep (reverseStep s) = s := by
  cases s <;> simp [reverseStep]

/-- Circuit reversal reverses the order of concatenation. -/
theorem reverse_append {I : Type*} (C D : Circuit I) :
    ReverseCircuit (C ++ D) = ReverseCircuit D ++ ReverseCircuit C := by
  simp [ReverseCircuit]

/-- Reversing a circuit twice returns the original circuit. -/
theorem reverse_involution {I : Type*} [Fintype I] [DecidableEq I] (C : Circuit I) :
    ReverseCircuit (ReverseCircuit C) = C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    rw [reverseCircuit_cons, reverse_append, reverseCircuit_cons, reverseCircuit_nil,
      List.nil_append, ih, reverseStep_involution]
    rfl

/-- Packages the reversal laws: reversal reverses concatenation order and is an involution. -/
theorem reverse_algebra :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (C D : Circuit I),
      ReverseCircuit (C ++ D) = ReverseCircuit D ++ ReverseCircuit C) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (C : Circuit I),
      ReverseCircuit (ReverseCircuit C) = C) :=
  ⟨fun _ _ _ C D => reverse_append C D, fun _ _ _ C => reverse_involution C⟩

/-- For a Hermitian unitary oracle and a unitary circuit, appending its reverse restores every
input state and doubles both query and fixed-gate counts. -/
theorem run_and_counts
    (I : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (hOH : Oᴴ = O)
    (C : Circuit I) (hC : IsUnitaryCircuit C) (ψ : QState I) :
    Run O (C ++ ReverseCircuit C) ψ = ψ ∧
    QueryCount (C ++ ReverseCircuit C) = 2 * QueryCount C ∧
    GateCount (C ++ ReverseCircuit C) = 2 * GateCount C := by
  refine ⟨?_, ?_, ?_⟩
  · rw [run_append]
    exact run_reverseCircuit_run O hO hOH C hC ψ
  · rw [queryCount_append, queryCount_reverseCircuit, two_mul]
  · rw [gateCount_append, gateCount_reverseCircuit, two_mul]

end Qatlib.Foundations.CircuitReversal.ReversalAlgebra
