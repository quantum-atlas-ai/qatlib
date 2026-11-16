/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ReadManyQry11.MainResults.SourceModel

@[expose] public section


/-!
Closed input-doubling and input-occurrence definitions retained from arXiv:1112.0548v1. The zero-gate top-gate probe diagnoses the legacy Lemma 3 domain; source circuit normalization and adversary composition remain deferred.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.ReadManyQry11.MainResults

open scoped BigOperators Real

namespace Qatlib.Papers.ReadManyQry11.MainResults

namespace Circuit

variable {n : ℕ}

/-- The number of input-wire occurrences of a circuit (each gate argument that is an
input wire, plus the output when it is an input wire).  This is the paper's formula size
`S` when the circuit is a formula (Lemma 3, p. 6; "the size of a formula is the total
number of inputs counted with multiplicity"). -/
def formulaSize (C : Circuit n) : ℕ :=
  ((C.gates.flatMap (fun g => g.args)).filter (fun a => a.isLeft)).length +
    (if C.out.isLeft then 1 else 0)

end Circuit

/-- The paper's doubling of an input to the `2n` inputs of the monotone circuit `f'` of
Lemma 3 (p. 6): `x₁, x̄₁, x₂, x̄₂, …, x_n, x̄_n`, indexed as `Fin n × Fin 2` and transported
along `Fin n × Fin 2 ≃ Fin (n * 2)`. -/
def doubleInput {n : ℕ} (x : Fin n → Bool) : Fin (n * 2) → Bool :=
  fun j =>
    let p : Fin n × Fin 2 := finProdFinEquiv.symm j
    if p.2 = 0 then x p.1 else !(x p.1)


/-- A monotone circuit with zero gates cannot have a prescribed top gate.
Thus the old Lemma 3 contract needs a nontrivial-gate domain restriction. -/
theorem no_top_at_zero (C : Circuit 2) (hm : C.IsMonotone)
    (hc : C.gateCount ≤ 0) : ¬ C.TopGateIs GateOp.and := by
  have hf : C.gates.filter (fun g => g.op != GateOp.not) = C.gates := by
    apply List.filter_eq_self.mpr
    intro g hg
    simpa using hm g hg
  have hl : C.gates.length = 0 := by
    simpa [Circuit.gateCount, hf] using hc
  rintro ⟨j, hj, hout, hop⟩
  omega

/-- A valid zero-gate input circuit supplies the legacy Lemma 3 counterexample. -/
def inputCircuit : Circuit 1 where
  gates := []
  out := Sum.inl 0
  wf := by intro i; exact Fin.elim0 i
  out_wf := by intro j hj; cases hj

/-- At the valid input circuit the legacy zero-gate monotone top-gate conclusion fails. -/
theorem zero_normal_fail : inputCircuit.gateCount = 0 ∧
    ¬ ∃ C : Circuit 2, C.IsMonotone ∧
      C.gateCount ≤ 2 * inputCircuit.gateCount ∧ C.TopGateIs GateOp.and := by
  refine ⟨rfl, ?_⟩
  rintro ⟨C, hm, hc, ht⟩
  apply no_top_at_zero C hm _ ht
  simpa [inputCircuit, Circuit.gateCount] using hc

end Qatlib.Papers.ReadManyQry11.MainResults
