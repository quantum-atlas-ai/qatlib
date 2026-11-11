/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWeakness97.MainResults.QueryComparisonMachineDefs

/-!
# Sequential oracle copies and tidy amplification

This module packages concrete finite oracle-circuit constructions as results about
`MachineProgram`. `clause79_complete` executes any number of independent copies through a shared
Boolean query port, with exact query and matrix-gate counts and a tensor-product execution
identity.

`clause80_complete` gives the finite-circuit amplification mechanism associated with Theorem
4.14 of [BennettEtAl1997]. Starting from success probability at least `2/3`, it obtains success
at least `1 - ε` on the desired output bit while restoring the query port and all copied work
registers to their specified basis states.

## Main statements

* `clause79_complete` constructs `k` sequential copies with `k * Q` queries and `k * G + 2 * k *
  Q` matrix gates.
* `clause80_complete` constructs a unitary tidy amplification circuit with a logarithmic bound
  on its repetition parameter and explicit query and gate bounds.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.UniformBqp.OracleAmplify

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

variable {W X : Type} [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]

/-- For a unitary machine circuit and a nonempty address space and workspace, construct `k`
independent sequential copies using `k * Q` queries and `k * G + 2 * k * Q` matrix gates. On
arbitrary product input states, the run applies the original circuit to each copy and
restores the shared query port to its fixed basis state. -/
theorem clause79_complete (k : ℕ) (n : ℕ) (hn : 0 < n) (W : Type) [Fintype W] [DecidableEq W]
    [Nonempty W] (P : MachineProgram n W) (hU : IsUnitaryCircuit P.circuit) :
    ∃ (D : MachineProgram n (Fin k → (Fin n × Bool) × W)),
      IsUnitaryCircuit D.circuit ∧
        D.queryCount = k * P.queryCount ∧
        D.gateCount = k * P.gateCount + 2 * k * P.queryCount ∧
        ∀ (x : Fin n → Bool) (ψ : Fin k → QState ((Fin n × Bool) × W)),
          Run (workspaceBitOracle (W := Fin k → (Fin n × Bool) × W) x) D.circuit
              (TensorState (Ket (⟨0, hn⟩, false)) (PiTensorState ψ)) =
            TensorState (Ket (⟨0, hn⟩, false))
              (PiTensorState fun j => Run (workspaceBitOracle (W := W) x) P.circuit (ψ j)) := by
  have hcop := Qatlib.Concepts.UniformBqp.OracleAmplify.standardOracleSequentialCopies
  unfold Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleSequentialCopies at hcop
  obtain ⟨D, hD, hQ, hG, hrun⟩ := hcop n k hn W P.circuit hU
  refine ⟨MachineProgram.mk D
      (TensorState (Ket (⟨0, hn⟩, false)) (PiTensorState (fun _ => P.initial))) ∅, hD, ?_, ?_, ?_⟩
  · exact hQ
  · exact hG
  · intro x ψ
    exact hrun x ψ

/-- From a unitary oracle circuit whose designated Boolean output is correct with probability at
least `2/3`, construct a unitary tidy circuit succeeding with probability at least `1 - ε`
for every positive `ε`, with explicit query and gate bounds and a repetition parameter
bounded logarithmically in `2 / ε`. The final success event restores all copied seeds and
the query port while retaining the correct output bit, giving the finite-circuit
amplification mechanism associated with Theorem 4.14 of [BennettEtAl1997]. -/
theorem clause80_complete (n : ℕ) (hn : 0 < n) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : MachineProgram n W) (hU : IsUnitaryCircuit P.circuit)
    (seed : (Fin n × Bool) × W) (v : ((Fin n × Bool) × W) → Bool) (input : X → Fin n → Bool)
    (b : X → Bool) (ε : ℝ)
    (hgap : ∀ x : X, (2 / 3 : ℝ) ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (input x)) P.circuit (Ket seed))
        (Finset.univ.filter fun z => v z = b x)) (hε : 0 < ε) :
    ∃ (r : ℕ) (D : Circuit ((Fin n × Bool) × ((Fin (2 * r + 1) → (Fin n × Bool) × W) × Bool))),
      r ≤ Nat.ceil (Real.log (2 / ε) / Real.log (9 / 8)) + 1 ∧
        IsUnitaryCircuit D ∧
        QueryCount D = 2 * (2 * r + 1) * P.queryCount ∧
        GateCount D ≤ 2 * ((2 * r + 1) * P.gateCount + 2 * (2 * r + 1) * P.queryCount) + 3 ∧
        ∀ x : X, 1 - ε ≤ MeasureProb
          (Run (workspaceBitOracle (W := (Fin (2 * r + 1) → (Fin n × Bool) × W) × Bool)
            (input x)) D
              (Ket ((⟨0, hn⟩, false), (fun _ => seed, false))))
            {((⟨0, hn⟩, false), (fun _ => seed, b x))} := by
  have hamp := Qatlib.Concepts.UniformBqp.OracleAmplify.standardOracleTidyAmplification
  unfold Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleTidyAmplification at hamp
  obtain ⟨r, D, hr, hD, hQ, hG, hsucc⟩ := hamp n hn W X P.circuit seed v input b ε hU hgap hε
  refine ⟨r, D, hr, hD, ?_, ?_, ?_⟩
  · exact hQ
  · exact hG
  · intro x
    exact hsucc x

end Qatlib.Papers.QWeakness97.MainResults
