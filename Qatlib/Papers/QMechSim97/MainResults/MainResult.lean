/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.ResourceComplexity
import Qatlib.Papers.QMechSim97.MainResults.Propagation
import Qatlib.Papers.QMechSim97.MainResults.PotentialWord
import Mathlib.Tactic

/-!
# Simulation resource comparisons

Combines the arithmetic resource estimates for the lattice simulation of [BoghosianTaylor1998]
with separate circuit constructions for propagation and pair potentials.
`resource_comparison_arithmetic` compares the defined quantum gate count with the classical
component count, while `source_actual_resource_pieces` records concrete unitary circuit bounds.

## Main statements

* `resource_comparison_arithmetic`: The qubit count, gate bound, and classical component count
  satisfy the stated comparison for `l ≥ 2` and `n ≥ 2` [BoghosianTaylor1998].
* `source_actual_resource_pieces`: There exist unitary reflection circuits with at most `6 * d *
  l ^ d` gates, and the all-pairs potential circuit is unitary with at most `4 * d ^ 2 * l ^ (2
  * d)` gates [BoghosianTaylor1998].

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.MainResult

open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.ResourceComplexity

/-- The qubit count, gate bound, and classical component count satisfy the stated comparison for
`l ≥ 2` and `n ≥ 2` [BoghosianTaylor1998]. -/
theorem resource_comparison_arithmetic (d l n : ℕ) (hl : 2 ≤ l) (hn : 2 ≤ n) :
    qubitCount d l = 2 * d * l ^ d ∧
    totalQuantumGates d l ≤ (d + 2 * d ^ 2) * (l ^ d) ^ 2 ∧
    classicalComponents d l n = (l ^ d) ^ n ∧
    (d + 2 * d ^ 2) * classicalComponents d l n
      ≥ (l ^ d) ^ (n - 2) * totalQuantumGates d l := by
  have hl1 : 1 ≤ l := by omega
  exact ⟨rfl, totalQuantumGates_le d l hl1, classicalComponents_eq d l n,
    classical_dominates d l n hl hn⟩

/-- There exist unitary reflection circuits with at most `6 * d * l ^ d` gates, and the
all-pairs potential circuit is unitary with at most `4 * d ^ 2 * l ^ (2 * d)` gates
[BoghosianTaylor1998]. -/
theorem source_actual_resource_pieces (d l : ℕ) [NeZero l]
    (θ : Fin (qubitCount d l) → Fin (qubitCount d l) → ℝ) :
    (∃ gs : List (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate
        (qubitCount d l)),
      Qatlib.Foundations.QueryWordCore.Circuit.IsUnitaryCircuit
        (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile gs) ∧
      Qatlib.Foundations.QueryWordCore.Circuit.GateCount
        (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile gs) ≤
          6 * d * l ^ d) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.IsUnitaryCircuit
      (PotentialWord.potentialWord (PotentialWord.wirePairs (qubitCount d l)) θ) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount
      (PotentialWord.potentialWord (PotentialWord.wirePairs (qubitCount d l)) θ) ≤
        4 * d ^ 2 * l ^ (2 * d) := by
  obtain ⟨gs,_,hU,_,hG,_⟩ := Propagation.lattice_propagation_word d l
  have hP := PotentialWord.lattice_potential_resources d l θ
  exact ⟨⟨gs,hU,hG⟩,hP.1,hP.2.2⟩

end Qatlib.Papers.QMechSim97.MainResults.MainResult
