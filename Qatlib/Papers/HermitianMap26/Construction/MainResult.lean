/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Basic
import Qatlib.Papers.HermitianMap26.Construction.PostProcessing

/-!
# Exact signed post-processing of a CPTP compilation

This module packages the signed Kraus compilation and exact trace reconstruction identities of
[CaiEtAl2026]. The completed `compiledFamily` is Kraus complete and defines a completely
positive, trace-preserving map, while `compiledProgram` provides its binary-tree realization.

The identity `trace_completed_postprocessing` recovers every trace pairing with the signed
action from weighted physical branch contributions. The completion branch carries zero
post-processing weight.

## Main statements

* `source_construction`: collects completeness, channel properties, the `SingleQubit` condition,
  and the leaf measurement count.
* `single_cptp_compilation`: combines exact post-processing with the branch-forgetting
  semantics.

## References

* [Cai et al., 2026][CaiEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.DimInstruments.DimTreeExec
open scoped ComplexOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction.SignedKraus

variable {d r : ℕ} (D : SignedKraus d r)

/-- The trace pairing with the signed Kraus output equals the sum of the completed
compiled-branch trace pairings weighted by their post-processing weights. [CaiEtAl2026]. -/
theorem trace_completed_postprocessing (hd : 0 < d) (ρ O : Op d) :
    (D.action ρ * O).trace =
      ∑ i, D.postProcessingWeight D.normalization i *
        (D.compiledFamily i * ρ * (D.compiledFamily i)ᴴ * O).trace := by
  rw [Fin.sum_univ_castSucc]
  simp only [compiledFamily, completedKraus_castSucc, completedKraus_last,
    postProcessingWeight_castSucc, postProcessingWeight_last, zero_mul, add_zero]
  rw [D.trace_postprocessing D.normalization (D.normalization_pos hd) ρ O, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)

/-- In positive dimension, the compiled family is complete and induces a completely positive,
trace-preserving map. Its compiled program satisfies `SingleQubit` and uses exactly
`Nat.clog 2 (r + 1)` measurements at every leaf. [CaiEtAl2026]. -/
theorem source_construction (hd : 0 < d) :
    KrausComplete D.compiledFamily ∧
      CompletelyPositive (krausMap D.compiledFamily) ∧
      TracePreserving (krausMap D.compiledFamily) ∧
      Qatlib.Concepts.KrausCompile.BinaryTree.SingleQubit d (D.compiledProgram hd) ∧
      (∀ t ∈ leaves (D.compiledProgram hd), t.measurements = Nat.clog 2 (r+1)) := by
  obtain ⟨hc, hp, ht⟩ := D.completed_cptp hd
  exact ⟨hc, hp, ht, D.compiled_binary_tree_circuit hd, D.construction_depth_bound hd⟩

/-- The completed family defines a completely positive, trace-preserving map whose branch trace
pairings recover the signed action by post-processing. Forgetting the program's branches
gives this same Kraus map. -/
theorem single_cptp_compilation (hd : 0 < d) :
    CompletelyPositive (krausMap D.compiledFamily) ∧
      TracePreserving (krausMap D.compiledFamily) ∧
      (∀ ρ O, (D.action ρ * O).trace =
        ∑ i, D.postProcessingWeight D.normalization i *
          (D.compiledFamily i * ρ * (D.compiledFamily i)ᴴ * O).trace) ∧
      (∀ ρ, forget (D.compiledProgram hd) ρ = krausMap D.compiledFamily ρ) := by
  obtain ⟨_, hp, ht⟩ := D.completed_cptp hd
  exact ⟨hp, ht, D.trace_completed_postprocessing hd, D.compiledProgram_forget hd⟩

end Qatlib.Papers.HermitianMap26.Construction.SignedKraus
