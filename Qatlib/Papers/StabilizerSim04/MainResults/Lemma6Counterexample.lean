/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StabilizerSim04.MainResults.Basic

@[expose] public section

/-!
# The Hadamard-mask rank statement needs independent generators

The Public statement `Qatlib.Papers.StabilizerSim04.MainResults.lemma6_hadamard_full_rank_statement`
asserts that every *consistent* square tableau admits a Hadamard mask making the X matrix
nonsingular. Consistency only asks the decoded rows to be Hermitian and pairwise commuting, so it
admits the tableau all of whose rows are the identity Pauli element. For that tableau every mask
leaves the X matrix zero, and the kernel is the whole vector space.

This module records that refutation. It isolates the missing hypothesis: the lemma of
[AaronsonGottesman2004] is applied to `n` independent commuting generators, and the rank argument
uses that independence. The corrected statement therefore needs
`Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.IndependentGenerators` on
`tableauGenerators t`, which is not part of the statement above. No corrected version is proved
here.

## Main statements

* `consistentTableau_identityRows`: the all-identity square tableau is consistent.
* `not_lemma6_hadamard_full_rank_statement`: the stated lemma is false as written.

## References

* [Aaronson and Gottesman, 2004][AaronsonGottesman2004]

https://arxiv.org/abs/quant-ph/0406196
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StabilizerSim04.MainResults

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Papers.StabilizerSim04.MainResults
open Matrix
open scoped Classical BigOperators

/-- The tableau whose every row is the identity Pauli element. -/
def identityRows (n : ℕ) : Tableau n n := fun _ => ⟨fun _ => false, fun _ => false, 0⟩

/-- The all-identity square tableau is consistent: every row decodes to a Hermitian Pauli element
and the decoded operators commute. -/
theorem consistentTableau_identityRows (n : ℕ) : ConsistentTableau (identityRows n) := by
  constructor
  · intro a
    left
    rfl
  · intro a b
    simp [identityRows, Row.decode, letter, op_trivial_word]

/-- The Hadamard-mask full-rank statement of [AaronsonGottesman2004], Lemma 6, is false for a
merely consistent tableau: the all-identity tableau has zero X matrix under every mask, so its
kernel is nontrivial. -/
theorem not_lemma6_hadamard_full_rank_statement : ¬ lemma6_hadamard_full_rank_statement := by
  intro h
  obtain ⟨mask, hm⟩ := h 1 (identityRows 1) (consistentTableau_identityRows 1)
  have hzero : ∀ i : Fin 1, ∑ j, (fun _ : Fin 1 => (1 : ZMod 2)) j *
      xMatrix (fun a => hadamardPoints mask (identityRows 1 a)) i j = 0 := by
    intro i
    simp [xMatrix, hadamardPoints, identityRows]
  have hv := hm (fun _ : Fin 1 => 1) hzero
  have h0 : (1 : ZMod 2) = 0 := congrFun hv 0
  exact absurd h0 (by decide)

end Qatlib.Papers.StabilizerSim04.MainResults
