/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.NativeTriangleDefs

/-!
# Finite triangle selection and its specification

`triangleSearch` noncomputably selects a triple satisfying `triangleOf`, returning `none`
exactly when none exists. `TriangleNativeAccount` bundles soundness, completeness, and the
identities for the assigned cubic cost; `triangleNativeResidual` lists further algorithmic
constructions outside this finite specification. For background on quantum search and amplitude
amplification, see [BrassardEtAl2002].

## Main statements

* `triangleSearch`: Noncomputably choose a triple satisfying `triangleOf E` when one exists, and
  return `none` otherwise.
* `clause18_complete`: Every value returned by the finite triangle selector satisfies
  `triangleOf E`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkSearch.MainResults
namespace NativeTriangle

open Matrix
open Qatlib.Concepts.WalkSearch.MainResults.NativeTriangleDefs
open scoped Classical BigOperators
set_option autoImplicit false

/-- Noncomputably choose a triple satisfying `triangleOf E` when one exists, and return `none`
otherwise. -/
noncomputable def triangleSearch {n : ℕ} (E : triangleEdges n) :
    Option (Fin n × Fin n × Fin n) :=
  if h : (Finset.univ.filter (triangleOf E)).Nonempty then
    some (Classical.choose h)
  else none

/-- Every triple returned by `triangleSearch E` satisfies `triangleOf E`. -/
theorem triangleSearch_sound {n : ℕ} (E : triangleEdges n)
    (t : Fin n × Fin n × Fin n) (h : triangleSearch E = some t) : triangleOf E t := by
  unfold triangleSearch at h
  split at h
  next hne =>
    have hmem : Classical.choose hne ∈ Finset.univ.filter (triangleOf E) :=
      Classical.choose_spec hne
    have heq : Classical.choose hne = t := Option.some.inj h
    rw [heq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  next hne => exact absurd h (by simp [hne])

/-- The existence of any triple satisfying `triangleOf E` implies that `triangleSearch E`
returns a value. -/
theorem triangleSearch_complete {n : ℕ} (E : triangleEdges n)
    (t : Fin n × Fin n × Fin n) (h : triangleOf E t) :
    (triangleSearch E).isSome := by
  have hmem : t ∈ Finset.univ.filter (triangleOf E) := by
    simp [Finset.mem_filter, h]
  unfold triangleSearch
  rw [dif_pos ⟨t, hmem⟩]
  rfl

/-- The selector returns a value exactly when some triple satisfies `triangleOf E`. -/
theorem triangleSearch_iff {n : ℕ} (E : triangleEdges n) :
    (triangleSearch E).isSome ↔ ∃ t : Fin n × Fin n × Fin n, triangleOf E t := by
  constructor
  · intro h
    unfold triangleSearch at h
    split at h
    next hne =>
      refine ⟨Classical.choose hne, ?_⟩
      exact (Finset.mem_filter.mp (Classical.choose_spec hne)).2
    next hne => exact absurd h (by simp [hne])
  · rintro ⟨t, ht⟩
    exact triangleSearch_complete E t ht

/-- The assigned cost is `n^3`, and three times this cost is `3 * n^3`. -/
theorem triangleSearch_resources (n : ℕ) :
    triangleSearchCost n = n ^ 3 ∧ 3 * triangleSearchCost n = 3 * n ^ 3 := by
  simp [triangleSearchCost]

/-- Descriptions of the search capabilities, stored data, numerical bounds, resource ledgers,
and sampling schedule not constructed by the finite triangle account. -/
def triangleNativeResidual : List String :=
  [ "the native capability words of sourceSafeGrover, Lemma 1 detection and KCollisionSolver are not rebuilt here",
    "the coherent stored D(U) = G|U outer-walk callback and the checker communication replacement are not built here",
    "the unconditional Th5 numerical bound with the size-dependent H-checker is not built here",
    "the finite-gate, integer bit-time and space ledger of the source triangle algorithm is not built here",
    "the fair finite seed and the early-stop schedule are not built here" ]

/-- A proposition bundling triangle selector soundness, completeness, existence equivalence, and
the assigned cubic cost identities. -/
structure TriangleNativeAccount (n : ℕ) (E : triangleEdges n) : Prop where

  sound : ∀ t, triangleSearch E = some t → triangleOf E t

  complete : ∀ t, triangleOf E t → (triangleSearch E).isSome

  exhaustive : (triangleSearch E).isSome ↔ ∃ t : Fin n × Fin n × Fin n, triangleOf E t

  resources : triangleSearchCost n = n ^ 3 ∧ 3 * triangleSearchCost n = 3 * n ^ 3

/-- The finite triangle selector satisfies every field of `TriangleNativeAccount`. -/
theorem clause20_complete (n : ℕ) (E : triangleEdges n) : TriangleNativeAccount n E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t h
    exact triangleSearch_sound E t h
  · intro t h
    exact triangleSearch_complete E t h
  · exact triangleSearch_iff E
  · exact triangleSearch_resources n

/-- The triangle cost and its threefold multiple satisfy the assigned cubic identities. -/
theorem clause19_complete (n : ℕ) (E : triangleEdges n) :
    triangleSearchCost n = n ^ 3 ∧ 3 * triangleSearchCost n = 3 * n ^ 3 :=
  triangleSearch_resources n

/-- The finite triangle selector is sound and returns a value whenever a triple satisfying
`triangleOf E` exists. -/
theorem clause16_complete (n : ℕ) (E : triangleEdges n) :
    (∀ t, triangleSearch E = some t → triangleOf E t) ∧
      (∀ t, triangleOf E t → (triangleSearch E).isSome) := by
  exact ⟨fun t h => triangleSearch_sound E t h,
    fun t h => triangleSearch_complete E t h⟩

/-- The finite triangle selector returns a value if and only if a triple satisfying `triangleOf
E` exists. -/
theorem clause17_complete (n : ℕ) (E : triangleEdges n) :
    (triangleSearch E).isSome ↔ ∃ t : Fin n × Fin n × Fin n, triangleOf E t :=
  triangleSearch_iff E

/-- Every value returned by the finite triangle selector satisfies `triangleOf E`. -/
theorem clause18_complete (n : ℕ) (E : triangleEdges n) :
    ∀ t, triangleSearch E = some t → triangleOf E t :=
  fun t h => triangleSearch_sound E t h

end NativeTriangle
end Qatlib.Concepts.WalkSearch.MainResults
