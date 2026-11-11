/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialBudgetRun

/-!
# Search scopes for combinatorial triangle finding

`sourceSearchScope` bounds the domains, floor, and checking costs of the search calls used by
the combinatorial algorithm. The support lemmas verify these calls fit the scope, and
`source_triangle_preflight_fits` compares the actual candidate triangle reservation with the
allocated one. For background on quantum search and amplitude amplification, see
[BrassardEtAl2002].

## Main statements

* `sourceSearchScope`: The search scope with domain bound `max (n * n) (n.choose 2 * τ)`, floor
  bound `n * n`, and checking cost bound three.
* `source_triangle_preflight_fits`: A candidate set with at most `n.choose 2 * τ` triangles has
  a safe Grover reservation no greater than `sourceTriangleReservation`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical

/-- The search scope with domain bound `max (n * n) (n.choose 2 * τ)`, floor bound `n * n`, and
checking cost bound three. -/
def sourceSearchScope (n τ : ℕ) : SearchCallScope :=
  ⟨max (n*n) (n.choose 2*τ),n*n,3⟩

/-- Specialize a scoped Grover family to the search scope required by the combinatorial triangle
algorithm. -/
def sourceSearchExecution (family : ScopedGroverFamily) (n τ : ℕ) : SGSExecution :=
  family.execution (sourceSearchScope n τ)

/-- The maximum of one and the two search families' fee factors. -/
def sourceCapabilityFeeFactor (sgs : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily) : ℕ :=
  max 1 (max sgs.κ ets.κ)

/-- The source search scope supports preparation calls on `n * n` candidates with checking cost
two and floor `n * n`. -/
theorem source_preparation_call_supported (n τ : ℕ) : (sourceSearchScope n τ).contains (n*n) 2 (n*n) :=
  ⟨Nat.le_max_left _ _,le_rfl,by norm_num [sourceSearchScope]⟩

/-- If `triCount T ≤ n.choose 2 * τ`, the source search scope supports search over `trianglesOf
T` with checking cost three and floor `n * n`. -/
theorem source_triangle_call_supported (n τ : ℕ) (T : Finset (Fin n×Fin n))
    (hT : triCount T≤ n.choose 2*τ) :
    (sourceSearchScope n τ).contains (Fintype.card {t //t∈trianglesOf T}) 3 (n*n) := by
  refine ⟨?_,le_rfl,le_rfl⟩
  simpa only [Fintype.card_coe] using! hT.trans (Nat.le_max_right _ _)

/-- The safe Grover reservation is monotone in the bound on the number of candidates. -/
theorem safeGroverReservation_mono (sgs : SGSExecution) (N M check floor : ℕ) (hNM : N≤ M) :
    safeGroverReservation sgs N check floor≤ safeGroverReservation sgs M check floor := by
  unfold safeGroverReservation
  gcongr

/-- A candidate set with at most `n.choose 2 * τ` triangles has a safe Grover reservation no
greater than `sourceTriangleReservation`. -/
theorem source_triangle_preflight_fits (sgs : SGSExecution) (n τ : ℕ) (T : Finset (Fin n×Fin n))
    (hT : triCount T≤ n.choose 2*τ) :
    safeGroverReservation sgs (Fintype.card {t //t∈trianglesOf T}) 3 (n*n)≤ sourceTriangleReservation sgs n τ := by
  apply safeGroverReservation_mono
  simpa only [Fintype.card_coe] using! hT
end Qatlib.Concepts.WalkSearch.MainResults
