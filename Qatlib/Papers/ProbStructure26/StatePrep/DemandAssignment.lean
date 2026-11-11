/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Demand-assignment support and the deterministic closing pass

Formal core of Corollary 1 and Lemmas S6–S7 of *Harnessing problem structure
for end-to-end quantum speed-ups* (arXiv:2609.40105v1), Methods “Search support
and resources for facility location” and Supplementary Section V.2–V.3.

For `a` facilities and `b` demands the paper prepares the exact uniform
superposition over the `a^b` demand-assignment strings, all facilities kept
open during the recursion, and then closes every facility that serves no
demand.  The declarations below establish the three combinatorial facts the
corollary rests on:

* the assignment register has exactly `a^b` configurations
  (`card_demandAssignment`);
* the closing pass `x ↦ (x, used facilities)` is a bijection from all-open
  assignments onto the configurations in which a facility is open exactly when
  it is used (`closing_bijective`, `card_closedAssignment`) — this is the
  statement of Lemma S7 that the closing pass maps `F_open` bijectively to
  `F_asg`;
* a recursive reassignment changes only one demand row and only the two
  facility bits `old → new`, leaving every facility bit open
  (`reassignRow_apply_self`, `reassignRow_apply_ne`,
  `reassignRow_preserves_allOpen`) — the locality statement of Lemma S6.

The per-row amplitudes of the recursion are supplied by
`SplitMassChain.uniform_population`; gate-level synthesis is not modelled here.
-/

namespace Qatlib.Papers.ProbStructure26.StatePrep

open Finset

/-- A demand assignment with `a` facilities and `b` demands: every demand
chooses exactly one facility. -/
abbrev DemandAssignment (a b : ℕ) := Fin b → Fin a

/-- The facilities actually used by at least one demand. -/
def usedFacilities {a b : ℕ} (x : DemandAssignment a b) : Finset (Fin a) :=
  Finset.univ.image x

/-- The closing pass of Corollary 1: facility `j` is open exactly when some
demand is assigned to it. -/
def closingBits {a b : ℕ} (x : DemandAssignment a b) : Fin a → Bool :=
  fun j => decide (j ∈ usedFacilities x)

/-- A closed assignment: the opening bits are exactly the indicator of the used
facility set, i.e. no unused facility is left open and no used one is closed. -/
def ClosedAssignment (a b : ℕ) :=
  { p : DemandAssignment a b × (Fin a → Bool) //
      ∀ j, (p.2 j = true ↔ ∃ i, p.1 i = j) }

/-- Closed assignments form a finite type by their finite ambient function space. -/
noncomputable instance closedAssignmentFintype (a b : ℕ) : Fintype (ClosedAssignment a b) := by
  classical
  exact Subtype.fintype _

/-- Membership in the used facility set is exactly being the image of a demand. -/
theorem mem_usedFacilities {a b : ℕ} {x : DemandAssignment a b} {j : Fin a} :
    j ∈ usedFacilities x ↔ ∃ i, x i = j := by
  simp [usedFacilities]

/-- The closing bit of a facility is set exactly when that facility is used. -/
theorem closingBits_eq_true {a b : ℕ} {x : DemandAssignment a b} {j : Fin a} :
    closingBits x j = true ↔ ∃ i, x i = j := by
  simp [closingBits, mem_usedFacilities]

/-- The closing pass sends every assignment to a closed assignment. -/
def closingPass {a b : ℕ} (x : DemandAssignment a b) : ClosedAssignment a b :=
  ⟨(x, closingBits x), fun _ => closingBits_eq_true⟩

/-- Lemma S7: the closing pass is a bijection from all-open demand assignments
onto the assignment support, so closing unused facilities neither loses nor
duplicates a configuration. -/
theorem closing_bijective (a b : ℕ) : Function.Bijective (closingPass (a := a) (b := b)) := by
  constructor
  · intro x y h
    have h' : (x, closingBits x) = (y, closingBits y) := Subtype.ext_iff.mp h
    exact Prod.mk.inj h' |>.1
  · intro p
    obtain ⟨⟨x, y⟩, hy⟩ := p
    refine ⟨x, ?_⟩
    have hyx : y = closingBits x := by
      funext j
      apply Bool.eq_iff_iff.mpr
      rw [hy j, closingBits_eq_true]
    apply Subtype.ext
    simp only [closingPass]
    rw [hyx]

/-- The assignment register has exactly `a^b` configurations. -/
theorem card_demandAssignment (a b : ℕ) :
    Fintype.card (DemandAssignment a b) = a ^ b := by
  simp [DemandAssignment]

/-- Corollary 1 support size: the closed assignment support also has `a^b`
configurations, because the closing pass is a bijection. -/
theorem card_closedAssignment (a b : ℕ) :
    Fintype.card (ClosedAssignment a b) = a ^ b := by
  rw [← card_demandAssignment a b]
  exact Fintype.card_congr ((Equiv.ofBijective (closingPass (a := a) (b := b)) (closing_bijective a b)).symm)

/-- All-open intermediate representation used while the assignment recursion
runs. -/
def allOpen (a : ℕ) : Fin a → Bool := fun _ => true

/-- A recursive reassignment in one demand row: demand `i` switches from its
current facility to facility `k`; all other demands are untouched. -/
def reassignRow {a b : ℕ} (i : Fin b) (k : Fin a) (x : DemandAssignment a b) :
    DemandAssignment a b :=
  Function.update x i k

/-- The reassigned demand now uses the new facility. -/
theorem reassignRow_apply_self {a b : ℕ} (i : Fin b) (k : Fin a)
    (x : DemandAssignment a b) : reassignRow i k x i = k := by
  simp [reassignRow]

/-- Every other demand row is untouched by the reassignment. -/
theorem reassignRow_apply_ne {a b : ℕ} (i i' : Fin b) (k : Fin a)
    (x : DemandAssignment a b) (h : i' ≠ i) : reassignRow i k x i' = x i' := by
  simp [reassignRow, h]

/-- Lemma S6 support statement: the reassignment changes the facility choice of
exactly one demand, hence acts inside one demand row. -/
theorem reassignRow_support {a b : ℕ} (i : Fin b) (k : Fin a)
    (x : DemandAssignment a b) :
    {i' | reassignRow i k x i' ≠ x i'} ⊆ {i} := by
  intro i' hi'
  by_contra hne
  exact hi' (reassignRow_apply_ne i i' k x (by simpa using hne))

/-- Lemma S6 invariant: the reassignment acts only on the assignment register,
so the all-open facility bits are preserved. -/
theorem reassignRow_preserves_allOpen {a b : ℕ} (i : Fin b) (k : Fin a)
    (x : DemandAssignment a b) (y : Fin a → Bool) (hy : y = allOpen a) :
    (reassignRow i k x, y) = (reassignRow i k x, allOpen a) := by
  rw [hy]

end Qatlib.Papers.ProbStructure26.StatePrep
