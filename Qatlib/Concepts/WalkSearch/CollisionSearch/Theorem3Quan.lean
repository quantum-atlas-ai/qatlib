/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.CollisionSearch.Theorem3Stat
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContractsClassical
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.CorrectedWalkBounds

/-!
# Graph collision from corrected solver contracts

The module proves soundness and cost identities for the graph-collision reduction `gcAlg`. It
constructs degenerate solver examples, uses a zero-charge solver to refute `theorem3`, and
establishes the corrected proposition `Theorem3` with its positive cost-constant assumption. See
[Ambainis2005] for the mathematical background.

## Main statements

* `gcAlg_sound`: validity of every returned graph collision.
* `theorem3_zero_constant_obstruction`: failure of `theorem3`.
* `theorem3_answer`: the corrected graph-collision proposition.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.CollisionSearch
open scoped Classical

/-- A collision-solver contract instance with one seed, failure exponent zero, cost constant
`K`, an always-empty result, and cost `K * s`. -/
def nullKCollisionSolver (K : ℕ) : KCollisionSolver where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := K
  run := fun {_n _k} _r _R _s _u _c _ρ => none
  cost := fun {_n _k} _r _R s _u _c _ρ => K * s
  sound := by intro n k r R s u c ρ t h; cases h
  reject := by intros; rfl
  finds := by intros; simp
  charges := by
    intro n k r R s u c ρ
    have hs : s ≤ (Nat.log 2 (n + 1) + 2) *
        (s + (n / r) ^ (k / 2) * (c + Nat.sqrt r * u)) := by
      calc
        s = 1 * s := (Nat.one_mul s).symm
        _ ≤ (Nat.log 2 (n + 1) + 2) * s := Nat.mul_le_mul_right s (by omega)
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    exact (Nat.mul_le_mul_left K hs).trans_eq (Nat.mul_assoc _ _ _).symm

/-- A collision-solver contract instance that chooses a satisfying tuple when one exists and
assigns zero cost, zero cost constant, and failure exponent zero. -/
def zeroChargeCollisionSolver : KCollisionSolver where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := 0
  run := fun {_n _k} _r R _s _u _c _ρ =>
    if h : ∃ t, R t = true then some (Classical.choose h) else none
  cost := fun {_n _k} _r _R _s _u _c _ρ => 0
  sound := by
    intro n k r R s u c ρ t ht
    split at ht
    · rename_i h
      cases ht
      exact Classical.choose_spec h
    · cases ht
  reject := by
    intro n k r R s u c ρ hR
    have hn : ¬ ∃ t, R t = true := by
      rintro ⟨t, ht⟩
      rw [hR t] at ht
      cases ht
    simp [hn]
  finds := by
    intro n k r R s u c hR
    simp [hR]
  charges := by intros; simp

/-- Every pair returned by `gcAlg` consists of distinct vertices joined by an edge and both
marked by `f`. -/
theorem gcAlg_sound {n : ℕ} (G : OGraph n) (f : Fin n → Bool)
    (kcs : KCollisionSolver) (r : ℕ) (ρ : kcs.seed) :
    (match gcAlg G f kcs r ρ with
    | (some (u, v), _) => f u = true ∧ f v = true ∧ (u, v) ∈ G.edges ∧ u ≠ v
    | (none, _) => True) := by
  cases hr : kcs.run r (gcRel G f) r 1 0 ρ with
  | none => simp [gcAlg, hr]
  | some t =>
    have hv := kcs.sound r (gcRel G f) r 1 0 ρ hr
    have hvals : f (t 0) = true ∧ f (t 1) = true ∧ (t 0, t 1) ∈ G.edges := by
      simpa [gcRel, adjB, Bool.and_eq_true, and_assoc] using hv
    have hne : t 0 ≠ t 1 := by
      intro he
      exact G.loopless (t 1) (he ▸ hvals.2.2)
    have hadj : adjB G (t 0) (t 1) = true := by simpa [adjB] using hvals.2.2
    simp [gcAlg, hr, hvals.1, hvals.2.1, hadj, hvals.2.2, hne]

/-- The graph-collision reduction returns no pair exactly when its underlying collision-solver
invocation returns no tuple. -/
theorem gcAlg_none_iff {n : ℕ} (G : OGraph n) (f : Fin n → Bool)
    (kcs : KCollisionSolver) (r : ℕ) (ρ : kcs.seed) :
    (gcAlg G f kcs r ρ).1 = none ↔ kcs.run r (gcRel G f) r 1 0 ρ = none := by
  cases hr : kcs.run r (gcRel G f) r 1 0 ρ with
  | none => simp [gcAlg, hr]
  | some t =>
    have hv := kcs.sound r (gcRel G f) r 1 0 ρ hr
    have hvals : (f (t 0) = true ∧ f (t 1) = true) ∧ adjB G (t 0) (t 1) = true := by
      simpa only [gcRel, Bool.and_eq_true] using hv
    simp [gcAlg, hr, hvals.1.1, hvals.1.2, hvals.2]

/-- When the underlying solver returns a tuple, the graph-collision reduction's cost is the
solver cost plus 2. -/
theorem gcAlg_some_cost {n : ℕ} (G : OGraph n) (f : Fin n → Bool)
    (kcs : KCollisionSolver) (r : ℕ) (ρ : kcs.seed) (t : Fin 2 → Fin n)
    (hr : kcs.run r (gcRel G f) r 1 0 ρ = some t) :
    (gcAlg G f kcs r ρ).2 = kcs.cost r (gcRel G f) r 1 0 ρ + 2 := by
  simp only [gcAlg, hr]
  split_ifs <;> rfl

/-- The loopless symmetric graph on two vertices whose edges are all ordered pairs of distinct
vertices. -/
def twoVertexEdgeGraph : OGraph 2 where
  edges := Finset.univ.filter (fun p : Fin 2 × Fin 2 => p.1 ≠ p.2)
  symm := by
    intro a b h
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (show b ≠ a from (Finset.mem_filter.mp h).2.symm)
  loopless := by intro a; simp

/-- Refutes `theorem3` using a zero-charge solver and the graph on two vertices. -/
theorem theorem3_zero_constant_obstruction : ¬ theorem3 := by
  intro h
  obtain ⟨r, _, _, _, _, _, hc⟩ := h 2 (by norm_num) twoVertexEdgeGraph
    (fun _ => true) zeroChargeCollisionSolver
  have hex : ∃ t : Fin 2 → Fin 2, gcRel twoVertexEdgeGraph (fun _ => true) t = true :=
    ⟨id, by simp [gcRel, adjB, twoVertexEdgeGraph]⟩
  have hr : zeroChargeCollisionSolver.run r (gcRel twoVertexEdgeGraph (fun _ => true))
      r 1 0 () = some (Classical.choose hex) := by
    simp [zeroChargeCollisionSolver, hex]
  have hb := hc ()
  rw [gcAlg_some_cost _ _ _ _ _ _ hr] at hb
  norm_num [zeroChargeCollisionSolver] at hb

/-- Establishes the corrected graph-collision contract `Theorem3`, using the positive
cost-constant assumption and a suitable subset size. See [Ambainis2005]. -/
theorem theorem3_answer : Theorem3 := by
  intro n hn G f kcs hκ
  obtain ⟨r, hr, hl, hu⟩ := correctedSubsetWindow (n^2) 3 (pow_pos hn _) (by decide)
  have hrn : r ≤ n := by
    by_contra hh
    have hh' : n ≤ r-1 := by omega
    have hp := Nat.pow_le_pow_left hh' 3
    have hn23 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn (by decide)
    omega
  have hp := Nat.pow_le_pow_left hrn 3
  refine ⟨r, hr, by nlinarith [hl], by nlinarith [hp], gcAlg_sound G f kcs r, ?_, ?_⟩
  · intro hex
    haveI := kcs.seedFin
    simpa only [gcAlg_none_iff] using kcs.finds r (gcRel G f) r 1 0 hex
  · intro ρ
    apply corrected_gc_budget n r kcs.κ (gcAlg G f kcs r ρ).2 hn hr hκ hl hu
    have hc := kcs.charges r (gcRel G f) r 1 0 ρ
    norm_num only [Nat.reduceDiv, pow_one, zero_add, mul_one] at hc
    cases he : kcs.run r (gcRel G f) r 1 0 ρ with
    | none => simpa only [gcAlg, he] using hc.trans (Nat.le_add_right _ 2)
    | some t =>
      rw [gcAlg_some_cost G f kcs r ρ t he]
      exact Nat.add_le_add_right hc 2

end Qatlib.Concepts.WalkSearch.CollisionSearch
