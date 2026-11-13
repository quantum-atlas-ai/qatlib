/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Theorem5Stat
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContractsClassical
import Qatlib.Concepts.WalkSearch.CollisionSearch.Theorem3Quan
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.CorrectedWalkBounds

/-!
# Corrected subgraph candidate-search guarantees

This module establishes `theorem5_answer`, the corrected contract for `hAlg`, including sound
candidate output, a finite-seed failure bound, and a cost estimate retaining the
collision-solver constant. It also proves `theorem5_unbounded_constant_obstruction`, refuting
the original contract whose cost bound omits that dependence.

These statements concern the abstract candidate-search component of quantum subgraph search as
surveyed in [Ambainis2005].

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.CollisionSearch

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms
open scoped Classical

/-- Every candidate returned by `hAlg` satisfies `hCandRel` for the given pattern graph and
distinguished vertex. -/
theorem hAlg_sound {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (kcs : KCollisionSolver) (r qH : ℕ) (stape : ℕ → kcs.seed) :
    (match hAlg adj H hv kcs r qH stape with
    | (some K, _) => hCandRel adj H hv K = true
    | (none, _) => True) := by
  cases hr : kcs.run r (hCandRel adj H hv) (r * r) r qH (stape 0) with
  | none => simp [hAlg, hr]
  | some K =>
    have hv := kcs.sound r (hCandRel adj H hv) (r * r) r qH (stape 0) hr
    simp [hAlg, hr, hv]

/-- The loopless undirected graph on `Fin k` whose edge set is empty. -/
def emptyOGraph (k : ℕ) : OGraph k where
  edges := ∅
  symm := by intro a b h; cases h
  loopless := by intro a; simp

/-- The original `theorem5` contract is false because its cost constant cannot bound
collision-solver interfaces with arbitrarily large charges. -/
theorem theorem5_unbounded_constant_obstruction : ¬ theorem5 := by
  intro h
  obtain ⟨r, hr, _, hu, _, _, hc⟩ := h 1 4 (by norm_num) (by norm_num)
    (emptyOGraph 4) 0 (fun _ _ => false) (nullKCollisionSolver (2 ^ 22)) 0
  have hr1 : r = 1 := by
    have hupper : r ^ 4 ≤ 2 := by simpa using hu
    by_contra hne
    have hr2 : 2 ≤ r := by omega
    have hp : 2 ^ 4 ≤ r ^ 4 := Nat.pow_le_pow_left hr2 4
    norm_num at hp
    omega
  subst r
  have hb := hc (fun _ => ())
  have heval : hAlg (n := 1) (fun _ _ => false) (emptyOGraph 4) 0 (nullKCollisionSolver (2 ^ 22))
      1 0 (fun _ => ()) = (none, 2 ^ 22) := rfl
  rw [heval] at hb
  norm_num at hb

/-- Establishes the corrected subgraph candidate-search contract `Theorem5`, with least-power
subset sizes and a cost bound retaining the collision-solver constant; see [Ambainis2005]. -/
theorem theorem5_answer : Theorem5 := by
  intro n k hk hn H hv adj kcs qH _hκ
  obtain ⟨r, hr, hl, hu⟩ := correctedSubsetWindow (n^(k-1)) k
    (pow_pos hn _) (by omega)
  refine ⟨r, hr, hl, hu, hAlg_sound adj H hv kcs r qH, ?_, ?_⟩
  · intro hex
    haveI := kcs.seedFin
    have hnone (ρ : kcs.seed) :
        (hAlg adj H hv kcs r qH (fun _ => ρ)).1 = none ↔
          kcs.run r (hCandRel adj H hv) (r*r) r qH ρ = none := by
      cases he : kcs.run r (hCandRel adj H hv) (r*r) r qH ρ with
      | none => simp [hAlg, he]
      | some K =>
        have ht := kcs.sound r (hCandRel adj H hv) (r*r) r qH ρ he
        simp [hAlg, he, ht]
    have ht := kcs.finds r (hCandRel adj H hv) (r*r) r qH hex
    simp only [← hnone] at ht
    exact ht.trans (by omega)
  · exact corrected_hAlg_real_cost hn adj H hv kcs r qH hr

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
