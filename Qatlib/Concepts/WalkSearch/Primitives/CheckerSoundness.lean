/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContractsClassical

/-!
# Soundness of the triangle checker

Proves that every pair returned by `triCheck` consists of distinct vertices in the chosen
subset, with a witness adjacent to both and an edge between the pair. This supplies the explicit
adjacency conditions used by the graph-search checker; see [Ambainis2005] for search background.

## Main statements

* `triCheck_sound`: Whenever `triCheck` returns `(u₁, u₂)`, these are distinct members of `U`
  and there exists a vertex `v` with `adj v u₁ = true`, `adj v u₂ = true`, and `adj u₁ u₂ =
  true`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

open Qatlib.Concepts.WalkSearch.WalkAlgorithms

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

/-- Whenever `triCheck` returns `(u₁, u₂)`, these are distinct members of `U` and there exists a
vertex `v` with `adj v u₁ = true`, `adj v u₂ = true`, and `adj u₁ u₂ = true`. -/
theorem triCheck_sound {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (ntape : ncs.seed) :
    (match triCheck adj U kcs ncs r' c₀ stape ntape with
    | (some (u₁,u₂),_) => u₁∈U ∧ u₂∈U ∧ u₁≠u₂ ∧
        ∃ v : Fin n,adj v u₁=true ∧ adj v u₂=true ∧ adj u₁ u₂=true
    | (none,_) => True) := by
  let m := Fintype.card ↥U
  let e : Fin m → Fin n := fun i => ((Fintype.equivFin ↥U).symm i : Fin n)
  have he (i : Fin m) : e i∈U := ((Fintype.equivFin ↥U).symm i).property
  have hinj : Function.Injective e := by
    intro a b hab
    exact (Fintype.equivFin ↥U).symm.injective (Subtype.ext hab)
  unfold triCheck
  (try dsimp only)
  split
  · rename_i u₁ u₂ q houtput
    split at houtput
    · rename_i v hsearch
      split at houtput
      · rename_i t hrun
        cases houtput
        have h := kcs.sound (n := m) (k := 2) r'
          (fun t => decide (t 0≠t 1 ∧ adj v (e (t 0)) ∧ adj v (e (t 1)) ∧ adj (e (t 0)) (e (t 1))))
          r' 1 0 (stape (v.val*c₀)) hrun
        have ht : t 0≠t 1 ∧ adj v (e (t 0))=true ∧ adj v (e (t 1))=true ∧
            adj (e (t 0)) (e (t 1))=true := of_decide_eq_true h
        exact ⟨he _,he _,fun hEq => ht.1 (hinj hEq),v,ht.2⟩
      · simp at houtput
    · simp at houtput
  · trivial
end Qatlib.Concepts.WalkSearch.Primitives
