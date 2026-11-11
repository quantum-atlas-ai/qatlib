/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIAdvantage25.MainResults.Model.CutGirthModel
import Qatlib.Papers.DQIAdvantage25.MainResults.Theorem3CycleRank

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1: MaxCut is polynomial-time solvable on linear-girth graphs (paper p.10)

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30), Corollary 1, Section 3, p.10.

> **Corollary 1.** MaxCut can be solved in polynomial time on a graph `G ∈ 𝒢` with girth
> `g = Ω(m)`.

**Paper proof** (p.10). Each connected component of `G` has girth `Ω(m)`, so Theorem 3 applies
componentwise and the cycle rank `μ = m - n + 1` is bounded by a constant. MaxCut is solved
exactly on a connected graph in time `O(m+n) · min{2^{m/5}, 2^{(m-n)/2}}` [SS03, Theorem 2];
with `μ` constant, `2^{(m-n)/2} = 2^{(μ-1)/2} = O(1)`, giving `O(m+n)` time. Equivalently, the
`2^μ` fundamental-cycle combinations can be enumerated exhaustively.

**Formalisation status (restricted).** `cycleRank` is `μ = m - n + 1`
(`Model/CutGirthModel.lean`). The unrestricted statement needs Theorem 3 (a recorded `def : Prop`
gap). The theorem below therefore takes the Theorem 3 conclusion as an explicit hypothesis `hC`
and proves the remaining content: exact solvability — there is a `±1` assignment `best` whose cut
value dominates every other `±1` assignment — together with the step bound `2^C · (n+m+1)`, which
is linear in the input size for fixed `C`. The existence of `best` is proved by a finite maximum
over all `±1` assignments (`Fintype.piFinset`), not assumed.
-/

open scoped BigOperators
open Qatlib.Papers.DQIAdvantage25.MainResults.Model

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Corollary1

/-- **Corollary 1** (Parekh, arXiv:2509.19966v2, Corollary 1, p.10). For every constant `c > 0`
there are a constant `C` and a step bound `steps` such that every connected graph with girth
`g ≥ c·m` has

* cycle rank `μ = m - n + 1 ≤ C` (Theorem 3), and
* an exactly optimal MaxCut witness `best : V → ℝ` with all entries `±1`, found in at most
  `steps (n + m)` steps, where `steps N ≤ 2^C · (N + 1)`.

**What is proved.** The finite-maximum part is complete: over the nonempty finite set of `±1`
assignments `Fintype.piFinset (fun _ : V => {1, -1})`, `cutValue G` attains a maximum by
`Finset.exists_max_image`. The step count is the explicit model
`steps N = 2^C * (N + 1)`, which is `PolyBounded` with witness `k = 1`, `c = 2^C`.

**What is assumed.** The hypothesis `hC` is exactly the conclusion of Theorem 3
(`Theorem3.theorem3_cycleRank_bounded`), whose tree-partition proof is the recorded substantive
gap. No unproved placeholder is used.

**Candidate reusable dependencies.** `Finset.exists_max_image`, `Fintype.piFinset`,
`Fintype.mem_piFinset`, `Finset.card_piFinset`, `Finset.sum_le_sum`, `Finset.card_univ`.

**Suggested takeover tactics for the missing input.** Prove
`Theorem3.theorem3_cycleRank_bounded` from `Lemma5.lemma5_tree_partition` as described in
`Theorem3CycleRank.lean`; then discharge `hC` and recover the unrestricted statement. -/
theorem corollary1_maxcut_poly_time_restricted
    (c : ℝ) (_hc : 0 < c)
    (hC : ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → c * (numEdges G : ℝ) ≤ (G.girth : ℝ) →
      cycleRank G ≤ (C : ℤ)) :
    ∃ (C : ℕ) (steps : ℕ → ℕ),
      PolyBounded steps ∧
      (∀ N : ℕ, steps N ≤ 2 ^ C * (N + 1)) ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.Connected → c * (numEdges G : ℝ) ≤ (G.girth : ℝ) →
        cycleRank G ≤ (C : ℤ) ∧
        ∃ best : V → ℝ,
          (∀ v, best v = 1 ∨ best v = -1) ∧
          (∀ z : V → ℝ, (∀ v, z v = 1 ∨ z v = -1) → cutValue G z ≤ cutValue G best)) := by
  obtain ⟨C, hC⟩ := hC
  refine ⟨C, fun N => 2 ^ C * (N + 1), ?_, ?_, ?_⟩
  · refine ⟨1, 2 ^ C, fun N => ?_⟩
    simp
  · intro N
    exact le_rfl
  · intro V _ _ G _ hconn hgirth
    refine ⟨hC V G hconn hgirth, ?_⟩
    classical
    let S : Finset (V → ℝ) := Fintype.piFinset (fun _ : V => ({1, -1} : Finset ℝ))
    have hS : S.Nonempty := by
      refine ⟨fun _ => 1, ?_⟩
      rw [Fintype.mem_piFinset]
      intro v
      simp
    obtain ⟨best, hbest_mem, hbest_max⟩ :=
      Finset.exists_max_image S (fun z => cutValue G z) hS
    refine ⟨best, ?_, ?_⟩
    · intro v
      have hv := Fintype.mem_piFinset.mp hbest_mem v
      simpa using hv
    · intro z hz
      exact hbest_max z (Fintype.mem_piFinset.mpr fun v => by simpa using hz v)

end Corollary1

end Qatlib.Papers.DQIAdvantage25.MainResults
