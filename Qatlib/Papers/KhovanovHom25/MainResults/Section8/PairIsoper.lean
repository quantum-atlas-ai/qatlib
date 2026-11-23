/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairBridge
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairFlow

/-!
# A constructive isoperimetric bound for the actual two-particle source graph

The finite directed flow of PairFlow has divergence two off the adjacent-pair
diagonal and minus `N-1` on it. The proved occupied-subset and cut bridges
transfer that calculation to the source graph. This replaces the false
strict loop-versus-cut claim in source Lemma40 and proves the ratio estimate
used in Corollary41 without invoking that false claim.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.KhovanovHom25.MainResults

open Qatlib.Papers.KhovanovHom25.MainResults

/-- The two-axis particle flow bounds the actual source loop-plus-cut weight below. -/
theorem two_sector_ratio (N : ℕ) (S : Finset (Vertex (N + 1)))
    (hS : S ⊆ vertexSet (N + 1) 2) :
    (S.card : ℚ) / ((N : ℚ) + 1) ≤
      loopSum N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) S +
        cutWeight N (twistedUnknotEdges N) S := by
  have hnat := PairFlow.two_card_le (PairBridge.pull S)
  rw [PairBridge.card_pull S hS] at hnat
  have hflow : (2 : ℚ) * (S.card : ℚ) ≤
      ((N : ℚ) + 1) * (PairFlow.loopCount (PairBridge.pull S) : ℚ) +
        (N : ℚ) * (PairFlow.cutCount (PairBridge.pull S) : ℚ) := by
    exact_mod_cast hnat
  have hloop := PairBridge.loop_pull S hS
  have hcount : (PairFlow.loopCount (PairBridge.pull S) : ℚ) =
      2 * loopSum N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) S := by
    linarith
  rw [hcount] at hflow
  have hcut := PairBridge.cut_pull_le S hS
  have hmul := mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg N : (0 : ℚ) ≤ N)
  have hnonneg : (0 : ℚ) ≤ cutWeight N (twistedUnknotEdges N) S := by
    unfold cutWeight
    positivity
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < (N : ℚ) + 1)]
  nlinarith

end Qatlib.Papers.KhovanovHom25.MainResults
