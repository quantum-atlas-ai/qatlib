/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.Theorem1Stat
import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialSoundness
import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialAllocatedCost
import Qatlib.Concepts.WalkSearch.MainResults.ClassificationAdaptiveTape
import Qatlib.Concepts.WalkSearch.MainResults.SearchEventBounds
import Qatlib.Concepts.WalkSearch.MainResults.IntegerBounds
import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialTapeCounting
import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialRealBudget
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.WalkSearch.Primitives

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults

theorem combinatorial_program_sound {n : ℕ} (G : UGraph n) (sgs : SGSExecution)
    (ets : PromisedEdgeSearchFamily) (k K c dHi dLo τ tThin : ℕ) :
    sourceCombSound G sgs ets k K c dHi dLo τ tThin := sourceCombAlg_sound G sgs ets k K c dHi dLo τ tThin
open scoped Classical

theorem theorem1_answer : Theorem1 := by
  intro n ε δ ε' hn hε hε1 hδ hε' hparam G family ets hfamily hets
    k K c dHi dLo τ tThin sgs hk hc hdLo
  have hδ1 : δ<1 := by linarith
  have hε'1 : ε'<1 := by linarith
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hτ : 1≤τ := by
    dsimp only [τ]
    exact Nat.ceil_pos.mpr (by positivity)
  have hhi : dLo≤dHi := by
    have hf := Nat.floor_le (by positivity : (0:ℝ)≤(n:ℝ)^(1-δ)/10)
    have hceil := Nat.le_ceil ((n:ℝ)^(1-δ))
    have hh : (Nat.floor ((n:ℝ)^(1-δ)/10):ℝ)≤10*(Nat.ceil ((n:ℝ)^(1-δ)):ℝ) := by
      nlinarith [Real.rpow_nonneg hnR.le (1-δ)]
    exact_mod_cast hh
  refine ⟨sourceCombAlg_sound G sgs ets k K c dHi dLo τ tThin,?_,?_⟩
  · letI:=sgs.seedFin
    letI:=ets.seedFin n
    intro htri
    have hn3 : 3≤n := by
      obtain ⟨⟨a,b,cc⟩,ht⟩ := Finset.one_le_card.mp htri
      have hmem := (mem_trianglesOf_iff G.edges a b cc).mp ht
      have hab : a.val<b.val := hmem.1
      have hbc : b.val<cc.val := hmem.2.1
      omega
    have h0 := source_joint_sampling_bad_card n ε hn hε hε1 G sgs ets K c hk
    have h2 := source_joint_degree_bad_card n δ hn hδ hδ1 G sgs ets k τ hc
    have hh := sourceComb_reject_card_from_local_bounds n k K c dHi dLo τ tThin G family ets
      hfamily hets hn3 hdLo hhi hτ htri h0 h2
    exact hh
  · intro t
    have hcost := sourceCombAlg_allocated_cost G sgs ets k K c dHi dLo τ tThin t hn
    have hcostR : ((Qatlib.Concepts.WalkSearch.MainResults.CombOut.queries (sourceCombAlg G sgs ets k K c dHi dLo τ tThin t)):ℝ)≤
        (sourceCombinatorialBudget sgs ets n k dHi dLo τ K c tThin:ℝ) := by exact_mod_cast hcost
    exact hcostR.trans
        (sourceCombinatorialBudget_real_bound n ε δ ε' family ets hn hε hε1 hδ hε' hparam hdLo)

end Qatlib.Concepts.WalkSearch.MainResults
