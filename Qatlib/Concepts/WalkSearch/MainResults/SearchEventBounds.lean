/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.PreparationScan
import Qatlib.Concepts.WalkSearch.MainResults.FiniteEventFibers

/-!
# Failure counts for scoped search calls

`safeGroverBadSeeds` collects seeds that fail to find an existing marked element. The module
translates the scoped search family guarantee into cardinality bounds, pads them to a common
cubic denominator, and bounds the event of any bad preparation call on a vertex seed tape. For
background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `safeGroverBadSeeds`: The seeds for which a marked element exists but the operational search
  returns `none`.
* `preparation_bad_calls_card`: Under the scope and exponent assumptions, the number of vertex
  seed tapes with a bad preparation call times `(n * n + 1)^3` is at most `n` times the total
  tape count.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false



open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators

/-- The seeds for which a marked element exists but the operational search returns `none`. -/
def safeGroverBadSeeds (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) : Finset sgs.seed := by
  letI:=sgs.seedFin
  exact Finset.univ.filter
      (fun ρ=>(∃ x,marked x=true) ∧ operationalSgsFind sgs marked check floor ρ=none)

/-- For a supported call, the bad seed count times `(max (Fintype.card α) floor +
1)^family.cExp` is at most the total seed count. -/
theorem safeGroverBadSeeds_source_bound (family : ScopedGroverFamily) (scope : SearchCallScope)
    {α : Type} [Fintype α] (marked : α → Bool) (check floor : ℕ)
    (h : scope.contains (Fintype.card α) check floor) :
    (safeGroverBadSeeds (family.execution scope) marked check floor).card*(max (Fintype.card α) floor+1)^family.cExp≤
      @Fintype.card (family.seed scope) (family.seedFin scope) := by
  letI:=family.seedFin scope
  letI:=(family.execution scope).seedFin
  by_cases hm : ∃ x,marked x=true
  · have hp : ∃ i : Fin (Fintype.card α),marked ((Fintype.equivFin α).symm i)=true := by
      obtain ⟨x,hx⟩:=hm
      exact ⟨Fintype.equivFin α x,by simpa only [Equiv.symm_apply_apply] using hx⟩
    have hh:=family.execution_finds_supported scope
        (fun i=>marked ((Fintype.equivFin α).symm i)) check floor h hp
    refine le_trans (Nat.mul_le_mul_right _ ?_) hh
    apply Finset.card_le_card
    intro ρ hρ
    simp_all [safeGroverBadSeeds, hm, operationalSgsFind]
  · have he : safeGroverBadSeeds (family.execution scope) marked check floor=∅ := by
      ext ρ
      simp [safeGroverBadSeeds,hm]
    simp only [he,Finset.card_empty,zero_mul,Nat.zero_le]

/-- For a supported call with floor `n * n` and exponent at least three, the bad seed count
times `(n * n + 1)^3` is at most the total seed count. -/
theorem safeGroverBadSeeds_padded_bound (family : ScopedGroverFamily) (scope : SearchCallScope)
    {α : Type} [Fintype α] (marked : α → Bool) (n check : ℕ) (hc : 3≤ family.cExp)
    (h : scope.contains (Fintype.card α) check (n*n)) :
    (safeGroverBadSeeds (family.execution scope) marked check (n*n)).card*(n*n+1)^3≤
      @Fintype.card (family.seed scope) (family.seedFin scope) := by
  have hbase : n*n+1≤ max (Fintype.card α) (n*n)+1 := Nat.add_le_add_right (Nat.le_max_right _ _) 1
  have hp : (n*n+1)^3≤(max (Fintype.card α) (n*n)+1)^family.cExp :=
    (Nat.pow_le_pow_left hbase 3).trans (Nat.pow_le_pow_right (by omega) hc)
  exact (Nat.mul_le_mul_left _ hp).trans
      (safeGroverBadSeeds_source_bound family scope marked check (n*n) h)

/-- Under the scope and exponent assumptions, the number of vertex seed tapes with a bad
preparation call times `(n * n + 1)^3` is at most `n` times the total tape count. -/
theorem preparation_bad_calls_card {n : ℕ} (G : UGraph n) (family : ScopedGroverFamily) (scope : SearchCallScope) (hc : 3≤ family.cExp)
    (hscope : scope.contains (n*n) 2 (n*n))
    (vs : List (Fin n)) :
    let sgs:=family.execution scope
    letI:=sgs.seedFin
    (Finset.univ.filter (fun t : Fin n → sgs.seed=>¬preparationCallsGood G sgs t vs)).card*(n*n+1)^3≤
      n*Fintype.card (Fin n → sgs.seed) := by
  let sgs:=family.execution scope
  letI:=sgs.seedFin
  letI:=sgs.seedNe
  let B : Fin n → Finset (Fin n → sgs.seed) :=
      fun v=>Finset.univ.filter (fun t=>t v∈safeGroverBadSeeds sgs (neighborhoodMarked G v) 2 (n*n))
  have hs : Finset.univ.filter (fun t : Fin n → sgs.seed=>¬preparationCallsGood G sgs t vs)⊆Finset.univ.biUnion B := by
    intro t ht
    have hh:= (Finset.mem_filter.mp ht).2
    unfold preparationCallsGood at hh
    push Not at hh
    obtain ⟨v,_,hm,hr⟩:=hh
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      simp only [safeGroverBadSeeds,Finset.mem_filter,Finset.mem_univ,true_and];exact ⟨hm,hr⟩⟩⟩
  have hB : ∀ v,(B v).card*(n*n+1)^3≤ Fintype.card (Fin n → sgs.seed) := by
    intro v
    have he :=
        function_coordinate_event_card v
        (fun ρ=>ρ∈safeGroverBadSeeds sgs (neighborhoodMarked G v) 2 (n*n))
    have hseed : (Finset.univ.filter (fun ρ : sgs.seed=>ρ∈safeGroverBadSeeds sgs (neighborhoodMarked G v) 2 (n*n)))=
        safeGroverBadSeeds sgs (neighborhoodMarked G v) 2 (n*n) := by ext ρ;simp
    have hfull : Fintype.card (Fin n → sgs.seed)=Fintype.card sgs.seed*Fintype.card ({j : Fin n //j≠v} → sgs.seed) :=
      (Fintype.card_congr (Equiv.funSplitAt v sgs.seed)).trans (Fintype.card_prod _ _)
    change (B v).card=_ at he
    rw [hseed] at he
    have hb:=Nat.mul_le_mul_right (Fintype.card ({j : Fin n //j≠v} → sgs.seed))
      (safeGroverBadSeeds_padded_bound family scope (neighborhoodMarked G v) n 2 hc (by simpa only [Fintype.card_prod,Fintype.card_fin] using hscope))
    change (safeGroverBadSeeds sgs (neighborhoodMarked G v) 2 (n*n)).card*(n*n+1)^3*Fintype.card
        ({j : Fin n //j≠v}→sgs.seed)≤Fintype.card sgs.seed*Fintype.card
        ({j : Fin n //j≠v}→sgs.seed) at hb
    rw [he,hfull]
    nlinarith
  have hcard:=Nat.mul_le_mul_right ((n*n+1)^3)
      ((Finset.card_le_card hs).trans Finset.card_biUnion_le)
  have hsum : (∑ v,(B v).card)*(n*n+1)^3≤ n*Fintype.card (Fin n → sgs.seed) := by
    rw [Finset.sum_mul]
    apply (Finset.sum_le_sum (fun v _=>hB v)).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  exact hcard.trans hsum
end Qatlib.Concepts.WalkSearch.MainResults
