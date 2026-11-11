/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedWeightedChain

/-!
# Coefficient lists and sign partitions for deferred LCU

This module supplies the finite-list bookkeeping for the corrected signed LCU construction
associated with Theorem 3 of [ChildsWiebe2012]. It relates `cwChainList` to coefficient sums and
weighted matrix sums, and verifies positivity, unitary payloads, and distinct ancilla positions
under the corresponding hypotheses.

`cwPositiveTerms` and `cwNegativeTerms` split the coefficient indices by sign. Their masses add
to the total absolute coefficient mass, and subtracting their weighted matrix sums recovers the
original signed sum.

## Main statements

- `cwChainList_weight` and `cwChainList_weighted` identify the list totals with finite-set sums.
* `cwChainList_bits_pairwise`, `cwChainList_bit_range`, and `cwChainList_tail_fresh` control the
  assigned ancilla positions.
- `cw_sign_cards` counts the two sign classes when every coefficient is nonzero.
* `cw_weight_sum` and `cw_signed_weighted` recover the total absolute mass and signed matrix
  sum.

## References

- [Childs and Wiebe, 2012][ChildsWiebe2012], Theorem 3.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- Mapping a function of the weight and matrix payload over `cwChainList` gives the
corresponding map over `S.toList`, independently of the assigned ancilla positions. -/
theorem cwChainList_map_payload {A : Type*} (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (f : ℝ×Matrix I I ℂ→A) :
    (cwChainList k off wt U S).map (fun t=>f t.2)=S.toList.map (fun q=>f (wt q,U q)) := by
  unfold cwChainList
  simp only [List.mapIdx_eq_zipIdx_map,List.map_map]
  conv_rhs => rw [← List.zipIdx_map_fst 0 S.toList,List.map_map]
  rfl

omit [Fintype I] [DecidableEq I] in

/-- The total weight of `cwChainList` is the sum of `wt q` over `S`. -/
theorem cwChainList_weight (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) :
    lcuListWeight (cwChainList k off wt U S)=∑ q∈S,wt q := by
  unfold lcuListWeight
  rw [cwChainList_map_payload]
  simp only [Finset.sum_map_toList]

omit [Fintype I] [DecidableEq I] in

/-- The weighted matrix sum of `cwChainList` is the sum of `wt q • U q` over `S`. -/
theorem cwChainList_weighted (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) :
    lcuListWeighted (cwChainList k off wt U S)=∑ q∈S,wt q • U q := by
  unfold lcuListWeighted
  rw [cwChainList_map_payload k off wt U S (fun p=>p.1 • p.2)]
  simp only [Finset.sum_map_toList]

omit [Fintype I] [DecidableEq I] in

/-- A nonempty index set produces a nonempty chain list. -/
theorem cwChainList_nonempty (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (hS : S.Nonempty) :
    cwChainList k off wt U S≠[] := by
  have hlen : 0<(cwChainList k off wt U S).length := by
    simpa [cwChainList] using Finset.card_pos.mpr hS
  exact List.ne_nil_of_length_pos hlen

omit [Fintype I] [DecidableEq I] in

/-- If every weight indexed by `S` is positive, every weight appearing in its chain list is
positive. -/
theorem cwChainList_positive (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (hwt : ∀ q∈S,0<wt q) :
    ∀ t∈cwChainList k off wt U S,0<t.2.1 := by
  intro t ht
  obtain ⟨j,hj,he⟩ := List.exists_of_mem_mapIdx (by simpa only [cwChainList] using ht)
  rw [← he]
  have hq : S.toList[j]∈S.toList := List.getElem_mem hj
  exact hwt _ (by simpa only [Finset.mem_toList] using hq)

/-- If all system matrices `U q` are unitary, every matrix payload in the chain list is unitary. -/
theorem cwChainList_unitaries (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ) :
    ∀ t∈cwChainList k off wt U S,t.2.2∈Matrix.unitaryGroup I ℂ := by
  intro t ht
  obtain ⟨j,hj,he⟩ := List.exists_of_mem_mapIdx (by simpa only [cwChainList] using ht)
  rw [← he]
  exact hU _

omit [Fintype I] [DecidableEq I] in

/-- The chain list has pairwise distinct ancilla positions when `off + S.card ≤ k + 1`, so the
assigned positions do not wrap around the register. -/
theorem cwChainList_bits_pairwise (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (hbound : off+S.card≤k+1) :
    (cwChainList k off wt U S).Pairwise (fun a b=>a.1≠b.1) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i<S.card := by simpa [cwChainList] using hi
  have hj' : j<S.card := by simpa [cwChainList] using hj
  simp only [cwChainList,List.getElem_mapIdx]
  intro he
  have hv := congrArg Fin.val he
  have hip : off+i<k+1 := by omega
  have hjp : off+j<k+1 := by omega
  simp only [Nat.mod_eq_of_lt hip,Nat.mod_eq_of_lt hjp] at hv
  omega
/-- The finite set of indices whose coefficients are strictly positive. -/
def cwPositiveTerms (k : ℕ) (c : Fin (k+1)→ℝ) := Finset.univ.filter (fun q=>0<c q)
/-- The finite set of indices whose coefficients are strictly negative. -/
def cwNegativeTerms (k : ℕ) (c : Fin (k+1)→ℝ) := Finset.univ.filter (fun q=>c q<0)
/-- The sum of the positive coefficients over `cwPositiveTerms`. -/
def cwPositiveWeight (k : ℕ) (c : Fin (k+1)→ℝ) : ℝ := ∑ q∈cwPositiveTerms k c,c q
/-- The sum of the absolute values of the negative coefficients over `cwNegativeTerms`. -/
def cwNegativeWeight (k : ℕ) (c : Fin (k+1)→ℝ) : ℝ := ∑ q∈cwNegativeTerms k c,|c q|

omit [Fintype I] [DecidableEq I] in

/-- The positive index set is nonempty whenever a positive coefficient exists. -/
theorem cw_positive_nonempty (k : ℕ) (c : Fin (k+1)→ℝ) (h : ∃ q,0<c q) :
    (cwPositiveTerms k c).Nonempty := by
  obtain ⟨q,hq⟩ := h
  exact ⟨q,by simp [cwPositiveTerms,hq]⟩

omit [Fintype I] [DecidableEq I] in

/-- The negative index set is nonempty whenever a negative coefficient exists. -/
theorem cw_negative_nonempty (k : ℕ) (c : Fin (k+1)→ℝ) (h : ∃ q,c q<0) :
    (cwNegativeTerms k c).Nonempty := by
  obtain ⟨q,hq⟩ := h
  exact ⟨q,by simp [cwNegativeTerms,hq]⟩

omit [Fintype I] [DecidableEq I] in

/-- The positive coefficient mass is strictly positive whenever a positive coefficient exists. -/
theorem cw_positive_weight_pos (k : ℕ) (c : Fin (k+1)→ℝ) (h : ∃ q,0<c q) :
    0<cwPositiveWeight k c := by
  apply Finset.sum_pos
  · intro q hq; exact (Finset.mem_filter.mp hq).2
  · exact cw_positive_nonempty k c h

omit [Fintype I] [DecidableEq I] in

/-- The negative absolute coefficient mass is strictly positive whenever a negative coefficient
exists. -/
theorem cw_negative_weight_pos (k : ℕ) (c : Fin (k+1)→ℝ) (h : ∃ q,c q<0) :
    0<cwNegativeWeight k c := by
  apply Finset.sum_pos
  · intro q hq; exact abs_pos.mpr (ne_of_lt ((Finset.mem_filter.mp hq).2))
  · exact cw_negative_nonempty k c h

omit [Fintype I] [DecidableEq I] in

/-- If every coefficient is nonzero, the positive and negative index-set cardinalities add to `k
+ 1`. -/
theorem cw_sign_cards (k : ℕ) (c : Fin (k+1)→ℝ) (hc : ∀ q,c q≠0) :
    (cwPositiveTerms k c).card+(cwNegativeTerms k c).card=k+1 := by
  have hn : cwNegativeTerms k c=Finset.univ.filter (fun q : Fin (k+1)=>¬0<c q) := by
    ext q
    simp only [cwNegativeTerms,Finset.mem_filter,Finset.mem_univ,true_and]
    have hh := hc q
    constructor
    · intro h; exact not_lt.mpr h.le
    · intro h
      have hle : c q≤0 := le_of_not_gt h
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exact False.elim (hh heq)
  rw [hn]
  exact (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun q : Fin (k+1)=>0<c q)).trans
    (Fintype.card_fin (k+1))

omit [Fintype I] [DecidableEq I] in

/-- The positive mass plus the negative absolute mass equals the sum of all absolute coefficient
values. -/
theorem cw_weight_sum (k : ℕ) (c : Fin (k+1)→ℝ) :
    cwPositiveWeight k c+cwNegativeWeight k c=∑ q,|c q| := by
  unfold cwPositiveWeight cwNegativeWeight cwPositiveTerms cwNegativeTerms
  rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : 0<c q
  · simp [hp,not_lt.mpr hp.le,abs_of_pos hp]
  · by_cases hn : c q<0
    · simp [hp,hn]
    · have hz : c q=0 := by linarith
      simp [hz]

omit [Fintype I] [DecidableEq I] in

/-- Subtracting the absolute-weight negative matrix sum from the positive matrix sum recovers `∑
q, c q • U q`. -/
theorem cw_signed_weighted (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :
    (∑ q∈cwPositiveTerms k c,c q • U q)-(∑ q∈cwNegativeTerms k c,|c q| • U q)=∑ q,c q • U q := by
  unfold cwPositiveTerms cwNegativeTerms
  rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : 0<c q
  · simp [hp,not_lt.mpr hp.le]
  · by_cases hn : c q<0
    · simp [hp,hn,abs_of_neg hn,neg_smul]
    · have hz : c q=0 := by linarith
      simp [hz]

omit [Fintype I] [DecidableEq I] in

/-- Under `off + S.card ≤ k + 1`, every chain-list ancilla position lies in the interval from
`off` inclusive to `off + S.card` exclusive. -/
theorem cwChainList_bit_range (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (hbound : off+S.card≤k+1) :
    ∀ t∈cwChainList k off wt U S,off≤t.1.val ∧ t.1.val<off+S.card := by
  intro t ht
  obtain ⟨j,hj,he⟩ := List.exists_of_mem_mapIdx (by simpa only [cwChainList] using ht)
  have hj' : j<S.card := by simpa using hj
  rw [← he]
  have hh : off+j<k+1 := by omega
  simp only [Nat.mod_eq_of_lt hh]
  omega

omit [Fintype I] [DecidableEq I] in

/-- For nonempty `S`, the first chain-list entry is assigned ancilla position `off % (k + 1)`. -/
theorem cwChainList_head_bit (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (hS : S.Nonempty) :
    ((cwChainList k off wt U S).head (cwChainList_nonempty k off wt U S hS)).1=
      ⟨off%(k+1),Nat.mod_lt _ (Nat.succ_pos k)⟩ := by
  simp [cwChainList]

omit [Fintype I] [DecidableEq I] in

/-- For nonempty `S` satisfying the position bound, no entry of the chain-list tail uses the
head's ancilla position `off % (k + 1)`. -/
theorem cwChainList_tail_fresh (k off : ℕ) (wt : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (S : Finset (Fin (k+1))) (hS : S.Nonempty)
    (hbound : off+S.card≤k+1) :
    ∀ t∈(cwChainList k off wt U S).tail,
      (⟨off%(k+1),Nat.mod_lt _ (Nat.succ_pos k)⟩ : Fin (k+1))≠t.1 := by
  have hpair := cwChainList_bits_pairwise k off wt U S hbound
  have hhead := cwChainList_head_bit k off wt U S hS
  have hne := cwChainList_nonempty k off wt U S hS
  cases he : cwChainList k off wt U S with
  | nil => exact False.elim (hne he)
  | cons u L =>
    have hpair' : (u::L).Pairwise (fun a b=>a.1≠b.1) := he ▸ hpair
    have hhead' : u.1=⟨off%(k+1),Nat.mod_lt _ (Nat.succ_pos k)⟩ := by
      simpa only [he,List.head_cons] using hhead
    intro t ht
    rw [← hhead']
    exact (List.pairwise_cons.mp hpair').1 t ht

end Qatlib.Papers.HamLCUSim12.LCUDeferred
