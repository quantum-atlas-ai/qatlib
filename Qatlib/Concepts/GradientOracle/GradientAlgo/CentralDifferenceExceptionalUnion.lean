/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Union bound for exceptional degrees

This module bounds a finite exceptional set covered by degree-indexed bad sets with
geometrically decreasing cardinalities. The estimate collects high-degree errors in the
central-difference analysis associated with [GilyenArunachalamWiebe2019].

## Main statements

* `centralDiff_exceptional_union`: bounds `q * (1/16)^k` for degrees starting at least at three
  give a total exceptional count at most `q/1000`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

/-- If an exceptional predicate is covered by degree-indexed sets of cardinality at most
`q*(1/16)^k` for `k ≥ N ≥ 3`, its cardinality is at most `q/1000`. -/
theorem centralDiff_exceptional_union {α : Type*} [Fintype α]
    (E : α → Prop) (B : ℕ → α → Prop) (N : ℕ) (hN : 3≤N)
    (q : ℝ) (hq : 0≤q)
    (hcount : ∀ k : ℕ,N≤k → ((Finset.univ.filter (B k)).card : ℝ)≤q*(1/16 : ℝ)^k)
    (hcover : ∀ a,E a → ∃ k,N≤k ∧ B k a) :
    ((Finset.univ.filter E).card : ℝ)≤q/1000 := by
  classical
  let w := fun a : α => if h : E a then (hcover a h).choose else N
  have hw (a : α) (ha : E a) : N≤w a ∧ B (w a) a := by
    simpa only [w,dif_pos ha] using (hcover a ha).choose_spec
  let K := Finset.univ.sup w
  let U := (Finset.range (K+1)).biUnion (fun j => Finset.univ.filter (B (N+j)))
  have hsub : Finset.univ.filter E⊆U := by
    intro a ha
    have he := (Finset.mem_filter.mp ha).2
    have h := hw a he
    have hk : w a≤K := Finset.le_sup (Finset.mem_univ a)
    apply Finset.mem_biUnion.mpr
    refine ⟨w a-N,Finset.mem_range.mpr (by omega),?_⟩
    rw [Nat.add_sub_of_le h.1]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩
  have hc : ((Finset.univ.filter E).card : ℝ)≤
      ∑ j∈Finset.range (K+1),((Finset.univ.filter (B (N+j))).card : ℝ) := by
    have h := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
    exact_mod_cast h
  have hs : ((Finset.univ.filter E).card : ℝ)≤
      q*(1/16 : ℝ)^N*(∑ j∈Finset.range (K+1),(1/16 : ℝ)^j) := by
    apply hc.trans
    calc
      _ ≤ ∑ j∈Finset.range (K+1),q*(1/16 : ℝ)^(N+j) :=
        Finset.sum_le_sum (fun j _ => hcount (N+j) (by omega))
      _ = _ := by simp only [pow_add,← Finset.mul_sum,mul_assoc]
  have hgeo : (∑ j∈Finset.range (K+1),(1/16 : ℝ)^j)≤16/15 := by
    have hg : Summable (fun j : ℕ => (1/16 : ℝ)^j) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h := hg.sum_le_tsum (Finset.range (K+1)) (fun _ _ => by positivity)
    rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ)≤1/16) (by norm_num : (1/16 : ℝ)<1)] at h
    norm_num at h
    exact h
  have hp : (1/16 : ℝ)^N≤(1/16 : ℝ)^3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have hstep :=
      mul_le_mul_of_nonneg_left hgeo (mul_nonneg hq (by positivity : (0 : ℝ)≤(1/16 : ℝ)^N))
  have hstep2 := mul_le_mul_of_nonneg_left hp hq
  norm_num at hstep2
  nlinarith
end Qatlib.Concepts.GradientOracle.GradientAlgo
