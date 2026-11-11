/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.VertexSamplingStat
import Qatlib.Concepts.WalkSearch.Primitives.SamplingTapeBounds

/-!
# Vertex sampling with replacement

`sampledSurvivors` contains the pairs whose common neighbors are missed by a vertex-sampling
tape. The module bounds each bad pair's tapes and applies a finite union bound to prove
`lemma3Sampling_withReplacement` and its `VertexSampling` interface.

This sampling step prepares graph instances for subset-search reductions [ChildsEisenberg2003].

## Main statements

* `badPairTapes_card_bound`: an inverse-fourth-power normalized per-pair bound.
* `lemma3Sampling_withReplacement`: the sampling contract.
* `vertexSampling_answer`: the `VertexSampling` proposition.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n k : ℕ}

/-- For an undirected graph, `b` is a neighbor of `a` exactly when `(a, b)` belongs to its edge
set. -/
theorem mem_graph_nbr_iff (G : UGraph n) (a b : Fin n) :
    b∈nbrOf G.edges a ↔ (a,b)∈G.edges := by
  rw [mem_nbrOf_iff]
  exact ⟨fun h=>h.elim id (G.symm b a),Or.inl⟩

/-- The ordered vertex pairs for which no sampled vertex is a common neighbor. -/
def sampledSurvivors (G : UGraph n) (s : Fin k→Fin n) : Finset (Fin n×Fin n) :=
  Finset.univ.filter fun p=>∀ v∈Finset.univ.image s,(p.1,v)∉G.edges ∨ (p.2,v)∉G.edges

/-- A pair survives the sample exactly when every tape entry lies outside the intersection of
its endpoint neighborhoods. -/
theorem mem_sampledSurvivors_iff (G : UGraph n) (s : Fin k→Fin n) (p : Fin n×Fin n) :
    p∈sampledSurvivors G s ↔ ∀ i,s i∉nbrOf G.edges p.1 ∩ nbrOf G.edges p.2 := by
  simp only [sampledSurvivors,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_inter,mem_graph_nbr_iff,not_and_or]
  constructor
  · intro h i
    exact h (s i) ⟨i,rfl⟩
  · rintro h v ⟨i,rfl⟩
    exact h i

/-- The sampling tapes on which a pair survives despite having more than `τ` common neighbors. -/
def badPairTapes (G : UGraph n) (τ : ℕ) (p : Fin n×Fin n) : Finset (Fin k→Fin n) :=
  Finset.univ.filter fun s=>τ<tOf G.edges p.1 p.2 ∧ p∈sampledSurvivors G s

/-- Under the sampling-size assumptions, each pair's bad-tape count is at most `n ^ k / n ^ 4`
over the reals. -/
theorem badPairTapes_card_bound (G : UGraph n) (ε : ℝ) (hn : 0<n) (hε : 0<ε)
    (hk : 4*(n:ℝ)^ε*(Nat.log 2 n+1:ℕ)≤(k:ℝ)) (p : Fin n×Fin n) :
    ((badPairTapes (k:=k) G (Nat.floor ((n:ℝ)^(1-ε))) p).card:ℝ) ≤
      (n:ℝ)^k/(n:ℝ)^4 := by
  by_cases hl : Nat.floor ((n:ℝ)^(1-ε))<tOf G.edges p.1 p.2
  · have heq : badPairTapes (k:=k) G (Nat.floor ((n:ℝ)^(1-ε))) p =
        Finset.univ.filter (fun s : Fin k→Fin n=>∀ i,s i∉nbrOf G.edges p.1 ∩ nbrOf G.edges p.2) := by
      ext s
      simp only [badPairTapes,Finset.mem_filter,Finset.mem_univ,true_and,hl,
        mem_sampledSurvivors_iff]
    rw [heq,avoiding_tape_card]
    rw [Nat.cast_pow]
    apply source_sampling_avoid_bound n _ k ε hn hε
    · exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    · exact ((Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg n) _)).mp hl).le
    · exact hk
  · have heq : badPairTapes (k:=k) G (Nat.floor ((n:ℝ)^(1-ε))) p=∅ := by
      ext s
      simp only [badPairTapes,Finset.mem_filter,Finset.mem_univ,true_and,hl,false_and,Finset.notMem_empty]
    rw [heq,Finset.card_empty,Nat.cast_zero]
    positivity

/-- Every tape whose survivors are not all thin belongs to the union of the bad-pair tape sets. -/
theorem bad_sample_subset_union (G : UGraph n) (τ : ℕ) :
    (Finset.univ.filter (fun s : Fin k→Fin n=>¬sampledSurvivors G s⊆thinPairs G.edges τ)) ⊆
      Finset.univ.biUnion (badPairTapes (k:=k) G τ) := by
  intro s hs
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hs
  rw [Finset.subset_iff] at hs
  push Not at hs
  obtain ⟨p,hp,hthin⟩:=hs
  have ht : τ<tOf G.edges p.1 p.2 := by
    simpa only [thinPairs,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hthin
  exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,by simp only [badPairTapes,Finset.mem_filter,Finset.mem_univ,true_and];exact ⟨ht,hp⟩⟩

/-- Establishes `lemma3Sampling`, the with-replacement vertex-sampling contract. -/
theorem lemma3Sampling_withReplacement : lemma3Sampling := by
  intro n ε hn hε _hε1 k _hkpos G
  change ((Finset.univ.filter (fun s : Fin k→Fin n=>¬sampledSurvivors G s⊆thinPairs G.edges (Nat.floor ((n:ℝ)^(1-ε))))).card:ℕ)*n < _
  let bad :=
      Finset.univ.filter
      (fun s : Fin k→Fin n=>¬sampledSurvivors G s⊆thinPairs G.edges (Nat.floor ((n:ℝ)^(1-ε))))
  have hk : 4*(n:ℝ)^ε*(Nat.log 2 n+1:ℕ)≤(k:ℝ) := by
    simpa only [k,Nat.cast_add,Nat.cast_one] using Nat.le_ceil (4*(n:ℝ)^ε*(Nat.log 2 n+1))
  have hb : (bad.card:ℝ)≤(n:ℝ)^2*((n:ℝ)^k/(n:ℝ)^4) := by
    have hc :=
        (Finset.card_le_card (bad_sample_subset_union (k:=k) G (Nat.floor ((n:ℝ)^(1-ε))))).trans Finset.card_biUnion_le
    have hcR : (bad.card:ℝ)≤∑ p : Fin n×Fin n,((badPairTapes (k:=k) G (Nat.floor ((n:ℝ)^(1-ε))) p).card:ℝ) := by
      exact_mod_cast hc
    apply hcR.trans
    calc
      _ ≤ ∑ _p : Fin n×Fin n,(n:ℝ)^k/(n:ℝ)^4 := Finset.sum_le_sum (fun p _=>badPairTapes_card_bound G ε hn hε hk p)
      _ = (n:ℝ)^2*((n:ℝ)^k/(n:ℝ)^4) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,pow_two]
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_fin]
  by_cases h1 : n=1
  · subst n
    have hbad : bad=∅ := by
      ext s
      simp only [bad,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty]
      simp only [iff_false,not_not]
      intro p _
      simp only [thinPairs,Finset.mem_filter,Finset.mem_univ,true_and,Nat.cast_one,Real.one_rpow,Nat.floor_one]
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin 1)
    change bad.card*1<1^k
    rw [hbad,Finset.card_empty,zero_mul,one_pow]
    norm_num
  · have hn1 : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_right hb hnR.le
    have heq : (n:ℝ)^2*((n:ℝ)^k/(n:ℝ)^4)*(n:ℝ)=(n:ℝ)^k/(n:ℝ) := by field_simp
    rw [heq] at hmul
    have hlt : (bad.card:ℝ)*(n:ℝ)<(n:ℝ)^k := hmul.trans_lt (div_lt_self (pow_pos hnR k) hn1)
    exact_mod_cast hlt

/-- Establishes `VertexSampling` using the with-replacement sampling theorem. -/
theorem vertexSampling_answer : VertexSampling := lemma3Sampling_withReplacement
end Qatlib.Concepts.WalkSearch.Primitives
