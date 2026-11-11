/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind16.MainResults.CostModel

set_option backward.isDefEq.respectTransparency false

/-!
# Composition of learning graphs: the OR construction (Lemma 4.1)

Carette--Laurière--Magniez, fixed arXiv:1609.07786v2, Section 4.1. Given learning graphs
`G_1, ..., G_n` for `f_1, ..., f_n`, the OR construction connects a fresh root to the roots of all
components, rescales the weights of component `i` by `c¹(G_i)/k` and routes the flow of a positive
instance uniformly to `k` positive components.

* `orGraph`: the cost data of the resulting learning graph.
* `orGraph_negCost`: `C⁰(G, z) = (1/k) ∑_i C⁰(G_i, z) C¹(G_i)`, which is
  `(n/k) · Exp_i[C⁰(G_i, z) C¹(G_i)]`.
* `orGraph_posCost`: `C¹(G, y) = 1`.
* `orRouting_exists`: the hypothesis "at least `k` of the `f_i` are true" provides the `k` routed
  components.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TriangleFind16.MainResults

variable {n : ℕ} {ι : Fin n → Type} [∀ i, Fintype (ι i)]

/-- The OR construction of Lemma 4.1: the disjoint union of the components `G_i`, the weights of
component `i` rescaled by `c¹(G_i)/k`, and the flow routed to the `k` components of `S`. -/
def orGraph (G : ∀ i : Fin n, FlowData (ι i)) (k : ℕ) (S : Finset (Fin n)) :
    FlowData (Σ i, ι i) where
  w0 x := (G x.1).posCost / (k : ℝ) * (G x.1).w0 x.2
  w1 x := (G x.1).posCost / (k : ℝ) * (G x.1).w1 x.2
  p x := (if x.1 ∈ S then 1 / (k : ℝ) else 0) * (G x.1).p x.2

/-- Lemma 4.1, negative part: `C⁰(G, z) = (1/k) ∑_i C⁰(G_i, z) C¹(G_i)`. -/
theorem orGraph_negCost (G : ∀ i : Fin n, FlowData (ι i)) (k : ℕ) (S : Finset (Fin n)) :
    (orGraph G k S).negCost
      = (1 / (k : ℝ)) * ∑ i, (G i).negCost * (G i).posCost := by
  have hstep : ∀ i : Fin n, ∑ j, (G i).posCost / (k : ℝ) * (G i).w0 j
      = (1 / (k : ℝ)) * ((G i).negCost * (G i).posCost) := by
    intro i
    rw [show (G i).negCost = ∑ j, (G i).w0 j from rfl, ← Finset.mul_sum]
    ring
  calc (orGraph G k S).negCost
      = ∑ i, ∑ j, (G i).posCost / (k : ℝ) * (G i).w0 j := by
        change ∑ x : Sigma ι, (G x.1).posCost / (k : ℝ) * (G x.1).w0 x.2 = _
        rw [Fintype.sum_sigma]
    _ = ∑ i, (1 / (k : ℝ)) * ((G i).negCost * (G i).posCost) := by
        exact Finset.sum_congr rfl fun i _ => hstep i
    _ = (1 / (k : ℝ)) * ∑ i, (G i).negCost * (G i).posCost := by
        rw [Finset.mul_sum]

/-- Lemma 4.1, with the paper's averaging notation:
`C⁰(G, z) = (n/k) · Exp_i[C⁰(G_i, z) C¹(G_i)]`. -/
theorem orGraph_negCost_expect (G : ∀ i : Fin n, FlowData (ι i)) (k : ℕ) (hn : 0 < n)
    (S : Finset (Fin n)) :
    (orGraph G k S).negCost
      = (n : ℝ) / (k : ℝ) * (𝔼 i, (G i).negCost * (G i).posCost) := by
  rw [orGraph_negCost, Fintype.expect_eq_sum_div_card]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Fintype.card_fin]
  field_simp

/-- Lemma 4.1, positive part: if every component has positive complexity and the flow is routed
to exactly `k` components, then the positive complexity is `1`. -/
theorem orGraph_posCost (G : ∀ i : Fin n, FlowData (ι i)) (k : ℕ) (S : Finset (Fin n))
    (hk : 0 < k) (hScard : S.card = k) (hpos : ∀ i, 0 < (G i).posCost)
    (hw1 : ∀ i j, (G i).w1 j ≠ 0) :
    (orGraph G k S).posCost = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  change ∑ x : Sigma ι, ((if x.1 ∈ S then 1 / (k : ℝ) else 0) * (G x.1).p x.2) ^ 2
      / ((G x.1).posCost / (k : ℝ) * (G x.1).w1 x.2) = 1
  rw [Fintype.sum_sigma' (f := fun i j =>
    ((if i ∈ S then 1 / (k : ℝ) else 0) * (G i).p j) ^ 2
      / ((G i).posCost / (k : ℝ) * (G i).w1 j))]
  have hcomp : ∀ i : Fin n,
      ∑ j, ((if i ∈ S then 1 / (k : ℝ) else 0) * (G i).p j) ^ 2
          / ((G i).posCost / (k : ℝ) * (G i).w1 j)
        = (if i ∈ S then 1 / (k : ℝ) else 0) ^ 2 * (k : ℝ) := by
    intro i
    have hterm : ∀ j : ι i,
        ((if i ∈ S then 1 / (k : ℝ) else 0) * (G i).p j) ^ 2
            / ((G i).posCost / (k : ℝ) * (G i).w1 j)
          = (if i ∈ S then 1 / (k : ℝ) else 0) ^ 2 * (k : ℝ) / (G i).posCost
              * ((G i).p j ^ 2 / (G i).w1 j) := by
      intro j
      have hc : (0 : ℝ) < (G i).posCost := hpos i
      have hw : (G i).w1 j ≠ 0 := hw1 i j
      field_simp
      try ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
    have hinner : ∑ j, (G i).p j ^ 2 / (G i).w1 j = (G i).posCost := rfl
    rw [hinner]
    have hc : (G i).posCost ≠ 0 := (hpos i).ne'
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => hcomp i)]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i : Fin n => i ∈ S)
    (f := fun i => (if i ∈ S then 1 / (k : ℝ) else 0) ^ 2 * (k : ℝ))]
  have hzero : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i ∈ S),
      (if i ∈ S then 1 / (k : ℝ) else 0) ^ 2 * (k : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : ¬ i ∈ S := by simpa using hi
    rw [if_neg hi']
    ring
  have hone : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∈ S),
      (if i ∈ S then 1 / (k : ℝ) else 0) ^ 2 * (k : ℝ) = 1 := by
    have hstep : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i ∈ S),
        (if i ∈ S then 1 / (k : ℝ) else 0) ^ 2 * (k : ℝ) = 1 / (k : ℝ) := by
      intro i hi
      have hi' : i ∈ S := by simpa using hi
      rw [if_pos hi']
      field_simp
      try ring
    rw [Finset.sum_congr rfl hstep]
    have hcard : (Finset.univ.filter (fun i : Fin n => i ∈ S)).card = k := by
      rw [← hScard]
      refine congrArg Finset.card ?_
      ext i
      simp
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  rw [hone, hzero, add_zero]

/-- The hypothesis of Lemma 4.1: if at least `k` components are positive on an input, then there
is a set of exactly `k` of them to which the flow can be routed. -/
theorem orRouting_exists (s : Finset (Fin n)) (k : ℕ) (h : k ≤ s.card) :
    ∃ S ⊆ s, S.card = k :=
  Finset.exists_subset_card_eq h

end Qatlib.Papers.TriangleFind16.MainResults
