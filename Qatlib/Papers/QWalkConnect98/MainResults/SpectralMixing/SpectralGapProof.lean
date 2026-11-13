/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing.MixingContraction
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# An elementary component spectral-gap bound

`edgeEnergy` sums squared differences over ordered adjacent vertex pairs. Path estimates and a
finite-range variance bound give a component Poincaré inequality, which bounds the quadratic
form of `walkM` on component-supported vectors summing to zero.

Polarization and a bilinear estimate yield Euclidean contraction with factor `elemRho`.
Comparing this factor with the required bound proves `spectralGap_of_regular` for regular graphs
of degree at least two. These results support the connectivity analysis in [Watrous1998].

## Main statements

* `poincare_edgeEnergy`: bound the squared norm by component size and edge energy.
* `walkM_contraction`: derive the Euclidean contraction with factor `elemRho`.
* `spectralGap_of_regular`: establish `SpectralGap` from regularity and the degree bound.

## References

* [Watrous, 1998][Watrous1998]
-/

namespace Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing

open Finset
open Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator
open scoped BigOperators Matrix

set_option autoImplicit false
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The contraction coefficient `1 - 2 * walkB d / (compSize G u * (compSize G u - 1))`, with
component sizes viewed as real numbers. -/
def elemRho (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (u : V) : ℝ :=
  1 - 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1))

/-- The sum of `(x u - x v) ^ 2` over ordered adjacent vertex pairs. -/
def edgeEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then (x u - x v) ^ 2 else 0

omit [DecidableEq V] in

/-- The edge energy is nonnegative. -/
theorem edgeEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    0 ≤ edgeEnergy G x := by
  unfold edgeEnergy
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
    split_ifs <;> positivity

omit [DecidableEq V] in

/-- The sum of the adjacency indicators in a row is the degree of its vertex. -/
theorem sum_ite_adj_row (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (∑ v, (if G.Adj u v then (1 : ℝ) else 0)) = ((G.neighborFinset u).card : ℝ) := by
  have hfilter : (Finset.univ.filter (fun v => G.Adj u v)) = G.neighborFinset u := by
    ext v
    simp [SimpleGraph.mem_neighborFinset]
  have h : (∑ v, (if G.Adj u v then (1 : ℝ) else 0)) =
      ((Finset.univ.filter (fun v => G.Adj u v)).card : ℝ) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h, hfilter]

omit [DecidableEq V] in

/-- The quadratic form of the adjacency matrix is the sum of `x u * x v` over ordered adjacent
vertex pairs. -/
theorem dotProduct_adjMatrix_self (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    x ⬝ᵥ (adjMatrix G *ᵥ x) = ∑ u, ∑ v, if G.Adj u v then x u * x v else 0 := by
  simp only [dotProduct, Matrix.mulVec, adjMatrix, Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : G.Adj u v
  · simp [hv]
  · simp [hv]

/-- The edge energy is twice the degree-weighted sum of coordinate squares minus twice the
adjacency quadratic form. -/
theorem edgeEnergy_eq (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    edgeEnergy G x =
      2 * (∑ u, x u ^ 2 * (∑ v, (if G.Adj u v then (1 : ℝ) else 0)))
        - 2 * (x ⬝ᵥ (adjMatrix G *ᵥ x)) := by
  set D : ℝ := ∑ u, x u ^ 2 * (∑ v, (if G.Adj u v then (1 : ℝ) else 0)) with hD
  have hpt : ∀ u v : V, (if G.Adj u v then (x u - x v) ^ 2 else 0) =
      ((if G.Adj u v then x u ^ 2 else 0) + (if G.Adj u v then x v ^ 2 else 0)
        - (if G.Adj u v then 2 * (x u * x v) else 0)) := by
    intro u v
    by_cases h : G.Adj u v
    · simp only [h, ite_true]; ring
    · simp only [h, ite_false]; ring
  have hA : (∑ u, ∑ v, (if G.Adj u v then x u ^ 2 else 0)) = D := by
    rw [hD]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : G.Adj u v <;> simp [h]
  have hB : (∑ u, ∑ v, (if G.Adj u v then x v ^ 2 else 0)) = D := by
    rw [hD, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : G.Adj u v
    · simp [h, h.symm]
    · have h' : ¬ G.Adj v u := fun hv => h hv.symm
      simp [h, h']
  have hC : (∑ u, ∑ v, (if G.Adj u v then 2 * (x u * x v) else 0)) =
      2 * (x ⬝ᵥ (adjMatrix G *ᵥ x)) := by
    rw [dotProduct_adjMatrix_self, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : G.Adj u v <;> simp [h]
  calc edgeEnergy G x
      = ∑ u, ∑ v, ((if G.Adj u v then x u ^ 2 else 0) + (if G.Adj u v then x v ^ 2 else 0)
          - (if G.Adj u v then 2 * (x u * x v) else 0)) := by
        unfold edgeEnergy
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hpt u v
    _ = (∑ u, ∑ v, (if G.Adj u v then x u ^ 2 else 0))
          + (∑ u, ∑ v, (if G.Adj u v then x v ^ 2 else 0))
          - (∑ u, ∑ v, (if G.Adj u v then 2 * (x u * x v) else 0)) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = D + D - 2 * (x ⬝ᵥ (adjMatrix G *ᵥ x)) := by rw [hA, hB, hC]
    _ = 2 * D - 2 * (x ⬝ᵥ (adjMatrix G *ᵥ x)) := by ring

/-- For a regular graph, the quadratic form of `walkM` equals the sum of coordinate squares
minus `walkB d / 2` times the edge energy. -/
theorem dotProduct_walkM_self (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (x : V → ℝ) :
    x ⬝ᵥ (walkM G d *ᵥ x) = (∑ u, x u ^ 2) - (walkB d / 2) * edgeEnergy G x := by
  have hM : walkM G d *ᵥ x = walkA d • x + walkB d • (adjMatrix G *ᵥ x) := by
    unfold walkM
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hM, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hself : x ⬝ᵥ x = ∑ u, x u ^ 2 := by
    simp [dotProduct, sq]
  have hdeg : (∑ u, x u ^ 2 * (∑ v, (if G.Adj u v then (1 : ℝ) else 0)))
      = d * (∑ u, x u ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [sum_ite_adj_row, hreg u]
    ring
  rw [hself, edgeEnergy_eq, hdeg]
  have h1 : walkA d + walkB d * d = 1 := walkA_add_walkB_mul d
  linear_combination (∑ u, x u ^ 2) * h1

omit [Fintype V] [DecidableEq V] in

/-- A zero-sum family bounded between `m` and `M` on a finite set has sum of squares at most the
set's cardinality times `(M - m) ^ 2 / 4`. -/
theorem sum_sq_le_card_mul_range_sq {s : Finset V} (x : V → ℝ) {m M : ℝ}
    (hm : ∀ v ∈ s, m ≤ x v) (hM : ∀ v ∈ s, x v ≤ M) (hsum : ∑ v ∈ s, x v = 0) :
    ∑ v ∈ s, x v ^ 2 ≤ (s.card : ℝ) * (M - m) ^ 2 / 4 := by
  have hterm : ∀ v ∈ s, (x v - m) * (x v - M) ≤ 0 := by
    intro v hv
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hm v hv]) (by linarith [hM v hv])
  have hsumle : ∑ v ∈ s, (x v - m) * (x v - M) ≤ 0 := Finset.sum_nonpos hterm
  have hexp : ∑ v ∈ s, (x v - m) * (x v - M)
      = (∑ v ∈ s, x v ^ 2) + (s.card : ℝ) * (m * M) := by
    have hpt : ∀ v, (x v - m) * (x v - M) = x v ^ 2 - (M + m) * x v + m * M := by
      intro v; ring
    simp only [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hquad : (∑ v ∈ s, x v ^ 2) ≤ (s.card : ℝ) * ((-m) * M) := by
    have h : (∑ v ∈ s, x v ^ 2) + (s.card : ℝ) * (m * M) ≤ 0 := by
      rw [← hexp]; exact hsumle
    nlinarith
  have hMM : (-m) * M ≤ (M - m) ^ 2 / 4 := by
    nlinarith [sq_nonneg (M + m)]
  calc ∑ v ∈ s, x v ^ 2 ≤ (s.card : ℝ) * ((-m) * M) := hquad
    _ ≤ (s.card : ℝ) * ((M - m) ^ 2 / 4) := by
        apply mul_le_mul_of_nonneg_left hMM (Nat.cast_nonneg _)
    _ = (s.card : ℝ) * (M - m) ^ 2 / 4 := by ring

omit [Fintype V] [DecidableEq V] in

/-- Every vertex selected by `getVert` along a walk is reachable from its starting vertex. -/
theorem walk_reachable_getVert {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (i : ℕ) :
    G.Reachable a (p.getVert i) := by
  induction p generalizing i with
  | nil => simp
  | cons h q ih =>
    cases i with
    | zero => simp
    | succ n =>
      rw [SimpleGraph.Walk.getVert_cons_succ]
      exact (SimpleGraph.Adj.reachable h).trans (ih n)

omit [Fintype V] [DecidableEq V] in

/-- Every vertex in the support of a walk is reachable from its starting vertex. -/
theorem walk_reachable_of_mem_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    ∀ w ∈ p.support, G.Reachable a w := by
  induction p with
  | nil =>
    intro w hw
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact SimpleGraph.Reachable.rfl
  | cons h q ih =>
    intro w hw
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact SimpleGraph.Reachable.rfl
    · exact (SimpleGraph.Adj.reachable h).trans (ih w hw)

/-- If a walk starts in the component of `u`, its finite support is contained in `compSet G u`. -/
theorem support_toFinset_subset_compSet {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (p : G.Walk a b) {u : V} (ha : G.Reachable u a) :
    p.support.toFinset ⊆ compSet G u := by
  intro w hw
  rw [List.mem_toFinset] at hw
  exact mem_compSet.mpr (ha.trans (walk_reachable_of_mem_support p w hw))

/-- A path starting in the component of `u` has length plus one at most `compSize G u`. -/
theorem length_le_compSize {G : SimpleGraph V} [DecidableRel G.Adj] {a b u : V}
    (p : G.Walk a b) (hp : p.IsPath) (ha : G.Reachable u a) :
    p.length + 1 ≤ compSize G u := by
  have hnodup : p.support.Nodup := hp.support_nodup
  have hcard : p.support.toFinset.card = p.support.length := List.toFinset_card_of_nodup hnodup
  have hle := Finset.card_le_card (support_toFinset_subset_compSet p ha)
  rw [hcard, SimpleGraph.Walk.length_support] at hle
  simpa [compSize] using hle

omit [Fintype V] [DecidableEq V] in

/-- The sum of successive coordinate differences along a walk telescopes to the difference
between its endpoint values. -/
theorem sum_getVert_sub {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (x : V → ℝ) :
    (∑ i ∈ Finset.range p.length, (x (p.getVert i) - x (p.getVert (i + 1))))
      = x a - x b := by
  have h := Finset.sum_range_sub' (fun i => x (p.getVert i)) p.length
  simpa using h

/-- The sum of squared coordinate differences along a path is at most the total edge energy. -/
theorem path_energy_le_edgeEnergy {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (x : V → ℝ) :
    (∑ i ∈ Finset.range p.length, (x (p.getVert i) - x (p.getVert (i + 1))) ^ 2)
      ≤ edgeEnergy G x := by
  have hprod : edgeEnergy G x =
      ∑ q : V × V, (if G.Adj q.1 q.2 then (x q.1 - x q.2) ^ 2 else 0) := by
    unfold edgeEnergy
    rw [Fintype.sum_prod_type]
  rw [hprod]
  set f : ℕ → V × V := fun i => (p.getVert i, p.getVert (i + 1)) with hf
  have hinj : Set.InjOn f ↑(Finset.range p.length) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    have h1 : p.getVert i = p.getVert j := congrArg Prod.fst hij
    exact hp.getVert_injOn (by simpa using Nat.le_of_lt hi)
      (by simpa using Nat.le_of_lt hj) h1
  have hL : (∑ i ∈ Finset.range p.length, (x (p.getVert i) - x (p.getVert (i + 1))) ^ 2)
      = ∑ q ∈ (Finset.range p.length).image f,
          (if G.Adj q.1 q.2 then (x q.1 - x q.2) ^ 2 else 0) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f]
    have hadj : G.Adj (p.getVert i) (p.getVert (i + 1)) :=
      p.adj_getVert_succ (Finset.mem_range.mp hi)
    simp [hadj]
  rw [hL]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun q _ _ => by split_ifs <;> positivity)

/-- For a zero-sum vector supported in the component of `u`, the sum of coordinate squares is at
most `compSize G u * (compSize G u - 1) / 4` times its edge energy. -/
theorem poincare_edgeEnergy {G : SimpleGraph V} [DecidableRel G.Adj] {u : V} (x : V → ℝ)
    (hsupp : ∀ v, ¬ G.Reachable u v → x v = 0) (hsum : ∑ v, x v = 0) :
    ∑ v, x v ^ 2 ≤ (compSize G u : ℝ) * ((compSize G u : ℝ) - 1) * edgeEnergy G x / 4 := by
  classical
  set s := compSet G u with hs_def
  have hsne : s.Nonempty := by
    rw [hs_def]
    exact ⟨u, self_mem_compSet G u⟩
  have hzero_out : ∀ v, v ∉ s → x v = 0 := by
    intro v hv
    apply hsupp v
    intro hr
    exact hv (by rw [hs_def]; exact mem_compSet.mpr hr)
  have hsum_s : ∑ v ∈ s, x v = 0 := by
    simpa [hsum] using
      (Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => hzero_out v hv))
  have hsq_s : ∑ v ∈ s, x v ^ 2 = ∑ v, x v ^ 2 := by
    simpa using (Finset.sum_subset (Finset.subset_univ s)
      (fun v _ hv => by rw [hzero_out v hv]; ring))
  by_cases hx0 : x = 0
  · rw [hx0]
    simp [edgeEnergy]
  obtain ⟨a, ha_mem, ha_max⟩ := Finset.exists_max_image s x hsne
  obtain ⟨b, hb_mem, hb_min⟩ := Finset.exists_min_image s x hsne
  have hcpos : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hsne
  have ha_pos : 0 < x a := by
    have hnonneg : 0 ≤ x a := by
      have h2 : ∑ v ∈ s, x v ≤ (s.card : ℝ) * x a := by
        calc ∑ v ∈ s, x v ≤ ∑ v ∈ s, x a := Finset.sum_le_sum (fun v hv => ha_max v hv)
          _ = (s.card : ℝ) * x a := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum_s] at h2
      nlinarith
    rcases lt_or_eq_of_le hnonneg with hlt | heq
    · exact hlt
    · exfalso
      apply hx0
      funext v
      by_cases hv : v ∈ s
      · have hall : ∀ w ∈ s, x w = 0 :=
          (Finset.sum_eq_zero_iff_of_nonpos (fun w hw => heq ▸ ha_max w hw)).mp hsum_s
        exact hall v hv
      · exact hzero_out v hv
  have hb_neg : x b < 0 := by
    have hnonpos : x b ≤ 0 := by
      have h2 : (s.card : ℝ) * x b ≤ ∑ v ∈ s, x v := by
        calc (s.card : ℝ) * x b = ∑ v ∈ s, x b := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ v ∈ s, x v := Finset.sum_le_sum (fun v hv => hb_min v hv)
      rw [hsum_s] at h2
      nlinarith
    rcases lt_or_eq_of_le hnonpos with hlt | heq
    · exact hlt
    · exfalso
      apply hx0
      funext v
      by_cases hv : v ∈ s
      · have hall : ∀ w ∈ s, x w = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun w hw => heq ▸ hb_min w hw)).mp hsum_s
        exact hall v hv
      · exact hzero_out v hv
  have ha_reach : G.Reachable u a := by rw [hs_def] at ha_mem; exact mem_compSet.mp ha_mem
  have hb_reach : G.Reachable u b := by rw [hs_def] at hb_mem; exact mem_compSet.mp hb_mem
  have hab : G.Reachable a b := ha_reach.symm.trans hb_reach
  obtain ⟨p, hp⟩ := hab.exists_isPath
  have hlen : p.length + 1 ≤ compSize G u := length_le_compSize p hp ha_reach
  have hlenR : (p.length : ℝ) ≤ (compSize G u : ℝ) - 1 := by
    have hcast : ((p.length + 1 : ℕ) : ℝ) ≤ (compSize G u : ℝ) := by exact_mod_cast hlen
    push_cast at hcast
    linarith
  have htel := sum_getVert_sub p x
  have henergy := path_energy_le_edgeEnergy p hp x
  have hcheb : (∑ i ∈ Finset.range p.length,
      (x (p.getVert i) - x (p.getVert (i + 1)))) ^ 2
      ≤ (p.length : ℝ) * ∑ i ∈ Finset.range p.length,
          (x (p.getVert i) - x (p.getVert (i + 1))) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range p.length)
      (f := fun i => x (p.getVert i) - x (p.getVert (i + 1)))
    simpa using h
  have hdiff_sq : (x a - x b) ^ 2 ≤ (p.length : ℝ) * edgeEnergy G x := by
    rw [← htel]
    calc (∑ i ∈ Finset.range p.length,
          (x (p.getVert i) - x (p.getVert (i + 1)))) ^ 2
        ≤ (p.length : ℝ) * ∑ i ∈ Finset.range p.length,
            (x (p.getVert i) - x (p.getVert (i + 1))) ^ 2 := hcheb
      _ ≤ (p.length : ℝ) * edgeEnergy G x :=
          mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg _)
  have hdiff_sq' : (x a - x b) ^ 2 ≤ ((compSize G u : ℝ) - 1) * edgeEnergy G x :=
    le_trans hdiff_sq (mul_le_mul_of_nonneg_right hlenR (edgeEnergy_nonneg G x))
  have hvar : ∑ v ∈ s, x v ^ 2 ≤ (s.card : ℝ) * (x a - x b) ^ 2 / 4 :=
    sum_sq_le_card_mul_range_sq x (fun v hv => hb_min v hv) (fun v hv => ha_max v hv) hsum_s
  have hvarN : ∑ v, x v ^ 2 ≤ (compSize G u : ℝ) * (x a - x b) ^ 2 / 4 := by
    rw [← hsq_s, hs_def]
    exact hvar
  calc ∑ v, x v ^ 2 ≤ (compSize G u : ℝ) * (x a - x b) ^ 2 / 4 := hvarN
    _ ≤ (compSize G u : ℝ) * (((compSize G u : ℝ) - 1) * edgeEnergy G x) / 4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hdiff_sq' (Nat.cast_nonneg _)
    _ = (compSize G u : ℝ) * ((compSize G u : ℝ) - 1) * edgeEnergy G x / 4 := by ring

/-- On a regular graph, the edge energy is at most `4 * d` times the sum of coordinate squares. -/
theorem edgeEnergy_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (x : V → ℝ) :
    edgeEnergy G x ≤ 4 * d * (∑ u, x u ^ 2) := by
  have hterm : ∀ u v : V, (if G.Adj u v then (x u - x v) ^ 2 else 0)
      ≤ (if G.Adj u v then 2 * x u ^ 2 + 2 * x v ^ 2 else 0) := by
    intro u v
    by_cases h : G.Adj u v
    · simp only [h, ite_true]
      nlinarith [sq_nonneg (x u + x v)]
    · simp [h]
  have hstep : (∑ u, ∑ v, (if G.Adj u v then (x u - x v) ^ 2 else 0))
      ≤ ∑ u, ∑ v, (if G.Adj u v then 2 * x u ^ 2 + 2 * x v ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact hterm u v
  have hA : (∑ u, ∑ v, (if G.Adj u v then 2 * x u ^ 2 else 0))
      = 2 * d * (∑ u, x u ^ 2) := by
    have h1 : ∀ u, (∑ v, (if G.Adj u v then 2 * x u ^ 2 else 0))
        = 2 * x u ^ 2 * (∑ v, (if G.Adj u v then (1 : ℝ) else 0)) := by
      intro u
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : G.Adj u v <;> simp [h]
    simp only [h1, sum_ite_adj_row]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [hreg u]
    ring
  have hB : (∑ u, ∑ v, (if G.Adj u v then 2 * x v ^ 2 else 0))
      = 2 * d * (∑ u, x u ^ 2) := by
    rw [Finset.sum_comm]
    have h1 : ∀ v, (∑ u, (if G.Adj u v then 2 * x v ^ 2 else 0))
        = 2 * x v ^ 2 * (∑ u, (if G.Adj u v then (1 : ℝ) else 0)) := by
      intro v
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : G.Adj u v <;> simp [h]
    have hdeg : ∀ v, (∑ u, (if G.Adj u v then (1 : ℝ) else 0)) = d := by
      intro v
      have hs : (∑ u, (if G.Adj u v then (1 : ℝ) else 0))
          = ∑ u, (if G.Adj v u then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases h : G.Adj u v
        · rw [ite_eq_left h, ite_eq_left h.symm]
        · rw [ite_eq_right h, ite_eq_right (fun hc => h hc.symm)]
      rw [hs, sum_ite_adj_row]
      exact hreg v
    simp only [h1, hdeg]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hterm2 : ∀ u v : V, (if G.Adj u v then 2 * x u ^ 2 + 2 * x v ^ 2 else 0)
      = (if G.Adj u v then 2 * x u ^ 2 else 0)
        + (if G.Adj u v then 2 * x v ^ 2 else 0) := by
    intro u v
    by_cases h : G.Adj u v <;> simp [h]
  unfold edgeEnergy
  calc (∑ u, ∑ v, (if G.Adj u v then (x u - x v) ^ 2 else 0))
      ≤ ∑ u, ∑ v, (if G.Adj u v then 2 * x u ^ 2 + 2 * x v ^ 2 else 0) := hstep
    _ = (∑ u, ∑ v, (if G.Adj u v then 2 * x u ^ 2 else 0))
          + (∑ u, ∑ v, (if G.Adj u v then 2 * x v ^ 2 else 0)) := by
        simp only [hterm2, Finset.sum_add_distrib]
    _ = 2 * d * (∑ u, x u ^ 2) + 2 * d * (∑ u, x u ^ 2) := by rw [hA, hB]
    _ = 4 * d * (∑ u, x u ^ 2) := by ring

/-- On a regular graph, the quadratic form of `walkM` is at least `(1 - 2 * walkB d * d)` times
the sum of coordinate squares. -/
theorem dotProduct_walkM_self_ge (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (x : V → ℝ) :
    (1 - 2 * walkB d * d) * (∑ u, x u ^ 2) ≤ x ⬝ᵥ (walkM G d *ᵥ x) := by
  rw [dotProduct_walkM_self G hreg]
  have hb2 : 0 ≤ walkB d / 2 := by
    unfold walkB
    positivity
  have hmul : (walkB d / 2) * edgeEnergy G x
      ≤ (walkB d / 2) * (4 * d * (∑ u, x u ^ 2)) :=
    mul_le_mul_of_nonneg_left (edgeEnergy_le G hreg x) hb2
  nlinarith [hmul]

/-- For a zero-sum vector supported on a component of size at least two in a regular graph, the
quadratic form of `walkM` is at most `elemRho G d u` times the sum of coordinate squares. -/
theorem dotProduct_walkM_self_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (u : V) (hN2 : 2 ≤ compSize G u) (x : V → ℝ)
    (hsupp : ∀ v, ¬ G.Reachable u v → x v = 0) (hsum : ∑ v, x v = 0) :
    x ⬝ᵥ (walkM G d *ᵥ x)
      ≤ (1 - 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)))
          * (∑ v, x v ^ 2) := by
  rw [dotProduct_walkM_self G hreg]
  have hNpos : (0 : ℝ) < (compSize G u : ℝ) := compSize_pos G u
  have hN1 : (1 : ℝ) < (compSize G u : ℝ) := by
    have : (2 : ℝ) ≤ (compSize G u : ℝ) := by exact_mod_cast hN2
    linarith
  have hden : (0 : ℝ) < (compSize G u : ℝ) * ((compSize G u : ℝ) - 1) :=
    mul_pos hNpos (by linarith)
  have hp := poincare_edgeEnergy (G := G) (u := u) x hsupp hsum
  have hb2 : 0 ≤ walkB d / 2 := by
    unfold walkB
    positivity
  have hmul : (walkB d / 2) * (4 * (∑ v, x v ^ 2) / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)))
      ≤ (walkB d / 2) * edgeEnergy G x := by
    apply mul_le_mul_of_nonneg_left _ hb2
    rw [div_le_iff₀ hden]
    linarith [hp]
  have hkey : 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1))
      * (∑ v, x v ^ 2) = (walkB d / 2) * (4 * (∑ v, x v ^ 2) / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1))) := by
    field_simp
    ring
  rw [← hkey] at hmul
  nlinarith [hmul]

/-- Every component of a regular graph of degree at least two contains at least three vertices. -/
theorem compSize_ge_three (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (u : V) : 3 ≤ compSize G u := by
  classical
  have hsub : G.neighborFinset u ⊆ (compSet G u).erase u := by
    intro v hv
    rw [Finset.mem_erase]
    rw [SimpleGraph.mem_neighborFinset] at hv
    exact ⟨hv.ne.symm, mem_compSet.mpr hv.reachable⟩
  have hle : (G.neighborFinset u).card ≤ ((compSet G u).erase u).card :=
    Finset.card_le_card hsub
  have hc : ((compSet G u).erase u).card = compSize G u - 1 := by
    rw [Finset.card_erase_of_mem (self_mem_compSet G u)]
    rfl
  have h24 : 2 ≤ (G.neighborFinset u).card := by
    have h2r : (2 : ℝ) ≤ ((G.neighborFinset u).card : ℝ) := by
      rw [hreg u]
      exact hd
    exact_mod_cast h2r
  omega

/-- For `2 ≤ d` and `3 ≤ N`, the quantity `2 * walkB d / (N * (N - 1))` is at most `2 - 2 *
walkB d * d`. -/
theorem delta_le (d : ℝ) (N : ℕ) (hd : 2 ≤ d) (hN : 3 ≤ N) :
    2 * walkB d / ((N : ℝ) * ((N : ℝ) - 1)) ≤ 2 - 2 * walkB d * d := by
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hden : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) := by
    apply mul_pos hNpos
    linarith
  have hD : (6 : ℝ) ≤ (N : ℝ) * ((N : ℝ) - 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 3)
      (by linarith : (0 : ℝ) ≤ (N : ℝ) + 2)]
  have hdm : (1 : ℝ) ≤ (d - 1) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d - 1) (by linarith : (0 : ℝ) ≤ d - 1)]
  have hkey : (4 : ℝ) ≤ (N : ℝ) * ((N : ℝ) - 1) * (d - 1) ^ 2 := by
    nlinarith [mul_le_mul hD hdm (by linarith) (by linarith), hD, hdm]
  rw [div_le_iff₀ hden]
  unfold walkB
  have hp : (0 : ℝ) < d + 1 := by linarith
  have hp2 : (0 : ℝ) < (d + 1) ^ 2 := by positivity
  rw [div_pow]
  field_simp
  nlinarith [hkey, hp2]

omit [Fintype V] in

/-- The vertex-space walk matrix is symmetric. -/
theorem walkM_transpose (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) :
    (walkM G d)ᵀ = walkM G d := by
  unfold walkM adjMatrix
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one]
  congr 2
  ext i j
  simp [G.adj_comm]

/-- The bilinear form defined by `walkM` is symmetric in its two real-vector arguments. -/
theorem dotProduct_walkM_comm (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (x y : V → ℝ) :
    x ⬝ᵥ (walkM G d *ᵥ y) = y ⬝ᵥ (walkM G d *ᵥ x) := by
  calc x ⬝ᵥ (walkM G d *ᵥ y) = x ⬝ᵥ ((walkM G d)ᵀ *ᵥ y) := by rw [walkM_transpose]
    _ = y ⬝ᵥ (walkM G d *ᵥ x) := Matrix.dotProduct_transpose_mulVec (walkM G d) x y

/-- For a regular graph of degree at least two, the absolute quadratic form on a
component-supported zero-sum vector is bounded by `elemRho G d u` times the sum of
coordinate squares. -/
theorem abs_dotProduct_walkM_self_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (u : V) (x : V → ℝ)
    (hsupp : ∀ v, ¬ G.Reachable u v → x v = 0) (hsum : ∑ v, x v = 0) :
    |x ⬝ᵥ (walkM G d *ᵥ x)|
      ≤ (1 - 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)))
          * (∑ v, x v ^ 2) := by
  have hN3 : 3 ≤ compSize G u := compSize_ge_three G hreg hd u
  have hN2 : 2 ≤ compSize G u := by omega
  have hup := dotProduct_walkM_self_le G hreg u hN2 x hsupp hsum
  have hlow := dotProduct_walkM_self_ge G hreg x
  have hdl := delta_le d (compSize G u) hd hN3
  have hS : (0 : ℝ) ≤ ∑ v, x v ^ 2 := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  have hρneg : -(1 - 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)))
      ≤ 1 - 2 * walkB d * d := by linarith
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hρneg hS, hlow]
  · exact hup

omit [DecidableEq V] in

/-- For `2 ≤ d` and component size at least three, the coefficient `elemRho G d u` is
nonnegative. -/
theorem rho_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ} (hd : 2 ≤ d) (u : V)
    (hN3 : 3 ≤ compSize G u) :
    (0 : ℝ) ≤ 1 - 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)) := by
  have hNr : (3 : ℝ) ≤ (compSize G u : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < (compSize G u : ℝ) := by linarith
  have hden : (0 : ℝ) < (compSize G u : ℝ) * ((compSize G u : ℝ) - 1) :=
    mul_pos hNpos (by linarith)
  have hD : (6 : ℝ) ≤ (compSize G u : ℝ) * ((compSize G u : ℝ) - 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (compSize G u : ℝ) - 3)
      (by linarith : (0 : ℝ) ≤ (compSize G u : ℝ) + 2)]
  have hb : walkB d ≤ 4 / 9 := by
    unfold walkB
    have h3 : (3 : ℝ) ≤ d + 1 := by linarith
    have h9 : (9 : ℝ) ≤ (d + 1) ^ 2 := by nlinarith
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (d + 1) ^ 2) (by norm_num : (0 : ℝ) < 9)]
    norm_num
    nlinarith
  have h2b : 2 * walkB d ≤ (compSize G u : ℝ) * ((compSize G u : ℝ) - 1) := by
    nlinarith [hb, hD]
  have hle : 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)) ≤ 1 := by
    rw [div_le_one hden]
    exact h2b
  linarith

/-- The Euclidean norm of a real scalar multiple is the absolute value of the scalar times the
original norm. -/
theorem l2norm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    l2norm (c • v) = |c| * l2norm v := by
  unfold l2norm
  have hsq : (∑ i, (c • v) i ^ 2) = c ^ 2 * (∑ i, v i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul, sq]
    ring
  rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- A nonzero finite real vector has nonzero Euclidean norm. -/
theorem l2norm_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : v ≠ 0) :
    l2norm v ≠ 0 := by
  intro h
  apply hv
  have hsq : l2norm v ^ 2 = ∑ i, v i ^ 2 := l2norm_sq_eq v
  rw [h] at hsq
  simp at hsq
  funext i
  have hsum0 : (∑ j, v j ^ 2) = 0 := hsq.symm
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp hsum0
  exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))

/-- For two zero-sum vectors supported in the same component of a regular graph of degree at
least two, the absolute `walkM` bilinear form is bounded by `elemRho G d u / 2` times the
sum of their squared norms. -/
theorem abs_dotProduct_walkM_bilinear (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (u : V) (x y : V → ℝ)
    (hsuppx : ∀ v, ¬ G.Reachable u v → x v = 0) (hsumx : ∑ v, x v = 0)
    (hsuppy : ∀ v, ¬ G.Reachable u v → y v = 0) (hsumy : ∑ v, y v = 0) :
    |x ⬝ᵥ (walkM G d *ᵥ y)|
      ≤ elemRho G d u / 2 * ((∑ v, x v ^ 2) + (∑ v, y v ^ 2)) := by
  have hplus_supp : ∀ v, ¬ G.Reachable u v → (x + y) v = 0 := by
    intro v hv
    simp only [Pi.add_apply, hsuppx v hv, hsuppy v hv, add_zero]
  have hminus_supp : ∀ v, ¬ G.Reachable u v → (x - y) v = 0 := by
    intro v hv
    simp only [Pi.sub_apply, hsuppx v hv, hsuppy v hv, sub_zero]
  have hplus_sum : ∑ v, (x + y) v = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hsumx, hsumy, add_zero]
  have hminus_sum : ∑ v, (x - y) v = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsumx, hsumy, sub_zero]
  have hp := abs_dotProduct_walkM_self_le G hreg hd u (x + y) hplus_supp hplus_sum
  have hm := abs_dotProduct_walkM_self_le G hreg hd u (x - y) hminus_supp hminus_sum
  have hp' : |(x + y) ⬝ᵥ (walkM G d *ᵥ (x + y))| ≤ elemRho G d u * (∑ v, (x + y) v ^ 2) := hp
  have hm' : |(x - y) ⬝ᵥ (walkM G d *ᵥ (x - y))| ≤ elemRho G d u * (∑ v, (x - y) v ^ 2) := hm

  have hpolar : (x + y) ⬝ᵥ (walkM G d *ᵥ (x + y)) - (x - y) ⬝ᵥ (walkM G d *ᵥ (x - y))
      = 4 * (x ⬝ᵥ (walkM G d *ᵥ y)) := by
    have hsym := dotProduct_walkM_comm G d x y
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, dotProduct_sub,
      add_dotProduct, sub_dotProduct]
    linear_combination -2 * hsym
  have hsqid : (∑ v, (x + y) v ^ 2) + (∑ v, (x - y) v ^ 2)
      = 2 * ((∑ v, x v ^ 2) + (∑ v, y v ^ 2)) := by
    rw [← Finset.sum_add_distrib]
    rw [show (∑ v, x v ^ 2) + (∑ v, y v ^ 2) = ∑ v, (x v ^ 2 + y v ^ 2) from
      Finset.sum_add_distrib.symm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htri : |(x + y) ⬝ᵥ (walkM G d *ᵥ (x + y)) - (x - y) ⬝ᵥ (walkM G d *ᵥ (x - y))|
      ≤ |(x + y) ⬝ᵥ (walkM G d *ᵥ (x + y))| + |(x - y) ⬝ᵥ (walkM G d *ᵥ (x - y))| := by
    have h := abs_add_le ((x + y) ⬝ᵥ (walkM G d *ᵥ (x + y)))
      (-((x - y) ⬝ᵥ (walkM G d *ᵥ (x - y))))
    simpa only [sub_eq_add_neg, abs_neg] using h
  have habs4 : |4 * (x ⬝ᵥ (walkM G d *ᵥ y))| = 4 * |x ⬝ᵥ (walkM G d *ᵥ y)| := by
    rw [abs_mul]
    norm_num
  have hupper : 4 * |x ⬝ᵥ (walkM G d *ᵥ y)|
      ≤ elemRho G d u * (2 * ((∑ v, x v ^ 2) + (∑ v, y v ^ 2))) := by
    rw [← habs4, ← hpolar, ← hsqid]
    calc |(x + y) ⬝ᵥ (walkM G d *ᵥ (x + y)) - (x - y) ⬝ᵥ (walkM G d *ᵥ (x - y))|
        ≤ |(x + y) ⬝ᵥ (walkM G d *ᵥ (x + y))|
            + |(x - y) ⬝ᵥ (walkM G d *ᵥ (x - y))| := htri
      _ ≤ elemRho G d u * (∑ v, (x + y) v ^ 2)
            + elemRho G d u * (∑ v, (x - y) v ^ 2) := add_le_add hp' hm'
      _ = elemRho G d u * ((∑ v, (x + y) v ^ 2) + (∑ v, (x - y) v ^ 2)) := by ring
  nlinarith [hupper]

/-- On a regular graph, a nonnegative `elemRho` and the stated bilinear estimate imply the
corresponding Euclidean contraction for every component-supported zero-sum vector. -/
theorem contraction_of_bilinear (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (u : V) (hρnn : 0 ≤ elemRho G d u)
    (hbil : ∀ x y : V → ℝ,
      (∀ v, ¬ G.Reachable u v → x v = 0) → (∑ v, x v = 0) →
      (∀ v, ¬ G.Reachable u v → y v = 0) → (∑ v, y v = 0) →
      |x ⬝ᵥ (walkM G d *ᵥ y)| ≤ elemRho G d u / 2 * ((∑ v, x v ^ 2) + (∑ v, y v ^ 2)))
    (x : V → ℝ) (hsupp : ∀ v, ¬ G.Reachable u v → x v = 0) (hsum : ∑ v, x v = 0) :
    l2norm (walkM G d *ᵥ x) ≤ elemRho G d u * l2norm x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [l2norm]
  by_cases hy0 : walkM G d *ᵥ x = 0
  · rw [hy0]
    have hz : l2norm (0 : V → ℝ) = 0 := by simp [l2norm]
    rw [hz]
    exact mul_nonneg hρnn (l2norm_nonneg x)
  have hMxsupp : ∀ v, ¬ G.Reachable u v → (walkM G d *ᵥ x) v = 0 :=
    walkM_mulVec_support G d u hsupp
  have hMxsum : ∑ v, (walkM G d *ᵥ x) v = 0 := by
    rw [sum_walkM_mulVec_eq G hreg x, hsum]
  set B : ℝ := l2norm x with hB
  set L : ℝ := l2norm (walkM G d *ᵥ x) with hL
  have hBpos : 0 < B := by
    rw [hB]; exact lt_of_le_of_ne (l2norm_nonneg x) (Ne.symm (l2norm_ne_zero hx0))
  have hLpos : 0 < L := by
    rw [hL]; exact lt_of_le_of_ne (l2norm_nonneg _) (Ne.symm (l2norm_ne_zero hy0))
  set c : ℝ := B⁻¹ with hc
  set e : ℝ := L⁻¹ with he
  have hcpos : 0 < c := by rw [hc]; exact inv_pos.mpr hBpos
  have hepos : 0 < e := by rw [he]; exact inv_pos.mpr hLpos
  have hcB : c * B = 1 := by rw [hc]; exact inv_mul_cancel₀ (ne_of_gt hBpos)
  have heL : e * L = 1 := by rw [he]; exact inv_mul_cancel₀ (ne_of_gt hLpos)
  set z : V → ℝ := c • x with hz
  set w : V → ℝ := e • (walkM G d *ᵥ x) with hw
  have hzsupp : ∀ v, ¬ G.Reachable u v → z v = 0 := by
    intro v hv
    rw [hz]
    simp only [Pi.smul_apply, smul_eq_mul, hsupp v hv, mul_zero]
  have hwsupp : ∀ v, ¬ G.Reachable u v → w v = 0 := by
    intro v hv
    rw [hw]
    simp only [Pi.smul_apply, smul_eq_mul, hMxsupp v hv, mul_zero]
  have hzsum : ∑ v, z v = 0 := by
    rw [hz]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hsum, mul_zero]
  have hwsum : ∑ v, w v = 0 := by
    rw [hw]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hMxsum, mul_zero]
  have hself : (walkM G d *ᵥ x) ⬝ᵥ (walkM G d *ᵥ x) = L ^ 2 := by
    rw [show (walkM G d *ᵥ x) ⬝ᵥ (walkM G d *ᵥ x) = ∑ v, (walkM G d *ᵥ x) v ^ 2 from by
      simp [dotProduct, sq]]
    rw [hL, l2norm_sq_eq]
  have hBsq : ∑ v, x v ^ 2 = B ^ 2 := by rw [hB, l2norm_sq_eq]
  have hzsq : ∑ v, z v ^ 2 = 1 := by
    rw [hz]
    have hstep : ∑ v, (c • x) v ^ 2 = c ^ 2 * (∑ v, x v ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hstep, hBsq]
    calc c ^ 2 * B ^ 2 = (c * B) ^ 2 := by ring
      _ = 1 := by rw [hcB]; norm_num
  have hwsq : ∑ v, w v ^ 2 = 1 := by
    rw [hw]
    have hstep : ∑ v, (e • (walkM G d *ᵥ x)) v ^ 2
        = e ^ 2 * (∑ v, (walkM G d *ᵥ x) v ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hstep]
    have hLsum : ∑ v, (walkM G d *ᵥ x) v ^ 2 = L ^ 2 := by rw [hL, l2norm_sq_eq]
    rw [hLsum]
    calc e ^ 2 * L ^ 2 = (e * L) ^ 2 := by ring
      _ = 1 := by rw [heL]; norm_num
  have hMz : walkM G d *ᵥ z = c • (walkM G d *ᵥ x) := by
    rw [hz]
    exact Matrix.mulVec_smul (walkM G d) c x
  have hval : w ⬝ᵥ (walkM G d *ᵥ z) = L * c := by
    rw [hMz, hw, dotProduct_smul, smul_dotProduct, hself]
    calc c * (e * L ^ 2) = L * c * (e * L) := by ring
      _ = L * c * 1 := by rw [heL]
      _ = L * c := by ring
  have hbl := hbil w z hwsupp hwsum hzsupp hzsum
  rw [hval] at hbl
  have hsumsq : (∑ v, w v ^ 2) + (∑ v, z v ^ 2) = 2 := by rw [hwsq, hzsq]; norm_num
  rw [hsumsq] at hbl
  rw [abs_of_nonneg (mul_nonneg (le_of_lt hLpos) (le_of_lt hcpos))] at hbl
  have hh : elemRho G d u / 2 * 2 = elemRho G d u := by ring
  rw [hh] at hbl
  calc L = L * 1 := (mul_one L).symm
    _ = L * (c * B) := by rw [hcB]
    _ = L * c * B := by ring
    _ ≤ elemRho G d u * B := mul_le_mul_of_nonneg_right hbl (l2norm_nonneg x)

/-- On a regular graph of degree at least two, `walkM` contracts component-supported zero-sum
vectors in Euclidean norm by the factor `elemRho G d u`. -/
theorem walkM_contraction (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (u : V) (x : V → ℝ)
    (hsupp : ∀ v, ¬ G.Reachable u v → x v = 0) (hsum : ∑ v, x v = 0) :
    l2norm (walkM G d *ᵥ x) ≤ elemRho G d u * l2norm x := by
  have hN3 : 3 ≤ compSize G u := compSize_ge_three G hreg hd u
  have hρnn : 0 ≤ elemRho G d u := rho_nonneg G hd u hN3
  exact contraction_of_bilinear G hreg u hρnn
    (fun x y hx hxs hy hys => abs_dotProduct_walkM_bilinear G hreg hd u x y hx hxs hy hys)
    x hsupp hsum

/-- Every regular graph of degree at least two satisfies `SpectralGap G d u` at each vertex `u`.
See [Watrous1998]. -/
theorem spectralGap_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (u : V) : SpectralGap G d u := by
  intro x hsupp hsum
  by_cases h1 : compSize G u = 1
  · exact spectralGap_singleton G d u h1 x hsupp hsum
  · have hN3 : 3 ≤ compSize G u := compSize_ge_three G hreg hd u
    have hcontr := walkM_contraction G hreg hd u x hsupp hsum
    have hρκ : elemRho G d u ≤ 1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) := by
      unfold elemRho
      have hcore : 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)
          ≤ 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)) := by
        have hd0 : (0 : ℝ) < d := by linarith
        have hNr : (3 : ℝ) ≤ (compSize G u : ℝ) := by exact_mod_cast hN3
        have hNpos : (0 : ℝ) < (compSize G u : ℝ) := by linarith
        have hDpos : (0 : ℝ) < (compSize G u : ℝ) * ((compSize G u : ℝ) - 1) :=
          mul_pos hNpos (by linarith)
        have hdnpos : (0 : ℝ) < d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2 := by
          have h1 : (0 : ℝ) < (d + 1) ^ 2 := by positivity
          have h2 : (0 : ℝ) < (compSize G u : ℝ) ^ 2 := by positivity
          exact mul_pos (mul_pos hd0 h1) h2
        have hR : 2 * walkB d / ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1))
            = 8 / ((d + 1) ^ 2 * ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1))) := by
          unfold walkB
          field_simp
          ring
        rw [hR]
        have hden2 : (0 : ℝ) <
            (d + 1) ^ 2 * ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1)) :=
          mul_pos (by positivity) hDpos
        rw [div_le_div_iff₀ hdnpos hden2]
        have hnn : (compSize G u : ℝ) - 1 ≤ d * (compSize G u : ℝ) := by
          nlinarith [hd, hNr]
        have hchain : (compSize G u : ℝ) * ((compSize G u : ℝ) - 1)
            ≤ d * (compSize G u : ℝ) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hnn (le_of_lt hNpos)]
        have hchain2 : (d + 1) ^ 2 * ((compSize G u : ℝ) * ((compSize G u : ℝ) - 1))
            ≤ (d + 1) ^ 2 * (d * (compSize G u : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
        nlinarith [hchain2]
      linarith
    calc l2norm (walkM G d *ᵥ x) ≤ elemRho G d u * l2norm x := hcontr
      _ ≤ (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) * l2norm x :=
          mul_le_mul_of_nonneg_right hρκ (l2norm_nonneg x)

end

end Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing
