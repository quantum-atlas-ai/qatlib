/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # The `K_d` switch count of Theorem 3.3

Childs--Kothari, arXiv:1011.1443v2, Section 3.1, p. 6.

The paper's family `Y` consists of the graphs that are a `K_d` on a `d`-element
vertex set together with isolated vertices; it is parametrised by that vertex set.
We count the parameter sets, the parameter sets whose graph contains a fixed
ordered pair of distinct vertices as an edge, and bound the ratio
`√(|Y| / |Y_e|)` by `Θ(n)` for fixed `d`.  A graph of the family is recovered
from its non-isolated vertex set as soon as `d ≥ 2`, so the parameter count is
also the count of graphs.
-/

set_option autoImplicit false
namespace Qatlib.Papers.MinorClosed10.MainResults.SwitchCounting

noncomputable section

open Qatlib.Papers.MinorClosed10.MainResults

/-- The graph that is complete on the vertex set `S` and has no other edges. -/
def KdGraph {n : ℕ} (S : Finset (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => a ∈ S ∧ b ∈ S)

/-- Adjacency in `KdGraph S`: two distinct vertices of `S`. -/
theorem KdGraph_adj {n : ℕ} (S : Finset (Fin n)) (a b : Fin n) :
    (KdGraph S).Adj a b ↔ a ≠ b ∧ a ∈ S ∧ b ∈ S := by
  rw [KdGraph, SimpleGraph.fromRel_adj]
  tauto

/-- The `d`-element vertex sets parametrising the family `Y`. -/
abbrev KdConfig (n d : ℕ) : Type :=
  {S : Finset (Fin n) // S.card = d}

instance (n d : ℕ) : Fintype (KdConfig n d) := by
  classical
  infer_instance

/-- `|Y| = C(n,d)`. -/
theorem card_kdConfig (n d : ℕ) : Fintype.card (KdConfig n d) = Nat.choose n d := by
  classical
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = d)) =
      (Finset.univ : Finset (Fin n)).powersetCard d := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The graphs of the paper's family: complete on a `d`-element set, isolated
elsewhere. -/
abbrev KdGraphFamily (n d : ℕ) : Type :=
  {G : SimpleGraph (Fin n) //
    ∃ S : Finset (Fin n), S.card = d ∧ ∀ a b, G.Adj a b ↔ a ≠ b ∧ a ∈ S ∧ b ∈ S}

noncomputable instance (n d : ℕ) : Fintype (KdGraphFamily n d) := by
  classical
  exact Fintype.ofFinite _

/-- The non-isolated vertices of a graph. -/
def supportSet {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => ∃ w, G.Adj v w)

/-- A set of at least two vertices has a second vertex different from any
prescribed member. -/
theorem exists_other_mem {α : Type} [DecidableEq α] {S : Finset α}
    (h : 2 ≤ S.card) {v : α} (hv : v ∈ S) : ∃ w ∈ S, w ≠ v := by
  have hpos : 0 < (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv]
    exact Nat.sub_pos_of_lt (by omega : 1 < S.card)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, Finset.mem_of_mem_erase hw, (Finset.mem_erase.mp hw).1⟩

/-- For `S` of cardinality at least two, the support of `KdGraph S` is `S`. -/
theorem supportSet_kdGraph {n : ℕ} {S : Finset (Fin n)} (h : 2 ≤ S.card) :
    supportSet (KdGraph S) = S := by
  ext v
  constructor
  · intro hv
    simp only [supportSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨w, hw⟩ := hv
    exact (KdGraph_adj S v w).mp hw |>.2.1
  · intro hv
    obtain ⟨w, hwS, hwne⟩ := exists_other_mem h hv
    simp only [supportSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, (KdGraph_adj S v w).mpr ⟨hwne.symm, hv, hwS⟩⟩

/-- The vertex set parameter determines its graph. -/
def configToGraph {n d : ℕ} (S : KdConfig n d) : KdGraphFamily n d :=
  ⟨KdGraph S.1, S.1, S.2, fun a b => KdGraph_adj S.1 a b⟩

/-- The non-isolated vertex set of a family graph is its parameter set. -/
noncomputable def graphToConfig {n d : ℕ} (h2 : 2 ≤ d) (G : KdGraphFamily n d) :
    KdConfig n d :=
  ⟨supportSet G.1, by
    obtain ⟨S, hS, hAdj⟩ := G.2
    have hs : supportSet G.1 = S := by
      ext v
      constructor
      · intro hv
        simp only [supportSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨w, hw⟩ := hv
        exact (hAdj v w).mp hw |>.2.1
      · intro hv
        obtain ⟨w, hwS, hwne⟩ := exists_other_mem (by omega : 2 ≤ S.card) hv
        simp only [supportSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w, (hAdj v w).mpr ⟨hwne.symm, hv, hwS⟩⟩
    rw [hs, hS]⟩

/-- For `d ≥ 2`, the vertex-set parameters are in bijection with the graphs of
the family. -/
noncomputable def kdConfigEquivGraph {n d : ℕ} (h2 : 2 ≤ d) :
    KdConfig n d ≃ KdGraphFamily n d where
  toFun := configToGraph
  invFun := graphToConfig h2
  left_inv S := by
    apply Subtype.ext
    exact supportSet_kdGraph (by omega : 2 ≤ S.1.card)
  right_inv G := by
    apply Subtype.ext
    obtain ⟨S, hS, hAdj⟩ := G.2
    have hs : supportSet G.1 = S := by
      ext v
      constructor
      · intro hv
        simp only [supportSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨w, hw⟩ := hv
        exact (hAdj v w).mp hw |>.2.1
      · intro hv
        obtain ⟨w, hwS, hwne⟩ := exists_other_mem (by omega : 2 ≤ S.card) hv
        simp only [supportSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w, (hAdj v w).mpr ⟨hwne.symm, hv, hwS⟩⟩
    ext a b
    change (KdGraph (supportSet G.1)).Adj a b ↔ G.1.Adj a b
    rw [KdGraph_adj, hs, hAdj]

/-- `|Y| = C(n,d)` also for the graph presentation when `d ≥ 2`. -/
theorem card_kdGraphFamily {n d : ℕ} (h2 : 2 ≤ d) :
    Fintype.card (KdGraphFamily n d) = Nat.choose n d := by
  classical
  rw [← card_kdConfig n d]
  exact Fintype.card_congr (kdConfigEquivGraph h2).symm

/-- Vertex sets whose graph contains the ordered pair `e` as an edge. -/
def edgeConfigs (n d : ℕ) (e : Fin n × Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard d).filter (fun S => e.1 ∈ S ∧ e.2 ∈ S)

/-- `|Y_e| = C(n-2,d-2)` for a fixed ordered pair of distinct vertices. -/
theorem card_edgeConfigs {n d : ℕ} {e : Fin n × Fin n} (hne : e.1 ≠ e.2)
    (h2 : 2 ≤ d) : (edgeConfigs n d e).card = Nat.choose (n - 2) (d - 2) := by
  classical
  have hpair : ({e.1, e.2} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hsub : ({e.1, e.2} : Finset (Fin n)) ⊆ Finset.univ := by simp
  have h := Finset.card_filter_powersetCard_subset
    ({e.1, e.2} : Finset (Fin n)) (Finset.univ : Finset (Fin n)) d hsub (by omega)
  rw [Finset.card_univ, Fintype.card_fin, hpair] at h
  have hfilter : (Finset.univ.powersetCard d).filter
        (fun S => e.1 ∈ S ∧ e.2 ∈ S) =
      (Finset.univ.powersetCard d).filter
        (fun S => ({e.1, e.2} : Finset (Fin n)) ⊆ S) := by
    apply Finset.filter_congr
    intro S _
    simp [Finset.insert_subset_iff]
  rw [edgeConfigs, hfilter, h]

/-- `d`-element vertex sets whose graph contains the ordered pair `e` as an edge. -/
abbrev KdConfigWithEdge (n d : ℕ) (e : Fin n × Fin n) : Type :=
  {S : KdConfig n d // (KdGraph S.1).Adj e.1 e.2}

noncomputable instance (n d : ℕ) (e : Fin n × Fin n) : Fintype (KdConfigWithEdge n d e) := by
  classical
  dsimp [KdConfigWithEdge]
  infer_instance

noncomputable instance (n d : ℕ) (e : Fin n × Fin n) :
    Fintype {G : KdGraphFamily n d // G.1.Adj e.1 e.2} := by
  classical
  infer_instance

/-- `|Y_e| = C(n-2,d-2)` in the parameter presentation. -/
theorem card_kdConfigWithEdge {n d : ℕ} {e : Fin n × Fin n} (hne : e.1 ≠ e.2)
    (h2 : 2 ≤ d) :
    Fintype.card (KdConfigWithEdge n d e) = Nat.choose (n - 2) (d - 2) := by
  classical
  have hcard : Fintype.card (KdConfigWithEdge n d e) =
      Fintype.card {S : Finset (Fin n) // S.card = d ∧ e.1 ∈ S ∧ e.2 ∈ S} := by
    apply Fintype.card_congr
    refine
      { toFun := fun x =>
          ⟨x.1.1, x.1.2, (KdGraph_adj x.1.1 e.1 e.2).mp x.2 |>.2⟩
        invFun := fun y =>
          ⟨⟨y.1, y.2.1⟩, (KdGraph_adj y.1 e.1 e.2).mpr ⟨hne, y.2.2.1, y.2.2.2⟩⟩
        left_inv := fun x => by cases x; rfl
        right_inv := fun y => by cases y; rfl }
  rw [hcard, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter
        (fun S : Finset (Fin n) => S.card = d ∧ e.1 ∈ S ∧ e.2 ∈ S)) =
      edgeConfigs n d e := by
    ext S
    simp [edgeConfigs, Finset.mem_powersetCard]
  rw [hfilter]
  exact card_edgeConfigs hne h2

/-- `|Y_e| = C(n-2,d-2)` for the graph presentation when `d ≥ 2`. -/
theorem card_kdGraphFamilyWithEdge {n d : ℕ} {e : Fin n × Fin n} (hne : e.1 ≠ e.2)
    (h2 : 2 ≤ d) :
    Fintype.card {G : KdGraphFamily n d // G.1.Adj e.1 e.2} =
      Nat.choose (n - 2) (d - 2) := by
  classical
  have heq : Fintype.card {G : KdGraphFamily n d // G.1.Adj e.1 e.2} =
      Fintype.card (KdConfigWithEdge n d e) := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquiv (kdConfigEquivGraph (n := n) (d := d) h2).symm ?_
    intro G
    have hval : (configToGraph ((kdConfigEquivGraph h2).symm G)).1 = G.1 := by
      have h := (kdConfigEquivGraph h2).right_inv G
      change configToGraph ((kdConfigEquivGraph h2).symm G) = G at h
      exact congrArg Subtype.val h
    rw [← hval]
    rfl
  rw [heq]
  exact card_kdConfigWithEdge hne h2

/-- The one-element family `X` of Theorem 3.3: the empty graph. -/
abbrev KdX (n : ℕ) : Type := {G : SimpleGraph (Fin n) // G = ⊥}

noncomputable instance (n : ℕ) : Fintype (KdX n) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance (n d : ℕ) (e : Fin n × Fin n) (y : KdConfig n d) :
    Fintype {_x : KdX n // (KdGraph y.1).Adj e.1 e.2} := by
  classical
  exact Fintype.ofFinite _

/-- `|X| = 1`. -/
theorem card_kdX (n : ℕ) : Fintype.card (KdX n) = 1 := by
  classical
  dsimp [KdX]
  exact Fintype.card_subtype_eq (⊥ : SimpleGraph (Fin n))

/-- The left fibre of the relation at the empty graph has `C(n-2,d-2)` elements. -/
theorem kdRelation_left_fiber {n d : ℕ} {e : Fin n × Fin n} (hne : e.1 ≠ e.2)
    (h2 : 2 ≤ d) :
    Fintype.card {y : KdConfig n d // (KdGraph y.1).Adj e.1 e.2} =
      Nat.choose (n - 2) (d - 2) :=
  card_kdConfigWithEdge hne h2

/-- Every right fibre has at most one element. -/
theorem kdRelation_right_fiber {n d : ℕ} {e : Fin n × Fin n} (y : KdConfig n d) :
    Fintype.card {_x : KdX n // (KdGraph y.1).Adj e.1 e.2} ≤ 1 := by
  classical
  calc Fintype.card {_x : KdX n // (KdGraph y.1).Adj e.1 e.2} ≤ Fintype.card (KdX n) :=
        Fintype.card_subtype_le _
    _ = 1 := card_kdX n

/-- Exact ratio of the two counting formulas. -/
theorem choose_ratio {n d : ℕ} (h2 : 2 ≤ d) (hdn : d ≤ n) :
    (Nat.choose n d : ℝ) / (Nat.choose (n - 2) (d - 2) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) - 1)) := by
  have hpos : (0 : ℝ) < Nat.choose (n - 2) (d - 2) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hmul := Nat.choose_mul (n := n) (k := d) (s := 2) h2
  have hmulR : (Nat.choose n d : ℝ) * (Nat.choose d 2 : ℝ) =
      (Nat.choose n 2 : ℝ) * (Nat.choose (n - 2) (d - 2) : ℝ) := by
    exact_mod_cast hmul
  have hd2 : (0 : ℝ) < (d : ℝ) * ((d : ℝ) - 1) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    nlinarith
  have hmul2 : (Nat.choose n d : ℝ) * ((d : ℝ) * ((d : ℝ) - 1)) =
      ((n : ℝ) * ((n : ℝ) - 1)) * (Nat.choose (n - 2) (d - 2) : ℝ) := by
    have h := hmulR
    rw [Nat.cast_choose_two, Nat.cast_choose_two] at h
    field_simp at h
    linarith
  rw [div_eq_div_iff (ne_of_gt hpos) (ne_of_gt hd2)]
  exact hmul2

/-- The switch ratio `√(|Y| / |Y_e|)` is bounded above by `n` and below by
`n/(2d)`; for fixed `d` this is `Θ(n)`. -/
theorem sqrt_choose_ratio_bounds {n d : ℕ} (h2 : 2 ≤ d) (hdn : d ≤ n) :
    (n : ℝ) / (2 * (d : ℝ)) ≤
        Real.sqrt ((Nat.choose n d : ℝ) / (Nat.choose (n - 2) (d - 2) : ℝ)) ∧
      Real.sqrt ((Nat.choose n d : ℝ) / (Nat.choose (n - 2) (d - 2) : ℝ)) ≤
        (n : ℝ) := by
  have h2R : (2 : ℝ) ≤ d := by exact_mod_cast h2
  have hnR : (2 : ℝ) ≤ n := le_trans h2R (by exact_mod_cast hdn)
  have hdpos : (0 : ℝ) < d := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) * ((d : ℝ) - 1) := by nlinarith
  rw [choose_ratio h2 hdn]
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    rw [show (2 * (d : ℝ)) ^ 2 = 4 * (d : ℝ) ^ 2 by ring]
    rw [div_le_div_iff₀ (by positivity) hd1]
    nlinarith [sq_nonneg ((n : ℝ) - 1), hnR]
  · rw [Real.sqrt_le_iff]
    constructor
    · positivity
    rw [div_le_iff₀ hd1]
    have hprod : (2 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by nlinarith [h2R]
    nlinarith [sq_nonneg ((n : ℝ) - 1), hnR, hprod]

end
end Qatlib.Papers.MinorClosed10.MainResults.SwitchCounting
