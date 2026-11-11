/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs
import Qatlib.Papers.GraphConnect03.MainResults.UpperBounds.Theorem1Connectivity

/-!
# Strong connectivity from a two-stage list certificate

This module defines `WhiteReach` and `TwoStageCertificate` for the list-model
strong-connectivity reduction in [DurrMhallaLei2003]. It proves that the union `TwoStageEdges`
of certified tree and back edges is strongly connected exactly when the original graph is
strongly connected, and bounds the associated query-cost expression.

## Main statements

* `theorem2_strongConnectivity_iff`: equivalence between original and certified strong
  connectivity.
* `strongConnectivityListCost_bigO`: an O(n √k log n) bound for fixed list degree.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.StrongList

open Classical
open Qatlib.Papers.GraphConnect03.MainResults.Defs

attribute [local instance] Classical.propDecidable

/-- A graph is strongly connected if an edge subrelation connects every ordered pair of
vertices. -/
theorem strongConnected_of_subgraph {n k : ℕ} {L : ListInstance n k}
    {sub : Vertex n → Vertex n → Prop}
    (hsub : ∀ u v, sub u v → L.HasEdge u v) :
    (∀ s t, Relation.ReflTransGen sub s t) → L.StrongConnected := by
  intro h s t
  exact Relation.ReflTransGen.mono (fun a b hab => hsub a b hab) _ _ (h s t)

/-- The union of the tree and back edge relations. -/
def TwoStageEdges {n k : ℕ} (L : ListInstance n k)
    (tree back : Vertex n → Vertex n → Prop) : Vertex n → Vertex n → Prop :=
  fun u v => tree u v ∨ back u v

/-- Reachability from `u` using edges whose endpoints have discovery indices at least `disc u`. -/
def WhiteReach {n k : ℕ} (L : ListInstance n k) (disc : Vertex n → ℕ) (u : Vertex n)
    (v : Vertex n) : Prop :=
  Relation.ReflTransGen
    (fun a b => L.HasEdge a b ∧ disc u ≤ disc a ∧ disc u ≤ disc b) u v

/-- Every vertex is white-reachable from itself. -/
theorem whiteReach_refl {n k : ℕ} {L : ListInstance n k} {disc : Vertex n → ℕ}
    (u : Vertex n) : WhiteReach L disc u u :=
  Relation.ReflTransGen.refl

/-- White reachability from `u` to `v` implies `disc u ≤ disc v`. -/
theorem whiteReach_end_disc {n k : ℕ} {L : ListInstance n k} {disc : Vertex n → ℕ}
    {u v : Vertex n} (h : WhiteReach L disc u v) : disc u ≤ disc v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc _ => exact hbc.2.2

/-- White reachability implies reachability in the original graph. -/
theorem whiteReach_reach {n k : ℕ} {L : ListInstance n k} {disc : Vertex n → ℕ}
    {u v : Vertex n} (h : WhiteReach L disc u v) : L.Reach u v :=
  Relation.ReflTransGen.mono (fun _ _ hab => hab.1) _ _ h

/-- A white path extends across an edge whose target has discovery index at least that of its
starting vertex. -/
theorem whiteReach_step {n k : ℕ} {L : ListInstance n k} {disc : Vertex n → ℕ}
    {u a b : Vertex n} (h : WhiteReach L disc u a) (he : L.HasEdge a b)
    (hb : disc u ≤ disc b) : WhiteReach L disc u b :=
  h.tail ⟨he, whiteReach_end_disc h, hb⟩

/-- A reachable target is either white-reachable or some white-reachable vertex has an edge to a
vertex discovered before the starting vertex [DurrMhallaLei2003]. -/
theorem whiteReach_or_split {n k : ℕ} {L : ListInstance n k} {disc : Vertex n → ℕ}
    {u t : Vertex n} (h : L.Reach u t) :
    WhiteReach L disc u t ∨
      ∃ a b : Vertex n, WhiteReach L disc u a ∧ L.HasEdge a b ∧ disc b < disc u := by
  induction h with
  | refl => exact Or.inl (whiteReach_refl u)
  | tail _sub hct ih =>
      rename_i mid fin
      rcases ih with hw | ⟨a, b, hwa, hab, hb⟩
      · by_cases hbt : disc fin < disc u
        · exact Or.inr ⟨mid, fin, hw, hct, hbt⟩
        · exact Or.inl (whiteReach_step hw hct (Nat.not_lt.mp hbt))
      · exact Or.inr ⟨a, b, hwa, hab, hb⟩

/-- Discovery indices, a rooted spanning tree satisfying the white-path property, and back edges
attaining discovery indices no greater than those of any outgoing neighbor
[DurrMhallaLei2003]. -/
structure TwoStageCertificate (n k : ℕ) (L : ListInstance n k) where

  disc : Vertex n → ℕ

  disc_injective : Function.Injective disc

  tree : Vertex n → Vertex n → Prop

  tree_edge : ∀ u v, tree u v → L.HasEdge u v

  root : Vertex n

  root_min : ∀ v, disc root ≤ disc v

  spanning : ∀ v, Relation.ReflTransGen tree root v

  white_path : ∀ u v, WhiteReach L disc u v → disc u < disc v →
    Relation.ReflTransGen tree u v

  back : Vertex n → Vertex n → Prop

  back_edge : ∀ u v, back u v → L.HasEdge u v

  back_min : ∀ u v, L.HasEdge u v → ∃ w, back u w ∧ disc w ≤ disc v

/-- Reachability of the certificate's root from `v` using tree and back edges. -/
def ReachesRoot {n k : ℕ} {L : ListInstance n k} (C : TwoStageCertificate n k L)
    (v : Vertex n) : Prop :=
  Relation.ReflTransGen (TwoStageEdges L C.tree C.back) v C.root

/-- Strong connectivity of the certified tree and back edge relation implies strong connectivity
of the original graph [DurrMhallaLei2003]. -/
theorem theorem2_reduction_easy {n k : ℕ} {L : ListInstance n k}
    (C : TwoStageCertificate n k L) :
    (∀ s t, Relation.ReflTransGen (TwoStageEdges L C.tree C.back) s t) →
      L.StrongConnected :=
  strongConnected_of_subgraph (by
    intro u v huv
    rcases huv with htree | hback
    · exact C.tree_edge u v htree
    · exact C.back_edge u v hback)

/-- For a two-stage certificate on a strongly connected graph, tree and back edges connect every
ordered pair of vertices [DurrMhallaLei2003]. -/
theorem theorem2_reduction_hard {n k : ℕ} {L : ListInstance n k}
    (C : TwoStageCertificate n k L) (hsc : L.StrongConnected) :
    ∀ s t : Vertex n, Relation.ReflTransGen (TwoStageEdges L C.tree C.back) s t := by
  have htoRoot : ∀ v : Vertex n, ReachesRoot C v := by
    by_contra hnot
    rw [not_forall] at hnot
    obtain ⟨v₀, hv₀⟩ := hnot
    have hS : (Finset.univ.filter (fun v : Vertex n => ¬ ReachesRoot C v)).Nonempty :=
      ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀⟩⟩
    obtain ⟨v, hvS, hmin⟩ :=
      Finset.exists_min_image (Finset.univ.filter (fun v : Vertex n => ¬ ReachesRoot C v))
        C.disc hS
    have hv : ¬ ReachesRoot C v := (Finset.mem_filter.mp hvS).2
    have hv_root : v ≠ C.root := by
      intro h
      exact hv (h ▸ Relation.ReflTransGen.refl)
    have hv_disc : C.disc C.root < C.disc v :=
      lt_of_le_of_ne (C.root_min v) (fun h => hv_root (C.disc_injective h.symm))
    have hgood : ∀ w : Vertex n, C.disc w < C.disc v → ReachesRoot C w := by
      intro w hw
      by_contra hwbad
      have hwS : w ∈ Finset.univ.filter (fun u : Vertex n => ¬ ReachesRoot C u) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwbad⟩
      have := hmin w hwS
      omega
    rcases whiteReach_or_split (L := L) (disc := C.disc) (u := v) (t := C.root)
        (hsc v C.root) with hwhite | ⟨a, b, hwa, hab, hb⟩
    · exact absurd (whiteReach_end_disc hwhite) (not_le.mpr hv_disc)
    · obtain ⟨w, hbw, hbwd⟩ := C.back_min a b hab
      have hwlt : C.disc w < C.disc v := lt_of_le_of_lt hbwd hb
      have hwgood : ReachesRoot C w := hgood w hwlt
      have hle : C.disc v ≤ C.disc a := whiteReach_end_disc hwa
      by_cases hlt : C.disc v < C.disc a
      · have htree : Relation.ReflTransGen C.tree v a := C.white_path v a hwa hlt
        have hva : Relation.ReflTransGen (TwoStageEdges L C.tree C.back) v a :=
          Relation.ReflTransGen.mono (fun x y hxy => Or.inl hxy) _ _ htree
        have haw : Relation.ReflTransGen (TwoStageEdges L C.tree C.back) a w :=
          Relation.ReflTransGen.single (Or.inr hbw)
        exact hv (hva.trans (haw.trans hwgood))
      · have heq : C.disc a = C.disc v := le_antisymm (Nat.not_lt.mp hlt) hle
        have hav : a = v := C.disc_injective heq
        have hvw : Relation.ReflTransGen (TwoStageEdges L C.tree C.back) v w :=
          hav ▸ Relation.ReflTransGen.single (Or.inr hbw)
        exact hv (hvw.trans hwgood)
  intro s t
  exact (htoRoot s).trans
    (Relation.ReflTransGen.mono (fun x y hxy => Or.inl hxy) _ _ (C.spanning t))

/-- For a two-stage certificate, the original graph is strongly connected if and only if tree
and back edges connect every ordered pair of vertices [DurrMhallaLei2003]. -/
theorem theorem2_strongConnectivity_iff {n k : ℕ} {L : ListInstance n k}
    (C : TwoStageCertificate n k L) :
    L.StrongConnected ↔
      ∀ s t : Vertex n, Relation.ReflTransGen (TwoStageEdges L C.tree C.back) s t :=
  ⟨theorem2_reduction_hard C, theorem2_reduction_easy C⟩

/-- For `n ≥ 2`, the strong-connectivity list-cost expression is at most `3 * (n * √k * log n)`
for any visited set. -/
theorem strongConnectivityListCost_le (n k : ℕ) (visited : Finset (Vertex n))
    (hn : 2 ≤ n) :
    strongConnectivityListCost n k visited ≤
      3 * ((n : ℝ) * Real.sqrt (k : ℝ) * Real.log (n : ℝ)) := by
  unfold strongConnectivityListCost backwardEdgeCost listGroverCharge
  have h1 : dfsListCost n k visited ≤ 2 * ((n : ℝ) * Real.sqrt (k : ℝ) * Real.log (n : ℝ)) :=
    Qatlib.Papers.GraphConnect03.MainResults.UpperBounds.dfsListCost_le n k visited hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hnonneg : 0 ≤ (n : ℝ) * Real.sqrt (k : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hlog
  nlinarith [h1, hnonneg]

/-- For fixed `k`, the strong-connectivity list cost with all vertices visited is O(n √k log n)
from `n = 2` onward [DurrMhallaLei2003]. -/
theorem strongConnectivityListCost_bigO (k : ℕ) :
    IsBigOFrom
      (fun n : ℕ => strongConnectivityListCost n k (Finset.univ : Finset (Vertex n)))
      (fun n : ℕ => (n : ℝ) * Real.sqrt (k : ℝ) * Real.log (n : ℝ)) 2 :=
  ⟨3, by norm_num, fun n hn => strongConnectivityListCost_le n k Finset.univ hn⟩

end Qatlib.Papers.GraphConnect03.StrongList
