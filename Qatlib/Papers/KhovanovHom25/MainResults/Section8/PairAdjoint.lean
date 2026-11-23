/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairBridge

/-!
# Exact coordinate adjacency of the two-particle source graph

An adjacent transposition preserves the order of the two particles whenever
it is a genuine particle-hole move. Thus every source edge is precisely one
coordinate nearest-neighbor move, and its actual weight is the indicator of
the triangular coordinate adjacency.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Qatlib.Papers.KhovanovHom25.MainResults.PairBridge

open Qatlib.Papers.KhovanovHom25.MainResults

/-- An adjacent transposition preserves strict order except on its two occupied endpoints. -/
theorem swap_order {N : ℕ} (i : Fin N) (a b : Fin (N + 1)) (hab : a < b)
    (hnot : ¬ (a = i.castSucc ∧ b = i.succ)) :
    (Equiv.swap i.castSucc i.succ) a < (Equiv.swap i.castSucc i.succ) b := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;>
    simp_all only [Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
      true_and, not_true_eq_false] <;> omega

/-- Every actual two-particle source move is a triangular coordinate edge. -/
theorem hop_pair {N : ℕ} (p q : PairFlow.Pair N)
    (h : PathModel.Hop (vertex p) (vertex q)) : PairFlow.Adj p q := by
  obtain ⟨i, hxor, hw⟩ := h
  have hnot : ¬ (p.val.1 = i.castSucc ∧ p.val.2 = i.succ) := by
    rintro ⟨ha, hb⟩
    exact hxor (by simp [vertex, ← ha, ← hb])
  let p' : PairFlow.Pair N :=
    ⟨((Equiv.swap i.castSucc i.succ) p.val.1, (Equiv.swap i.castSucc i.succ) p.val.2),
      swap_order i _ _ p.property hnot⟩
  have hv : vertex p' = vertex q := by
    calc
      _ = PathModel.flip (vertex p) i := by
        simp only [vertex, p', PathModel.flip, Finset.map_insert, Finset.map_singleton,
          Equiv.coe_toEmbedding]
      _ = _ := hw.symm
  have heq : p' = q := vertex_injective hv
  rw [← heq]
  have hd : ¬ ((i.val = p.val.1.val ∨ i.val = p.val.2.val) ↔
      (i.val + 1 = p.val.1.val ∨ i.val + 1 = p.val.2.val)) := by
    intro he
    apply hxor
    apply propext
    simpa only [vertex, Finset.mem_insert, Finset.mem_singleton,
      Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] using he
  simp only [PairFlow.Adj, PairFlow.left, PairFlow.right, p', swap_val]
  split_ifs <;> omega

/-- The source edge relation and the actual triangular coordinate relation coincide. -/
theorem pair_hop_iff {N : ℕ} (p q : PairFlow.Pair N) :
    PathModel.Hop (vertex p) (vertex q) ↔ PairFlow.Adj p q := ⟨hop_pair p q, pair_hop p q⟩

/-- Actual source weights are exactly the triangular coordinate adjacency indicators. -/
theorem pair_edge {N : ℕ} (p q : PairFlow.Pair N) :
    edgeWeightAt N (twistedUnknotEdges N) (vertex p) (vertex q) =
      if PairFlow.Adj p q then 1 else 0 := by
  rw [path_edge_indicator]
  exact if_congr (pair_hop_iff p q) rfl rfl

end Qatlib.Papers.KhovanovHom25.MainResults.PairBridge
