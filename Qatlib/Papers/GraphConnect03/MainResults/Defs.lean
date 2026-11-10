/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.Defs

open Filter

abbrev Vertex (n : ℕ) := Fin n

structure Digraph (n : ℕ) where

  adj : Vertex n → Vertex n → Bool

namespace Digraph

variable {n : ℕ}

def Reach (G : Digraph n) (s t : Vertex n) : Prop :=
  Relation.ReflTransGen (fun u v => G.adj u v = true) s t

theorem Reach.refl (G : Digraph n) (s : Vertex n) : G.Reach s s :=
  Relation.ReflTransGen.refl

theorem Reach.trans {G : Digraph n} {a b c : Vertex n}
    (hab : G.Reach a b) (hbc : G.Reach b c) : G.Reach a c :=
  Relation.ReflTransGen.trans hab hbc

theorem Reach.edge {G : Digraph n} {u v : Vertex n} (h : G.adj u v = true) :
    G.Reach u v :=
  Relation.ReflTransGen.single h

theorem Reach.mono {G H : Digraph n} (hGH : ∀ u v, G.adj u v = true → H.adj u v = true)
    {s t : Vertex n} (h : G.Reach s t) : H.Reach s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hGH _ _ hbc)

def Connected (G : Digraph n) : Prop := ∀ s t : Vertex n, G.Reach s t

theorem connected_iff (G : Digraph n) :
    G.Connected ↔ ∀ s t : Vertex n, G.Reach s t := Iff.rfl

end Digraph

structure UndirectedMatrix (n : ℕ) where

  adj : Vertex n → Vertex n → Bool

  symm : ∀ u v, adj u v = adj v u

  loopless : ∀ u, adj u u = false

namespace UndirectedMatrix

variable {n : ℕ}

def toDigraph (M : UndirectedMatrix n) : Digraph n := ⟨M.adj⟩

def Connected (M : UndirectedMatrix n) : Prop := M.toDigraph.Connected

theorem connected_iff (M : UndirectedMatrix n) :
    M.Connected ↔ ∀ s t : Vertex n, M.toDigraph.Reach s t := Iff.rfl

theorem reach_symm (M : UndirectedMatrix n) {s t : Vertex n}
    (h : M.toDigraph.Reach s t) : M.toDigraph.Reach t s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      refine Relation.ReflTransGen.head ?_ ih
      simpa [toDigraph] using (M.symm _ _).trans hbc

end UndirectedMatrix

structure ListInstance (n k : ℕ) where

  nbr : Vertex n → Fin k → Vertex n

  simple : ∀ u, Function.Injective (nbr u)

namespace ListInstance

variable {n k : ℕ}

def HasEdge (L : ListInstance n k) (u v : Vertex n) : Prop :=
  ∃ i : Fin k, L.nbr u i = v

def Reach (L : ListInstance n k) (s t : Vertex n) : Prop :=
  Relation.ReflTransGen (fun u v => L.HasEdge u v) s t

theorem Reach.refl (L : ListInstance n k) (s : Vertex n) : L.Reach s s :=
  Relation.ReflTransGen.refl

theorem Reach.trans {L : ListInstance n k} {a b c : Vertex n}
    (hab : L.Reach a b) (hbc : L.Reach b c) : L.Reach a c :=
  Relation.ReflTransGen.trans hab hbc

theorem Reach.edge {L : ListInstance n k} {u v : Vertex n} (h : L.HasEdge u v) :
    L.Reach u v :=
  Relation.ReflTransGen.single h

def StrongConnected (L : ListInstance n k) : Prop := ∀ s t : Vertex n, L.Reach s t

def UndirectedPromise (L : ListInstance n k) : Prop :=
  ∀ u v : Vertex n, L.HasEdge u v → L.HasEdge v u

def Connected (L : ListInstance n k) : Prop :=
  ∀ s t : Vertex n, Relation.SymmGen (fun u v => L.HasEdge u v) s t

end ListInstance

def matrixGroverCharge (n : ℕ) : ℝ := Real.sqrt (n : ℝ) * Real.log (n : ℝ)

def listGroverCharge (n k : ℕ) : ℝ := Real.sqrt (k : ℝ) * Real.log (n : ℝ)

def dfsSearchCount {n : ℕ} (visited : Finset (Vertex n)) : ℕ := 2 * visited.card

def dfsMatrixCost {n : ℕ} (visited : Finset (Vertex n)) : ℝ :=
  (dfsSearchCount visited : ℝ) * matrixGroverCharge n

def dfsListCost (n k : ℕ) (visited : Finset (Vertex n)) : ℝ :=
  (dfsSearchCount visited : ℝ) * listGroverCharge n k

def backwardEdgeCost (n k : ℕ) : ℝ := (n : ℝ) * listGroverCharge n k

def strongConnectivityListCost (n k : ℕ) (visited : Finset (Vertex n)) : ℝ :=
  dfsListCost n k visited + backwardEdgeCost n k

opaque matrixConnectivityQueryComplexity : ℕ → ℝ

opaque listStrongConnectivityQueryComplexity : ℕ → ℕ → ℝ

def IsOmegaFrom (f q : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n → c * f n ≤ q n

def IsBigOFrom (q f : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n → q n ≤ c * f n

end Qatlib.Papers.GraphConnect03.MainResults.Defs
