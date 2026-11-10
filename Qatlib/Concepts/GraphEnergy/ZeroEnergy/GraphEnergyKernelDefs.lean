/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphEnergy.ZeroEnergy.LazyGraphDefs
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GraphEnergy.ZeroEnergy

open Qatlib.Concepts.GraphEnergy.ZeroEnergy

variable {V : Type} [Fintype V] [DecidableEq V]

def dirichletSum (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ x, ∑ y, stationary G x * kernel G x y * (f x - f y) ^ 2

def twoDisjointEdges : SimpleGraph (Fin 4) where
  Adj a b := a.val + b.val = 1 ∨ a.val + b.val = 5
  symm := ⟨by
    intro a b h
    rcases h with h | h <;> omega⟩
  loopless := ⟨fun a h => by rcases h with h | h <;> omega⟩

instance : DecidableRel twoDisjointEdges.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val + b.val = 1) ∨ (a.val + b.val = 5)))

def edgeWithIsolate : SimpleGraph (Fin 3) where
  Adj a b := a.val + b.val = 1
  symm := ⟨by
    intro a b h
    omega⟩
  loopless := ⟨fun a h => by omega⟩

instance : DecidableRel edgeWithIsolate.Adj := fun a b =>
  inferInstanceAs (Decidable (a.val + b.val = 1))

def singleEdgeFin2 : SimpleGraph (Fin 2) where
  Adj a b := a.val + b.val = 1
  symm := ⟨by
    intro a b h
    omega⟩
  loopless := ⟨fun a h => by omega⟩

instance : DecidableRel singleEdgeFin2.Adj := fun a b =>
  inferInstanceAs (Decidable (a.val + b.val = 1))

end Qatlib.Concepts.GraphEnergy.ZeroEnergy
