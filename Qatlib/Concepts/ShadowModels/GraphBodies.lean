/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliInvolution
import Qatlib.Foundations.FiniteStats.BornEstimator.JointApparatus

/-!
# Pauli anticommutation graphs

This module proves that products of Pauli words are nonzero and that any two Pauli words commute
or anticommute. `pauliGraph` encodes anticommutation as adjacency, giving a graph representation
of incompatibility among a family of Pauli observables. See [XuEtAl2026] for background.

## Main statements

* `pauli_commute_or_anticommute`: the commutation dichotomy for Pauli words.
* `pauliGraph_adj_iff`: graph adjacency is exactly operator anticommutation.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.GraphBodies
open scoped Classical BigOperators
open Qatlib.Concepts.ShadowModels.ProductPOVM
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath

/-- The product of two Pauli word operators is nonzero. -/
theorem pauliProduct_ne_zero (n : ℕ) (w v : PauliWord n) : pauliWordOp n w*pauliWordOp n v≠0 := by
  intro hz
  have h := (pauliUnitary n w*pauliUnitary n v).property.1
  change star (pauliWordOp n w*pauliWordOp n v)*(pauliWordOp n w*pauliWordOp n v)=1 at h
  rw [hz,mul_zero] at h
  exact zero_ne_one h

/-- Any two Pauli word operators either commute or anticommute. -/
theorem pauli_commute_or_anticommute (n : ℕ) (w v : PauliWord n) :
    Commute (pauliWordOp n w) (pauliWordOp n v) ∨
      pauliWordOp n w*pauliWordOp n v=-(pauliWordOp n v*pauliWordOp n w) := by
  have h := pauliWordOp_symplectic n w v
  generalize he : symplecticForm (symplecticX w,symplecticZ w) (symplecticX v,symplecticZ v)=a at h
  fin_cases a
  · exact Or.inl (by simpa only [Commute,SemiconjBy,ZMod.val,pow_zero,one_smul] using h)
  · exact Or.inr (by simpa only [ZMod.val,pow_one,neg_one_smul] using h)

/-- Anticommuting Pauli word operators do not commute. -/
theorem pauli_anticommute_not_commute (n : ℕ) (w v : PauliWord n)
    (ha : pauliWordOp n w*pauliWordOp n v=-(pauliWordOp n v*pauliWordOp n w)) :
    ¬Commute (pauliWordOp n w) (pauliWordOp n v) := by
  intro hc
  have he := hc.eq.symm.trans ha
  have hz : pauliWordOp n v*pauliWordOp n w=0 := by
    ext i j
    have hh := congrFun₂ he i j
    change (pauliWordOp n v*pauliWordOp n w) i j=-(pauliWordOp n v*pauliWordOp n w) i j at hh
    change (pauliWordOp n v*pauliWordOp n w) i j=0
    linear_combination (1/2:ℂ)*hh
  exact pauliProduct_ne_zero n v w hz

/-- The simple graph on a family of Pauli words whose edges join pairs with noncommuting
operators. -/
def pauliGraph {V : Type*} (n : ℕ) (words : V → PauliWord n) : SimpleGraph V :=
  commutationGraph (fun i => pauliObservable n (words i))

/-- Two vertices of the Pauli graph are adjacent exactly when their operators anticommute, as in
the Pauli frustration graph of [XuEtAl2026]. -/
theorem pauliGraph_adj_iff {V : Type*} (n : ℕ) (words : V → PauliWord n) (i j : V) :
    (pauliGraph n words).Adj i j ↔
      pauliWordOp n (words i)*pauliWordOp n (words j)=-(pauliWordOp n (words j)*pauliWordOp n (words i)) := by
  constructor
  · intro h
    rcases pauli_commute_or_anticommute n (words i) (words j) with hc|ha
    · exact False.elim (h hc)
    · exact ha
  · exact pauli_anticommute_not_commute n (words i) (words j)

end Qatlib.Concepts.ShadowModels.GraphBodies
