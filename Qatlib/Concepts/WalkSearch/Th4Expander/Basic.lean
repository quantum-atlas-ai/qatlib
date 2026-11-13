/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverQuan
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainQuan
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4MarkedMassQuan
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4WalkOracleQuan

/-!
# Expander walk detection bounds

This module assembles the regular-graph transition kernel, the marked-fraction lower bound, and
a unitary realization of Szegedy frame preparation. `source_theorem_four_expander_chain` also
records that a lifted vertex basis state is supported on its incident directed edges.

With an explicit symmetric-chain gap and a nonempty marked set, `source_theorem_four_grover`
gives a constant average detection probability and quantitative program-count bounds at a search
length proportional to `sqrt (n / δ)`, in the walk-search framework of [Szegedy2004].

## Main statements

* `source_theorem_four_walk_oracle`: existence of unitary frame preparation.
* `source_theorem_four_grover`: detection probability and search-length bounds.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.Th4Expander
open Qatlib.Concepts.WalkSearch.WalkDetector
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.Th4Expander.Basic

/-- A nonempty undirected graph with positive constant degree defines a symmetric transition
matrix, and each lifted basis state is supported only on adjacent pairs with the prescribed
first vertex [Szegedy2004]. -/
theorem source_theorem_four_expander_chain
    (n d : ℕ) (adj : Fin n → Fin n → Bool)
    (hn : 0 < n) (hd : 0 < d)
    (hsym : ∀ i j, adj i j = adj j i)
    (hreg : ∀ i, (Finset.univ.filter (fun j => adj i j)).card = d) :
    IsTransitionMatrix (expanderStep n d adj) ∧
    (∀ i j, expanderStep n d adj i j = expanderStep n d adj j i) ∧
    (∀ i : Fin n, ∀ p : Fin n × Fin n,
      (SzegedyIsometry (expanderStep n d adj) *ᵥ Ket i) p ≠ 0 →
        p.1 = i ∧ adj i p.2) :=
  szegedyTheorem4ExpanderChain n d adj hn hd hsym hreg

/-- A nonempty marked set on `Fin n`, with positive `n`, has marked fraction at least `1 / n`. -/
theorem source_theorem_four_marked_mass
    (n : ℕ) (f : Fin n → Bool)
    (hn : 0 < n) (hmarked : ∃ i, f i = true) :
    (1 / (n : ℝ)) ≤ markedFraction (Finset.univ.filter (fun i => f i = true)) :=
  szegedyTheorem4MarkedMass n f hn hmarked

/-- For a transition matrix and a fixed ancillary basis state, there is a unitary sending every
input vertex basis state to its Szegedy frame image. -/
theorem source_theorem_four_walk_oracle
    (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ) (j : I)
    (hP : IsTransitionMatrix P) :
    ∃ U : Matrix (I × I) (I × I) ℂ,
      U ∈ Matrix.unitaryGroup (I × I) ℂ ∧
      ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i :=
  szegedyTheorem4WalkOracle I P j hP

/-- Under the chain-gap, nonempty-marked-set, and unitary-preparation hypotheses, the average
detection probability is at least `1 / 32`. The three program counts are bounded by the
stated linear expressions in a search length at most `1000 * sqrt (n / δ) + 1`
[Szegedy2004]. -/
theorem source_theorem_four_grover
    (n d : ℕ) (adj : Fin n → Fin n → Bool) (f : Fin n → Bool) (δ : ℝ)
    (j : Fin n) (U : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hn : 0 < n) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : SymmetricChainGap (expanderStep n d adj) δ)
    (hmarked : ∃ i, f i = true)
    (hU : U ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ)
    (hprepare : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) =
      SzegedyIsometry (expanderStep n d adj) *ᵥ Ket i) :
    (1 / 32 : ℝ) ≤
      (∑ k : Fin (expanderSearchLength n δ),
        detectionProbability U (Finset.univ.filter (fun i => f i = true)) j (k.val + 1)) /
        ((expanderSearchLength n δ : ℝ)) ∧
    (∀ k : Fin (expanderSearchLength n δ),
      (detectionCounts (detectionProgram j (k.val + 1))).1 ≤
        4 * (expanderSearchLength n δ) + 1 ∧
      (detectionCounts (detectionProgram j (k.val + 1))).2.1 ≤
        4 * (expanderSearchLength n δ) + 1 ∧
      (detectionCounts (detectionProgram j (k.val + 1))).2.2 ≤
        4 * (expanderSearchLength n δ) + 2) ∧
    ((expanderSearchLength n δ : ℝ) ≤ 1000 * Real.sqrt ((n : ℝ) / δ) + 1) :=
  szegedyTheorem4ExpanderGrover n d adj f δ j U hn hδ hδ1 hgap hmarked hU hprepare

end Qatlib.Concepts.WalkSearch.Th4Expander.Basic
