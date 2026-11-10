/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverQuan
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainQuan
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4MarkedMassQuan
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4WalkOracleQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

theorem source_theorem_four_marked_mass
    (n : ℕ) (f : Fin n → Bool)
    (hn : 0 < n) (hmarked : ∃ i, f i = true) :
    (1 / (n : ℝ)) ≤ markedFraction (Finset.univ.filter (fun i => f i = true)) :=
  szegedyTheorem4MarkedMass n f hn hmarked

theorem source_theorem_four_walk_oracle
    (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ) (j : I)
    (hP : IsTransitionMatrix P) :
    ∃ U : Matrix (I × I) (I × I) ℂ,
      U ∈ Matrix.unitaryGroup (I × I) ℂ ∧
      ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i :=
  szegedyTheorem4WalkOracle I P j hP

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
