/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainStat
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.WalkSearch.Detection
open Matrix

namespace Qatlib.Concepts.WalkSearch.Th4Expander

def SzegedyTheorem4ExpanderGrover : Prop :=
  ∀ (n d : ℕ) (adj : Fin n → Fin n → Bool) (f : Fin n → Bool) (δ : ℝ)
      (j : Fin n) (U : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    0 < n → 0 < δ → δ ≤ 1 →
    SymmetricChainGap (expanderStep n d adj) δ →
    (∃ i, f i = true) →
    U ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ →
    (∀ i, U *ᵥ TensorState (Ket i) (Ket j) =
      SzegedyIsometry (expanderStep n d adj) *ᵥ Ket i) →
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
    ((expanderSearchLength n δ : ℝ) ≤ 1000 * Real.sqrt ((n : ℝ) / δ) + 1)

end Qatlib.Concepts.WalkSearch.Th4Expander
