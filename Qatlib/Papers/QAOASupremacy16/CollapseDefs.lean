/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.GapModels
import Qatlib.Papers.QAOASupremacy16.CondProb
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.QAOASupremacy16.CollapseDefs

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.GapModels
open Qatlib.Foundations.ProbabilityCore.Conditioning
open Qatlib.Papers.QAOASupremacy16.CircuitDefs

def RelativeGapTransportData : Prop :=
  ∀ L : Language, HasQuantumGap L →
    ∃ k : ℕ, ∃ q p : (n : ℕ) → Reg n → Bool × Reg k → ℝ,
      (∀ n x z, 0 ≤ q n x z) ∧
      (∀ n x z, 0 ≤ p n x z) ∧
      (∀ n x z, |p n x z - q n x z| ≤ (1 / 10) * q n x z) ∧
      (∀ n x, 0 < q n x (false, ZeroStr k) + q n x (true, ZeroStr k)) ∧
      (∀ n x, L n x = true → 2 / 3 ≤ postSelect (q n x) (ZeroStr k) true) ∧
      (∀ n x, L n x = false → postSelect (q n x) (ZeroStr k) true ≤ 1 / 3)

theorem relative_data_implies_gap
    (H : RelativeGapTransportData) :
    ∀ L : Language, HasQuantumGap L → HasClassicalGap L := by
  intro L hL
  obtain ⟨k, q, p, hqnn, hpnn, hclose, hden, hyes, hno⟩ := H L hL
  refine ⟨0.54, 0.41, by norm_num, ?_⟩
  refine ⟨⟨fun n x => postSelect (p n x) (ZeroStr k) true, ?_, ?_, ?_⟩⟩
  · intro n x
    exact postSelect_nonneg (hclose n x) (hqnn n x (false, ZeroStr k))
      (hqnn n x (true, ZeroStr k)) (hden n x)
  · intro n x hx
    exact postSelect_yes_lower (hclose n x) (hqnn n x (false, ZeroStr k))
      (hqnn n x (true, ZeroStr k)) (hden n x) (hyes n x hx)
  · intro n x hx
    exact postSelect_no_upper (hclose n x) (hqnn n x (false, ZeroStr k))
      (hqnn n x (true, ZeroStr k)) (hden n x) (hno n x hx)

theorem supplied_hierarchy_stabilization
    {PH : LanguageHierarchy} (facts : ConditionalCollapseData PH)
    (H : RelativeGapTransportData) :
    HierarchyStabilizes PH 3 :=
  facts.stabilizes_of_gap_transport
    (relative_data_implies_gap H)

theorem supplied_gap_level3
    {PH : LanguageHierarchy} (facts : ConditionalCollapseData PH)
    (H : RelativeGapTransportData) :
    ∀ L : Language, HasQuantumGap L → L ∈ PH 3 := by
  intro L hL
  exact facts.classicalGap_in_level3 L
    (relative_data_implies_gap H L hL)

end Qatlib.Papers.QAOASupremacy16.CollapseDefs
