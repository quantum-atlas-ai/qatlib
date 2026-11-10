/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleDiagnostics
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

def degreeTestLowCorrected (G : UGraph n) (v : Fin n) (K c : ℕ) (tape : Fin K→Fin c→Fin n) : Bool :=
  decide (2*hitRounds G v K c tape+1 ≤ K)

def testCorrectCorrected (G : UGraph n) (v : Fin n) (dHi dLo K c : ℕ)
    (tape : Fin K→Fin c→Fin n) : Prop :=
  (dHi<degOf G.edges v→degreeTestLowCorrected G v K c tape=false) ∧
  (degOf G.edges v<dLo→degreeTestLowCorrected G v K c tape=true)

def reliableCapabilities (sgs : SafeGrover) (ets : EdgeTriSearch) : Prop :=
    3 ≤ sgs.cExp ∧ 3 ≤ ets.cExp

def capabilityFeeFactor (sgs : SafeGrover) (ets : EdgeTriSearch) : ℕ := max 1 (max sgs.κ ets.κ)

theorem emptyGraph_degreeTest_corrected (v : Fin n) (K c : ℕ) (hK : 0<K)
    (tape : Fin K→Fin c→Fin n) : degreeTestLowCorrected (emptyGraph n) v K c tape=true := by
  simpa [degreeTestLowCorrected,hitRounds,emptyGraph] using! hK

theorem rejecting_capabilities_not_reliable : ¬ reliableCapabilities rejectingGrover rejectingEdgeSearch := by
  norm_num [reliableCapabilities,rejectingGrover,rejectingEdgeSearch]

theorem source_dense_four_term_budget (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(1+(3/7:ℝ))+(n:ℝ)^(1+(1/7:ℝ)+(1/7:ℝ))+
      (n:ℝ)^((3-(1/7:ℝ))/2)+(n:ℝ)^((3-min (1/7:ℝ) ((3/7:ℝ)-(1/7:ℝ)-(1/7:ℝ)))/2) ≤
        4*(n:ℝ)^(10/7:ℝ) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [show (1+(3/7:ℝ))=(10/7:ℝ) by norm_num,
    show (1+(1/7:ℝ)+(1/7:ℝ))=(9/7:ℝ) by norm_num,
    show ((3-(1/7:ℝ))/2)=(10/7:ℝ) by norm_num,
    show ((3-min (1/7:ℝ) ((3/7:ℝ)-(1/7:ℝ)-(1/7:ℝ)))/2)=(10/7:ℝ) by norm_num]
  have hh := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (9/7:ℝ) ≤ 10/7)
  linarith
end Qatlib.Concepts.WalkSearch.Primitives
