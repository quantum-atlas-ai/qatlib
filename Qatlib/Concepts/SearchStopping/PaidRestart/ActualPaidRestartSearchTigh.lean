/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.ActualPaidRestartSearchStat
import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartExpectedReceiptTigh
set_option warningAsError false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

theorem actualPaidRestartSearch : ActualPaidRestartSearch := by
  intro I _ _ hN T' seed hT hprep t θ hθ hθupper hangle
  (try dsimp only)
  obtain ⟨j,hj,hhalf⟩ := half_budget_angle θ hθ hθupper
  let hC := (actualRestartSearchWord I hN T' (Ket seed) hT (normalized_ket seed)
    hprep ∅ j).1
  refine ⟨j,hC,hj,?_⟩
  intro A hcard
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθupper⟩).ne'
  have hsuccess : 1/2 ≤ MeasureProb (GroverState A j) A := by
    rw [measureProb_groverState hN A θ (by simpa only [hcard] using hangle) hs hc j]
    exact hhalf
  have hp : 0 < MeasureProb (GroverState A j) A := by linarith
  have hq := (actualRestartExpectedReceipt I hN T' (Ket seed) hT (normalized_ket seed)
    hprep A j hC (j+1) (by omega)).2 hp
  have hm := (actualRestartExpectedReceipt I hN T' (Ket seed) hT (normalized_ket seed)
    hprep A j hC (j+2) (by omega)).2 hp
  have he := (actualRestartExpectedReceipt I hN T' (Ket seed) hT (normalized_ket seed)
    hprep A j hC 2 (by decide)).2 hp
  have hd (c : ℝ) (hc0 : 0 ≤ c) : c/MeasureProb (GroverState A j) A ≤ 2*c := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hpi : 2*(Real.pi/(8*θ)) = Real.pi/(4*θ) := by field_simp [ne_of_gt hθ]; ring
  refine ⟨hq.1, ?_, ?_, ?_, ?_⟩
  · change generalUnboundedTime (branchClockNext (bbhtActualRestartNextPrice
      T' (Ket seed) j A hC (normalized_ket seed) (j+1))) _ ≤ _
    rw [hq.2.1]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    have hb := hd ((j+1 : ℕ) : ℝ) (by positivity)
    push_cast at hb
    linarith
  · rw [hm.2.1]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    have hb := hd ((j+2 : ℕ) : ℝ) (by positivity)
    push_cast at hb
    linarith
  · rw [he.2.1]
    have hb := ENNReal.ofReal_le_ofReal (hd 2 (by norm_num))
    norm_num at hb ⊢
    exact hb
  · exact (actualRestartFirstSuccess I hN T' (Ket seed) hT (normalized_ket seed)
      hprep A j hC (j+1) (by omega)).2.1

end Qatlib.Concepts.SearchStopping.PaidRestart
