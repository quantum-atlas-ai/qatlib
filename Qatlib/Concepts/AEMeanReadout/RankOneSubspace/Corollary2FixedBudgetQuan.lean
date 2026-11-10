/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Corollary2FixedBudgetStat
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem5ApproximateCountingQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

theorem corollary2FixedBudget : Corollary2FixedBudget := by
  intro N P S c hN hS hc hPc hP
  refine ⟨(prepared_ae_access_ledger P (by omega) (QFTMatrix N) ⟨0, hN⟩).1, ?_⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hsn : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hn
  have he : 2*Real.pi/(P : ℝ)*Real.sqrt ((S.card : ℝ)*N)+Real.pi^2/(P : ℝ)^2*N =
      2*Real.pi/c*Real.sqrt (S.card : ℝ)+Real.pi^2/c^2 := by
    rw [hPc, Real.sqrt_mul (by positivity : 0 ≤ (S.card : ℝ))]
    field_simp [ne_of_gt hc, ne_of_gt hsn]
    rw [Real.sq_sqrt (le_of_lt hn)]
    ring
  have hh := theorem5ApproximateCounting N P S hN hS hP
  simpa only [he] using hh

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
