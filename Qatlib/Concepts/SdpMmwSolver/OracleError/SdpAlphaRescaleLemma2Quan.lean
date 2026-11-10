/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpAlphaRescaleLemma2Stat
import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpMmwSolver.OracleError
open scoped BigOperators
set_option warningAsError false

theorem not_sdpAlphaRescaleLemma2 : ¬ SdpAlphaRescaleLemma2OriginalContract := by
  intro h
  have hf := (h 1 1 (fun _ => 1) 1 1 (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by intro i; norm_num)
    (by norm_num) (by norm_num)).2 (fun _ => 3 / 2)
    (by intro i; norm_num) (by norm_num)
  norm_num at hf

theorem sdpAlphaRescaleObjective (m : ℕ) (b sol : Fin m → ℝ) (α : ℝ) :
    (∑ i, sol i * (b i / α)) = (∑ i, sol i * b i) / α := by
  simp only [← mul_div_assoc, Finset.sum_div]

theorem sdpAlphaRescaleAdditive (m : ℕ) (b sol : Fin m → ℝ) (α δ : ℝ)
    (hα : 0 < α) (h : (∑ i, sol i * (b i / α)) ≤ 1 + δ / α) :
    (∑ i, sol i * b i) ≤ α + δ := by
  rw [sdpAlphaRescaleObjective] at h
  have hb := (div_le_iff₀ hα).mp h
  have he : (1 + δ / α) * α = α + δ := by field_simp
  rwa [he] at hb

theorem sdpAlphaRescaleLemma2 : SdpAlphaRescaleLemma2 := by
  intro n m b R r α δ _hn _hm hR _hr hα _hδ hb _hαR _hrαR
  constructor
  · refine ⟨Fin.snoc b (R + 1), ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        linarith
      · simpa only [Fin.snoc_castSucc] using! hb j
    · simp only [Fin.snoc_last]
    · intro i
      simp only [Fin.snoc_castSucc]
  · intro sol _hsol hscaled
    rw [sdpAlphaRescaleObjective] at hscaled
    exact (div_le_iff₀ hα).mp hscaled

end Qatlib.Concepts.SdpMmwSolver.OracleError
