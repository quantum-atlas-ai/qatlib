/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpDualSampleOutputStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SdpDuality.ConeSeparation

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract
open scoped Classical BigOperators

theorem sdpDualSampleOutput : SdpDualSampleOutput := by
  intro D m y j₀ α R δ η hα hR hδ hy
  let T := sdpDualCertRounds D R δ η
  have hT : 0 < T := Nat.succ_pos _
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hnonneg (i : Fin m) : 0 ≤ sdpDualCertificate m δ α R j₀ y T i := by
    unfold sdpDualCertificate
    apply add_nonneg
    · split_ifs <;> positivity
    · exact div_nonneg (Finset.sum_nonneg fun t _ => hy t i) hTr.le
  have hscale : 0 < sdpDualSampleScale m δ α R j₀ y T := by
    have he := Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j₀)
    have hpos : 0 < sdpDualCertificate m δ α R j₀ y T j₀ := by
      unfold sdpDualCertificate
      rw [if_pos rfl]
      exact add_pos_of_pos_of_nonneg (by positivity)
        (div_nonneg (Finset.sum_nonneg fun t _ => hy t j₀) hTr.le)
    exact hpos.trans_le he
  refine ⟨hscale,?_,?_,?_,?_⟩
  · intro i
    exact div_nonneg (hnonneg i) hscale.le
  · unfold sdpDualSampleDist
    rw [← Finset.sum_div]
    exact div_self hscale.ne'
  · intro i
    unfold sdpDualSampleDist
    rw [mul_comm,div_mul_cancel₀ _ hscale.ne']
  · unfold sdpDualSampleScale sdpDualCertificate
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [← Finset.sum_div,Finset.sum_comm]

end Qatlib.Concepts.SdpMmwSolver.SdpContract
