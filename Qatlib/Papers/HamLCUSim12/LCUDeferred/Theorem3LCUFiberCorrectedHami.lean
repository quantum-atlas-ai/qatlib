/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.Theorem3LCUFiberCorrectedStat
import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedProtocol
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator

theorem theorem3LCUFiberCorrected : Theorem3LCUFiberCorrected := by
  intro k I _ _ _hk U _hU c hc hp hn ψ x
  have hy : IndependentLCUBit (cwControlBit k c) (-cwNegativeCircuitCorrected k c U) :=
    independentLCUBit_neg _ _ (chainCircuitCorrected_independent _ _ (cw_negative_tail_fresh k c U hc hn))
  have hratio : 0≤cwPositiveWeight k c/cwNegativeWeight k c :=
    div_nonneg (cw_positive_weight_pos k c hp).le (cw_negative_weight_pos k c hn).le
  unfold cwOutputCorrected ApplyGate cwZero
  rw [cwProtocolCorrected_decompose,lcuLevelGateCorrected_zero_corner _ _ hratio _ _ hy]
  have hP := (cw_prefixes_zero_corner k c U hp hn ψ x).1
  have hN := (cw_prefixes_zero_corner k c U hp hn ψ x).2
  unfold cwZero at hP hN
  change _=(((∑ q,c q • U q)*ᵥψ) x)/(((∑ q,|c q|):ℝ):ℂ)
  simp only [Matrix.neg_mulVec,Pi.neg_apply]
  rw [hP,hN,← cw_weight_sum k c,← cw_signed_weighted k c U]
  rw [Matrix.sub_mulVec,Pi.sub_apply]
  have ha : (cwPositiveWeight k c:ℂ)≠0 := by exact_mod_cast (cw_positive_weight_pos k c hp).ne'
  have hb : (cwNegativeWeight k c:ℂ)≠0 := by exact_mod_cast (cw_negative_weight_pos k c hn).ne'
  have hs : ((cwPositiveWeight k c+cwNegativeWeight k c:ℝ):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (add_pos (cw_positive_weight_pos k c hp) (cw_negative_weight_pos k c hn)))
  push_cast at ha hb hs ⊢
  field_simp [ha,hb,hs]
  ring

end Qatlib.Papers.HamLCUSim12.LCUDeferred
