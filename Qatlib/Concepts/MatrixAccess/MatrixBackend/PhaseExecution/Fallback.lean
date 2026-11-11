/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Program

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Exact original OQ #132@c0d79a391c008771dd64bd305ec2133c1b32c2d6 generic finite-producer cost slice.
The amplifier-only suffix and its private dependencies remain in OQ history.
These are actual producer counters, not host bit time or other-algorithm bounds. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Polynomial

/-- The actual initial packet has endpoint response one at every degree budget. -/
theorem initial_phase_response_endpoint (d : ℕ) :
    (responseP (gaussianRatComplex gone)
      ((List.replicate d gone).map gaussianRatComplex)).eval 1 = 1 := by
  induction d with
  | zero => simp
  | succ d ih => simpa [List.replicate_succ, responseP_cons] using ih

/-- An endpoint margin forces rejection of the actual initial packet. -/
theorem initial_phase_score_lower (p : List ℚ) (d : ℕ) (μ : ℚ)
    (hdegree : (realTarget p).degree ≤ (d : WithBot ℕ))
    (hmargin : (realTarget p).eval 1 ≤ 1 - (μ : ℝ)) :
    μ ≤ (scoreData p d ⟨gone, List.replicate d gone⟩).1.1 := by
  have h := scoreData_uniform_error p d ⟨gone, List.replicate d gone⟩
    (by simp) hdegree 1 (by norm_num)
  dsimp only at h
  norm_num only [Rat.cast_one,Complex.ofReal_one] at h
  rw [initial_phase_response_endpoint] at h
  simp only [Complex.one_re] at h
  have hm : (μ : ℝ) ≤ ((scoreData p d ⟨gone, List.replicate d gone⟩).1.1 : ℝ) := by
    linarith [le_abs_self (1 - (realTarget p).eval 1)]
  exact_mod_cast hm

/-- Direct actual counter bridge once the executable initial score rejects.
This does not assume that search eventually finds an acceptable packet. -/
theorem finite_phase_rejected_table_cost (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hreject : ¬ (scoreData p d ⟨gone, List.replicate d gone⟩).1.1 ≤
      (1/2 : ℚ) ^ phaseToleranceBits eps) :
    let result := finitePhaseSynthesis p d eps
    result.backendCalls = 1 ∧
    result.tableMultiplications = 2 ^ phaseGridBits d (phaseToleranceBits eps) - 1 := by
  dsimp only
  unfold finitePhaseSynthesis
  simp only [hreject, ite_false]
  exact ⟨trivial, (phase_grid_actual_cover_and_table_cost
    (phaseGridBits d (phaseToleranceBits eps))
    (phaseBackendBits d (phaseToleranceBits eps))).2.1⟩

/-- Rejected initialization pays the whole cached table even if search stops early.
No success, parity or global boundedness certificate is needed for this cost. -/
theorem finite_phase_fallback_cost (p : List ℚ) (d : ℕ) (eps μ : ℚ)
    (heps : 0 < eps) (hstrict : eps < μ)
    (hdegree : (realTarget p).degree ≤ (d : WithBot ℕ))
    (hmargin : (realTarget p).eval 1 ≤ 1 - (μ : ℝ)) :
    let result := finitePhaseSynthesis p d eps
    result.backendCalls = 1 ∧
    result.tableMultiplications = 2 ^ phaseGridBits d (phaseToleranceBits eps) - 1 := by
  have hscore := initial_phase_score_lower p d μ hdegree hmargin
  have hreject : ¬ (scoreData p d ⟨gone, List.replicate d gone⟩).1.1 ≤
      (1/2 : ℚ) ^ phaseToleranceBits eps := by
    intro h
    exact (not_le_of_gt hstrict) (hscore.trans (h.trans (phaseTolerance_le eps heps)))
  exact finite_phase_rejected_table_cost p d eps hreject

/-- Positive tolerance alone forces the fallback table size to exceed its reciprocal. -/
theorem phase_table_reciprocal_size (d : ℕ) (eps : ℚ) (heps : 0 < eps) :
    1 / eps ≤ (2 ^ phaseGridBits d (phaseToleranceBits eps) : ℕ) := by
  let k := phaseToleranceBits eps
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have htol : 1 / (2 : ℚ)^k ≤ eps := by
    simpa only [k, one_div, inv_pow] using phaseTolerance_le eps heps
  have hsmall : 1 / eps ≤ (2 : ℚ)^k := by
    apply (div_le_iff₀ heps).mpr
    simpa only [mul_comm] using (div_le_iff₀ hpow).mp htol
  have hbits : k ≤ phaseGridBits d k := Nat.le_add_right _ _
  have hlarge : (2 : ℚ)^k ≤ (2 : ℚ)^phaseGridBits d k :=
    pow_le_pow_right₀ (by norm_num) hbits
  exact_mod_cast hsmall.trans hlarge

/-- Actual same-run arithmetic ledger, with the subtraction at N=1 handled. -/
theorem finite_phase_fallback_reciprocal_cost (p : List ℚ) (d : ℕ) (eps μ : ℚ)
    (heps : 0 < eps) (hstrict : eps < μ)
    (hdegree : (realTarget p).degree ≤ (d : WithBot ℕ))
    (hmargin : (realTarget p).eval 1 ≤ 1 - (μ : ℝ)) :
    (1 : ℚ) / eps ≤ (finitePhaseSynthesis p d eps).tableMultiplications + 1 := by
  have hc := (finite_phase_fallback_cost p d eps μ heps hstrict hdegree hmargin).2
  have hN : 0 < 2 ^ phaseGridBits d (phaseToleranceBits eps) := by positivity
  have hplus : (finitePhaseSynthesis p d eps).tableMultiplications + 1 =
      2 ^ phaseGridBits d (phaseToleranceBits eps) := by omega
  have hr := phase_table_reciprocal_size d eps heps
  exact hr.trans_eq (by exact_mod_cast hplus.symm)


end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
