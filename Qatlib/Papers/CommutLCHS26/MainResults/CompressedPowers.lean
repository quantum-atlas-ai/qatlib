/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.CompressedPowers

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

theorem compressed_power_error (V : Matrix I I ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hR : IsIsometry R) (r : ℕ) :
    ‖compress R (coherentOAAOperator U R) R‖ ≤ 1 ∧
      ‖(compress R (coherentOAAOperator U R) R) ^ r - V ^ r‖ ≤
        (r : ℝ) * coherentOAAError ‖V - (2 : ℝ) • compress R U R‖ := by
  have h : BlockEncoding V U R R 2 ‖V - (2 : ℝ) • compress R U R‖ :=
    ⟨hU, hR, hR, by norm_num, norm_nonneg _, le_rfl⟩
  have hc := (compress_norm_le hR hR (coherentOAAOperator U R)).trans
    (unitary_norm_le_one (coherent_oaa_word_correct U R hR hU).2.2.2.1)
  refine ⟨hc, ?_⟩
  exact (l2_norm_pow_sub_pow_le _ V hc (l2_norm_unitary_le_one hV) r).trans
    (mul_le_mul_of_nonneg_left
      (coherent_oaa_compressed_error V U R _ hV h).2 (Nat.cast_nonneg r))

theorem compressed_power_error_le_six (V : Matrix I I ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hR : IsIsometry R)
    (ε : ℝ) (hlocal : ‖V - (2 : ℝ) • compress R U R‖ ≤ ε) (hε : ε ≤ 1) (r : ℕ) :
    ‖(compress R (coherentOAAOperator U R) R) ^ r - V ^ r‖ ≤
      6 * (r : ℝ) * ε := by
  let δ := ‖V - (2 : ℝ) • compress R U R‖
  have hd0 : 0 ≤ δ := norm_nonneg _
  have hd1 : δ ≤ 1 := hlocal.trans hε
  have hdsq : δ ^ 2 ≤ 1 := by nlinarith
  have herr : coherentOAAError δ ≤ 6 * ε := by
    unfold coherentOAAError
    have hcoef : 3 + (3 / 2) * δ + (1 / 2) * δ ^ 2 ≤ 5 := by linarith
    exact (mul_le_mul_of_nonneg_right hcoef hd0).trans (by linarith)
  exact (compressed_power_error V U R hV hU hR r).2.trans (by
    calc (r : ℝ) * coherentOAAError δ ≤ (r : ℝ) * (6 * ε) :=
        mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg r)
      _ = 6 * (r : ℝ) * ε := by ring)

theorem weighted_compressed_power_error {J : Type} [Fintype J]
    (V : J → Matrix I I ℂ) (U : J → Matrix H H ℂ) (R : Matrix H I ℂ)
    (w : J → ℂ) (ε : J → ℝ) (hV : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup H ℂ) (hR : IsIsometry R)
    (hlocal : ∀ i, ‖V i - (2 : ℝ) • compress R (U i) R‖ ≤ ε i)
    (hε : ∀ i, ε i ≤ 1) (r : ℕ) :
    ‖(∑ i, w i • (compress R (coherentOAAOperator (U i) R) R) ^ r) -
      (∑ i, w i • V i ^ r)‖ ≤
        ∑ i, ‖w i‖ * (6 * (r : ℝ) * ε i) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (compressed_power_error_le_six (V i) (U i) R (hV i) (hU i) hR
      (ε i) (hlocal i) (hε i) r) (norm_nonneg _)

end Qatlib.Papers.CommutLCHS26.MainResults.CompressedPowers
