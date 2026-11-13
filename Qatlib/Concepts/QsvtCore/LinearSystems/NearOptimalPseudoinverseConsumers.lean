/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverseLine
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitReciprocalCutoff
import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseConsumers

/-!
# Consumers of the near optimal inverse polynomial

This module compares the degree bound of the Chebyshev reciprocal construction with the explicit
conservative cutoff. It also proves that an inverse word of the prescribed length has zero
success probability and no postselection output on normalized inputs with zero least squares
overlap. The mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `nearOptimalReciprocal_vs_conservative_cutoff`: a quantitative comparison for integer `κ ≥
  64`.
* `nearOptimalReciprocal_zero_overlap_output`: zero output at zero least squares overlap.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.LinearSystems
open Matrix

/-- For integer `κ ≥ 64` and `0 < ε ≤ 1 / 2`, the near optimal degree bound is at most half the
conservative cutoff at precision index `ceil (log (1 / ε) / log 2) + 2`. -/
theorem nearOptimalReciprocal_vs_conservative_cutoff (κ : ℕ) (ε : ℝ)
    (hκ : 64 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    let k : ℕ := Nat.ceil (Real.log (1/ε)/Real.log 2)
    ((2*nearOptimalReciprocalJ (κ : ℝ) ε+1 : ℕ) : ℝ) ≤
      (explicitInverseCutoff κ (k+2) : ℝ)/2 := by
  let k : ℕ := Nat.ceil (Real.log (1/ε)/Real.log 2)
  have hκr : (64 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hκ1 : (1 : ℝ) < κ := by linarith
  have hd := (nearOptimalReciprocal_cutoff_bounds (κ : ℝ) ε hκ1 hε hε1).2.2
  have hdegree : ((2*nearOptimalReciprocalJ (κ : ℝ) ε+1 : ℕ) : ℝ) ≤
      32*(κ : ℝ)*Real.log ((κ : ℝ)/ε) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      nearOptimalReciprocalJ, nearOptimalReciprocalB] using! hd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk := Nat.le_ceil (Real.log (1/ε)/Real.log 2)
  change Real.log (1/ε)/Real.log 2 ≤ (k : ℝ) at hk
  rw [div_le_iff₀ hlog2] at hk
  have hlog2u : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have heps : Real.log (1/ε) ≤ (k : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlog2u (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith
  have he : Real.log ((κ : ℝ)/ε) = Real.log (κ : ℝ)+Real.log (1/ε) := by
    rw [Real.log_div hκ0.ne' hε.ne', one_div, Real.log_inv]
    ring
  have hL : Real.log ((κ : ℝ)/ε) ≤ Real.log (κ : ℝ)+(k : ℝ) := by linarith
  have hsum : 64*(Real.log (κ : ℝ)+(k : ℝ)) ≤
      (κ : ℝ)*((k : ℝ)+(κ : ℝ)+3) := by
    have hm := mul_le_mul_of_nonneg_right hκr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hl : 64*Real.log (κ : ℝ) ≤ (κ : ℝ)*(κ : ℝ) := by
      have hl1 := mul_le_mul_of_nonneg_left (Real.log_le_self hκ0.le) (by norm_num : (0 : ℝ) ≤ 64)
      have hl2 := mul_le_mul_of_nonneg_right hκr hκ0.le
      nlinarith
    nlinarith
  have hbound : 32*(κ : ℝ)*Real.log ((κ : ℝ)/ε) ≤
      (κ : ℝ)*(κ : ℝ)*((k : ℝ)+(κ : ℝ)+3)/2 := by
    have hl := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 64)
    have htotal : 64*Real.log ((κ : ℝ)/ε) ≤ (κ : ℝ)*((k : ℝ)+(κ : ℝ)+3) := hl.trans hsum
    have hm := mul_le_mul_of_nonneg_left htotal hκ0.le
    nlinarith
  apply hdegree.trans
  rw [(explicit_inverse_cutoff_integer_formula κ (k+2)).1]
  push_cast
  nlinarith

/-- Under the inverse gap and parameter hypotheses, a phase word of length `2 *
nearOptimalReciprocalJ κ ε + 1` has zero postselection probability and no output for every
normalized zero overlap input; see [GilyenSuLowWiebe2019]. -/
theorem nearOptimalReciprocal_zero_overlap_output
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (henc : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding A U L R)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i →
      κ⁻¹ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) :
    ∃ Φ : List ℝ, Φ.length = 2*nearOptimalReciprocalJ κ ε+1 ∧
      ∀ v : QState O, Normalized v → Qatlib.Concepts.LocalMachine.LocalTransport.leastSquaresOverlap A v = 0 →
        Encoding.postselectionProbability
          (sourceRealWord U (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector R) (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector L) Φ)ᴴ
          (sourceAverageClean R) (sourceAverageClean L) v = 0 ∧
        Encoding.postselectionOutput
          (sourceRealWord U (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector R) (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector L) Φ)ᴴ
          (sourceAverageClean R) (sourceAverageClean L) v = none := by
  obtain ⟨Φ, hlen, hexact, _, _⟩ := nearOptimalReciprocal_inverse_word
    H I O A U L R κ ε hκ hε hε1 henc hgap
  refine ⟨Φ, hlen, ?_⟩
  intro v _ hv
  have hkernel := Qatlib.Concepts.QsvtCore.LinearSystems.inverse_overlap_zero_kernel A v hv
  have hcorner := hexact.adjoint.encoded
  have hz : Encoding.postselectionVector
      (sourceRealWord U (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector R) (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector L) Φ)ᴴ
      (sourceAverageClean R) (sourceAverageClean L) v = 0 := by
    unfold Encoding.postselectionVector
    rw [hcorner]
    exact Qatlib.Concepts.QsvtCore.LinearSystems.inverse_odd_adjoint_kernel A _ v hkernel
  constructor
  · rw [Encoding.postselectionProbability_eq_norm_sq hexact.right_isometry, hz]
    simp [Qatlib.Concepts.BlockEncoding.Postselection.stateVector]
  · rw [Encoding.postselectionOutput, hz]
    exact (Qatlib.Concepts.BlockEncoding.Postselection.conditionalState_eq_none_iff (0 : QState I)).mpr rfl

end Qatlib.Concepts.QsvtCore.LinearSystems
