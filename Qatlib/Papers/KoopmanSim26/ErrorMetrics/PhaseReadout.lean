/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.ErrorMetrics.CoherenceCounterexample
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Papers.KoopmanSim26.ErrorMetrics.Coherence

namespace Qatlib.Papers.KoopmanSim26.ErrorMetrics.PhaseReadout

def phaseNode : ℝ := Real.pi/Real.log 2

theorem phaseNode_exp : Complex.exp ((-phaseNode*Real.log 2:ℝ)*Complex.I)=-1 := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : -phaseNode*Real.log 2=-Real.pi := by
    unfold phaseNode
    field_simp
  rw [he, Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem zero_phase_output : spectralUnitary decayL 0 1 0 *ᵥ plusInput=plusInput := by
  rw [decay_spectralUnitary]
  ext b
  simp only [Matrix.mulVec_diagonal]
  cases b <;> simp

theorem selected_phase_output : spectralUnitary decayL 0 1 phaseNode *ᵥ plusInput=
    (fun b : Bool => if b then -plusInput b else plusInput b) := by
  rw [decay_spectralUnitary, phaseNode_exp]
  ext b
  simp only [Matrix.mulVec_diagonal]
  cases b <;> simp

theorem source_phase_outputs_orthogonal :
    inner (𝕜:=ℂ) (WithLp.toLp 2 (spectralUnitary decayL 0 1 0 *ᵥ plusInput))
      (WithLp.toLp 2 (spectralUnitary decayL 0 1 phaseNode *ᵥ plusInput))=0 := by
  rw [zero_phase_output, selected_phase_output, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ b : Bool, (if b then -plusInput b else plusInput b)*star (plusInput b))=0
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  unfold plusInput
  ring

theorem source_phase_outputs_same_born (b : Bool) :
    BornProb (spectralUnitary decayL 0 1 0 *ᵥ plusInput) b =
      BornProb (spectralUnitary decayL 0 1 phaseNode *ᵥ plusInput) b := by
  rw [spectral_born, spectral_born]

end Qatlib.Papers.KoopmanSim26.ErrorMetrics.PhaseReadout
