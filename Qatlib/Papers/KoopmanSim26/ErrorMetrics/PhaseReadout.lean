/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.ErrorMetrics.CoherenceCounterexample

/-!
# Relative phase invisible to Born readout

The decay example supplies two spectral outputs with identical computational-basis probabilities
and different relative phases. Choosing `phaseNode` equal to pi divided by log two changes the
uniform input into its sign-flipped counterpart.

The theorems `source_phase_outputs_orthogonal` and `source_phase_outputs_same_born` show that
these outputs are orthogonal even though their Born distributions coincide. This gives an
explicit boundary for interpreting the probability-based comparison metrics in [ZhangEtAl2026].

## Main statements

- `phaseNode_exp` evaluates the selected spectral phase to minus one.
- `zero_phase_output` and `selected_phase_output` compute the two output vectors.
- `source_phase_outputs_orthogonal` proves zero complex inner product.
* `source_phase_outputs_same_born` proves equality of every computational-basis Born
  probability.

## References

- [Zhang et al., 2026][ZhangEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Papers.KoopmanSim26.ErrorMetrics.Coherence

namespace Qatlib.Papers.KoopmanSim26.ErrorMetrics.PhaseReadout

/-- The value `phaseNode` is the spectral node `pi / log 2` at which the decay example's second
amplitude acquires phase minus one. -/
def phaseNode : ℝ := Real.pi/Real.log 2

/-- At `phaseNode`, the complex phase `exp(-i phaseNode log 2)` equals minus one. -/
theorem phaseNode_exp : Complex.exp ((-phaseNode*Real.log 2:ℝ)*Complex.I)=-1 := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : -phaseNode*Real.log 2=-Real.pi := by
    unfold phaseNode
    field_simp
  rw [he, Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The zero-node spectral unitary leaves the uniform input `plusInput` unchanged. -/
theorem zero_phase_output : spectralUnitary decayL 0 1 0 *ᵥ plusInput=plusInput := by
  rw [decay_spectralUnitary]
  ext b
  simp only [Matrix.mulVec_diagonal]
  cases b <;> simp

/-- At `phaseNode`, the spectral unitary negates the amplitude at `true` and preserves the
amplitude at `false`. -/
theorem selected_phase_output : spectralUnitary decayL 0 1 phaseNode *ᵥ plusInput=
    (fun b : Bool => if b then -plusInput b else plusInput b) := by
  rw [decay_spectralUnitary, phaseNode_exp]
  ext b
  simp only [Matrix.mulVec_diagonal]
  cases b <;> simp

/-- The zero-node and selected-node spectral outputs have zero complex Euclidean inner product.
Together with their equal Born probabilities, this illustrates the phase information
invisible to the probability metric in [ZhangEtAl2026]. -/
theorem source_phase_outputs_orthogonal :
    inner (𝕜:=ℂ) (WithLp.toLp 2 (spectralUnitary decayL 0 1 0 *ᵥ plusInput))
      (WithLp.toLp 2 (spectralUnitary decayL 0 1 phaseNode *ᵥ plusInput))=0 := by
  rw [zero_phase_output, selected_phase_output, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ b : Bool, (if b then -plusInput b else plusInput b)*star (plusInput b))=0
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  unfold plusInput
  ring

/-- The zero-node and selected-node spectral outputs have equal Born probabilities at every
computational-basis outcome. Their orthogonality illustrates the limits of the probability
comparison used in [ZhangEtAl2026]. -/
theorem source_phase_outputs_same_born (b : Bool) :
    BornProb (spectralUnitary decayL 0 1 0 *ᵥ plusInput) b =
      BornProb (spectralUnitary decayL 0 1 phaseNode *ᵥ plusInput) b := by
  rw [spectral_born, spectral_born]

end Qatlib.Papers.KoopmanSim26.ErrorMetrics.PhaseReadout
