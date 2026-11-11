/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.HigherMoments.HigherPauliMomentConsumers

/-!
# ClassShadows20 · HigherMoments · two-qubit finite moment

This file fixes the two-qubit maximally mixed input and records two exact finite
identities: every fixed Pauli-axis table has the explicitly normalized mass
`1 / 3²`, and the ordered second shadow moment is the purity `1 / 4`.
The result consumes the existing tensor-Pauli measurement law and higher-order
kernel; it does not define another producer or a finite-gate implementation.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ClassShadows20.HigherMoments

open scoped BigOperators Classical ComplexOrder
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Papers.ClassShadows20.HigherMoments

/- The concrete four-dimensional maximally mixed input. -/
/-- The maximally mixed density matrix on the two-qubit register. -/
def twoQubitMixed : Operator 4 := (1 / 4 : ℂ) • (1 : Operator 4)

/-- The concrete two-qubit maximally mixed operator is a density operator. -/
theorem twoQubitMixed_density : IsDensityOperator twoQubitMixed := by
  refine ⟨?_, ?_⟩
  · exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by
      rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) from by norm_num]
      exact RCLike.ofReal_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 1 / 4))
  · show Matrix.trace ((1 / 4 : ℂ) • (1 : Operator 4)) = 1
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_one]
    norm_num [Complex.ofReal_div]

/-- The finite two-qubit Pauli law is normalized on all `12²` records. -/
theorem twoQubitPauliLaw_normalized :
    ∑ o : Fin 2 → Fin 3 × Bool,
      (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density).prob o = 1 := by
  exact (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density).sum_one

/-- For every fixed two-qubit axis table, the four outcome bits carry mass `1/9`. -/
theorem twoQubitPauliLaw_axis_normalized (a : Fin 2 → Fin 3) :
    ∑ b : Fin 2 → Bool,
      (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density).prob
        (fun i => (a i, b i)) = (1 : ℝ) / 9 := by
  convert tensorPauliLaw_axis_mass 2 twoQubitMixed twoQubitMixed_density a using 1 <;> norm_num

/-- Two fresh two-qubit Pauli snapshots have exact ordered moment `tr(ρ²) = 1/4`. -/
theorem twoQubitPauliLaw_second_moment :
    higherUMean (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density) 2
      (higherShadowKernel 2) = (1 : ℝ) / 4 := by
  rw [higherShadowKernel_mean]
  norm_num [twoQubitMixed, pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, Matrix.trace_one, Complex.ext_iff]

/-! A concrete local observable consumer.  Restricting a Pauli word to one
qubit gives the exact support-controlled second moment `3`; this is the
finite random-measurement statistic used by the variance budget. -/

/-- The first-wire Pauli word, with identity on the second wire. -/
def firstQubitPauliWord (a : Fin 3) : Fin 2 → Option (Fin 3) :=
  fun i => if i = 0 then some a else none

/-- A one-site Pauli shadow on the two-qubit maximally mixed input has second
moment `3`, independent of the chosen Pauli axis. -/
theorem twoQubit_firstQubitPauli_second_moment (a : Fin 3) :
    (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density).expect
      (fun o => (tensorPauliValue (firstQubitPauliWord a) o) ^ 2) = 3 := by
  simpa [firstQubitPauliWord, tensorPauliWeight, Fin.sum_univ_succ] using
    (tensorPauliValue_second_moment 2 twoQubitMixed twoQubitMixed_density
      (firstQubitPauliWord a))

/-- On the maximally mixed input the first-wire nonidentity Pauli has zero
mean, so its exact variance is the support-controlled second moment `3`. -/
theorem twoQubit_firstQubitPauli_variance (a : Fin 3) :
    (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density).variance
      (tensorPauliValue (firstQubitPauliWord a)) = 3 := by
  have hm := tensor_pauli_word_exact_moments 2 twoQubitMixed twoQubitMixed_density
    (firstQubitPauliWord a)
  rw [hm.2.2.2]
  have htrace :
      (Matrix.trace (tensorPauliWord 2 (firstQubitPauliWord a) * twoQubitMixed)).re = 0 := by
    rw [twoQubitMixed, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
    rw [tensorPauliWord, tensorPauliProduct_trace]
    simp [firstQubitPauliWord, tensorPauliWordFactor, trace_pauliMatrix]
  rw [htrace]
  norm_num [tensorPauliWeight, firstQubitPauliWord]

/-- The finite two-qubit Pauli measurement normalization and second moment hold together. -/
theorem twoQubitPauli_measurement_and_moment :
    (∑ o : Fin 2 → Fin 3 × Bool,
      (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density).prob o = 1) ∧
    (∀ a : Fin 2 → Fin 3,
      ∑ b : Fin 2 → Bool,
        (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density).prob
          (fun i => (a i, b i)) = (1 : ℝ) / 9) ∧
    higherUMean (tensorPauliLaw 2 twoQubitMixed twoQubitMixed_density) 2
      (higherShadowKernel 2) = (1 : ℝ) / 4 := by
  exact ⟨twoQubitPauliLaw_normalized, twoQubitPauliLaw_axis_normalized,
    twoQubitPauliLaw_second_moment⟩

end Qatlib.Papers.ClassShadows20.HigherMoments
