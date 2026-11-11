/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.DiagonalizedLCHS
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Finite.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Coherent evolution and classical mixtures

This module constructs a two-level dissipative generator `decayL` and a normalized uniform input
`plusInput`. Its exact propagator attenuates the second amplitude by one half, so normalizing
`decayOutput` gives outcome probability four fifths for `false`.

Every spectral unitary preserves the uniform Born distribution, and any finite classical mixture
of these distributions still gives probability one half. The result
`coherent_ne_classical_mixture` therefore separates coherent LCHS evolution from probability
mixing in the simulation setting of [ZhangEtAl2026], while `actual_source_lchs_formula` verifies
the exact operator integral for this same example.

## Main statements

- `decay_propagator` computes the dissipative propagator explicitly.
* `coherent_born_zero` and `mixture_born_zero` give the distinct probabilities four fifths and
  one half.
* `coherent_ne_classical_mixture` proves the mismatch for every finite distribution of spectral
  nodes.
- `actual_source_lchs_formula` establishes the Cauchy-weighted LCHS identity.

## References

- [Zhang et al., 2026][ZhangEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.KoopmanSim26.ErrorMetrics.Coherence

/-- The matrix `decayL` is a diagonal two-level dissipative generator with entry zero at `false`
and entry `-log 2` at `true`. -/
def decayL : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then (-Real.log 2:ℝ) else 0)

/-- The negative of `decayL` is positive semidefinite, establishing the dissipativity condition
for its LCHS representation. -/
theorem decayL_negative_psd : (-decayL).PosSemidef := by
  rw [decayL, Matrix.diagonal_neg]
  apply Matrix.PosSemidef.diagonal
  intro b
  cases b <;> simp
  exact_mod_cast (Real.log_nonneg (by norm_num : (1:ℝ)≤2))

/-- The vector `plusInput` is the uniform two-level input whose two amplitudes are both `1 /
sqrt 2`. -/
def plusInput : Bool → ℂ := fun _ => ((Real.sqrt 2)⁻¹ : ℝ)

/-- Each computational-basis outcome of `plusInput` has Born probability one half. -/
theorem plusInput_born (b : Bool) : BornProb plusInput b=1/2 := by
  unfold BornProb plusInput
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The uniform input `plusInput` has total Born probability one. -/
theorem plusInput_normalized : Normalized plusInput := by
  change (∑ b : Bool, BornProb plusInput b)=1
  simp [plusInput_born]

/-- At time one with zero Hamiltonian part, the propagator of `decayL` is diagonal with entries
one and one half at `false` and `true`, respectively. -/
theorem decay_propagator : propagator decayL 0 1=
    Matrix.diagonal (fun b : Bool => if b then (1/2:ℂ) else 1) := by
  simp only [propagator, smul_zero, add_zero, one_smul, decayL, Matrix.exp_diagonal]
  apply congrArg Matrix.diagonal
  funext b
  cases b
  · simp [Pi.coe_exp]
  · rw [Pi.coe_exp]
    simp only [if_true]
    change NormedSpace.exp ((-Real.log 2:ℝ):ℂ)=(1/2:ℂ)
    rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num

/-- The vector `decayOutput` is the unnormalized output obtained by applying the time-one
dissipative propagator to `plusInput`. -/
def decayOutput : Bool → ℂ := propagator decayL 0 1 *ᵥ plusInput

/-- The unnormalized Born weights of `decayOutput` are one half at `false` and one eighth at
`true`. -/
theorem decayOutput_born (b : Bool) : BornProb decayOutput b=if b then 1/8 else 1/2 := by
  unfold decayOutput
  rw [decay_propagator]
  simp only [Matrix.mulVec_diagonal, BornProb]
  cases b
  · simpa only [BornProb, Bool.false_eq_true, if_false, one_mul] using! plusInput_born false
  · change ‖(1/2:ℂ)*plusInput true‖^2=(1/8:ℝ)
    rw [norm_mul, mul_pow]
    have hp := plusInput_born true
    unfold BornProb at hp
    rw [hp]
    norm_num

/-- The quantity `stateMass` is the total Born weight of a two-level vector, computed by summing
its squared amplitude norms. -/
def stateMass (ψ : Bool → ℂ) : ℝ := ∑ b, BornProb ψ b

/-- The vector `normalizedState` scales every amplitude by the reciprocal square root of its
total Born weight. -/
def normalizedState (ψ : Bool → ℂ) : Bool → ℂ := fun b => (Real.sqrt (stateMass ψ))⁻¹ • ψ b

/-- For a vector with positive total Born weight, normalization divides each Born weight by that
total. -/
theorem normalizedState_born (ψ : Bool → ℂ) (hm : 0 < stateMass ψ) (b : Bool) :
    BornProb (normalizedState ψ) b=BornProb ψ b/stateMass ψ := by
  unfold BornProb normalizedState
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hm.le]
  ring

/-- A vector with positive total Born weight becomes normalized under `normalizedState`. -/
theorem normalizedState_normalized (ψ : Bool → ℂ) (hm : 0 < stateMass ψ) :
    Normalized (normalizedState ψ) := by
  change (∑ b : Bool, BornProb (normalizedState ψ) b)=1
  simp_rw [normalizedState_born ψ hm]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hm)

/-- The total Born weight of the dissipative output is five eighths. -/
theorem decayOutput_mass : stateMass decayOutput=5/8 := by
  simp [stateMass, decayOutput_born]
  norm_num

/-- Normalizing the coherent dissipative output gives Born probability four fifths for outcome
`false`. -/
theorem coherent_born_zero : BornProb (normalizedState decayOutput) false=4/5 := by
  rw [normalizedState_born _ (by rw [decayOutput_mass]; norm_num), decayOutput_born,
      decayOutput_mass]
  norm_num

/-- The spectral unitary for the decay example is diagonal, with phase one at `false` and
`exp(-i k log 2)` at `true`. -/
theorem decay_spectralUnitary (k : ℝ) : spectralUnitary decayL 0 1 k=
    Matrix.diagonal (fun b : Bool => if b then Complex.exp ((-k*Real.log 2:ℝ)*Complex.I) else 1) := by
  unfold spectralUnitary decayL
  rw [zero_add, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  apply congrArg Matrix.diagonal
  funext b
  cases b
  · simp [Pi.smul_apply, Pi.coe_exp]
  · simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, mul_one]
    rw [← Complex.exp_eq_exp_ℂ]
    congr 1
    simp only [Complex.real_smul]
    push_cast
    ring

/-- For every real spectral node, applying the spectral unitary to `plusInput` leaves each Born
probability equal to one half. -/
theorem spectral_born (k : ℝ) (b : Bool) :
    BornProb (spectralUnitary decayL 0 1 k *ᵥ plusInput) b=1/2 := by
  rw [decay_spectralUnitary]
  simp only [Matrix.mulVec_diagonal, BornProb]
  cases b
  · simpa only [Bool.false_eq_true, if_false, one_mul] using! plusInput_born false
  · change ‖Complex.exp ((-k*Real.log 2:ℝ)*Complex.I)*plusInput true‖^2=(1/2:ℝ)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact plusInput_born true

/-- Every spectral-unitary output of `plusInput` in the decay example is normalized. -/
theorem spectral_normalized (k : ℝ) : Normalized (spectralUnitary decayL 0 1 k *ᵥ plusInput) := by
  change (∑ b : Bool, BornProb (spectralUnitary decayL 0 1 k *ᵥ plusInput) b)=1
  simp [spectral_born]

/-- Any finite probability mixture of spectral-node outputs has probability one half for outcome
`false`. -/
theorem mixture_born_zero {J : Type} [Fintype J] [DecidableEq J]
    (q : FinDist J) (nodes : J → ℝ) :
    q.expect (fun j => BornProb (spectralUnitary decayL 0 1 (nodes j) *ᵥ plusInput) false)=1/2 := by
  simp only [FinDist.expect, spectral_born]
  rw [← Finset.sum_mul, q.sum_one]
  norm_num

/-- The normalized coherent decay output has a different probability for `false` from every
finite classical mixture of the spectral-unitary outputs. This distinguishes probability
mixing from the coherent representation used in [ZhangEtAl2026]. -/
theorem coherent_ne_classical_mixture {J : Type} [Fintype J] [DecidableEq J]
    (q : FinDist J) (nodes : J → ℝ) :
    BornProb (normalizedState decayOutput) false ≠
      q.expect (fun j => BornProb (spectralUnitary decayL 0 1 (nodes j) *ᵥ plusInput) false) := by
  rw [coherent_born_zero, mixture_born_zero]
  norm_num

/-- The Cauchy-weighted integral of the decay example's spectral unitaries equals its exact
time-one propagator. -/
theorem actual_source_lchs_formula :
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • spectralUnitary decayL 0 1 k)=propagator decayL 0 1 :=
  (diagonalized_lchs_spectral_representation decayL 0 1 decayL_negative_psd Matrix.isHermitian_zero (by norm_num)).2

end Qatlib.Papers.KoopmanSim26.ErrorMetrics.Coherence
