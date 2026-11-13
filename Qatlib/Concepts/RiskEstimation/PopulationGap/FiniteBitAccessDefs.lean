/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout

/-!
# Dyadic loading and rational phase gates

This module defines downward dyadic loading of real inputs and proves its rounding-error bounds.
It uses a rational Cayley phase construction to approximate `Rz` and realizes the resulting
phase matrix as one legal fixed gate with zero queries.

For the quantum gate and phase-rotation background, see [NielsenChuang2010].

## Main statements

* `loadReal_error`: The absolute dyadic loading error is strictly less than `2⁻ᵏ`.
* `riskPhaseGate_error`: For `|θ| ≤ 1`, the rational risk phase gate differs from `Rz θ` by norm
  at most `2 * 2⁻ᵏ`.
* `riskPhaseGate_fixed_gate`: The one-bit risk phase matrix is realized exactly by a legal gate
  list of length one with zero queries and one counted gate.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.RiskEstimation.PopulationGap (clause11 euclid_gcd_fuel)
open Qatlib.Concepts.RiskEstimation.PopulationGap (shorBitLength euclidGcd euclidStepBound)
open Qatlib.Concepts.RiskEstimation.PopulationGap (SpaceSchedule)

/-- The integer numerator obtained by flooring `x * 2 ^ k`. -/
noncomputable def loadNumerator (k : ℕ) (x : ℝ) : ℤ := ⌊x * (2 : ℝ)^k⌋

/-- The downward dyadic rational approximation `loadNumerator k x / 2 ^ k`. -/
noncomputable def loadReal (k : ℕ) (x : ℝ) : ℚ :=
  (loadNumerator k x : ℚ) / ((2 : ℚ)^k)

/-- The real-loading approximation equals `dyadicRound` at the same precision. -/
theorem loadReal_eq_dyadicRound (k : ℕ) (x : ℝ) :
    loadReal k x = dyadicRound k x := by
  simp only [loadReal, loadNumerator, dyadicRound]

/-- Casting `loadReal` to the reals gives its integer numerator divided by `2 ^ k`. -/
theorem loadReal_cast (k : ℕ) (x : ℝ) :
    (loadReal k x : ℝ) = ((loadNumerator k x : ℤ) : ℝ) / (2 : ℝ)^k := by
  simp only [loadReal]
  push_cast
  ring

/-- Downward dyadic loading never exceeds the original real input. -/
theorem loadReal_le (k : ℕ) (x : ℝ) : (loadReal k x : ℝ) ≤ x := by
  have hf := Int.floor_le (x * (2 : ℝ)^k)
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  rw [loadReal_cast, div_le_iff₀ hp]
  exact hf

/-- The dyadic loading error multiplied by `2 ^ k` is strictly less than one. -/
theorem loadReal_error_scaled (k : ℕ) (x : ℝ) :
    |(loadReal k x : ℝ) - x| * (2 : ℝ)^k < 1 := by
  rw [loadReal_eq_dyadicRound k x]
  exact dyadicRound_error k x

/-- The absolute dyadic loading error is strictly less than `2⁻ᵏ`. -/
theorem loadReal_error (k : ℕ) (x : ℝ) :
    |(loadReal k x : ℝ) - x| < (1/2 : ℝ)^k := by
  have h := loadReal_error_scaled k x
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  have h' : |(loadReal k x : ℝ) - x| < (1:ℝ) / (2:ℝ)^k := (lt_div_iff₀ hp).mpr h
  rw [← _root_.one_div_pow] at h'
  exact h'

/-- Dyadic loading preserves nonpositivity. -/
theorem loadReal_nonpos (k : ℕ) {x : ℝ} (hx : x ≤ 0) : (loadReal k x : ℝ) ≤ 0 := by
  have h := loadReal_le k x
  linarith

/-- Dyadic loading preserves strict negativity. -/
theorem loadReal_neg (k : ℕ) {x : ℝ} (hx : x < 0) : (loadReal k x : ℝ) < 0 := by
  have hfloor : ((⌊x * (2 : ℝ)^k⌋ : ℤ) : ℝ) < 0 := by
    have h1 := Int.floor_le (x * (2 : ℝ)^k)
    have hp : (0:ℝ) < (2:ℝ)^k := by positivity
    have h2 : x * (2 : ℝ)^k < 0 := by nlinarith [hx]
    linarith
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  rw [loadReal_cast, div_lt_iff₀ hp]
  simp only [loadNumerator]
  simpa using! hfloor

/-- Dyadic loading represents every integer exactly. -/
theorem loadReal_int (k : ℕ) (m : ℤ) : loadReal k (m : ℝ) = (m : ℚ) := by
  have hpow : (2 : ℝ)^k = (((2 ^ k : ℕ) : ℤ) : ℝ) := by
    have h1 : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ)^k := Nat.cast_pow 2 k
    have h2 : (((2 ^ k : ℕ) : ℤ) : ℝ) = ((2 ^ k : ℕ) : ℝ) := rfl
    rw [h2, h1]
  have hfloor : (⌊(m : ℝ) * (2 : ℝ)^k⌋ : ℤ) = m * ((2 ^ k : ℕ) : ℤ) := by
    rw [hpow, ← Int.cast_mul, Int.floor_intCast]
  simp only [loadReal, loadNumerator, hfloor]
  push_cast
  have h2 : (2 : ℚ)^k ≠ 0 := by positivity
  field_simp

/-- Dyadic loading preserves the bound `|x| ≤ 1`. -/
theorem loadReal_abs_le_one (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(loadReal k x : ℝ)| ≤ 1 := by
  have hle := loadReal_le k x
  rw [loadReal_cast] at hle
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ)^k := by push_cast; ring
  have hlow : ((loadNumerator k x : ℤ) : ℝ) > x * (2 : ℝ)^k - 1 := by
    have h := Int.lt_floor_add_one (x * (2 : ℝ)^k)
    simp only [loadNumerator]
    linarith
  have hbound : -(2 : ℝ)^k ≤ x * (2 : ℝ)^k := by
    have hx1 : (-1:ℝ) ≤ x := (abs_le.mp hx).1
    have hm := mul_le_mul_of_nonneg_right hx1 (by positivity : (0:ℝ) ≤ (2:ℝ)^k)
    nlinarith
  have hnum : (-(2 ^ k : ℕ) : ℤ) ≤ loadNumerator k x := by
    have hz : (-(2 ^ k : ℕ) : ℤ) - 1 < (loadNumerator k x : ℤ) := by
      have hz' : (((-(2 ^ k : ℕ) : ℤ) - 1 : ℤ) : ℝ) < ((loadNumerator k x : ℤ) : ℝ) := by
        have heq : (((-(2 ^ k : ℕ) : ℤ) - 1 : ℤ) : ℝ) = -((2 : ℝ)^k) - 1 := by
          push_cast [Int.cast_sub, Int.cast_neg]
          ring
        rw [heq]
        linarith [hlow, hbound]
      exact (Int.cast_lt).mp hz'
    omega
  rw [loadReal_cast, abs_le]
  constructor
  · rw [le_div_iff₀ hp]
    have hz' : ((-(2 ^ k : ℕ) : ℤ) : ℝ) ≤ (loadNumerator k x : ℝ) := by
      exact_mod_cast hnum
    have hcast2 : ((-(2 ^ k : ℕ) : ℤ) : ℝ) = -((2 : ℝ)^k) := by
      push_cast [Int.cast_neg]
      ring
    rw [show (-1:ℝ) * (2:ℝ)^k = -((2:ℝ)^k) by ring, ← hcast2]
    exact hz'
  · have hx1 : x ≤ 1 := (abs_le.mp hx).2
    linarith

/-- The dyadic rational phase approximation obtained by loading `θ` at precision `k`. -/
noncomputable def solvePhase (k : ℕ) (θ : ℝ) : ℚ := loadReal k θ

/-- The real cast of `solvePhase` agrees with the real cast of `loadReal`. -/
theorem solvePhase_cast (k : ℕ) (θ : ℝ) : (solvePhase k θ : ℝ) = (loadReal k θ : ℝ) := rfl

/-- The absolute error of the dyadic phase approximation is strictly less than `2⁻ᵏ`. -/
theorem solvePhase_error (k : ℕ) (θ : ℝ) :
    |(solvePhase k θ : ℝ) - θ| < (1/2 : ℝ)^k :=
  loadReal_error k θ

/-- The matrix-norm distance between two `Rz` rotations is at most the absolute difference of
their angles. -/
theorem rz_sub_le (θ a : ℝ) : ‖Rz θ - Rz a‖ ≤ |θ - a| := by
  have h : Rz θ - Rz a = Matrix.diagonal (fun b => if b then
      Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I) else 0) := by
    unfold Rz
    rw [Matrix.diagonal_sub]
    congr 1
    funext b
    split_ifs <;> simp
  rw [h, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
  intro b
  by_cases hb : b
  · simp only [hb, if_true]
    exact norm_exp_mul_I_sub_le θ a
  · simp [hb]

/-- Replacing a phase by `solvePhase k θ` changes its `Rz` matrix by norm at most `2⁻ᵏ`. -/
theorem solvePhase_phase_error (k : ℕ) (θ : ℝ) :
    ‖Rz θ - Rz (((solvePhase k θ : ℝ)))‖ ≤ (1/2 : ℝ)^k := by
  have h := rz_sub_le θ (solvePhase k θ : ℝ)
  have h' := solvePhase_error k θ
  calc ‖Rz θ - Rz (((solvePhase k θ : ℝ)))‖ ≤ |θ - (solvePhase k θ : ℝ)| := h
    _ = |(solvePhase k θ : ℝ) - θ| := abs_sub_comm _ _
    _ ≤ (1/2 : ℝ)^k := le_of_lt h'

/-- The `k`th power of the reciprocal of two equals `(1 / 2) ^ k`. -/
theorem inv2_pow (k : ℕ) : ((2 : ℝ) ⁻¹) ^ k = (1/2 : ℝ)^k := by
  have h1 : (1/2 : ℝ)^k = (1:ℝ)^k / (2:ℝ)^k := _root_.div_pow _ _ _
  have h2 : ((2 : ℝ) ⁻¹) ^ k = ((2:ℝ)^k)⁻¹ := inv_pow ..
  have h3 : ((2:ℝ)^k)⁻¹ = (1:ℝ) / (2:ℝ)^k := by rw [inv_eq_one_div]
  rw [h1, h2, h3, one_pow]

/-- The rational phase gate constructed from a counted Cayley approximation to the dyadically
loaded phase. -/
noncomputable def riskPhaseGate (k : ℕ) (θ : ℝ) : Matrix Bool Bool ℂ :=
  rationalPhaseGate (countedCayleyPhase (solvePhase k θ) k).1

/-- The rational risk phase gate is unitary. -/
theorem riskPhaseGate_unitary (k : ℕ) (θ : ℝ) :
    riskPhaseGate k θ ∈ Matrix.unitaryGroup Bool ℂ := by
  exact rationalPhaseGate_mem_unitaryGroup
    (gaussianRatComplex_countedCayleyPhase_norm (solvePhase k θ) k)

/-- For `|θ| ≤ 1`, the rational risk phase gate differs from `Rz θ` by norm at most `2 * 2⁻ᵏ`. -/
theorem riskPhaseGate_error (k : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1) :
    ‖riskPhaseGate k θ - Rz θ‖ ≤ 2 * (1/2 : ℝ)^k := by
  have hload : |(solvePhase k θ : ℝ)| ≤ 1 := loadReal_abs_le_one k hθ
  have hsyn : ‖riskPhaseGate k θ - Rz (((solvePhase k θ : ℝ)))‖ ≤ (1/2 : ℝ)^k := by
    have h := (rational_cayley_gate_unitarity_and_target_error
      (solvePhase k θ) k).2 hload
    rw [inv2_pow] at h
    exact h
  have hphase := rz_sub_le θ (solvePhase k θ : ℝ)
  have herr : |(solvePhase k θ : ℝ) - θ| ≤ (1/2 : ℝ)^k :=
    le_of_lt (solvePhase_error k θ)
  have h2 : ‖Rz (((solvePhase k θ : ℝ))) - Rz θ‖ ≤ |(solvePhase k θ : ℝ) - θ| := by
    rw [show Rz (((solvePhase k θ : ℝ))) - Rz θ
        = -(Rz θ - Rz (((solvePhase k θ : ℝ)))) by abel, norm_neg]
    rw [abs_sub_comm]
    exact hphase
  have htri : ‖riskPhaseGate k θ - Rz θ‖
      ≤ ‖riskPhaseGate k θ - Rz (((solvePhase k θ : ℝ)))‖
          + ‖Rz (((solvePhase k θ : ℝ))) - Rz θ‖ := by
    have heq : riskPhaseGate k θ - Rz θ
        = (riskPhaseGate k θ - Rz (((solvePhase k θ : ℝ))))
          + (Rz (((solvePhase k θ : ℝ))) - Rz θ) := by abel
    rw [heq]
    exact norm_add_le _ _
  calc ‖riskPhaseGate k θ - Rz θ‖
      ≤ ‖riskPhaseGate k θ - Rz (((solvePhase k θ : ℝ)))‖
          + ‖Rz (((solvePhase k θ : ℝ))) - Rz θ‖ := htri
    _ ≤ (1/2 : ℝ)^k + |(solvePhase k θ : ℝ) - θ| := add_le_add hsyn h2
    _ ≤ 2 * (1/2 : ℝ)^k := by linarith

/-- For every natural `L`, `2 ^ (L + 1)` is strictly greater than `L + 1`. -/
theorem two_pow_gt (L : ℕ) : (2 : ℕ) ^ (L + 1) > L + 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have h1 : (2 : ℕ) ^ (L + 1 + 1) = (2 : ℕ) ^ (L + 1) * 2 := Nat.pow_succ _ _
    rw [h1]
    omega

/-- For every natural `L`, `2 ^ (L + 3)` is strictly greater than `L + 3`. -/
theorem two_pow_gt_succ (L : ℕ) : (2 : ℕ) ^ (L + 3) > L + 3 := by
  have h := two_pow_gt (L + 2)
  rw [show L + 2 + 1 = L + 3 by omega] at h
  simpa using! h

/-- The base-two logarithm of `2 ^ m` is `m`. -/
theorem log2_pow_two (m : ℕ) : Nat.log2 (2 ^ m) = m := by
  rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num)]

/-- The real cast of an integer's natural absolute value equals its real absolute value. -/
theorem natAbs_cast_eq (m : ℤ) : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
  by_cases hm : 0 ≤ m
  · have h1 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
    have h2 : ((m.natAbs : ℕ) : ℝ) = ((m.natAbs : ℤ) : ℝ) :=
      (Int.cast_natCast _).symm
    rw [h2, h1]
    have h3 : ((m : ℤ) : ℝ) ≥ 0 := by exact_mod_cast hm
    simp [abs_of_nonneg h3]
  · have hm' : m ≤ 0 := le_of_not_ge hm
    have h1 : (m.natAbs : ℤ) = -m := Int.ofNat_natAbs_of_nonpos hm'
    have h2 : ((m.natAbs : ℕ) : ℝ) = ((m.natAbs : ℤ) : ℝ) :=
      (Int.cast_natCast _).symm
    rw [h2, h1]
    have h3 : ((-m : ℤ) : ℝ) = -((m : ℤ) : ℝ) := by push_cast; ring
    rw [h3]
    have h4 : ((m : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hm'
    simp [abs_of_nonpos h4]

/-- The rational risk phase gate relabelled onto a one-bit register. -/
noncomputable def riskPhaseGateRegister (k : ℕ) (θ : ℝ) : Matrix (Reg 1) (Reg 1) ℂ :=
  relabelGate noWorkOneBitEquiv.symm (riskPhaseGate k θ)

/-- The risk phase gate on a one-bit register is unitary. -/
theorem riskPhaseGateRegister_unitary (k : ℕ) (θ : ℝ) :
    riskPhaseGateRegister k θ ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
  exact (relabelGate_mem_unitaryGroup noWorkOneBitEquiv.symm _).2
    (rationalPhaseGate_mem_unitaryGroup
      (gaussianRatComplex_countedCayleyPhase_norm (solvePhase k θ) k))

/-- The one-bit risk phase matrix is realized exactly by a legal gate list of length one with
zero queries and one counted gate. -/
theorem riskPhaseGate_fixed_gate (k : ℕ) (θ : ℝ) :
    ∃ gs : List (ReflectionGate 1), reflectionLegal gs ∧ gs.length = 1 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = 1 ∧
      ∀ ψ : QState (Reg 1),
        Run 1 (reflectionCompile gs) ψ = riskPhaseGateRegister k θ *ᵥ ψ :=
  noWork_one_bit_unitary_table _ (riskPhaseGateRegister_unitary k θ)

/-- A gate list with one counted gate and zero queries exists for every choice of phase
parameters. -/
theorem riskPhaseGate_fixed_gate_ledger (k : ℕ) (θ : ℝ) :
    ∃ gs : List (ReflectionGate 1), GateCount (reflectionCompile gs) = 1 ∧
      QueryCount (reflectionCompile gs) = 0 := by
  obtain ⟨gs, _, _, hq, hg, _⟩ := riskPhaseGate_fixed_gate k θ
  exact ⟨gs, hg, hq⟩
end Qatlib.Concepts.RiskEstimation.PopulationGap
