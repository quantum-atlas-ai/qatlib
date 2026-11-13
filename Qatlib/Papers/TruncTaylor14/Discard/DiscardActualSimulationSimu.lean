/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TruncTaylor14.Discard.DiscardActualSimulationStat
import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardSegmentationCorrectedSimu

/-!
# Actual simulation by Taylor reset and discard

This module proves `SourceDiscardActualSimulation` for finite unitary decompositions of a
Hermitian Hamiltonian with a supplied coefficient-sum bound. The result combines circuit
well-formedness, exact query and gate counts, amplified-workspace semantics, and a trace-norm
error bound for repeated reset-and-discard steps. See [BerryEtAl2015Taylor].

## Main statements

* `hamiltonianEvolution_power`: Repeated equal-time evolution equals evolution for the
  accumulated time.
* `sourceDiscardActualSimulation`: The full actual-simulation statement for the chosen Taylor
  cutoff.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
noncomputable section
namespace Qatlib.Papers.TruncTaylor14.DiscardCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped ComplexOrder Matrix.Norms.L2Operator

local instance (priority := 10000) instProdProdFast' {α β γ : Type} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] : DecidableEq ((α × β) × γ) :=
  @instDecidableEqProd (α × β) γ (@instDecidableEqProd α β _ _) _

/-- The `n`th power of Hamiltonian evolution for time `τ` equals evolution for time `n * τ`. -/
private theorem hamiltonianEvolution_power {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (τ : ℝ) (n : ℕ) :
    hamiltonianEvolution H τ ^ n = hamiltonianEvolution H ((n : ℝ) * τ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have hgroup : hamiltonianEvolution H ((n : ℝ) * τ + τ)
        = hamiltonianEvolution H ((n : ℝ) * τ) * hamiltonianEvolution H τ :=
      hamiltonianEvolution_add H _ _
    have hcast : ((n : ℝ) + 1) * τ = (n : ℝ) * τ + τ := by ring
    rw [Nat.cast_succ, hcast, hgroup]

/-- The Taylor reset-and-discard construction satisfies `SourceDiscardActualSimulation`,
including its circuit counts, amplified-workspace identity, and state trace-norm error
guarantee. See [BerryEtAl2015Taylor]. -/
theorem sourceDiscardActualSimulation : SourceDiscardActualSimulation := by
  intro J I _ _ _ _ h U j₀ t Λ k hU hHer hΛ ht
  (try simp only [])
  set r := max 1 (Nat.ceil (Λ * t / Real.log 2)) with hrdef
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrNat : 1 ≤ r := le_max_left _ _
  have hrpos : (0 : ℝ) < r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hrNat
    linarith
  have hτ0 : 0 ≤ t / (r : ℝ) := div_nonneg ht hrpos.le
  have hceil : Λ * t / Real.log 2 ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (Λ * t / Real.log 2))))
  have hsmall : (∑ j, |h j|) * |t / (r : ℝ)| ≤ Real.log 2 := by
    have hh : Λ * t ≤ (r : ℝ) * Real.log 2 := (div_le_iff₀ hlog).mp hceil
    have hΛt : (∑ j, |h j|) * t ≤ Λ * t := mul_le_mul_of_nonneg_right hΛ ht
    rw [abs_of_nonneg hτ0]
    have hkey : (∑ j, |h j|) * (t / (r : ℝ)) ≤ (r : ℝ) * Real.log 2 / (r : ℝ) := by
      rw [le_div_iff₀ hrpos]
      calc (∑ j, |h j|) * (t / (r : ℝ)) * (r : ℝ) = (∑ j, |h j|) * t := by
            field_simp
        _ ≤ Λ * t := hΛt
        _ ≤ (r : ℝ) * Real.log 2 := hh
    have hcancel : (r : ℝ) * Real.log 2 / (r : ℝ) = Real.log 2 := by
      field_simp
    rw [hcancel] at hkey
    exact hkey
  obtain ⟨hframe, hwf, hqc, hgc⟩ :=
    taylor_lcu_actual_prepare_select_and_counts_ln2 (I := I) h j₀ (t / (r : ℝ))
      (sourceDiscardCutoffKey r k) hsmall
  obtain ⟨hlwf, hlq, hlg⟩ := source_discard_substituted_ledger
    (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))
    (rangeProjector (taylorFrame (I := I) j₀ (sourceDiscardCutoffKey r k))) r hwf
    (rangeProjector_isOrthogonalProjector (taylorFrame_isIsometry j₀ _))
  have hsub := (substitute_adjoint_evaluate_cost (taylorQuery U (sourceDiscardCutoffKey r k))
    (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))
    (sourceDiscardOAAWord (rangeProjector (taylorFrame (I := I) j₀
      (sourceDiscardCutoffKey r k))))).1
  have hoaa := (source_discard_oaa_semantics
    (evaluate (taylorQuery U (sourceDiscardCutoffKey r k))
      (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)))
    (rangeProjector (taylorFrame (I := I) j₀ (sourceDiscardCutoffKey r k)))).1
  have hFR : (1 : Matrix ((TaylorWordLabel J (sourceDiscardCutoffKey r k) × (Bool × J)) × I)
      ((TaylorWordLabel J (sourceDiscardCutoffKey r k) × (Bool × J)) × I) ℂ) -
      2 * FiberProjector (I := I)
        (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) =
      -FiberReflection (I := I)
        (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) := by
    have hsm : (2 : ℂ) • FiberProjector (I := I)
        (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) =
        2 * FiberProjector (I := I)
          (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) := by
      ext a b
      simp [Matrix.smul_apply, two_mul]
    rw [FiberReflection, ReflectionAbout, hsm, neg_sub]
  have hident : relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k))
      (evaluate (taylorQuery U (sourceDiscardCutoffKey r k))
        (substituteAdjointCircuit (taylorLCUWord h j₀ (t / (r : ℝ))
          (sourceDiscardCutoffKey r k))
          (sourceDiscardOAAWord (rangeProjector (taylorFrame (I := I) j₀
            (sourceDiscardCutoffKey r k)))))) =
      -(relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k))
          (evaluate (taylorQuery U (sourceDiscardCutoffKey r k))
            (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))) *
        FiberReflection (I := I)
          (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) *
        (relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k))
          (evaluate (taylorQuery U (sourceDiscardCutoffKey r k))
            (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))))ᴴ *
        FiberReflection (I := I)
          (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) *
        relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k))
          (evaluate (taylorQuery U (sourceDiscardCutoffKey r k))
            (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)))) := by
    rw [hsub, hoaa, relabelGate_obliviousAmplitudeAmplification,
      relabel_rangeProjector_taylorFrame, ObliviousAmplitudeAmplification,
      Matrix.star_eq_conjTranspose, hFR]
    have keyneg : ∀ (X Y : Matrix ((TaylorWordLabel J (sourceDiscardCutoffKey r k) × (Bool × J)) × I)
          ((TaylorWordLabel J (sourceDiscardCutoffKey r k) × (Bool × J)) × I) ℂ),
        X * (-Y) = -(X * Y) := fun X Y => mul_neg X Y
    rw [keyneg, keyneg]
    simp only [neg_mul, neg_neg]
  refine ⟨⟨hlwf, ?_, ?_⟩, hident, ?_⟩
  · rw [hlq, hqc]
    ring
  · rw [hlg, hgc]
    ring
  · intro ρ hρ htr
    have henc := taylor_discard_block_encoding_ln2 J I h U j₀ (t / (r : ℝ))
      (sourceDiscardCutoffKey r k) hU hsmall
    have hUevo : hamiltonianEvolution (∑ j, (h j : ℂ) • U j) (t / (r : ℝ)) ∈
        Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hHer _
    have hX := taylor_ln2_matrix_remainder J I h U (t / (r : ℝ))
      (sourceDiscardCutoffKey r k) hU hsmall
    have hchan := resetDiscardSegmentation
      (TaylorWordLabel J (sourceDiscardCutoffKey r k) × (Bool × J)) I
      (relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k))
        (evaluate (taylorQuery U (sourceDiscardCutoffKey r k))
          (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))))
      (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀))
      (Polynomial.aeval (∑ j, (h j : ℂ) • U j)
        (exponentialTaylorPolynomial (t / (r : ℝ)) (sourceDiscardCutoffKey r k + 1)))
      (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) (t / (r : ℝ)))
      2 (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) 0 r
      henc hUevo hX (by norm_num) (by norm_num) (by norm_num) ρ hρ htr
    have hm16 : (16 : ℕ) ≤ factorialTaylorPrecision r k := by
      show (16 : ℕ) ≤ 2 * (k + Nat.clog 2 (max 1 r) + 8)
      omega
    have h2mraw := (factorial_taylor_native_cutoff_and_rate.1
      (factorialTaylorPrecision r k)).1
    have h2m : (2 : ℝ) ^ (factorialTaylorPrecision r k) ≤
        (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ) := by
      rw [sourceDiscardCutoffKey]
      exact_mod_cast h2mraw
    have hδle : (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) ≤ 1 := by
      rw [div_le_one₀ (by positivity)]
      calc (2 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
        _ ≤ (2 : ℝ) ^ (factorialTaylorPrecision r k) :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm16
        _ ≤ (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ) := h2m
    have hδpos : (0 : ℝ) ≤ 2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ) :=
      div_nonneg (by positivity)
        (le_of_lt (by exact_mod_cast Nat.factorial_pos ((sourceDiscardCutoffKey r k) + 1)))
    have h31 : (15 + 12 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) +
        4 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) ^ 2) *
        (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) ≤
        31 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) := by
      nlinarith [hδle, hδpos]
    have hbound1 : 4 * (r : ℝ) * ((15 + 12 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) +
        4 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) ^ 2) *
        (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ))) ≤
        124 * (r : ℝ) * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) := by
      calc 4 * (r : ℝ) * ((15 + 12 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) +
          4 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) ^ 2) *
          (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ))) ≤
          4 * (r : ℝ) * (31 * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ))) :=
            mul_le_mul_of_nonneg_left h31 (mul_nonneg (by positivity) hrpos.le)
        _ = 124 * (r : ℝ) * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) := by
            ring
    have hc : (r : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (max 1 r)) := by
      exact_mod_cast (Nat.le_max_right 1 r).trans
        (Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) (max 1 r))
    have hmexp : (factorialTaylorPrecision r k) = 2 * (k + Nat.clog 2 (max 1 r) + 8) := rfl
    have h16pow : (248 : ℝ) * (2 : ℝ) ^ (k + Nat.clog 2 (max 1 r)) ≤
        (2 : ℝ) ^ (k + 2 * Nat.clog 2 (max 1 r) + 16) := by
      calc (248 : ℝ) * (2 : ℝ) ^ (k + Nat.clog 2 (max 1 r))
          ≤ (2 : ℝ) ^ 16 * (2 : ℝ) ^ (k + Nat.clog 2 (max 1 r)) :=
            mul_le_mul_of_nonneg_right (by norm_num : (248 : ℝ) ≤ (2 : ℝ) ^ 16)
              (by positivity)
        _ ≤ (2 : ℝ) ^ 16 * (2 : ℝ) ^ (k + 2 * Nat.clog 2 (max 1 r)) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) (by positivity)
        _ = (2 : ℝ) ^ (k + 2 * Nat.clog 2 (max 1 r) + 16) := by rw [pow_add]; ring
    have hbound2 : 124 * (r : ℝ) *
        (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ)) ≤ (1 / 2 : ℝ) ^ k := by
      have hposf : (0 : ℝ) < (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ) :=
        by exact_mod_cast Nat.factorial_pos _
      rw [show 124 * (r : ℝ) * (2 / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ))
            = 248 * (r : ℝ) / (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ) from by
          (field_simp; ring),
        _root_.one_div_pow,
        div_le_div_iff₀ hposf (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
      rw [one_mul]
      calc 248 * (r : ℝ) * (2 : ℝ) ^ k = 248 * ((r : ℝ) * (2 : ℝ) ^ k) := by ring
        _ ≤ 248 * ((2 : ℝ) ^ (Nat.clog 2 (max 1 r)) * (2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by positivity))
              (by positivity)
        _ = 248 * (2 : ℝ) ^ (k + Nat.clog 2 (max 1 r)) := by rw [pow_add]; ring
        _ ≤ (2 : ℝ) ^ (k + 2 * Nat.clog 2 (max 1 r) + 16) := h16pow
        _ ≤ (2 : ℝ) ^ (factorialTaylorPrecision r k) := by
            rw [hmexp]; exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
        _ ≤ (((sourceDiscardCutoffKey r k) + 1).factorial : ℝ) := h2m
    simp only [mul_zero, add_zero] at hchan
    have hfinal := hchan.trans (le_trans hbound1 hbound2)
    have hpow : hamiltonianEvolution (∑ j, (h j : ℂ) • U j) (t / (r : ℝ)) ^ r =
        hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t := by
      rw [hamiltonianEvolution_power]
      rw [mul_div_cancel₀ t hrpos.ne']
    show Matrix.traceNorm ((ResetDiscardStepCorrected
        (relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k))
          (evaluate (taylorQuery U (sourceDiscardCutoffKey r k))
            (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))))
        (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)))^[r] ρ -
        hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t * ρ *
          (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t)ᴴ) ≤ (1 / 2 : ℝ) ^ k
    rw [← hpow, Matrix.conjTranspose_pow]
    exact hfinal

end Qatlib.Papers.TruncTaylor14.DiscardCore
