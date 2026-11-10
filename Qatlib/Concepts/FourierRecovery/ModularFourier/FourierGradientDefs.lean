/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefined
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.FullRange
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefined
open Qatlib.Concepts.SignalPrimitive.GridGradient

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open scoped ComplexOrder ENNReal
open Classical BigOperators

theorem nat_succ_le_two_pow (n : ℕ) : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.one_le_two_pow (n := n)
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      calc ((n + 1 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ n + 1 := by rw [hcast]; linarith [ih]
        _ ≤ (2 : ℝ) ^ n * 2 := by nlinarith [h1]
        _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]

theorem exists_two_pow_ge {C : ℝ} (hC : 0 < C) :
    ∃ n : ℕ, C ≤ (2 : ℝ) ^ (n + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  rw [pow_succ]
  have h3 : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := nat_succ_le_two_pow n
  linarith

noncomputable def gradientAssemblyW (ε : ℝ) : ℝ := ε / 4

noncomputable def gradientAssemblyM (d : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (128 * (d : ℝ) / (ε * ε)) + 2

noncomputable def gradientAssemblyM_minimal (d : ℕ) (ε : ℝ) : ℕ :=
  max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε)))

noncomputable def gradientAssemblyK (ε : ℝ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_two_pow_ge (by positivity : 0 < 16 * Real.pi / ε))

def stageB_fourier_gradient_gext_next_spec : Prop :=
  (∀ (k : ℕ),
      abs ((1 : ℝ) / (2 : ℝ) ^ (k + 1) - realRecord k ((1 : ℝ) / (2 : ℝ) ^ (k + 1)))
        = (1 : ℝ) / (2 : ℝ) ^ (k + 1)) ∧
  (∀ (k : ℕ) (m : ℕ),
      abs ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)
        - realRecord k ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)))
        = (1 : ℝ) / (2 : ℝ) ^ (k + 1)) ∧
  (∀ (ε : ℝ) (hε : 0 < ε) (j : ℕ), j < gradientAssemblyK ε hε →
      4 * Real.pi / (2 : ℝ) ^ (j + 1) > ε / 4) ∧
  (∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε),
      2 ≤ gradientAssemblyM_minimal d ε ∧
        16 * (d : ℝ) / ((gradientAssemblyM_minimal d ε : ℝ) * gradientAssemblyW ε) ≤ ε / 2 ∧
        (∀ (M' : ℕ) (hM2 : 2 ≤ M'),
          16 * (d : ℝ) / ((M' : ℝ) * gradientAssemblyW ε) ≤ ε / 2 →
            gradientAssemblyM_minimal d ε ≤ M') ∧
        gradientAssemblyM_minimal d ε ≤ gradientAssemblyM d ε ∧
        gradientAssemblyM d ε - gradientAssemblyM_minimal d ε ≤ 2)

def charRegisterQubits (K k : ℕ) : ℕ := K + k

def gridRegisterQubits (d M : ℕ) : ℕ := d * Nat.clog 2 (max 2 M)

def centeredOutputBits (M : ℕ) : ℕ := Nat.clog 2 (max 2 M) + 1

def qftElementaryGates (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

def knownBasisSetUpGates (K k : ℕ) : ℕ := if k = 0 then 0 else 1

def knownBasisSwap {I : Type} [DecidableEq I] (o a : I) : I → I :=
  fun x => if x = o then a else if x = a then o else x

noncomputable def knownBasisSetUpGate {I : Type} [Fintype I] [DecidableEq I]
    (o a : I) : Matrix I I ℂ :=
  permMatrix (knownBasisSwap o a)

noncomputable def knownBasisSetUpWord (K k : ℕ) : List (Step (ZMod (2 ^ (K + k)))) :=
  if k = 0 then []
  else [.gate (knownBasisSetUpGate 0 (fullRangeCharacterIndex K k))]

noncomputable def gradientHeadlineM (d ε δ : ℝ) : ℕ :=
  max 2 (Nat.ceil (16 * (d : ℝ) / (ε * δ)))

noncomputable def parameterInterval {d : ℕ} (M : ℕ) (w : ℝ) (z : GradientGrid d M) (j : Fin d) :
    ℝ × ℝ :=
  (centeredGridOutput M (z j) - w, centeredGridOutput M (z j) + w)

noncomputable def quantizeStep (w : ℝ) (x : ℝ) : ℤ := ⌊x / w⌋

noncomputable def gradientReadoutLoss (d M k : ℕ) (B w : ℝ) : ℝ :=
  16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B + 4 * Real.pi / (2 : ℝ) ^ (k + 1)

def stageB_fourier_gradient_gext_next2_spec : Prop :=
  (∀ (d ε δ : ℝ) (hd : 0 ≤ d) (hε : 0 < ε) (hδ : 0 < δ),
      2 ≤ gradientHeadlineM d ε δ ∧
      16 * d / ((gradientHeadlineM d ε δ : ℝ) * ε) ≤ δ ∧
      (∀ (M' : ℕ) (hM2 : 2 ≤ M'),
        16 * d / ((M' : ℝ) * ε) ≤ δ → gradientHeadlineM d ε δ ≤ M')) ∧
  (∀ (d M k : ℕ) (hM : 0 < M) (B w : ℝ) (hw : 0 < w),
      1 - gradientReadoutLoss d M k B w ≤ 1 - 4 * Real.pi * B) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (w δ : ℝ) (hw : 0 < w) (hδ : 0 < δ),
      16 * (d : ℝ) / ((M : ℝ) * w) ≤ δ → w ≥ 16 * (d : ℝ) / ((M : ℝ) * δ))

def stageB_fourier_gradient_gext_next3_spec : Prop :=
  (∀ (K k : ℕ),
      knownBasisSetUpGates K k ≤ 1 ∧
      QueryCount (knownBasisSetUpWord K k) = 0 ∧
      GateCount (knownBasisSetUpWord K k) = knownBasisSetUpGates K k) ∧
  (∀ (n : ℕ),
      (localQFT n).countP (fun g => match g with | .h _ => true | _ => false) = n ∧
      (localQFT n).countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
        = n * (n - 1) / 2 ∧
      (localQFT n).countP (fun g => match g with | .swap _ _ => true | _ => false) = n / 2 ∧
      (localQFT n).length = qftElementaryGates n) ∧
  (∀ (d M K k : ℕ),
      readoutSpaceBits d M K k = gridRegisterQubits d M + charRegisterQubits K k ∧
      readoutIntegerBits K k = charRegisterQubits K k) ∧
  (∀ (m : ℕ) (z : Fin (2 ^ m)),
      |(2 : ℝ) ^ m * centeredGridOutput (2 ^ m) z| ≤ (2 : ℝ) ^ (m - 1)) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (w : ℝ)
      (hg : ∀ j : Fin d, |g j| ≤ 1 / 4) (hw : w ≤ 1 / 8)
      (z : GradientGrid d M)
      (hgood : ∀ j : Fin d, phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w),
      ∀ j : Fin d,
        (parameterInterval M w z j).1 ≤ g j ∧ g j ≤ (parameterInterval M w z j).2) ∧
  (∀ (d : ℕ) (g ê : Fin d → ℝ) (w : ℝ),
      (∀ j : Fin d, |ê j - g j| ≤ w) →
      (∑ j : Fin d, ê j * g j) - (∑ j : Fin d, g j ^ 2) ≥ -w * ∑ j : Fin d, |g j|)

end Qatlib.Concepts.FourierRecovery.ModularFourier
