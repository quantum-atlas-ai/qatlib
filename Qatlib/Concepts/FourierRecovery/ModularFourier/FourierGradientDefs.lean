/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefined

/-!
# Parameters and specifications for Fourier gradient assembly

This module defines explicit window widths, grid sizes, and record precisions for finite
precision Fourier gradient readout. `gradientAssemblyM_minimal` and `gradientHeadlineM` encode
the grid choices used in the associated minimality statements. The numerical gradient estimation
setting follows [Jordan2005Gradient].

It also defines basis setup words, register and elementary QFT budgets, parameter intervals,
quantization, and the combined `gradientReadoutLoss`. The specification propositions collect the
corresponding accuracy, minimality, and resource claims.

## Main statements

* `gradientAssemblyK`: the least precision meeting the chosen power of two threshold.
* `gradientReadoutLoss`: the sum of window, residual, and recording losses.
* `stageB_fourier_gradient_gext_next3_spec`: implementation counts and output certificates.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

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

/-- For every natural `n`, the real number `n + 1` is at most `2^n`. -/
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

/-- Every positive real number is bounded above by `2^(n + 1)` for some natural `n`. -/
theorem exists_two_pow_ge {C : ℝ} (hC : 0 < C) :
    ∃ n : ℕ, C ≤ (2 : ℝ) ^ (n + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  rw [pow_succ]
  have h3 : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := nat_succ_le_two_pow n
  linarith

/-- The assembled gradient window width `ε / 4`. -/
noncomputable def gradientAssemblyW (ε : ℝ) : ℝ := ε / 4

/-- The assembled grid size `ceil (128 * d / ε^2) + 2`. -/
noncomputable def gradientAssemblyM (d : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (128 * (d : ℝ) / (ε * ε)) + 2

/-- The grid size `max 2 (ceil (128 * d / ε^2))` used for the minimal window budget. -/
noncomputable def gradientAssemblyM_minimal (d : ℕ) (ε : ℝ) : ℕ :=
  max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε)))

/-- The least natural record precision whose power of two meets the threshold `16 * π / ε`. -/
noncomputable def gradientAssemblyK (ε : ℝ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_two_pow_ge (by positivity : 0 < 16 * Real.pi / ε))

/-- The specification combining sharp recording errors, minimal record precision, and minimal
grid size with a bound on the assembled size excess. -/
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

/-- The character register width `K + k`. -/
def charRegisterQubits (K k : ℕ) : ℕ := K + k

/-- The grid register budget `d * Nat.clog 2 (max 2 M)`. -/
def gridRegisterQubits (d M : ℕ) : ℕ := d * Nat.clog 2 (max 2 M)

/-- The signed centered output budget `Nat.clog 2 (max 2 M) + 1`. -/
def centeredOutputBits (M : ℕ) : ℕ := Nat.clog 2 (max 2 M) + 1

/-- The elementary QFT gate count, including Hadamards, controlled phase gates, and swaps. -/
def qftElementaryGates (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

/-- The known basis setup gate count, equal to zero for `k = 0` and one otherwise. -/
def knownBasisSetUpGates (K k : ℕ) : ℕ := if k = 0 then 0 else 1

/-- The permutation interchanging `o` and `a` and fixing every other label. -/
def knownBasisSwap {I : Type} [DecidableEq I] (o a : I) : I → I :=
  fun x => if x = o then a else if x = a then o else x

/-- The permutation matrix that exchanges the specified origin and target basis labels. -/
noncomputable def knownBasisSetUpGate {I : Type} [Fintype I] [DecidableEq I]
    (o a : I) : Matrix I I ℂ :=
  permMatrix (knownBasisSwap o a)

/-- The empty setup word for `k = 0`, and otherwise a single gate exchanging zero with the full
range character index. -/
noncomputable def knownBasisSetUpWord (K k : ℕ) : List (Step (ZMod (2 ^ (K + k)))) :=
  if k = 0 then []
  else [.gate (knownBasisSetUpGate 0 (fullRangeCharacterIndex K k))]

/-- The grid size `max 2 (ceil (16 * d / (ε * δ)))` for separate accuracy and failure
tolerances. -/
noncomputable def gradientHeadlineM (d ε δ : ℝ) : ℕ :=
  max 2 (Nat.ceil (16 * (d : ℝ) / (ε * δ)))

/-- The interval of radius `w` centered at coordinate `j` of the centered grid output. -/
noncomputable def parameterInterval {d : ℕ} (M : ℕ) (w : ℝ) (z : GradientGrid d M) (j : Fin d) :
    ℝ × ℝ :=
  (centeredGridOutput M (z j) - w, centeredGridOutput M (z j) + w)

/-- The integer floor of a real value divided by the quantization step `w`. -/
noncomputable def quantizeStep (w : ℝ) (x : ℝ) : ℤ := ⌊x / w⌋

/-- The sum of Fourier window loss, stationary phase residual loss, and finite record loss. -/
noncomputable def gradientReadoutLoss (d M k : ℕ) (B w : ℝ) : ℝ :=
  16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B + 4 * Real.pi / (2 : ℝ) ^ (k + 1)

/-- The specification for minimal headline grid size, the stationary residual loss ceiling, and
the accuracy bound implied by a confidence budget. -/
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

/-- The specification for basis setup cost, elementary QFT counts, register widths, centered
output magnitude, certified parameter intervals, and gradient inner products. -/
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
