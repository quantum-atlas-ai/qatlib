/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Bound
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Rational and integer readout of amplitude labels

This module turns an AE phase label into a rational dyadic estimate or an integer count
estimate. `dyadicRound` rounds down to a prescribed binary precision, while `countLabelReadout`
and `countLabelReadoutNearest` implement floor and nearest-integer count readout for the
amplitude-estimation and counting setting of [BrassardEtAl2002].

## Main statements

* `dyadicRound_error`: bound the error after dyadic rounding.
* `countLabelReadout_error`: bound floor count-readout error by one.
* `countLabelReadoutNearest_error`: bound nearest count-readout error by one half.
* `countLabelReadoutNearest_tie`: specify upward rounding at a half-integer tie.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- Round `x` down to the rational dyadic value `⌊x * 2^b⌋ / 2^b`. -/
noncomputable def dyadicRound (b : ℕ) (x : ℝ) : ℚ :=
  ((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℚ) / ((2 : ℚ)^b)

/-- Casting dyadic rounding to the reals gives the scaled integer-floor formula. -/
theorem dyadicRound_cast (b : ℕ) (x : ℝ) :
    (dyadicRound b x : ℝ) = ((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) / (2 : ℝ)^b := by
  simp only [dyadicRound]
  push_cast
  ring

/-- The real value of dyadic rounding is at most the input. -/
theorem dyadicRound_le (b : ℕ) (x : ℝ) : (dyadicRound b x : ℝ) ≤ x := by
  have hfloor := Int.floor_le (x * (2 : ℝ)^b)
  have hpos : (0:ℝ) < (2 : ℝ)^b := by positivity
  rw [dyadicRound_cast, div_le_iff₀ hpos]
  exact hfloor

/-- The absolute dyadic-rounding error multiplied by `2^b` is strictly less than one. -/
theorem dyadicRound_error (b : ℕ) (x : ℝ) :
    |(dyadicRound b x : ℝ) - x| * (2 : ℝ)^b < 1 := by
  have hfloor := Int.floor_le (x * (2 : ℝ)^b)
  have hup := Int.lt_floor_add_one (x * (2 : ℝ)^b)
  have hpos : (0:ℝ) < (2 : ℝ)^b := by positivity
  have hid : |((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) / (2 : ℝ)^b - x| * (2 : ℝ)^b
      = |((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) - x * (2 : ℝ)^b| := by
    calc
      |((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) / (2 : ℝ)^b - x| * (2 : ℝ)^b
          = |((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) / (2 : ℝ)^b - x| * |(2 : ℝ)^b| := by
            rw [abs_of_pos hpos]
      _ = |(((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) / (2 : ℝ)^b - x) * (2 : ℝ)^b| := by
            rw [abs_mul]
      _ = |((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) - x * (2 : ℝ)^b| := by
            congr 1
            field_simp
  rw [dyadicRound_cast, hid]
  have h1 : ((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) - x * (2 : ℝ)^b ≤ 0 := by linarith
  have h2 : -1 < ((⌊x * (2 : ℝ)^b⌋ : ℤ) : ℝ) - x * (2 : ℝ)^b := by linarith
  rw [abs_lt]
  constructor
  · linarith
  · linarith

/-- Dyadic rounding fixes zero at every precision. -/
theorem dyadicRound_zero (b : ℕ) : dyadicRound b 0 = 0 := by
  simp [dyadicRound]

/-- Dyadic rounding fixes one at every precision. -/
theorem dyadicRound_one (b : ℕ) : dyadicRound b 1 = 1 := by
  have hpow : (2 : ℝ)^b = (((2 ^ b : ℕ) : ℤ) : ℝ) := by
    have h1 : ((2 ^ b : ℕ) : ℝ) = (2 : ℝ)^b := Nat.cast_pow 2 b
    have h2 : (((2 ^ b : ℕ) : ℤ) : ℝ) = ((2 ^ b : ℕ) : ℝ) := by rfl
    rw [h2, h1]
  have hfloor : (⌊1 * (2 : ℝ)^b⌋ : ℤ) = ((2 ^ b : ℕ) : ℤ) := by
    rw [one_mul, hpow, Int.floor_intCast]
  rw [dyadicRound, hfloor]
  simp [Int.cast_ofNat, Nat.cast_pow]

/-- The rational dyadic rounding of an AE label's amplitude estimate at precision `b`. -/
noncomputable def labelReadout (M : ℕ) (b : ℕ) (z : Fin M) : ℚ :=
  dyadicRound b (aeEstimate M z)

/-- Every AE label's amplitude estimate lies in the interval `[0, 1]`. -/
theorem aeEstimate_mem (M : ℕ) (z : Fin M) : 0 ≤ aeEstimate M z ∧ aeEstimate M z ≤ 1 := by
  constructor
  · exact sq_nonneg _
  · exact Real.sin_sq_le_one _

/-- The natural-number floor of `N` times the AE label's amplitude estimate. -/
noncomputable def countLabelReadout (N : ℕ) (M : ℕ) (z : Fin M) : ℕ :=
  Nat.floor ((N : ℝ) * aeEstimate M z)

/-- Floor count readout never exceeds the population size `N`. -/
theorem countLabelReadout_le (N M : ℕ) (z : Fin M) : countLabelReadout N M z ≤ N := by
  have hle : aeEstimate M z ≤ 1 := (aeEstimate_mem M z).2
  have ha0 : (0:ℝ) ≤ aeEstimate M z := (aeEstimate_mem M z).1
  have hnonneg : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z :=
    mul_nonneg (Nat.cast_nonneg N) ha0
  have hfloor : (Nat.floor ((N : ℝ) * aeEstimate M z) : ℝ)
      ≤ (N : ℝ) * aeEstimate M z := Nat.floor_le hnonneg
  have htop : (N : ℝ) * aeEstimate M z ≤ (N : ℝ) := by
    have := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg N)
    simpa using! this
  have hcast : (Nat.floor ((N : ℝ) * aeEstimate M z) : ℝ) ≤ (N : ℝ) := by linarith
  exact Nat.cast_le.mp hcast

/-- Floor count readout differs from the scaled amplitude estimate by strictly less than one. -/
theorem countLabelReadout_error (N M : ℕ) (z : Fin M) :
    |(countLabelReadout N M z : ℝ) - (N : ℝ) * aeEstimate M z| < 1 := by
  have hle : aeEstimate M z ≤ 1 := (aeEstimate_mem M z).2
  have ha0 : (0:ℝ) ≤ aeEstimate M z := (aeEstimate_mem M z).1
  have hnonneg : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z :=
    mul_nonneg (Nat.cast_nonneg N) ha0
  have hfloor : (Nat.floor ((N : ℝ) * aeEstimate M z) : ℝ)
      ≤ (N :ℝ) * aeEstimate M z := Nat.floor_le hnonneg
  have hup : (N : ℝ) * aeEstimate M z
      < (Nat.floor ((N : ℝ) * aeEstimate M z) : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((N : ℝ) * aeEstimate M z)
    push_cast at h
    exact h
  rw [countLabelReadout, abs_lt]
  constructor
  · linarith
  · linarith

/-- If the scaled amplitude estimate is a natural number `k`, floor count readout returns `k`
exactly. -/
theorem countLabelReadout_exact (N M : ℕ) (z : Fin M) (k : ℕ)
    (h : (N : ℝ) * aeEstimate M z = (k : ℝ)) :
    countLabelReadout N M z = k := by
  have hfloor : Nat.floor ((N : ℝ) * aeEstimate M z) = k := by
    rw [h, Nat.floor_natCast]
  exact hfloor

/-- Floor count readout with population size zero is zero. -/
theorem countLabelReadout_zero (N M : ℕ) (z : Fin M) :
    countLabelReadout 0 M z = 0 := by
  simp [countLabelReadout]

/-- An amplitude estimate equal to one gives floor count readout equal to `N`. -/
theorem countLabelReadout_full (N M : ℕ) (z : Fin M) (h : aeEstimate M z = 1) :
    countLabelReadout N M z = N := by
  have hfloor : Nat.floor ((N : ℝ) * aeEstimate M z) = N := by
    rw [h, mul_one, Nat.floor_natCast]
  exact hfloor

/-- Round the scaled amplitude estimate to a natural number by taking the floor after adding one
half. -/
noncomputable def countLabelReadoutNearest (N : ℕ) (M : ℕ) (z : Fin M) : ℕ :=
  Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2)

/-- Nearest-integer count readout never exceeds the population size `N`. -/
theorem countLabelReadoutNearest_le (N M : ℕ) (z : Fin M) :
    countLabelReadoutNearest N M z ≤ N := by
  have hle : aeEstimate M z ≤ 1 := (aeEstimate_mem M z).2
  have ha0 : (0:ℝ) ≤ aeEstimate M z := (aeEstimate_mem M z).1
  have hnonneg : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z + 1 / 2 :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg N) ha0) (by norm_num)
  have hfloor : (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)
      ≤ (N : ℝ) * aeEstimate M z + 1 / 2 := Nat.floor_le hnonneg
  have htop : (N : ℝ) * aeEstimate M z + 1 / 2 ≤ (N : ℝ) + 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg N)
    simpa using! this
  have hcast : (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)
      ≤ (N : ℝ) + 1 / 2 := by linarith
  have hlt : (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℕ) < N + 1 := by
    have h1 : (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ) < (N : ℝ) + 1 := by linarith
    have h2 : (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)
        < ((N + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using! h1
    exact_mod_cast h2
  rw [countLabelReadoutNearest]
  omega

/-- Nearest-integer count readout differs from the scaled amplitude estimate by at most one
half. -/
theorem countLabelReadoutNearest_error (N M : ℕ) (z : Fin M) :
    |(countLabelReadoutNearest N M z : ℝ) - (N : ℝ) * aeEstimate M z| ≤ 1 / 2 := by
  have ha0 : (0:ℝ) ≤ aeEstimate M z := (aeEstimate_mem M z).1
  have hnonneg : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z + 1 / 2 :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg N) ha0) (by norm_num)
  have hfloor : (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)
      ≤ (N : ℝ) * aeEstimate M z + 1 / 2 := Nat.floor_le hnonneg
  have hup : (N : ℝ) * aeEstimate M z + 1 / 2
      < (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((N : ℝ) * aeEstimate M z + 1 / 2)
    push_cast at h
    exact h
  rw [countLabelReadoutNearest, abs_le]
  constructor
  · linarith
  · linarith

/-- At the half-integer scaled estimate `k + 1/2`, nearest-integer count readout returns `k +
1`. -/
theorem countLabelReadoutNearest_tie (N M : ℕ) (z : Fin M) (k : ℕ)
    (h : (N : ℝ) * aeEstimate M z = (k : ℝ) + 1 / 2) :
    countLabelReadoutNearest N M z = k + 1 := by
  have hfloor : Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) = k + 1 := by
    have hval : ((N : ℝ) * aeEstimate M z + 1 / 2) = (((k + 1 : ℕ) : ℝ)) := by
      rw [h]
      push_cast
      ring
    rw [hval, Nat.floor_natCast]
  exact hfloor
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
