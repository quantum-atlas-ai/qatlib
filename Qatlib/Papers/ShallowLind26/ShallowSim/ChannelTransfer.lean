/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RawChannelWord.CptpWordBound.RawChannelWord
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm

/-!
# Channel transfer and composition (Lemma 2.1)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 2.1, page 6.
The second item of the Lemma is

`‖Φ^m - Ψ^m‖_⋄ ≤ m ‖Φ - Ψ‖_⋄`

for any two channels `Φ, Ψ` and every integer `m ≥ 1`, uniformly in an untouched
reference.  The source proof contracts the telecoping identity

`Φ^m - Ψ^m = ∑_{j<m} Φ^{m-1-j} (Φ - Ψ) Ψ^j`

through the triangle inequality and the contractivity of channels.

We formalize the iteration and the telescoping bound on the library's
finite-reference diamond norm `finiteDiamondNorm`.  Channel contractivity is
`Qatlib.Concepts.RawChannelWord.CptpWordBound.g1`, which proves
the sharp bound one for genuine CPTP maps over arbitrary complex raw inputs.
-/

open Matrix
open scoped BigOperators ENNReal

namespace Qatlib.Papers.ShallowLind26.ShallowSim.ChannelTransfer

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

/-- Iterates a CPTP channel; `pow T 0` is the identity channel and
`pow T (m+1)` is `pow T m` followed by `T`. -/
def channelPow {D : ℕ} (T : QuantumChannel D D) : ℕ → QuantumChannel D D
  | 0 => QuantumChannel.id D
  | m + 1 => (channelPow T m).comp T

/-- The underlying map of the zero-th power is the identity map. -/
@[simp] theorem channelPow_zero_map {D : ℕ} (T : QuantumChannel D D) :
    (channelPow T 0).map = LinearMap.id := rfl

/-- The underlying map of the successor power composes the previous power with
the channel, in that order. -/
@[simp] theorem channelPow_succ_map {D : ℕ} (T : QuantumChannel D D) (m : ℕ) :
    (channelPow T (m + 1)).map = (channelPow T m).map.comp T.map := rfl

/-- **Lemma 2.1, contractivity input.**  Every power of a channel has
finite-reference diamond norm at most one. -/
theorem finiteDiamondNorm_pow_le_one {D : ℕ} (T : QuantumChannel D D) (m : ℕ) :
    finiteDiamondNorm (channelPow T m).map ≤ (1 : ℝ≥0∞) :=
  (g1 D D (channelPow T m)).2.1

/-- **Lemma 2.1(5).**  For two channels on the same system and any `m ≥ 1`,
the diamond norm of the difference of the `m`-th powers is at most `m` times
the diamond norm of the channel difference. -/
theorem finiteDiamondNorm_pow_sub_le {D : ℕ} (T S : QuantumChannel D D) (m : ℕ) :
    finiteDiamondNorm ((channelPow T m).map - (channelPow S m).map)
      ≤ (m : ℝ≥0∞) * finiteDiamondNorm (T.map - S.map) := by
  induction m with
  | zero =>
    simp [channelPow]
  | succ m ih =>
    have hsub : (channelPow T (m + 1)).map - (channelPow S (m + 1)).map
        = ((channelPow T m).map).comp (T.map - S.map)
          + ((channelPow T m).map - (channelPow S m).map).comp S.map := by
      ext Z i j
      simp [channelPow, LinearMap.comp_apply, sub_eq_add_neg]
      abel
    have hcomp₁ := (finiteDiamondNorm_algebra D D D (T.map - S.map)
      (0 : Operator D →ₗ[ℂ] Operator D) (channelPow T m).map).2.1
    have hcomp₂ := (finiteDiamondNorm_algebra D D D S.map
      (0 : Operator D →ₗ[ℂ] Operator D)
      ((channelPow T m).map - (channelPow S m).map)).2.1
    have hT : finiteDiamondNorm (channelPow T m).map ≤ (1 : ℝ≥0∞) :=
      finiteDiamondNorm_pow_le_one T m
    have hS : finiteDiamondNorm S.map ≤ (1 : ℝ≥0∞) := (g1 D D S).2.1
    have hsum : finiteDiamondNorm (((channelPow T m).map).comp (T.map - S.map)
          + ((channelPow T m).map - (channelPow S m).map).comp S.map)
        ≤ finiteDiamondNorm (((channelPow T m).map).comp (T.map - S.map))
          + finiteDiamondNorm (((channelPow T m).map - (channelPow S m).map).comp S.map) :=
      (finiteDiamondNorm_algebra D D D
        (((channelPow T m).map).comp (T.map - S.map))
        (((channelPow T m).map - (channelPow S m).map).comp S.map)
        LinearMap.id).1
    rw [hsub]
    calc finiteDiamondNorm (((channelPow T m).map).comp (T.map - S.map)
          + ((channelPow T m).map - (channelPow S m).map).comp S.map)
        ≤ finiteDiamondNorm (((channelPow T m).map).comp (T.map - S.map))
          + finiteDiamondNorm (((channelPow T m).map - (channelPow S m).map).comp S.map) := hsum
      _ ≤ (finiteDiamondNorm (channelPow T m).map * finiteDiamondNorm (T.map - S.map))
          + (finiteDiamondNorm ((channelPow T m).map - (channelPow S m).map)
              * finiteDiamondNorm S.map) := add_le_add hcomp₁ hcomp₂
      _ ≤ ((1 : ℝ≥0∞) * finiteDiamondNorm (T.map - S.map))
          + ((m : ℝ≥0∞) * finiteDiamondNorm (T.map - S.map) * (1 : ℝ≥0∞)) := by
            exact add_le_add
              (mul_le_mul_left hT _)
              (mul_le_mul' ih hS)
      _ = ((m + 1 : ℕ) : ℝ≥0∞) * finiteDiamondNorm (T.map - S.map) := by
            rw [Nat.cast_add, Nat.cast_one]
            ring

end

end Qatlib.Papers.ShallowLind26.ShallowSim.ChannelTransfer
