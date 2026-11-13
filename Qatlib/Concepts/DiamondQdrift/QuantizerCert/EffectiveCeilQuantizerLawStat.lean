/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore

/-!
# Rational lower oracles and ceiling quantization

This module defines `RatLowerOracle`, the mass certificate `ceilQuantizerCert`, and the integer
weight construction `effectiveCeilQuantizer`. `EffectiveCeilQuantizerLaw` states bounds on the
least certified precision, total weight, and normalized law error for finite sampling in the
qDRIFT setting of [Campbell2019].

## Main statements

* `effectiveQuantizerPrecision`: the infimum of certified natural precisions.
* `EffectiveCeilQuantizerLaw`: precision and probability approximation guarantees.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.DiamondQdrift.QuantizerCert

open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- A nonnegative rational lower approximation to `x` at every precision `k`, with deficit at
most `2⁻ᵏ`. -/
def RatLowerOracle (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k, 0 ≤ q k ∧ (q k : ℝ) ≤ x ∧ x - (q k : ℝ) ≤ ((2 : ℝ)⁻¹)^k

/-- The sum of the rational lower coefficient approximations at precision `k`, cast to the
reals. -/
def ratLowerMass {L : ℕ} (q : Fin L → ℕ → ℚ) (k : ℕ) : ℝ := ∑ j, (q j k : ℝ)

/-- The lower mass at precision `k` dominates the quantization uncertainty `2 * L * (M + 1) *
2⁻ᵏ`. -/
def ceilQuantizerCert {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (k : ℕ) : Prop :=
  (2*(L : ℝ)*((M : ℝ)+1))*((2 : ℝ)⁻¹)^k ≤ ratLowerMass q k

/-- The infimum of the natural precisions satisfying `ceilQuantizerCert`. -/
noncomputable def effectiveQuantizerPrecision {L : ℕ} (M : ℕ)
    (q : Fin L → ℕ → ℚ) : ℕ := sInf {k : ℕ | ceilQuantizerCert M q k}

/-- Assign each coefficient the natural ceiling of `M` times its rational lower approximation
divided by the lower mass, then add one. -/
noncomputable def effectiveCeilQuantizer {L : ℕ} (q : Fin L → ℕ → ℚ)
    (k M : ℕ) : Fin L → ℕ :=
  fun j => Nat.ceil ((M : ℝ)*(q j k : ℝ)/ratLowerMass q k)+1

/-- For valid lower oracles, positive mass, and positive scale, the selected precision is
certified and bounded, the total weight is between `M` and `M + 2 * L`, and normalized law
error is at most `4 * L / M`. -/
def EffectiveCeilQuantizerLaw : Prop :=
  ∀ (L M : ℕ) (h : Fin L → ℝ) (q : Fin L → ℕ → ℚ),
    (∀ j, RatLowerOracle (h j) (q j)) → 0 < ∑ j, h j → 0 < M →
    let k := effectiveQuantizerPrecision M q
    let w := effectiveCeilQuantizer q k M
    let W := weightTotal w
    ceilQuantizerCert M q k ∧
    k ≤ Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j))) ∧
    (M ≤ W ∧ (∑ j, (w j : ℝ)) ≤ M+2*(L : ℝ)) ∧
    (∑ j, |((w j : ℝ)/(W : ℝ))-h j/(∑ j, h j)|) ≤ 4*(L : ℝ)/M

end Qatlib.Concepts.DiamondQdrift.QuantizerCert
