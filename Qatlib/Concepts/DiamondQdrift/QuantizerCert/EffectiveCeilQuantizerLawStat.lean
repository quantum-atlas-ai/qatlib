/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQDrift
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.DiamondQdrift.QuantizerCert

open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

def RatLowerOracle (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k, 0 ≤ q k ∧ (q k : ℝ) ≤ x ∧ x - (q k : ℝ) ≤ ((2 : ℝ)⁻¹)^k

def ratLowerMass {L : ℕ} (q : Fin L → ℕ → ℚ) (k : ℕ) : ℝ := ∑ j, (q j k : ℝ)

def ceilQuantizerCert {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (k : ℕ) : Prop :=
  (2*(L : ℝ)*((M : ℝ)+1))*((2 : ℝ)⁻¹)^k ≤ ratLowerMass q k

noncomputable def effectiveQuantizerPrecision {L : ℕ} (M : ℕ)
    (q : Fin L → ℕ → ℚ) : ℕ := sInf {k : ℕ | ceilQuantizerCert M q k}

noncomputable def effectiveCeilQuantizer {L : ℕ} (q : Fin L → ℕ → ℚ)
    (k M : ℕ) : Fin L → ℕ :=
  fun j => Nat.ceil ((M : ℝ)*(q j k : ℝ)/ratLowerMass q k)+1

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
