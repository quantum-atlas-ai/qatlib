/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeCharacterKickbackStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical

def FullRangeFixedPointPrecision : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (K k : ℕ) (f : X → ℝ) (lo s R : ℝ),
    0 < s → 0 ≤ R → s*R < (2 : ℝ)^K →
    (∀ x, lo ≤ f x ∧ f x ≤ lo+R) → ∀ x : X,
    0 ≤ fullRangeInteger k f lo s x ∧ fullRangeInteger k f lo s x < (2^(K+k) : ℕ) ∧
    ((fullRangeValueTable K k f lo s x).val : ℤ) = fullRangeInteger k f lo s x ∧
    (0 ≤ f x-(lo+((fullRangeValueTable K k f lo s x).val : ℝ)/(s*(2 : ℝ)^k)) ∧
      f x-(lo+((fullRangeValueTable K k f lo s x).val : ℝ)/(s*(2 : ℝ)^k)) < 1/(s*(2 : ℝ)^k)) ∧
    ApplyGate (gradientValueOracle (2^(K+k)) (fullRangeValueTable K k f lo s))
      (Ket (x,0)) = Ket (x,fullRangeValueTable K k f lo s x)

end Qatlib.Concepts.GradientOracle.FullRange
