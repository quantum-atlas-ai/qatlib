/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib
open scoped Classical

def DlogTwoDimSamplingLaw : Prop :=
  ∀ (p q : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q →
    orderOf g = p - 1 → ∀ r : ℕ, x = g ^ r →
      Normalized (dlogTwoDimState p q g x) ∧
      (∀ (c d : Fin q) (y : ZMod p),
          BornProb (dlogTwoDimState p q g x) (c, d, y)
            = ‖((p - 1 : ℕ) : ℂ)⁻¹ * ∑ a : Fin (p - 1), ∑ b : Fin (p - 1),
                if g ^ (a : ℕ) * x ^ (p - 1 - (b : ℕ)) = y then
                  offGridPhase q ((a : ℕ) / q) c * offGridPhase q ((b : ℕ) / q) d
                else 0‖ ^ 2) ∧
      (∀ (c d : Fin q) (k : ℕ), k < p - 1 →
          BornProb (dlogTwoDimState p q g x) (c, d, g ^ k)
            = ‖((p - 1 : ℕ) : ℂ)⁻¹ * (q : ℂ)⁻¹ * ∑ b : Fin (p - 1),
                Complex.exp (2 * Real.pi * Complex.I *
                  ((((r * (b : ℕ) + k) % (p - 1) : ℕ) : ℝ) * (c : ℕ)
                    + ((b : ℕ) : ℝ) * (d : ℕ)) / (q : ℝ))‖ ^ 2)

end Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
