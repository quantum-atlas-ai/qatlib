/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb

open Qatlib
open scoped Classical

def DlogTwoDimSamplingLawLegacy : Prop :=
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
            = ‖((p - 1 : ℕ) : ℂ)⁻¹ * ∑ b : Fin (p - 1),
                Complex.exp (2 * Real.pi * Complex.I *
                  ((((r * (b : ℕ) + k) % (p - 1) : ℕ) : ℝ) * (c : ℕ)
                    + ((b : ℕ) : ℝ) * (d : ℕ)) / (q : ℝ))‖ ^ 2)

end Qatlib.Concepts.PeriodSampling.DlogGoodProb

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997

open Qatlib
open scoped Classical

def DlogGoodOutputProbabilityLegacy : Prop :=
  ∀ (p q r : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q → x = g ^ r →
    (MeasureProb (dlogTwoDimState p q g x)
        (Finset.univ.filter fun t : Fin q × Fin q × ZMod p =>
          dlogGoodPair p q r t.1 t.2.1)
      ≥ (p - 1 : ℝ) / (240 * q)) ∧
    (∀ (c d : Fin q) (k : ℕ), k < p - 1 → dlogGoodPair p q r c d →
        BornProb (dlogTwoDimState p q g x) (c, d, g ^ k) ≥ 1 / (20 * q ^ 2)) ∧
    (q ≤ 2 * (p - 1) →
      MeasureProb (dlogTwoDimState p q g x)
          (Finset.univ.filter fun t : Fin q × Fin q × ZMod p =>
            dlogGoodPair p q r t.1 t.2.1)
        ≥ 1 / 480)

end Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997

open Qatlib
open scoped Classical

def DlogGoodCMarginalLegacy : Prop :=
  ∀ (p q r : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q → x = g ^ r →
    ∀ c : Fin q, dlogSmallResidue p q c →
      (MeasureProb (dlogTwoDimState p q g x)
          (Finset.univ.filter fun t : Fin q × Fin q × ZMod p => t.1 = c)
        ≥ (p - 1 : ℝ) / (20 * q ^ 2)) ∧
      (q ≤ 2 * (p - 1) →
        MeasureProb (dlogTwoDimState p q g x)
            (Finset.univ.filter fun t : Fin q × Fin q × ZMod p => t.1 = c)
          ≥ 1 / (40 * q))

end Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997

open scoped Classical

def DlogPrimePowerDivisibilityLegacy : Prop :=
  ∀ (p q : ℕ) [NeZero p], Nat.Prime p → 3 ≤ p → (p : ℕ) < q →
    (∀ c₁ c₂ : Fin q, dlogSmallResidue p q c₁ → dlogSmallResidue p q c₂ →
        dlogCprime p q c₁ = dlogCprime p q c₂ → c₁ = c₂) ∧
    (∀ c : Fin q, dlogSmallResidue p q c →
        0 ≤ dlogCprime p q c ∧ dlogCprime p q c ≤ (p - 1 : ℕ)) ∧
    (∀ w : ℕ, 2 ≤ w → w ∣ p - 1 →
        (Finset.univ.filter fun c : Fin q =>
            dlogSmallResidue p q c ∧ (w : ℤ) ∣ dlogCprime p q c).card
          ≤ (p - 1) / w + 1)

end Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997
