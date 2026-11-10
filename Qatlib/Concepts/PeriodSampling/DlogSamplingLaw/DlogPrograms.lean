/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib

def centeredResidue (q : ℤ) (z : ℤ) : ℤ :=
  let r := z % q
  if r ≤ q / 2 then r else r - q

def dlogTwoDimState (p q : ℕ) (g x : ZMod p) :
    QState (Fin q × Fin q × ZMod p) :=
  fun t =>
    ((p - 1 : ℕ) : ℂ)⁻¹ * ∑ a : Fin (p - 1), ∑ b : Fin (p - 1),
      if g ^ (a : ℕ) * x ^ (p - 1 - (b : ℕ)) = t.2.2 then
        offGridPhase q ((a : ℕ) / q) t.1 * offGridPhase q ((b : ℕ) / q) t.2.1
      else 0

def dlogSmallResidue (p q : ℕ) (c : Fin q) : Prop :=
  |(centeredResidue (q : ℤ) (((c : ℕ) * (p - 1) : ℤ)) : ℤ)| ≤ (q : ℝ) / 12

noncomputable def dlogT (p q r : ℕ) (c d : Fin q) : ℝ :=
  (r * (c : ℕ) + (d : ℕ) : ℝ) -
    (r : ℝ) / ((p - 1 : ℕ) : ℝ) *
      ((centeredResidue (q : ℤ) (((c : ℕ) * (p - 1) : ℤ)) : ℤ) : ℝ)

def dlogGoodPair (p q r : ℕ) (c d : Fin q) : Prop :=
  (∃ j : ℤ, |dlogT p q r c d - (j : ℝ) * (q : ℝ)| ≤ 1 / 2) ∧
    dlogSmallResidue p q c

def dlogCprime (p q : ℕ) (c : Fin q) : ℤ :=
  (((c : ℕ) * (p - 1) : ℤ) -
    centeredResidue (q : ℤ) (((c : ℕ) * (p - 1) : ℤ))) / (q : ℤ)

end Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
