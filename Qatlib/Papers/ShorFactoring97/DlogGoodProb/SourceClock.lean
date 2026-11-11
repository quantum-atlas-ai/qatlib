/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodOutputProbabilityShor
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Actual Born bounds in the source clock window

The source quant-ph/9508027v2 §6 chooses q = 2^t with p < q < 2p.
The installed finite proof uses q ≤ 2(p-1); evenness makes that guard
automatic in the source window. No uniform-good conditional law is assumed.
The pointwise 1/(16q²) bound also implies the printed decimal 0.054/q².
These results do not implement modular arithmetic, the sampling circuit,
the uniform-good tail transport, or effective CRT recovery.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShorFactoring97.DlogGoodProb

open scoped Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib.Concepts.PeriodSampling.DlogGoodProb

/-- Evenness of the source power-of-two clock implies the finite proof's guard. -/
theorem source_clock_guard (p t : ℕ) (hp : 3 ≤ p)
    (hlo : p < 2 ^ t) (hhi : 2 ^ t < 2 * p) : 2 ^ t ≤ 2 * (p - 1) := by
  cases t with
  | zero => norm_num at hlo; omega
  | succ t => rw [pow_succ] at hhi ⊢; omega

/-- The actual source-window state is normalized and has good mass at least 1/480. -/
theorem source_clock_good_mass (p t r : ℕ) [NeZero p]
    (g x : ZMod p) (hp : p.Prime) (hp3 : 3 ≤ p) (hx0 : x ≠ 0)
    (hpq : p < 2 ^ t) (hqhi : 2 ^ t < 2 * p)
    (ho : orderOf g = p - 1) (hx : x = g ^ r) :
    Normalized (dlogTwoDimState p (2 ^ t) g x) ∧
    (1 / 480 : ℝ) ≤ MeasureProb (dlogTwoDimState p (2 ^ t) g x)
      (Finset.univ.filter fun o : Fin (2 ^ t) × Fin (2 ^ t) × ZMod p =>
        dlogGoodPair p (2 ^ t) r o.1 o.2.1) := by
  exact ⟨(dlogTwoDimSamplingLaw p (2 ^ t) g x hp hp3 hx0 hpq ho r hx).1,
    (DlogGoodOutputProbability_proof p (2 ^ t) r g x hp hp3 hx0 hpq ho hx).2.2
      (source_clock_guard p t hp3 hpq hqhi)⟩

/-- The true finite Born probability implies the source's decimal lower bound. -/
theorem source_decimal_point_bound (p q r : ℕ) [NeZero p] (g x : ZMod p)
    (hp : 3 ≤ p) (hprime : p.Prime) (hx0 : x ≠ 0) (hpq : p < q)
    (ho : orderOf g = p - 1) (hx : x = g ^ r)
    (c d : Fin q) (k : ℕ) (hk : k < p - 1) (hgood : dlogGoodPair p q r c d) :
    (0.054 : ℝ) / (q : ℝ) ^ 2 ≤ BornProb (dlogTwoDimState p q g x) (c, d, g ^ k) := by
  have h := dlog_good_state_probability_strong p q r g x hp hprime hx0 hpq ho hx c d k hk hgood
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hden : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hq
  have hsmall : (0.054 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (16 * (q : ℝ) ^ 2) := by
    field_simp
    nlinarith
  exact hsmall.trans h

end Qatlib.Papers.ShorFactoring97.DlogGoodProb
