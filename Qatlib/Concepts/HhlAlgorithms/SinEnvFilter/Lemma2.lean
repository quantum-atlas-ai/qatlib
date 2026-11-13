/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.FilterBounds
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# HHL filter distance and Lipschitz continuity

`source_lemma2_distance_eq` expresses the distance between normalized filter vectors in terms of
their real overlap. `source_lemma2_lipschitz` bounds that distance by `2 * κ` times the phase
difference, giving the filter estimate associated with Lemma 2 of [HarrowHassidimLloyd2009].

## Main statements

* `source_lemma2_distance_eq`: the overlap formula for filter distance.
* `source_lemma2`: the distance identity and Lipschitz estimate together.

## References

* [Harrow et al., 2009, Lemma 2][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma2

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Foundations.PureStateMath
open scoped Real

/-- The distance between the two normalized three-state filter vectors equals the square root of
twice one minus their real overlap; see [Harrow et al., Lemma 2][HarrowHassidimLloyd2009]. -/
theorem source_lemma2_distance_eq (κ lam₁ lam₂ : ℝ) (hκ : 0 < κ) :
    Real.sqrt (∑ s : Fin 3, ‖sinEnvelopeHVector (1 / (2 * κ)) lam₁ s -
        sinEnvelopeHVector (1 / (2 * κ)) lam₂ s‖ ^ 2) =
      Real.sqrt (2 * (1 - ∑ s : Fin 3,
        (sinEnvelopeHVector (1 / (2 * κ)) lam₁ s *
          star (sinEnvelopeHVector (1 / (2 * κ)) lam₂ s)).re)) := by
  have hd : (0 : ℝ) < 1 / (2 * κ) := by positivity
  have hn₁ := source_filter_normalized κ lam₁ hκ
  have hn₂ := source_filter_normalized κ lam₂ hκ
  set a : QState (Fin 3) := sinEnvelopeHVector (1 / (2 * κ)) lam₁ with ha
  set b : QState (Fin 3) := sinEnvelopeHVector (1 / (2 * κ)) lam₂ with hb
  have haN : ∑ s : Fin 3, Complex.normSq (a s) = 1 := by
    simpa only [ha, Complex.normSq_eq_norm_sq] using hn₁
  have hbN : ∑ s : Fin 3, Complex.normSq (b s) = 1 := by
    simpa only [hb, Complex.normSq_eq_norm_sq] using hn₂
  have hmain : ∑ s : Fin 3, ‖a s - b s‖ ^ 2 =
      2 * (1 - ∑ s : Fin 3, (a s * star (b s)).re) := by
    calc
      ∑ s : Fin 3, ‖a s - b s‖ ^ 2
          = ∑ s : Fin 3, (Complex.normSq (a s) + Complex.normSq (b s) -
              2 * (a s * star (b s)).re) := by
            refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [← Complex.normSq_eq_norm_sq]
            exact Complex.normSq_sub (a s) (b s)
      _ = (∑ s : Fin 3, Complex.normSq (a s)) + (∑ s : Fin 3, Complex.normSq (b s)) -
            2 * (∑ s : Fin 3, (a s * star (b s)).re) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 2 * (1 - ∑ s : Fin 3, (a s * star (b s)).re) := by
            rw [haN, hbN]
            ring
  simpa only [ha, hb] using congrArg Real.sqrt hmain

/-- For positive `κ` and distinct phases, the three-state filter distance is at most `2 * κ *
|lam₁ - lam₂|`, as in [Harrow et al., Lemma 2][HarrowHassidimLloyd2009]. -/
theorem source_lemma2_lipschitz (κ lam₁ lam₂ : ℝ) (hκ : 0 < κ) (hne : lam₁ ≠ lam₂) :
    Real.sqrt (∑ s : Fin 3, ‖sinEnvelopeHVector (1 / (2 * κ)) lam₁ s -
        sinEnvelopeHVector (1 / (2 * κ)) lam₂ s‖ ^ 2) ≤ 2 * κ * |lam₁ - lam₂| := by
  have h := source_filter_lipschitz κ lam₁ lam₂ hκ
  simpa only [Pi.sub_apply] using h

/-- Combines the overlap formula for the three-state filter distance with its `2 * κ` Lipschitz
bound; see [Harrow et al., Lemma 2][HarrowHassidimLloyd2009]. -/
theorem source_lemma2 (κ lam₁ lam₂ : ℝ) (hκ : 0 < κ) (hne : lam₁ ≠ lam₂) :
    Real.sqrt (∑ s : Fin 3, ‖sinEnvelopeHVector (1 / (2 * κ)) lam₁ s -
        sinEnvelopeHVector (1 / (2 * κ)) lam₂ s‖ ^ 2) =
      Real.sqrt (2 * (1 - ∑ s : Fin 3,
        (sinEnvelopeHVector (1 / (2 * κ)) lam₁ s *
          star (sinEnvelopeHVector (1 / (2 * κ)) lam₂ s)).re)) ∧
    Real.sqrt (∑ s : Fin 3, ‖sinEnvelopeHVector (1 / (2 * κ)) lam₁ s -
        sinEnvelopeHVector (1 / (2 * κ)) lam₂ s‖ ^ 2) ≤ 2 * κ * |lam₁ - lam₂| :=
  ⟨source_lemma2_distance_eq κ lam₁ lam₂ hκ,
    source_lemma2_lipschitz κ lam₁ lam₂ hκ hne⟩

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma2
