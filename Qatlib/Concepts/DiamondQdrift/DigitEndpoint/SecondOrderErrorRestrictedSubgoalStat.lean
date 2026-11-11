/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixture
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Restricted second order error specification

This module defines magnitude importance sampling and quadratic approximations `QdriftBranchU`
and `QdriftTargetV`. `SecondOrderErrorRestrictedSubgoal` states an entrywise error bound with
explicit dimension and remainder factors, reflecting the second order cancellation used in
qDRIFT analysis [Campbell2019].

## Main statements

* `qdriftImportanceDist`: sampling probabilities proportional to coefficient magnitudes.
* `SecondOrderErrorRestrictedSubgoal`: the explicit entrywise error specification.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint

open Qatlib
open Matrix

/-- The finite probability law with probabilities `|h j| / Λ` when `Λ` is the positive
coefficient magnitude sum [Campbell2019]. -/
noncomputable def qdriftImportanceDist {J : Type} [Fintype J] (h : J → ℝ) (Λ : ℝ)
    (hΛ : Λ = ∑ j, |h j|) (hΛpos : 0 < Λ) : FinDist J where
  prob := fun j => |h j| / Λ
  nonneg := fun j => div_nonneg (abs_nonneg _) hΛpos.le
  sum_one := by
    have hΛ' : Λ ≠ 0 := hΛpos.ne'
    rw [← Finset.sum_div, ← hΛ, div_self hΛ']

/-- The quadratic branch approximation `1 + dt • A j + dt² • R j`. -/
def QdriftBranchU {J I : Type} [DecidableEq I] (dt : ℝ) (A R : J → Matrix I I ℂ)
    (j : J) : Matrix I I ℂ :=
  1 + (dt : ℂ) • A j + ((dt ^ 2 : ℝ) : ℂ) • R j

/-- The quadratic target approximation `1 + dt • B + dt² • S`. -/
def QdriftTargetV {I : Type} [DecidableEq I] (dt : ℝ) (B S : Matrix I I ℂ) :
    Matrix I I ℂ :=
  1 + (dt : ℂ) • B + ((dt ^ 2 : ℝ) : ℂ) • S

/-- The importance sampled quadratic mixture differs entrywise from the target quadratic
conjugation by at most the stated `dt²` times a polynomial in dimension, coefficient mass,
entry bounds, and remainders [Campbell2019]. -/
def SecondOrderErrorRestrictedSubgoal : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (h : J → ℝ) (H : J → Matrix I I ℂ) (Λ : ℝ)
    (hΛ : Λ = ∑ j, |h j|) (hΛpos : 0 < Λ)
    (dt r : ℝ), 0 ≤ dt → 0 ≤ r →
    ∀ (cH : ℝ), (∀ (j : J) (a b : I), ‖(H j) a b‖ ≤ cH) →
    ∀ (A : J → Matrix I I ℂ),
    (∀ j, A j = (-(Complex.I) * ((Λ * (SignType.sign (h j) : ℝ)) : ℂ)) • H j) →
    ∀ (R : J → Matrix I I ℂ) (S : Matrix I I ℂ),
    (∀ (j : J) (a b : I), ‖(R j) a b‖ ≤ r) → (∀ (a b : I), ‖S a b‖ ≤ r) →
    ∀ (ρ : Matrix I I ℂ) (cρ : ℝ), (∀ (a b : I), ‖ρ a b‖ ≤ cρ) →
    ∀ (a b : I),
    ‖(ChannelMixture (qdriftImportanceDist h Λ hΛ hΛpos) (QdriftBranchU dt A R) ρ
        - QdriftTargetV dt (-(Complex.I) • ∑ j, (h j : ℂ) • H j) S * ρ *
          (QdriftTargetV dt (-(Complex.I) • ∑ j, (h j : ℂ) • H j) S)ᴴ) a b‖
      ≤ dt ^ 2 * (2 * (Fintype.card I : ℝ) ^ 2 * Λ ^ 2 * cH ^ 2 * cρ
          + 4 * (Fintype.card I : ℝ) * r * cρ
          + 4 * (Fintype.card I : ℝ) ^ 2 * Λ * cH * cρ * r * dt
          + 2 * (Fintype.card I : ℝ) ^ 2 * r ^ 2 * cρ * dt ^ 2)

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
