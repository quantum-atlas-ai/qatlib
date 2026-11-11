/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Range

/-!
# Specification of the normalized resonant phase bound

`amplifiedQFTOmega` defines the negative Fourier phase exp(−2πi/N).
`Lemma20RestrictedSpec.expected` records the squared-norm bound for the normalized resonant
progression and noise contribution appearing in Lemma 20 of [Cornwell2014].

## Main statements

* `amplifiedQFTOmega`: The negative Fourier phase exp(−2πi/N).
* `expected`: Specifies that the normalized resonant progression contribution and disjoint noise
  phase sum have squared norm at most one under the stated finite-domain and cardinality
  assumptions.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open scoped BigOperators

namespace Qatlib.Concepts.AmpTransform.ErrorStream

/-- The negative Fourier phase exp(−2πi/N). -/
noncomputable def amplifiedQFTOmega (N : ℕ) : ℂ :=
  Complex.exp (((-2 * Real.pi / (N : ℝ)) : ℂ) * Complex.I)

end Qatlib.Concepts.AmpTransform.ErrorStream

namespace Qatlib.Concepts.AmpTransform.ErrorStream.Lemma20RestrictedSpec

open Qatlib

/-- Specifies that the normalized resonant progression contribution and disjoint noise phase sum
have squared norm at most one under the stated finite-domain and cardinality assumptions. -/
def expected : Prop :=
  (∀ (n N M L T s P y : ℕ) (A G : Finset ℕ),
  N = 2 ^ n →
  A = (Finset.range M).image (fun r => s + r * P) →
  A ⊆ Finset.range N →
  G ⊆ Finset.range N →
  A.card = M →
  G.card = L →
  Disjoint A G →
  T = M + L →
  0 < T →
  y < N →
  y ≠ 0 →
  (P * y) % N = 0 →
  ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y) +
    (1 : ℂ) / (T : ℂ) *
      (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖ ^ 2 ≤ (1 : ℝ))
end Qatlib.Concepts.AmpTransform.ErrorStream.Lemma20RestrictedSpec
