/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ScatteringQFT11.MainResults.NegativeMassBounds

@[expose] public section


set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix

open Qatlib.Papers.ScatteringQFT11.MainResults
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ScatteringQFT11.MainResults

/-- The stronger completed-square estimate also implies the literal v1 Eq. (80),
whose leading coefficient is -24; v2 corrected that coefficient to -6. -/
theorem phi4_v1_field_bound {n sites : Type*} [Fintype n] [DecidableEq n]
    [Fintype sites] [DecidableEq sites] (d : ℕ) (a m0sq lam : ℝ)
    (ha : 0 < a) (hm : m0sq ≤ 0) (hl : 0 < lam)
    (gradSq phi piOp : sites → Matrix n n ℂ)
    (hgrad : ∀ y, (gradSq y).PosSemidef) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (hpi : ∀ y, (piOp y)ᴴ = piOp y) (ψ : QState n) (hψ : Normalized ψ) {E : ℝ}
    (hE : expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ ≤ E) (x : sites) :
    expectation (phi x * phi x) ψ ≤ -24 * m0sq / lam
      + Real.sqrt (36 * m0sq ^ 2 / lam ^ 2
        + 24 / (lam * a ^ d)
          * (E + 3 * (((Fintype.card sites : ℝ) * a ^ d) - a ^ d) * m0sq ^ 2 / (2 * lam))) := by
  have hbound := phi4_negative_mass_field_bound d a m0sq lam ha hm hl
    gradSq phi piOp hgrad hphi hpi ψ hψ hE x
  have hdiv : m0sq / lam ≤ 0 := div_nonpos_of_nonpos_of_nonneg hm hl.le
  have hlead : -6 * m0sq / lam ≤ -24 * m0sq / lam := by
    calc -6 * m0sq / lam = -6 * (m0sq / lam) := by ring
      _ ≤ -24 * (m0sq / lam) := by linarith
      _ = -24 * m0sq / lam := by ring
  linarith

end Qatlib.Papers.ScatteringQFT11.MainResults
