/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeisenbergEst25.MainResults.Facts.PaperFact52

set_option backward.isDefEq.respectTransparency false

/-!
# Expected Fidelity Reduction for Inverse-Free State Estimation

This module proves Lemma 4.1, showing that the Schur-Weyl pretty-good-measurement
fidelity expression `eq20` reduces term-by-term to the closed quadratic form
`eq17` (`f_0^2 x_0^2 + ∑_{i=1}^L (f_i x_i + f_{i-1} y_i)^2`) via the Weyl dimension
ratio identities of Fact 5.2.

## Main statements

* `lemma41_expected_fidelity_eq`: `eq20 d L N f = eq17 d L N f` for `2 ≤ d`, `0 < L ≤ N`.

## References

* [Chen, 2025][Chen2025HeisenbergEst], Lemma 4.1, Eq. (17), Section 4, p. 9.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HeisenbergEst25.MainResults.Protocol

open Qatlib.Papers.HeisenbergEst25.MainResults.Model
open Qatlib.Papers.HeisenbergEst25.MainResults.Facts

/-- **Lemma 4.1**: the pretty-good-measurement fidelity expression `eq20` equals the
closed-form tridiagonal sum of squares `eq17` for any probe weight sequence `f`. -/
theorem lemma41_expected_fidelity_eq (d L N : ℕ) (f : ℕ → ℝ)
    (hd : 2 ≤ d) (hL : 0 < L) (hN : L ≤ N) :
    eq20 d L N f = eq17 d L N f := by
  unfold eq20 eq17
  have hx0 : alphaCoeff d L N 0 * Real.sqrt (gammaDimRatio d L N 0) = xCoeff d L N 0 :=
    fact52_alpha_dim_ratio d L N 0 hd hL hN (Nat.zero_le L)
  have hx : ∀ i ∈ Finset.Icc 1 L,
      alphaCoeff d L N i * Real.sqrt (gammaDimRatio d L N i) = xCoeff d L N i :=
    fun i hi => fact52_alpha_dim_ratio d L N i hd hL hN (Finset.mem_Icc.mp hi).2
  have hy : ∀ i ∈ Finset.Icc 1 L,
      betaCoeff d L N (i - 1) * Real.sqrt (gammaDimRatioPrev d L N i) = yCoeff d L N i :=
    fun i hi =>
      fact52_beta_dim_ratio d L N i hd hL hN (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  rw [show (f 0 * alphaCoeff d L N 0 * Real.sqrt (gammaDimRatio d L N 0)) ^ 2 =
      (f 0 * xCoeff d L N 0) ^ 2 by
    rw [show f 0 * alphaCoeff d L N 0 * Real.sqrt (gammaDimRatio d L N 0) =
        f 0 * xCoeff d L N 0 by rw [← hx0]; ring]]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hxi := hx i hi
  have hyi := hy i hi
  rw [show f i * alphaCoeff d L N i * Real.sqrt (gammaDimRatio d L N i) +
        f (i - 1) * betaCoeff d L N (i - 1) * Real.sqrt (gammaDimRatioPrev d L N i) =
      f i * xCoeff d L N i + f (i - 1) * yCoeff d L N i by
    rw [show f i * alphaCoeff d L N i * Real.sqrt (gammaDimRatio d L N i) =
          f i * (alphaCoeff d L N i * Real.sqrt (gammaDimRatio d L N i)) by ring,
      show f (i - 1) * betaCoeff d L N (i - 1) * Real.sqrt (gammaDimRatioPrev d L N i) =
          f (i - 1) * (betaCoeff d L N (i - 1) * Real.sqrt (gammaDimRatioPrev d L N i)) by ring,
      hxi, hyi]]

end Qatlib.Papers.HeisenbergEst25.MainResults.Protocol
