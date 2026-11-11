/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.JuntaLearningDefs

/-!
# Parseval identity and Fourier-sampling normalization

This module proves the uniform Boolean-cube Parseval identity used in [AticiServedio2007], Lemma
II.1. `parseval_identity` equates the sum of squared Fourier coefficients of a real-valued cube
function with its uniform second moment.

For functions taking values of squared magnitude one, `parseval_boolean` gives total Fourier
mass one. Applying this to the sign representation of a Boolean target yields `fsWeight_total`,
the normalization required for the Fourier-sampling distribution.

## Main statements

- `parseval_identity` identifies Fourier squared mass with uniform squared norm.
- `parseval_boolean` specializes this identity to sign-valued functions.
- `fsWeight_total` proves that all Fourier-sampling weights sum to one.

## References

* [Atici and Servedio, 2007][AticiServedio2007], Quantum Algorithms for Learning and Testing
  Juntas, Lemma II.1.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
open scoped BigOperators

variable {n : ℕ}

/-- The sum of squared uniform Fourier coefficients of a real-valued Boolean-cube function
equals its uniform second moment. This is the Parseval identity stated in Lemma II.1 of
[AticiServedio2007]. -/
theorem parseval_identity (F : (Fin n → Bool) → ℝ) :
    ∑ S : Finset (Fin n), uniformFourierCoeff S F ^ 2 =
      uniformExpect (fun x => F x ^ 2) := by
  unfold uniformExpect
  rw [sum_sq_eq_mul_sum_uniformFourierCoeff_sq]
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]

/-- If a real-valued Boolean-cube function has square one at every input, the sum of its squared
uniform Fourier coefficients is one. -/
theorem parseval_boolean (F : (Fin n → Bool) → ℝ)
    (hF : ∀ x, F x ^ 2 = 1) :
    ∑ S : Finset (Fin n), uniformFourierCoeff S F ^ 2 = 1 := by
  rw [parseval_identity]
  unfold uniformExpect
  have hsum : ∑ x : Fin n → Bool, F x ^ 2 = (2 : ℝ) ^ n := by
    rw [Finset.sum_congr rfl (fun x _ => hF x)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [hsum, inv_mul_cancel₀ (by positivity)]

/-- The Fourier-sampling weights of a Boolean target sum to one over all coordinate sets. -/
theorem fsWeight_total (f : (Fin n → Bool) → Bool) :
    ∑ S : Finset (Fin n), fsWeight f S = 1 := by
  unfold fsWeight signCoeff
  exact parseval_boolean (signFun f) (fun x => by unfold signFun; split_ifs <;> norm_num)

end Qatlib.Papers.JuntaLearning07.MainResults
