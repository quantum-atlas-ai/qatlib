/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


section

set_option backward.isDefEq.respectTransparency false

/-!
# Finite-sum reduction error

Source: arXiv:2501.12378v2, Section 5.2, Eq. (5.2), p. 30.
This extracts the proved quantitative error estimate from the incomplete
hardness candidate. It is independent of any complexity-model predicates.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.KhovanovHom25.MainResults

/-- **Eq. (5.2), quantitative core.**  The Kauffman-bracket approximation error
accumulates over at most `2m² + 5m + 3` bidegrees: if every bidegree Betti
number is known to additive error `ε`, then any signed sum over the Betti
numbers (as it appears in the bracket state sum) has error at most
`(2m² + 5m + 3)·ε`.

The phases `q^j` and `(-1)^i` of eq. (5.2) have modulus one and are therefore
absorbed into the real error bound; this is the exact counting statement of
eq. (5.2) with `m` the number of crossings.  Ranges: homological degrees
`0 ≤ i ≤ m` (`m+1` values) and `q`-degrees `-m-1 ≤ j ≤ m+1` (`2m+3` values),
giving `(m+1)(2m+3) = 2m² + 5m + 3` terms. -/
theorem reduction_error_bound (m : ℕ) (ε : ℝ)
    (β β' : Fin (m + 1) → Fin (2 * m + 3) → ℝ)
    (h : ∀ i j, |β' i j - β i j| ≤ ε) :
    |∑ i, ∑ j, (β' i j - β i j)| ≤ (2 * (m : ℝ) ^ 2 + 5 * m + 3) * ε := by
  have hinner : ∀ i : Fin (m + 1),
      |∑ j, (β' i j - β i j)| ≤ (2 * (m : ℝ) + 3) * ε := by
    intro i
    calc |∑ j, (β' i j - β i j)| ≤ ∑ j, |β' i j - β i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin (2 * m + 3), ε := Finset.sum_le_sum fun j _ => h i j
      _ = (2 * (m : ℝ) + 3) * ε := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  calc |∑ i, ∑ j, (β' i j - β i j)|
      ≤ ∑ i, |∑ j, (β' i j - β i j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (m + 1), (2 * (m : ℝ) + 3) * ε :=
        Finset.sum_le_sum fun i _ => hinner i
    _ = (m + 1 : ℝ) * ((2 * (m : ℝ) + 3) * ε) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring
    _ = (2 * (m : ℝ) ^ 2 + 5 * m + 3) * ε := by ring

end Qatlib.Papers.KhovanovHom25.MainResults
