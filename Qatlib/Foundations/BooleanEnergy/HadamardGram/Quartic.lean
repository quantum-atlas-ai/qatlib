/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.HadamardGram.Energy
import Qatlib.Foundations.BooleanEnergy.HadamardGram.PairExpansion

/-!
# Quartic rectangle expansion of Gram energy

This module expands squared column Gram entries into a constant diagonal contribution and
four-spin products indexed by increasing row pairs. Summing over column pairs gives
`energy_rectangles`, the rectangle form of the Hadamard energy considered in
[SuksmonoMinato2019].

## Main statements

* `gram_square_rectangles`: Expand a squared Gram entry.
* `energy_rectangles`: Expand total energy over row-column rectangles.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.HadamardGram

/-- The square of a column-pair Gram entry equals `M` plus twice the sum of four-spin products
over increasing row pairs; see [SuksmonoMinato2019]. -/
theorem gram_square_rectangles {M N : ℕ} (q : Fin M → Fin N → Bool) (p : ColumnPair N) :
    gram q (left p) (right p)^2 = (M:ℝ) + 2*∑ r : ColumnPair M,
      (spin (q (left r) (left p))*spin (q (left r) (right p))) *
      (spin (q (right r) (left p))*spin (q (right r) (right p))) := by
  rw [gram_apply,sum_square_pairs]
  simp only [mul_pow,spin_sq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]

/-- The Gram energy equals `M` times the number of column pairs plus twice the sum of four-spin
rectangle products over row and column pairs. -/
theorem energy_rectangles {M N : ℕ} (q : Fin M → Fin N → Bool) :
    energy q = (M:ℝ)*(Fintype.card (ColumnPair N):ℝ) +
      2*∑ p : ColumnPair N, ∑ r : ColumnPair M,
      (spin (q (left r) (left p))*spin (q (left r) (right p))) *
      (spin (q (right r) (left p))*spin (q (right r) (right p))) := by
  simp only [energy,gram_square_rectangles,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

end Qatlib.Foundations.BooleanEnergy.HadamardGram
