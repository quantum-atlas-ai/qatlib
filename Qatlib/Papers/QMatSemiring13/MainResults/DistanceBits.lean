/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatSemiring13.MainResults.DominanceReduction
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults — the `ℓ` most significant bits of the distance product

Le Gall and Nishimura, fixed arXiv:1310.3898v1.
PDF SHA-256 1d042e95c69668deb534b7bc64dacdbeab9ccd52d8c325d88efc1728fd339971.

Section 4.2 of the paper computes the `ℓ` most significant bits of every entry of
the distance product `C[i,j] = min_k (A[i,k] + B[k,j])` by reducing the problem to
`2^ℓ` strict existence dominance products.  Writing `W` for a power of two larger
than every finite entry of `C`, the reduction uses the shifted matrices

`A'_x[i,j] = A[i,j] - x W / 2^{ℓ/2}` and `B'_x[i,j] = -B[i,j] + x W / 2^ℓ`,

and the Boolean matrix `D_d = A'_{d₁} ∗ B'_{d₂}` where `d = d₁ 2^{ℓ/2} + d₂`.

This module proves the two facts the reduction rests on:
* `D_d[i,j] = 0` exactly when every witness satisfies `A[i,k] + B[k,j] ≥ dW/2^ℓ`
  (the paper's `min_k (A[i,k] + B[k,j]) ≥ dW/2^ℓ`);
* consequently, the smallest `d` with `D_d[i,j] = 1` pins `C[i,j]` into the interval
  `[(d-1)W/2^ℓ, dW/2^ℓ)`, which is what "the `ℓ` most significant bits" means.

The finite-carrier hypothesis is the paper's own reduction step ("Assume first that
all the entries of `C` are finite and non-negative"); entries that are `-∞`, `∞`, or
negative are handled in the paper by two extra dominance products and are not
covered here.  Working over `ℚ` rather than `ℤ` keeps `dQ/2^ℓ` exact, which is the
representation the paper's bit expansion `C[i,j] = ∑_k C[i,j]_k W/2^k` uses.

Boundary: the `2^ℓ`-fold dominance reduction itself, and the running times obtained
from it (Theorem 4.2, Theorem 4.3), are not modelled here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMatSemiring13.MainResults

open Matrix

/-- The `(i,j)` entry of the distance product over `ℚ`, as the minimum over `k`.
The minimum of an empty family is `⊤` (`∞`). -/
noncomputable def distEntry {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    WithTop ℚ :=
  (Finset.univ : Finset (Fin n)).inf (fun k => (A i k + B k j : ℚ))

/-- Coercion bookkeeping: a `WithTop ℚ` comparison against a sum of two coerced
rationals is the underlying rational comparison. -/
theorem withTop_coe_le_coe_add {a b c : ℚ} :
    (↑c : WithTop ℚ) ≤ ↑a + ↑b ↔ c ≤ a + b := by
  rw [← WithTop.coe_add, WithTop.coe_le_coe]

/-- The minimum over `k` is at least `c` exactly when every witness is. -/
theorem distEntry_ge_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (i j : Fin n) :
    (c : WithTop ℚ) ≤ distEntry A B i j ↔ ∀ k : Fin n, c ≤ A i k + B k j := by
  rw [distEntry, Finset.le_inf_iff]
  exact ⟨fun h k => withTop_coe_le_coe_add.mp (h k (Finset.mem_univ k)),
    fun h k _ => withTop_coe_le_coe_add.mpr (h k)⟩

/-- Section 4.2, key equivalence: for shifts `α` (applied to `A`) and `β` (applied
to `-B`), the strict existence dominance product `(A - α) ∗ (β - B)` is zero at
`(i,j)` exactly when every witness satisfies `α + β ≤ A[i,k] + B[k,j]`.  With
`α = d₁ W / 2^{ℓ/2}` and `β = d₂ W / 2^ℓ` this is the paper's statement that
`D_d[i,j] = 0` iff the distance product is at least `dW/2^ℓ`. -/
theorem strictExistsDominance_shift_eq_false_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (α β : ℚ) (i j : Fin n) :
    ¬ strictExistsDominance (fun a b => A a b - α) (fun a b => β - B a b) i j ↔
      ∀ k : Fin n, α + β ≤ A i k + B k j := by
  simp only [strictExistsDominance, not_exists, not_lt]
  constructor
  · intro h k
    linarith [h k]
  · intro h k
    linarith [h k]

/-- Section 4.2, stated with the distance product entry: `D_d[i,j] = 0` exactly when
`min_k (A[i,k] + B[k,j]) ≥ dW/2^ℓ`. -/
theorem strictExistsDominance_shift_distEntry_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (α β c : ℚ) (hαβ : α + β = c) (i j : Fin n) :
    ¬ strictExistsDominance (fun a b => A a b - α) (fun a b => β - B a b) i j ↔
      (c : WithTop ℚ) ≤ distEntry A B i j := by
  rw [strictExistsDominance_shift_eq_false_iff, distEntry_ge_iff]
  constructor
  · intro h k
    rw [← hαβ]
    exact h k
  · intro h k
    rw [hαβ]
    exact h k

/-- Section 4.2, bit recovery: if `d` is the smallest index for which
`D_d[i,j] ≠ 0`, then the distance-product entry lies in `[(d-1)W/2^ℓ, dW/2^ℓ)`.
This is exactly the interval that determines the `ℓ` most significant bits of
`C[i,j]`. -/
theorem msb_interval {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) (W : ℚ) (ℓ : ℕ) (i j : Fin n)
    (hnonneg : ∀ k : Fin n, 0 ≤ A i k + B k j)
    (hne : ∃ d : ℕ, ¬ (∀ k : Fin n, (d : ℚ) * W / 2 ^ ℓ ≤ A i k + B k j)) :
    (∀ k : Fin n, ((Nat.find hne : ℚ) - 1) * W / 2 ^ ℓ ≤ A i k + B k j) ∧
      ¬ (∀ k : Fin n, (Nat.find hne : ℚ) * W / 2 ^ ℓ ≤ A i k + B k j) := by
  classical
  have hP0 : ∀ k : Fin n, ((0 : ℕ) : ℚ) * W / 2 ^ ℓ ≤ A i k + B k j := by
    intro k
    simpa using hnonneg k
  have hpos : 0 < Nat.find hne := by
    rcases Nat.eq_zero_or_pos (Nat.find hne) with h | h
    · exact absurd (h ▸ hP0) (Nat.find_spec hne)
    · exact h
  have hcast : ((Nat.find hne : ℚ)) - 1 = ((Nat.find hne - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.find hne)]
    norm_num
  refine ⟨?_, Nat.find_spec hne⟩
  intro k
  have hP := not_not.mp (Nat.find_min hne (Nat.sub_one_lt (Nat.ne_of_gt hpos))) k
  rwa [← hcast] at hP

end Qatlib.Papers.QMatSemiring13.MainResults
