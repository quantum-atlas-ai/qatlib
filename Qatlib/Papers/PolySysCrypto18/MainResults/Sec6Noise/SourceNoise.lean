/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PolySysCrypto18.MainResults.SourceModel
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults.Sec6Noise


/-- The Hamming weight `‖e‖_H` of a vector over `F_p` (number of nonzero entries). -/
def hammingWeight {p r : ℕ} (e : Fin r → ZMod p) : ℕ :=
  (Finset.univ.filter (fun j => e j ≠ 0)).card

/-- Over a prime residue field, raising each coordinate to `p - 1` gives its nonzero indicator; the sum of the resulting natural representatives is the Hamming weight. -/
theorem lemma_6_2 {p r : ℕ} [Fact p.Prime] (e : Fin r → ZMod p) :
    (∀ j, (e j) ^ (p - 1) = 0 ∨ (e j) ^ (p - 1) = 1) ∧
    (∑ j, ((e j) ^ (p - 1)).val) = hammingWeight e := by
  have hp1 : 0 < p - 1 := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  constructor
  · intro j
    by_cases h : e j = 0
    · left; rw [h]; exact zero_pow (by omega)
    · right; exact ZMod.pow_card_sub_one_eq_one h
  · have hterm : ∀ j, ((e j) ^ (p - 1)).val = if e j = 0 then 0 else 1 := by
      intro j
      by_cases h : e j = 0
      · rw [h, zero_pow (by omega)]; simp
      · rw [ZMod.pow_card_sub_one_eq_one h, ite_eq_right h, ZMod.val_one p]
    simp only [hterm]
    rw [show (∑ j : Fin r, (if e j = 0 then (0:ℕ) else 1))
          = ∑ j : Fin r, (if e j ≠ 0 then (1:ℕ) else 0) from by
        refine Finset.sum_congr rfl ?_
        intro j _
        by_cases h : e j = 0 <;> simp [h]]
    rw [← Finset.sum_filter]
    simp [hammingWeight]

end Qatlib.Papers.PolySysCrypto18.MainResults.Sec6Noise
