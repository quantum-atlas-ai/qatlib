/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-!
# Polynomial cost bounds for zeta reconstruction

The predicates `PolyBoundedTwo` and `PolyBoundedThree` are closed under the cost combinations
used here. Substituting the extension-degree bound `max 18 (2 * g)` into a three-variable cost
and multiplying by the number of stages preserves a polynomial bound in genus and logarithmic
field size.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `polyBoundedTwo_mul`: The pointwise product of two polynomially bounded two-variable costs is
  polynomially bounded.
* `polyBoundedThree_eval_max_stage`: Multiplying the substituted cost by `max 18 (2 * g)` still
  gives a polynomial bound in `g` and `lq`.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Cost

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-- A constant multiple of a fixed power of `a + b + 1` is polynomially bounded in two
variables. -/
theorem polyBoundedTwo_const_mul (c k : ℕ) :
    PolyBoundedTwo (fun a b => c * (a + b + 1) ^ k) :=
  ⟨c, k, fun _ _ => le_refl _⟩

/-- The pointwise sum of two polynomially bounded two-variable costs is polynomially bounded. -/
theorem polyBoundedTwo_add {f g : ℕ → ℕ → ℕ}
    (hf : PolyBoundedTwo f) (hg : PolyBoundedTwo g) :
    PolyBoundedTwo (fun a b => f a b + g a b) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, k1 + k2, ?_⟩
  intro a b
  have hbase : 1 ≤ a + b + 1 := by omega
  have b1 : c1 * (a + b + 1) ^ k1 ≤ c1 * (a + b + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_right k1 k2))
  have b2 : c2 * (a + b + 1) ^ k2 ≤ c2 * (a + b + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_left k2 k1))
  calc f a b + g a b
      ≤ c1 * (a + b + 1) ^ k1 + c2 * (a + b + 1) ^ k2 :=
        Nat.add_le_add (h1 a b) (h2 a b)
    _ ≤ c1 * (a + b + 1) ^ (k1 + k2) + c2 * (a + b + 1) ^ (k1 + k2) :=
        Nat.add_le_add b1 b2
    _ = (c1 + c2) * (a + b + 1) ^ (k1 + k2) := by rw [Nat.add_mul]

/-- The pointwise product of two polynomially bounded two-variable costs is polynomially
bounded. -/
theorem polyBoundedTwo_mul {f g : ℕ → ℕ → ℕ}
    (hf : PolyBoundedTwo f) (hg : PolyBoundedTwo g) :
    PolyBoundedTwo (fun a b => f a b * g a b) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, ?_⟩
  intro a b
  calc f a b * g a b
      ≤ (c1 * (a + b + 1) ^ k1) * (c2 * (a + b + 1) ^ k2) :=
        Nat.mul_le_mul (h1 a b) (h2 a b)
    _ = (c1 * c2) * (a + b + 1) ^ (k1 + k2) := by
        have hregroup : c1 * (a + b + 1) ^ k1 * (c2 * (a + b + 1) ^ k2)
            = c1 * c2 * ((a + b + 1) ^ k1 * (a + b + 1) ^ k2) := by ring
        rw [hregroup, ← pow_add]

/-- Multiplication by the repetition factor `19 * (a + b + 1)` preserves a two-variable
polynomial cost bound. -/
theorem polyBoundedTwo_linear_rep (f : ℕ → ℕ → ℕ) (hf : PolyBoundedTwo f) :
    PolyBoundedTwo (fun a b => (19 * (a + b + 1)) * f a b) := by
  obtain ⟨c, k, h⟩ := hf
  refine ⟨19 * c, k + 1, ?_⟩
  intro a b
  have hbase : 1 ≤ a + b + 1 := by omega
  calc (19 * (a + b + 1)) * f a b
      ≤ (19 * (a + b + 1)) * (c * (a + b + 1) ^ k) :=
        Nat.mul_le_mul_left _ (h a b)
    _ = 19 * c * (a + b + 1) ^ (k + 1) := by
        rw [pow_succ]; ring
    _ = (19 * c) * (a + b + 1) ^ (k + 1) := by ring

/-- Substituting `max 18 (2 * g)` for the third argument of a polynomially bounded cost gives a
two-variable polynomial bound. -/
theorem polyBoundedThree_eval_max (f : ℕ → ℕ → ℕ → ℕ)
    (hf : PolyBoundedThree f) :
    PolyBoundedTwo (fun g lq => f g lq (max 18 (2 * g))) := by
  obtain ⟨c, e, hc⟩ := hf
  refine ⟨c * 19 ^ e, e, ?_⟩
  intro g lq
  have hbase : g + lq + max 18 (2 * g) + 1 ≤ 19 * (g + lq + 1) := by
    have : max 18 (2 * g) ≤ 2 * g + 18 := by omega
    omega
  calc f g lq (max 18 (2 * g))
      ≤ c * (g + lq + max 18 (2 * g) + 1) ^ e := hc g lq (max 18 (2 * g))
    _ ≤ c * (19 * (g + lq + 1)) ^ e := by
        exact Nat.mul_le_mul_left _ (pow_le_pow_left' hbase e)
    _ = c * (19 ^ e * (g + lq + 1) ^ e) := by rw [Nat.mul_pow]
    _ = (c * 19 ^ e) * (g + lq + 1) ^ e := by ring

/-- Multiplying the substituted cost by `max 18 (2 * g)` still gives a polynomial bound in `g`
and `lq`. See [Kedlaya2006]. -/
theorem polyBoundedThree_eval_max_stage (f : ℕ → ℕ → ℕ → ℕ)
    (hf : PolyBoundedThree f) :
    PolyBoundedTwo (fun g lq => (max 18 (2 * g)) * f g lq (max 18 (2 * g))) := by
  obtain ⟨c, e, hc⟩ := hf
  refine ⟨c * 19 ^ (e + 1), e + 1, ?_⟩
  intro g lq
  set X : ℕ := g + lq + 1 with hXdef
  have hX : 1 ≤ X := by omega
  have hmax : max 18 (2 * g) ≤ 19 * X := by
    have : max 18 (2 * g) ≤ 2 * g + 18 := by omega
    omega
  have hbase : g + lq + max 18 (2 * g) + 1 ≤ 19 * X := by
    have : max 18 (2 * g) ≤ 2 * g + 18 := by omega
    omega
  have hfbound : f g lq (max 18 (2 * g)) ≤ c * (19 * X) ^ e := by
    calc f g lq (max 18 (2 * g))
        ≤ c * (g + lq + max 18 (2 * g) + 1) ^ e := hc g lq (max 18 (2 * g))
      _ ≤ c * (19 * X) ^ e :=
          Nat.mul_le_mul_left _ (pow_le_pow_left' hbase e)
  calc (max 18 (2 * g)) * f g lq (max 18 (2 * g))
      ≤ (19 * X) * (c * (19 * X) ^ e) :=
        Nat.mul_le_mul hmax hfbound
    _ = c * (19 * X) ^ (e + 1) := by rw [pow_succ]; ring
    _ = c * (19 ^ (e + 1) * X ^ (e + 1)) := by rw [Nat.mul_pow]
    _ = (c * 19 ^ (e + 1)) * X ^ (e + 1) := by ring

end Qatlib.Papers.ZetaCurve04.MainResults.Cost
