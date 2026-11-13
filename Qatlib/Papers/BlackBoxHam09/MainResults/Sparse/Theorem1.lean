/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs

/-!
# Theorem 1 step count and query budget arithmetic

This module selects `theorem1Steps` as the maximum of two natural ceilings and defines the
corresponding parameter `theorem1Eps`. It proves that this parameter meets the Lemma 4 range and
a scalar walk error bound, while `theorem1_repeat_query_budget` bounds the oracle count of a
repeated circuit from an assumed per-step query bound.

These estimates accompany the sparse simulation bound of Theorem 1 in [BerryChilds2012].

## Main statements

* `theorem1Eps_le_lemma4_range` bounds the selected parameter.
* `theorem1_repeat_query_budget` bounds the oracle count of a repeated circuit.

## References

* [Berry and Childs, 2012][BerryChilds2012]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Sparse

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

/-- For nonnegative norm bounds and time and positive `δ`, the Theorem 1 query expression is
strictly positive. -/
theorem theorem1QueryExpr_pos {Λ Λmax t δ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛmax0 : 0 ≤ Λmax) (hδ0 : 0 < δ) (ht : 0 ≤ t) (D : ℕ) :
    0 < theorem1QueryExpr Λ D Λmax t δ := by
  unfold theorem1QueryExpr
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hfirst : 0 ≤ Λ * t / Real.sqrt δ := div_nonneg (mul_nonneg hΛ0 ht) hsqrt.le
  have hsecond : 0 ≤ (D : ℝ) * Λmax * t :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg D) hΛmax0) ht
  linarith

/-- The maximum of the natural ceilings of `Λ * t / sqrt δ` and `Λmax * D * t`, used as the step
count for Theorem 1. See [Berry and Childs, Theorem 1][BerryChilds2012]. -/
def theorem1Steps (Λ Λmax t δ : ℝ) (D : ℕ) : ℕ :=
  max ⌈Λ * t / Real.sqrt δ⌉₊ ⌈Λmax * (D : ℝ) * t⌉₊

/-- The selected step count is at least `Λ * t / sqrt δ`. -/
theorem theorem1Steps_ge_first (Λ Λmax t δ : ℝ) (D : ℕ) :
    Λ * t / Real.sqrt δ ≤ (theorem1Steps Λ Λmax t δ D : ℝ) := by
  have h1 := Nat.le_ceil (Λ * t / Real.sqrt δ)
  have h2 : ⌈Λ * t / Real.sqrt δ⌉₊ ≤ theorem1Steps Λ Λmax t δ D := le_max_left _ _
  calc Λ * t / Real.sqrt δ ≤ (⌈Λ * t / Real.sqrt δ⌉₊ : ℝ) := h1
    _ ≤ (theorem1Steps Λ Λmax t δ D : ℝ) := by exact_mod_cast h2

/-- The selected step count is at least `Λmax * D * t`. -/
theorem theorem1Steps_ge_second (Λ Λmax t δ : ℝ) (D : ℕ) :
    Λmax * (D : ℝ) * t ≤ (theorem1Steps Λ Λmax t δ D : ℝ) := by
  have h1 := Nat.le_ceil (Λmax * (D : ℝ) * t)
  have h2 : ⌈Λmax * (D : ℝ) * t⌉₊ ≤ theorem1Steps Λ Λmax t δ D := le_max_right _ _
  calc Λmax * (D : ℝ) * t ≤ (⌈Λmax * (D : ℝ) * t⌉₊ : ℝ) := h1
    _ ≤ (theorem1Steps Λ Λmax t δ D : ℝ) := by exact_mod_cast h2

/-- The selected step count is positive when `Λ`, `t`, and `δ` are positive. -/
theorem theorem1Steps_pos {Λ Λmax t δ : ℝ} {D : ℕ}
    (hΛ0 : 0 < Λ) (ht : 0 < t) (hδ0 : 0 < δ) :
    0 < theorem1Steps Λ Λmax t δ D := by
  have ha : 0 < Λ * t / Real.sqrt δ :=
    div_pos (mul_pos hΛ0 ht) (Real.sqrt_pos.mpr hδ0)
  have hc : 0 < ⌈Λ * t / Real.sqrt δ⌉₊ := Nat.ceil_pos.mpr ha
  exact lt_of_lt_of_le hc (le_max_left _ _)

/-- For nonnegative norm bounds and time and positive `δ`, the selected step count is at most
`theorem1QueryExpr + 1`. -/
theorem theorem1Steps_le_queryExpr {Λ Λmax t δ : ℝ} {D : ℕ}
    (hΛ0 : 0 ≤ Λ) (hΛmax0 : 0 ≤ Λmax) (ht : 0 ≤ t) (hδ0 : 0 < δ) :
    (theorem1Steps Λ Λmax t δ D : ℝ) ≤ theorem1QueryExpr Λ D Λmax t δ + 1 := by
  have ha : 0 ≤ Λ * t / Real.sqrt δ :=
    div_nonneg (mul_nonneg hΛ0 ht) (Real.sqrt_pos.mpr hδ0).le
  have hb : 0 ≤ Λmax * (D : ℝ) * t :=
    mul_nonneg (mul_nonneg hΛmax0 (Nat.cast_nonneg D)) ht
  have h1 : (⌈Λ * t / Real.sqrt δ⌉₊ : ℝ) < Λ * t / Real.sqrt δ + 1 :=
    Nat.ceil_lt_add_one ha
  have h2 : (⌈Λmax * (D : ℝ) * t⌉₊ : ℝ) < Λmax * (D : ℝ) * t + 1 :=
    Nat.ceil_lt_add_one hb
  have hmax : (theorem1Steps Λ Λmax t δ D : ℝ) =
      max (⌈Λ * t / Real.sqrt δ⌉₊ : ℝ) (⌈Λmax * (D : ℝ) * t⌉₊ : ℝ) := by
    unfold theorem1Steps
    rw [Nat.cast_max]
  rw [hmax, max_le_iff]
  unfold theorem1QueryExpr
  constructor <;> linarith

/-- The parameter `Λ1 * t / theorem1Steps Λ Λmax t δ D` associated with the selected integer
step count. See [Berry and Childs, Theorem 1][BerryChilds2012]. -/
def theorem1Eps (Λ1 Λ Λmax t δ : ℝ) (D : ℕ) : ℝ :=
  Λ1 * t / (theorem1Steps Λ Λmax t δ D : ℝ)

/-- The selected parameter `theorem1Eps` is positive when `Λ1`, `Λ`, `t`, and `δ` are positive. -/
theorem theorem1Eps_pos {Λ1 Λ Λmax t δ : ℝ} {D : ℕ}
    (hΛ1 : 0 < Λ1) (hΛ0 : 0 < Λ) (ht : 0 < t) (hδ0 : 0 < δ) :
    0 < theorem1Eps Λ1 Λ Λmax t δ D := by
  unfold theorem1Eps
  exact div_pos (mul_pos hΛ1 ht) (Nat.cast_pos.mpr (theorem1Steps_pos hΛ0 ht hδ0))

/-- Under the stated positive parameter hypotheses, `theorem1Eps ≤ Λ1 / (D * Λmax)`, the
parameter range used in Lemma 4. -/
theorem theorem1Eps_le_lemma4_range {Λ1 Λ Λmax t δ : ℝ} {D : ℕ}
    (hΛ1 : 0 < Λ1) (hΛ0 : 0 < Λ) (hΛmax0 : 0 < Λmax) (ht : 0 < t) (hδ0 : 0 < δ)
    (hD : 0 < D) :
    theorem1Eps Λ1 Λ Λmax t δ D ≤ Λ1 / ((D : ℝ) * Λmax) := by
  have hNpos : 0 < (theorem1Steps Λ Λmax t δ D : ℝ) :=
    Nat.cast_pos.mpr (theorem1Steps_pos hΛ0 ht hδ0)
  have hden : 0 < (D : ℝ) * Λmax := mul_pos (Nat.cast_pos.mpr hD) hΛmax0
  have hN := theorem1Steps_ge_second (Λ := Λ) (Λmax := Λmax) (t := t) (δ := δ) D
  unfold theorem1Eps
  rw [div_le_div_iff₀ hNpos hden]
  have hkey : t * (D : ℝ) * Λmax ≤ (theorem1Steps Λ Λmax t δ D : ℝ) := by
    nlinarith [hN]
  calc Λ1 * t * ((D : ℝ) * Λmax) = Λ1 * (t * (D : ℝ) * Λmax) := by ring
    _ ≤ Λ1 * (theorem1Steps Λ Λmax t δ D : ℝ) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt hΛ1)

/-- For positive `Λ`, `t`, and `δ` and nonzero `Λ1`, the selected parameter satisfies the scalar
walk error bound `Λ ^ 2 * theorem1Eps ^ 2 / Λ1 ^ 2 ≤ δ`. See [Berry and Childs, Theorem
1][BerryChilds2012]. -/
theorem theorem1_walk_error_le {Λ1 Λ Λmax t δ : ℝ} {D : ℕ}
    (hΛ0 : 0 < Λ) (ht : 0 < t) (hδ0 : 0 < δ) (hΛ1 : Λ1 ≠ 0) :
    Λ ^ 2 * (theorem1Eps Λ1 Λ Λmax t δ D) ^ 2 / Λ1 ^ 2 ≤ δ := by
  have hNpos : 0 < (theorem1Steps Λ Λmax t δ D : ℝ) :=
    Nat.cast_pos.mpr (theorem1Steps_pos hΛ0 ht hδ0)
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hN := theorem1Steps_ge_first (Λ := Λ) (Λmax := Λmax) (t := t) (δ := δ) D
  have hkey : Λ * t ≤ (theorem1Steps Λ Λmax t δ D : ℝ) * Real.sqrt δ := by
    rw [div_le_iff₀ hs] at hN
    linarith
  have hsq : (Λ * t) ^ 2 ≤ ((theorem1Steps Λ Λmax t δ D : ℝ) * Real.sqrt δ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hkey 2
  have hsq' : ((theorem1Steps Λ Λmax t δ D : ℝ) * Real.sqrt δ) ^ 2 =
      (theorem1Steps Λ Λmax t δ D : ℝ) ^ 2 * δ := by
    rw [mul_pow, Real.sq_sqrt hδ0.le]
  have hgoal : Λ ^ 2 * (theorem1Eps Λ1 Λ Λmax t δ D) ^ 2 / Λ1 ^ 2 =
      Λ ^ 2 * t ^ 2 / (theorem1Steps Λ Λmax t δ D : ℝ) ^ 2 := by
    unfold theorem1Eps
    field_simp [hNpos.ne', hΛ1]
  rw [hgoal, div_le_iff₀ (pow_pos hNpos 2)]
  nlinarith [hsq, hsq']

/-- If a circuit uses at most a nonnegative cost `c` queries, repeating it `theorem1Steps` times
uses at most `c * (theorem1QueryExpr + 1)` queries under the stated sign conditions. This
gives a query count estimate associated with Theorem 1 of [BerryChilds2012]. -/
theorem theorem1_repeat_query_budget {Λ Λmax t δ c : ℝ} {D : ℕ} (C : Circuit2 ι L)
    (hΛ0 : 0 ≤ Λ) (hΛmax0 : 0 ≤ Λmax) (ht : 0 ≤ t) (hδ0 : 0 < δ)
    (hc : 0 ≤ c) (hstep : (QueryCount2 C : ℝ) ≤ c) :
    (QueryCount2 (RepeatCircuit2 C (theorem1Steps Λ Λmax t δ D)) : ℝ) ≤
      c * (theorem1QueryExpr Λ D Λmax t δ + 1) := by
  rw [queryCount2_repeatCircuit]
  have hN := theorem1Steps_le_queryExpr (Λ := Λ) (Λmax := Λmax) (t := t) (δ := δ)
    (D := D) hΛ0 hΛmax0 ht hδ0
  have hcn : ((theorem1Steps Λ Λmax t δ D * QueryCount2 C : ℕ) : ℝ) =
      (theorem1Steps Λ Λmax t δ D : ℝ) * (QueryCount2 C : ℝ) := by push_cast; ring
  rw [hcn]
  have hq : 0 ≤ (QueryCount2 C : ℝ) := Nat.cast_nonneg _
  calc (theorem1Steps Λ Λmax t δ D : ℝ) * (QueryCount2 C : ℝ)
      ≤ (theorem1QueryExpr Λ D Λmax t δ + 1) * (QueryCount2 C : ℝ) :=
        mul_le_mul_of_nonneg_right hN hq
    _ ≤ (theorem1QueryExpr Λ D Λmax t δ + 1) * c := by
        exact mul_le_mul_of_nonneg_left hstep (by
          have := theorem1QueryExpr_pos (Λ := Λ) (Λmax := Λmax) (t := t) (δ := δ) (D := D)
            hΛ0 hΛmax0 hδ0 ht
          linarith)
    _ = c * (theorem1QueryExpr Λ D Λmax t δ + 1) := by ring

end Qatlib.Papers.BlackBoxHam09.MainResults.Sparse
