/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs

/-!
# Lemma 6 amplification parameter arithmetic

This module defines the planar rotation `groverStep` and proves its exact iteration formula in
`grover_iterate`. The ceiling choice `lemma6Iters` and the scale `lemma6X` satisfy the scalar
bounds collected by `lemma6_amplitude_amplified_state_prep`, including a bound on the associated
query count expression.

The rotation and parameter estimates support the amplitude amplification analysis of Lemma 6 in
[BerryChilds2012].

## Main statements

* `grover_iterate` gives the exact planar iteration formula.
* `lemma6_amplitude_amplified_state_prep` collects the scalar amplification estimates.

## References

* [Berry and Childs, 2012][BerryChilds2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

/-- The planar rotation that sends `(sin α, cos α)` to `(sin (α + 2 * θ), cos (α + 2 * θ))`. -/
def groverStep (θ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1 * Real.cos (2 * θ) + v.2 * Real.sin (2 * θ),
   -v.1 * Real.sin (2 * θ) + v.2 * Real.cos (2 * θ))

/-- One application of `groverStep θ` advances the angle `(2 * r + 1) * θ` to `(2 * (r + 1) + 1)
* θ`. -/
theorem groverStep_sin_cos (θ : ℝ) (r : ℕ) :
    groverStep θ (Real.sin (((2 * r + 1 : ℕ) : ℝ) * θ),
        Real.cos (((2 * r + 1 : ℕ) : ℝ) * θ)) =
      (Real.sin (((2 * (r + 1) + 1 : ℕ) : ℝ) * θ),
        Real.cos (((2 * (r + 1) + 1 : ℕ) : ℝ) * θ)) := by
  have h2 : (((2 * (r + 1) + 1 : ℕ) : ℝ) * θ) =
      (((2 * r + 1 : ℕ) : ℝ) * θ) + 2 * θ := by
    push_cast
    ring
  simp only [groverStep, h2, Real.sin_add, Real.cos_add]
  exact Prod.ext (by ring) (by ring)

/-- After `r` applications of `groverStep θ`, the initial pair `(sin θ, cos θ)` has angle `(2 *
r + 1) * θ`. See [Berry and Childs, Lemma 6][BerryChilds2012]. -/
theorem grover_iterate (θ : ℝ) (r : ℕ) :
    (groverStep θ)^[r] (Real.sin θ, Real.cos θ) =
      (Real.sin (((2 * r + 1 : ℕ) : ℝ) * θ),
        Real.cos (((2 * r + 1 : ℕ) : ℝ) * θ)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      exact groverStep_sin_cos θ r

/-- The squared coordinates of the iterated sine and cosine pair sum to one. -/
theorem grover_iterate_normalized (θ : ℝ) (r : ℕ) :
    ((groverStep θ)^[r] (Real.sin θ, Real.cos θ)).1 ^ 2 +
      ((groverStep θ)^[r] (Real.sin θ, Real.cos θ)).2 ^ 2 = 1 := by
  rw [grover_iterate, Real.sin_sq_add_cos_sq]

/-- The natural ceiling of half the square root amplification parameter minus one half, used as
the iteration count in Lemma 6. -/
def lemma6Iters (Λ1 ε : ℝ) (D : ℕ) (Λmax : ℝ) : ℕ :=
  ⌈(1 / 2) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) - 1 / 2⌉₊

/-- The odd multiplier `2 * lemma6Iters + 1` is at least `sqrt (ε * Λmax * D / Λ1)`. See [Berry
and Childs, Lemma 6][BerryChilds2012]. -/
theorem lemma6Iters_ge (Λ1 ε Λmax : ℝ) (D : ℕ) :
    Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) ≤ 2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1 := by
  have h := Nat.le_ceil ((1 / 2) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) - 1 / 2)
  unfold lemma6Iters
  linarith

/-- The odd multiplier `2 * lemma6Iters + 1` is at most `sqrt (ε * Λmax * D / Λ1) + 2`. See
[Berry and Childs, Lemma 6][BerryChilds2012]. -/
theorem lemma6Iters_le (Λ1 ε Λmax : ℝ) (D : ℕ) :
    (2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1) ≤
      Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) + 2 := by
  unfold lemma6Iters
  by_cases hx : (1 / 2) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) - 1 / 2 ≤ 0
  · have h0 : ⌈(1 / 2) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) - 1 / 2⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr hx
    rw [h0]
    have hsq : 0 ≤ Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) := Real.sqrt_nonneg _
    linarith
  · have hx0 : 0 < (1 / 2) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) - 1 / 2 :=
      lt_of_not_ge hx
    have h := Nat.ceil_lt_add_one (le_of_lt hx0)
    linarith

/-- The scale `(2 * r + 1) ^ 2 * Λ1 / (ε * D)` associated with `r` planar amplification
iterations. -/
def lemma6X (Λ1 ε : ℝ) (D : ℕ) (r : ℕ) : ℝ :=
  (2 * (r : ℝ) + 1) ^ 2 * Λ1 / (ε * (D : ℝ))

/-- For positive `D`, `Λ1`, and `ε` and nonnegative `Λmax`, the scale selected using
`lemma6Iters` is at least `Λmax`. See [Berry and Childs, Lemma 6][BerryChilds2012]. -/
theorem lemma6X_ge_max {Λ1 Λmax ε : ℝ} {D : ℕ} (hD : 0 < D) (hΛ1 : 0 < Λ1) (hε0 : 0 < ε)
    (hmax : 0 ≤ Λmax) :
    Λmax ≤ lemma6X Λ1 ε D (lemma6Iters Λ1 ε D Λmax) := by
  have hden : 0 < ε * (D : ℝ) := mul_pos hε0 (Nat.cast_pos.mpr hD)
  have hx0 : 0 ≤ ε * Λmax * (D : ℝ) / Λ1 := by positivity
  have hsq : ε * Λmax * (D : ℝ) / Λ1 =
      (Real.sqrt (ε * Λmax * (D : ℝ) / Λ1)) ^ 2 := by
    rw [Real.sq_sqrt hx0]
  have hle := lemma6Iters_ge Λ1 ε Λmax D
  have hp : (Real.sqrt (ε * Λmax * (D : ℝ) / Λ1)) ^ 2 ≤
      (2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  have hkey : Λmax ≤ (2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1) ^ 2 * Λ1 / (ε * (D : ℝ)) := by
    rw [le_div_iff₀ hden]
    have h1 : Λmax * (ε * (D : ℝ)) = ε * Λmax * (D : ℝ) / Λ1 * Λ1 := by
      field_simp
    rw [h1]
    calc ε * Λmax * (D : ℝ) / Λ1 * Λ1
        = (Real.sqrt (ε * Λmax * (D : ℝ) / Λ1)) ^ 2 * Λ1 := by
          rw [hsq.symm]
      _ ≤ (2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1) ^ 2 * Λ1 := by
          exact mul_le_mul_of_nonneg_right hp (le_of_lt hΛ1)
  exact hkey

/-- Multiplying the selected odd iteration multiplier by a nonnegative cost `c` gives at most `c
* (lemma6QueryExpr + 1)`. -/
theorem lemma6_query_count {Λ1 ε Λmax c : ℝ} {D : ℕ} (hc : 0 ≤ c) :
    c * (2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1) ≤
      c * (lemma6QueryExpr Λ1 ε D Λmax + 1) := by
  unfold lemma6QueryExpr
  have h := lemma6Iters_le Λ1 ε Λmax D
  nlinarith [h, hc]

/-- Under the stated sparsity, norm, and positivity hypotheses, collect the selected iteration
lower bound, the scale bound, the exact planar rotation formula, and the scalar query budget
inequality for Lemma 6 of [BerryChilds2012]. -/
theorem lemma6_amplitude_amplified_state_prep
    (BB : BlackBox ι D L) {Λ1 Λmax ε : ℝ}
    (hsp : IsColumnSparse BB.H D) (hD : 0 < D)
    (hΛ1 : colSumNorm BB.H ≤ Λ1) (hΛmax : maxEntryNorm BB.H ≤ Λmax)
    (hΛ1pos : 0 < Λ1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmax0 : 0 ≤ Λmax) (c : ℝ) (hc : 0 ≤ c) :
    Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) ≤
        2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1 ∧
      Λmax ≤ lemma6X Λ1 ε D (lemma6Iters Λ1 ε D Λmax) ∧
      (∀ θ : ℝ, (groverStep θ)^[lemma6Iters Λ1 ε D Λmax]
          (Real.sin θ, Real.cos θ) =
        (Real.sin (((2 * lemma6Iters Λ1 ε D Λmax + 1 : ℕ) : ℝ) * θ),
          Real.cos (((2 * lemma6Iters Λ1 ε D Λmax + 1 : ℕ) : ℝ) * θ))) ∧
      c * (2 * (lemma6Iters Λ1 ε D Λmax : ℝ) + 1) ≤
        c * (lemma6QueryExpr Λ1 ε D Λmax + 1) := by
  refine ⟨lemma6Iters_ge Λ1 ε Λmax D, lemma6X_ge_max hD hΛ1pos hε0 hmax0,
    fun θ => grover_iterate θ _, lemma6_query_count (D := D) hc⟩

end Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse
