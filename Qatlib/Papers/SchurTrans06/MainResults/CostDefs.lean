/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Cost bounds and unitary cascades for the Schur transform

`sourceCGCost` models the sum of reduced Wigner and controlled-unitary synthesis costs across
Clebsch–Gordan levels. `sourceSchurCost` sums these costs across the Schur cascade with a
divided error budget; `IsPolyCost` and `IsNStageCascadePoly` state polynomial bounds in
`sourceScale`. The module also proves that `cascadeProd` preserves unitarity. See
[BaconChuangHarrow2005] for the mathematical setting.

## Main statements

* `sourceCGCost_poly`: bounds the Clebsch–Gordan cost by a polynomial in the source scale.
* `sourceSchurCost_le`: gives the explicit bound `n * (32 * sourceScale n d ε ^ 5)` for `0 < ε ≤
  1`.
* `cascade_unitary`: proves unitarity of a finite product of unitary stages.

## References

* [Bacon et al., 2005][BaconChuangHarrow2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SchurTrans06.MainResults

open scoped BigOperators
open Finset

/-- The scale `d + log (n + 1) + log (1 / ε) + 2` used in the transform cost bounds. -/
def sourceScale (n d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) + Real.log ((n : ℝ) + 1) + Real.log (1 / ε) + 2

/-- A cost function has a uniform polynomial upper bound in `sourceScale` for `0 < ε ≤ 1`. -/
def IsPolyCost (f : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ c : ℕ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ (n d : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 → f n d ε ≤ K * sourceScale n d ε ^ c

/-- A cost function is bounded by `n` times a uniform polynomial in `sourceScale` for `0 < ε ≤
1`. -/
def IsNStageCascadePoly (f : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ c : ℕ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ (n d : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      f n d ε ≤ (n : ℝ) * (K * sourceScale n d ε ^ c)

/-- The source scale is positive for `0 < ε ≤ 1`. -/
theorem sourceScale_pos {n d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < sourceScale n d ε := by
  have h1 : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hε).2 hε1
  have h3 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold sourceScale
  linarith

/-- The source scale is at least one for `0 < ε ≤ 1`. -/
theorem sourceScale_one_le {n d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ sourceScale n d ε := by
  have h1 : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hε).2 hε1
  have h3 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold sourceScale
  linarith

/-- The source scale is nonnegative for `0 < ε ≤ 1`. -/
theorem sourceScale_nonneg {n d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ sourceScale n d ε := (sourceScale_pos hε hε1).le

/-- The source scale is monotone in the dimension parameter. -/
theorem sourceScale_mono_d {n d₁ d₂ : ℕ} {ε : ℝ} (h : d₁ ≤ d₂) :
    sourceScale n d₁ ε ≤ sourceScale n d₂ ε := by
  unfold sourceScale
  have : (d₁ : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast h
  linarith

/-- The modeled classical reduced Wigner cost `d² * (d + log (n + 1) + 2)²`. -/
def reducedWignerClassicalCost (n d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 * ((d : ℝ) + Real.log ((n : ℝ) + 1) + 2) ^ 2

/-- The modeled controlled-unitary synthesis cost `(d + log (1 / ε) + 2)²`. -/
def controlledUnitarySynthesisCost (d : ℕ) (ε : ℝ) : ℝ :=
  ((d : ℝ) + Real.log (1 / ε) + 2) ^ 2

/-- The sum of the modeled classical reduced Wigner cost and controlled-unitary synthesis cost. -/
def tHatCost (n d : ℕ) (ε : ℝ) : ℝ :=
  reducedWignerClassicalCost n d + controlledUnitarySynthesisCost d ε

/-- The dimension recursion with zero costs at dimensions zero and one, adding one `tHatCost` at
each subsequent level. -/
private def cgCostRec : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | 1, _, _ => 0
  | d + 2, n, ε => cgCostRec (d + 1) n ε + tHatCost n (d + 2) ε

/-- The Clebsch–Gordan cost obtained from the dimension recursion `cgCostRec`. -/
def sourceCGCost (n d : ℕ) (ε : ℝ) : ℝ := cgCostRec d n ε

/-- The modeled Clebsch–Gordan cost at dimension zero is zero. -/
@[simp] theorem sourceCGCost_zero (n : ℕ) (ε : ℝ) : sourceCGCost n 0 ε = 0 := rfl

/-- The modeled Clebsch–Gordan cost at dimension one is zero. -/
@[simp] theorem sourceCGCost_one (n : ℕ) (ε : ℝ) : sourceCGCost n 1 ε = 0 := rfl

/-- Increasing the dimension from `d + 1` to `d + 2` adds `tHatCost n (d + 2) ε`. -/
theorem sourceCGCost_succ (n d : ℕ) (ε : ℝ) :
    sourceCGCost n (d + 2) ε = sourceCGCost n (d + 1) ε + tHatCost n (d + 2) ε :=
  rfl

/-- The sum of Clebsch–Gordan costs over `n - 1` cascade stages, each using error `ε / (n + 1)`. -/
def sourceSchurCost (n d : ℕ) (ε : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n - 1), sourceCGCost (k + 1) d (ε / ((n : ℝ) + 1))

/-- The real logarithm of `n + 1` is nonnegative for natural `n`. -/
theorem log_nat_succ_nonneg (n : ℕ) : 0 ≤ Real.log ((n : ℝ) + 1) := by
  apply Real.log_nonneg
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The real logarithm of `1 / ε` is nonnegative for `0 < ε ≤ 1`. -/
theorem log_inv_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ Real.log (1 / ε) := by
  apply Real.log_nonneg
  rw [one_div]
  exact (one_le_inv₀ hε).2 hε1

/-- For `0 < ε ≤ 1`, the dimension parameter is at most the source scale. -/
theorem le_sourceScale (n d : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (d : ℝ) ≤ sourceScale n d ε := by
  unfold sourceScale
  have h1 := log_nat_succ_nonneg n
  have h2 := log_inv_nonneg hε hε1
  linarith

/-- For `0 < ε ≤ 1`, one reduced-transform level costs at most twice the fourth power of the
source scale. See [Bacon et al., 2005, Result: poly(d, log n, log(1/ǫ)) Clebsch-Gordan
transform][BaconChuangHarrow2005]. -/
theorem tHatCost_le (n d : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    tHatCost n d ε ≤ 2 * sourceScale n d ε ^ 4 := by
  have hn := log_nat_succ_nonneg n
  have he := log_inv_nonneg hε hε1
  have hs1 : 1 ≤ sourceScale n d ε := sourceScale_one_le hε hε1
  have hs0 : 0 ≤ sourceScale n d ε := le_trans zero_le_one hs1
  have hA0 : 0 ≤ (d : ℝ) + Real.log ((n : ℝ) + 1) + 2 := by linarith
  have hB0 : 0 ≤ (d : ℝ) + Real.log (1 / ε) + 2 := by linarith
  have hdS : (d : ℝ) ≤ sourceScale n d ε := le_sourceScale n d hε hε1
  have hAS : (d : ℝ) + Real.log ((n : ℝ) + 1) + 2 ≤ sourceScale n d ε := by
    unfold sourceScale; linarith
  have hBS : (d : ℝ) + Real.log (1 / ε) + 2 ≤ sourceScale n d ε := by
    unfold sourceScale; linarith
  have hr : reducedWignerClassicalCost n d ≤ sourceScale n d ε ^ 4 := by
    unfold reducedWignerClassicalCost
    have h1 : (d : ℝ) ^ 2 ≤ sourceScale n d ε ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg d) hdS 2
    have h2 : ((d : ℝ) + Real.log ((n : ℝ) + 1) + 2) ^ 2 ≤ sourceScale n d ε ^ 2 :=
      pow_le_pow_left₀ hA0 hAS 2
    calc
      (d : ℝ) ^ 2 * ((d : ℝ) + Real.log ((n : ℝ) + 1) + 2) ^ 2
          ≤ sourceScale n d ε ^ 2 * sourceScale n d ε ^ 2 :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = sourceScale n d ε ^ 4 := by ring
  have hc : controlledUnitarySynthesisCost d ε ≤ sourceScale n d ε ^ 2 := by
    unfold controlledUnitarySynthesisCost
    exact pow_le_pow_left₀ hB0 hBS 2
  have h24 : sourceScale n d ε ^ 2 ≤ sourceScale n d ε ^ 4 := by
    have h1 : (1 : ℝ) ≤ sourceScale n d ε ^ 2 := by
      have h := mul_le_mul hs1 hs1 (by norm_num) hs0
      simpa [pow_two] using h
    calc
      sourceScale n d ε ^ 2 = sourceScale n d ε ^ 2 * 1 := by ring
      _ ≤ sourceScale n d ε ^ 2 * sourceScale n d ε ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = sourceScale n d ε ^ 4 := by ring
  unfold tHatCost
  linarith

/-- For `0 < ε ≤ 1`, one Clebsch–Gordan recursion step increases cost by at most twice the
fourth power of the new source scale. See [Bacon et al., 2005, Result: poly(d, log n,
log(1/ǫ)) Clebsch-Gordan transform][BaconChuangHarrow2005]. -/
theorem sourceCG_one_level_poly (n d : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    sourceCGCost n (d + 2) ε ≤
      sourceCGCost n (d + 1) ε + 2 * sourceScale n (d + 2) ε ^ 4 := by
  rw [sourceCGCost_succ]
  have ht := tHatCost_le n (d + 2) hε hε1
  linarith

/-- For `0 < ε ≤ 1`, the Clebsch–Gordan cost is at most `d * (2 * sourceScale n d ε ^ 4)`. See
[Bacon et al., 2005, Main result: n poly(d, log n, log(1/ǫ)) Schur transform
circuit][BaconChuangHarrow2005]. -/
theorem sourceCGCost_le (n d : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    sourceCGCost n d ε ≤ (d : ℝ) * (2 * sourceScale n d ε ^ 4) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | k
    · rw [sourceCGCost_zero]
      simp only [Nat.cast_zero, zero_mul]
      exact le_refl 0
    · rw [sourceCGCost_one]
      have hs1 : (1 : ℝ) ≤ sourceScale n (0 + 1) ε :=
        sourceScale_one_le (n := n) (d := 0 + 1) (ε := ε) hε hε1
      have hs0 : 0 ≤ sourceScale n (0 + 1) ε ^ 4 :=
        pow_nonneg (le_trans zero_le_one hs1) 4
      have h2 : (0 : ℝ) ≤ 2 * sourceScale n (0 + 1) ε ^ 4 := by linarith
      have h1 : (0 : ℝ) ≤ ((0 + 1 : ℕ) : ℝ) := by positivity
      exact mul_nonneg h1 h2
    · rw [sourceCGCost_succ]
      have ihk :
          sourceCGCost n (k + 1) ε ≤
            ((k + 1 : ℕ) : ℝ) * (2 * sourceScale n (k + 1) ε ^ 4) :=
        ih (k + 1) (by omega)
      have hmono : sourceScale n (k + 1) ε ≤ sourceScale n (k + 2) ε :=
        sourceScale_mono_d (by omega)
      have hsk0 : 0 ≤ sourceScale n (k + 1) ε :=
        le_trans zero_le_one (sourceScale_one_le (n := n) (d := k + 1) (ε := ε) hε hε1)
      have hpow : sourceScale n (k + 1) ε ^ 4 ≤ sourceScale n (k + 2) ε ^ 4 :=
        pow_le_pow_left₀ hsk0 hmono 4
      have hih2 :
          sourceCGCost n (k + 1) ε ≤
            ((k : ℝ) + 1) * (2 * sourceScale n (k + 2) ε ^ 4) := by
        refine le_trans ihk ?_
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)
      have ht := tHatCost_le n (k + 2) hε hε1
      have hgoal := add_le_add hih2 ht
      calc
        sourceCGCost n (k + 1) ε + tHatCost n (k + 2) ε
            ≤ ((k : ℝ) + 1) * (2 * sourceScale n (k + 2) ε ^ 4) +
                2 * sourceScale n (k + 2) ε ^ 4 := hgoal
        _ = ((k + 2 : ℕ) : ℝ) * (2 * sourceScale n (k + 2) ε ^ 4) := by
              push_cast; ring

/-- The modeled Clebsch–Gordan cost has a polynomial bound in the source scale. See [Bacon et
al., 2005, Result: poly(d, log n, log(1/ǫ)) Clebsch-Gordan
transform][BaconChuangHarrow2005]. -/
theorem sourceCGCost_poly : IsPolyCost sourceCGCost := by
  refine ⟨5, 2, by norm_num, fun n d ε hε hε1 => ?_⟩
  have h := sourceCGCost_le n d hε hε1
  have hs1 : 1 ≤ sourceScale n d ε := sourceScale_one_le hε hε1
  have hs0 : 0 ≤ sourceScale n d ε := le_trans zero_le_one hs1
  have hdS : (d : ℝ) ≤ sourceScale n d ε := le_sourceScale n d hε hε1
  refine le_trans h ?_
  calc
    (d : ℝ) * (2 * sourceScale n d ε ^ 4)
        = 2 * ((d : ℝ) * sourceScale n d ε ^ 4) := by ring
    _ ≤ 2 * (sourceScale n d ε * sourceScale n d ε ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hdS (pow_nonneg hs0 4)
    _ = 2 * sourceScale n d ε ^ 5 := by ring

/-- At each indicated cascade stage, the scale with divided error is at most twice the overall
source scale for `0 < ε ≤ 1`. See [Bacon et al., 2005, Main result: n poly(d, log n,
log(1/ǫ)) Schur transform circuit][BaconChuangHarrow2005]. -/
theorem sourceSchurStageScale_le (n d k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hk : k + 1 < n) :
    sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) ≤ 2 * sourceScale n d ε := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlogk : Real.log (((k + 1 : ℕ) : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := by
    have hx : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    have hxy : ((k + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have hk2 : k + 2 ≤ n + 1 := by omega
      have heq : ((k + 1 : ℕ) : ℝ) + 1 = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [heq]
      exact_mod_cast hk2
    exact Real.log_le_log hx hxy
  have hlogdiv :
      Real.log (1 / (ε / ((n : ℝ) + 1))) =
        Real.log ((n : ℝ) + 1) + Real.log (1 / ε) := by
    have h1 : (1 : ℝ) / (ε / ((n : ℝ) + 1)) = ((n : ℝ) + 1) * (1 / ε) := by
      field_simp
    rw [h1, Real.log_mul (ne_of_gt hn1) (ne_of_gt (div_pos (by norm_num) hε))]
  have hn := log_nat_succ_nonneg n
  have he := log_inv_nonneg hε hε1
  unfold sourceScale
  rw [hlogdiv]
  linarith

/-- The modeled Schur cascade cost is bounded by `n` times a polynomial in the source scale. See
[Bacon et al., 2005, Main result: n poly(d, log n, log(1/ǫ)) Schur transform
circuit][BaconChuangHarrow2005]. -/
theorem sourceSchurCost_poly : IsNStageCascadePoly sourceSchurCost := by
  refine ⟨5, 32, by norm_num, fun n d ε hε hε1 => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hε' : 0 < ε / ((n : ℝ) + 1) := div_pos hε hn1
  have hε'1 : ε / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn1]
    have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    linarith
  have hs1 : 1 ≤ sourceScale n d ε := sourceScale_one_le hε hε1
  have hs0 : 0 ≤ sourceScale n d ε := le_trans zero_le_one hs1
  have hterm : ∀ k ∈ Finset.range (n - 1),
      sourceCGCost (k + 1) d (ε / ((n : ℝ) + 1)) ≤ 32 * sourceScale n d ε ^ 5 := by
    intro k hk
    have hklt : k + 1 < n := by
      have := Finset.mem_range.1 hk
      omega
    have hcg := sourceCGCost_le (k + 1) d hε' hε'1
    have hsc := sourceSchurStageScale_le n d k hε hε1 hklt
    have hsk0 : 0 ≤ sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) :=
      le_trans zero_le_one (sourceScale_one_le hε' hε'1)
    have hpow : sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) ^ 4 ≤
        (2 * sourceScale n d ε) ^ 4 :=
      pow_le_pow_left₀ hsk0 hsc 4
    have hmid : (d : ℝ) * (2 * sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) ^ 4) ≤
        sourceScale n d ε * (2 * (2 * sourceScale n d ε) ^ 4) := by
      refine mul_le_mul (le_sourceScale n d hε hε1) ?_ ?_ hs0
      · exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      · have h4 : 0 ≤ sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) ^ 4 :=
          pow_nonneg hsk0 4
        linarith
    refine le_trans hcg (le_trans hmid (le_of_eq ?_))
    ring
  unfold sourceSchurCost
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range (n - 1)).card : ℝ) ≤ (n : ℝ) := by
    rw [Finset.card_range]
    exact_mod_cast Nat.sub_le n 1
  have hc0 : 0 ≤ 32 * sourceScale n d ε ^ 5 := by
    have := pow_nonneg hs0 5
    linarith
  exact mul_le_mul_of_nonneg_right hcard hc0

/-- A square complex matrix multiplied on the right by its adjoint equals the identity. -/
def IsUnitary {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Prop :=
  M * star M = 1

/-- The identity matrix satisfies `IsUnitary`. -/
theorem isUnitary_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsUnitary (1 : Matrix ι ι ℂ) := by
  simp [IsUnitary]

/-- The product of two matrices satisfying `IsUnitary` also satisfies `IsUnitary`. -/
theorem IsUnitary.mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : IsUnitary A) (hB : IsUnitary B) :
    IsUnitary (A * B) := by
  unfold IsUnitary at *
  have h : A * B * star (A * B) = A * (B * star B) * star A := by
    rw [star_mul]
    noncomm_ring
  rw [h, hB, mul_one, hA]

/-- The ordered product of a finite family of square matrices, with the last stage multiplied on
the right. -/
def cascadeProd {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (m : ℕ) → (Fin m → Matrix ι ι ℂ) → Matrix ι ι ℂ
  | 0, _ => 1
  | m + 1, f => cascadeProd m (fun i => f i.castSucc) * f (Fin.last m)

/-- A cascade of unitary stages is unitary. See [Bacon et al., 2005, Result: poly(d, log n,
log(1/ǫ)) Clebsch-Gordan transform][BaconChuangHarrow2005]. -/
theorem cascade_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (m : ℕ) (stages : Fin m → Matrix ι ι ℂ), (∀ i, IsUnitary (stages i)) →
      IsUnitary (cascadeProd m stages) := by
  intro m
  induction m with
  | zero => intro stages _; simp [cascadeProd, IsUnitary]
  | succ m ih =>
      intro stages h
      simp only [cascadeProd]
      exact (ih (fun i => stages i.castSucc) (fun i => h i.castSucc)).mul
        (h (Fin.last m))

/-- The recursive Clebsch–Gordan cost equals the sum of `tHatCost` over dimensions two through
`d`. See [Bacon et al., 2005, Result: poly(d, log n, log(1/ǫ)) Clebsch-Gordan
transform][BaconChuangHarrow2005]. -/
theorem sourceCGCost_eq_sum (n d : ℕ) (ε : ℝ) :
    sourceCGCost n d ε = ∑ i ∈ Finset.range (d - 1), tHatCost n (i + 2) ε := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | k
    · simp [sourceCGCost, cgCostRec]
    · simp [sourceCGCost, cgCostRec]
    · rw [sourceCGCost_succ]
      rw [ih (k + 1) (by omega)]
      have hk1 : (k + 1 - 1) = k := by omega
      have hk2 : (k + 2 - 1) = k + 1 := by omega
      rw [hk1, hk2, Finset.sum_range_succ]

/-- For `0 < ε ≤ 1`, the modeled Schur cost is at most `n * (32 * sourceScale n d ε ^ 5)`. See
[Bacon et al., 2005, Main result: n poly(d, log n, log(1/ǫ)) Schur transform
circuit][BaconChuangHarrow2005]. -/
theorem sourceSchurCost_le (n d : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    sourceSchurCost n d ε ≤ (n : ℝ) * (32 * sourceScale n d ε ^ 5) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hε' : 0 < ε / ((n : ℝ) + 1) := div_pos hε hn1
  have hε'1 : ε / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn1]
    have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    linarith
  have hs1 : 1 ≤ sourceScale n d ε := sourceScale_one_le hε hε1
  have hs0 : 0 ≤ sourceScale n d ε := le_trans zero_le_one hs1
  have hterm : ∀ k ∈ Finset.range (n - 1),
      sourceCGCost (k + 1) d (ε / ((n : ℝ) + 1)) ≤ 32 * sourceScale n d ε ^ 5 := by
    intro k hk
    have hklt : k + 1 < n := by
      have := Finset.mem_range.1 hk
      omega
    have hcg := sourceCGCost_le (k + 1) d hε' hε'1
    have hsc := sourceSchurStageScale_le n d k hε hε1 hklt
    have hsk0 : 0 ≤ sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) :=
      le_trans zero_le_one (sourceScale_one_le hε' hε'1)
    have hpow : sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) ^ 4 ≤
        (2 * sourceScale n d ε) ^ 4 :=
      pow_le_pow_left₀ hsk0 hsc 4
    have hmid : (d : ℝ) * (2 * sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) ^ 4) ≤
        sourceScale n d ε * (2 * (2 * sourceScale n d ε) ^ 4) := by
      refine mul_le_mul (le_sourceScale n d hε hε1) ?_ ?_ hs0
      · exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      · have h4 : 0 ≤ sourceScale (k + 1) d (ε / ((n : ℝ) + 1)) ^ 4 :=
          pow_nonneg hsk0 4
        linarith
    refine le_trans hcg (le_trans hmid (le_of_eq ?_))
    ring
  unfold sourceSchurCost
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range (n - 1)).card : ℝ) ≤ (n : ℝ) := by
    rw [Finset.card_range]
    exact_mod_cast Nat.sub_le n 1
  have hc0 : 0 ≤ 32 * sourceScale n d ε ^ 5 := by
    have := pow_nonneg hs0 5
    linarith
  exact mul_le_mul_of_nonneg_right hcard hc0

end Qatlib.Papers.SchurTrans06.MainResults
