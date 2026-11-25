/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterError19.GroupedError.TrotterCommutatorScalingSteps
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrderConsumers

@[expose] public section

/-!
# Explicit step selection in the norm-sum analysis

Corollary 7 of arXiv:1912.08854v3 uses the norms of the generators to choose
the segment count. Supply an integer choice with the `|t|^(p+1)` factor,
interpret the resulting list of exponentials, and verify its norm error.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Papers.TrotterError19.GroupedError

namespace Qatlib.Papers.TrotterError19.MainResults

/-- Corollary 7 with an explicit sufficient integer step count in the norm-sum model.
The emitted product is unitary, reaches the requested accuracy, and charges its exact length. -/
theorem corollary7_norm_sum_selected_steps {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hxs : ∀ X ∈ xs, Xᴴ = -X) (hH : Hᴴ = -H)
    (hc : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n)
    (t ε : ℝ) (hε : 0 < ε) :
    let L := suzukiMass xs + ‖H‖
    let α := 2 * Real.exp (L * |t|) * L ^ (p + 1)
    let r := max 1 (Nat.ceil ((α * |t| ^ (p + 1) / (((p + 1).factorial : ℝ) * ε)) ^
      ((1 : ℝ) / p)))
    let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten
    0 < r ∧ w.prod ∈ Matrix.unitaryGroup I ℂ ∧ w.length = r * xs.length ∧
      ‖w.prod - NormedSpace.exp (t • H)‖ ≤ ε := by
  let L := suzukiMass xs + ‖H‖
  let α := 2 * Real.exp (L * |t|) * L ^ (p + 1)
  let r := max 1 (Nat.ceil ((α * |t| ^ (p + 1) / (((p + 1).factorial : ℝ) * ε)) ^
    ((1 : ℝ) / p)))
  have hL : 0 ≤ L := add_nonneg (general_trotter_mass_nonneg xs) (norm_nonneg H)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hb := trotter_selected_scalar_budget α t ε p hα hε hp
  have hr : 0 < r := hb.1
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hf : (0 : ℝ) < (p + 1).factorial := by exact_mod_cast Nat.factorial_pos (p + 1)
  let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten
  change 0 < r ∧ w.prod ∈ Matrix.unitaryGroup I ℂ ∧ w.length = r * xs.length ∧
    ‖w.prod - NormedSpace.exp (t • H)‖ ≤ ε
  obtain ⟨hu, hw, he⟩ := general_order_actual_word_error_and_cost I xs H p r t hxs hH hr hc
  have ht : |t / (r : ℝ)| = |t| / (r : ℝ) := by
    rw [abs_div, abs_of_nonneg hrR.le]
  have hexp : Real.exp (L * |t / (r : ℝ)|) ≤ Real.exp (L * |t|) := by
    rw [ht]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (div_le_self (abs_nonneg _) hr1) hL)
  refine ⟨hr, hu, hw, he.trans ?_⟩
  calc
    2 * (r : ℝ) * Real.exp (L * |t / (r : ℝ)|) * (L * |t / (r : ℝ)|) ^ (p + 1) /
          ((p + 1).factorial : ℝ)
      ≤ 2 * (r : ℝ) * Real.exp (L * |t|) * (L * |t / (r : ℝ)|) ^ (p + 1) /
          ((p + 1).factorial : ℝ) := by
        apply div_le_div_of_nonneg_right _ hf.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
    _ = α * |t| ^ (p + 1) / (((p + 1).factorial : ℝ) * (r : ℝ) ^ p) := by
      rw [ht, mul_pow, div_pow, pow_succ (r : ℝ) p]
      dsimp [α]
      field_simp [hrR.ne', hf.ne']
    _ ≤ ε := hb.2

end Qatlib.Papers.TrotterError19.MainResults
