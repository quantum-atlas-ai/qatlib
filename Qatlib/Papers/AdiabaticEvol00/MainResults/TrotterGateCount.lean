/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Mathlib.Algebra.Order.Floor.Semiring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.TrotterGateCount

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

theorem trotter_product_formula_error {D m r : ℕ} (H : Fin m → Operator D) (t : ℝ)
    (hr : 0 < r) (hH : ∀ j, (H j).IsHermitian) :
    ‖pfFamily H t r - HamiltonianEvolution (∑ j, H j) t‖ ≤
      t ^ 2 / (2 * r) * pfCommutatorSum H :=
  product_formula_finite_family_segmented D m r H t hr hH

theorem trotter_error_le_of_steps {D m r : ℕ} (H : Fin m → Operator D) (t ε : ℝ)
    (hr : 0 < r) (hH : ∀ j, (H j).IsHermitian)
    (hstep : t ^ 2 / (2 * r) * pfCommutatorSum H ≤ ε) :
    ‖pfFamily H t r - HamiltonianEvolution (∑ j, H j) t‖ ≤ ε :=
  le_trans (trotter_product_formula_error H t hr hH) hstep

def trotterFactorCount (T k : ℝ) (m : ℕ) : ℝ := k * T ^ 2 * (m : ℝ)

theorem trotter_required_factors {T C ε : ℝ} {m r : ℕ} (hm : 0 < (m : ℝ))
    (hr : T ^ 2 * C / (2 * ε) ≤ (r : ℝ)) :
    T ^ 2 * C / (2 * ε) * (m : ℝ) ≤ (r : ℝ) * (m : ℝ) :=
  mul_le_mul_of_nonneg_right hr (le_of_lt hm)

theorem trotter_gate_count {T C ε : ℝ} {m : ℕ} (hm : 0 < (m : ℝ)) (hC : 0 ≤ C)
    (hε : 0 < ε) :
    ∃ r : ℕ, T ^ 2 * C / (2 * ε) ≤ (r : ℝ) ∧
      (r : ℝ) * (m : ℝ) ≤ (T ^ 2 * C / (2 * ε) + 1) * (m : ℝ) := by
  have hxnonneg : 0 ≤ T ^ 2 * C / (2 * ε) := by positivity
  refine ⟨⌈T ^ 2 * C / (2 * ε)⌉₊, Nat.le_ceil _, ?_⟩
  have h1 : ((⌈T ^ 2 * C / (2 * ε)⌉₊ : ℕ) : ℝ) ≤ T ^ 2 * C / (2 * ε) + 1 := by
    have := Nat.ceil_lt_add_one hxnonneg
    linarith
  exact mul_le_mul_of_nonneg_right h1 (le_of_lt hm)

theorem trotter_count_square (n : ℝ) (k C : ℝ) (hn : 0 ≤ n) :
    trotterFactorCount (n ^ k) C 1 = C * n ^ (2 * k) := by
  unfold trotterFactorCount
  have hsq : (n ^ k) ^ 2 = n ^ (2 * k) := by
    rw [← Real.rpow_natCast (n ^ k) 2]
    rw [← Real.rpow_mul hn k ((2 : ℕ) : ℝ)]
    congr 1
    ring
  rw [hsq]
  norm_num

end Qatlib.Papers.AdiabaticEvol00.MainResults.TrotterGateCount
