/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Theorem 3 simulation charging and cost shape

Fixed source arXiv:1010.4458v2, Theorem 3: if the evolution of the Hamiltonian
`H` for time `T` is simulated in time `C * min T 1`, then a state `psi'` with
`‖psi - psi'|| ≤ ε` can be generated in time
`O(C * κ * log^3 (κ/ε) / ε^3 * log^2 (1/ε))`.

This module proves the exact scalar charging and composition laws behind that
displayed bound: the `min T 1` charging of a sliced simulation schedule, the
cost shape as an explicit function, its monotonicity in `κ`, and the total
charged time of a finite schedule whose amplification/estimation repetition
count obeys the displayed polylogarithmic budget. No Hamiltonian-simulation
algorithm, VTAA schedule or output-state accuracy is modeled here; those
remain unformalized parts of the source theorem.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.Thm3Cost

/-- The source simulation charge: evolving for time `T` costs `C * min T 1`. -/
def simCharge (C T : ℝ) : ℝ := C * min T 1

/-- Slicing a simulation of time `T` into `r > 0` equal pieces and charging
each piece by `simCharge` costs exactly `C * min T r`; in particular slicing
never costs more than one whole-block charge per piece count. -/
theorem simSlice (C T r : ℝ) (hr : 0 < r) :
    r * simCharge C (T / r) = C * min T r := by
  unfold simCharge
  rcases le_or_gt (T / r) 1 with h | h
  · have hTr : T ≤ r := (div_le_one hr).mp h
    rw [min_eq_left h, min_eq_left hTr]
    field_simp
  · have hTr : r < T := (one_lt_div hr).mp h
    rw [min_eq_right (le_of_lt h), min_eq_right (le_of_lt hTr)]
    ring

/-- The Theorem 3 cost shape `C * κ * log^3 (κ/ε) / ε^3 * log^2 (1/ε)`. -/
def thm3Cost (C κ ε : ℝ) : ℝ :=
  C * κ * (Real.log (κ / ε) ^ 3 / ε ^ 3) * Real.log (1 / ε) ^ 2

/-- The cost shape is nonnegative for `0 ≤ C`, `1 ≤ κ` and `0 < ε ≤ 1`. -/
theorem thm3CostNonneg (C κ ε : ℝ) (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : 0 ≤ thm3Cost C κ ε := by
  have hκe : 1 ≤ κ / ε := by rw [le_div_iff₀ hε]; linarith
  have h1 : 0 ≤ Real.log (κ / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have h2 : 0 ≤ Real.log (1 / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  unfold thm3Cost
  positivity

/-- The cost shape is monotone in the condition number: for `0 ≤ C`,
`1 ≤ κ₁ ≤ κ₂` and `0 < ε ≤ 1`, `thm3Cost C κ₁ ε ≤ thm3Cost C κ₂ ε`. -/
theorem thm3MonoK (C κ₁ κ₂ ε : ℝ) (hC : 0 ≤ C) (hκ : 1 ≤ κ₁) (hκ' : κ₁ ≤ κ₂)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    thm3Cost C κ₁ ε ≤ thm3Cost C κ₂ ε := by
  have hlog₁ : 0 ≤ Real.log (κ₁ / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  have hlog₂ : 0 ≤ Real.log (κ₂ / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  have hlogε : 0 ≤ Real.log (1 / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  have hε3 : 0 < ε ^ 3 := by positivity
  have hlogle : Real.log (κ₁ / ε) ≤ Real.log (κ₂ / ε) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff_of_pos_right hε]
    linarith
  have h3 : Real.log (κ₁ / ε) ^ 3 ≤ Real.log (κ₂ / ε) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hlogle 3
  have hd3 : Real.log (κ₁ / ε) ^ 3 / ε ^ 3 ≤ Real.log (κ₂ / ε) ^ 3 / ε ^ 3 :=
    (div_le_div_iff_of_pos_right hε3).mpr h3
  have hA1 : 0 ≤ Real.log (κ₁ / ε) ^ 3 / ε ^ 3 :=
    div_nonneg (pow_nonneg hlog₁ 3) (le_of_lt hε3)
  have hCκ₂ : 0 ≤ C * κ₂ := mul_nonneg hC (by linarith)
  unfold thm3Cost
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlogε 2)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hκ' hC) hd3 hA1 hCκ₂

/-- Cast helper: summing a real constant over `Fin n` is `n * C`. -/
private theorem sumConstCast (C : ℝ) (n : ℕ) :
    ∑ _j : Fin n, C = (n : ℝ) * C := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, ih, Nat.cast_succ]
      ring

/-- Composition law of Theorem 3: a finite schedule of `n` simulation runs,
each of duration at most `κ` and each charged by `simCharge C`, has total
charged time at most `thm3Cost C κ ε` whenever the repetition count `n` obeys
the displayed polylogarithmic budget `log^3 (κ/ε) * log^2 (1/ε) / ε^3`. -/
theorem thm3Total (C κ ε : ℝ) (n : ℕ) (T t : Fin n → ℝ)
    (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsim : ∀ j, t j ≤ simCharge C (T j))
    (hn : (n : ℝ) ≤ Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3) :
    ∑ j, t j ≤ thm3Cost C κ ε := by
  have hlogk : 0 ≤ Real.log (κ / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  have hlogε : 0 ≤ Real.log (1 / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  have hsum : ∑ j, t j ≤ (n : ℝ) * C := by
    calc ∑ j, t j ≤ ∑ _j : Fin n, C :=
          Finset.sum_le_sum fun j _ =>
            le_trans (hsim j)
              (le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
                (by norm_num))
      _ = (n : ℝ) * C := sumConstCast C n
  have hX : 0 ≤ Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3 := by
    positivity
  have hstep2 : (n : ℝ) * C ≤ C * (Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3) :=
    le_trans (mul_le_mul_of_nonneg_right hn hC) (le_of_eq (by ring))
  have hstep3 : C * (Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3)
      ≤ thm3Cost C κ ε := by
    have hκX : Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3
        ≤ κ * (Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3) :=
      le_mul_of_one_le_left hX hκ
    calc C * (Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3)
        ≤ C * (κ * (Real.log (κ / ε) ^ 3 * Real.log (1 / ε) ^ 2 / ε ^ 3)) :=
          mul_le_mul_of_nonneg_left hκX hC
      _ = thm3Cost C κ ε := by
          unfold thm3Cost
          field_simp
  exact le_trans hsum (le_trans hstep2 hstep3)

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.Thm3Cost
