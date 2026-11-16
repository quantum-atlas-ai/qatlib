/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PolynomialToolkit
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

@[expose] public section


set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Polynomial

namespace Qatlib.Papers.SpectralAmp17.MainResults.Chebyshev

open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

/-- The paper's natural-index recurrence agrees with Mathlib's first-kind Chebyshev family. -/
theorem chebT_eq_mathlib (j : ℕ) :
    chebT j = Polynomial.Chebyshev.T ℝ (j : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · simp [chebT]
    rcases j with _ | j
    · simp [chebT]
    have h0 := ih j (by omega)
    have h1 := ih (j + 1) (by omega)
    change 2 * X * chebT (j + 1) - chebT j =
      Polynomial.Chebyshev.T ℝ ((j + 2 : ℕ) : ℤ)
    rw [h1, h0]
    simp only [Nat.cast_add, Nat.cast_ofNat, Polynomial.Chebyshev.T_add_two]
    simp only [Nat.cast_one]

/-- Substituting the quadratic Chebyshev polynomial doubles the index. -/
theorem chebT_comp_quadratic (j : ℕ) :
    (chebT j).comp (2 * X ^ 2 - 1) = chebT (2 * j) := by
  rw [chebT_eq_mathlib, chebT_eq_mathlib,
    ← Polynomial.Chebyshev.T_two ℝ, ← Polynomial.Chebyshev.T_mul]
  congr 1
  push_cast
  ring

/-- Negating the input multiplies the source Chebyshev polynomial by its parity sign. -/
theorem chebT_comp_neg (j : ℕ) :
    (chebT j).comp (-X) = Polynomial.C ((-1 : ℝ) ^ j) * chebT j := by
  apply Polynomial.funext
  intro x
  simp only [chebT_eq_mathlib, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_eval_neg,
    Int.cast_negOnePow_natCast]

/-- The signed quadratic substitution gives the even-index term used in the Gaussian truncation. -/
theorem chebT_comp_neg_quadratic (j : ℕ) :
    ((chebT j).comp (-X)).comp (2 * X ^ 2 - 1) =
      Polynomial.C ((-1 : ℝ) ^ j) * chebT (2 * j) := by
  rw [chebT_comp_neg, Polynomial.mul_comp, Polynomial.C_comp, chebT_comp_quadratic]

/-- Equation 69 follows from the actual source polynomial definitions and Chebyshev composition. -/
theorem eq69_pGauss_value (γ : ℝ) (n : ℕ) :
    pGauss γ n = Polynomial.C (Real.exp (-(γ ^ 2) / 2)) *
      (Polynomial.C (besselI 0 (γ ^ 2 / 2)) +
        2 * ∑ j ∈ Finset.Icc 1 (n / 2),
          Polynomial.C (besselI j (γ ^ 2 / 2) * (-1 : ℝ) ^ j) * chebT (2 * j)) := by
  have hsum :
      (∑ j ∈ Finset.Icc 1 (n / 2),
        Polynomial.C (besselI j (γ ^ 2 / 2)) *
          ((chebT j).comp (-X)).comp (2 * X ^ 2 - 1)) =
        ∑ j ∈ Finset.Icc 1 (n / 2),
          Polynomial.C (besselI j (γ ^ 2 / 2) * (-1 : ℝ) ^ j) * chebT (2 * j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [chebT_comp_neg_quadratic, ← mul_assoc, ← Polynomial.C_mul]
  have hneg : -(γ ^ 2 / 2) = -(γ ^ 2) / 2 := by ring
  unfold pGauss pExp
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.add_comp,
    Polynomial.ofNat_comp, Polynomial.sum_comp]
  rw [hsum, hneg]
  norm_num

end Qatlib.Papers.SpectralAmp17.MainResults.Chebyshev
