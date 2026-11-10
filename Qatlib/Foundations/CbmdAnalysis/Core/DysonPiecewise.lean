/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.DysonPropagator
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def dysonPiecewise {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) : ℕ → ℂ → Matrix I I ℂ
  | 0, _ => 1
  | n + 1, z => dysonPropagator (H n) (L n) (τ n) (τ (n + 1)) z *
      dysonPiecewise H L τ n z

noncomputable def dysonPiecewiseBudget {I : Type} [Fintype I] [DecidableEq I]
    (L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ∫ u in τ j..τ (j + 1), ‖L j u‖

theorem dysonPiecewise_differentiable {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (τ : ℕ → ℝ) (n : ℕ) :
    Differentiable ℂ (dysonPiecewise H L τ n) := by
  induction n with
  | zero => exact differentiable_const _
  | succ n ih =>
    exact (dysonPropagator_differentiable (H n) (L n) (hH n) (hL n) _ _).mul ih

theorem dysonPiecewise_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j))
    (hHherm : ∀ j u, (H j u).IsHermitian) (hLpos : ∀ j u, (L j u).PosSemidef)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (n : ℕ) (z : ℂ) :
    ‖dysonPiecewise H L τ n z‖ ≤
      Real.exp (max z.im 0 * dysonPiecewiseBudget L τ n) := by
  induction n with
  | zero =>
    simp only [dysonPiecewise, dysonPiecewiseBudget, Finset.range_zero,
      Finset.sum_empty, mul_zero, Real.exp_zero]
    rcases subsingleton_or_nontrivial (Matrix I I ℂ) with h | h
    · simp [Subsingleton.elim (1 : Matrix I I ℂ) 0]
    · exact CStarRing.norm_one.le
  | succ n ih =>
    have hn := dysonPropagator_norm_le (H n) (L n) (hH n) (hL n)
      (hHherm n) (hLpos n) _ _ (hτ (Nat.le_succ n)) z
    calc
      _ ≤ ‖dysonPropagator (H n) (L n) (τ n) (τ (n + 1)) z‖ *
          ‖dysonPiecewise H L τ n z‖ := norm_mul_le _ _
      _ ≤ Real.exp (max z.im 0 * ∫ u in τ n..τ (n + 1), ‖L n u‖) *
          Real.exp (max z.im 0 * dysonPiecewiseBudget L τ n) :=
        mul_le_mul hn ih (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        simp only [dysonPiecewiseBudget, Finset.sum_range_succ]
        ring

theorem dysonPiecewise_real_unitary {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j))
    (hHherm : ∀ j u, (H j u).IsHermitian) (hLherm : ∀ j u, (L j u).IsHermitian)
    (τ : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    dysonPiecewise H L τ n (x : ℂ) ∈ Matrix.unitaryGroup I ℂ := by
  induction n with
  | zero => exact (Matrix.unitaryGroup I ℂ).one_mem
  | succ n ih =>
    exact (Matrix.unitaryGroup I ℂ).mul_mem
      (dysonPropagator_real_unitary (H n) (L n) (hH n) (hL n)
        (hHherm n) (hLherm n) _ _ x) ih

noncomputable def dysonPiecewisePath {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (n : ℕ) (z : ℂ)
    (t : ℝ) : Matrix I I ℂ :=
  dysonPropagator (H n) (L n) (τ n) t z * dysonPiecewise H L τ n z

theorem dysonPiecewisePath_hasDerivAt {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (n : ℕ)
    (hH : Continuous (H n)) (hL : Continuous (L n)) (z : ℂ) (t : ℝ) :
    HasDerivAt (dysonPiecewisePath H L τ n z)
      (-(Complex.I • (H n t + z • L n t) * dysonPiecewisePath H L τ n z t)) t := by
  convert! (dysonPropagator_hasDerivAt (H n) (L n) hH hL (τ n) t z).mul_const
    (dysonPiecewise H L τ n z) using 1
  simp only [dysonPiecewisePath, neg_mul, mul_assoc]

theorem dysonPiecewisePath_join {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    dysonPiecewisePath H L τ (n + 1) z (τ (n + 1)) =
      dysonPiecewisePath H L τ n z (τ (n + 1)) := by
  simp only [dysonPiecewisePath, dysonPropagator_self, one_mul, dysonPiecewise]

@[simp] theorem dysonPiecewisePath_initial {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (z : ℂ) :
    dysonPiecewisePath H L τ 0 z (τ 0) = 1 := by
  simp only [dysonPiecewisePath, dysonPropagator_self, dysonPiecewise, mul_one]

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
