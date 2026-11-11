/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent

/-!
# Polyak–Łojasiewicz bounds for gradient iterates

`gdIter` defines fixed-step gradient descent, and `PLCond` relates the squared gradient norm to
a reference cost gap. Smoothness and a permitted step size give a one-step gap bound, followed
by geometric and exponential estimates under the stated additional hypotheses.

This development follows [YaoEtAl2026].

## Main statements

* `pl_one_step`: the next gap is at most `1 - η * μ` times the current gap.
* `pl_iterate_geometric`: the one-step estimate iterates when `η * μ ≤ 1`.
* `lemma3_pl_contraction`: a global lower bound allows an exponential gap estimate.

## References

* [Yao et al., 2026][YaoEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Gradient InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.PL

open Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient-descent sequence starting at `x0` with fixed step size `η`. -/
def gdIter (f : E → ℝ) (η : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | n + 1 => gdIter f η x0 n - η • ∇ f (gdIter f η x0 n)

/-- The Polyak–Łojasiewicz condition `(1 / 2) * ‖∇ f x‖ ^ 2 ≥ μ * (f x - fstar)` at every point. -/
def PLCond (f : E → ℝ) (μ fstar : ℝ) : Prop :=
  ∀ x, (1 / 2) * ‖∇ f x‖ ^ 2 ≥ μ * (f x - fstar)

/-- For positive `β`, `SmoothGrad f β`, `PLCond f μ fstar`, and `0 < η ≤ 1 / β`, the gap after
one gradient step is at most `(1 - η * μ)` times the current gap. -/
theorem pl_one_step (f : E → ℝ) (β η μ fstar : ℝ) (hβ : 0 < β)
    (hsmooth : SmoothGrad f β) (hη0 : 0 < η) (hη : η ≤ 1 / β)
    (hpl : PLCond f μ fstar) (x : E) :
    f (x - η • ∇ f x) - fstar ≤ (1 - η * μ) * (f x - fstar) := by
  have hdesc := lemma1_descent_lower f β η hβ hsmooth hη0 hη x
  have hplx := hpl x
  have hηle : 0 ≤ η := le_of_lt hη0
  have hstep : η * ((1 / 2) * ‖∇ f x‖ ^ 2) ≥ η * (μ * (f x - fstar)) :=
    mul_le_mul_of_nonneg_left hplx hηle
  nlinarith [hdesc, hstep]

/-- Under smoothness, the PL condition, `0 < η ≤ 1 / β`, and `η * μ ≤ 1`, the gap at iterate `n`
is at most `(1 - η * μ) ^ n` times the initial gap. -/
theorem pl_iterate_geometric (f : E → ℝ) (β η μ fstar : ℝ) (hβ : 0 < β)
    (hsmooth : SmoothGrad f β) (hη0 : 0 < η) (hη : η ≤ 1 / β)
    (hpl : PLCond f μ fstar) (hμη : η * μ ≤ 1) (x0 : E) :
    ∀ n : ℕ,
      f (gdIter f η x0 n) - fstar ≤ (1 - η * μ) ^ n * (f x0 - fstar) := by
  intro n
  induction n with
  | zero => simp [gdIter]
  | succ m ih =>
      have hstep := pl_one_step f β η μ fstar hβ hsmooth hη0 hη hpl (gdIter f η x0 m)
      have hnn : 0 ≤ 1 - η * μ := by linarith
      calc f (gdIter f η x0 (m + 1)) - fstar
          = f (gdIter f η x0 m - η • ∇ f (gdIter f η x0 m)) - fstar := by rfl
        _ ≤ (1 - η * μ) * (f (gdIter f η x0 m) - fstar) := hstep
        _ ≤ (1 - η * μ) * ((1 - η * μ) ^ m * (f x0 - fstar)) :=
            mul_le_mul_of_nonneg_left ih hnn
        _ = (1 - η * μ) ^ (m + 1) * (f x0 - fstar) := by rw [pow_succ]; ring

/-- Under smoothness, the PL condition, a global lower bound `fstar`, `0 < η ≤ 1 / β`, and `η *
μ ≤ 1`, the gap at iterate `n` is at most `exp (-(η * μ * n))` times the initial gap. See
[YaoEtAl2026]. -/
theorem lemma3_pl_contraction (f : E → ℝ) (β η μ fstar : ℝ) (hβ : 0 < β)
    (hsmooth : SmoothGrad f β) (hη0 : 0 < η) (hη : η ≤ 1 / β)
    (hpl : PLCond f μ fstar) (hmin : ∀ x, fstar ≤ f x) (hμη : η * μ ≤ 1)
    (x0 : E) (n : ℕ) :
    f (gdIter f η x0 n) - fstar ≤
      Real.exp (-(η * μ * n)) * (f x0 - fstar) := by
  have hgeo := pl_iterate_geometric f β η μ fstar hβ hsmooth hη0 hη hpl hμη x0 n
  have hnn : 0 ≤ 1 - η * μ := by linarith
  have hbase : 1 - η * μ ≤ Real.exp (-(η * μ)) := by
    have := Real.add_one_le_exp (-(η * μ))
    linarith
  have hpow : (1 - η * μ) ^ n ≤ Real.exp (-(η * μ)) ^ n := pow_le_pow_left₀ hnn hbase n
  have hexp : Real.exp (-(η * μ)) ^ n = Real.exp (-(η * μ * n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpow
  have hgap0 : 0 ≤ f x0 - fstar := by linarith [hmin x0]
  calc f (gdIter f η x0 n) - fstar
      ≤ (1 - η * μ) ^ n * (f x0 - fstar) := hgeo
    _ ≤ Real.exp (-(η * μ * n)) * (f x0 - fstar) :=
        mul_le_mul_of_nonneg_right hpow hgap0

end Qatlib.Papers.DissipVarFw26.FrameworkCost.PL
