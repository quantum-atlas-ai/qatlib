/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Multivariate trigonometric polynomials (SignalJing26, Section II)

This module fixes the polynomial model of *Multivariate quantum signal processing
with optimal query complexity* (Jing, Wang, Yu, Zhang; arXiv:2610.03393v1), Section II.

An `N`-variate polynomial in the half-angle variable `z(x) = e^{ix/2}` (Equation (1) of
the paper) is represented by its finitely supported coefficient function
`C : (Fin N → ℤ) →₀ ℂ`, with value

  `P(x) = ∑_n C_n ∏_j z(x_j)^{n_j} = ∑_n C_n e^{i (n · x) / 2}`.

The three quantities the paper attaches to `P` are

* the **parity** `Parity p P`: `C_n = 0` unless `n ≡ p (mod 2)` entrywise,
* the **degree vector** `degree P j = max_{n : C_n ≠ 0} |n_j|`, and
* the **coefficient 1-norm** `coeffL1 P = ∑_n |C_n|`,

together with the supremum-bound predicate `SupNormLE P 1` standing for `‖P‖_∞ ≤ 1`.

The normalized class `P_L` of Equation (10) is `InPL L P`.

All definitions are half-angle (`P_{1/2}`) — the class in which Section III A lives.
The integer-angle unitary class `P_1` of Section III B is the `z(x) = e^{ix}` model; it is
handled by the same coefficient carrier and reinterpreted in `Sources/MultivarCircuit.lean`.
-/

namespace Qatlib.Papers.SignalJing26.MultivarQSP.Sources

open scoped BigOperators

set_option autoImplicit false

/-- Exponent vectors `n ∈ ℤ^N` of a multivariate trigonometric polynomial. -/
abbrev ExpVec (N : ℕ) := Fin N → ℤ

/-- The coefficient carrier of an `N`-variate trigonometric polynomial in `e^{ix_j/2}`.
This is Equation (1) of the paper: a finitely supported family of complex coefficients. -/
abbrev TrigPoly (N : ℕ) : Type := (ExpVec N) →₀ ℂ

namespace TrigPoly

variable {N : ℕ}

/-- The value `P(x) = ∑_n C_n e^{i (n · x)/2}` of the polynomial at `x : ℝ^N`, i.e. the
half-angle evaluation of Equation (1). -/
noncomputable def eval (P : TrigPoly N) (x : Fin N → ℝ) : ℂ :=
  ∑ n ∈ P.support,
    P.toFun n * Complex.exp (Complex.I * ((∑ j : Fin N, (n j : ℂ) * (x j : ℂ)) / 2))

/-- The coefficient 1-norm `‖P‖_{c,1} = ∑_n |C_n|` of the paper, Section II. -/
noncomputable def coeffL1 (P : TrigPoly N) : ℝ :=
  ∑ n ∈ P.support, ‖P.toFun n‖

/-- The `j`-th entry of the degree vector `deg_j(P) = max_{n : C_n ≠ 0} |n_j|`
(Equation (2)). It is `0` for the zero polynomial, as in the paper. -/
noncomputable def degree (P : TrigPoly N) (j : Fin N) : ℕ :=
  P.support.sup (fun n => (n j).natAbs)

/-- `P` has parity `p` if `C_n = 0` unless `n ≡ p` entrywise modulo two (Section II). -/
def Parity (p : ExpVec N) (P : TrigPoly N) : Prop :=
  ∀ n ∈ P.support, ∀ j : Fin N, Even (n j - p j)

/-- `‖P‖_∞ ≤ c`, i.e. `‖P(x)‖ ≤ c` for every `x`. This is the sup-norm bound of the paper. -/
def SupNormLE (P : TrigPoly N) (c : ℝ) : Prop :=
  ∀ x : Fin N → ℝ, ‖eval P x‖ ≤ c

/-- The normalized class `P_L` of Equation (10): degree at most `L`, parity `L mod 2`,
and coefficient 1-norm at most one. -/
def InPL (L : Fin N → ℕ) (P : TrigPoly N) : Prop :=
  (∀ j : Fin N, degree P j ≤ L j) ∧ Parity (fun j => (L j : ℤ)) P ∧ coeffL1 P ≤ 1

/-- The even-degree class `P_{L,0}` of Equation (11): degree at most `L`, trivial parity,
and coefficient 1-norm at most one. -/
def InPL0 (L : Fin N → ℕ) (P : TrigPoly N) : Prop :=
  (∀ j : Fin N, degree P j ≤ L j) ∧ Parity (fun _ => (0 : ℤ)) P ∧ coeffL1 P ≤ 1

/-- The zero polynomial evaluates to zero. -/
@[simp] theorem eval_zero (x : Fin N → ℝ) : eval (0 : TrigPoly N) x = 0 := by
  simp [eval]

/-- The coefficient 1-norm of the zero polynomial is zero. -/
@[simp] theorem coeffL1_zero : coeffL1 (0 : TrigPoly N) = 0 := by
  simp [coeffL1]

/-- The coefficient 1-norm is nonnegative. -/
theorem coeffL1_nonneg (P : TrigPoly N) : 0 ≤ coeffL1 P := by
  unfold coeffL1
  exact Finset.sum_nonneg (fun n _ => norm_nonneg _)

/-- The zero polynomial has degree zero in every coordinate. -/
theorem degree_zero (j : Fin N) : degree (0 : TrigPoly N) j = 0 := by
  simp [degree]

/-- The zero polynomial lies in every normalized class `P_L`. -/
theorem zero_inPL (L : Fin N → ℕ) : InPL L (0 : TrigPoly N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j; rw [degree_zero]; exact Nat.zero_le _
  · intro n hn
    simp at hn
  · rw [coeffL1_zero]; norm_num

/-- If `P` has parity `p` and `P` is supported in a set all of whose exponents have parity
`p`, then `P` has parity `p`. (Elementary restatement used to pass between parity
witnesses.) -/
theorem parity_of_forall (p : ExpVec N) (P : TrigPoly N)
    (h : ∀ n ∈ P.support, ∀ j : Fin N, Even (n j - p j)) : Parity p P := h

/-- The supremum bound is monotone in the bound. -/
theorem supNormLE_mono {P : TrigPoly N} {c d : ℝ} (hcd : c ≤ d) (h : SupNormLE P c) :
    SupNormLE P d := fun x => le_trans (h x) hcd

end TrigPoly

end Qatlib.Papers.SignalJing26.MultivarQSP.Sources
