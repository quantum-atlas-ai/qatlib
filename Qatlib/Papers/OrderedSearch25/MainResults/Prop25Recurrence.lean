/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Proposition 25: the neighbouring-coefficient recurrence

Carolan–Childs–Kovacs-Deak–Schaeffer, fixed arXiv:2503.21090v2, Section 4.1,
Proposition 25, Equations (137), (144) and (145).

The paper encodes the polynomial equality constraint (28) as

`(I + (-1)^t V_n) (a^(t) - a^(t-1)) = 0`   (Equation (144)),

where `a^(t)` is the coefficient vector of the symmetric Laurent polynomial
`q_t` and `V_n` is the reversal permutation of Equation (138). Taking the
difference of (144) at `t` and at `t+1` kills the reversal operator and
expresses `a^(t)` through its two neighbours:

`a^(t) = ½ (a^(t-1) + a^(t+1)) + ½ (-1)^t V_n (a^(t-1) - a^(t+1))`   (Equation (137)).

This module formalises that linear-algebra step for an *arbitrary* complex
matrix `V` acting on `Fin n → ℂ`, which is more general than the specific
`V_n`: the argument only uses linearity and the parity sign `(-1)^t`.

Not formalised here: the discrete-Fourier step that turns the evaluation
constraints (28) into the coefficient constraint (144).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch25.MainResults

open Matrix

/-- **Proposition 25 / Equation (137)**, derived from (144)–(145). Let `V` be
any complex `n × n` matrix (in the paper, the reversal permutation `V_n`), let
`A t` be the coefficient vector of `q_t`, and suppose the two constraints

`(I + s V) (A t - A (t-1)) = 0`,  `(I - s V) (A (t+1) - A t) = 0`

hold with `s = (-1)^t` (Equation (144) at `t` and `t+1`). Then the middle
vector is the paper's explicit average:
`A t = ½ (A (t-1) + A (t+1)) + ½ s V (A (t-1) - A (t+1))`. -/
theorem prop25_recurrence (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ)
    (A : ℕ → Fin n → ℂ) (t : ℕ) (s : ℂ)
    (h1 : (A t - A (t - 1)) + s • (V *ᵥ (A t - A (t - 1))) = 0)
    (h2 : (A (t + 1) - A t) + (-s) • (V *ᵥ (A (t + 1) - A t)) = 0) :
    A t = (1 / 2 : ℂ) • (A (t - 1) + A (t + 1))
      + (1 / 2 * s) • (V *ᵥ (A (t - 1) - A (t + 1))) := by
  funext i
  have h1i := congrFun h1 i
  have h2i := congrFun h2 i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_sub,
    smul_eq_mul] at h1i h2i ⊢
  linear_combination (1 / 2 : ℂ) * (h1i - h2i)

/-- The reversal permutation matrix `V_n` of Equation (138):
`(V_n)_{i,j} = 1` when `i + j + 1 = n`, and `0` otherwise. -/
def vnMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if (i : ℕ) + (j : ℕ) + 1 = n then 1 else 0

/-- The concrete instance of Proposition 25 for the reversal matrix `V_n`. -/
theorem prop25_recurrence_vn (n : ℕ) (A : ℕ → Fin n → ℂ) (t : ℕ) (s : ℂ)
    (h1 : (A t - A (t - 1)) + s • (vnMatrix n *ᵥ (A t - A (t - 1))) = 0)
    (h2 : (A (t + 1) - A t) + (-s) • (vnMatrix n *ᵥ (A (t + 1) - A t)) = 0) :
    A t = (1 / 2 : ℂ) • (A (t - 1) + A (t + 1))
      + (1 / 2 * s) • (vnMatrix n *ᵥ (A (t - 1) - A (t + 1))) :=
  prop25_recurrence n (vnMatrix n) A t s h1 h2

end Qatlib.Papers.OrderedSearch25.MainResults
