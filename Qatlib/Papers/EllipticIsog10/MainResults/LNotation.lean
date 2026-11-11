/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# The subexponential `L`-notation and the `√2` constant of the hidden-shift sieve

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3.

The source writes

`L_N(1/2, c) = exp((c + o(1)) · √(ln N · ln ln N))`

(§4, before Proposition 4.1) and then states

* Theorem 5.2 / Theorem A.1: the general abelian hidden shift problem costs
  `L_|A|(1/2, √2)` time and `poly(log |A|)` space;
* Theorem 5.4: Algorithm 3 costs `L_q(1/2, 3/2 + √2)` when Theorem 5.2 supplies
  the hidden-shift subroutine.

Two pieces of that arithmetic are formalized here, with the `(1 + o(1))` and the
`o(1)` absorbed into the leading constant as the source does:

1. `Lsubexp_add`: the `L`-notation is multiplicative in the second argument, so
   composing a cost `L(1/2, a)` with a subroutine cost `L(1/2, b)` yields
   `L(1/2, a + b)`.  This is the step that turns `3/2` (Theorem 4.6's exponent
   for one evaluation of the hiding functions) plus `√2` (Theorem 5.2's
   exponent) into `3/2 + √2` in Theorem 5.4.
2. `sieveExponent` and `sieveExponent_optimal`: after Lemma A.3, Algorithm 5 is
   analysed with `k = c·√(log₂N · log₂log₂N)` and `m·k = (1+o(1))log₂N`, and its
   running time is `L_N(1/2, c + 1/(2c))`.  Minimizing `c + 1/(2c)` over `c > 0`
   gives `√2` at `c = 1/√2`, which is the constant of Theorem 5.2 / A.1.

The analytic derivation of the exponent from the algorithm (`(1+o(1))` estimates,
the `mk = (1+o(1))log₂N` substitution and the `o(1)` bookkeeping) is *not*
formalized; see the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

noncomputable section

/-- The subexponential cost scale `L_N(1/2, c) = exp(c · √(ln N · ln ln N))` of
the paper's `L`-notation, with the `(1 + o(1))` factor absorbed into the value
`c` and with the `1/2` exponent fixed, as it is in every result of this paper. -/
def Lsubexp (N c : ℝ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log N * Real.log (Real.log N)))

/-- `L_N(1/2, 0) = 1`: a subexponential cost with vanishing constant is free at
leading order, which is how the source treats `L(0)` and `L(o(1))`. -/
theorem Lsubexp_zero (N : ℝ) : Lsubexp N 0 = 1 := by
  simp [Lsubexp]

/-- **`L`-notation is multiplicative in its second argument.** Composing a cost
`L(1/2, a)` with a subroutine of cost `L(1/2, b)` costs `L(1/2, a + b)`; this is
the arithmetic of Theorem 5.4 (`3/2 + √2`). -/
theorem Lsubexp_add (N a b : ℝ) :
    Lsubexp N a * Lsubexp N b = Lsubexp N (a + b) := by
  rw [Lsubexp, Lsubexp, Lsubexp, ← Real.exp_add]
  congr 1
  ring

/-- `L_N(1/2, c)` is a positive cost for every scale and constant. -/
theorem Lsubexp_pos (N c : ℝ) : 0 < Lsubexp N c := Real.exp_pos _

/-- `L` is monotone in the second argument. -/
theorem Lsubexp_mono (N : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Lsubexp N a ≤ Lsubexp N b := by
  rw [Lsubexp, Lsubexp, Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg _)

/-- **Sum of two subexponential costs is dominated by the larger one.**  For
constants `c`, `d`, the cost `L(1/2,c) + L(1/2,d)` is at most twice
`L(1/2, max c d)`; this is the `L(c1) + L(c2) = L(max c1 c2)` step used when
combining the stages of Algorithms 1 and 2 (Propositions 4.1, Theorem 4.6). -/
theorem Lsubexp_add_le_two_mul_max (N c d : ℝ) :
    Lsubexp N c + Lsubexp N d ≤ 2 * Lsubexp N (max c d) := by
  have hc : Lsubexp N c ≤ Lsubexp N (max c d) := Lsubexp_mono N (le_max_left c d)
  have hd : Lsubexp N d ≤ Lsubexp N (max c d) := Lsubexp_mono N (le_max_right c d)
  linarith

/-- **Theorem 5.4's exponent.** With one evaluation of the hiding functions
costing `L_q(1/2, √3/2)` (Corollary 4.7) and Theorem 5.2's hidden-shift solver
costing `L_q(1/2, √2)` evaluations, Algorithm 3 costs `L_q(1/2, √3/2 + √2)`. -/
theorem theorem5_4_exponent (q : ℝ) :
    Lsubexp q (Real.sqrt 3 / 2) * Lsubexp q (Real.sqrt 2) =
      Lsubexp q (Real.sqrt 3 / 2 + Real.sqrt 2) :=
  Lsubexp_add q (Real.sqrt 3 / 2) (Real.sqrt 2)

/-- The sieve exponent `c + 1/(2c)` that the source obtains after Lemma A.3:
with `k = c·√(log₂N · log₂log₂N)` and `m·k = (1+o(1))log₂N`, the running time of
Algorithm 5 is `2^k · k^m = L_N(1/2, c + 1/(2c))`. -/
def sieveExponent (c : ℝ) : ℝ := c + 1 / (2 * c)

/-- **The `√2` lower bound.** For every `c > 0` the sieve exponent is at least
`√2`; equivalently `(c + 1/(2c))² = c² + 1/(4c²) + 1 ≥ 2`. -/
theorem sieveExponent_ge_sqrt_two (c : ℝ) (hc : 0 < c) :
    Real.sqrt 2 ≤ sieveExponent c := by
  have hnonneg : 0 ≤ sieveExponent c := by
    unfold sieveExponent
    positivity
  have hsq : 2 ≤ sieveExponent c ^ 2 := by
    have hsquare : 0 ≤ (c - 1 / (2 * c)) ^ 2 := sq_nonneg _
    have hcne : c ≠ 0 := ne_of_gt hc
    unfold sieveExponent
    field_simp at hsquare ⊢
    nlinarith
  calc Real.sqrt 2 ≤ Real.sqrt (sieveExponent c ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = sieveExponent c := Real.sqrt_sq hnonneg

/-- **The optimal constant.** Choosing `c = 1/√2` as in the source makes the sieve
exponent exactly `√2`, which is the constant of Theorem 5.2 and Theorem A.1. -/
theorem sieveExponent_at_optimum : sieveExponent (1 / Real.sqrt 2) = Real.sqrt 2 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold sieveExponent
  field_simp
  nlinarith

/-- **`c = 1/√2` is the minimizer.** The sieve exponent never drops below its
value at `c = 1/√2`, so `√2` is the best constant obtainable from the
Algorithm 5 analysis, as the source asserts. -/
theorem sieveExponent_optimal (c : ℝ) (hc : 0 < c) :
    sieveExponent (1 / Real.sqrt 2) ≤ sieveExponent c := by
  rw [sieveExponent_at_optimum]
  exact sieveExponent_ge_sqrt_two c hc

/-- **Corollary 4.7, arithmetic core.**  Theorem 4.6 bounds the running time of
Algorithm 2 by `L(1/(4z))` plus `max {L(3z), L(z)(ln q)^{3+ε}}`, whose leading
`L`-exponent is `max {1/(4z), 3z}`.  For every `z > 0` this exponent is at
least `√3/2`. -/
theorem cor4_7_max_lower (z : ℝ) (hz : 0 < z) :
    Real.sqrt 3 / 2 ≤ max (1 / (4 * z)) (3 * z) := by
  by_contra h
  rw [not_le] at h
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h1 : 1 / (4 * z) < Real.sqrt 3 / 2 := lt_of_le_of_lt (le_max_left _ _) h
  have h2 : 3 * z < Real.sqrt 3 / 2 := lt_of_le_of_lt (le_max_right _ _) h
  have e1 : 1 < 2 * Real.sqrt 3 * z := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * z)] at h1
    have heq : (Real.sqrt 3 / 2) * (4 * z) = 2 * Real.sqrt 3 * z := by ring
    linarith [h1, heq]
  have e2 : 6 * z < Real.sqrt 3 := by linarith [h2]
  nlinarith [e1, e2, hs3sq, hs3]

/-- **Corollary 4.7, optimal parameter.**  The exponent `max {1/(4z), 3z}` is
attained at `z = 1/(2√3)`, where both terms equal `√3/2`; hence the bound
`L_q(1/2, √3/2)` is exactly the best the `z`-optimisation yields. -/
theorem cor4_7_at_optimum :
    max (1 / (4 * (1 / (2 * Real.sqrt 3)))) (3 * (1 / (2 * Real.sqrt 3)))
      = Real.sqrt 3 / 2 := by
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3
  have hA : 1 / (4 * (1 / (2 * Real.sqrt 3))) = Real.sqrt 3 / 2 := by
    field_simp
    nlinarith [hs3sq]
  have hB : 3 * (1 / (2 * Real.sqrt 3)) = Real.sqrt 3 / 2 := by
    field_simp
    nlinarith [hs3sq]
  rw [hA, hB, max_self]

/-- **Corollary 4.7.**  Optimising `z > 0` yields the leading constant `√3/2`
of Algorithm 2's running time `L_q(1/2, √3/2)`: `√3/2` is a lower bound for
every `z > 0` and is achieved at `z = 1/(2√3)`. -/
theorem cor4_7 :
    (∀ z : ℝ, 0 < z → Real.sqrt 3 / 2 ≤ max (1 / (4 * z)) (3 * z)) ∧
      max (1 / (4 * (1 / (2 * Real.sqrt 3)))) (3 * (1 / (2 * Real.sqrt 3)))
        = Real.sqrt 3 / 2 :=
  ⟨cor4_7_max_lower, cor4_7_at_optimum⟩

end

end Qatlib.Papers.EllipticIsog10.MainResults
