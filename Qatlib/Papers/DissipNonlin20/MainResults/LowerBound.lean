/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# DissipNonlin20 — Lemma 7/8 support and the Theorem 2 composition

Source: arXiv:2011.03185 (quantum simulation of dissipative nonlinear
dynamics), Lemmas 7-8 and Theorem 2 (pp. 24-27).

This module preserves the closed declarations of the original development of
this material: the scalar analytic endpoints of Lemma 8 (the solution formula
`lemma8_solution_hasDerivAt`, the overlap bound, the initial-overlap identity
and the `log(1+1/ε) ≤ 2 log(1/ε)` comparison), the Lemma 7 query lower-bound
chain (trace distance → advantage → query bound), and the quantitative
composition `theorem2_composition` (queries ≥ c₁/ε with T ≤ c₂ log(1/ε)
forces queries ≥ c₁ exp(T/c₂)).

Two obligations remain deferred/refuted in this development with the
original statements preserved in the project history:

* `lemma8_statement` — needs the blow-up of `nonlinearSolution` at
  `t* = log(R/(R - 1/w0))` and the existence/monotonicity of the time `T`
  with `K(T) ≥ 2`;
* `theorem2_statement` — refuted in the legacy model by
  `theorem2_statement_refuted` below: `QuadraticODEAlgorithm` carries only an
  unconstrained `queries` function and a `bounded_error : Prop` flag, so the
  zero-query record satisfies every hypothesis and defeats the lower bound;
  a faithful statement needs a state-discrimination semantics first.
-/

set_option autoImplicit false

namespace Qatlib.Papers.DissipNonlin20.MainResults.LowerBound

noncomputable section

/-- The Bernoulli estimate used by Lemma 7: for `0 ≤ ε ≤ 2`,
`1 - (1 - ε)^(2k) ≤ 2kε`. -/
theorem one_sub_pow_le_mul (ε : ℝ) (k : ℕ) (hε2 : ε ≤ 2) :
    1 - (1 - ε) ^ (2 * k) ≤ 2 * (k : ℝ) * ε := by
  have h := one_add_mul_le_pow (a := -ε) (by linarith) (2 * k)
  have h' : 1 - 2 * (k : ℝ) * ε ≤ (1 - ε) ^ (2 * k) := by
    convert h using 1; push_cast; ring
  linarith

/-- **Lemma 7, trace-distance chain (printed p. 24).**  The trace distance of the `k`-copy
states is at most `√(1 - (1-ε)^{2k})`, and this is at most `√(2kε)`.  This is the displayed
chain `√(1 - (1-ε)^{2k}) ≤ √(2kε)` of the proof. -/

theorem lemma7_trace_distance_le (ε : ℝ) (k : ℕ) (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.sqrt (1 - (1 - ε) ^ (2 * k)) ≤ Real.sqrt (2 * (k : ℝ) * ε) := by
  apply Real.sqrt_le_sqrt
  exact one_sub_pow_le_mul ε k (by linarith)

/-- **Lemma 7, advantage bound.**  If the advantage over random guessing is `β` and
`β ≤ √(1 - (1-ε)^{2k})/2`, then `4β² ≤ 1 - (1-ε)^{2k}`.  This is the Helstrom step of the
proof: the advantage is at most half the trace distance, so it is at most
`√(1 - (1-ε)^{2k})/2`. -/

theorem lemma7_advantage_bound (ε β : ℝ) (k : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β)
    (hadv : β ≤ Real.sqrt (1 - (1 - ε) ^ (2 * k)) / 2) :
    4 * β ^ 2 ≤ 1 - (1 - ε) ^ (2 * k) := by
  have hbase0 : 0 ≤ 1 - ε := by linarith
  have hbase1 : 1 - ε ≤ 1 := by linarith
  have hpow : (1 - ε) ^ (2 * k) ≤ 1 := pow_le_one₀ hbase0 hbase1
  have hx : 0 ≤ 1 - (1 - ε) ^ (2 * k) := by linarith
  have h2 : 2 * β ≤ Real.sqrt (1 - (1 - ε) ^ (2 * k)) := by linarith
  have hnn : 0 ≤ 2 * β := by positivity
  have hsq := pow_le_pow_left₀ hnn h2 2
  rw [Real.sq_sqrt hx] at hsq
  nlinarith

/-- **Lemma 7, query lower bound with explicit constant.**  A protocol distinguishing two
qubit states of overlap `1 - ε` with advantage `β` must use at least `2β²/ε` queries.  This
is the `Ω(1/ε)` claim of Lemma 7 (printed p. 24), with the constant made explicit by
combining the Helstrom bound `4β² ≤ 1 - (1-ε)^{2k}` and the Bernoulli estimate
`1 - (1-ε)^{2k} ≤ 2kε`. -/

theorem lemma7_query_lower_bound (ε β : ℝ) (k : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β)
    (hadv : β ≤ Real.sqrt (1 - (1 - ε) ^ (2 * k)) / 2) :
    2 * β ^ 2 / ε ≤ (k : ℝ) := by
  have h4 := lemma7_advantage_bound ε β k hε hε1 hβ hadv
  have hb := one_sub_pow_le_mul ε k (by linarith)
  have h2k : 4 * β ^ 2 ≤ 2 * (k : ℝ) * ε := by linarith
  rw [div_le_iff₀ hε]
  nlinarith

/-- **Lemma 7, bounded-error form (printed p. 24).**  If the protocol succeeds with
probability at least `2/3`, its advantage is at least `1/6`; plugging `β = 1/6` into
`lemma7_query_lower_bound` gives the bound `k ≥ 1/(18ε)`.  This is the `Ω(1/ε)` statement of
Lemma 7 with an explicit constant. -/

theorem lemma7_statement (ε : ℝ) (k : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hadv : (1 : ℝ) / 6 ≤ Real.sqrt (1 - (1 - ε) ^ (2 * k)) / 2) :
    (1 : ℝ) / (18 * ε) ≤ (k : ℝ) := by
  have h := lemma7_query_lower_bound ε (1 / 6) k hε hε1 (by norm_num) hadv
  have heq : 2 * (1 / 6 : ℝ) ^ 2 / ε = 1 / (18 * ε) := by
    field_simp
    ring
  linarith

/-! ## Lemma 8: the explicit quadratic ODE instance -/

/-- The explicit solution (5.2) of the scalar equation `u' = -u + R u²`:
`u(t) = 1 / (R - e^t (R - 1/u(0)))`. -/

def nonlinearSolution (R x0 t : ℝ) : ℝ :=
  1 / (R - Real.exp t * (R - 1 / x0))

/-- **Lemma 8, Eq. (5.2): the explicit solution solves (5.1).**  For
`u(t) = 1/(R - e^t (R - 1/u(0)))`, one has `u'(t) = -u(t) + R u(t)²`, the scalar form of
(5.1) `du/dt = -u + R u²`. -/

theorem lemma8_solution_hasDerivAt (R x0 t : ℝ)
    (hD : R - Real.exp t * (R - 1 / x0) ≠ 0) :
    HasDerivAt (fun y => nonlinearSolution R x0 y)
      (-(nonlinearSolution R x0 t) + R * nonlinearSolution R x0 t ^ 2) t := by
  have hden : HasDerivAt (fun y : ℝ => R - Real.exp y * (R - 1 / x0))
      (-(Real.exp t * (R - 1 / x0))) t :=
    ((Real.hasDerivAt_exp t).mul_const (R - 1 / x0)).const_sub R
  have hinv := hden.inv hD
  have hinv' : HasDerivAt (fun y : ℝ => (R - Real.exp y * (R - 1 / x0))⁻¹)
      ((Real.exp t * (R - 1 / x0)) /
        (R - Real.exp t * (R - 1 / x0)) ^ 2) t :=
    hinv.congr_deriv (by ring)
  have hfun : (fun y => nonlinearSolution R x0 y)
      = fun y => (R - Real.exp y * (R - 1 / x0))⁻¹ := by
    funext y
    simp [nonlinearSolution, one_div]
  have hval : ((Real.exp t * (R - 1 / x0)) / (R - Real.exp t * (R - 1 / x0)) ^ 2) =
      -(1 / (R - Real.exp t * (R - 1 / x0))) +
        R * (1 / (R - Real.exp t * (R - 1 / x0))) ^ 2 := by
    field_simp [hD]
    ring
  rw [hfun]
  change HasDerivAt (fun y => (R - Real.exp y * (R - 1 / x0))⁻¹)
    (-(1 / (R - Real.exp t * (R - 1 / x0))) +
      R * (1 / (R - Real.exp t * (R - 1 / x0))) ^ 2) t
  exact hinv'.congr_deriv hval

/-- **Lemma 8, Eq. (5.15): the overlap bound.**  For `K ≥ 2`,
`(K + 1)/√(2K² + 2) ≤ 3/√10`.  This is the bound displayed in (5.15), obtained by squaring:
`10(K+1)² ≤ 9(2K²+2) ⟺ 4(2K-1)(K-2) ≥ 0`. -/

theorem lemma8_overlap_bound (K : ℝ) (hK : 2 ≤ K) :
    (K + 1) / Real.sqrt (2 * K ^ 2 + 2) ≤ 3 / Real.sqrt 10 := by
  have hK1 : 0 ≤ K + 1 := by linarith
  have hden : 0 < 2 * K ^ 2 + 2 := by positivity
  have hsqineq : (K + 1) ^ 2 / (2 * K ^ 2 + 2) ≤ 9 / 10 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 10)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * K - 1) (by linarith : (0:ℝ) ≤ K - 2)]
  have hleft : Real.sqrt ((K + 1) ^ 2 / (2 * K ^ 2 + 2)) =
      (K + 1) / Real.sqrt (2 * K ^ 2 + 2) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hK1]
  have hright : Real.sqrt (9 / 10 : ℝ) = 3 / Real.sqrt 10 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 9)]
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  have := Real.sqrt_le_sqrt hsqineq
  rwa [hleft, hright] at this

/-- **Lemma 8, Eq. (5.17): the logarithmic time scaling.**  For `0 < ε ≤ 1/2`,
`log(1 + 1/ε) ≤ 2 log(1/ε)`.  The paper's terminal time obeys
`T < log(1 + 1/√(2ε - ε² - ε))` (5.17), which is `O(log(1/ε))`; this lemma records the
elementary comparison with `log(1/ε)` used for that estimate. -/

theorem lemma8_time_scaling (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    Real.log (1 + 1 / ε) ≤ 2 * Real.log (1 / ε) := by
  have hle : 1 + 1 / ε ≤ 2 / ε := by
    have h1 : 1 ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      linarith
    have h2 : (2 : ℝ) / ε = 1 / ε + 1 / ε := by ring
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + 1 / ε) hle
  have hsplit : Real.log (2 / ε) = Real.log 2 + Real.log (1 / ε) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hε), one_div, Real.log_inv]
    ring
  have hlog2 : Real.log 2 ≤ Real.log (1 / ε) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hε]
    nlinarith
  linarith

/-- **Lemma 8, Eq. (5.4)--(5.7): the initial overlap.**  If the angle `θ` is chosen with
`2 sin²(θ/2) = ε`, then `cos θ = 1 - ε`; this is the identity (5.4) + (5.7) producing two
qubit states `|φ(0)⟩ = (|0⟩+|1⟩)/√2` and `|ψ(0)⟩ = cos(θ+π/4)|0⟩ + sin(θ+π/4)|1⟩` with
overlap `1 - ε`. -/

theorem lemma8_initial_overlap (θ ε : ℝ) (h : 2 * Real.sin (θ / 2) ^ 2 = ε) :
    Real.cos θ = 1 - ε := by
  have h2 : θ = 2 * (θ / 2) := by ring
  rw [h2, Real.cos_two_mul_eq_one_sub]
  linarith

/- **Lemma 8: existence of the hard instance (printed pp. 24--26).**

There is an instance of the quantum quadratic ODE problem (5.1) with `R ≥ √2` and two
initial states of squared norm one and overlap `1 - ε`, whose solutions at a time
`T = O(log(1/ε))` have normalised overlap at most `√(3/10)`.

The statement is made concrete through the explicit solution `nonlinearSolution` of (5.2):
the first initial state is `(1/√2, 1/√2)`, the second is `(v₀, w₀)`, and at time `T` the
normalised overlap of the two output states is
`(K+1)/√(2K²+2)` with `K = w(T)/v(T)`, exactly the quantity of (5.14)--(5.15).

Not formalised: the existence of `T` with `K(T) ≥ 2` (5.13), which the paper obtains from
`w(t) → ∞` as `t → t*` (5.3) while `v(t)` remains finite, together with the monotonicity of
`K(t)`; and the rewriting of `T < t*` into the explicit expression (5.17).  The overlap
bound (5.15) itself is proved in `lemma8_overlap_bound`, the solution formula in
`lemma8_solution_hasDerivAt`, the initial-overlap identity (5.7) in
`lemma8_initial_overlap`, and the `O(log(1/ε))` comparison in `lemma8_time_scaling`. -/

/-- The algorithm record of Theorem 2: a worst-case query function together
with the bounded-error specification flag. -/
structure QuadraticODEAlgorithm where
  /-- Worst-case number of queries to the input oracle at evolution time `T`. -/
  queries : ℝ → ℕ
  /-- The bounded-error specification. -/
  bounded_error : Prop

/-- **Theorem 2 (printed p. 24, proof on p. 27): the exponential lower bound.**

Assume `R ≥ √2`.  Then there is an instance of the quantum quadratic ODE problem (Problem 1)
such that any bounded-error quantum algorithm producing a state approximating `u(T)/‖u(T)‖`
must have worst-case time (query) complexity exponential in `T`: there are constants
`c > 0` and `T₀` with `exp(c T) ≤ queries T` for all `T ≥ T₀`.

The proof composes Lemma 8 (an `ε`-overlap pair whose outputs at time `T = O(log(1/ε))` have
overlap at most `√(3/10)`) with Lemma 7 (`Ω(1/ε)` queries are needed to distinguish states of
overlap `1 - ε`); eliminating `ε = Θ(exp(-T/c₂))` gives the exponential bound.  The
quantitative composition itself is proved in `theorem2_composition`. -/

theorem theorem2_composition (ε T c1 c2 : ℝ) (k : ℕ)
    (hε : 0 < ε) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hT : T ≤ c2 * Real.log (1 / ε))
    (hk : c1 / ε ≤ (k : ℝ)) :
    c1 * Real.exp (T / c2) ≤ (k : ℝ) := by
  have hexp : Real.exp (T / c2) ≤ 1 / ε := by
    calc Real.exp (T / c2) ≤ Real.exp (Real.log (1 / ε)) := by
          apply Real.exp_le_exp.2
          rw [div_le_iff₀ hc2]
          linarith
      _ = 1 / ε := Real.exp_log (by positivity)
  calc c1 * Real.exp (T / c2) ≤ c1 * (1 / ε) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hc1)
    _ = c1 / ε := by ring
    _ ≤ (k : ℝ) := hk

/-- The legacy `theorem2_statement` of the original development of this
material is refuted as stated: the zero-query record with `bounded_error := True`
satisfies the hypotheses for every `R ≥ √2`, while `exp(cT) ≤ 0` is false.
The corrected contract must tie `queries` to an actual state-preparation
semantics. -/
theorem theorem2_statement_refuted :
    ¬ ∀ (Alg : QuadraticODEAlgorithm), Alg.bounded_error →
      ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
        Real.exp (c * T) ≤ (Alg.queries T : ℝ) := by
  intro h
  obtain ⟨c, hc, T₀, hT⟩ := h ⟨fun _ => 0, True⟩ trivial
  have hq : (((⟨fun _ => 0, True⟩ : QuadraticODEAlgorithm).queries) T₀ : ℝ) = 0 := by simp
  have hbound := hT T₀ le_rfl
  rw [hq] at hbound
  have hexp : 0 < Real.exp (c * T₀) := Real.exp_pos _
  linarith

end

end Qatlib.Papers.DissipNonlin20.MainResults.LowerBound
