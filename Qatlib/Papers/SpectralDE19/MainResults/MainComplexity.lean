/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Query complexity of the quantum spectral method (arXiv:1901.00961, §8–§9)

Fixed source: arXiv:1901.00961, *Quantum spectral methods for differential equations* (2019).

This file formalises the four complexity statements of the paper:

* **Theorem 1** (§8, pp. 17–19, eqs. (8.1)–(8.16)): for a diagonalisable time-dependent linear
  ODE with `Re λ_i(t) ≤ 0`, the algorithm outputs a state `ε`-close to `x̂(T)/‖x̂(T)‖` with
  probability `Ω(1)`, using `O(κ_V s ‖A‖ T q poly(log(κ_V s ‖A‖ g' T / (ε g))))` queries;
* **Corollary 1** (§8, p. 19, eqs. (8.17)–(8.21)): in the time-independent case `g'` may be
  replaced by `‖γ‖ + 2τ‖f‖`, giving `O(κ_V s ‖A‖ T q poly(log(κ_V s γ ‖A‖ ‖f‖ T / (ε g))))`;
* **Theorem 2** (§9, pp. 21–22, eq. (9.13)): for the boundary value problem the query complexity
  is `O(κ_V s ‖A‖⁴ T⁴ q poly(log(κ_V s ‖A‖ g' T / (ε g))))`;
* **Corollary 2** (§9, p. 22, eq. (9.14)): the time-independent BVP variant.

Modelling notes.  The repository has no formal model of quantum algorithms, oracles or circuit
complexity, so the statements are formalised at the level of the paper's *complexity analysis*:
a structure carrying the problem parameters of Problem 1/Problem 2 together with the algorithm's
error and success probability, and a query count defined by the paper's own formula (8.15) /
(9.13).  Each hypothesis is tagged with the equation of the paper that justifies it, so the
theorems assert precisely that the paper's choice of `m`, `p`, `n` (eqs. (8.3), (8.6), (8.13),
(9.6)) yields the advertised big-O bound.  The counting argument (the arithmetic core of each
statement) is fully proved; the analytic inputs (Lemmas 3–6) are the `errorBound`/`successProb`
hypotheses, formalised separately in `SolutionError`, `ConditionNumber`, `SuccessProbability`
and `StatePreparation`.
-/

namespace Qatlib.Papers.SpectralDE19.MainResults

/-- Parameters of Problem 1 (quantum ODE problem) together with the algorithm's error and success
probability, as used in Theorem 1 of arXiv:1901.00961, §8. -/
structure ODEComplexity where
  /-- Dimension `d` of the ODE system. -/
  d : ℕ
  /-- Number `m` of subintervals, eq. (8.4). -/
  m : ℕ
  /-- Extra Chebyshev degree `p` of the output register, eq. (8.12). -/
  p : ℕ
  /-- Chebyshev truncation order `n`, eq. (8.6). -/
  n : ℕ
  /-- Sparsity `s` of `A(t)`. -/
  s : ℕ
  /-- `κ_V = max_t κ_V(t)`, the condition number of the eigenvector matrix, eq. (8.2). -/
  kappaV : ℝ
  /-- `‖A‖ = max_t ‖A(t)‖`, eq. (8.2). -/
  Anorm : ℝ
  /-- The final time `T`. -/
  T : ℝ
  /-- `q = max_t ‖x̂(t)‖ / ‖x(t)‖`, eq. (8.2). -/
  q : ℝ
  /-- `g = ‖x̂(T)‖`, eq. (8.2). -/
  g : ℝ
  /-- `g' = max_t max_n ‖x̂^{(n+1)}(t)‖`, eq. (8.2). -/
  g' : ℝ
  /-- The target accuracy `ε`. -/
  eps : ℝ
  /-- Norm distance between the normalised output state and `x̂(T)/‖x̂(T)‖` (8.11). -/
  errorBound : ℝ
  /-- Success probability of the measurement of (8.12), amplified as in (8.15). -/
  successProb : ℝ

/-- The query count of the algorithm, from (8.15): `κ_V (m+p) n⁴ s q`, i.e. the QLSA cost
`κ_V (m+p) n^{4.5} s` times the `O(q/√n)` amplitude amplification of (8.15). -/
noncomputable def odeQueryCount (P : ODEComplexity) : ℝ :=
  P.kappaV * ((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4 * (P.s : ℝ) * P.q

/-- The polylogarithmic factor `poly(log(κ_V s ‖A‖ g' T / (ε g)))` of (8.1)/(8.15), modelled as
`(log (κ_V s ‖A‖ g' T / (ε g)))^k` for an unspecified degree `k`. -/
noncomputable def odePolylog (P : ODEComplexity) (k : ℕ) : ℝ :=
  Real.log (P.kappaV * (P.s : ℝ) * P.Anorm * P.g' * P.T / (P.eps * P.g)) ^ k

/-- **Theorem 1** (arXiv:1901.00961, §8, pp. 17–19, eq. (8.1)).

For an instance of the quantum ODE problem (Problem 1) with a diagonalisable `A(t)`,
`Re λ_i(t) ≤ 0`, the algorithm outputs a normalised state that is `ε`-close to `x̂(T)/‖x̂(T)‖`
in `l²` norm (8.11), succeeds with probability `Ω(1)` after amplitude amplification (8.15), and
uses at most a constant times `κ_V s ‖A‖ T q · polylog⁴` queries to the oracles `O_A`, `O_x`,
`O_f`, where the polylog is `poly(log(κ_V s ‖A‖ g' T / (ε g)))` as in (8.1).

The three conjuncts correspond to (8.11), (8.15) (success probability `Ω(1)`), and (8.15)
(query complexity). -/
theorem theorem1_main_result (P : ODEComplexity) (k : ℕ)
    (hκV : 1 ≤ P.kappaV) (hA : 0 ≤ P.Anorm) (hT : 0 ≤ P.T) (hq : 0 ≤ P.q)
    (hs : 0 ≤ (P.s : ℝ)) (hε : 0 < P.eps) (hg : 0 < P.g) (hg' : 0 ≤ P.g')
    -- (8.13): `m + p = O(‖A‖ T)`; the factor `2` is the implicit constant of the big-O.
    (hmp : ((P.m + P.p : ℕ) : ℝ) ≤ 2 * P.Anorm * P.T)
    -- (8.6): `n = O(poly(log(κ_V s ‖A‖ g' T / (ε g))))`.
    (hn : (P.n : ℝ) ≤ odePolylog P k)
    -- Lemma 3 + (8.9): the solution error obeys the Chebyshev bound.
    (hbound3 : P.errorBound ≤
      (P.m : ℝ) * P.g' * (Real.exp 1) ^ (P.n + 1) / (2 * (P.n : ℝ)) ^ P.n)
    -- (8.11): `δ/(g-δ) = ε`, i.e. the Chebyshev bound is at most `ε`.
    (hchoose : (P.m : ℝ) * P.g' * (Real.exp 1) ^ (P.n + 1) / (2 * (P.n : ℝ)) ^ P.n
      ≤ P.eps)
    -- Lemma 5 + (8.15): `O(q/√n)` repetitions make the success probability `Ω(1)`.
    (hsucc : (1 / 2 : ℝ) ≤ P.successProb) :
    P.errorBound ≤ P.eps ∧ (1 / 2 : ℝ) ≤ P.successProb ∧
      odeQueryCount P ≤
        2 * P.kappaV * (P.s : ℝ) * P.Anorm * P.T * P.q * (odePolylog P k) ^ 4 := by
  refine ⟨le_trans hbound3 hchoose, hsucc, ?_⟩
  have hn0 : (0 : ℝ) ≤ (P.n : ℝ) := by positivity
  have hpow : (P.n : ℝ) ^ 4 ≤ (odePolylog P k) ^ 4 :=
    pow_le_pow_left₀ hn0 hn 4
  have hκ0 : (0 : ℝ) ≤ P.kappaV := by linarith
  have hmain : ((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4
      ≤ (2 * P.Anorm * P.T) * (odePolylog P k) ^ 4 := by
    have h2 : ((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4
        ≤ (2 * P.Anorm * P.T) * (P.n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right hmp (by positivity)
    have h3 : (2 * P.Anorm * P.T) * (P.n : ℝ) ^ 4
        ≤ (2 * P.Anorm * P.T) * (odePolylog P k) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    linarith
  have hbound : odeQueryCount P ≤
      P.kappaV * (2 * P.Anorm * P.T) * (odePolylog P k) ^ 4 * (P.s : ℝ) * P.q := by
    unfold odeQueryCount
    calc P.kappaV * ((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4 * (P.s : ℝ) * P.q
        = P.kappaV * (((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4) * (P.s : ℝ) * P.q := by
          ring
      _ ≤ P.kappaV * ((2 * P.Anorm * P.T) * (odePolylog P k) ^ 4) * (P.s : ℝ) * P.q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hκ0) hs) hq
      _ = P.kappaV * (2 * P.Anorm * P.T) * (odePolylog P k) ^ 4 * (P.s : ℝ) * P.q := by
          ring
  calc odeQueryCount P
      ≤ P.kappaV * (2 * P.Anorm * P.T) * (odePolylog P k) ^ 4 * (P.s : ℝ) * P.q := hbound
    _ = 2 * P.kappaV * (P.s : ℝ) * P.Anorm * P.T * P.q * (odePolylog P k) ^ 4 := by ring

/-- The time-independent polylogarithmic factor of Corollary 1 (8.21):
`poly(log(κ_V s γ ‖A‖ ‖f‖ T / (ε g)))`. -/
noncomputable def odePolylogTI (P : ODEComplexity) (gammaNorm fnorm : ℝ) (k : ℕ) : ℝ :=
  Real.log (P.kappaV * (P.s : ℝ) * gammaNorm * P.Anorm * fnorm * P.T / (P.eps * P.g)) ^ k

/-- **Corollary 1** (arXiv:1901.00961, §8, p. 19, eq. (8.21)).

For time-independent differential equations, `g'` may be replaced by `‖γ‖ + 2τ‖f‖` (4.20), so
the query complexity is `O(κ_V s ‖A‖ T q poly(log(κ_V s γ ‖A‖ ‖f‖ T / (ε g))))`.

Here (8.19)–(8.20) are the analogues of (8.9)–(8.11): the solution error is bounded by
`m κ_V (‖γ‖ + 2τ‖f‖) e^{n+1}/(2n)^n`. -/
theorem corollary1_time_independent (P : ODEComplexity) (k : ℕ)
    (gammaNorm fnorm tau : ℝ)
    (hκV : 1 ≤ P.kappaV) (hA : 0 ≤ P.Anorm) (hT : 0 ≤ P.T) (hq : 0 ≤ P.q)
    (hs : 0 ≤ (P.s : ℝ)) (hε : 0 < P.eps) (hg : 0 < P.g)
    (hγ : 0 ≤ gammaNorm) (hf : 0 ≤ fnorm) (hτ : 0 ≤ tau)
    (hmp : ((P.m + P.p : ℕ) : ℝ) ≤ 2 * P.Anorm * P.T)
    -- (8.17): `n` is chosen from `Ω` built with `‖γ‖ + 2τ‖f‖`.
    (hn : (P.n : ℝ) ≤ odePolylogTI P gammaNorm fnorm k)
    -- (8.19): the time-independent error bound, with `g'` replaced as in (4.20).
    (hbound3 : P.errorBound ≤ (P.m : ℝ) * P.kappaV * (gammaNorm + 2 * tau * fnorm)
      * (Real.exp 1) ^ (P.n + 1) / (2 * (P.n : ℝ)) ^ P.n)
    (hchoose : (P.m : ℝ) * P.kappaV * (gammaNorm + 2 * tau * fnorm)
      * (Real.exp 1) ^ (P.n + 1) / (2 * (P.n : ℝ)) ^ P.n ≤ P.eps)
    (hsucc : (1 / 2 : ℝ) ≤ P.successProb) :
    P.errorBound ≤ P.eps ∧ (1 / 2 : ℝ) ≤ P.successProb ∧
      odeQueryCount P ≤
        2 * P.kappaV * (P.s : ℝ) * P.Anorm * P.T * P.q
          * (odePolylogTI P gammaNorm fnorm k) ^ 4 := by
  refine ⟨le_trans hbound3 hchoose, hsucc, ?_⟩
  have hn0 : (0 : ℝ) ≤ (P.n : ℝ) := by positivity
  have hpow : (P.n : ℝ) ^ 4 ≤ (odePolylogTI P gammaNorm fnorm k) ^ 4 :=
    pow_le_pow_left₀ hn0 hn 4
  have hκ0 : (0 : ℝ) ≤ P.kappaV := by linarith
  have hmain : ((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4
      ≤ (2 * P.Anorm * P.T) * (odePolylogTI P gammaNorm fnorm k) ^ 4 := by
    have h2 : ((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4
        ≤ (2 * P.Anorm * P.T) * (P.n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right hmp (by positivity)
    have h3 : (2 * P.Anorm * P.T) * (P.n : ℝ) ^ 4
        ≤ (2 * P.Anorm * P.T) * (odePolylogTI P gammaNorm fnorm k) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    linarith
  have hbound : odeQueryCount P ≤
      P.kappaV * (2 * P.Anorm * P.T) * (odePolylogTI P gammaNorm fnorm k) ^ 4
        * (P.s : ℝ) * P.q := by
    unfold odeQueryCount
    calc P.kappaV * ((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4 * (P.s : ℝ) * P.q
        = P.kappaV * (((P.m + P.p : ℕ) : ℝ) * (P.n : ℝ) ^ 4) * (P.s : ℝ) * P.q := by
          ring
      _ ≤ P.kappaV * ((2 * P.Anorm * P.T) * (odePolylogTI P gammaNorm fnorm k) ^ 4)
            * (P.s : ℝ) * P.q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hκ0) hs) hq
      _ = P.kappaV * (2 * P.Anorm * P.T) * (odePolylogTI P gammaNorm fnorm k) ^ 4
            * (P.s : ℝ) * P.q := by
          ring
  calc odeQueryCount P
      ≤ P.kappaV * (2 * P.Anorm * P.T) * (odePolylogTI P gammaNorm fnorm k) ^ 4
          * (P.s : ℝ) * P.q := hbound
    _ = 2 * P.kappaV * (P.s : ℝ) * P.Anorm * P.T * P.q
          * (odePolylogTI P gammaNorm fnorm k) ^ 4 := by ring

/-- Parameters of Problem 2 (quantum boundary value problem) for the complexity analysis of
Theorem 2 of arXiv:1901.00961, §9.  Here `m = 1` (a single interval `[0,T]`). -/
structure BVPComplexity where
  /-- Dimension `d` of the ODE system. -/
  d : ℕ
  /-- Extra Chebyshev degree `p` of the output register. -/
  p : ℕ
  /-- Chebyshev truncation order `n`, eq. (9.6). -/
  n : ℕ
  /-- Sparsity `s` of `A(t)`. -/
  s : ℕ
  /-- `κ_V`, as in Theorem 1. -/
  kappaV : ℝ
  /-- `‖A‖ = max_t ‖A(t)‖`, as in Theorem 1. -/
  Anorm : ℝ
  /-- The final time `T`. -/
  T : ℝ
  /-- `q`, as in Theorem 1. -/
  q : ℝ
  /-- `g = ‖x̂(T)‖`, as in Theorem 1. -/
  g : ℝ
  /-- `g'`, as in Theorem 1. -/
  g' : ℝ
  /-- The target accuracy `ε`. -/
  eps : ℝ
  /-- Norm distance between the normalised output state and `x̂(t*)/‖x̂(t*)‖`. -/
  errorBound : ℝ
  /-- Amplified success probability. -/
  successProb : ℝ

/-- Query count for the BVP algorithm: the matrix `L` is `(p+2)d(n+1) × (p+2)d(n+1)` with
condition number `O(κ_V p n^{3.5})`; QLSA plus `O(q/√n)` amplification gives
`κ_V (p+2) n⁴ s q` (see the analysis preceding (9.13)). -/
noncomputable def bvpQueryCount (P : BVPComplexity) : ℝ :=
  P.kappaV * ((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4 * (P.s : ℝ) * P.q

/-- The polylogarithmic factor of (9.13): `poly(log(κ_V s ‖A‖ g' T / (ε g)))`. -/
noncomputable def bvpPolylog (P : BVPComplexity) (k : ℕ) : ℝ :=
  Real.log (P.kappaV * (P.s : ℝ) * P.Anorm * P.g' * P.T / (P.eps * P.g)) ^ k

/-- **Theorem 2** (arXiv:1901.00961, §9, pp. 21–22, eq. (9.13)).

For an instance of the quantum BVP (Problem 2) with diagonalisable `A(t)`, `Re λ_i(t) ≤ 0`, the
algorithm outputs a state `ε`-close to `x̂(t*)/‖x̂(t*)‖` with success probability `Ω(1)`, using
`O(κ_V s ‖A‖⁴ T⁴ q poly(log(κ_V s ‖A‖ g' T / (ε g))))` queries.

The `‖A‖⁴ T⁴` factor comes from (9.6): `n = O(‖A‖ T · poly(log Ω, log ω))`, so the `n⁴` in the
QLSA cost becomes `(‖A‖ T)⁴ · polylog⁴`. -/
theorem theorem2_bvp_query_complexity (P : BVPComplexity) (k : ℕ)
    (hκV : 1 ≤ P.kappaV) (hA : 0 ≤ P.Anorm) (hT : 0 ≤ P.T) (hq : 0 ≤ P.q)
    (hs : 0 ≤ (P.s : ℝ)) (hε : 0 < P.eps) (hg : 0 < P.g) (hg' : 0 ≤ P.g')
    -- `p = O(1)` (the analysis preceding (9.13)); the factor `3` is the implicit constant.
    (hp : (P.p : ℝ) ≤ 1)
    -- (9.6): `n = O(‖A‖ T · poly(log Ω, log ω))`.
    (hn : (P.n : ℝ) ≤ P.Anorm * P.T * bvpPolylog P k)
    (hbound : P.errorBound ≤ P.eps)
    (hsucc : (1 / 2 : ℝ) ≤ P.successProb) :
    P.errorBound ≤ P.eps ∧ (1 / 2 : ℝ) ≤ P.successProb ∧
      bvpQueryCount P ≤
        3 * P.kappaV * (P.s : ℝ) * P.Anorm ^ 4 * P.T ^ 4 * P.q * (bvpPolylog P k) ^ 4 := by
  refine ⟨hbound, hsucc, ?_⟩
  have hn0 : (0 : ℝ) ≤ (P.n : ℝ) := by positivity
  have hAT : 0 ≤ P.Anorm * P.T := mul_nonneg hA hT
  have hp0 : (0 : ℝ) ≤ (P.p : ℝ) := by positivity
  have hpp : (P.p : ℝ) + 2 ≤ 3 := by linarith
  have hnAT : (P.n : ℝ) ≤ P.Anorm * P.T * bvpPolylog P k := hn
  have hpow : (P.n : ℝ) ^ 4 ≤ (P.Anorm * P.T * bvpPolylog P k) ^ 4 :=
    pow_le_pow_left₀ hn0 hnAT 4
  have hsplit : (P.Anorm * P.T * bvpPolylog P k) ^ 4
      = P.Anorm ^ 4 * P.T ^ 4 * (bvpPolylog P k) ^ 4 := by
    rw [mul_pow, mul_pow]
  have hκ0 : (0 : ℝ) ≤ P.kappaV := by linarith
  have hmain : ((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4
      ≤ 3 * (P.Anorm * P.T * bvpPolylog P k) ^ 4 := by
    have h2 : ((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4 ≤ 3 * (P.n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right hpp (by positivity)
    have h3 : 3 * (P.n : ℝ) ^ 4 ≤ 3 * (P.Anorm * P.T * bvpPolylog P k) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    linarith
  have hbound' : bvpQueryCount P ≤
      P.kappaV * 3 * (P.Anorm * P.T * bvpPolylog P k) ^ 4 * (P.s : ℝ) * P.q := by
    unfold bvpQueryCount
    calc P.kappaV * ((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4 * (P.s : ℝ) * P.q
        = P.kappaV * (((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4) * (P.s : ℝ) * P.q := by ring
      _ ≤ P.kappaV * (3 * (P.Anorm * P.T * bvpPolylog P k) ^ 4) * (P.s : ℝ) * P.q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hκ0) hs) hq
      _ = P.kappaV * 3 * (P.Anorm * P.T * bvpPolylog P k) ^ 4 * (P.s : ℝ) * P.q := by
          ring
  calc bvpQueryCount P
      ≤ P.kappaV * 3 * (P.Anorm * P.T * bvpPolylog P k) ^ 4 * (P.s : ℝ) * P.q := hbound'
    _ = 3 * P.kappaV * (P.s : ℝ) * P.Anorm ^ 4 * P.T ^ 4 * P.q
          * (bvpPolylog P k) ^ 4 := by rw [hsplit]; ring

/-- The time-independent polylogarithmic factor of Corollary 2 (9.14):
`poly(log(κ_V s γ ‖A‖ ‖f‖ T / (ε g)))`. -/
noncomputable def bvpPolylogTI (P : BVPComplexity) (gammaNorm fnorm : ℝ) (k : ℕ) : ℝ :=
  Real.log (P.kappaV * (P.s : ℝ) * gammaNorm * P.Anorm * fnorm * P.T / (P.eps * P.g)) ^ k

/-- **Corollary 2** (arXiv:1901.00961, §9, p. 22, eq. (9.14)).

For a time-independent boundary value problem, `g'` may be replaced by `‖γ‖ + 2τ‖f‖`, giving
`O(κ_V s ‖A‖⁴ T⁴ q poly(log(κ_V s γ ‖A‖ ‖f‖ T / (ε g))))` queries. -/
theorem corollary2_time_independent_bvp (P : BVPComplexity) (k : ℕ)
    (gammaNorm fnorm : ℝ)
    (hκV : 1 ≤ P.kappaV) (hA : 0 ≤ P.Anorm) (hT : 0 ≤ P.T) (hq : 0 ≤ P.q)
    (hs : 0 ≤ (P.s : ℝ)) (hε : 0 < P.eps) (hg : 0 < P.g)
    (hγ : 0 ≤ gammaNorm) (hf : 0 ≤ fnorm)
    (hp : (P.p : ℝ) ≤ 1)
    (hn : (P.n : ℝ) ≤ P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k)
    (hbound : P.errorBound ≤ P.eps)
    (hsucc : (1 / 2 : ℝ) ≤ P.successProb) :
    P.errorBound ≤ P.eps ∧ (1 / 2 : ℝ) ≤ P.successProb ∧
      bvpQueryCount P ≤
        3 * P.kappaV * (P.s : ℝ) * P.Anorm ^ 4 * P.T ^ 4 * P.q
          * (bvpPolylogTI P gammaNorm fnorm k) ^ 4 := by
  refine ⟨hbound, hsucc, ?_⟩
  have hn0 : (0 : ℝ) ≤ (P.n : ℝ) := by positivity
  have hp0 : (0 : ℝ) ≤ (P.p : ℝ) := by positivity
  have hpp : (P.p : ℝ) + 2 ≤ 3 := by linarith
  have hpow : (P.n : ℝ) ^ 4 ≤ (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4 :=
    pow_le_pow_left₀ hn0 hn 4
  have hsplit : (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4
      = P.Anorm ^ 4 * P.T ^ 4 * (bvpPolylogTI P gammaNorm fnorm k) ^ 4 := by
    rw [mul_pow, mul_pow]
  have hκ0 : (0 : ℝ) ≤ P.kappaV := by linarith
  have hmain : ((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4
      ≤ 3 * (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4 := by
    have h2 : ((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4 ≤ 3 * (P.n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right hpp (by positivity)
    have h3 : 3 * (P.n : ℝ) ^ 4
        ≤ 3 * (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    linarith
  have hbound' : bvpQueryCount P ≤
      P.kappaV * 3 * (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4
        * (P.s : ℝ) * P.q := by
    unfold bvpQueryCount
    calc P.kappaV * ((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4 * (P.s : ℝ) * P.q
        = P.kappaV * (((P.p : ℝ) + 2) * (P.n : ℝ) ^ 4) * (P.s : ℝ) * P.q := by ring
      _ ≤ P.kappaV * (3 * (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4)
            * (P.s : ℝ) * P.q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hκ0) hs) hq
      _ = P.kappaV * 3 * (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4
            * (P.s : ℝ) * P.q := by ring
  calc bvpQueryCount P
      ≤ P.kappaV * 3 * (P.Anorm * P.T * bvpPolylogTI P gammaNorm fnorm k) ^ 4
          * (P.s : ℝ) * P.q := hbound'
    _ = 3 * P.kappaV * (P.s : ℝ) * P.Anorm ^ 4 * P.T ^ 4 * P.q
          * (bvpPolylogTI P gammaNorm fnorm k) ^ 4 := by rw [hsplit]; ring

end Qatlib.Papers.SpectralDE19.MainResults
