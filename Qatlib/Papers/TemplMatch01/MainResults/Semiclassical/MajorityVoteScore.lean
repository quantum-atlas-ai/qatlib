/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Semiclassical majority-vote score

Defines the majority-vote outcome probability `majorityProbZero` and its phase-averaged score
`majorityVoteScore` in the template-matching setting of [SasakiCarliniJozsa2001]. Products
representing odd and even double factorials evaluate the required even-power trigonometric
integrals.

The theorem `majorityVoteScore_eq_closedForm` expresses the score as one half plus a finite
coefficient sum multiplied by `cos θ`, and `mvClosedForm_one` evaluates the one-copy case.

## Main statements

* `W_closed`: evaluates the integral of even powers of sine and cosine.
* `majorityVoteScore_eq_closedForm`: identifies the integral score with its finite-sum
  expression.
* `mvClosedForm_one`: computes the one-copy score expression.

## References

* [Sasaki et al., 2001][SasakiCarliniJozsa2001]
-/

namespace Qatlib.Papers.TemplMatch01.MainResults.Semiclassical

open Qatlib.Foundations.PureStateMath
open Matrix MeasureTheory BigOperators
open scoped ComplexOrder BigOperators MatrixOrder

set_option autoImplicit false

open intervalIntegral

/-- The real product of the first `n` positive odd integers, with value one at `n = 0`. -/
noncomputable def dfOdd (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (2*(i:ℝ)+1)

/-- The real product of the first `n` positive even integers, with value one at `n = 0`. -/
noncomputable def dfEven (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (2*(i:ℝ)+2)

/-- The empty odd-integer product equals one. -/
@[simp] lemma dfOdd_zero : dfOdd 0 = 1 := by simp [dfOdd]

/-- The empty even-integer product equals one. -/
@[simp] lemma dfEven_zero : dfEven 0 = 1 := by simp [dfEven]

/-- Extending the odd-integer product from `n` to `n + 1` multiplies it by `2 * n + 1`. -/
lemma dfOdd_succ (n : ℕ) : dfOdd (n+1) = (2*(n:ℝ)+1) * dfOdd n := by
  rw [dfOdd, Finset.prod_range_succ, dfOdd]; ring

/-- Extending the even-integer product from `n` to `n + 1` multiplies it by `2 * n + 2`. -/
lemma dfEven_succ (n : ℕ) : dfEven (n+1) = (2*(n:ℝ)+2) * dfEven n := by
  rw [dfEven, Finset.prod_range_succ, dfEven]; ring

/-- Identifies `dfEven n` with the real cast of the double factorial of `2 * n`. -/
lemma dfEven_eq (n : ℕ) : dfEven n = (Nat.doubleFactorial (2*n) : ℝ) := by
  rw [dfEven, Nat.doubleFactorial_eq_prod_even, Nat.cast_prod]
  apply Finset.prod_congr rfl; intro x _; push_cast; ring

/-- Identifies `dfOdd n` with the real cast of the double factorial of the natural number `2 * n
- 1`. -/
lemma dfOdd_eq : ∀ n : ℕ, dfOdd n = (Nat.doubleFactorial (2*n-1) : ℝ)
  | 0 => by simp
  | 1 => by simp [dfOdd]
  | (k+2) => by
      have ih := dfOdd_eq (k+1)
      have hstep : dfOdd (k+2) = (2*(k:ℝ)+3) * dfOdd (k+1) := by
        rw [show k+2 = (k+1)+1 by ring, dfOdd_succ]; push_cast; ring
      have hd : (Nat.doubleFactorial (2*(k+2)-1) : ℝ)
          = (2*(k:ℝ)+3) * (Nat.doubleFactorial (2*(k+1)-1) : ℝ) := by
        have hone : (2*(k+1)-1)+2 = 2*k+3 := by omega
        have hnat : Nat.doubleFactorial (2*(k+2)-1)
            = (2*k+3) * Nat.doubleFactorial (2*(k+1)-1) := by
          rw [show 2*(k+2)-1 = (2*(k+1)-1)+2 by omega, Nat.doubleFactorial_add_two, hone]
        rw [hnat]; push_cast; ring
      rw [hstep, ih, hd]

/-- The integral of `sin x ^ (2 * p) * cos x ^ (2 * q)` over `[0, π]`. -/
noncomputable def W (p q : ℕ) : ℝ := ∫ x in (0:ℝ)..Real.pi, Real.sin x ^ (2*p) * Real.cos x ^ (2*q)

/-- Evaluates `W 0 q` as `π * dfOdd q / dfEven q`. -/
lemma W_zero (q : ℕ) : W 0 q = Real.pi * dfOdd q / dfEven q := by
  induction q with
  | zero => simp [W]
  | succ q ih =>
      have h := integral_cos_pow (a := (0:ℝ)) (b := Real.pi) (n := 2*q)
      simp only [Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero, mul_zero,
        sub_zero, zero_div, zero_add] at h
      have h2 : W 0 (q+1) = (2*(q:ℝ)+1)/(2*(q:ℝ)+2) * W 0 q := by
        have hL : W 0 (q+1) = ∫ x in (0:ℝ)..Real.pi, Real.cos x ^ (2*q+2) := by
          simp [W, show 2*(q+1) = 2*q+2 by ring]
        have hR : W 0 q = ∫ x in (0:ℝ)..Real.pi, Real.cos x ^ (2*q) := by simp [W]
        rw [hL, hR, h]
        push_cast; ring
      rw [h2, ih, dfOdd_succ, dfEven_succ]
      have hq2 : (2*(q:ℝ)+2) ≠ 0 := by positivity
      have hq1 : (2*(q:ℝ)+1) ≠ 0 := by positivity
      field_simp

open MeasureTheory in

/-- For `p ≥ 1`, relates `W p q` to `W (p - 1) (q + 1)` through the factors `2 * q + 1` and `2 *
p - 1`. -/
lemma W_rec (p q : ℕ) (hp : 1 ≤ p) :
    (2*(q:ℝ)+1) * W p q = (2*(p:ℝ)-1) * W (p-1) (q+1) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p-1, by omega⟩
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) Real.pi,
      HasDerivAt (fun y => Real.sin y ^ (2*k+1) * Real.cos y ^ (2*q+1))
        ((2*(k:ℝ)+1) * (Real.sin x ^ (2*k) * Real.cos x ^ (2*(q+1)))
          - (2*(q:ℝ)+1) * (Real.sin x ^ (2*(k+1)) * Real.cos x ^ (2*q))) x := by
    intro x _
    have h3 := ((Real.hasDerivAt_sin x).pow (2*k+1)).mul
      ((Real.hasDerivAt_cos x).pow (2*q+1))
    convert! h3 using 1
    (try simp only [Pi.pow_apply])
    rw [show 2*k+1-1 = 2*k by omega, show 2*q+1-1 = 2*q by omega]
    have hs : (Real.sin x)^(2*k+1) = (Real.sin x)^(2*k) * Real.sin x := by ring
    have hc : (Real.cos x)^(2*q+1) = (Real.cos x)^(2*q) * Real.cos x := by ring
    have hs2 : (Real.sin x)^(2*(k+1)) = (Real.sin x)^(2*k) * Real.sin x * Real.sin x := by
      rw [show 2*(k+1) = 2*k+2 by ring, pow_add]; ring
    have hc2 : (Real.cos x)^(2*(q+1)) = (Real.cos x)^(2*q) * Real.cos x * Real.cos x := by
      rw [show 2*(q+1) = 2*q+2 by ring, pow_add]; ring
    rw [hs, hc, hs2, hc2]
    push_cast
    ring
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := Real.pi)
    hderiv (by apply Continuous.intervalIntegrable; fun_prop)
  have hzero : ∫ x in (0:ℝ)..Real.pi,
      ((2*(k:ℝ)+1) * (Real.sin x ^ (2*k) * Real.cos x ^ (2*(q+1)))
        - (2*(q:ℝ)+1) * (Real.sin x ^ (2*(k+1)) * Real.cos x ^ (2*q))) = 0 := by
    rw [hF]; simp [Real.sin_pi, Real.sin_zero]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hzero
  have hpk : (2*((k+1:ℕ):ℝ)-1) = (2*(k:ℝ)+1) := by push_cast; ring
  rw [show (k+1)-1 = k from by omega]
  rw [hpk, W, W]
  linarith [hzero]

/-- Evaluates `W p q` as `π * dfOdd p * dfOdd q / dfEven (p + q)`. -/
lemma W_closed (p q : ℕ) : W p q = Real.pi * dfOdd p * dfOdd q / dfEven (p+q) := by
  induction p generalizing q with
  | zero => simpa using W_zero q
  | succ p ih =>
      have h2p : (2*((p+1:ℕ):ℝ)-1) = (2*(p:ℝ)+1) := by push_cast; ring
      have hrec := W_rec (p+1) q (by omega)
      rw [h2p, show p+1-1 = p from by omega] at hrec
      have ih2 := ih (q+1)
      rw [ih2, dfOdd_succ] at hrec
      rw [show p + (q+1) = (p+q+1) from by omega] at hrec
      have hq : (2*(q:ℝ)+1) ≠ 0 := by positivity
      have step : W (p+1) q
          = (2*(p:ℝ)+1) * (Real.pi * dfOdd p * ((2*(q:ℝ)+1)*dfOdd q) / dfEven (p+q+1))
              / (2*(q:ℝ)+1) := by
        rw [eq_div_iff hq, mul_comm]
        exact hrec
      rw [step, dfOdd_succ, show p+1+q = p+q+1 from by omega]
      field_simp

/-- Evaluates the integral defining `W p q` with an additional factor `cos (2 * x)` using
double-factorial products and the ratio `(q - p) / (p + q + 1)`. -/
lemma Jint (p q : ℕ) :
    ∫ x in (0:ℝ)..Real.pi, Real.sin x ^ (2*p) * Real.cos x ^ (2*q) * Real.cos (2*x)
      = Real.pi * dfOdd p * dfOdd q / dfEven (p+q) * (((q:ℝ)-(p:ℝ))/(((p+q:ℕ):ℝ)+1)) := by
  have hcos2 : ∀ x : ℝ, Real.cos (2*x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by
    intro x; rw [Real.cos_two_mul, Real.sin_sq]; ring
  have hsplit : ∀ x : ℝ, Real.sin x ^ (2*p) * Real.cos x ^ (2*q) * Real.cos (2*x)
      = Real.sin x ^ (2*p) * Real.cos x ^ (2*(q+1))
        - Real.sin x ^ (2*(p+1)) * Real.cos x ^ (2*q) := by
    intro x
    rw [hcos2]
    have hc : Real.cos x ^ (2*(q+1)) = Real.cos x ^ (2*q) * Real.cos x ^ 2 := by
      rw [show 2*(q+1) = 2*q+2 by ring, pow_add]
    have hs : Real.sin x ^ (2*(p+1)) = Real.sin x ^ (2*p) * Real.sin x ^ 2 := by
      rw [show 2*(p+1) = 2*p+2 by ring, pow_add]
    rw [hc, hs]; ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  change W p (q+1) - W (p+1) q
      = Real.pi * dfOdd p * dfOdd q / dfEven (p+q) * (((q:ℝ)-(p:ℝ))/(((p+q:ℕ):ℝ)+1))
  rw [W_closed p (q+1), W_closed (p+1) q, dfOdd_succ (q), dfOdd_succ p]
  rw [show p+(q+1) = p+q+1 from by omega, show p+1+q = p+q+1 from by omega]
  rw [show p+q+1 = (p+q)+1 from by omega, dfEven_succ]
  have hpq : ((p+q:ℕ):ℝ) + 1 = (p:ℝ)+(q:ℝ)+1 := by push_cast; ring
  rw [hpq]
  field_simp
  push_cast
  ring

/-- Evaluates the normalized phase integral of the even half-angle powers multiplied by `cos φ`. -/
lemma Jint2 (p q : ℕ) :
    (1/(2*Real.pi)) * ∫ φ in (0:ℝ)..(2*Real.pi),
        Real.sin (φ/2) ^ (2*p) * Real.cos (φ/2) ^ (2*q) * Real.cos φ
      = dfOdd p * dfOdd q / dfEven (p+q) * (((q:ℝ)-(p:ℝ))/(((p+q:ℕ):ℝ)+1)) := by
  have h := integral_comp_div (f := fun x => Real.sin x ^ (2*p) * Real.cos x ^ (2*q) * Real.cos (2*x))
    (a := (0:ℝ)) (b := (2*Real.pi)) (c := 2) (by norm_num)
  simp only [zero_div, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0), smul_eq_mul] at h
  rw [h, show (2*Real.pi)/2 = Real.pi by ring, Jint]
  field_simp

/-- The binomial probability sum over `k ≤ N / 2` for outcome zero in the majority-vote rule,
including the tie when `N` is even. -/
noncomputable def majorityProbZero (N : ℕ) (φ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N / 2 + 1), (Nat.choose N k : ℝ) *
    (Real.sin (φ / 2)) ^ (2 * k) * (Real.cos (φ / 2)) ^ (2 * (N - k))

/-- The uniform phase average of the two template fidelities weighted by the majority-vote
outcome probabilities. -/
noncomputable def majorityVoteScore (N : ℕ) (θ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
    (majorityProbZero N φ * Real.cos ((φ - θ) / 2) ^ 2
      + (1 - majorityProbZero N φ) * Real.sin ((φ + θ) / 2) ^ 2)

/-- The real double-factorial ratio `(2 * k + 1)!! / (2 * k + 1)` used in the score
coefficients. -/
noncomputable def oddDFact (k : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * k + 1) : ℝ) / (2 * (k : ℝ) + 1)

/-- The binomial and double-factorial coefficient of the `k`th contribution to the majority-vote
score. -/
noncomputable def mvCoefficient (N k : ℕ) : ℝ :=
  (Nat.choose N k : ℝ) * oddDFact k * oddDFact (N - k) /
    (Nat.doubleFactorial (2 * N) : ℝ) * ((N : ℝ) - 2 * (k : ℝ)) / ((N : ℝ) + 1)

/-- The expression one half plus `cos θ` times the sum of `mvCoefficient N k` over `k ≤ N / 2`. -/
noncomputable def mvClosedForm (N : ℕ) (θ : ℝ) : ℝ :=
  1 / 2 + (∑ k ∈ Finset.range (N / 2 + 1), mvCoefficient N k) * Real.cos θ

/-- The double-factorial ratio `oddDFact k` equals the product `dfOdd k`. -/
lemma oddDFact_eq_dfOdd (k : ℕ) : oddDFact k = dfOdd k := by
  cases k with
  | zero => simp [oddDFact, dfOdd]
  | succ k =>
      rw [oddDFact, dfOdd_eq]
      rw [show 2*(k+1)+1 = (2*(k+1)-1)+2 from by omega, Nat.doubleFactorial_add_two]
      have hm : (2*(k+1)-1)+2 = 2*(k+1)+1 := by omega
      rw [hm]
      have hden : ((2*(k+1)+1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp

/-- The majority-vote outcome probability is a continuous function of the phase. -/
lemma continuous_majorityProbZero (N : ℕ) : Continuous (majorityProbZero N) := by
  unfold majorityProbZero
  fun_prop

/-- Expresses the square of the half-angle cosine as `(1 + cos x) / 2`. -/
lemma cos_sq_half (x : ℝ) : Real.cos (x/2)^2 = (1 + Real.cos x)/2 := by
  have h := Real.cos_two_mul (x/2)
  rw [show 2*(x/2) = x by ring] at h
  linarith

/-- Expresses the square of the half-angle sine as `(1 - cos x) / 2`. -/
lemma sin_sq_half (x : ℝ) : Real.sin (x/2)^2 = (1 - Real.cos x)/2 := by
  have h := Real.cos_two_mul (x/2)
  rw [show 2*(x/2) = x by ring] at h
  have h2 := Real.sin_sq (x/2)
  linarith

/-- Rewrites the majority-vote score integrand into a constant term and cosine contributions
involving the outcome probability. -/
lemma pointwise (N : ℕ) (θ φ : ℝ) :
    majorityProbZero N φ * Real.cos ((φ-θ)/2)^2
      + (1 - majorityProbZero N φ) * Real.sin ((φ+θ)/2)^2
    = 1/2 + majorityProbZero N φ * Real.cos φ * Real.cos θ
      - (1/2) * Real.cos (φ+θ) := by
  rw [cos_sq_half, sin_sq_half, Real.cos_sub, Real.cos_add]; ring

/-- The normalized phase integral of `majorityProbZero N φ * cos φ` equals the finite sum of
majority-vote coefficients. -/
lemma hsum (N : ℕ) :
    (1/(2*Real.pi)) * ∫ φ in (0:ℝ)..(2*Real.pi), majorityProbZero N φ * Real.cos φ
      = ∑ k ∈ Finset.range (N/2+1), mvCoefficient N k := by
  have hpull : ∫ φ in (0:ℝ)..(2*Real.pi), majorityProbZero N φ * Real.cos φ
      = ∑ k ∈ Finset.range (N/2+1), (Nat.choose N k : ℝ) *
          ∫ φ in (0:ℝ)..(2*Real.pi),
            Real.sin (φ/2)^(2*k) * Real.cos (φ/2)^(2*(N-k)) * Real.cos φ := by
    simp only [majorityProbZero]
    simp_rw [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum (fun k hk =>
      (by fun_prop : Continuous (fun φ : ℝ =>
        (Nat.choose N k : ℝ) * Real.sin (φ/2)^(2*k) * Real.cos (φ/2)^(2*(N-k)) * Real.cos φ)).intervalIntegrable 0 (2*Real.pi))]
    apply Finset.sum_congr rfl; intro k hk
    rw [show (fun φ => (Nat.choose N k : ℝ) * Real.sin (φ/2)^(2*k) * Real.cos (φ/2)^(2*(N-k)) * Real.cos φ)
          = (fun φ => (Nat.choose N k : ℝ) *
              (Real.sin (φ/2)^(2*k) * Real.cos (φ/2)^(2*(N-k)) * Real.cos φ)) from by
      ext; ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hpull, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  have hkN : k ≤ N := by
    have := Finset.mem_range.mp hk; omega
  rw [show (1/(2*Real.pi)) * ((Nat.choose N k : ℝ) * ∫ φ in (0:ℝ)..(2*Real.pi),
         Real.sin (φ/2)^(2*k) * Real.cos (φ/2)^(2*(N-k)) * Real.cos φ)
        = (Nat.choose N k : ℝ) * ((1/(2*Real.pi)) * ∫ φ in (0:ℝ)..(2*Real.pi),
         Real.sin (φ/2)^(2*k) * Real.cos (φ/2)^(2*(N-k)) * Real.cos φ) from by ring]
  rw [Jint2 k (N-k), mvCoefficient, oddDFact_eq_dfOdd, oddDFact_eq_dfOdd, ← dfEven_eq N]
  have hk1 : k + (N-k) = N := by omega
  have hk2 : ((N-k:ℕ):ℝ) = (N:ℝ)-(k:ℝ) := Nat.cast_sub hkN
  rw [hk1, hk2]
  ring

/-- The phase-averaged majority-vote score equals `mvClosedForm N θ` for every number of copies
and template angle. See [SasakiCarliniJozsa2001]. -/
theorem majorityVoteScore_eq_closedForm (N : ℕ) (θ : ℝ) :
    majorityVoteScore N θ = mvClosedForm N θ := by
  have hInt : (1/(2*Real.pi)) * ∫ φ in (0:ℝ)..(2*Real.pi),
      (majorityProbZero N φ * Real.cos ((φ-θ)/2)^2
        + (1 - majorityProbZero N φ) * Real.sin ((φ+θ)/2)^2)
      = 1/2 + Real.cos θ * ((1/(2*Real.pi)) *
          ∫ φ in (0:ℝ)..(2*Real.pi), majorityProbZero N φ * Real.cos φ) := by
    simp_rw [pointwise N θ]
    have hB : Continuous (fun φ : ℝ => majorityProbZero N φ * Real.cos φ * Real.cos θ) :=
      ((continuous_majorityProbZero N).mul Real.continuous_cos).mul continuous_const
    have hA : Continuous (fun φ : ℝ => (1/2:ℝ) + majorityProbZero N φ * Real.cos φ * Real.cos θ) :=
      continuous_const.add hB
    have hC : Continuous (fun φ : ℝ => (1/2:ℝ) * Real.cos (φ+θ)) :=
      continuous_const.mul (Real.continuous_cos.comp (continuous_id.add continuous_const))
    have hcos : ∫ φ in (0:ℝ)..(2*Real.pi), Real.cos (φ+θ) = 0 := by
      rw [integral_comp_add_right (f := Real.cos) (a := (0:ℝ)) (b := 2*Real.pi) (d := θ)]
      rw [show (0:ℝ)+θ = θ by ring, integral_cos]
      rw [show 2*Real.pi + θ = θ + 2*Real.pi by ring, Real.sin_add_two_pi]
      ring
    rw [intervalIntegral.integral_sub (hA.intervalIntegrable 0 (2*Real.pi))
          (hC.intervalIntegrable 0 (2*Real.pi))]
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 (2*Real.pi))
          (hB.intervalIntegrable 0 (2*Real.pi))]
    rw [show (∫ φ in (0:ℝ)..(2*Real.pi), (1/2:ℝ)) = Real.pi by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring]
    rw [intervalIntegral.integral_mul_const (Real.cos θ)]
    rw [intervalIntegral.integral_const_mul, hcos]
    simp only [mul_zero, sub_zero]
    field_simp
  rw [majorityVoteScore, hInt, mvClosedForm, hsum N]
  ring

/-- For one copy, the majority-vote score expression is `1 / 2 + cos θ / 4`. See
[SasakiCarliniJozsa2001]. -/
theorem mvClosedForm_one (θ : ℝ) :
    mvClosedForm 1 θ = 1 / 2 + Real.cos θ / 4 := by
  simp [mvClosedForm, mvCoefficient, oddDFact, Nat.doubleFactorial]
  ring

end Qatlib.Papers.TemplMatch01.MainResults.Semiclassical
