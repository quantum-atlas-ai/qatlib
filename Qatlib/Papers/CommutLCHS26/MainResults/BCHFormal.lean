/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Formal matrix logarithms of exponential words

`logCoefficient` and `logSeries` define matrix formal logarithms through the exponent variable
in power polynomials. The coefficients `exponentCoefficient` recover the factorial relations
needed to reconstruct a normalized series from its logarithm degree by degree.

The module also proves reversal symmetry, conjugate transpose compatibility, real scaling, and
the first and cubic Strang logarithm formulas. These formal identities support the symmetric
product formula analysis of [AftabAnTrivisa2026].

## Main statements

* `exp_log_coefficient`: reconstructs each coefficient of a series with constant coefficient
  one.
* `symmetric_logCoefficient_even`: gives vanishing of even logarithm coefficients for symmetric
  words.
* `symmetric_logCoefficient_skew`: gives skew Hermitian logarithm coefficients for symmetric
  skew Hermitian inputs.
* `strang_logCoefficient_three`: computes the cubic double commutator expression.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open SubdivisionPolynomial
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The matrix obtained by extracting the linear coefficient in the exponent variable from the
degree `n` power polynomial. -/
def logCoefficient (f : PowerSeries (Matrix I I ℂ)) (n : ℕ) : Matrix I I ℂ :=
  fun i j => (powerPolynomial f n i j).coeff 1

/-- The matrix power series with coefficients `logCoefficient f n`. -/
def logSeries (f : PowerSeries (Matrix I I ℂ)) : PowerSeries (Matrix I I ℂ) :=
  PowerSeries.mk (logCoefficient f)

/-- Complex polynomials agreeing at every natural number are equal. -/
private theorem polynomial_eq_of_nat_eval (p q : Polynomial ℂ)
    (h : ∀ n : ℕ, p.eval (n : ℂ) = q.eval (n : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℂ)))).mono
  rintro _ ⟨n, rfl⟩
  exact h n

/-- For a series with constant coefficient one, the derivative of its power polynomial is the
degree convolution of its logarithm coefficient with its power polynomial. -/
theorem powerPolynomial_derivative (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 1) (n : ℕ) (i j : I) :
    (powerPolynomial f n i j).derivative =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ l : I,
        Polynomial.C (logCoefficient f p.1 i l) * powerPolynomial f p.2 l j := by
  apply polynomial_eq_of_nat_eval
  intro q
  have h := congrArg (fun P : Polynomial ℂ => P.derivative.eval 0)
    (powerPolynomial_shift f hf n q i j)
  simpa only [Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, mul_one,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    zero_add, Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_zero, Polynomial.eval_one, mul_zero, add_zero, Polynomial.eval_C,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    zero_add, Nat.cast_zero, Nat.cast_one, mul_one, one_mul, logCoefficient,
    powerPolynomial_eval f hf] using h

/-- The matrix power series obtained by extracting the rth exponent variable coefficient of each
power polynomial. -/
def exponentCoefficient (f : PowerSeries (Matrix I I ℂ)) (r : ℕ) :
    PowerSeries (Matrix I I ℂ) :=
  PowerSeries.mk fun n => fun i j => (powerPolynomial f n i j).coeff r

/-- For a series with constant coefficient one, the zeroth exponent coefficient series is one. -/
theorem exponentCoefficient_zero (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 1) : exponentCoefficient f 0 = 1 := by
  apply PowerSeries.ext
  intro n
  ext i j
  simpa only [exponentCoefficient, PowerSeries.coeff_mk,
    Polynomial.coeff_zero_eq_eval_zero, Nat.cast_zero, pow_zero] using!
    powerPolynomial_eval f hf n 0 i j

/-- For a series with constant coefficient one, successive exponent coefficient series satisfy
the formal exponential recurrence with `logSeries`. -/
theorem exponentCoefficient_succ (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 1) (r : ℕ) :
    ((r + 1 : ℕ) : ℂ) • exponentCoefficient f (r + 1) =
      logSeries f * exponentCoefficient f r := by
  apply PowerSeries.ext
  intro n
  ext i j
  have h := congrArg (fun P : Polynomial ℂ => P.coeff r)
    (powerPolynomial_derivative f hf n i j)
  simpa only [exponentCoefficient, logSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_smul, Matrix.smul_apply, smul_eq_mul,
    Polynomial.coeff_derivative, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_C, Nat.cast_add, Nat.cast_one,
    PowerSeries.coeff_mul, Matrix.sum_apply, Matrix.mul_apply, mul_comm] using h

/-- For a series with constant coefficient one, multiplying the rth exponent coefficient series
by `r!` gives the rth power of its logarithm series. -/
theorem exponentCoefficient_factorial (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 1) (r : ℕ) :
    (r.factorial : ℂ) • exponentCoefficient f r = logSeries f ^ r := by
  induction r with
  | zero => simp [exponentCoefficient_zero f hf]
  | succ r ih =>
    calc
      _ = (r.factorial : ℂ) •
          (((r + 1 : ℕ) : ℂ) • exponentCoefficient f (r + 1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul, mul_smul, smul_comm]
      _ = (r.factorial : ℂ) • (logSeries f * exponentCoefficient f r) := by
        rw [exponentCoefficient_succ f hf]
      _ = logSeries f * ((r.factorial : ℂ) • exponentCoefficient f r) := by
        rw [mul_smul_comm]
      _ = _ := by rw [ih, pow_succ']

/-- For a series with constant coefficient one, the rth exponent coefficient series is the rth
logarithm series power divided by `r!`. -/
theorem exponentCoefficient_eq (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 1) (r : ℕ) :
    exponentCoefficient f r = (r.factorial : ℂ)⁻¹ • logSeries f ^ r := by
  have hr : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  calc
    _ = (r.factorial : ℂ)⁻¹ • ((r.factorial : ℂ) • exponentCoefficient f r) := by
      rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
    _ = _ := by rw [exponentCoefficient_factorial f hf]

/-- A matrix series with constant coefficient one is recovered degree by degree by
exponentiating its formal logarithm. -/
theorem exp_log_coefficient (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 1) (n : ℕ) :
    PowerSeries.coeff n f = ∑ r ∈ Finset.range (n + 1),
      (r.factorial : ℂ)⁻¹ • PowerSeries.coeff n (logSeries f ^ r) := by
  ext i j
  have he := Polynomial.eval₂_eq_sum_range' (RingHom.id ℂ)
    (Nat.lt_succ_of_le (powerPolynomial_degree f n i j)) (1 : ℂ)
  rw [Polynomial.eval₂_id] at he
  have h1 : (powerPolynomial f n i j).eval 1 = PowerSeries.coeff n f i j := by
    simpa only [Nat.cast_one, pow_one] using! powerPolynomial_eval f hf n 1 i j
  rw [h1] at he
  simp only [RingHom.id_apply, one_pow, mul_one] at he
  rw [he]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun F => (PowerSeries.coeff n F : Matrix I I ℂ) i j)
    (exponentCoefficient_eq f hf r)
  simpa only [exponentCoefficient, PowerSeries.coeff_mk, PowerSeries.coeff_smul,
    Matrix.smul_apply, smul_eq_mul] using! h

/-- The zeroth logarithm coefficient is zero. -/
theorem logCoefficient_zero (f : PowerSeries (Matrix I I ℂ)) : logCoefficient f 0 = 0 := by
  ext i j
  simp [logCoefficient, powerPolynomial, choosePolynomial, Polynomial.coeff_one]

set_option backward.isDefEq.respectTransparency true in

/-- The first logarithm coefficient is the first coefficient of the original series. -/
theorem logCoefficient_one (f : PowerSeries (Matrix I I ℂ)) :
    logCoefficient f 1 = PowerSeries.coeff 1 f := by
  ext i j
  simp [logCoefficient, powerPolynomial, choosePolynomial, Finset.sum_range_succ]

/-- The linear coefficient of the descending Pochhammer polynomial of degree `k + 1` is `(-1)^k
* k!`. -/
private theorem descPochhammer_linear (k : ℕ) :
    (descPochhammer ℂ (k + 1)).coeff 1 = (-1 : ℂ) ^ k * (k.factorial : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X]
    have hzero : (descPochhammer ℂ (k + 1)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact descPochhammer_ne_zero_eval_zero ℂ (by omega)
    rw [hzero, Polynomial.coeff_mul_natCast, ih, Nat.factorial_succ, Nat.cast_mul,
      pow_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- The linear coefficient of the binomial polynomial of degree `k + 1` is `(-1)^k / (k + 1)`. -/
theorem choosePolynomial_linear (k : ℕ) :
    (choosePolynomial (k + 1)).coeff 1 = (-1 : ℂ) ^ k / (k + 1) := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [choosePolynomial, Polynomial.coeff_smul, descPochhammer_linear,
    smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The nth logarithm coefficient is the finite alternating sum of the nth coefficients of
positive powers of `f - 1`, divided by their exponents. -/
theorem logCoefficient_finite (f : PowerSeries (Matrix I I ℂ)) (n : ℕ) :
    logCoefficient f n = ∑ k ∈ Finset.range n,
      ((-1 : ℝ) ^ k / (k + 1)) • PowerSeries.coeff n ((f - 1) ^ (k + 1)) := by
  ext i j
  simp only [logCoefficient, powerPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast]
  rw [Finset.sum_range_succ']
  have hzero : (choosePolynomial 0).coeff 1 = 0 := by
    simp [choosePolynomial, Polynomial.coeff_one]
  simp only [choosePolynomial_linear, hzero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Every even logarithm coefficient of a reversal invariant exponential word vanishes. -/
theorem symmetric_logCoefficient_even (ws : List (Matrix I I ℂ))
    (hws : ws.reverse = ws) (n : ℕ) (hn : Even n) :
    logCoefficient (wordSeries ws) n = 0 := by
  ext i j
  have h := congrArg (fun P : Polynomial ℂ => P.coeff 1)
    (symmetric_powerPolynomial_parity ws hws n i j)
  have he : (-Polynomial.X : Polynomial ℂ) = Polynomial.C (-1) * Polynomial.X := by simp
  simp only [he, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_smul,
    smul_eq_mul, pow_one, hn.neg_one_pow, one_mul] at h
  change (powerPolynomial (wordSeries ws) n i j).coeff 1 = 0
  linear_combination (-1 / 2 : ℂ) * h

/-- The matrix power series formed by taking the conjugate transpose of each coefficient. -/
def adjointSeries (f : PowerSeries (Matrix I I ℂ)) : PowerSeries (Matrix I I ℂ) :=
  PowerSeries.mk fun n => (PowerSeries.coeff n f)ᴴ

/-- Taking coefficientwise conjugate transpose reverses the order of power series
multiplication. -/
theorem adjointSeries_mul (f g : PowerSeries (Matrix I I ℂ)) :
    adjointSeries (f * g) = adjointSeries g * adjointSeries f := by
  apply PowerSeries.ext
  intro n
  simp only [adjointSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  rfl

/-- The adjoint of an exponential word series is the word series of the reversed, conjugate
transposed list. -/
theorem adjointSeries_word (ws : List (Matrix I I ℂ)) :
    adjointSeries (wordSeries ws) = wordSeries (ws.reverse.map Matrix.conjTranspose) := by
  have hs (X : Matrix I I ℂ) : adjointSeries (wordSeries [X]) = wordSeries [Xᴴ] := by
    apply PowerSeries.ext
    intro n
    simp only [adjointSeries, wordSeries, PowerSeries.coeff_mk, suzukiSeries_singleton,
      Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_pow]
  have hnil : adjointSeries (wordSeries ([] : List (Matrix I I ℂ))) = wordSeries [] := by
    apply PowerSeries.ext
    intro n
    cases n <;> simp [adjointSeries, wordSeries, suzukiSeries]
  induction ws with
  | nil => exact hnil
  | cons X xs ih =>
    have hc : wordSeries (X :: xs) = wordSeries [X] * wordSeries xs := by
      simpa only [List.singleton_append] using! wordSeries_append [X] xs
    rw [hc, adjointSeries_mul, hs, ih]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      wordSeries_append]

/-- Coefficientwise conjugate transpose preserves powers of a single matrix series. -/
theorem adjointSeries_pow (f : PowerSeries (Matrix I I ℂ)) (q : ℕ) :
    adjointSeries (f ^ q) = adjointSeries f ^ q := by
  induction q with
  | zero =>
    apply PowerSeries.ext
    intro n
    cases n <;> simp [adjointSeries]
  | succ q ih => rw [pow_succ, adjointSeries_mul, ih, ← pow_succ']

/-- Every coefficient of a binomial polynomial is fixed by complex conjugation. -/
theorem choosePolynomial_real (k r : ℕ) :
    star ((choosePolynomial k).coeff r) = (choosePolynomial k).coeff r := by
  have h : (choosePolynomial k).map (starRingEnd ℂ) = choosePolynomial k := by
    simp [choosePolynomial, Polynomial.smul_eq_C_mul]
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff r) h
  simpa only [Polynomial.coeff_map, starRingEnd_apply] using! hc

/-- Logarithm coefficients commute with coefficientwise conjugate transpose. -/
theorem logCoefficient_adjoint (f : PowerSeries (Matrix I I ℂ)) (n : ℕ) :
    logCoefficient (adjointSeries f) n = (logCoefficient f n)ᴴ := by
  have hsub : adjointSeries (f - 1) = adjointSeries f - 1 := by
    apply PowerSeries.ext
    intro n
    cases n <;> simp [adjointSeries]
  ext i j
  simp only [logCoefficient, powerPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul, Matrix.conjTranspose_apply, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun F => (PowerSeries.coeff n F : Matrix I I ℂ) i j)
    (adjointSeries_pow (f - 1) k)
  rw [hsub] at h
  simp only [adjointSeries, PowerSeries.coeff_mk, Matrix.conjTranspose_apply] at h
  rw [h, choosePolynomial_real]
  exact mul_comm _ _

/-- Scaling every matrix in an exponential word by a real scalar scales its nth logarithm
coefficient by the nth power of that scalar. -/
theorem logCoefficient_scale (ws : List (Matrix I I ℂ)) (a : ℝ) (n : ℕ) :
    logCoefficient (wordSeries (ws.map (fun X => a • X))) n =
      a ^ n • logCoefficient (wordSeries ws) n := by
  ext i j
  have hp : powerPolynomial (wordSeries (ws.map (fun X => a • X))) n i j =
      (a : ℂ) ^ n • powerPolynomial (wordSeries ws) n i j := by
    apply polynomial_eq_of_nat_eval
    intro q
    simp only [Polynomial.eval_smul, smul_eq_mul]
    rw [powerPolynomial_eval _ (by simp [wordSeries]),
      powerPolynomial_eval _ (by simp [wordSeries]), word_power_scaled_coefficient,
      Matrix.smul_apply, Complex.real_smul, Complex.ofReal_pow]
  have h := congrArg (fun p : Polynomial ℂ => p.coeff 1) hp
  simpa only [logCoefficient, Polynomial.coeff_smul, Matrix.smul_apply,
    Complex.real_smul, Complex.ofReal_pow, smul_eq_mul] using! h

/-- Every logarithm coefficient of a reversal invariant word of skew Hermitian matrices is skew
Hermitian. -/
theorem symmetric_logCoefficient_skew (ws : List (Matrix I I ℂ))
    (hws : ws.reverse = ws) (hskew : ∀ X ∈ ws, Xᴴ = -X) (n : ℕ) :
    (logCoefficient (wordSeries ws) n)ᴴ = -logCoefficient (wordSeries ws) n := by
  have hw : ws.reverse.map Matrix.conjTranspose = ws.map (fun X => (-1 : ℝ) • X) := by
    rw [hws]
    apply List.map_congr_left
    intro X hX
    simpa only [neg_one_smul] using! hskew X hX
  rw [← logCoefficient_adjoint, adjointSeries_word, hw, logCoefficient_scale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [symmetric_logCoefficient_even ws hws n hn]
    simp
  · rw [hn.neg_one_pow, neg_one_smul]

/-- A convergent real linear combination of logarithm coefficients of a reversal invariant skew
Hermitian word is skew Hermitian. -/
theorem logCoefficient_hasSum_skew (ws : List (Matrix I I ℂ))
    (hws : ws.reverse = ws) (hskew : ∀ X ∈ ws, Xᴴ = -X)
    (a : ℕ → ℝ) (v : Matrix I I ℂ)
    (h : HasSum (fun n => a n • logCoefficient (wordSeries ws) n) v) :
    vᴴ = -v := by
  have ht := h.matrix_conjTranspose
  simp only [Matrix.conjTranspose_smul, star_trivial,
    symmetric_logCoefficient_skew ws hws hskew, smul_neg] at ht
  exact ht.unique h.neg

/-- The nth coefficient of a matrix exponential word is the finite factorial weighted sum of the
nth coefficients of powers of its logarithm series. -/
theorem word_exp_log (ws : List (Matrix I I ℂ)) (n : ℕ) :
    suzukiSeries ws n = ∑ r ∈ Finset.range (n + 1),
      (r.factorial : ℂ)⁻¹ • PowerSeries.coeff n (logSeries (wordSeries ws) ^ r) := by
  simpa only [wordSeries, PowerSeries.coeff_mk] using!
    exp_log_coefficient (wordSeries ws) (by simp [wordSeries]) n

/-- The first logarithm coefficient of the Strang series is `X + Y`. -/
theorem strang_logCoefficient_one (X Y : Matrix I I ℂ) :
    logCoefficient (strangSeries X Y) 1 = X + Y := by
  rw [logCoefficient_one, strangSeries_first]

/-- Every even logarithm coefficient of the Strang series vanishes. -/
theorem strang_logCoefficient_even (X Y : Matrix I I ℂ) (n : ℕ) (hn : Even n) :
    logCoefficient (strangSeries X Y) n = 0 :=
  symmetric_logCoefficient_even _ rfl n hn

/-- The logarithm coefficients of the Strang series are skew Hermitian when both generators are
skew Hermitian. -/
theorem strang_logCoefficient_skew (X Y : Matrix I I ℂ)
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (n : ℕ) :
    (logCoefficient (strangSeries X Y) n)ᴴ = -logCoefficient (strangSeries X Y) n := by
  apply symmetric_logCoefficient_skew _ rfl
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl
  · simp [Matrix.conjTranspose_smul, hX]
  · exact hY
  · simp [Matrix.conjTranspose_smul, hX]

/-- For a series with constant coefficient one, the cubic logarithm coefficient is its cubic
coefficient minus half the two ordered linear quadratic products plus one third of the
linear coefficient cubed. -/
theorem logCoefficient_three (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1) :
    logCoefficient f 3 = PowerSeries.coeff 3 f -
      (1 / 2 : ℝ) • (PowerSeries.coeff 1 f * PowerSeries.coeff 2 f +
        PowerSeries.coeff 2 f * PowerSeries.coeff 1 f) +
      (1 / 3 : ℝ) • PowerSeries.coeff 1 f ^ 3 := by
  rw [logCoefficient_finite]
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hf, pow_succ]
  module

/-- The cubic Strang logarithm coefficient is the sum of the indicated double commutators with
coefficients `-1/24` and `1/12`. -/
theorem strang_logCoefficient_three (X Y : Matrix I I ℂ) :
    logCoefficient (strangSeries X Y) 3 =
      (-1 / 24 : ℝ) • (X * (X * Y - Y * X) - (X * Y - Y * X) * X) +
      (1 / 12 : ℝ) • (Y * (Y * X - X * Y) - (Y * X - X * Y) * Y) := by
  rw [logCoefficient_three _ (strangSeries_constant X Y)]
  norm_num [strangSeries, wordSeries, suzukiSeries_cons_three,
    suzukiSeries_cons_two, suzukiSeries_cons_one, suzukiSeries_nil_succ]
  simp only [pow_succ, pow_zero, Matrix.mul_add, Matrix.add_mul, sub_eq_add_neg,
    mul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.mul_assoc, smul_add, Matrix.one_mul]
  match_scalars <;> ring

end Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal
