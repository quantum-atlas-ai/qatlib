/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHDynkin
import Qatlib.Papers.CommutLCHS26.MainResults.FormalPowers
import Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.FieldSimp

/-!
# Formal logarithms through power polynomials

`chooseQ` and `powerPolynomial` encode coefficients of natural powers of a normalized formal
series as polynomials in the exponent. The linear term defines `logCoefficient`, and `logSeries`
collects these coefficients.

The module proves the finite logarithm formula, compatibility with algebra homomorphisms, and
additivity for products of commuting normalized series over rational monoid algebras. These
identities underlie the word logarithm construction for [AftabAnTrivisa2026].

## Main statements

* `powerPolynomial_eval`: recovers a coefficient of a natural power.
* `logCoefficient_finite`: gives the finite alternating logarithm sum.
* `logCoefficient_map`: transports logarithm coefficients under algebra homomorphisms.
* `logCoefficient_mul`: proves additivity for commuting normalized series.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLog

open scoped BigOperators MonoidAlgebra
open BCHDynkin SubdivisionPolynomial FormalPowers

section Projection
variable {A : Type} [Ring A]

/-- The polynomial obtained by applying an additive map to each coefficient. -/
def project (L : A →+ ℚ) (p : Polynomial A) : Polynomial ℚ :=
  ⟨⟨p.toFinsupp.coeff.mapRange L L.map_zero⟩⟩

/-- The nth coefficient of a projected polynomial is the additive image of its nth coefficient. -/
theorem project_coeff (L : A →+ ℚ) (p : Polynomial A) (n : ℕ) :
    (project L p).coeff n = L (p.coeff n) := rfl

/-- Coefficientwise projection by an additive map preserves polynomial addition. -/
theorem project_add (L : A →+ ℚ) (p q : Polynomial A) :
    project L (p + q) = project L p + project L q := by
  apply Polynomial.ext
  intro n
  simp only [project_coeff, Polynomial.coeff_add, map_add]

/-- Coefficientwise projection sends a monomial to the monomial with its coefficient mapped. -/
theorem project_monomial (L : A →+ ℚ) (n : ℕ) (a : A) :
    project L (Polynomial.monomial n a) = Polynomial.monomial n (L a) := by
  apply Polynomial.ext
  intro r
  by_cases h : n = r <;> simp [project_coeff, Polynomial.coeff_monomial, h]

/-- Coefficientwise additive projection commutes with evaluation at natural numbers. -/
theorem project_eval_nat (L : A →+ ℚ) (p : Polynomial A) (q : ℕ) :
    (project L p).eval (q : ℚ) = L (p.eval (q : A)) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [project_add, Polynomial.eval_add, Polynomial.eval_add, map_add, hp, hr]
  | monomial n a =>
    rw [project_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
    simp only [← Nat.cast_pow, ← nsmul_eq_mul', map_nsmul]

end Projection

section CoefficientAlgebra
variable {M : Type} [Monoid M]

/-- Polynomials over a rational monoid algebra are equal if their evaluations agree at every
natural number. -/
theorem polynomial_eq_of_nat_eval (p q : Polynomial (MonoidAlgebra ℚ M))
    (h : ∀ n : ℕ, p.eval (n : MonoidAlgebra ℚ M) = q.eval (n : MonoidAlgebra ℚ M)) : p = q := by
  apply Polynomial.ext
  intro r
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro w
  let L : MonoidAlgebra ℚ M →+ ℚ :=
    { toFun := fun v => v.coeff w
      map_zero' := by simp
      map_add' := by intros; simp }
  have hpq : project L p = project L q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective
      (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ)))).mono
    rintro _ ⟨n, rfl⟩
    change (project L p).eval (n : ℚ) = (project L q).eval (n : ℚ)
    rw [project_eval_nat, project_eval_nat]
    exact congrArg L (h n)
  have hr := congrArg (fun P : Polynomial ℚ => P.coeff r) hpq
  change (project L p).coeff r = (project L q).coeff r at hr
  rw [project_coeff, project_coeff] at hr
  exact hr

end CoefficientAlgebra

section Newton
variable {A : Type} [Ring A] [Algebra ℚ A]

/-- The rational binomial polynomial obtained by dividing the descending Pochhammer polynomial
by its degree factorial. -/
def chooseQ (k : ℕ) : Polynomial ℚ := (k.factorial : ℚ)⁻¹ • descPochhammer ℚ k

/-- The rational binomial polynomial evaluates at a natural number to the corresponding binomial
coefficient. -/
theorem chooseQ_eval (k q : ℕ) : (chooseQ k).eval (q : ℚ) = (q.choose k : ℚ) := by
  rw [chooseQ, Polynomial.eval_smul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_eq_mul]
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- The finite binomial polynomial encoding the degree `n` coefficients of powers of a series
through the coefficients of powers of `f - 1`. -/
def powerPolynomial (f : PowerSeries A) (n : ℕ) : Polynomial A :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (PowerSeries.coeff n ((f - 1) ^ k)) *
    (chooseQ k).map (algebraMap ℚ A)

omit [Algebra ℚ A] in

/-- Evaluation at a natural number preserves polynomial multiplication over the given ring. -/
theorem eval_mul_nat (p q : Polynomial A) (n : ℕ) :
    (p * q).eval (n : A) = p.eval (n : A) * q.eval (n : A) := by
  exact Polynomial.eval₂_mul_noncomm (RingHom.id A) (n : A)
    (fun k => (Nat.cast_commute n (q.coeff k)).symm)

/-- Mapping a rational polynomial into the algebra commutes with evaluation at natural numbers. -/
theorem map_eval_nat (p : Polynomial ℚ) (n : ℕ) :
    (p.map (algebraMap ℚ A)).eval (n : A) = algebraMap ℚ A (p.eval (n : ℚ)) := by
  rw [Polynomial.eval_map]
  simpa only [map_natCast] using
    (Polynomial.eval₂_at_apply (p := p) (algebraMap ℚ A) (n : ℚ))

/-- For a series with constant coefficient one, evaluating its nth power polynomial at a natural
exponent gives the nth coefficient of that power. -/
theorem powerPolynomial_eval (f : PowerSeries A) (hf : f.constantCoeff = 1) (n q : ℕ) :
    (powerPolynomial f n).eval (q : A) = PowerSeries.coeff n (f ^ q) := by
  rw [power_coefficient_newton f hf n q]
  simp only [powerPolynomial, Polynomial.eval_finsetSum, eval_mul_nat, Polynomial.eval_C,
    map_eval_nat, chooseQ_eval, map_natCast, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact (Nat.cast_commute (q.choose k) _).symm.eq

/-- For a series with constant coefficient one, the constant term of its nth power polynomial is
the nth coefficient of the unit series. -/
theorem powerPolynomial_zero (f : PowerSeries A) (hf : f.constantCoeff = 1) (n : ℕ) :
    (powerPolynomial f n).coeff 0 = PowerSeries.coeff n (1 : PowerSeries A) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa only [Nat.cast_zero, pow_zero] using powerPolynomial_eval f hf n 0

/-- The linear coefficient of the nth power polynomial, defining the nth formal logarithm
coefficient. -/
def logCoefficient (f : PowerSeries A) (n : ℕ) : A := (powerPolynomial f n).coeff 1

/-- The formal power series formed from the logarithm coefficients. -/
def logSeries (f : PowerSeries A) : PowerSeries A := PowerSeries.mk (logCoefficient f)

/-- The linear coefficient of the rational descending Pochhammer polynomial of degree `k + 1`
equals `(-1)^k * k!`. -/
private theorem descPochhammer_linear (k : ℕ) :
    (descPochhammer ℚ (k + 1)).coeff 1 = (-1 : ℚ) ^ k * (k.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X]
    have hzero : (descPochhammer ℚ (k + 1)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact descPochhammer_ne_zero_eval_zero ℚ (by omega)
    rw [hzero, Polynomial.coeff_mul_natCast, ih, Nat.factorial_succ, Nat.cast_mul,
      pow_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- The linear coefficient of the rational binomial polynomial of degree `k + 1` is `(-1)^k / (k
+ 1)`. -/
theorem chooseQ_linear (k : ℕ) :
    (chooseQ (k + 1)).coeff 1 = (-1 : ℚ) ^ k / (k + 1) := by
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [chooseQ, Polynomial.coeff_smul, descPochhammer_linear,
    smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The nth formal logarithm coefficient is the finite alternating sum of the nth coefficients
of positive powers of `f - 1`, divided by their exponents. -/
theorem logCoefficient_finite (f : PowerSeries A) (n : ℕ) :
    logCoefficient f n = ∑ k ∈ Finset.range n,
      ((-1 : ℚ) ^ k / (k + 1)) • PowerSeries.coeff n ((f - 1) ^ (k + 1)) := by
  simp only [logCoefficient, powerPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_map]
  rw [Finset.sum_range_succ']
  have hz : (chooseQ 0).coeff 1 = 0 := by simp [chooseQ, Polynomial.coeff_one]
  simp only [hz, map_zero, mul_zero, add_zero, chooseQ_linear]
  apply Finset.sum_congr rfl
  intro k _
  rw [Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

/-- Rational algebra homomorphisms preserve formal logarithm coefficients. -/
theorem logCoefficient_map {B : Type} [Ring B] [Algebra ℚ B] (φ : A →ₐ[ℚ] B)
    (f : PowerSeries A) (n : ℕ) :
    logCoefficient (PowerSeries.map φ.toRingHom f) n = φ (logCoefficient f n) := by
  rw [logCoefficient_finite, logCoefficient_finite, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  congr 1
  change PowerSeries.coeff n _ =
    PowerSeries.coeff n (PowerSeries.map φ.toRingHom ((f - 1) ^ (k + 1)))
  congr 1
  simp only [map_pow, map_sub, map_one]

end Newton

section Multiplication
variable {M : Type} [Monoid M]

/-- For commuting series over a rational monoid algebra with constant coefficient one, the power
polynomial of their product is the degree convolution of their power polynomials. -/
theorem powerPolynomial_mul (f g : PowerSeries (MonoidAlgebra ℚ M))
    (hf : f.constantCoeff = 1) (hg : g.constantCoeff = 1) (hfg : Commute f g) (n : ℕ) :
    powerPolynomial (f * g) n = ∑ p ∈ Finset.antidiagonal n,
      powerPolynomial f p.1 * powerPolynomial g p.2 := by
  apply polynomial_eq_of_nat_eval
  intro q
  rw [powerPolynomial_eval (f * g) (by simp [hf, hg])]
  simp only [Polynomial.eval_finsetSum, eval_mul_nat, powerPolynomial_eval f hf,
    powerPolynomial_eval g hg]
  rw [hfg.mul_pow, PowerSeries.coeff_mul]

/-- For commuting series over a rational monoid algebra with constant coefficient one, the
logarithm coefficient of their product is the sum of their logarithm coefficients. -/
theorem logCoefficient_mul (f g : PowerSeries (MonoidAlgebra ℚ M))
    (hf : f.constantCoeff = 1) (hg : g.constantCoeff = 1) (hfg : Commute f g) (n : ℕ) :
    logCoefficient (f * g) n = logCoefficient f n + logCoefficient g n := by
  have hp := congrArg (fun p : Polynomial (MonoidAlgebra ℚ M) => p.coeff 1)
    (powerPolynomial_mul f g hf hg hfg n)
  change logCoefficient (f * g) n = _ at hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.mul_coeff_one,
    powerPolynomial_zero f hf, powerPolynomial_zero g hg] at hp
  have he : logCoefficient (f * g) n =
      PowerSeries.coeff n ((1 : PowerSeries (MonoidAlgebra ℚ M)) * logSeries g + logSeries f * 1) := by
    rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    simp only [logSeries, PowerSeries.coeff_mk]
    rw [← Finset.sum_add_distrib]
    exact hp
  simpa only [one_mul, mul_one, map_add, logSeries, PowerSeries.coeff_mk,
    add_comm] using he

end Multiplication
end Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLog
