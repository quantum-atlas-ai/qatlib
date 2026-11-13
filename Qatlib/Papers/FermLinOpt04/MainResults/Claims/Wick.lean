/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.Monomial

/-!
# Wick trace formulas for Gaussian states

The Gaussian-state predicate gives Pfaffian formulas for traces of even Majorana monomials with
the specified power of the imaginary unit. Traces of odd Majorana monomials vanish. These
results formalize the indicated identities from [Bravyi2005Fermionic].

## Main statements

* `wick_state`: evaluates an even correlator as `pfaffianSub M T`.
* `wick_state_odd`: gives zero for odd correlators.

## References

* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.FermLinOpt04.MainResults.Model

namespace Qatlib.Papers.FermLinOpt04.MainResults.Claims

/-- For a Gaussian state and an even-cardinality index set, the trace of the state times
`I^(T.card / 2)` times the ordered Majorana monomial equals `pfaffianSub M T`. This is the
Wick formula corresponding to equation (17) of [Bravyi2005Fermionic]. -/
theorem wick_state {n : ℕ} {ρ : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} (hρ : IsGaussianState ρ M)
    {T : Finset (Fin (2 * n))} (hT : Even T.card) :
    Matrix.trace (ρ * ((Complex.I ^ (T.card / 2)) • monomial T)) = pfaffianSub M T := by
  obtain ⟨-, -, hρeq⟩ := hρ
  subst hρeq
  have h2 : ((2 : ℂ) ^ n) ≠ 0 := by
    have hpos : (0 : ℂ) < 2 ^ n := by positivity
    exact ne_of_gt hpos
  have hII : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    trace_gaussianOp_mul_monomial_even M (((2 : ℂ) ^ n)⁻¹) hT,
    inv_mul_cancel₀ h2, one_mul, ← mul_assoc, ← mul_pow, hII, one_pow, one_mul]

/-- For a Gaussian state and an odd-cardinality index set, the trace of the state times the
ordered Majorana monomial vanishes. -/
theorem wick_state_odd {n : ℕ} {ρ : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} (hρ : IsGaussianState ρ M)
    {T : Finset (Fin (2 * n))} (hT : Odd T.card) :
    Matrix.trace (ρ * monomial T) = 0 := by
  obtain ⟨-, -, hρeq⟩ := hρ
  subst hρeq
  rw [trace_gaussianOp_mul_monomial_odd M (((2 : ℂ) ^ n)⁻¹) hT]

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
