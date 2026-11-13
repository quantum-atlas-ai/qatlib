/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse

/-!
# Singular polynomials through Hermitian dilation

This module expresses even and odd polynomials of a Hermitian dilation in terms of the two Gram
matrices. The polynomial forms `evenSingularPolynomial q` and `oddSingularPolynomial q`
represent `q(X ^ 2)` and `X * q(X ^ 2)` respectively.

The resulting identities turn QSVT response polynomials into concrete Gram-polynomial formulas
for odd cross-frame and even same-frame compressions, as in the singular value transformation
framework of [GilyenSuLowWiebe2019].

## Main statements

* `aeval_evenSingularPolynomial`: even evaluation is block diagonal with Gram-polynomial blocks.
* `aeval_oddSingularPolynomial`: odd evaluation has the two Gram-polynomial off-diagonal blocks.
* `qsvt_odd_eq_singularPolynomial`: an odd response gives `A * aeval (Aᴴ * A) q`.
* `qsvt_even_right_eq_singularPolynomial`: an even right-frame response gives `aeval (Aᴴ * A)
  q`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib
section PolynomialBlocks

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- The even polynomial obtained by composing `q` with `X ^ 2`. -/
noncomputable def evenSingularPolynomial (q : Polynomial ℂ) : Polynomial ℂ :=
  q.comp (X ^ 2)

/-- The odd polynomial `X * q(X ^ 2)` associated with `q`. -/
noncomputable def oddSingularPolynomial (q : Polynomial ℂ) : Polynomial ℂ :=
  X * evenSingularPolynomial q

/-- The square of the Hermitian dilation is block diagonal with blocks `A * Aᴴ` and `Aᴴ * A`. -/
theorem hermitianDilation_sq (A : Matrix O I ℂ) :
    hermitianDilation A ^ 2 =
      Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
  simp [hermitianDilation, pow_two, Matrix.fromBlocks_multiply]

/-- Polynomial evaluation on a block diagonal matrix evaluates the polynomial independently on
each diagonal block. -/
theorem aeval_fromBlocks_diagonal (B : Matrix O O ℂ) (C : Matrix I I ℂ)
    (q : Polynomial ℂ) :
    aeval (Matrix.fromBlocks B 0 0 C) q =
      Matrix.fromBlocks (aeval B q) 0 0 (aeval C q) := by
  refine Polynomial.induction_on' q ?_ ?_
  · intro p r hp hr
    simp only [Polynomial.aeval_add, hp, hr, Matrix.fromBlocks_add, add_zero]
  · intro n a
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Matrix.fromBlocks_diagonal_pow, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    cases i <;> cases j <;> simp

/-- Evaluating `q(X ^ 2)` on the Hermitian dilation gives the block diagonal evaluations of `q`
on the two Gram matrices. -/
theorem aeval_evenSingularPolynomial (A : Matrix O I ℂ) (q : Polynomial ℂ) :
    aeval (hermitianDilation A) (evenSingularPolynomial q) =
      Matrix.fromBlocks (aeval (A * Aᴴ) q) 0 0 (aeval (Aᴴ * A) q) := by
  rw [evenSingularPolynomial, Polynomial.aeval_comp, Polynomial.aeval_X_pow,
    hermitianDilation_sq, aeval_fromBlocks_diagonal]

/-- Evaluating `X * q(X ^ 2)` on the dilation gives off-diagonal blocks `A * aeval (Aᴴ * A) q`
and `Aᴴ * aeval (A * Aᴴ) q`. -/
theorem aeval_oddSingularPolynomial (A : Matrix O I ℂ) (q : Polynomial ℂ) :
    aeval (hermitianDilation A) (oddSingularPolynomial q) =
      Matrix.fromBlocks 0 (A * aeval (Aᴴ * A) q)
        (Aᴴ * aeval (A * Aᴴ) q) 0 := by
  rw [oddSingularPolynomial, Polynomial.aeval_mul, Polynomial.aeval_X,
    aeval_evenSingularPolynomial]
  simp [hermitianDilation, Matrix.fromBlocks_multiply]

end PolynomialBlocks

section QSVTBridge

variable {H I O : Type*}
  [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

/-- If the response polynomial is `oddSingularPolynomial q` and the phase-list length is odd,
cross-frame compression equals `A * aeval (Aᴴ * A) q`. -/
theorem qsvt_odd_eq_singularPolynomial {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (q : Polynomial ℂ)
    (hpoly : responseP base zs = oddSingularPolynomial q)
    (hodd : zs.length % 2 = 1) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R =
      A * aeval (Aᴴ * A) q := by
  rw [qsvt_odd_eq_dilation h base zs hodd, hpoly, aeval_oddSingularPolynomial]
  simp

/-- If the response polynomial is `evenSingularPolynomial q` and the phase-list length is even,
left-frame compression equals `aeval (A * Aᴴ) q`. -/
theorem qsvt_even_left_eq_singularPolynomial {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (q : Polynomial ℂ)
    (hpoly : responseP base zs = evenSingularPolynomial q)
    (heven : zs.length % 2 = 0) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L =
      aeval (A * Aᴴ) q := by
  rw [qsvt_even_left_eq_dilation h base zs heven, hpoly, aeval_evenSingularPolynomial]
  simp

/-- If the response polynomial is `evenSingularPolynomial q` and the phase-list length is even,
right-frame compression with the adjoint oracle equals `aeval (Aᴴ * A) q`. -/
theorem qsvt_even_right_eq_singularPolynomial {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (q : Polynomial ℂ)
    (hpoly : responseP base zs = evenSingularPolynomial q)
    (heven : zs.length % 2 = 0) :
    compress R (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R =
      aeval (Aᴴ * A) q := by
  rw [qsvt_even_right_eq_dilation h base zs heven, hpoly, aeval_evenSingularPolynomial]
  simp

end QSVTBridge

end Qatlib.Concepts.CoherentSim.CoherentOAA
