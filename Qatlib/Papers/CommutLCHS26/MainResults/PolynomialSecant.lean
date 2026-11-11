/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Polynomial secants on Hermitian matrices

This module studies the polynomial `secant` and transfers scalar Lipschitz bounds to evaluations
at Hermitian matrices. These estimates provide polynomial functional calculus tools for the
operator analysis associated with [AftabAnTrivisa2026].

## Main statements

* `eval_self`: the secant value at its base point is the derivative.
* `norm_secant_le`: a Lipschitz bound controls the evaluated matrix secant.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.PolynomialSecant

open Matrix Polynomial Set
open scoped Classical Matrix.Norms.L2Operator NNReal

/-- The polynomial quotient of `p - C (p.eval a)` by `X - C a`. -/
def secant (p : Polynomial ℂ) (a : ℂ) : Polynomial ℂ :=
  (Polynomial.X_sub_C_dvd_sub_C_eval (p := p) (a := a)).choose

/-- Subtracting the value of a polynomial at `a` factors as `X - C a` times its secant
polynomial. -/
theorem factor (p : Polynomial ℂ) (a : ℂ) :
    p - C (p.eval a) = (X - C a) * secant p a :=
  (Polynomial.X_sub_C_dvd_sub_C_eval (p := p) (a := a)).choose_spec

/-- The difference of polynomial values at `x` and `a` equals `x - a` times the secant
polynomial evaluated at `x`. -/
theorem eval_factor (p : Polynomial ℂ) (a x : ℂ) :
    p.eval x - p.eval a = (x - a) * (secant p a).eval x := by
  have h := congrArg (fun q : Polynomial ℂ => q.eval x) (factor p a)
  simpa using h

/-- The secant polynomial evaluated at its base point equals the derivative of the original
polynomial there. -/
theorem eval_self (p : Polynomial ℂ) (a : ℂ) : (secant p a).eval a = p.derivative.eval a := by
  have h := congrArg (fun q : Polynomial ℂ => q.derivative.eval a) (factor p a)
  simpa using h.symm

/-- A Lipschitz bound for a polynomial on `[-M, M]` bounds its secant values when the base point
lies in the interior. -/
theorem eval_bound (p : Polynomial ℂ) (M a x : ℝ) (L : ℝ≥0)
    (ha : a ∈ Ioo (-M) M) (hx : x ∈ Icc (-M) M)
    (hl : LipschitzOnWith L (fun y : ℝ => p.eval (y : ℂ)) (Icc (-M) M)) :
    ‖(secant p (a : ℂ)).eval (x : ℂ)‖ ≤ (L : ℝ) := by
  by_cases hxa : x = a
  · subst x
    rw [eval_self]
    exact ((p.hasDerivAt (a : ℂ)).comp_ofReal).le_of_lipschitzOn
      (Icc_mem_nhds ha.1 ha.2) hl
  · have h := (lipschitzOnWith_iff_norm_sub_le.mp hl) hx ⟨ha.1.le, ha.2.le⟩
    rw [eval_factor] at h
    simp only [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    have hd : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hxa)
    by_contra hbad
    have hh := mul_pos hd (sub_pos.mpr (lt_of_not_ge hbad))
    nlinarith

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Polynomial evaluation at a Hermitian matrix is diagonalized by its eigenvector unitary, with
eigenvalues obtained by evaluating the polynomial. -/
theorem aeval_diagonalization (B : Matrix I I ℂ) (hB : B.IsHermitian) (p : Polynomial ℂ) :
    aeval B p = (hB.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => p.eval (hB.eigenvalues i : ℂ)) * (hB.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
  let eigVals : I → ℂ := fun i => (hB.eigenvalues i : ℂ)
  let D := Matrix.diagonal eigVals
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hB.eigenvectorUnitary
  have heval : (aeval eigVals) p = fun i => p.eval (eigVals i) := by
    funext i
    rw [Polynomial.aeval_pi_apply₂]
    simp [Polynomial.aeval_def]
  have hpd : aeval D p = Matrix.diagonal (fun i => p.eval (eigVals i)) := by
    have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℂ) eigVals p
    rw [heval] at h
    exact h
  have hpd' : aeval (Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) p =
      Matrix.diagonal (fun i => p.eval (eigVals i)) := by simpa [D, eigVals] using! hpd
  have hp : aeval B p = Φ (Matrix.diagonal (fun i => p.eval (eigVals i))) := by
    rw [hB.spectral_theorem, Polynomial.aeval_algHom_apply, hpd']
  simpa [Φ, eigVals] using! hp

/-- A uniform bound on polynomial values over the norm interval of a Hermitian matrix bounds the
norm of its matrix evaluation. -/
theorem norm_aeval_le (B : Matrix I I ℂ) (hB : B.IsHermitian) (p : Polynomial ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ x : ℝ, |x| ≤ ‖B‖ → ‖p.eval (x : ℂ)‖ ≤ L) :
    ‖aeval B p‖ ≤ L := by
  have heig (i : I) : |hB.eigenvalues i| ≤ ‖B‖ := by
    have hd := aeval_diagonalization B hB (X : Polynomial ℂ)
    simp only [Polynomial.aeval_X, Polynomial.eval_X] at hd
    have hn : ‖B‖ = ‖fun j : I => (hB.eigenvalues j : ℂ)‖ := by
      conv_lhs => rw [hd]
      change ‖(hB.eigenvectorUnitary : Matrix I I ℂ) *
        Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) *
          (star hB.eigenvectorUnitary : unitary (Matrix I I ℂ))‖ = _
      rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    have h := norm_le_pi_norm (fun j : I => (hB.eigenvalues j : ℂ)) i
    rw [← hn] at h
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  rw [aeval_diagonalization B hB p]
  change ‖(hB.eigenvectorUnitary : Matrix I I ℂ) *
    Matrix.diagonal (fun i => p.eval (hB.eigenvalues i : ℂ)) *
      (star hB.eigenvectorUnitary : unitary (Matrix I I ℂ))‖ ≤ L
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hL).mpr
  intro i
  exact hb _ (heig i)

/-- A Lipschitz bound for a polynomial on an interval containing the spectrum bounds the matrix
evaluation of its secant polynomial. -/
theorem norm_secant_le (B : Matrix I I ℂ) (hB : B.IsHermitian) (p : Polynomial ℂ)
    (M a : ℝ) (L : ℝ≥0) (hM : ‖B‖ ≤ M) (ha : a ∈ Ioo (-M) M)
    (hl : LipschitzOnWith L (fun y : ℝ => p.eval (y : ℂ)) (Icc (-M) M)) :
    ‖aeval B (secant p (a : ℂ))‖ ≤ (L : ℝ) := by
  apply norm_aeval_le B hB _ L L.2
  intro x hx
  exact eval_bound p M a x L ha (abs_le.mp (hx.trans hM)) hl

end Qatlib.Papers.CommutLCHS26.MainResults.PolynomialSecant
