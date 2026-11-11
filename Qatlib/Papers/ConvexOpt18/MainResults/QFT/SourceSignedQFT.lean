/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceConvexModel

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 signed quantum Fourier transform (Lemma B.1)

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3, Appendix B, Lemma B.1
(pp. 41--42, equations (B.3)--(B.5)).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Lemma B.1 (p. 41): for even `N`, `QFT_G^{-1} = e^{-πiN/2} · (U QFT_N^{-1} U)`, where `U`
is the diagonal unitary `U|x⟩ = e^{πix}|x⟩` (a tensor product of single-qubit unitaries) and
`QFT_G^{-1}` is the inverse QFT over the signed range `G = {-N/2, …, N/2-1}`.

Matrix form of equations (B.4)--(B.5): the exponent identity
`γ(x)γ(y) = xy - (N/2)(x+y) + N²/4` gives
`e^{-2πiγ(x)γ(y)/N} = e^{-πiN/2} · e^{πix} · e^{-2πixy/N} · e^{πiy}`. -/
theorem source_lemma_B_1 (N : ℕ) (hN : 0 < N) (hEven : 2 * (N / 2) = N) :
    qftGInv N =
      Complex.exp (-(Real.pi * Complex.I * (N : ℂ) / 2)) •
        (Matrix.diagonal (fun x : Fin N => Complex.exp (Real.pi * Complex.I * (x.val : ℂ))) *
          qftInv N *
          Matrix.diagonal (fun x : Fin N => Complex.exp (Real.pi * Complex.I * (x.val : ℂ)))) := by
  have hN2 : ((N / 2 : ℕ) : ℂ) = (N : ℂ) / 2 := by
    have h2 : ((2 * (N / 2) : ℕ) : ℂ) = (N : ℂ) := by rw [hEven]
    push_cast at h2
    linear_combination h2 / 2
  have hdivZ : ((N : ℤ) / 2) = ((N / 2 : ℕ) : ℤ) := by omega
  have hx : ∀ x : Fin N, (gamma N x : ℂ) = (x.val : ℂ) - (N : ℂ) / 2 := by
    intro x
    rw [gamma]
    push_cast
    rw [hdivZ, Int.cast_natCast, hN2]
  ext x y
  rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [qftGInv, qftInv, smul_eq_mul]
  rw [hx x, hx y]
  have hexp :
      -(2 * Real.pi * Complex.I * ((x.val : ℂ) - (N : ℂ) / 2) *
          ((y.val : ℂ) - (N : ℂ) / 2) / (N : ℂ))
        = -(Real.pi * Complex.I * (N : ℂ) / 2) + Real.pi * Complex.I * (x.val : ℂ)
          + -(2 * Real.pi * Complex.I * (x.val : ℂ) * (y.val : ℂ) / (N : ℂ))
          + Real.pi * Complex.I * (y.val : ℂ) := by
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    field_simp
    ring
  rw [hexp]
  simp only [Complex.exp_add]
  ring

end Qatlib.Papers.ConvexOpt18.MainResults
