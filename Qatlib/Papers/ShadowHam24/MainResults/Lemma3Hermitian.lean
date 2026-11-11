/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowHam24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3 (arXiv:2407.21775, p. 13, Eq. (19))

If the system is finite-dimensional, the operators in `S` are orthogonal with
`tr(O_m^† O_{m'}) = λ δ_{mm'}` for some `λ > 0`, and the Hamiltonian `H` is
Hermitian, then the shadow Hamiltonian `H_S` (the matrix of IP coefficients) is
Hermitian.

Note: the printed statement of Lemma 3 does not explicitly say that `H` is
Hermitian, but its proof in Supplementary Note 1 uses `H^† = H` when taking the
Hermitian conjugate of `tr(O_m'^† [H,O_m])`.  Without that hypothesis the lemma
is false (a 2×2 counterexample with a non-Hermitian `H` produces a
non-Hermitian `H_S`), so we faithfully include `H.IsHermitian` as a necessary
assumption and record this in the docstring.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace Qatlib.Papers.ShadowHam24.MainResults

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

/-- Hermitian conjugation of the trace in Eq. (19): for Hermitian `H`,
`conj(tr(O_m^† [H,O_m'])) = tr(O_m'^† [H,O_m])`. -/
lemma star_trace_commutator (H : Matrix N N ℂ) (O : M → Matrix N N ℂ)
    (m m' : M) (hH : H.IsHermitian) :
    star (((O m)ᴴ * (H * O m' - O m' * H)).trace)
      = ((O m')ᴴ * (H * O m - O m * H)).trace := by
  rw [← Matrix.trace_conjTranspose]
  have h1 : (((O m)ᴴ * (H * O m' - O m' * H))ᴴ)
      = ((O m')ᴴ * H - H * (O m')ᴴ) * O m := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hH.eq]
  rw [h1, Matrix.sub_mul, Matrix.trace_sub]
  have a : (((O m')ᴴ * H) * O m).trace = ((O m')ᴴ * (H * O m)).trace := by
    rw [Matrix.mul_assoc]
  have b : ((H * (O m')ᴴ) * O m).trace = ((O m')ᴴ * (O m * H)).trace := by
    rw [trace_cycle3 H ((O m')ᴴ) (O m), Matrix.trace_mul_comm (O m * H) ((O m')ᴴ)]
  rw [a, b, ← Matrix.trace_sub, ← Matrix.mul_sub]

/-- **Lemma 3** (paper p. 13, Eq. (19)): under operator orthogonality with
`λ > 0`, Hermiticity of `H`, and the invariance property defining `H_S`, the
matrix `H_S` is Hermitian. -/
theorem shadowHamiltonian_isHermitian (H : Matrix N N ℂ) (O : M → Matrix N N ℂ)
    (hS : Matrix M M ℂ) (lam : ℂ)
    (hlam : ∃ r : ℝ, 0 < r ∧ lam = (r : ℂ))
    (horth : ∀ m m', ((O m)ᴴ * O m').trace = if m = m' then lam else 0)
    (hH : H.IsHermitian)
    (hip : InvarianceProperty H O hS) :
    hS.IsHermitian := by
  obtain ⟨r, hrpos, rfl⟩ := hlam
  have hne : (r : ℂ) ≠ 0 := by
    intro h
    have : r = 0 := Complex.ofReal_eq_zero.mp h
    linarith
  -- Under orthogonality, the IP coefficients equal the Eq. (19) formula.
  have hcoefficient : ∀ m m',
      hS m m' = -(1 / (r : ℂ)) * ((O m')ᴴ * (H * O m - O m * H)).trace := by
    intro m m'
    have hEq : ((O m')ᴴ * (H * O m - O m * H)).trace
        = - ∑ k, hS m k * ((O m')ᴴ * O k).trace := by
      rw [hip m, Matrix.mul_neg, Matrix.mul_sum, Matrix.trace_neg, Matrix.trace_sum]
      congr 1
      apply Finset.sum_congr rfl; intro k _
      rw [Matrix.mul_smul, Matrix.trace_smul]
      simp
    have hsum : (∑ k, hS m k * ((O m')ᴴ * O k).trace) = hS m m' * (r : ℂ) := by
      rw [Finset.sum_eq_single m']
      · rw [horth m' m']; simp
      · intro b _ hb
        rw [horth m' b]
        have hmb : m' ≠ b := fun h => hb h.symm
        simp [hmb]
      · intro h; exact absurd (Finset.mem_univ m') h
    rw [hEq, hsum]
    field_simp [hne]
  have h1 : star (1 / (r : ℂ)) = 1 / (r : ℂ) := by
    rw [one_div, star_inv₀]
    simp
  rw [Matrix.IsHermitian.ext_iff]
  intro m m'
  rw [hcoefficient m' m, hcoefficient m m']
  have hT := star_trace_commutator H O m m' hH
  rw [star_mul, star_neg, h1, hT]
  ring

end Qatlib.Papers.ShadowHam24.MainResults
