/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2: the PAR bit law

Source: arXiv:1605.03590v2, Appendix B, Lemma 2 (pp.11--12, Eqs. (B6)--(B7)).

The protocol replaces each controlled rotation by the conditional `U`/`U†` gadget of
Fig. 6.  On an eigenvector `U|φ⟩ = e^{iφ}|φ⟩`, one gadget contributes the relative
phase `φ` on the ancilla branches; with the per-rotation phase `θ` included, `M`
repetitions accumulate the relative phase `M(φ+θ)`.  After the final Hadamard and
measurement of the ancilla, the paper obtains (Eq. (B7), with `θ - φ ↦ θ + φ` in
the chosen orientation)

`P(0 | φ; θ, M) = (1 + cos(2 M [φ + θ])) / 2`.

We model the ancilla branches by their accumulated phases and the final Hadamard
amplitudes `(z₀ + z₁)/2`, `(z₀ - z₁)/2`, and prove the exact Born law, including
normalization.  The branch-phase accumulation is proved from `Complex.exp_nat_mul`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- Phase accumulated on the two ancilla branches after `M` applications of the
conditional-`U`/`U†` gadget, each carrying the relative phase `φ + θ`
(Eqs. (B6)--(B7)). -/
noncomputable def parBranchPhase (φ θ : ℝ) (M : ℕ) (b : Bool) : ℂ :=
  if b then (Complex.exp (-(Complex.I * (φ + θ)))) ^ M
  else (Complex.exp (Complex.I * (φ + θ))) ^ M

/-- The two ancilla branch phases are the `M`-th powers of the single-step phases
`e^{i(φ+θ)}` and `e^{-i(φ+θ)}`. -/
theorem parBranchPhase_false (φ θ : ℝ) (M : ℕ) :
    parBranchPhase φ θ M false =
      Complex.exp (Complex.I * ((M : ℝ) * (φ + θ))) := by
  simp only [parBranchPhase, Bool.false_eq_true, if_false]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The `true` branch is the conjugate (inverse) phase of the `false` branch. -/
theorem parBranchPhase_true (φ θ : ℝ) (M : ℕ) :
    parBranchPhase φ θ M true =
      Complex.exp (-(Complex.I * ((M : ℝ) * (φ + θ)))) := by
  simp only [parBranchPhase, if_true]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Ancilla amplitudes after the final Hadamard (Eq. (B7)).  With
`A = M(φ + θ)`, the outcome-0 amplitude is `cos A` and the outcome-1 amplitude is
`i sin A`. -/
noncomputable def parAmplitude (φ θ : ℝ) (M : ℕ) : Bool → ℂ :=
  fun b =>
    if b then Complex.I * Complex.sin ((M : ℝ) * (φ + θ))
    else Complex.cos ((M : ℝ) * (φ + θ))

/-- The amplitudes in `parAmplitude` are exactly the Hadamard transform of the two
accumulated branch phases, as in Eq. (B7). -/
theorem parAmplitude_eq_hadamard (φ θ : ℝ) (M : ℕ) :
    parAmplitude φ θ M false =
        (parBranchPhase φ θ M false + parBranchPhase φ θ M true) / 2 ∧
    parAmplitude φ θ M true =
        (parBranchPhase φ θ M false - parBranchPhase φ θ M true) / 2 := by
  let A : ℂ := ((φ : ℂ) + (θ : ℂ)) * (M : ℂ)
  have hA : ((M : ℝ) * (φ + θ) : ℂ) = A := by
    simp [A, mul_comm]
  have hfalse : parBranchPhase φ θ M false = Complex.exp (A * Complex.I) := by
    simpa [hA, mul_comm] using parBranchPhase_false φ θ M
  have htrue : parBranchPhase φ θ M true = Complex.exp (-(A * Complex.I)) := by
    simpa [hA, mul_comm] using parBranchPhase_true φ θ M
  constructor
  · rw [parAmplitude, hA, hfalse, htrue]
    simp only [Bool.false_eq_true, if_false]
    rw [Complex.exp_mul_I, ← neg_mul, ← Complex.cos_sub_sin_I]
    ring
  · rw [parAmplitude, hA, hfalse, htrue]
    simp only [if_true]
    rw [Complex.exp_mul_I, ← neg_mul, ← Complex.cos_sub_sin_I]
    ring

/-- arXiv:1605.03590v2, Lemma 2 (p.11): the probability that the PAR protocol outputs
`0` after `M` rotations, given the eigenphase `φ` and shift `θ`, is
`(1 + cos(2M[φ + θ])) / 2`; the complementary outcome has probability
`(1 - cos(2M[φ + θ])) / 2`, and the two sum to one. -/
theorem lemma2_par_bit_law (φ θ : ℝ) (M : ℕ) :
    Complex.normSq (parAmplitude φ θ M false) =
        (1 + Real.cos (2 * (M : ℝ) * (φ + θ))) / 2 ∧
    Complex.normSq (parAmplitude φ θ M true) =
        (1 - Real.cos (2 * (M : ℝ) * (φ + θ))) / 2 ∧
    Complex.normSq (parAmplitude φ θ M false) +
        Complex.normSq (parAmplitude φ θ M true) = 1 := by
  have hA : ((M : ℂ) * ((φ : ℂ) + (θ : ℂ))) = (((M : ℝ) * (φ + θ) : ℝ) : ℂ) := by
    push_cast
    ring_nf
  have hcos : Complex.normSq (Complex.cos ((M : ℂ) * ((φ : ℂ) + (θ : ℂ)))) =
      (1 + Real.cos (2 * (M : ℝ) * (φ + θ))) / 2 := by
    rw [hA, ← Complex.ofReal_cos, Complex.normSq_ofReal, ← sq, Real.cos_sq]
    ring_nf
  have hsin : Complex.normSq (Complex.I * Complex.sin ((M : ℂ) * ((φ : ℂ) + (θ : ℂ)))) =
      (1 - Real.cos (2 * (M : ℝ) * (φ + θ))) / 2 := by
    rw [hA, Complex.normSq_mul, Complex.normSq_I, one_mul, ← Complex.ofReal_sin,
      Complex.normSq_ofReal, ← sq, Real.sin_sq, Real.cos_sq]
    ring_nf
  have hnorm : Complex.normSq (Complex.cos ((M : ℂ) * ((φ : ℂ) + (θ : ℂ)))) +
      Complex.normSq (Complex.I * Complex.sin ((M : ℂ) * ((φ : ℂ) + (θ : ℂ)))) = 1 := by
    rw [hcos, hsin]
    ring_nf
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast, parAmplitude, Bool.false_eq_true, if_false] using hcos
  · simpa only [Complex.ofReal_natCast, parAmplitude, if_true] using hsin
  · simpa only [Complex.ofReal_natCast, parAmplitude, Bool.false_eq_true, if_false, if_true] using hnorm

end Qatlib.Papers.ReactionMech16.MainResults.Source
