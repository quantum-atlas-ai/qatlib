/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel.SourceCSPModel

set_option backward.isDefEq.respectTransparency false

/-!
# The QAOA state and its computational-basis measurement law

Lin--Zhu, fixed arXiv:1601.01744v1.  Equations (2.4)--(2.6) on p.4 define

* `|s⟩` the uniform superposition,
* `|γ,β⟩ = e^{-iβB} e^{-iγC} |s⟩` with `B = ∑_i X_i`,
* the objective `C` diagonal in the computational basis with eigenvalue `C(z)`,
* the measurement distribution in the computational basis.

The transverse-field factor is written in its exact product form
`e^{-iβB} = ∏_i (cos β · I - i sin β · X_i)`, which is the standard identity used
by QAOA (all `X_i` commute).  The phase factor is diagonal.  This gives a
concrete amplitude, not a freely chosen output distribution.

The last theorem converts any lower bound on the expected satisfied fraction
into an actual output assignment; this is the finite-distribution (Markov)
step that the paper leaves implicit when it says QAOA "finds an assignment".

Boundary: the analytic QAOA expectation lower bounds of Sections 4--5 are not
proved here; they are stated in the claim files.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState

open Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Amplitudes on the computational basis. -/
abbrev Amp (V : Type) := (V → Bool) → ℂ

/-- Flip one coordinate of an assignment. -/
def flipAt (v : V) (z : V → Bool) : V → Bool :=
  Function.update z v (!z v)

/-- Flipping the same coordinate twice is the identity. -/
theorem flipAt_involutive (v : V) : Function.Involutive (flipAt v) := by
  intro z
  funext w
  by_cases h : w = v
  · subst h
    simp [flipAt, Function.update_self]
  · simp [flipAt, Function.update_of_ne h]

/-- A sum over the cube is invariant under flipping one coordinate. -/
theorem sum_flipAt (f : (V → Bool) → ℝ) (v : V) :
    (∑ z : V → Bool, f (flipAt v z)) = ∑ z : V → Bool, f z := by
  refine Finset.sum_bij (fun z _ => flipAt v z) (fun z _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro a _ b _ hab
    have h1 : flipAt v (flipAt v a) = a := flipAt_involutive v a
    have h2 : flipAt v (flipAt v b) = b := flipAt_involutive v b
    have h3 := congrArg (flipAt v) hab
    rw [h1, h2] at h3
    exact h3
  · intro b _
    exact ⟨flipAt v b, Finset.mem_univ _, flipAt_involutive v b⟩
  · intro a _
    rfl

/-- The uniform superposition `|s⟩` of (2.4). -/
def uniformAmp : Amp V :=
  fun _ => (1 / Real.sqrt (Fintype.card (V → Bool)) : ℂ)

/-- One phase-separation factor `e^{-iγC}`; `C` is diagonal with eigenvalue
`C(z) = satValue X z` (equation (2.5)). -/
def phaseStep (X : CSPInstance V) (γ : ℝ) (ψ : Amp V) : Amp V :=
  fun z => Complex.exp (-(γ : ℂ) * Complex.I * (satValue X z : ℂ)) * ψ z

/-- One single-qubit mixer factor `cos β · I - i sin β · X_v` from the exact
product form of `e^{-iβB}`. -/
def mixerStep (β : ℝ) (v : V) (ψ : Amp V) : Amp V :=
  fun z => (Real.cos β : ℂ) * ψ z - Complex.I * (Real.sin β : ℂ) * ψ (flipAt v z)

/-- The product of the single-qubit mixer factors over all qubits.  The order
of the fold is immaterial because the factors commute. -/
def mixer (β : ℝ) (ψ : Amp V) : Amp V :=
  (List.finRange (Fintype.card V)).foldl
    (fun φ i => mixerStep β ((Fintype.equivFin V).symm i) φ) ψ

/-- The QAOA state `|γ,β⟩ = e^{-iβB} e^{-iγC} |s⟩` of (2.5). -/
def qaoaState (X : CSPInstance V) (γ β : ℝ) : Amp V :=
  mixer β (phaseStep X γ uniformAmp)

/-- Computational-basis measurement probability `|⟨z|γ,β⟩|²`. -/
def qaoaProb (X : CSPInstance V) (γ β : ℝ) (z : V → Bool) : ℝ :=
  Complex.normSq (qaoaState X γ β z)

/-- Measurement probabilities are nonnegative. -/
theorem qaoaProb_nonneg (X : CSPInstance V) (γ β : ℝ) (z : V → Bool) :
    0 ≤ qaoaProb X γ β z :=
  Complex.normSq_nonneg _

/-- Expected total number of satisfied constraints under the QAOA measurement,
i.e. `⟨γ,β| C |γ,β⟩` of (2.6). -/
def qaoaExpectedValue (X : CSPInstance V) (γ β : ℝ) : ℝ :=
  ∑ z : V → Bool, qaoaProb X γ β z * satValue X z

/-- Expected satisfied fraction `⟨γ,β| C |γ,β⟩ / m`. -/
def qaoaExpectedFraction (X : CSPInstance V) (γ β : ℝ) : ℝ :=
  qaoaExpectedValue X γ β / (X.m : ℝ)

/-- Pointwise expansion of the squared norm of one mixer step
`c·w - i·s·w'`; the cross term is the imaginary part of `w * conj w'`. -/
lemma normSq_mixer_expand (c s : ℝ) (w w' : ℂ) :
    Complex.normSq ((c : ℂ) * w - Complex.I * (s : ℂ) * w')
      = c^2 * Complex.normSq w + s^2 * Complex.normSq w'
        + 2 * c * s * (w.re * w'.im - w.im * w'.re) := by
  rw [show (c : ℂ) * w - Complex.I * (s : ℂ) * w'
        = (c : ℂ) * w + (-(Complex.I * (s : ℂ) * w')) by ring]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- One phase-separation step preserves the total squared norm. -/
lemma sum_normSq_phaseStep (X : CSPInstance V) (γ : ℝ) (ψ : Amp V) :
    (∑ z, Complex.normSq (phaseStep X γ ψ z)) = ∑ z, Complex.normSq (ψ z) := by
  apply Finset.sum_congr rfl
  intro z _
  unfold phaseStep
  rw [Complex.normSq_mul]
  have h : Complex.normSq (Complex.exp (-(γ : ℂ) * Complex.I * (satValue X z : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have harg : -(γ : ℂ) * Complex.I * (satValue X z : ℂ)
        = Complex.I * ((-(γ * satValue X z) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [h, one_mul]

/-- One single-qubit mixer step preserves the total squared norm. -/
lemma sum_normSq_mixerStep (β : ℝ) (v : V) (ψ : Amp V) :
    (∑ z, Complex.normSq (mixerStep β v ψ z)) = ∑ z, Complex.normSq (ψ z) := by
  simp only [mixerStep]
  have hpoint : ∀ z, Complex.normSq
      ((Real.cos β : ℂ) * ψ z - Complex.I * (Real.sin β : ℂ) * ψ (flipAt v z))
      = Real.cos β^2 * Complex.normSq (ψ z) + Real.sin β^2 * Complex.normSq (ψ (flipAt v z))
        + 2 * Real.cos β * Real.sin β *
            ((ψ z).re * (ψ (flipAt v z)).im - (ψ z).im * (ψ (flipAt v z)).re) :=
    fun z => normSq_mixer_expand _ _ _ _
  let f : (V → Bool) → ℝ := fun z =>
    (ψ z).re * (ψ (flipAt v z)).im - (ψ z).im * (ψ (flipAt v z)).re
  have hf : ∀ z, f (flipAt v z) = - f z := by
    intro z
    simp only [f]
    rw [flipAt_involutive v z]
    ring
  have hfsum : (∑ z, f (flipAt v z)) = - ∑ z, f z := by
    calc (∑ z, f (flipAt v z)) = ∑ z, - f z := Finset.sum_congr rfl fun z _ => hf z
      _ = - ∑ z, f z := by
            simpa using (Finset.sum_neg_distrib (s := Finset.univ) (f := f))
  have hflip := sum_flipAt f v
  have hcross : (∑ z, f z) = 0 := by
    rw [hfsum] at hflip
    linarith
  calc
    (∑ z, Complex.normSq ((Real.cos β : ℂ) * ψ z
        - Complex.I * (Real.sin β : ℂ) * ψ (flipAt v z)))
        = ∑ z, (Real.cos β^2 * Complex.normSq (ψ z)
            + Real.sin β^2 * Complex.normSq (ψ (flipAt v z))
            + 2 * Real.cos β * Real.sin β * f z) :=
          Finset.sum_congr rfl fun z _ => hpoint z
    _ = Real.cos β^2 * (∑ z, Complex.normSq (ψ z))
          + Real.sin β^2 * (∑ z, Complex.normSq (ψ (flipAt v z)))
          + 2 * Real.cos β * Real.sin β * (∑ z, f z) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
    _ = Real.cos β^2 * (∑ z, Complex.normSq (ψ z))
          + Real.sin β^2 * (∑ z, Complex.normSq (ψ z)) + 0 := by
        rw [sum_flipAt (fun z => Complex.normSq (ψ z)) v, hcross, mul_zero]
    _ = ∑ z, Complex.normSq (ψ z) := by
        rw [← add_mul, Real.cos_sq_add_sin_sq, one_mul, add_zero]

/-- The full mixer, a product of single-qubit steps, preserves the total
squared norm. -/
lemma sum_normSq_mixer (β : ℝ) (ψ : Amp V) :
    (∑ z, Complex.normSq (mixer β ψ z)) = ∑ z, Complex.normSq (ψ z) := by
  unfold mixer
  induction (List.finRange (Fintype.card V)) generalizing ψ with
  | nil => simp
  | cons i L ih =>
    simp only [List.foldl_cons]
    rw [ih (mixerStep β ((Fintype.equivFin V).symm i) ψ)]
    exact sum_normSq_mixerStep β ((Fintype.equivFin V).symm i) ψ

/-- Measurement probabilities sum to one.

Source: arXiv:1601.01744v1, (2.4)--(2.5), p.4.  The phase factor has unit
modulus and every mixer factor is a unitary because `X_v` is an involutive
permutation of the computational basis.  Hence `e^{-iβB}e^{-iγC}|s⟩` is a unit
vector and the squared amplitudes sum to one.

Proved by the norm-preservation lemmas above: `sum_normSq_phaseStep` for the
diagonal phase, `sum_normSq_mixerStep` for one mixer factor (the cross term
cancels under `z ↦ flipAt v z`), and `sum_normSq_mixer` for the fold. -/
theorem qaoaProb_sum_one (X : CSPInstance V) (γ β : ℝ) :
    (∑ z : V → Bool, qaoaProb X γ β z) = 1 := by
  unfold qaoaProb qaoaState
  rw [sum_normSq_mixer, sum_normSq_phaseStep]
  simp only [uniformAmp]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card (V → Bool) := by
    exact_mod_cast Fintype.card_pos (α := V → Bool)
  have hval : (1 / ((Real.sqrt (Fintype.card (V → Bool)) : ℝ) : ℂ))
      = ((1 / Real.sqrt (Fintype.card (V → Bool)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hval, Complex.normSq_ofReal]
  rw [show (1 / Real.sqrt (Fintype.card (V → Bool))) * (1 / Real.sqrt (Fintype.card (V → Bool)))
        = 1 / (Real.sqrt (Fintype.card (V → Bool)))^2 by ring]
  rw [Real.sq_sqrt hcard.le]
  field_simp

/-- Any finite probability law has an atom of positive mass. -/
theorem exists_positive_of_sum_one {f : (V → Bool) → ℝ}
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∑ z, f z = 1) : ∃ z, 0 < f z := by
  by_contra h
  push_neg at h
  have hle : ∑ z : V → Bool, f z ≤ 0 :=
    Finset.sum_nonpos fun z _ => h z
  linarith

/-- Markov step for a finite measurement law: some output of positive
probability has objective value at least the expected objective. -/
theorem exists_output_ge_expect (X : CSPInstance V) (γ β : ℝ)
    (h0 : ∀ z, 0 ≤ qaoaProb X γ β z)
    (h1 : ∑ z : V → Bool, qaoaProb X γ β z = 1) :
    ∃ z : V → Bool,
      0 < qaoaProb X γ β z ∧ qaoaExpectedValue X γ β ≤ satValue X z := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `hcon z : 0 < qaoaProb X γ β z → satValue X z < qaoaExpectedValue X γ β`
  have hterm_le : ∀ z, qaoaProb X γ β z * satValue X z ≤
      qaoaProb X γ β z * qaoaExpectedValue X γ β := by
    intro z
    rcases eq_or_lt_of_le (h0 z) with hz | hz
    · rw [← hz]; simp
    · exact mul_le_mul_of_nonneg_left (hcon z hz).le (h0 z)
  obtain ⟨z₀, hz₀⟩ := exists_positive_of_sum_one h0 h1
  have hstrict : qaoaProb X γ β z₀ * satValue X z₀ <
      qaoaProb X γ β z₀ * qaoaExpectedValue X γ β :=
    mul_lt_mul_of_pos_left (hcon z₀ hz₀) hz₀
  have hsum_lt : (∑ z : V → Bool, qaoaProb X γ β z * satValue X z) <
      ∑ z : V → Bool, qaoaProb X γ β z * qaoaExpectedValue X γ β := by
    refine Finset.sum_lt_sum (fun z _ => hterm_le z) ⟨z₀, Finset.mem_univ _, hstrict⟩
  have hRHS : (∑ z : V → Bool, qaoaProb X γ β z * qaoaExpectedValue X γ β)
      = qaoaExpectedValue X γ β := by
    rw [← Finset.sum_mul, h1, one_mul]
  have hLHS : (∑ z : V → Bool, qaoaProb X γ β z * satValue X z)
      = qaoaExpectedValue X γ β := rfl
  rw [hLHS, hRHS] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-- If a lower bound on the expected satisfied fraction is available, then an
output assignment of positive probability attains at least that fraction.
This is the formal reading of "there is a quantum algorithm which finds an
assignment satisfying ..." (Theorems 2, 3, Lemma 4, Corollaries 5 and 7). -/
theorem exists_output_ge_fraction (X : CSPInstance V) (γ β : ℝ) (r : ℝ)
    (h0 : ∀ z, 0 ≤ qaoaProb X γ β z)
    (h1 : ∑ z : V → Bool, qaoaProb X γ β z = 1)
    (h : r ≤ qaoaExpectedFraction X γ β) :
    ∃ z : V → Bool, 0 < qaoaProb X γ β z ∧ r ≤ satFraction X z := by
  obtain ⟨z, hzpos, hzval⟩ := exists_output_ge_expect X γ β h0 h1
  refine ⟨z, hzpos, ?_⟩
  have hm : (0 : ℝ) < (X.m : ℝ) := by exact_mod_cast X.hm
  have hmul : r * (X.m : ℝ) ≤ qaoaExpectedValue X γ β := by
    have h' := mul_le_mul_of_nonneg_right h hm.le
    rw [qaoaExpectedFraction, div_mul_cancel₀ _ hm.ne'] at h'
    exact h'
  calc
    r = r * (X.m : ℝ) / (X.m : ℝ) := by field_simp [hm.ne']
    _ ≤ satValue X z / (X.m : ℝ) := by
      exact div_le_div_of_nonneg_right (hmul.trans hzval) hm.le
    _ = satFraction X z := rfl

end Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState
