/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.ZeroMarginCanonicalComplementComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.DeflatedSchwarzAndFilterComp

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-! Source: Berntson and Sünderhauf, *Complementary polynomials in quantum signal
processing*, arXiv:2406.04246v2 (CMP 406, 161 (2025)), Corollary 2.1 and its proof
in §2.2.

Corollary 2.1 states that when `P` is a real polynomial satisfying the
assumptions of Problem 1, the canonical complementary polynomial is real up to a
multiplicative phase. The canonical complement used here is the frozen
`BoundaryCanon` normalization: the complement of degree at most `d`, exact
complementarity on the unit circle, no zero inside the disk, and a positive real
value at zero (with the saturated zero complement kept as its own branch). That
normalization picks the phase, so the canonical complement has real coefficients
outright, and every open-disk-zero-free solution of Problem 1 is a unit multiple
of it. -/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CompQSPBernt25.MainResults

open Polynomial
open Qatlib.Concepts.LaurentPolys.BoundaryCanon

/-- Conjugating the coefficients of a complex polynomial evaluates at the
conjugate point: `conj P z = conj (P (conj z))`. -/
theorem eval_map_conj (p : Polynomial ℂ) (z : ℂ) :
    (p.map (starRingEnd ℂ)).eval z = star (p.eval (star z)) := by
  simpa using (Polynomial.eval_map_apply (f := starRingEnd ℂ) (p := p) (star z))

/-- A polynomial with conjugate-symmetric coefficients takes conjugate values at
conjugate points. -/
theorem eval_star_of_map_conj_eq (p : Polynomial ℂ) (hp : p.map (starRingEnd ℂ) = p)
    (z : ℂ) : p.eval (star z) = star (p.eval z) := by
  have h := eval_map_conj p (star z)
  rw [hp, star_star] at h
  exact h

/-- Conjugating the coefficients of a complement preserves canonicality for a
real input: the normalized complement of a real polynomial has a conjugate
canonical complement. -/
theorem boundaryCanonical_map_conj (P Q : Polynomial ℂ) (d : ℕ)
    (hP : P.map (starRingEnd ℂ) = P) (hQ : BoundaryCanonical P Q d) :
    BoundaryCanonical P (Q.map (starRingEnd ℂ)) d := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hQ.1
  · intro z hz
    have hzc : ‖star z‖ = 1 := by simpa using hz
    have hmod : ‖P.eval z‖ = ‖P.eval (star z)‖ := by
      rw [eval_star_of_map_conj_eq P hP z, norm_star]
    rw [eval_map_conj, norm_star, hmod]
    exact hQ.2.1 (star z) hzc
  · rcases hQ.2.2 with h0 | ⟨hr, hi, hn⟩
    · exact Or.inl (by rw [h0, Polynomial.map_zero])
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [eval_map_conj]
        simp only [star_zero, Complex.star_def, Complex.conj_re]
        exact hr
      · rw [eval_map_conj]
        simp only [star_zero, Complex.star_def, Complex.conj_im, neg_eq_zero]
        exact hi
      · intro z hz hz0
        have hzs : ‖star z‖ < 1 := by simpa using hz
        apply hn (star z) hzs
        have h := hz0
        rw [eval_map_conj] at h
        simpa using h

/-- Corollary 2.1, normalized form: the canonical complement of a real
polynomial has real coefficients. The canonical normalization fixes the free
multiplicative phase, so realness holds on the nose. -/
theorem boundaryCanonical_map_conj_eq_of_real_input (P Q : Polynomial ℂ) (d : ℕ)
    (hP : P.map (starRingEnd ℂ) = P) (hQ : BoundaryCanonical P Q d) :
    Q.map (starRingEnd ℂ) = Q :=
  boundaryCanonical_unique P Q (Q.map (starRingEnd ℂ)) d hQ
    (boundaryCanonical_map_conj P Q d hP hQ)

/-- Corollary 2.1, existence form: every real polynomial bounded by one on the
unit circle admits a real canonical complementary polynomial of degree at most
`d`. -/
theorem exists_real_boundaryCanonical (P : Polynomial ℂ) (d : ℕ)
    (hP : P.map (starRingEnd ℂ) = P) (hp : P.natDegree ≤ d)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ Q : Polynomial ℂ, BoundaryCanonical P Q d ∧ Q.map (starRingEnd ℂ) = Q := by
  obtain ⟨Q, hQ⟩ := boundaryCanonical_exists P d hp hb
  exact ⟨Q, hQ, boundaryCanonical_map_conj_eq_of_real_input P Q d hP hQ⟩

/-- Corollary 2.1, phase form: for real `P`, any solution of Problem 1 of degree
at most `d` without zeros in the open disk is a unit multiple of a real
polynomial, i.e. it is real up to a multiplicative phase. -/
theorem exists_phase_multiple_real_complement (P Q : Polynomial ℂ) (d : ℕ)
    (hP : P.map (starRingEnd ℂ) = P) (hdegP : P.natDegree ≤ d) (hdeg : Q.natDegree ≤ d)
    (hcomp : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2 + ‖Q.eval z‖^2 = 1)
    (hnz : ∀ z : ℂ, ‖z‖ < 1 → Q.eval z ≠ 0) :
    ∃ (c : ℂ) (R : Polynomial ℂ),
      ‖c‖ = 1 ∧ R.map (starRingEnd ℂ) = R ∧ Q = C c * R := by
  by_cases hQ0 : Q = 0
  · exact ⟨1, 0, by simp, by simp, by simp [hQ0]⟩
  have hbP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1 := by
    intro z hz
    nlinarith [hcomp z hz, norm_nonneg (P.eval z), norm_nonneg (Q.eval z)]
  obtain ⟨S, hS, hSreal⟩ := exists_real_boundaryCanonical P d hP hdegP hbP
  have hQz : Q.eval 0 ≠ 0 := hnz 0 (by simp)
  let c : ℂ := (‖Q.eval 0‖ : ℂ) / Q.eval 0
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hQz)
  have hc0 : c * Q.eval 0 = (‖Q.eval 0‖ : ℂ) := div_mul_cancel₀ _ hQz
  have hne : c ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hc
    norm_num at hc
  have hT : BoundaryCanonical P (C c * Q) d := by
    refine ⟨?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · exact (natDegree_mul_le).trans (by simp [hdeg])
    · intro z hz
      rw [eval_mul, eval_C, norm_mul, hc, one_mul]
      exact hcomp z hz
    · rw [eval_mul, eval_C, hc0, Complex.ofReal_re]
      exact norm_pos_iff.mpr hQz
    · rw [eval_mul, eval_C, hc0, Complex.ofReal_im]
    · intro z hz
      rw [eval_mul, eval_C]
      exact mul_ne_zero (norm_ne_zero_iff.mp (by rw [hc]; norm_num)) (hnz z hz)
  have hTS : C c * Q = S := boundaryCanonical_unique P S (C c * Q) d hS hT
  refine ⟨c⁻¹, S, ?_, hSreal, ?_⟩
  · rw [norm_inv, hc, inv_one]
  · rw [← hTS, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hne, C_1, one_mul]

end Qatlib.Papers.CompQSPBernt25.MainResults
