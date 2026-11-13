/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.Defs
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Coefficientwise orthogonal purification errors

The functions `purified` and `purifiedTilde` describe a state and its coefficientwise
perturbation, and `ptraceP` traces out the purification register. The orthogonality and
normalization hypotheses bound the trace distance between their reduced matrices. This
development supports the treatment in [TangWright2025].

## Main statements

* `purifiedTilde`: rescaled purification components with added errors.
* `ptraceP`: partial trace over the second register.
* `lemma32_orthogonal_errors`: reduced-state trace distance is at most `δ`.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped ComplexOrder
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.PurifErrors

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The bipartite vector whose coordinate `(i, p)` is the output coefficient `o i` times the
purification coefficient `φ i p`. -/
def purified {r q : ℕ} (o : Fin r → ℂ) (φ : Fin r → Fin q → ℂ) :
    Fin r × Fin q → ℂ :=
  fun p => o p.1 * φ p.1 p.2

/-- The perturbed bipartite vector obtained by rescaling each purification component by `α i`
and adding `err i` before multiplying by `o i`. -/
def purifiedTilde {r q : ℕ} (o : Fin r → ℂ) (φ : Fin r → Fin q → ℂ)
    (α : Fin r → ℂ) (err : Fin r → Fin q → ℂ) : Fin r × Fin q → ℂ :=
  fun p => o p.1 * (α p.1 * φ p.1 p.2 + err p.1 p.2)

/-- The reduced matrix obtained by tracing the outer product of a bipartite vector over its
second register. -/
def ptraceP {r q : ℕ} (ψ : Fin r × Fin q → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => ∑ p, ψ (i, p) * star (ψ (j, p))

/-- Under the stated orthonormality, error orthogonality, normalization, and coefficient bounds
`1 - δ ≤ ‖α i‖^2 ≤ 1`, the reduced-state trace distance is at most `δ` [Tang and Wright,
Lemma 3.2][TangWright2025]. -/
theorem lemma32_orthogonal_errors {r q : ℕ} (_hr : 0 < r)
    (o : Fin r → ℂ) (φ : Fin r → Fin q → ℂ) (α : Fin r → ℂ)
    (err : Fin r → Fin q → ℂ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hnorm : ∑ i : Fin r, ‖o i‖ ^ 2 = 1)
    (hnorm' : ∑ i : Fin r, ‖o i‖ ^ 2 * (‖α i‖ ^ 2 + ∑ p : Fin q, ‖err i p‖ ^ 2) = 1)
    (horth : ∀ i j : Fin r, ∑ p : Fin q, star (φ i p) * φ j p =
      if i = j then 1 else 0)
    (herr : ∀ i j : Fin r, ∑ p : Fin q, star (φ i p) * err j p = 0)
    (hα : ∀ i : Fin r, 1 - δ ≤ ‖α i‖ ^ 2)
    (hαle : ∀ i : Fin r, ‖α i‖ ^ 2 ≤ 1) :
    (1 / 2) * Matrix.traceNorm
      (ptraceP (purified o φ) -
        ptraceP (purifiedTilde o φ α err)) ≤ δ := by
  set W : Matrix (Fin r) (Fin q) ℂ := Matrix.of (fun i p => o i * err i p) with hWdef

  have hcast : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]

  have hconj : ∀ a b : Fin r, ∑ p : Fin q, φ a p * star (φ b p)
      = if a = b then 1 else 0 := by
    intro a b
    have hpt : ∀ p : Fin q, φ a p * star (φ b p) = star (star (φ a p) * φ b p) := by
      intro p
      rw [star_mul, star_star, mul_comm]
    rw [Finset.sum_congr rfl (fun p _ => hpt p), ← star_sum, horth a b]
    by_cases h : a = b <;> simp [h]
  have herr2 : ∀ a b : Fin r, ∑ p : Fin q, φ a p * star (err b p) = 0 := by
    intro a b
    have hpt : ∀ p : Fin q, φ a p * star (err b p) = star (star (φ a p) * err b p) := by
      intro p
      rw [star_mul, star_star, mul_comm]
    rw [Finset.sum_congr rfl (fun p _ => hpt p), ← star_sum, herr a b]
    simp
  have herr3 : ∀ a b : Fin r, ∑ p : Fin q, err a p * star (φ b p) = 0 := by
    intro a b
    have hpt : ∀ p : Fin q, err a p * star (φ b p) = star (φ b p * star (err a p)) := by
      intro p
      rw [star_mul, star_star]
    rw [Finset.sum_congr rfl (fun p _ => hpt p), ← star_sum, herr2 b a]
    simp

  have hM : ∀ i j : Fin r,
      (∑ p : Fin q, (o i * φ i p) * star (o j * φ j p))
        = if i = j then ((‖o i‖ ^ 2 : ℝ) : ℂ) else 0 := by
    intro i j
    have hpt : ∀ p : Fin q, (o i * φ i p) * star (o j * φ j p)
        = o i * star (o j) * (φ i p * star (φ j p)) := by
      intro p
      rw [star_mul]
      ring
    rw [Finset.sum_congr rfl (fun p _ => hpt p), ← Finset.mul_sum, hconj i j]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, mul_one, hcast (o i)]
    · rw [if_neg h, mul_zero, if_neg h]

  have hN : ∀ i j : Fin r,
      (∑ p : Fin q, (o i * (α i * φ i p + err i p))
          * star (o j * (α j * φ j p + err j p)))
        = (if i = j then ((‖o i‖ ^ 2 * ‖α i‖ ^ 2 : ℝ) : ℂ) else 0) + (W * Wᴴ) i j := by
    intro i j
    have hpt : ∀ p : Fin q,
        (o i * (α i * φ i p + err i p)) * star (o j * (α j * φ j p + err j p))
        = o i * star (o j) * (α i * star (α j)) * (φ i p * star (φ j p))
          + o i * star (o j) * (α i * (φ i p * star (err j p)))
          + o i * star (o j) * (star (α j) * (err i p * star (φ j p)))
          + o i * star (o j) * (err i p * star (err j p)) := by
      intro p
      simp only [star_mul, star_add]
      ring
    have hS1 : ∑ p : Fin q, o i * star (o j) * (α i * star (α j)) * (φ i p * star (φ j p))
        = if i = j then ((‖o i‖ ^ 2 * ‖α i‖ ^ 2 : ℝ) : ℂ) else 0 := by
      rw [← Finset.mul_sum, hconj i j]
      by_cases h : i = j
      · subst h
        rw [if_pos rfl, if_pos rfl, mul_one, hcast (o i), hcast (α i)]
        push_cast
        ring
      · rw [if_neg h, mul_zero, if_neg h]
    have hz2 : ∑ p : Fin q, α i * (φ i p * star (err j p)) = 0 := by
      have h : α i * ∑ p : Fin q, φ i p * star (err j p) = 0 := by
        rw [herr2 i j, mul_zero]
      rwa [Finset.mul_sum] at h
    have hS2 : ∑ p : Fin q, o i * star (o j) * (α i * (φ i p * star (err j p)))
        = 0 := by
      rw [← Finset.mul_sum, hz2, mul_zero]
    have hz3 : ∑ p : Fin q, star (α j) * (err i p * star (φ j p)) = 0 := by
      have h : star (α j) * ∑ p : Fin q, err i p * star (φ j p) = 0 := by
        rw [herr3 i j, mul_zero]
      rwa [Finset.mul_sum] at h
    have hS3 : ∑ p : Fin q, o i * star (o j) * (star (α j) * (err i p * star (φ j p)))
        = 0 := by
      rw [← Finset.mul_sum, hz3, mul_zero]
    have hS4 : ∑ p : Fin q, o i * star (o j) * (err i p * star (err j p))
        = (W * Wᴴ) i j := by
      have hWW : (W * Wᴴ) i j
          = ∑ p : Fin q, (o i * err i p) * star (o j * err j p) := by
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hWdef]
      rw [hWW]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [star_mul]
      ring
    rw [Finset.sum_congr rfl (fun p _ => hpt p)]
    simp only [Finset.sum_add_distrib]
    rw [hS1, hS2, hS3, hS4]
    ring

  have hID : ptraceP (purified o φ) - ptraceP (purifiedTilde o φ α err)
      = Matrix.diagonal (fun i => ((‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) : ℂ))
        - W * Wᴴ := by
    ext i j
    have hL : (ptraceP (purified o φ) - ptraceP (purifiedTilde o φ α err)) i j
        = (if i = j then ((‖o i‖ ^ 2 : ℝ) : ℂ) else 0)
          - ((if i = j then ((‖o i‖ ^ 2 * ‖α i‖ ^ 2 : ℝ) : ℂ) else 0)
            + (W * Wᴴ) i j) := by
      simp only [Matrix.sub_apply, ptraceP, purified, purifiedTilde]
      rw [hM i j, hN i j]
    rw [hL]
    by_cases h : i = j
    · subst h
      simp [Matrix.sub_apply]
      ring
    · simp only [Matrix.sub_apply, Matrix.diagonal_apply, if_neg h, zero_add]

  have hc : ∀ i : Fin r, 0 ≤ (‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) := fun i =>
    mul_nonneg (sq_nonneg (‖o i‖)) (by linarith [hαle i])
  have hpsd1 : (Matrix.diagonal (fun i : Fin r =>
      ((‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => Complex.le_def.mpr ⟨hc i, by
      simp only [Complex.ofReal_im]; simp⟩)
  have hpsd2 : (W * Wᴴ).PosSemidef := by
    simpa using! Matrix.posSemidef_conjTranspose_mul_self (Wᴴ)
  have htN1 : Matrix.traceNorm
      (Matrix.diagonal (fun i : Fin r => ((‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) : ℂ)))
      = ((Matrix.diagonal (fun i : Fin r =>
          ((‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) : ℂ))).trace).re := by
    have h := hpsd1.traceNorm_eq_trace
    simpa [Complex.ofReal_re] using! congrArg Complex.re h
  have htN2 : Matrix.traceNorm (W * Wᴴ) = ((W * Wᴴ).trace).re := by
    have h := hpsd2.traceNorm_eq_trace
    simpa [Complex.ofReal_re] using! congrArg Complex.re h

  have hb1 : ((Matrix.diagonal (fun i : Fin r =>
      ((‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) : ℂ))).trace).re ≤ δ := by
    have hcs : (Matrix.diagonal (fun i : Fin r =>
          ((‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) : ℂ))).trace
        = ((∑ i : Fin r, ‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2) : ℝ) : ℂ) := by
      rw [Matrix.trace_diagonal, Complex.ofReal_sum]
    rw [hcs, Complex.ofReal_re]
    calc ∑ i : Fin r, ‖o i‖ ^ 2 * (1 - ‖α i‖ ^ 2)
        ≤ ∑ i : Fin r, ‖o i‖ ^ 2 * δ :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by linarith [hα i]) (sq_nonneg (‖o i‖))
      _ = δ * ∑ i : Fin r, ‖o i‖ ^ 2 := by
          rw [Finset.sum_congr rfl (fun i _ => mul_comm (‖o i‖ ^ 2) δ), ← Finset.mul_sum]
      _ = δ := by rw [hnorm, mul_one]
  have hb2 : ((W * Wᴴ).trace).re ≤ δ := by
    have htr : (W * Wᴴ).trace
        = ∑ i : Fin r, ∑ p : Fin q, (o i * err i p) * star (o i * err i p) := by
      simp only [hWdef, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.of_apply]
    have hcs : (W * Wᴴ).trace
        = ((∑ i : Fin r, ∑ p : Fin q, ‖o i * err i p‖ ^ 2 : ℝ) : ℂ) := by
      rw [htr, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun p _ => hcast _
    have hsplit2 : ∀ i : Fin r, ∑ p : Fin q, ‖o i * err i p‖ ^ 2
        = ‖o i‖ ^ 2 * ∑ p : Fin q, ‖err i p‖ ^ 2 := by
      intro i
      have hpt : ∀ p : Fin q, ‖o i * err i p‖ ^ 2 = ‖o i‖ ^ 2 * ‖err i p‖ ^ 2 := by
        intro p
        rw [Complex.norm_mul, mul_pow]
      rw [Finset.sum_congr rfl (fun p _ => hpt p), ← Finset.mul_sum]
    rw [hcs, Complex.ofReal_re, Finset.sum_congr rfl (fun i _ => hsplit2 i)]
    have hlower : (1 - δ) * ∑ i : Fin r, ‖o i‖ ^ 2
        ≤ ∑ i : Fin r, ‖o i‖ ^ 2 * ‖α i‖ ^ 2 := by
      calc (1 - δ) * ∑ i : Fin r, ‖o i‖ ^ 2
          = ∑ i : Fin r, ‖o i‖ ^ 2 * (1 - δ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
        _ ≤ ∑ i : Fin r, ‖o i‖ ^ 2 * ‖α i‖ ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hα i) (sq_nonneg (‖o i‖))
    rw [hnorm, mul_one] at hlower
    have hident : ∑ i : Fin r, ‖o i‖ ^ 2 * ∑ p : Fin q, ‖err i p‖ ^ 2
        + ∑ i : Fin r, ‖o i‖ ^ 2 * ‖α i‖ ^ 2
        = ∑ i : Fin r, ‖o i‖ ^ 2 * (‖α i‖ ^ 2 + ∑ p : Fin q, ‖err i p‖ ^ 2) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith

  have hfinal : Matrix.traceNorm (ptraceP (purified o φ)
      - ptraceP (purifiedTilde o φ α err)) ≤ 2 * δ := by
    rw [hID, sub_eq_add_neg]
    refine le_trans (Matrix.traceNorm_add_le _ _) ?_
    rw [Matrix.traceNorm_neg, htN1, htN2]
    linarith
  calc (1 / 2 : ℝ) * Matrix.traceNorm (ptraceP (purified o φ)
      - ptraceP (purifiedTilde o φ α err))
      ≤ (1 / 2 : ℝ) * (2 * δ) := mul_le_mul_of_nonneg_left hfinal (by norm_num)
    _ = δ := by ring

end Qatlib.Papers.AmpInvReqTang26.PurifErrors
