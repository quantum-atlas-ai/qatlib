/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PEPSPrep11.MainResults.OverlapLowerBound

Schwarz--Temme--Verstraete, "Preparing projected entangled pair states on a
quantum computer", fixed arXiv:1104.1410v2 (21 Feb 2012).

This file formalises **Lemma 2** (p. 3 of v2, proof on pp. 3--4, Eq. (1)--(8)).

Lemma 2 (source). Let `|ψ_t⟩ = Z_t^{-1/2} |A_t⟩` be the normalised PEPS with
`Z_t = ⟨A_t|A_t⟩`, and let `|A_{t+1}⟩ = A_{t+1}|A_t⟩` where `A_{t+1}` is the
PEPS projector of step `t+1`.  Then
`|⟨ψ_{t+1}|ψ_t⟩|² ≥ 1/κ(A_{t+1})² > 0`.

Here `A_{t+1}` is modelled as a positive self-adjoint operator `T` on a
finite-dimensional complex Hilbert space `E` (the virtual space at the vertex
being processed; the paper's `A^{(v)} : ℂ^{D^k} → ℂ^d` is extended to an
operator on `ℂ^{D^k}` via the physical-subspace projector `P_phy`, which is how
the algorithm actually acts — see step 4(c) and the discussion on p. 3).
For an injective PEPS projector the paper assumes `A ≥ 0` (in fact `> 0`) after
a polar decomposition, and `κ(A) = σ_max(A)/σ_min(A)`; on a positive
self-adjoint operator this is `λ_max/λ_min`.

The mathematical content is exactly the chain (1)--(8): the overlap is
`⟨A_t|A_{t+1}|A_t⟩ / (√Z_t √Z_{t+1})`, bounded below via `A ≥ 0` and
`A/σ_max ≤ 1`, and `Z_{t+1} ≥ σ_min² Z_t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PEPSPrep11.MainResults.OverlapLowerBound

open scoped ComplexOrder BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Largest eigenvalue `λ_max` of a self-adjoint operator.  For a positive
self-adjoint operator this is the largest singular value `σ_max`. -/
def eigMax {n : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hdim : Module.finrank ℂ E = n) (hn : 0 < n) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (hT.eigenvalues hdim)

/-- Smallest eigenvalue `λ_min` of a self-adjoint operator.  For a positive
definite self-adjoint operator this is the smallest singular value `σ_min`. -/
def eigMin {n : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hdim : Module.finrank ℂ E = n) (hn : 0 < n) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (hT.eigenvalues hdim)

/-- The condition number `κ(T) = σ_max/σ_min = λ_max/λ_min`. -/
def condNumber {n : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hdim : Module.finrank ℂ E = n) (hn : 0 < n) : ℝ :=
  eigMax T hT hdim hn / eigMin T hT hdim hn

/-- Every eigenvalue of a positive self-adjoint operator is non-negative. -/
theorem eigenvalues_nonneg {n : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hpsd : ∀ x, 0 ≤ (inner ℂ (T x) x).re)
    (hdim : Module.finrank ℂ E = n) (i : Fin n) : 0 ≤ hT.eigenvalues hdim i := by
  have hb : inner ℂ (T ((hT.eigenvectorBasis hdim) i)) ((hT.eigenvectorBasis hdim) i) =
      (hT.eigenvalues hdim i : ℂ) := by
    rw [hT.apply_eigenvectorBasis hdim i, inner_smul_left]
    simp
  have := hpsd ((hT.eigenvectorBasis hdim) i)
  rwa [hb, Complex.ofReal_re] at this

/-- Lemma 2, Eq. (5)--(8): the squared overlap is bounded below by `1/κ(T)²`.

Source: *Preparing projected entangled pair states on a quantum computer*,
arXiv:1104.1410v2, Lemma 2 (p. 3); proof pp. 3--4, Eq. (1)--(8).

`T` models the PEPS projector `A_{t+1}` of the source (positive self-adjoint
operator on the virtual space), `a` models the unnormalised `|A_t⟩`, and the
conclusion is exactly `|⟨ψ_{t+1}|ψ_t⟩|² ≥ 1/κ(A_{t+1})²`. -/
theorem lemma2_overlap_lower_bound {n : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hpsd : ∀ x, 0 ≤ (inner ℂ (T x) x).re)
    (hdim : Module.finrank ℂ E = n) (hn : 0 < n)
    (hpos : 0 < eigMin T hT hdim hn)
    (a : E) (ha : a ≠ 0) :
    (1 : ℝ) / (condNumber T hT hdim hn) ^ 2 ≤
      (‖inner ℂ (T a) a‖ / (‖T a‖ * ‖a‖)) ^ 2 := by
  classical
  -- Spectral data: eigenbasis, eigenvalues, and the spectral coordinates of `a`.
  set b := hT.eigenvectorBasis hdim with hb_def
  set lam : Fin n → ℝ := hT.eigenvalues hdim with hlam_def
  set c : Fin n → ℂ := fun i => (b.repr a).ofLp i with hc_def
  set Λ : ℝ := eigMax T hT hdim hn with hΛ_def
  set μ : ℝ := eigMin T hT hdim hn with hμ_def
  have hlam0 : ∀ i, 0 ≤ lam i := eigenvalues_nonneg T hT hpsd hdim
  have hlam_le : ∀ i, lam i ≤ Λ := by
    intro i
    exact Finset.le_sup' (f := hT.eigenvalues hdim) (b := i) (Finset.mem_univ i)
  have hmu_le : ∀ i, μ ≤ lam i := by
    intro i
    exact Finset.inf'_le (f := hT.eigenvalues hdim) (b := i) (Finset.mem_univ i)
  have hμ_pos : 0 < μ := hpos
  have hΛ_pos : 0 < Λ := lt_of_lt_of_le hμ_pos (le_trans (hmu_le ⟨0, hn⟩) (hlam_le ⟨0, hn⟩))
  -- Expansion of `a` and of `T a` in the eigenbasis.
  have hsum_a : ∑ i, c i • b i = a := OrthonormalBasis.sum_repr b a
  have hTa : T a = ∑ i, ((lam i : ℂ) * c i) • b i := by
    conv_lhs => rw [← hsum_a]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul, hT.apply_eigenvectorBasis hdim i, smul_smul, mul_comm]
    rfl
  have hrepr_Ta : ∀ i, (b.repr (T a)).ofLp i = (lam i : ℂ) * c i := by
    intro i
    exact hT.eigenvectorBasis_apply_self_apply hdim a i
  -- Norms in spectral coordinates.
  have hnorm_a : ‖a‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    have h1 : ‖a‖ = ‖b.repr a‖ := (b.repr.norm_map a).symm
    rw [h1, EuclideanSpace.norm_sq_eq]
  have hnorm_Ta : ‖T a‖ ^ 2 = ∑ i, (lam i) ^ 2 * ‖c i‖ ^ 2 := by
    have h1 : ‖T a‖ = ‖b.repr (T a)‖ := (b.repr.norm_map (T a)).symm
    rw [h1, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hrepr_Ta i, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hlam0 i)]
    ring
  -- Real part of the overlap `⟨T a, a⟩` is `∑ λ_i ‖c_i‖²`, and the imaginary
  -- part vanishes because `T` is self-adjoint.
  have hinner_term : ∀ i : Fin n,
      (inner ℂ ((lam i : ℂ) * c i) (c i)).re = lam i * ‖c i‖ ^ 2 := by
    intro i
    rw [RCLike.inner_apply]
    have hconj : (starRingEnd ℂ) ((lam i : ℂ) * c i) =
        (lam i : ℂ) * (starRingEnd ℂ) (c i) := by
      rw [map_mul, Complex.conj_ofReal]
    rw [hconj]
    have hnorm : c i * (starRingEnd ℂ) (c i) = ((Complex.normSq (c i) : ℝ) : ℂ) := by
      rw [Complex.mul_conj]
    have hassoc : c i * ((lam i : ℂ) * (starRingEnd ℂ) (c i)) =
        (lam i : ℂ) * (c i * (starRingEnd ℂ) (c i)) := by ring
    rw [hassoc, hnorm, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hinner_re : (inner ℂ (T a) a).re = ∑ i, lam i * ‖c i‖ ^ 2 := by
    rw [show inner ℂ (T a) a = inner ℂ (b.repr (T a)) (b.repr a) from
      (b.repr.inner_map_map (T a) a).symm]
    rw [PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa only [hc_def, hrepr_Ta i] using hinner_term i
  have hinner_im : (inner ℂ (T a) a).im = 0 := by
    have hreal : (starRingEnd ℂ) (inner ℂ (T a) a) = inner ℂ (T a) a := by
      calc (starRingEnd ℂ) (inner ℂ (T a) a) = inner ℂ a (T a) := inner_conj_symm a (T a)
        _ = inner ℂ (T a) a := (hT a a).symm
    exact Complex.conj_eq_iff_im.mp hreal
  set S : ℝ := ∑ i, lam i * ‖c i‖ ^ 2 with hS_def
  have hinner_val : inner ℂ (T a) a = (S : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; exact hinner_re
    · rw [Complex.ofReal_im]; exact hinner_im
  have hS_nonneg : 0 ≤ S := by
    rw [hS_def]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hlam0 i) (by positivity))
  have hnorm_inner : ‖inner ℂ (T a) a‖ = S := by
    rw [hinner_val, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS_nonneg]
  -- Norms are positive.
  have hC_pos : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  -- Upper bound `‖T a‖² ≤ Λ · ⟨T a, a⟩` (Eq. (2)--(5)).
  have hupper : ‖T a‖ ^ 2 ≤ Λ * S := by
    rw [hnorm_Ta, hS_def, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have h1 : lam i ^ 2 ≤ Λ * lam i := by
      have h2 : 0 ≤ (Λ - lam i) * lam i :=
        mul_nonneg (by linarith [hlam_le i]) (hlam0 i)
      nlinarith
    calc lam i ^ 2 * ‖c i‖ ^ 2 ≤ (Λ * lam i) * ‖c i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Λ * (lam i * ‖c i‖ ^ 2) := by ring
  -- Lower bound `‖T a‖² ≥ μ² · ‖a‖²` (Eq. (6)--(7)).
  have hlower : μ ^ 2 * ‖a‖ ^ 2 ≤ ‖T a‖ ^ 2 := by
    rw [hnorm_Ta, hnorm_a, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have h1 : μ ^ 2 ≤ lam i ^ 2 := by
      have h2 : 0 ≤ μ := le_of_lt hμ_pos
      nlinarith [hmu_le i, hlam0 i]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- `‖T a‖ > 0`.
  have hB_pos : 0 < ‖T a‖ ^ 2 := by
    have h1 : 0 < μ ^ 2 * ‖a‖ ^ 2 := by positivity
    linarith [hlower]
  have hnorm_Ta_pos : 0 < ‖T a‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (T a)) with h | h
    · rw [← h] at hB_pos
      norm_num at hB_pos
    · exact h
  -- Final algebra.
  have hS_ge : ‖T a‖ ^ 2 / Λ ≤ S := by
    rw [div_le_iff₀ hΛ_pos]
    linarith [hupper]
  -- `‖T a‖² ≤ Λ S` and `μ² ‖a‖² ≤ ‖T a‖²` give
  -- `‖T a‖² ‖a‖² ≤ S² (Λ/μ)²`.
  have hBC : ‖T a‖ ^ 2 * ‖a‖ ^ 2 ≤ S ^ 2 * (Λ / μ) ^ 2 := by
    have hC_le : ‖a‖ ^ 2 ≤ ‖T a‖ ^ 2 / μ ^ 2 := by
      rw [le_div_iff₀ (pow_pos hμ_pos 2)]
      nlinarith [hlower]
    have hstep1 : ‖T a‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖T a‖ ^ 2 * (‖T a‖ ^ 2 / μ ^ 2) :=
      mul_le_mul_of_nonneg_left hC_le (by positivity)
    have hsq : ‖T a‖ ^ 2 * ‖T a‖ ^ 2 ≤ (Λ * S) ^ 2 := by
      have h := mul_self_le_mul_self (a := ‖T a‖ ^ 2) (b := Λ * S) (by positivity) hupper
      simpa [sq] using h
    have h1 : ‖T a‖ ^ 2 * (‖T a‖ ^ 2 / μ ^ 2) =
        (‖T a‖ ^ 2 * ‖T a‖ ^ 2) / μ ^ 2 := by
      field_simp
    have h2 : (Λ * S) ^ 2 / μ ^ 2 = S ^ 2 * (Λ / μ) ^ 2 := by
      rw [mul_pow]
      field_simp
    have hstep2 : ‖T a‖ ^ 2 * (‖T a‖ ^ 2 / μ ^ 2) ≤ S ^ 2 * (Λ / μ) ^ 2 := by
      rw [h1, ← h2]
      exact div_le_div_of_nonneg_right hsq (pow_pos hμ_pos 2).le
    linarith [hstep1, hstep2]
  rw [hnorm_inner]
  have hκpos : 0 < (Λ / μ) ^ 2 := pow_pos (div_pos hΛ_pos hμ_pos) 2
  have hbcpos : 0 < ‖T a‖ ^ 2 * ‖a‖ ^ 2 := mul_pos hB_pos hC_pos
  have hrewrite : (S / (‖T a‖ * ‖a‖)) ^ 2 = S ^ 2 / (‖T a‖ ^ 2 * ‖a‖ ^ 2) := by
    rw [div_pow, mul_pow]
  have hcond : condNumber T hT hdim hn = Λ / μ := by
    unfold condNumber
    rw [hΛ_def, hμ_def]
  rw [hrewrite, hcond, div_le_div_iff₀ hκpos hbcpos]
  simpa using hBC

/-- Lemma 2, strict positivity part: the lower bound `1/κ(A_{t+1})²` is
strictly positive, as stated in the source (`> 0`).

Source: arXiv:1104.1410v2, Lemma 2, p. 3 (end of proof: "the injectivity
assumption ... implies left invertibility ... thus κ(A_{t+1}) is finite,
therefore p > 0"). -/
theorem lemma2_overlap_pos {n : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hpsd : ∀ x, 0 ≤ (inner ℂ (T x) x).re)
    (hdim : Module.finrank ℂ E = n) (hn : 0 < n)
    (hpos : 0 < eigMin T hT hdim hn)
    (a : E) (ha : a ≠ 0) :
    0 < ‖inner ℂ (T a) a‖ / (‖T a‖ * ‖a‖) := by
  have h := lemma2_overlap_lower_bound T hT hpsd hdim hn hpos a ha
  have hμ_pos : 0 < eigMin T hT hdim hn := hpos
  have hΛ_pos : 0 < eigMax T hT hdim hn := by
    have hle1 : eigMin T hT hdim hn ≤ hT.eigenvalues hdim ⟨0, hn⟩ :=
      Finset.inf'_le (f := hT.eigenvalues hdim) (b := ⟨0, hn⟩) (Finset.mem_univ _)
    have hle2 : hT.eigenvalues hdim ⟨0, hn⟩ ≤ eigMax T hT hdim hn :=
      Finset.le_sup' (f := hT.eigenvalues hdim) (b := ⟨0, hn⟩) (Finset.mem_univ _)
    linarith
  have hκpos : 0 < condNumber T hT hdim hn := by
    rw [condNumber]
    exact div_pos hΛ_pos hμ_pos
  have hbound : (0 : ℝ) < 1 / (condNumber T hT hdim hn) ^ 2 :=
    one_div_pos.mpr (pow_pos hκpos 2)
  have hsq : 0 < (‖inner ℂ (T a) a‖ / (‖T a‖ * ‖a‖)) ^ 2 := lt_of_lt_of_le hbound h
  have hxnn : 0 ≤ ‖inner ℂ (T a) a‖ / (‖T a‖ * ‖a‖) :=
    div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hxne : ‖inner ℂ (T a) a‖ / (‖T a‖ * ‖a‖) ≠ 0 := by
    intro h0
    rw [h0] at hsq
    norm_num at hsq
  exact lt_of_le_of_ne hxnn (Ne.symm hxne)

end Qatlib.Papers.PEPSPrep11.MainResults.OverlapLowerBound
