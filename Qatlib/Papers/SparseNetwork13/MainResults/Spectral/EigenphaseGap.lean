/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.SpectralModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — Lemma 11: eigenphase gap of the quantum walk

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

**Lemma 11** (§4.2, p.25): the eigenphase gap around `π` of the walk operator `U(A,B)` is
at least `√(2λ/3)`.

Paper proof (p.25, Eq. (134)--(135)): by Lemma 7 the modified network has
`λ₂(L̄_{G′}) ≥ λ/3`, so the singular value `s₂(D(A,B)) = √(λ/6)`-lower-bounded (Eq. 134);
each singular value `s_j ∈ (0,1)` maps to the eigenphase `e^{±2i·arccos s_j}` (Lemma 10),
and with `θ_j = π/2 − arccos s_j` one has `θ_j ≥ sin θ_j = s_j ≥ √(λ/6)`, hence the gap
`2θ_j ≥ 2√(λ/6) = √(2λ/3)`.

This file formalises the numerical core: the phase gap `2θ_j` arising from a singular value
`s` is at least `√(2λ/3)` whenever `s ≥ √(λ/6)`.  The walk operator `U(A,B)` itself and its
singular-value-to-eigenphase correspondence (Lemma 10) are not modelled here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.Spectral

/-- The eigenphase gap around `π` of the walk operator, in terms of a singular value `s`:
with `θ = π/2 − arccos s`, the two eigenphases are `±2θ`, so the distance to `π` is `2θ`. -/
def eigenphaseGapAroundPi (s : ℝ) : ℝ := 2 * (Real.pi / 2 - Real.arccos s)

/-- **Arithmetic identity from Eq. (135).**  `2√(λ/6) = √(2λ/3)`. -/
theorem two_sqrt_lam_six (lam : ℝ) (hlam : 0 ≤ lam) :
    2 * Real.sqrt (lam / 6) = Real.sqrt (2 * lam / 3) := by
  have h2 : (2 * Real.sqrt (lam / 6)) ^ 2 = 2 * lam / 3 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [← h2]
  exact (Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (lam / 6))).symm

/-- The inequality `θ ≥ sin θ` of the proof of Lemma 11, instantiated at
`θ = π/2 − arccos s`, whose sine is `s`. -/
theorem sin_arccos_gap (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ≤ Real.pi / 2 - Real.arccos s := by
  have hmem : -1 ≤ s := by linarith
  have hθ : Real.sin (Real.pi / 2 - Real.arccos s) = s := by
    rw [Real.sin_pi_div_two_sub, Real.cos_arccos hmem hs1]
  have hle : Real.sin (Real.pi / 2 - Real.arccos s) ≤ Real.pi / 2 - Real.arccos s := by
    apply Real.sin_le
    have := (Real.arccos_le_pi_div_two).mpr hs0
    linarith
  rwa [hθ] at hle

/-- **Lemma 11 (arXiv:1311.1851v10, §4.2, p.25).**  If `s : ℝ` is the relevant singular
value of `D(A,B)` (a number in `[0,1]` with `s ≥ √(λ/6)` by Eq. (134)), then the eigenphase
gap around `π` of the walk is at least `√(2λ/3)`.  This is the numerical content of the
paper's Eq. (135).  The walk operator and Lemma 10's eigenphase correspondence are not
built here (see `eigenphaseGapAroundPi`). -/
theorem lemma11_eigenphase_gap (lam s : ℝ) (hlam : 0 < lam)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs : Real.sqrt (lam / 6) ≤ s) :
    Real.sqrt (2 * lam / 3) ≤ eigenphaseGapAroundPi s := by
  have hgap : 2 * s ≤ eigenphaseGapAroundPi s := by
    unfold eigenphaseGapAroundPi
    have := sin_arccos_gap s hs0 hs1
    linarith
  rw [← two_sqrt_lam_six lam (le_of_lt hlam)]
  exact le_trans (by linarith) hgap

end Qatlib.Papers.SparseNetwork13.MainResults.Spectral
