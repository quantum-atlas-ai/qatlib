/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma A.1: recovering the shift from `|ψ_1⟩, …, |ψ_{2^{k-1}}⟩`

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Lemma A.1 and its proof (Appendix A).

Fourier sampling on the cyclic group `ℤ_N` produces the states

`|ψ_x⟩ = (|0⟩ + ω^{s x}|1⟩)/√2`,  `ω = e^{2πi/N}`,

with known labels `x`.  Lemma A.1 takes one copy each of
`|ψ_1⟩, |ψ_2⟩, |ψ_4⟩, …, |ψ_{2^{k-1}}⟩` and reconstructs `s` in polynomial time
with probability `Ω(1)` whenever `2^k = Ω(N)`.

The proof computes the tensor product

`∏_{j<k} |ψ_{2^j}⟩ = 2^{-k/2} Σ_{y<2^k} ω^{s y} |y⟩`

and measures it after the inverse quantum Fourier transform over `ℤ_N`.  The
inverse transform maps the target `|s⟩ = N^{-1/2} Σ_{y<N} ω^{s y} |y⟩` to the
computational basis state `|s⟩`, so the success probability is the squared
overlap

`|⟨s | ∏_j ψ_{2^j}⟩|² = 2^k / N`.

This module formalizes exactly that amplitude computation.  The inverse QFT
itself, the measurement postulate and the polynomial-time claim are not modelled
here; see the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

open Complex

/-- A unit-modulus phase contributes only its classical amplitude to the overlap:
`(a · conj w) · (b · w) = a · b` when `‖w‖ = 1`.  This is the computation
`conj(ω^{sy}) · ω^{sy} = 1` that the source uses at every `y`. -/
theorem conj_mul_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) (a b : ℝ) :
    ((a : ℂ) * (starRingEnd ℂ) w) * ((b : ℂ) * w) = ((a * b : ℝ) : ℂ) := by
  have hunit : (starRingEnd ℂ) w * w = 1 := by
    rw [Complex.conj_mul', hw]
    norm_num
  calc ((a : ℂ) * (starRingEnd ℂ) w) * ((b : ℂ) * w)
      = ((a : ℂ) * (b : ℂ)) * ((starRingEnd ℂ) w * w) := by ring
    _ = ((a * b : ℝ) : ℂ) := by
          rw [hunit, mul_one]
          push_cast
          ring

/-- **Lemma A.1, amplitude computation.**  For a unit-modulus phase `ω` the
overlap of the target state `|s⟩` with the product of the `k` Fourier-sampling
states is the real number `2^k / (√N · √(2^k))`, i.e. `√(2^k/N)`.

The `y`-th amplitude of the target is `N^{-1/2} ω^{s y}`, the `y`-th amplitude of
the product is `2^{-k/2} ω^{s y}` for `y < 2^k` and `0` otherwise, so every
summand contributes `(√N · √(2^k))⁻¹`. -/
theorem lemmaA1_overlap_sum (N k s : ℕ) (ω : ℂ) (hω : ‖ω‖ = 1)
    (hkN : 2 ^ k ≤ N) :
    (Finset.range N).sum (fun y =>
        (starRingEnd ℂ) ((1 / Real.sqrt (N : ℝ) : ℝ) * ω ^ (s * y)) *
          ((if y < 2 ^ k then (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) else 0) * ω ^ (s * y)))
      = (((((2 ^ k : ℕ) : ℝ) * (1 / Real.sqrt (N : ℝ)) *
          (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ))) : ℝ) : ℂ) := by
  have hphase : ∀ y : ℕ, ‖ω ^ (s * y)‖ = 1 := by
    intro y
    rw [norm_pow, hω, one_pow]
  have hterm : ∀ y : ℕ,
      (starRingEnd ℂ) ((1 / Real.sqrt (N : ℝ) : ℝ) * ω ^ (s * y)) *
          ((if y < 2 ^ k then (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) else 0) * ω ^ (s * y))
        = (if y < 2 ^ k then
            (((1 / Real.sqrt (N : ℝ)) * (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) : ℝ) : ℂ)
           else 0) := by
    intro y
    by_cases hy : y < 2 ^ k
    · rw [if_pos hy, if_pos hy, map_mul, Complex.conj_ofReal]
      exact conj_mul_of_norm_one (hphase y) _ _
    · rw [if_neg hy, if_neg hy]
      simp
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range N).filter (fun y => y < 2 ^ k) = Finset.range (2 ^ k) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨lt_of_lt_of_le h hkN, h⟩
  rw [hfilter, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Lemma A.1, success probability.**  The squared overlap of the product state
with `|s⟩` is `2^k / N`, which is the success probability of the Fourier-sampling
reconstruction. -/
theorem lemmaA1_overlap_probability (N k s : ℕ) (ω : ℂ) (hω : ‖ω‖ = 1) (hN : 0 < N)
    (hkN : 2 ^ k ≤ N) :
    Complex.normSq
        ((Finset.range N).sum (fun y =>
          (starRingEnd ℂ) ((1 / Real.sqrt (N : ℝ) : ℝ) * ω ^ (s * y)) *
            ((if y < 2 ^ k then (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) else 0) *
              ω ^ (s * y))))
      = ((2 ^ k : ℕ) : ℝ) / N := by
  rw [lemmaA1_overlap_sum N k s ω hω hkN, Complex.normSq_ofReal]
  have hM : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hA : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hB : Real.sqrt ((2 ^ k : ℕ) : ℝ) ^ 2 = ((2 ^ k : ℕ) : ℝ) := Real.sq_sqrt hM.le
  have hAne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
  have hBne : Real.sqrt ((2 ^ k : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hM)
  field_simp
  nlinarith

/-- **Lemma A.1, `Ω(1)` success.**  If `2^k = Ω(N)` in the explicit form
`N ≤ C · 2^k`, then the reconstruction succeeds with probability at least `1/C`,
which is the source's `Ω(1)`. -/
theorem lemmaA1_probability_lower (N k : ℕ) (C : ℝ) (hC : 0 < C) (hN : 0 < N)
    (h : (N : ℝ) ≤ C * ((2 ^ k : ℕ) : ℝ)) :
    1 / C ≤ ((2 ^ k : ℕ) : ℝ) / N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos]
  have hCne : C ≠ 0 := ne_of_gt hC
  have hkey : (1 / C) * (C * ((2 ^ k : ℕ) : ℝ)) = ((2 ^ k : ℕ) : ℝ) := by
    field_simp
  nlinarith

end Qatlib.Papers.EllipticIsog10.MainResults
