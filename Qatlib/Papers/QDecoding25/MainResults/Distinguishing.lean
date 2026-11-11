/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

set_option backward.isDefEq.respectTransparency false

/-! Average distinguishing probability for
"The Quantum Decoding Problem: Tight Achievability Bounds and
Application to Regev's Reduction" (arXiv:2509.24796v2, 2025).

Lemma 9 of the paper: `N` states living in a `K`-dimensional space
have average distinguishing probability at most `K/N`.

The proof is the standard trace bookkeeping: for a POVM written as
`M_c = A_c†A_c` (every PSD POVM element factors so; the spectral
factorization is the abstracted step) and states `|φ_c⟩` with
`‖φ_c‖ = 1`,

`⟨φ_c|M_c|φ_c⟩ = ‖A_c φ_c‖² ≤ ‖A_c‖_F² = tr(M_c)` (row-wise
Cauchy–Schwarz), and `∑_c tr(M_c) = tr(∑_c M_c) = tr(1) = K`.

- `abs_sum_mul_sq_le` is the row-wise Cauchy–Schwarz for complex sums.
- `sum_success_le_card` is the summed bound `Σ_c p_c ≤ K`.
- `avg_success_le_card` is **Lemma 9**, the averaged `K/N` bound.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.QDecoding25.MainResults.Distinguishing

open scoped Matrix

variable {K : Type} [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- Row-wise Cauchy–Schwarz for complex sums:
`‖∑ a j * v j‖² ≤ (∑ ‖a j‖²) * (∑ ‖v j‖²)`. -/
theorem abs_sum_mul_sq_le (a v : K → ℂ) :
    ‖∑ j, a j * v j‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖v j‖ ^ 2) := by
  set x : EuclideanSpace ℂ K := WithLp.toLp 2 (fun j => starRingEnd ℂ (a j)) with hx
  set y : EuclideanSpace ℂ K := WithLp.toLp 2 v with hy
  have hinner : inner ℂ x y = ∑ j, a j * v j := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm, hx, hy]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) x y
  have hnorma : ‖x‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), hx]
    exact Finset.sum_congr rfl fun j _ => by simp
  have hnormv : ‖y‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), hy]
  calc ‖∑ j, a j * v j‖ ^ 2 = ‖(inner ℂ x y)‖ ^ 2 := by rw [hinner]
    _ ≤ (‖x‖ * ‖y‖) ^ 2 := by
          refine sq_le_sq.mpr ?_
          rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
          exact hcs
    _ = (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖v j‖ ^ 2) := by
          rw [mul_pow, ← hnorma, ← hnormv]

/-- **Lemma 9, summed form**: for unit states `v c` and a POVM given as
`A_c†A_c` summing to the identity, the total success probability is at
most the dimension `K`. -/
theorem sum_success_le_card {N : ℕ} (v : Fin N → K → ℂ)
    (hv : ∀ c, ∑ j, ‖v c j‖ ^ 2 = 1)
    (A : Fin N → Matrix K K ℂ)
    (hsum : ∑ c, (A c)ᴴ * (A c) = 1) :
    ∑ c, ∑ i, ‖∑ j, (A c) i j * (v c) j‖ ^ 2 ≤ ((Fintype.card K : ℕ) : ℝ) := by
  classical
  -- row-wise CS step
  have hterm : ∀ c i, ‖∑ j, (A c) i j * (v c) j‖ ^ 2 ≤ ∑ j, ‖(A c) i j‖ ^ 2 := by
    intro c i
    have h := abs_sum_mul_sq_le (fun j => (A c) i j) (v c)
    rw [hv c, mul_one] at h
    exact h
  -- the diagonal of A†A is the column norm-square sum
  have hentry : ∀ (c : Fin N) (i : K),
      ((A c)ᴴ * A c) i i = ((∑ j, ‖(A c) j i‖ ^ 2 : ℝ) : ℂ) := by
    intro c i
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (starRingEnd ℂ ((A c) j i)) * (A c) j i
        = ((‖(A c) j i‖ ^ 2 : ℝ) : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq]
  -- per-coordinate normalization: sum over c of column sums is 1
  have hper : ∀ i : K, ∑ c, ∑ j, ‖(A c) j i‖ ^ 2 = 1 := by
    intro i
    have h3 : ∑ c, ((A c)ᴴ * A c) i i = (1 : ℂ) := by
      rw [← Matrix.sum_apply, hsum]
      simp
    have h4 : (1 : ℂ) = ((∑ c, ∑ j, ‖(A c) j i‖ ^ 2 : ℝ) : ℂ) := by
      refine h3.symm.trans ?_
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun c _ => hentry c i
    exact Complex.ofReal_injective
      (by rw [Complex.ofReal_one]; exact h4.symm)
  -- transpose the double sum and conclude
  have hswap : ∀ c : Fin N, ∑ i, ∑ j, ‖(A c) i j‖ ^ 2
      = ∑ i, ∑ j, ‖(A c) j i‖ ^ 2 := by
    intro c
    rw [Finset.sum_comm]
  calc ∑ c, ∑ i, ‖∑ j, (A c) i j * (v c) j‖ ^ 2
      ≤ ∑ c, ∑ i, ∑ j, ‖(A c) i j‖ ^ 2 :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i _ => hterm c i
    _ = ∑ c, ∑ i, ∑ j, ‖(A c) j i‖ ^ 2 :=
        Finset.sum_congr rfl fun c _ => hswap c
    _ = ∑ i, ∑ c, ∑ j, ‖(A c) j i‖ ^ 2 := Finset.sum_comm
    _ = ∑ i : K, 1 := Finset.sum_congr rfl fun i _ => hper i
    _ = ((Fintype.card K : ℕ) : ℝ) := by simp

/-- **Lemma 9**: the average success probability of distinguishing `N`
states in a `K`-dimensional space with a POVM `{A_c†A_c}` is at most
`K / N`. -/
theorem avg_success_le_card {N : ℕ} (hN : 0 < N) (v : Fin N → K → ℂ)
    (hv : ∀ c, ∑ j, ‖v c j‖ ^ 2 = 1)
    (A : Fin N → Matrix K K ℂ)
    (hsum : ∑ c, (A c)ᴴ * (A c) = 1) :
    (1 / (N : ℝ)) * ∑ c, ∑ i, ‖∑ j, (A c) i j * (v c) j‖ ^ 2
      ≤ ((Fintype.card K : ℕ) : ℝ) / (N : ℝ) := by
  have h := sum_success_le_card v hv A hsum
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc (1 / (N : ℝ)) * ∑ c, ∑ i, ‖∑ j, (A c) i j * (v c) j‖ ^ 2
      ≤ (1 / (N : ℝ)) * ((Fintype.card K : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((Fintype.card K : ℕ) : ℝ) / (N : ℝ) := by field_simp

end Qatlib.Papers.QDecoding25.MainResults.Distinguishing
