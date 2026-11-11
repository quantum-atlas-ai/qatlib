/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# RobustQLearn14.MainResults.DepolarizingNoise — classical reduction to LPN

Fixed source: Cross--Smith--Smolin, *Quantum learning robust to noise*,
arXiv:1407.5088v1 (18 Jul 2014).

Claim `c005` (Sec. IV B, Eq. (10), pp. 3--4).  Under independent depolarizing
noise `D_η^{⊗(n+1)}` (Eq. (1), `η < 1/2`), a classical query returns the sample
`(x ⊕ e_{1:n}, f_a(x) ⊕ e_{n+1})` (Eq. (9)), where each noise bit is `1` with
probability `η`.  Since `f_a` is linear over `GF(2)`,

  `f_a(x ⊕ e) = f_a(x) + ⟨a, e⟩`,

so with `x' = x ⊕ e` the sample is `(x', f_a(x') + (⟨a,e⟩ + e_{n+1}))`: an LPN
sample whose result bit is flipped with probability

  `ζ_a = Pr_e[⟨a,e⟩ = 1]`,                                          (10)

equivalently the Hamming-weight double sum of Eq. (10) in the paper.  The total
result-bit error rate is

  `η' = η (1 - ζ_a) + ζ_a (1 - η)`,                                 (10)

and `η' ∈ [η, 1 - η]`.

This file formalizes the `GF(2)` algebra of Eqs. (9)--(10) and proves the
interval.  `zetaNoise` is the probabilistic form of the paper's `ζ_a`; Eq. (10)
in the paper is the Hamming-weight expansion of the same probability (the
purely combinatorial expansion is not separately formalized here).
-/

open scoped BigOperators

namespace Qatlib.Papers.RobustQLearn14.MainResults

noncomputable section

/-! ## `GF(2)` sample algebra -/

/-- The `GF(2)` inner product `⟨a,x⟩ = Σ_i a_i x_i`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (9), p. 3. -/
def lpnDot {n : ℕ} (a x : Fin n → ZMod 2) : ZMod 2 := ∑ i, a i * x i

/-- The parity function `f_a(x) = ⟨a,x⟩`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (9), p. 3. -/
def lpnParity {n : ℕ} (a x : Fin n → ZMod 2) : ZMod 2 := lpnDot a x

/-- Coordinatewise XOR `x ⊕ e` over `GF(2)`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (9), p. 3. -/
def lpnXorVec {n : ℕ} (x e : Fin n → ZMod 2) : Fin n → ZMod 2 := fun i => x i + e i

/-- In characteristic two, `x + x = 0`.
Source: arXiv:1407.5088v1, Sec. IV B, p. 3 (`GF(2)` arithmetic). -/
theorem lpnAddSelf (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc x + x = 2 * x := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- Every element of `GF(2)` is `0` or `1`.
Source: arXiv:1407.5088v1, Sec. IV B, p. 3 (`GF(2)` arithmetic). -/
theorem lpnZeroOrOne (x : ZMod 2) : x = 0 ∨ x = 1 := by decide +revert

/-- The two elements of `GF(2)` are `0` and `1`.
Source: arXiv:1407.5088v1, Sec. IV B, p. 3 (`GF(2)` arithmetic). -/
theorem lpnUniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

/-- The total weight of one noise bit is one: `(1-η) + η = 1`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3 (independent bit flips). -/
theorem lpnSumFactor (η : ℝ) :
    (∑ y : ZMod 2, (if y = 0 then 1 - η else η)) = 1 := by
  rw [lpnUniv]
  rw [Finset.sum_insert (by simp : (0 : ZMod 2) ∉ ({1} : Finset (ZMod 2)))]
  rw [Finset.sum_singleton]
  simp only [if_true, if_neg (show (1 : ZMod 2) ≠ 0 by decide)]
  ring

/-- Linearity of the parity function over `GF(2)`:
`f_a(x ⊕ e) = f_a(x) + ⟨a,e⟩`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (9), p. 3. -/
theorem lpnDot_xor {n : ℕ} (a x e : Fin n → ZMod 2) :
    lpnDot a (lpnXorVec x e) = lpnDot a x + lpnDot a e := by
  unfold lpnDot lpnXorVec
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `c005` / Eq. (9): the classically observed noisy sample equals the LPN
sample `(x', f_a(x') ⊕ (⟨a,e⟩ ⊕ e_{n+1}))`, i.e. the result-bit error is
`⟨a,e⟩ ⊕ e_{n+1}`.  Source: arXiv:1407.5088v1, Sec. IV B, Eq. (9), p. 3. -/
theorem lpn_sample_reduction {n : ℕ} (a x e : Fin n → ZMod 2) (en : ZMod 2) :
    lpnParity a (lpnXorVec x e) + en = lpnParity a x + (lpnDot a e + en) := by
  unfold lpnParity
  rw [lpnDot_xor]
  ring

/-- `c005` / Eq. (10): the LPN error bit `⟨a,e⟩ ⊕ e_{n+1}` is `1` exactly in the
two mixture cases (odd parity with a clean result bit, or even parity with a
flipped result bit), which yields `η' = η(1-ζ_a) + ζ_a(1-η)`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3. -/
theorem lpn_error_decomposition {n : ℕ} (a e : Fin n → ZMod 2) (en : ZMod 2) :
    lpnDot a e + en = 1 ↔ (lpnDot a e = 1 ∧ en = 0) ∨ (lpnDot a e = 0 ∧ en = 1) := by
  have hcases : ∀ z w : ZMod 2, z + w = 1 ↔ (z = 1 ∧ w = 0) ∨ (z = 0 ∧ w = 1) := by
    intro z w
    rcases lpnZeroOrOne z with rfl | rfl <;>
      rcases lpnZeroOrOne w with rfl | rfl <;> decide
  exact hcases (lpnDot a e) en

/-! ## Noise rate and the total error rate `η'` -/

/-- Bernoulli weight `∏_i η^{e_i}(1-η)^{1-e_i}` of a `GF(2)` noise vector.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3 (independent bit flips). -/
def bernoulliWeight (n : ℕ) (η : ℝ) (e : Fin n → ZMod 2) : ℝ :=
  ∏ i, if e i = 0 then 1 - η else η

/-- The Bernoulli weight is nonnegative for `0 ≤ η ≤ 1`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3. -/
theorem bernoulliWeight_nonneg (n : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (e : Fin n → ZMod 2) : 0 ≤ bernoulliWeight n η e := by
  unfold bernoulliWeight
  exact Finset.prod_nonneg (fun i _ => by split_ifs with h <;> linarith)

/-- The Bernoulli weights of all noisy vectors sum to one.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3 (normalized distribution). -/
theorem bernoulliWeight_sum (n : ℕ) (η : ℝ) :
    (∑ e : Fin n → ZMod 2, bernoulliWeight n η e) = 1 := by
  unfold bernoulliWeight
  have hp := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (ZMod 2)))
    (g := fun (_i : Fin n) (y : ZMod 2) => if y = 0 then 1 - η else η)
  rw [Fintype.piFinset_univ] at hp
  rw [hp]
  simp [lpnSumFactor]

/-- `c005` / Eq. (10): `ζ_a` is the probability that the noise vector has odd
parity on the support of `a`, `ζ_a = Pr_e[⟨a,e⟩ = 1]`.  This is the
probabilistic form of the Hamming-weight double sum in Eq. (10).
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3. -/
def zetaNoise (n : ℕ) (a : Fin n → ZMod 2) (η : ℝ) : ℝ :=
  ∑ e : Fin n → ZMod 2, bernoulliWeight n η e * (if lpnDot a e = 0 then 0 else 1)

/-- `c005`: `ζ_a ≥ 0` for a legitimate noise rate `0 ≤ η ≤ 1`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3 (`ζ_a` is a probability). -/
theorem zetaNoise_nonneg (n : ℕ) (a : Fin n → ZMod 2) (η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : 0 ≤ zetaNoise n a η := by
  unfold zetaNoise
  exact Finset.sum_nonneg (fun e _ =>
    mul_nonneg (bernoulliWeight_nonneg n η hη0 hη1 e) (by split_ifs <;> norm_num))

/-- `c005`: `ζ_a ≤ 1` for a legitimate noise rate `0 ≤ η ≤ 1`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 3 (`ζ_a` is a probability). -/
theorem zetaNoise_le_one (n : ℕ) (a : Fin n → ZMod 2) (η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : zetaNoise n a η ≤ 1 := by
  unfold zetaNoise
  calc (∑ e : Fin n → ZMod 2,
        bernoulliWeight n η e * (if lpnDot a e = 0 then 0 else 1))
      ≤ ∑ e : Fin n → ZMod 2, bernoulliWeight n η e * 1 := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hw := bernoulliWeight_nonneg n η hη0 hη1 e
        have hind : (if lpnDot a e = 0 then (0 : ℝ) else 1) ≤ 1 := by
          split_ifs <;> norm_num
        exact mul_le_mul_of_nonneg_left hind hw
    _ = ∑ e : Fin n → ZMod 2, bernoulliWeight n η e := by simp
    _ = 1 := bernoulliWeight_sum n η

/-- The total result-bit error rate `η' = η(1-ζ_a) + ζ_a(1-η)` of Eq. (10).
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), pp. 3--4. -/
def lpnErrorRate (η ζ : ℝ) : ℝ := η * (1 - ζ) + ζ * (1 - η)

/-- `c005`: the LPN noise rate lies in `[η, 1-η]` whenever `0 ≤ η ≤ 1/2` and
`ζ_a ∈ [0,1]` (the paper's constant noise rate `η < 1/2`).
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 4
("the LPN problem with noise rate η' ∈ [η, 1-η]"). -/
theorem lpnErrorRate_mem_interval (η ζ : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    η ≤ lpnErrorRate η ζ ∧ lpnErrorRate η ζ ≤ 1 - η := by
  have h1 : (0 : ℝ) ≤ 1 - 2 * η := by linarith
  have h2 : (0 : ℝ) ≤ 1 - ζ := by linarith
  have h3 : (0 : ℝ) ≤ ζ * (1 - 2 * η) := mul_nonneg hζ0 h1
  have h4 : (0 : ℝ) ≤ (1 - 2 * η) * (1 - ζ) := mul_nonneg h1 h2
  constructor <;> unfold lpnErrorRate <;> nlinarith

/-- `c005`, combined form: for a legitimate depolarizing noise rate `η ≤ 1/2`,
the total error rate of the reduced LPN instance lies in `[η, 1-η]`.
Source: arXiv:1407.5088v1, Sec. IV B, Eq. (10), p. 4. -/
theorem lpn_noise_rate_mem_interval (n : ℕ) (a : Fin n → ZMod 2) (η : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) :
    η ≤ lpnErrorRate η (zetaNoise n a η) ∧
      lpnErrorRate η (zetaNoise n a η) ≤ 1 - η :=
  lpnErrorRate_mem_interval η (zetaNoise n a η) hη0 hη
    (zetaNoise_nonneg n a η hη0 (by linarith))
    (zetaNoise_le_one n a η hη0 (by linarith))

end

end Qatlib.Papers.RobustQLearn14.MainResults
