/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBounds

set_option backward.isDefEq.respectTransparency false

/-!
# SourceMainTheorem — the main Lie-algebra product formula of arXiv:1512.03416v1

Fixed paper version: arXiv:1512.03416v1 (R. D. Somma, "A Trotter–Suzuki
approximation for Lie groups with applications to Hamiltonian simulation",
10 December 2015).  Source location: main results, p. 2–3, unnumbered theorem
("Let r ≥ 1 be an integer such that Eq. (4) holds ... Then there is a unitary W
that approximates U as in Eqs. (2) and (3) and the number of terms in the
product is N = r N_p").

The paper states the result for a real Lie algebra of (possibly infinite) basis
dimension `K`, with skew-Hermitian generators `ĥ_k`, error measured on a state
`|ψ⟩` (Eq. (2)) and the product `W = ∏ e^{t_n ĥ_{k_n}}` (Eq. (3)).  This file
records the finite-dimensional matrix specialization already proved in the
library as `Qatlib.Concepts.TrotterFormula.GeneralOrder.clause17`
(frozen v2.0.2): for a list `hs` of skew-Hermitian matrices, recursion depth `k`
(i.e. Suzuki order `2p` with `p = k+1`), time `t` and precision `ε > 0`, the
segmented recursive Suzuki word built from `recursiveSuzukiGenerators hs k`
(whose five-block recursion `a ++ a ++ b ++ a ++ a` is the paper's
`(W_{2p}(s_p λ))² W_{2p}((1-4s_p)λ) (W_{2p}(s_pλ))²`) is unitary, has exactly
`r * (2 * |hs| * 5^k) = r N_p` exponentials, and is within `ε` of
`exp(t • ∑ hs)` in operator norm.

The state-dependent Eq. (2) error and the abstract series condition Eq. (4) in
`β_{j+1}`, `f_j` are replaced by the concrete operator-norm certificate
`pfCommAlphaSelf` of the frozen spec; see the `covered_by` note on claim c001.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The segment count realizing Eq. (4): the same explicit choice as the frozen
`clause17` ε-guarantee,
`r = max 1 ⌈(p! α |t|^{p+1} / ((p+1)! ε))^{1/p}⌉` with matched order
`p = 2(k+1)` and `α = pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2(k+1)+1)`. -/
noncomputable def sourceRecursiveSegments {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε : ℝ) : ℕ :=
  max 1
    (Nat.ceil
      ((((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^
        ((1 : ℝ) / (2 * (k + 1)))))

/-- A finite sum of anti-Hermitian matrices is anti-Hermitian. -/
theorem source_sum_antiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (hxs : ∀ X ∈ xs, Xᴴ = -X) : xs.sumᴴ = -xs.sum := by
  induction xs with
  | nil => simp
  | cons X xs ih =>
    simp only [List.sum_cons, Matrix.conjTranspose_add, hxs X (by simp),
      ih (by intro Y hY; exact hxs Y (by simp [hY])), neg_add]

/-- Matched-word baseline for the recursive Suzuki word at matched order
`p := 2(k+1)`: the `pf_segment_word_prod` shape fed to
`pf_matched_word_segmented_skew`. -/
theorem recursive_matched_error {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hr : 0 < r) :
    ‖(recursiveSuzukiWord hs k t r).prod - NormedSpace.exp (t • hs.sum)‖ ≤
      ((Nat.factorial (2 * (k + 1)) : ℝ) *
        pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
        |t| ^ (2 * (k + 1) + 1)) /
      ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * (r : ℝ) ^ (2 * (k + 1))) := by
  have hword : (recursiveSuzukiWord hs k t r).prod =
      suzukiExponentialWord (recursiveSuzukiGenerators hs k) (t / r) ^ r :=
    pf_segment_word_prod (recursiveSuzukiGenerators hs k) t r
  rw [hword]
  exact pf_matched_word_segmented_skew (recursiveSuzukiGenerators hs k) hs.sum
    (2 * (k + 1)) r t (by omega) hr
    (fun n hn => recursive_suzuki_all_even_order_coefficients I hs k n hn)
    (recursiveSuzukiGenerators_antiHermitian hs k hhs)
    (source_sum_antiHermitian hs hhs)

/-- Nonnegative reals: the `e`-th root raised to the `m`-th power is the
number itself (when `e * m = 1`). -/
theorem rpow_root_pow {u e : ℝ} (hu : 0 ≤ u) {m : ℕ} (_hm : m ≠ 0)
    (he : e * (m : ℝ) = 1) : (u ^ e) ^ m = u := by
  have h1 : (u ^ e) ^ m = (u ^ e) ^ ((m : ℝ)) := (Real.rpow_natCast (u ^ e) m).symm
  rw [h1, ← Real.rpow_mul hu, he, Real.rpow_one]

/-- The ε-guarantee of the paper's segment choice Eq. (4): with
`r := sourceRecursiveSegments hs k t ε`, the segmented recursive Suzuki word is
within `ε` of `exp(t • ∑ hs)` in operator norm. -/
theorem sourceSegments_error {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hε : 0 < ε) :
    ‖(recursiveSuzukiWord hs k t (sourceRecursiveSegments hs k t ε)).prod -
        NormedSpace.exp (t • hs.sum)‖ ≤ ε := by
  have hr' : 0 < sourceRecursiveSegments hs k t ε := by
    unfold sourceRecursiveSegments
    omega
  have hα : (0 : ℝ) ≤ pfCommAlphaSelf
      (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbound := recursive_matched_error hs k (sourceRecursiveSegments hs k t ε) t hhs hr'
  have hu0 : (0 : ℝ) ≤
      (((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) := by
    have hn : (0 : ℝ) ≤ (Nat.factorial (2 * (k + 1)) : ℝ) *
        pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
        |t| ^ (2 * (k + 1) + 1) := by
      exact mul_nonneg (mul_nonneg (by positivity) hα) (by positivity)
    have hd : (0 : ℝ) < (Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε := by positivity
    exact div_nonneg hn hd.le
  have hrc : (((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^ ((1 : ℝ) / (2 * (k + 1))) ≤
      ((sourceRecursiveSegments hs k t ε : ℕ) : ℝ) := by
    unfold sourceRecursiveSegments
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_max_iff.mpr (Or.inr (le_refl _))
  have hrm : (((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ≤
      ((sourceRecursiveSegments hs k t ε : ℕ) : ℝ) ^ (2 * (k + 1)) := by
    have hkey : ((((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^ ((1 : ℝ) / (2 * (k + 1)))) ^
          (2 * (k + 1)) =
        (((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) :=
      rpow_root_pow hu0 (by positivity) (by push_cast; field_simp)
    refine le_trans hkey.symm.le
      (pow_le_pow_left₀ (Real.rpow_nonneg hu0 _) hrc (2 * (k + 1)))
  have hB0 : (0 : ℝ) ≤ (Nat.factorial (2 * (k + 1) + 1) : ℝ) := by positivity
  have hden : (0 : ℝ) < (Nat.factorial (2 * (k + 1) + 1) : ℝ) *
      ((sourceRecursiveSegments hs k t ε : ℕ) : ℝ) ^ (2 * (k + 1)) := by positivity
  refine hbound.trans ?_
  rw [div_le_iff₀ hden]
  have hf : ε * ((Nat.factorial (2 * (k + 1) + 1) : ℝ) *
      (((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε))) =
      (Nat.factorial (2 * (k + 1)) : ℝ) *
        pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
        |t| ^ (2 * (k + 1) + 1) := by
    have hBne : ((Nat.factorial (2 * (k + 1) + 1) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  calc (Nat.factorial (2 * (k + 1)) : ℝ) *
        pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
        |t| ^ (2 * (k + 1) + 1)
        = ε * ((Nat.factorial (2 * (k + 1) + 1) : ℝ) *
            (((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε))) := hf.symm
    _ ≤ ε * ((Nat.factorial (2 * (k + 1) + 1) : ℝ) *
          ((sourceRecursiveSegments hs k t ε : ℕ) : ℝ) ^ (2 * (k + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrm hB0) hε.le

/-- **Main result (arXiv:1512.03416v1, p. 2–3, Eq. (4))**: for a list `hs` of
skew-Hermitian matrices (the finite-dimensional Lie-algebra specialization of
the paper's generators `ĥ_k`, with `L = |hs|`), recursion depth `k` (Suzuki
order `2p` with `p = k+1`), time `t` and precision `ε > 0`, there are a segment
count `r ≥ 1` and a unitary product `W` of exactly `r * (2 * |hs| * 5^k)` =
`r N_p` exponentials such that `‖W - exp(t • ∑ hs)‖ ≤ ε`.  The word is the
recursive Suzuki word of the frozen construction; the bridge to the frozen
theorem is `Qatlib.Concepts.TrotterFormula.GeneralOrder.clause17`. -/
theorem mainResult_productFormula {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hε : 0 < ε) :
    ∃ (W : Matrix I I ℂ) (r : ℕ) (word : List (Matrix I I ℂ)),
      1 ≤ r ∧ W = word.prod ∧ W ∈ Matrix.unitaryGroup I ℂ ∧
        word.length = r * (2 * hs.length * 5 ^ k) ∧
          ‖W - NormedSpace.exp (t • hs.sum)‖ ≤ ε := by
  have hr : 0 < sourceRecursiveSegments hs k t ε := by
    unfold sourceRecursiveSegments
    omega
  have hspec := (clause17 I).1 hs k (sourceRecursiveSegments hs k t ε) t (fun _ => 0) hhs hr
  exact ⟨(recursiveSuzukiWord hs k t (sourceRecursiveSegments hs k t ε)).prod,
    sourceRecursiveSegments hs k t ε,
    recursiveSuzukiWord hs k t (sourceRecursiveSegments hs k t ε),
    Nat.one_le_iff_ne_zero.mpr (by omega), rfl, hspec.1, hspec.2.1,
    sourceSegments_error hs k t ε hhs hε⟩

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem
