/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.SourceTermCountModel
public import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# TermCountBound — Eq. (5) of arXiv:1512.03416v1

Fixed paper version: arXiv:1512.03416v1 (R. D. Somma, 10 December 2015).
Source: p. 2, Eq. (5)–(6), and the derivation on p. 3, Eqs. (12)–(14).

The paper: for finite-dimensional `g` and `y t ≥ ε`,
`N = O(5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)})` (Eq. (5)),
with `β := maxΣ|γ|` from Eq. (6) and `y := max‖ĥ_k U(λ)|ψ⟩‖`.  The proof
(Eq. (13)–(14)) uses `β_{j+1} ≤ β^j y`, `f_j ≤ 6`, and chooses
`r = ⌈5^{p+2} L^{1+1/p} β y^{1/(2p)} t^{1+1/(2p)}/ε^{1/(2p)}⌉` (Eq. (14)),
then multiplies by `N_p` to reach Eq. (5).

What is formalised here is exactly that last multiplication with an explicit
constant: `N = r N_p` as defined in `SourceTermCountModel` (the segment count is
Eq. (14)), and `N ≤ 20 · (Eq. (5) shape) + N_p`, the additive `N_p` being the
rounding of `⌈·⌉`.  In the regime where Eq. (14) gives at least one segment
(`1 ≤ sourceSegmentReal`, the paper's "suffices to choose r" reading of
`y t ≥ ε`), the additive term is absorbed and the clean bound
`N ≤ 20 · (Eq. (5) shape)` holds.

The abstract Lie-algebra constants `β`, `y` are kept as the paper's real
parameters; the concrete matrix-side certificate `pfCommAlphaSelf` enters through
the frozen `g17` bridge in `SourceMainTheorem`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

/-- Eq. (14) × `N_p` (arXiv:1512.03416v1, p. 3): the real segment count times
`N_p = 2L5^{p-1}` equals `10` times the Eq. (5) shape, since
`5^{p+2}·5^{p-1} = 5·5^{2p}` and `L^{1+1/p}·L = L^{2+1/p}`. -/
theorem sourceSegmentReal_mul_macro {p : ℕ} (hp : 1 ≤ p) {L β y t ε : ℝ}
    (hL : 0 < L) (_hβ : 0 ≤ β) :
    sourceSegmentReal p L β y t ε * sourceMacroCount L p =
      10 * eq5Bound p L β y t ε := by
  have h5 : (5 : ℝ) ^ (p + 2) * (5 : ℝ) ^ (p - 1) = (5 : ℝ) * (5 : ℝ) ^ (2 * p) := by
    rw [← pow_add]
    have he : p + 2 + (p - 1) = 2 * p + 1 := by omega
    rw [he, pow_succ']
  have hLp : L ^ (1 + 1 / (p : ℝ)) * L = L ^ (2 + 1 / (p : ℝ)) := by
    have h : L ^ (2 + 1 / (p : ℝ)) = L ^ (1 + 1 / (p : ℝ)) * L ^ (1 : ℝ) := by
      rw [← Real.rpow_add hL]
      congr 1
      ring
    rw [h, Real.rpow_one]
  unfold sourceSegmentReal sourceMacroCount eq5Bound
  rw [show (5 : ℝ) ^ (p + 2) * L ^ (1 + 1 / (p : ℝ)) * β *
        y ^ (1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ))) /
        ε ^ (1 / (2 * (p : ℝ))) * (2 * L * 5 ^ (p - 1)) =
      ((5 : ℝ) ^ (p + 2) * (5 : ℝ) ^ (p - 1)) *
        (L ^ (1 + 1 / (p : ℝ)) * L) * (2 * β) *
        y ^ (1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ))) /
        ε ^ (1 / (2 * (p : ℝ))) by ring]
  rw [h5, hLp]
  ring

/-- **Eq. (5), derived form (arXiv:1512.03416v1, p. 2–3)**: for `p ≥ 1`, `L ≥ 1`,
`β ≥ 1`, the total number of exponentials `N = r N_p` with the Eq. (14) segment
count satisfies `N ≤ 20 · 5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)}/ε^{1/(2p)}
+ N_p`. -/
theorem sourceNumTerms_le_eq5 {p : ℕ} (hp : 1 ≤ p) {L β y t ε : ℝ}
    (hL : 1 ≤ L) (hβ : 1 ≤ β) (hy : 0 ≤ y) (ht : 0 ≤ t) (hε : 0 < ε) :
    sourceNumTerms p L β y t ε ≤ 20 * eq5Bound p L β y t ε + sourceMacroCount L p := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have hx0 : 0 ≤ sourceSegmentReal p L β y t ε := by
    unfold sourceSegmentReal
    have h1 : (0 : ℝ) ≤ (5 : ℝ) ^ (p + 2) := by positivity
    have h2 : (0 : ℝ) ≤ L ^ (1 + 1 / (p : ℝ)) := Real.rpow_nonneg hLpos.le _
    have h3 : (0 : ℝ) ≤ y ^ (1 / (2 * (p : ℝ))) := Real.rpow_nonneg hy _
    have h4 : (0 : ℝ) ≤ t ^ (1 + 1 / (2 * (p : ℝ))) := Real.rpow_nonneg ht _
    have h5 : (0 : ℝ) ≤ ε ^ (1 / (2 * (p : ℝ))) := (Real.rpow_pos_of_pos hε _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hβ0) h3) h4) h5
  have hceil : (sourceSegments p L β y t ε : ℝ) < sourceSegmentReal p L β y t ε + 1 := by
    unfold sourceSegments
    exact Nat.ceil_lt_add_one hx0
  have hNp : 0 ≤ sourceMacroCount L p := by
    unfold sourceMacroCount
    positivity
  have heq5 : 0 ≤ eq5Bound p L β y t ε := by
    unfold eq5Bound
    have h1 : (0 : ℝ) ≤ (5 : ℝ) ^ (2 * p) := by positivity
    have h2 : (0 : ℝ) ≤ L ^ (2 + 1 / (p : ℝ)) := Real.rpow_nonneg hLpos.le _
    have h3 : (0 : ℝ) ≤ y ^ (1 / (2 * (p : ℝ))) := Real.rpow_nonneg hy _
    have h4 : (0 : ℝ) ≤ t ^ (1 + 1 / (2 * (p : ℝ))) := Real.rpow_nonneg ht _
    have h5 : (0 : ℝ) ≤ ε ^ (1 / (2 * (p : ℝ))) := (Real.rpow_pos_of_pos hε _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hβ0) h3) h4) h5
  calc sourceNumTerms p L β y t ε
      = (sourceSegments p L β y t ε : ℝ) * sourceMacroCount L p := rfl
    _ ≤ (sourceSegmentReal p L β y t ε + 1) * sourceMacroCount L p :=
        mul_le_mul_of_nonneg_right hceil.le hNp
    _ = sourceSegmentReal p L β y t ε * sourceMacroCount L p +
          sourceMacroCount L p := by ring
    _ = 10 * eq5Bound p L β y t ε + sourceMacroCount L p := by
        rw [sourceSegmentReal_mul_macro hp hLpos hβ0]
    _ ≤ 20 * eq5Bound p L β y t ε + sourceMacroCount L p := by
        linarith [heq5]

/-- **Eq. (5), clean form (arXiv:1512.03416v1, p. 2)**: in the regime where
Eq. (14) yields at least one segment (`1 ≤ sourceSegmentReal`, the paper's
`y t ≥ ε` regime), the total number of exponentials is
`N ≤ 20 · 5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}`, i.e. the
paper's `N = O(5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)})` with
explicit constant `20`. -/
theorem sourceNumTerms_le_eq5_of_one_le {p : ℕ} (hp : 1 ≤ p) {L β y t ε : ℝ}
    (hL : 1 ≤ L) (hβ : 1 ≤ β) (_hy : 0 ≤ y) (_ht : 0 ≤ t) (_hε : 0 < ε)
    (hx1 : 1 ≤ sourceSegmentReal p L β y t ε) :
    sourceNumTerms p L β y t ε ≤ 20 * eq5Bound p L β y t ε := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have hx0 : 0 ≤ sourceSegmentReal p L β y t ε := le_trans (by norm_num) hx1
  have hceil : (sourceSegments p L β y t ε : ℝ) < sourceSegmentReal p L β y t ε + 1 := by
    unfold sourceSegments
    exact Nat.ceil_lt_add_one hx0
  have hNp : 0 ≤ sourceMacroCount L p := by
    unfold sourceMacroCount
    positivity
  have hdouble : sourceSegmentReal p L β y t ε + 1 ≤ 2 * sourceSegmentReal p L β y t ε := by
    linarith
  calc sourceNumTerms p L β y t ε
      = (sourceSegments p L β y t ε : ℝ) * sourceMacroCount L p := rfl
    _ ≤ (sourceSegmentReal p L β y t ε + 1) * sourceMacroCount L p :=
        mul_le_mul_of_nonneg_right hceil.le hNp
    _ ≤ (2 * sourceSegmentReal p L β y t ε) * sourceMacroCount L p :=
        mul_le_mul_of_nonneg_right hdouble hNp
    _ = 2 * (sourceSegmentReal p L β y t ε * sourceMacroCount L p) := by ring
    _ = 2 * (10 * eq5Bound p L β y t ε) := by
        rw [sourceSegmentReal_mul_macro hp hLpos hβ0]
    _ = 20 * eq5Bound p L β y t ε := by ring

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

section

set_option backward.isDefEq.respectTransparency false

/-!
## The Eq. (5) shape for the segment count of the recursive Suzuki word

Fixed paper version: arXiv:1512.03416v1 (R. D. Somma, 10 December 2015).
Source: p. 2, Eqs. (5)-(6), and p. 3, Eqs. (12)-(14) of [Somma2016],
[arXiv:1512.03416v1](https://arxiv.org/abs/1512.03416v1),
[doi:10.1063/1.4952761](https://doi.org/10.1063/1.4952761).

`Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem.sourceRecursiveSegments`
is the segment count of the paper's main theorem,
`r = max 1 ⌈(p! α |t|^{p+1} / ((p+1)! ε))^{1/p}⌉` with `p = 2(k+1)` and
`α = Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
(recursiveSuzukiGenerators hs k) (2(k+1)+1)`.  As a function of the commutator
certificate `α` it does not display the Eq. (5) dependence on the paper's
structural constants: Eq. (6) defines `β := max Σ |γ|`, and the derivation on
p. 3 uses `β_{j+1} ≤ β^j y` with `y := max ‖ĥ_k U(λ)|ψ⟩‖`.  This module supplies
that transfer.  If the certificate is dominated by `β^p y` at the matched order
`p = 2(k+1)`, then

`r ≤ 20 · 5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}`,

which is Eq. (5)'s shape, and multiplying by `N_p = 2 L 5^{p-1}` bounds the
number of exponentials of the constructed word.

Two regimes enter as hypotheses rather than conclusions.  `1 ≤ β`: Eq. (6) is a
maximum of sums of absolute structure constants, so `β = 0` occurs only for the
degenerate zero algebra, where the statement is false because `r ≥ 1` while the
right-hand side vanishes.  `1 ≤ eq5Bound …` is the paper's `y t ≥ ε` regime, in
which Eq. (14) yields at least one segment; it is what turns the ceiling into a
bounded additive term.

Boundary: the paper's real Lie algebra is represented by its finite matrix
specialisation; `β` and `y` are carried as real parameters rather than computed
from structure constants or from the state.  Nothing here re-proves the error
estimate of `mainResult_productFormula`; only the scalar bookkeeping of
Eqs. (5) and (14) is related.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem
open Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

/-- Ceiling arithmetic for an `n`-th root: if `x ≤ R ^ n` and `1 ≤ R`, then the
ceiling of the `n`-th root of `x` is at most `R + 1`, and the `max 1` of a
segment count is at most `20 R`. -/
private lemma ceil_rpow_inv_le {n : ℕ} (hn : 1 ≤ n) {x R : ℝ} (hx : 0 ≤ x)
    (hxR : x ≤ R ^ n) (hR : 1 ≤ R) :
    (max 1 (Nat.ceil (x ^ ((n : ℝ)⁻¹))) : ℝ) ≤ 20 * R := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hnne : n ≠ 0 := by omega
  have hroot : x ^ ((n : ℝ)⁻¹) ≤ R := by
    have h := Real.rpow_le_rpow hx hxR (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast hRpos.le hnne] at h
  have hceil : (Nat.ceil (x ^ ((n : ℝ)⁻¹)) : ℝ) ≤ x ^ ((n : ℝ)⁻¹) + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hx _)).le
  apply max_le
  · linarith
  · linarith

/-- The pre-ceiling segment count of Eq. (14) of arXiv:1512.03416v1, taken to the
`p = 2(k+1)` root, is at most `β y^{1/p} t^{1+1/p} / ε^{1/p}`: the factorial
ratio `p!/(p+1)! = 1/(p+1)` and the certificate hypothesis `α ≤ β^p y` leave
exactly that monomial. -/
private lemma segmentRoot_le_eq5Factor {k : ℕ} {β y t ε α : ℝ}
    (hβ : 1 ≤ β) (ht : 0 < t) (hε : 0 < ε) (hα0 : 0 ≤ α)
    (hαβ : α ≤ β ^ (2 * (k + 1)) * y) :
    (((Nat.factorial (2 * (k + 1)) : ℝ) * α * |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^ (((2 * (k + 1) : ℕ)) : ℝ)⁻¹ ≤
      β * y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) *
        t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) /
        ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) := by
  have hn1 : 1 ≤ 2 * (k + 1) := by omega
  have hnne : (2 * (k + 1) : ℕ) ≠ 0 := by omega
  have hβ0 : (0 : ℝ) < β := by linarith
  have hy0 : (0 : ℝ) ≤ y := by
    have h : (0 : ℝ) ≤ y * β ^ (2 * (k + 1)) := by
      rw [mul_comm]
      exact le_trans hα0 hαβ
    exact nonneg_of_mul_nonneg_left h (pow_pos hβ0 _)
  have hA0 : 0 ≤ (Nat.factorial (2 * (k + 1)) : ℝ) * α * |t| ^ (2 * (k + 1) + 1) /
      ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by positivity) hα0) (by positivity)
    · positivity
  have hfac : (Nat.factorial (2 * (k + 1) + 1) : ℝ) =
      (((2 * (k + 1) : ℕ) : ℝ) + 1) * (Nat.factorial (2 * (k + 1)) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hden0 : (0 : ℝ) < (((2 * (k + 1) : ℕ) : ℝ) + 1) * ε := by positivity
  have hAB : (Nat.factorial (2 * (k + 1)) : ℝ) * α * |t| ^ (2 * (k + 1) + 1) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε) ≤
      β ^ (2 * (k + 1)) * y * t ^ (2 * (k + 1) + 1) / ε := by
    rw [abs_of_pos ht, hfac]
    have hcancel : (Nat.factorial (2 * (k + 1)) : ℝ) * α * t ^ (2 * (k + 1) + 1) /
          ((((2 * (k + 1) : ℕ) : ℝ) + 1) * (Nat.factorial (2 * (k + 1)) : ℝ) * ε)
        = α * t ^ (2 * (k + 1) + 1) / ((((2 * (k + 1) : ℕ) : ℝ) + 1) * ε) := by
      have hnf : (Nat.factorial (2 * (k + 1)) : ℝ) ≠ 0 := by positivity
      have hn1' : (((2 * (k + 1) : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      have hεne : ε ≠ 0 := ne_of_gt hε
      field_simp
    rw [hcancel]
    have hstep : α * t ^ (2 * (k + 1) + 1) ≤
        (β ^ (2 * (k + 1)) * y) * t ^ (2 * (k + 1) + 1) :=
      mul_le_mul_of_nonneg_right hαβ (by positivity)
    calc α * t ^ (2 * (k + 1) + 1) / ((((2 * (k + 1) : ℕ) : ℝ) + 1) * ε)
        ≤ (β ^ (2 * (k + 1)) * y) * t ^ (2 * (k + 1) + 1) /
            ((((2 * (k + 1) : ℕ) : ℝ) + 1) * ε) :=
          div_le_div_of_nonneg_right hstep hden0.le
      _ ≤ β ^ (2 * (k + 1)) * y * t ^ (2 * (k + 1) + 1) / ε := by
          apply div_le_div_of_nonneg_left (by positivity) hε
          nlinarith [hden0, hε]
  have hZ0 : 0 ≤ β * y ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) *
      t ^ (1 + (((2 * (k + 1) : ℕ) : ℝ)⁻¹)) / ε ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) := by
    have hy' : (0 : ℝ) ≤ y ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) := Real.rpow_nonneg hy0 _
    have ht' : (0 : ℝ) ≤ t ^ (1 + (((2 * (k + 1) : ℕ) : ℝ)⁻¹)) :=
      Real.rpow_nonneg ht.le _
    have hε' : (0 : ℝ) < ε ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) :=
      Real.rpow_pos_of_pos hε _
    exact div_nonneg (mul_nonneg (mul_nonneg hβ0.le hy') ht') hε'.le
  have hZpow : (β * y ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) *
        t ^ (1 + (((2 * (k + 1) : ℕ) : ℝ)⁻¹)) / ε ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹)) ^
        (2 * (k + 1)) = β ^ (2 * (k + 1)) * y * t ^ (2 * (k + 1) + 1) / ε := by
    rw [div_pow, mul_pow, mul_pow, Real.rpow_inv_natCast_pow (n := 2 * (k + 1)) hy0 hnne,
      Real.rpow_inv_natCast_pow (n := 2 * (k + 1)) hε.le hnne]
    have hT : t ^ (1 + (((2 * (k + 1) : ℕ) : ℝ)⁻¹)) =
        t * t ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) := by
      rw [Real.rpow_add ht, Real.rpow_one]
    rw [hT, mul_pow, Real.rpow_inv_natCast_pow (n := 2 * (k + 1)) ht.le hnne]
    ring
  calc (((Nat.factorial (2 * (k + 1)) : ℝ) * α * |t| ^ (2 * (k + 1) + 1)) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹)
      ≤ (β ^ (2 * (k + 1)) * y * t ^ (2 * (k + 1) + 1) / ε) ^
          (((2 * (k + 1) : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow hA0 hAB (by positivity)
    _ = β * y ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) *
        t ^ (1 + (((2 * (k + 1) : ℕ) : ℝ)⁻¹)) /
        ε ^ (((2 * (k + 1) : ℕ) : ℝ)⁻¹) := by
        rw [← hZpow]
        exact Real.pow_rpow_inv_natCast (n := 2 * (k + 1)) hZ0 hnne

/-- **Eq. (5) shape for the segment count of Eq. (14) (arXiv:1512.03416v1, p. 2-3)**:
if the commutator certificate `pfCommAlphaSelf` of the recursive Suzuki generators
is dominated by `β^p y` at the matched order `p = 2(k+1)`, and `β ≥ 1`, `t > 0`
and the Eq. (5) shape is at least `1` (the paper's `y t ≥ ε` regime), then the
segment count actually used by the constructed word satisfies the paper's
`N = O(5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)})` with explicit
constant `20`. -/
theorem sourceRecursiveSegments_le_eq5_shape {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε β y : ℝ)
    (hε : 0 < ε) (hL : 1 ≤ hs.length) (hβ : 1 ≤ β) (ht : 0 < t)
    (hβy : pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) ≤
      β ^ (2 * (k + 1)) * y)
    (hge : 1 ≤ eq5Bound (k + 1) (hs.length : ℝ) β y t ε) :
    (sourceRecursiveSegments hs k t ε : ℝ) ≤
      20 * eq5Bound (k + 1) (hs.length : ℝ) β y t ε := by
  set L : ℝ := (hs.length : ℝ)
  have hL1 : 1 ≤ L := by
    rw [show L = (hs.length : ℝ) from rfl]
    exact_mod_cast hL
  have hexp : (1 : ℝ) / (2 * (k + 1)) = (((2 * (k + 1) : ℕ)) : ℝ)⁻¹ := by
    rw [one_div]
    push_cast
    ring
  have hα0 : (0 : ℝ) ≤ pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hroot := segmentRoot_le_eq5Factor (k := k) (β := β) (y := y) (t := t) (ε := ε)
    (α := pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1))
    hβ ht hε hα0 hβy
  have hA0 : 0 ≤ (Nat.factorial (2 * (k + 1)) : ℝ) *
      pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
      |t| ^ (2 * (k + 1) + 1) / ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by positivity) hα0) (by positivity)
    · positivity
  have hy0 : (0 : ℝ) ≤ y := by
    have h : (0 : ℝ) ≤ y * β ^ (2 * (k + 1)) := by
      have h0 : (0 : ℝ) ≤ β ^ (2 * (k + 1)) * y := le_trans hα0 hβy
      rwa [mul_comm (β ^ (2 * (k + 1))) y] at h0
    exact nonneg_of_mul_nonneg_left h (pow_pos (by linarith : (0 : ℝ) < β) _)
  have hB0 : 0 ≤ β * y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) *
      t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) / ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) := by
    have hy' : (0 : ℝ) ≤ y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) := Real.rpow_nonneg hy0 _
    have ht' : (0 : ℝ) ≤ t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) :=
      Real.rpow_nonneg ht.le _
    have hε' : (0 : ℝ) < ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) := Real.rpow_pos_of_pos hε _
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hy') ht') hε'.le
  have heq5 : eq5Bound (k + 1) L β y t ε =
      (5 ^ (2 * (k + 1)) * L ^ (2 + 1 / ((k : ℝ) + 1))) *
        (β * y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) *
          t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) /
          ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) := by
    unfold eq5Bound
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hF1 : (1 : ℝ) ≤ 5 ^ (2 * (k + 1)) * L ^ (2 + 1 / ((k : ℝ) + 1)) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (Real.one_le_rpow hL1 (by positivity))
  have hBle : β * y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) *
      t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) / ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) ≤
      eq5Bound (k + 1) L β y t ε := by
    rw [heq5]
    calc β * y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) *
          t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) / ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)
        = 1 * (β * y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) *
            t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) /
            ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hF1 hB0
  have hstep : ((Nat.factorial (2 * (k + 1)) : ℝ) *
        pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
        |t| ^ (2 * (k + 1) + 1) / ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ≤
      eq5Bound (k + 1) L β y t ε ^ (2 * (k + 1)) := by
    have h1 : (((Nat.factorial (2 * (k + 1)) : ℝ) *
          pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1) / ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^
          (((2 * (k + 1) : ℕ) : ℝ)⁻¹)) ^ (2 * (k + 1)) ≤
        (β * y ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹) *
          t ^ (1 + ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) /
          ε ^ ((((2 * (k + 1) : ℕ)) : ℝ)⁻¹)) ^
          (2 * (k + 1)) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hA0 _) hroot _
    rw [Real.rpow_inv_natCast_pow (n := 2 * (k + 1)) hA0 (by omega)] at h1
    exact h1.trans (pow_le_pow_left₀ hB0 hBle _)
  unfold sourceRecursiveSegments
  rw [show (1 : ℝ) / (2 * (k + 1)) = (((2 * (k + 1) : ℕ)) : ℝ)⁻¹ from hexp]
  rw [Nat.cast_max, Nat.cast_one]
  exact ceil_rpow_inv_le (n := 2 * (k + 1)) (by omega) hA0 hstep hge

/-- **Eq. (5) for the number of exponentials of the constructed word**: the
segment bound of `sourceRecursiveSegments_le_eq5_shape` multiplied by the paper's
`N_p = 2 L 5^{p-1}` (here `p = k+1`) bounds the length `r N_p` of the recursive
Suzuki word of the main theorem. -/
theorem sourceRecursiveTermCount_le_eq5_shape {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε β y : ℝ)
    (hε : 0 < ε) (hL : 1 ≤ hs.length) (hβ : 1 ≤ β) (ht : 0 < t)
    (hβy : pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) ≤
      β ^ (2 * (k + 1)) * y)
    (hge : 1 ≤ eq5Bound (k + 1) (hs.length : ℝ) β y t ε) :
    (sourceRecursiveSegments hs k t ε : ℝ) * (2 * (hs.length : ℝ) * 5 ^ k) ≤
      20 * eq5Bound (k + 1) (hs.length : ℝ) β y t ε * (2 * (hs.length : ℝ) * 5 ^ k) := by
  have hNp : (0 : ℝ) ≤ 2 * (hs.length : ℝ) * 5 ^ k := by positivity
  exact mul_le_mul_of_nonneg_right
    (sourceRecursiveSegments_le_eq5_shape hs k t ε β y hε hL hβ ht hβy hge) hNp

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

end
