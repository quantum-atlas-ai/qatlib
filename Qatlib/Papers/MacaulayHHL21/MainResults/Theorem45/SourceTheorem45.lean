/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel
import Qatlib.Papers.MacaulayHHL21.MainResults.Lemma43.SourceLemma43
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4.5 — lower bound on the truncated QLS condition number

Fixed paper: arXiv:2111.00405, Theorem 4.5 on p.9 (with equations (9), (10), (11) and
Lemmas 4.3, 4.4).

Statement (verbatim): *Suppose `a₁, …, a_t ∈ {0,1}ⁿ` are the `t` solutions of
`F = F₁ ∪ F₂` … and let `h` be the minimum Hamming weight of the `t` solutions. Let `d` be
the selected degree … If all the `t` solutions have the same Hamming weight `h` or the
minimum ℓ2-norm solution vector `y = M⁺b` is in the convex hull of `y₁, …, y_t`, then the
tQLScn of `M` … using max degree is `κ_b(M) ≥ √(((d+1)^h − 1)/t)`, and using total degree
is `κ_b(M) ≥ √((C(d+h,h) − 1)/t).`*

The paper's derivation is exactly the composition of equation (9) (`κ_b(M) ≥ ‖M⁺b‖`), the
norm formulas (10)/(11) for a monomial solution vector of Hamming weight `h`, and the hull
lower bound of Lemma 4.3 (equal weights) or Lemma 4.4 (convex hull).  The arithmetic core is
proved once in `tqlscn_lowerBound_of_normBound`; the equal-weight branch is derived from
`lemma43_affineHull_l2_lowerBound`.  The convex-hull branch takes the Lemma 4.4 norm bound
as an explicit hypothesis, because Lemma 4.4 is proved for real 0/1 vectors in
`Lemma44/SourceLemma44.lean` and transporting it to the complex model is a separate bridge
(recorded in the accompanying PR notes).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Theorem45

open Qatlib.Papers.MacaulayHHL21.MainResults
open Qatlib.Papers.MacaulayHHL21.MainResults.Lemma43

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Arithmetic core of Theorem 4.5 (p.9): if `‖y₀‖ = √R`, `‖y₀‖ ≤ √t·‖y‖`, `‖M‖ ≥ 1`,
`‖b‖ = 1`, then `κ_b(M) = ‖M‖·‖y‖/‖b‖ ≥ √(R/t)`.  This is the combination of equation (9)
with the norm lower bound supplied by Lemma 4.3 or Lemma 4.4. -/
theorem tqlscn_lowerBound_of_normBound
    {t : ℕ} {R : ℝ} [NeZero t] (hR : 0 ≤ R)
    {y0Norm yNorm matNorm bNorm : ℝ}
    (hy0 : y0Norm = Real.sqrt R)
    (hbound : y0Norm ≤ Real.sqrt (t : ℝ) * yNorm)
    (hM : 1 ≤ matNorm) (hb : bNorm = 1) :
    Real.sqrt (R / (t : ℝ)) ≤ tqlscn matNorm yNorm bNorm := by
  have ht : 0 < t := Nat.pos_of_neZero t
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hbase : Real.sqrt R ≤ Real.sqrt (t : ℝ) * yNorm := by
    rw [← hy0]; exact hbound
  have hmain : Real.sqrt (R / (t : ℝ)) ≤ yNorm := by
    rw [Real.sqrt_div hR (t : ℝ), div_le_iff₀ (Real.sqrt_pos.mpr htpos)]
    rw [mul_comm yNorm (Real.sqrt (t : ℝ))]
    exact hbase
  have hy : 0 ≤ yNorm := le_trans (Real.sqrt_nonneg _) hmain
  have hmn : yNorm ≤ tqlscn matNorm yNorm bNorm :=
    tqlscn_ge_minNormSolution hM hb hy
  linarith [hmain, hmn]

/-- Theorem 4.5 (arXiv:2111.00405, p.9), max-degree form, equal-Hamming-weight case:
combining equation (10) `‖yᵢ‖² = (d+1)^h − 1`, Lemma 4.3 (the minimum-norm solution lies in
the complex affine hull) and equation (9). -/
theorem theorem45_maxDegree_sameWeight
    {t d h : ℕ} [NeZero t] (Y : Fin t → ι → ℂ)
    (hZ : ∀ i, IsZeroOne (Y i))
    (hSame : ∀ i, hammingWeight (Y i) = h)
    {y : ι → ℂ} (hy : y ∈ affineHull Y)
    (hY0 : l2NormSq (Y 0) = ((d : ℝ) + 1) ^ h - 1)
    {matNorm bNorm : ℝ} (hM : 1 ≤ matNorm) (hb : bNorm = 1) :
    Real.sqrt ((((d : ℝ) + 1) ^ h - 1) / (t : ℝ)) ≤ tqlscn matNorm (l2Norm y) bNorm := by
  classical
  have ht : 0 < t := Nat.pos_of_neZero t
  have hEq : ∀ i, hammingWeight (Y i) = hammingWeight (Y 0) := by
    intro i; rw [hSame i, hSame 0]
  have h43 : l2Norm (Y 0) ≤ Real.sqrt (t : ℝ) * l2Norm y :=
    lemma43_affineHull_l2_lowerBound Y hZ hEq hy
  have hnormY0 : l2Norm (Y 0) = Real.sqrt (((d : ℝ) + 1) ^ h - 1) := by
    rw [l2Norm, hY0]
  have hrad : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ h - 1 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hbase : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith
    have h1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ h := one_le_pow₀ hbase
    linarith
  exact tqlscn_lowerBound_of_normBound hrad hnormY0 h43 hM hb

/-- Theorem 4.5 (arXiv:2111.00405, p.9), total-degree form, equal-Hamming-weight case:
combining equation (11) `‖yᵢ‖² = C(d+h,h) − 1`, Lemma 4.3 and equation (9). -/
theorem theorem45_totalDegree_sameWeight
    {t d h : ℕ} [NeZero t] (Y : Fin t → ι → ℂ)
    (hZ : ∀ i, IsZeroOne (Y i))
    (hSame : ∀ i, hammingWeight (Y i) = h)
    {y : ι → ℂ} (hy : y ∈ affineHull Y)
    (hY0 : l2NormSq (Y 0) = (Nat.choose (d + h) h : ℝ) - 1)
    {matNorm bNorm : ℝ} (hM : 1 ≤ matNorm) (hb : bNorm = 1) :
    Real.sqrt (((Nat.choose (d + h) h : ℝ) - 1) / (t : ℝ)) ≤
      tqlscn matNorm (l2Norm y) bNorm := by
  classical
  have ht : 0 < t := Nat.pos_of_neZero t
  have hEq : ∀ i, hammingWeight (Y i) = hammingWeight (Y 0) := by
    intro i; rw [hSame i, hSame 0]
  have h43 : l2Norm (Y 0) ≤ Real.sqrt (t : ℝ) * l2Norm y :=
    lemma43_affineHull_l2_lowerBound Y hZ hEq hy
  have hnormY0 : l2Norm (Y 0) = Real.sqrt ((Nat.choose (d + h) h : ℝ) - 1) := by
    rw [l2Norm, hY0]
  have hrad : (0 : ℝ) ≤ (Nat.choose (d + h) h : ℝ) - 1 := by
    have hle : h ≤ d + h := Nat.le_add_left h d
    have hpos : 0 < Nat.choose (d + h) h := Nat.choose_pos hle
    have hpos1 : (1 : ℝ) ≤ (Nat.choose (d + h) h : ℝ) := by exact_mod_cast hpos
    linarith
  exact tqlscn_lowerBound_of_normBound hrad hnormY0 h43 hM hb

/-- Theorem 4.5 (arXiv:2111.00405, p.9), max-degree form, convex-hull case: when the
minimum-norm solution lies in the convex hull, Lemma 4.4 supplies `‖Y 0‖ ≤ √t·‖y‖`; equation
(10) and (9) then give the bound.  The Lemma 4.4 norm bound is an explicit hypothesis here. -/
theorem theorem45_maxDegree_convexHull
    {t d h : ℕ} [NeZero t] (Y : Fin t → ι → ℂ)
    (hY0 : l2NormSq (Y 0) = ((d : ℝ) + 1) ^ h - 1) (hZ : IsZeroOne (Y 0))
    {y : ι → ℂ}
    (hconv : l2Norm (Y 0) ≤ Real.sqrt (t : ℝ) * l2Norm y)
    {matNorm bNorm : ℝ} (hM : 1 ≤ matNorm) (hb : bNorm = 1) :
    Real.sqrt ((((d : ℝ) + 1) ^ h - 1) / (t : ℝ)) ≤ tqlscn matNorm (l2Norm y) bNorm := by
  have hnormY0 : l2Norm (Y 0) = Real.sqrt (((d : ℝ) + 1) ^ h - 1) := by
    rw [l2Norm, hY0]
  have hrad : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ h - 1 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hbase : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith
    have h1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ h := one_le_pow₀ hbase
    linarith
  exact tqlscn_lowerBound_of_normBound hrad hnormY0 hconv hM hb

/-- Theorem 4.5 (arXiv:2111.00405, p.9), total-degree form, convex-hull case. -/
theorem theorem45_totalDegree_convexHull
    {t d h : ℕ} [NeZero t] (Y : Fin t → ι → ℂ)
    (hY0 : l2NormSq (Y 0) = (Nat.choose (d + h) h : ℝ) - 1) (hZ : IsZeroOne (Y 0))
    {y : ι → ℂ}
    (hconv : l2Norm (Y 0) ≤ Real.sqrt (t : ℝ) * l2Norm y)
    {matNorm bNorm : ℝ} (hM : 1 ≤ matNorm) (hb : bNorm = 1) :
    Real.sqrt (((Nat.choose (d + h) h : ℝ) - 1) / (t : ℝ)) ≤
      tqlscn matNorm (l2Norm y) bNorm := by
  have hnormY0 : l2Norm (Y 0) = Real.sqrt ((Nat.choose (d + h) h : ℝ) - 1) := by
    rw [l2Norm, hY0]
  have hrad : (0 : ℝ) ≤ (Nat.choose (d + h) h : ℝ) - 1 := by
    have hle : h ≤ d + h := Nat.le_add_left h d
    have hpos : 0 < Nat.choose (d + h) h := Nat.choose_pos hle
    have hpos1 : (1 : ℝ) ≤ (Nat.choose (d + h) h : ℝ) := by exact_mod_cast hpos
    linarith
  exact tqlscn_lowerBound_of_normBound hrad hnormY0 hconv hM hb

/-- **Theorem 4.5** (arXiv:2111.00405, p.9), max-degree form: under the paper's disjunction
("all `t` solutions have the same Hamming weight `h`" or "the minimum-norm solution lies in
the convex hull"), `κ_b(M) ≥ √(((d+1)^h − 1)/t)`. -/
theorem theorem45_maxDegree
    {t d h : ℕ} [NeZero t] (Y : Fin t → ι → ℂ)
    (hZ : ∀ i, IsZeroOne (Y i))
    {y : ι → ℂ} (hy : y ∈ affineHull Y)
    (hY0 : l2NormSq (Y 0) = ((d : ℝ) + 1) ^ h - 1)
    (hcase : (∀ i, hammingWeight (Y i) = h) ∨
      (l2Norm (Y 0) ≤ Real.sqrt (t : ℝ) * l2Norm y))
    {matNorm bNorm : ℝ} (hM : 1 ≤ matNorm) (hb : bNorm = 1) :
    Real.sqrt ((((d : ℝ) + 1) ^ h - 1) / (t : ℝ)) ≤ tqlscn matNorm (l2Norm y) bNorm := by
  rcases hcase with hsame | hconv
  · exact theorem45_maxDegree_sameWeight Y hZ hsame hy hY0 hM hb
  · exact theorem45_maxDegree_convexHull Y hY0 (hZ 0) hconv hM hb

/-- **Theorem 4.5** (arXiv:2111.00405, p.9), total-degree form: under the paper's
disjunction, `κ_b(M) ≥ √((C(d+h,h) − 1)/t)`. -/
theorem theorem45_totalDegree
    {t d h : ℕ} [NeZero t] (Y : Fin t → ι → ℂ)
    (hZ : ∀ i, IsZeroOne (Y i))
    {y : ι → ℂ} (hy : y ∈ affineHull Y)
    (hY0 : l2NormSq (Y 0) = (Nat.choose (d + h) h : ℝ) - 1)
    (hcase : (∀ i, hammingWeight (Y i) = h) ∨
      (l2Norm (Y 0) ≤ Real.sqrt (t : ℝ) * l2Norm y))
    {matNorm bNorm : ℝ} (hM : 1 ≤ matNorm) (hb : bNorm = 1) :
    Real.sqrt (((Nat.choose (d + h) h : ℝ) - 1) / (t : ℝ)) ≤
      tqlscn matNorm (l2Norm y) bNorm := by
  rcases hcase with hsame | hconv
  · exact theorem45_totalDegree_sameWeight Y hZ hsame hy hY0 hM hb
  · exact theorem45_totalDegree_convexHull Y hY0 (hZ 0) hconv hM hb

end Qatlib.Papers.MacaulayHHL21.MainResults.Theorem45
