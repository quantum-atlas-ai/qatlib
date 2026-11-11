/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option backward.isDefEq.respectTransparency false

/-!
# CorrWalkSim16, Lemma 1: the coefficient functional `s`

Berry--Novo, *Corrected quantum walk for optimal Hamiltonian simulation*,
arXiv:1606.03443v3. Lemma 1 and Eq. (42) on PDF p. 8.

A *function of the walk step* `U` is represented by its coefficient family
`F : ℤ → ℂ`, standing for `∑ n, F n • U^n`.  Eq. (42) defines

  `s(F) := ∑ n, ‖F n‖`,

the `ℓ¹` weight of the coefficients, which is the success-amplitude budget of
the linear-combination-of-unitaries step.  This file proves the three
assertions of Lemma 1:

* Eq. (43), `s(αF + βG) ≤ ‖α‖ s(F) + ‖β‖ s(G)` (`coeffL1_affine_le`);
* Eq. (44), `s(F G) ≤ s(F) s(G)` for the coefficient convolution
  `(F G) n = ∑ k, F (n - k) * G k` (`coeffL1_conv_le`);
* Eq. (45), equality in the first bound when `F` and `G` live on disjoint sets
  of powers (`coeffL1_affine_eq_of_disjoint`).

The convolution bound is the `ℓ¹` convolution inequality: the paper's proof
Eqs. (48)-(49) sums the absolute values of the Cauchy product; here it is done
by reindexing the product family over `ℤ × ℤ` along the fiber of the addition
map, which is the same computation written with infinite sums.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.CorrWalkSim16.MainResults

open scoped BigOperators

/-- Eq. (42): the functional `s(F) = ∑ n, |F n|` of a coefficient family. -/
def coeffL1 (F : ℤ → ℂ) : ℝ := ∑' n, ‖F n‖

/-- The coefficient family of the product `F G` of two functions of `U`
(Eq. (48) of the paper): `(F G) n = ∑ k, F (n - k) G k`. -/
def coeffMul (F G : ℤ → ℂ) : ℤ → ℂ := fun n => ∑' k : ℤ, F (n - k) * G k

/-- The coefficient family of the adjoint `F†`: the `n`-th coefficient is the
conjugate of the `(-n)`-th coefficient, since `U` is unitary. -/
def coeffStar (F : ℤ → ℂ) : ℤ → ℂ := fun n => (starRingEnd ℂ) (F (-n))

/-- Reindexing `k ↦ (n - k, k)` identifies `ℤ` with the fiber of addition at `n`. -/
def addFiberEquiv (n : ℤ) : {p : ℤ × ℤ // p.1 + p.2 = n} ≃ ℤ where
  toFun p := p.val.2
  invFun k := ⟨(n - k, k), by ring⟩
  left_inv p := by
    have hp : p.val.1 + p.val.2 = n := p.property
    refine Subtype.ext ?_
    refine Prod.ext ?_ rfl
    show n - p.val.2 = p.val.1
    omega
  right_inv k := rfl

/-- The fiber sums of the product family are the convolution sums. -/
theorem tsum_addFiber_eq (F G : ℤ → ℂ) (n : ℤ) :
    (∑' p : {p : ℤ × ℤ // p.1 + p.2 = n}, ‖F p.val.1‖ * ‖G p.val.2‖)
      = ∑' k : ℤ, ‖F (n - k)‖ * ‖G k‖ := by
  rw [← Equiv.tsum_eq (addFiberEquiv n) (fun k : ℤ => ‖F (n - k)‖ * ‖G k‖)]
  refine tsum_congr fun p => ?_
  have hnk : n - p.val.2 = p.val.1 := by
    have hp : p.val.1 + p.val.2 = n := p.property
    omega
  show ‖F p.val.1‖ * ‖G p.val.2‖ = ‖F (n - p.val.2)‖ * ‖G p.val.2‖
  rw [hnk]

/-- The product of two nonnegative norm families is summable on `ℤ × ℤ`. -/
theorem summable_mul_norm_prod (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) :
    Summable fun p : ℤ × ℤ => ‖F p.1‖ * ‖G p.2‖ :=
  Summable.mul_of_nonneg hF hG (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- The total mass of the product family factors. -/
theorem tsum_mul_norm_prod (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) :
    (∑' p : ℤ × ℤ, ‖F p.1‖ * ‖G p.2‖) = (∑' n, ‖F n‖) * ∑' n, ‖G n‖ := by
  have hfg := summable_mul_norm_prod F G hF hG
  have h1 : (∑' p : ℤ × ℤ, ‖F p.1‖ * ‖G p.2‖)
      = ∑' b : ℤ, ∑' c : ℤ, ‖F b‖ * ‖G c‖ := hfg.tsum_prod
  rw [h1]
  have h2 : ∀ b : ℤ, (∑' c : ℤ, ‖F b‖ * ‖G c‖) = ‖F b‖ * ∑' c, ‖G c‖ := by
    intro b
    exact tsum_mul_left
  rw [tsum_congr h2]
  exact tsum_mul_right

/-- The convolution sums are summable whenever both coefficient families are
absolutely summable. -/
theorem summable_norm_conv (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) (n : ℤ) :
    Summable fun k : ℤ => ‖F (n - k)‖ * ‖G k‖ := by
  have hF' : Summable fun k : ℤ => ‖F (n - k)‖ := by
    simpa only [Function.comp_def] using hF.comp_injective (i := fun k : ℤ => n - k)
      (by
        intro a b h
        have h' : n + (-a) = n + (-b) := by simpa [sub_eq_add_neg] using h
        exact neg_injective (add_left_cancel h'))
  have hmul : Summable fun p : ℤ × ℤ => ‖F (n - p.1)‖ * ‖G p.2‖ :=
    Summable.mul_of_nonneg hF' hG (fun k => norm_nonneg _) (fun k => norm_nonneg _)
  simpa only [Function.comp_def] using hmul.comp_injective
    (i := fun k : ℤ => (k, k)) (by intro a b h; simpa using h)

/-- Eq. (49): the modulus of the `n`-th product coefficient is bounded by the
`n`-th convolution sum of absolute values. -/
theorem norm_coeffMul_le (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) (n : ℤ) :
    ‖coeffMul F G n‖ ≤ ∑' k : ℤ, ‖F (n - k)‖ * ‖G k‖ := by
  have hsum := summable_norm_conv F G hF hG n
  have hnorm : Summable fun k : ℤ => ‖F (n - k) * G k‖ := by
    refine hsum.congr fun k => ?_
    simp
  have h1 := norm_tsum_le_tsum_norm hnorm
  refine h1.trans_eq ?_
  exact tsum_congr fun k => by simp

/-- The coefficient families of products of absolutely summable families are
absolutely summable. -/
theorem summable_norm_coeffMul (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) :
    Summable fun n => ‖coeffMul F G n‖ := by
  have hfg := summable_mul_norm_prod F G hF hG
  have hfib : Summable fun n : ℤ =>
      ∑' p : {p : ℤ × ℤ // p.1 + p.2 = n}, ‖F p.val.1‖ * ‖G p.val.2‖ :=
    (hfg.hasSum.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)).summable
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hfib
  refine le_trans (norm_coeffMul_le F G hF hG n) ?_
  rw [tsum_addFiber_eq]

/-- Eq. (43): subadditivity of `s` under affine combinations. -/
theorem coeffL1_affine_le (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) (α β : ℂ) :
    coeffL1 (fun n => α * F n + β * G n) ≤ ‖α‖ * coeffL1 F + ‖β‖ * coeffL1 G := by
  have hα : Summable fun n => ‖α‖ * ‖F n‖ := hF.mul_left ‖α‖
  have hβ : Summable fun n => ‖β‖ * ‖G n‖ := hG.mul_left ‖β‖
  have hsum : Summable fun n => ‖α * F n + β * G n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hα.add hβ)
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
  calc coeffL1 (fun n => α * F n + β * G n) = ∑' n, ‖α * F n + β * G n‖ := rfl
    _ ≤ ∑' n, (‖α‖ * ‖F n‖ + ‖β‖ * ‖G n‖) := by
          refine hsum.tsum_le_tsum (fun n => ?_) (hα.add hβ)
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, norm_mul]
    _ = (∑' n, ‖α‖ * ‖F n‖) + ∑' n, ‖β‖ * ‖G n‖ := Summable.tsum_add hα hβ
    _ = ‖α‖ * coeffL1 F + ‖β‖ * coeffL1 G := by
          rw [tsum_mul_left, tsum_mul_left]
          rfl

/-- Eq. (43) for plain sums: `s(F + G) ≤ s(F) + s(G)`. -/
theorem coeffL1_add_le (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) :
    coeffL1 (fun n => F n + G n) ≤ coeffL1 F + coeffL1 G := by
  have := coeffL1_affine_le F G hF hG (1 : ℂ) (1 : ℂ)
  simpa using this

/-- Eq. (44): submultiplicativity of `s` under the coefficient product. -/
theorem coeffL1_conv_le (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) :
    coeffL1 (coeffMul F G) ≤ coeffL1 F * coeffL1 G := by
  have hfg := summable_mul_norm_prod F G hF hG
  have hfibSummable :
      Summable fun n : ℤ => ∑' p : {p : ℤ × ℤ // p.1 + p.2 = n}, ‖F p.val.1‖ * ‖G p.val.2‖ :=
    (hfg.hasSum.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)).summable
  have hnorm :
      ∀ n : ℤ, ‖coeffMul F G n‖
        ≤ ∑' p : {p : ℤ × ℤ // p.1 + p.2 = n}, ‖F p.val.1‖ * ‖G p.val.2‖ := by
    intro n
    refine le_trans (norm_coeffMul_le F G hF hG n) ?_
    rw [tsum_addFiber_eq]
  have hsummable : Summable fun n : ℤ => ‖coeffMul F G n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hfibSummable
  calc coeffL1 (coeffMul F G) = ∑' n, ‖coeffMul F G n‖ := rfl
    _ ≤ ∑' n, ∑' p : {p : ℤ × ℤ // p.1 + p.2 = n}, ‖F p.val.1‖ * ‖G p.val.2‖ :=
          hsummable.tsum_le_tsum hnorm hfibSummable
    _ = ∑' p : ℤ × ℤ, ‖F p.1‖ * ‖G p.2‖ :=
          (hfg.hasSum.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)).tsum_eq
    _ = (∑' n, ‖F n‖) * ∑' n, ‖G n‖ := tsum_mul_norm_prod F G hF hG
    _ = coeffL1 F * coeffL1 G := rfl

/-- Eq. (45): on disjoint sets of powers the affine bound is an equality. -/
theorem coeffL1_affine_eq_of_disjoint (F G : ℤ → ℂ) (hF : Summable fun n => ‖F n‖)
    (hG : Summable fun n => ‖G n‖) (hdisj : ∀ n, F n = 0 ∨ G n = 0) (α β : ℂ) :
    coeffL1 (fun n => α * F n + β * G n) = ‖α‖ * coeffL1 F + ‖β‖ * coeffL1 G := by
  have hα : Summable fun n => ‖α‖ * ‖F n‖ := hF.mul_left ‖α‖
  have hβ : Summable fun n => ‖β‖ * ‖G n‖ := hG.mul_left ‖β‖
  have hterm : ∀ n, ‖α * F n + β * G n‖ = ‖α‖ * ‖F n‖ + ‖β‖ * ‖G n‖ := by
    intro n
    rcases hdisj n with h | h
    · simp [h]
    · simp [h]
  calc coeffL1 (fun n => α * F n + β * G n) = ∑' n, ‖α * F n + β * G n‖ := rfl
    _ = ∑' n, (‖α‖ * ‖F n‖ + ‖β‖ * ‖G n‖) := tsum_congr hterm
    _ = (∑' n, ‖α‖ * ‖F n‖) + ∑' n, ‖β‖ * ‖G n‖ := Summable.tsum_add hα hβ
    _ = ‖α‖ * coeffL1 F + ‖β‖ * coeffL1 G := by
          rw [tsum_mul_left, tsum_mul_left]
          rfl

/-- `s` is monotone under pointwise domination of the moduli. -/
theorem coeffL1_le_of_norm_le (F G : ℤ → ℂ) (h : ∀ n, ‖F n‖ ≤ ‖G n‖)
    (hG : Summable fun n => ‖G n‖) : coeffL1 F ≤ coeffL1 G := by
  have hF : Summable fun n => ‖F n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) h hG
  exact hF.tsum_le_tsum h hG

/-- `s` of the zero family vanishes. -/
@[simp]
theorem coeffL1_zero : coeffL1 (fun _ : ℤ => (0 : ℂ)) = 0 := by
  simp [coeffL1]

/-- `s` is nonnegative. -/
theorem coeffL1_nonneg (F : ℤ → ℂ) : 0 ≤ coeffL1 F := tsum_nonneg fun _ => norm_nonneg _

/-- `s` is homogeneous under scalar multiplication. -/
theorem coeffL1_smul (F : ℤ → ℂ) (α : ℂ) :
    coeffL1 (fun n => α * F n) = ‖α‖ * coeffL1 F := by
  rw [coeffL1, coeffL1, ← tsum_mul_left]
  exact tsum_congr fun n => norm_mul _ _

/-- The adjoint family has the same `ℓ¹` weight (reindex `n ↦ -n`). -/
theorem coeffL1_coeffStar (F : ℤ → ℂ) : coeffL1 (coeffStar F) = coeffL1 F := by
  have h : (∑' n : ℤ, ‖coeffStar F n‖) = ∑' n : ℤ, ‖F n‖ := by
    rw [← Equiv.tsum_eq (Equiv.neg ℤ) (fun n : ℤ => ‖F n‖)]
    refine tsum_congr fun n => ?_
    simp [coeffStar]
  rw [coeffL1, coeffL1, h]

/-- The adjoint family is absolutely summable whenever `F` is. -/
theorem summable_norm_coeffStar (F : ℤ → ℂ) (hF : Summable fun n => ‖F n‖) :
    Summable fun n => ‖coeffStar F n‖ := by
  have he : Summable fun n : ℤ => ‖F (-n)‖ := by
    simpa only [Function.comp_def] using hF.comp_injective (i := fun n : ℤ => -n) (by intro a b h; simpa using h)
  refine he.congr fun n => ?_
  simp [coeffStar]

end Qatlib.Papers.CorrWalkSim16.MainResults
