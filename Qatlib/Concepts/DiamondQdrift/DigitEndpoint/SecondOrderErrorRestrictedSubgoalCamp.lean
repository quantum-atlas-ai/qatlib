/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.DigitEndpoint.SecondOrderErrorRestrictedSubgoalStat
import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixture

/-!
# Entrywise second order qDRIFT error

This module proves `SecondOrderErrorRestrictedSubgoal` for quadratic branch and target
expansions. Matrix entry estimates and weighted sum identities give an explicit error polynomial
after the first order terms cancel, in the qDRIFT analysis setting of [Campbell2019].

## Main statements

* `conj_expand_mul`: the quadratic conjugation expansion.
* `secondOrderErrorRestrictedSubgoal`: the restricted entrywise second order error estimate.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false
open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint

open Qatlib
open Matrix

/-- The norm of a matrix product entry is bounded by the sum of products of the corresponding
entry norms. -/
private theorem norm_entry_mul_le {I : Type} [Fintype I] (X Y : Matrix I I ℂ) (a b : I) :
    ‖(X * Y) a b‖ ≤ ∑ k, ‖X a k‖ * ‖Y k b‖ := by
  rw [Matrix.mul_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le ..)

/-- Uniform entry bounds `x` and `y` give a product entry bound of the index cardinality times
`x * y`. -/
private theorem norm_entry_mul_le_of {I : Type} [Fintype I] (X Y : Matrix I I ℂ)
    {x y : ℝ} (hx : ∀ a b, ‖X a b‖ ≤ x) (hy : ∀ a b, ‖Y a b‖ ≤ y) (a b : I) :
    ‖(X * Y) a b‖ ≤ (Fintype.card I : ℝ) * (x * y) := by
  have hx0 : 0 ≤ x := (norm_nonneg _).trans (hx a b)
  calc ‖(X * Y) a b‖ ≤ ∑ k, ‖X a k‖ * ‖Y k b‖ := norm_entry_mul_le X Y a b
    _ ≤ ∑ _k : I, x * y :=
        Finset.sum_le_sum fun k _ => mul_le_mul (hx a k) (hy k b) (norm_nonneg _) hx0
    _ = (Fintype.card I : ℝ) * (x * y) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Uniform bounds on three matrix factors give an entry bound of the squared index cardinality
times `x * (y * z)`. -/
private theorem norm_entry_mul_mul_le_of {I : Type} [Fintype I] (X Y Z : Matrix I I ℂ)
    {x y z : ℝ} (hx : ∀ a b, ‖X a b‖ ≤ x) (hy : ∀ a b, ‖Y a b‖ ≤ y)
    (hz : ∀ a b, ‖Z a b‖ ≤ z) (a b : I) :
    ‖(X * Y * Z) a b‖ ≤ (Fintype.card I : ℝ) ^ 2 * (x * (y * z)) := by
  calc ‖(X * Y * Z) a b‖
      ≤ (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) * (x * y) * z) :=
        norm_entry_mul_le_of (X * Y) Z (norm_entry_mul_le_of X Y hx hy) hz a b
    _ = (Fintype.card I : ℝ) ^ 2 * (x * (y * z)) := by ring

/-- A uniform entry norm bound is preserved by conjugate transpose. -/
private theorem norm_entry_conjTranspose_le {I : Type} [Fintype I] (X : Matrix I I ℂ)
    {x : ℝ} (hx : ∀ a b, ‖X a b‖ ≤ x) (a b : I) : ‖Xᴴ a b‖ ≤ x := by
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.norm_conj]
  exact hx b a

/-- Entry bounds on two matrices add to bound the corresponding entry of their sum. -/
private theorem norm_entry_add_le {I : Type} [Fintype I] {X Y : Matrix I I ℂ} {x y : ℝ}
    (a b : I) (hx : ‖X a b‖ ≤ x) (hy : ‖Y a b‖ ≤ y) : ‖(X + Y) a b‖ ≤ x + y :=
  (norm_add_le _ _).trans (add_le_add hx hy)

/-- Entry bounds on two matrices add to bound the corresponding entry of their difference. -/
private theorem norm_entry_sub_le {I : Type} [Fintype I] {X Y : Matrix I I ℂ} {x y : ℝ}
    (a b : I) (hx : ‖X a b‖ ≤ x) (hy : ‖Y a b‖ ≤ y) : ‖(X - Y) a b‖ ≤ x + y :=
  (norm_sub_le _ _).trans (add_le_add hx hy)

/-- A probability weighted sum preserves a common uniform matrix entry norm bound. -/
private theorem norm_entry_weighted_sum_le {J I : Type} [Fintype J] [Fintype I]
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (X : J → Matrix I I ℂ) {m : ℝ} (hX : ∀ j a b, ‖(X j) a b‖ ≤ m) (a b : I) :
    ‖(∑ j, (p j : ℂ) • X j) a b‖ ≤ m := by
  calc ‖(∑ j, (p j : ℂ) • X j) a b‖
      = ‖∑ j, (p j : ℂ) * (X j) a b‖ := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ ≤ ∑ j, ‖(p j : ℂ) * (X j) a b‖ := norm_sum_le _ _
    _ = ∑ j, p j * ‖(X j) a b‖ := Finset.sum_congr rfl fun j _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
    _ ≤ ∑ j, p j * m := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hX j a b) (hp j)
    _ = m := by rw [← Finset.sum_mul, hpsum, one_mul]

/-- The entry norm of a sum of three scalar multiples is bounded by the sum of the scalar norms
times the corresponding entry bounds. -/
private theorem norm_entry_smul3_le {I : Type} [Fintype I]
    {u₂ u₃ u₄ : ℂ} {v₂ v₃ v₄ : ℝ} (hu₂ : ‖u₂‖ = v₂) (hu₃ : ‖u₃‖ = v₃) (hu₄ : ‖u₄‖ = v₄)
    (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃) (hv₄ : 0 ≤ v₄)
    (D₂ D₃ D₄ : Matrix I I ℂ) {m₂ m₃ m₄ : ℝ} (a b : I)
    (h₂ : ‖D₂ a b‖ ≤ m₂) (h₃ : ‖D₃ a b‖ ≤ m₃) (h₄ : ‖D₄ a b‖ ≤ m₄) :
    ‖(u₂ • D₂ + u₃ • D₃ + u₄ • D₄) a b‖ ≤ v₂ * m₂ + v₃ * m₃ + v₄ * m₄ := by
  calc ‖(u₂ • D₂ + u₃ • D₃ + u₄ • D₄) a b‖
      ≤ ‖(u₂ • D₂ + u₃ • D₃) a b‖ + ‖(u₄ • D₄) a b‖ := norm_add_le _ _
    _ ≤ (‖(u₂ • D₂) a b‖ + ‖(u₃ • D₃) a b‖) + ‖(u₄ • D₄) a b‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ = (‖u₂‖ * ‖D₂ a b‖ + ‖u₃‖ * ‖D₃ a b‖) + ‖u₄‖ * ‖D₄ a b‖ := by
        simp only [Matrix.smul_apply, smul_eq_mul, norm_mul]
    _ = (v₂ * ‖D₂ a b‖ + v₃ * ‖D₃ a b‖) + v₄ * ‖D₄ a b‖ := by
        rw [hu₂, hu₃, hu₄]
    _ ≤ (v₂ * m₂ + v₃ * m₃) + v₄ * m₄ :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₂ hv₂)
          (mul_le_mul_of_nonneg_left h₃ hv₃)) (mul_le_mul_of_nonneg_left h₄ hv₄)

/-- Conjugate transpose preserves the real time coefficients in the quadratic branch expansion. -/
private theorem qdriftBranchU_conjTranspose {J I : Type} [DecidableEq I] (dt : ℝ)
    (A R : J → Matrix I I ℂ) (j : J) :
    (QdriftBranchU dt A R j)ᴴ
      = 1 + (dt : ℂ) • (A j)ᴴ + ((dt ^ 2 : ℝ) : ℂ) • (R j)ᴴ := by
  simp only [QdriftBranchU, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal]

/-- Conjugate transpose preserves the real time coefficients in the quadratic target expansion. -/
private theorem qdriftTargetV_conjTranspose {I : Type} [DecidableEq I] (dt : ℝ)
    (B S : Matrix I I ℂ) :
    (QdriftTargetV dt B S)ᴴ = 1 + (dt : ℂ) • Bᴴ + ((dt ^ 2 : ℝ) : ℂ) • Sᴴ := by
  simp only [QdriftTargetV, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal]

/-- Expand left and right multiplication by quadratic matrix expressions into constant through
quartic scalar terms. -/
private theorem conj_expand_mul {I : Type} [Fintype I] [DecidableEq I] (u₁ u₂ : ℂ)
    (X₁ X₂ ρ : Matrix I I ℂ) :
    (1 + u₁ • X₁ + u₂ • X₂) * ρ * ((1 : Matrix I I ℂ) + u₁ • X₁ᴴ + u₂ • X₂ᴴ)
      = ρ + u₁ • (X₁ * ρ + ρ * X₁ᴴ)
        + ((u₁ * u₁) • (X₁ * ρ * X₁ᴴ) + u₂ • (X₂ * ρ + ρ * X₂ᴴ))
        + (u₁ * u₂) • (X₁ * ρ * X₂ᴴ + X₂ * ρ * X₁ᴴ)
        + (u₂ * u₂) • (X₂ * ρ * X₂ᴴ) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/-- Distribute a finite scalar weighted sum over a common constant matrix and four scalar matrix
terms. -/
private theorem weighted_sum_expansion {J I : Type} [Fintype J] [Fintype I]
    (p : J → ℂ) (u₁ u₂ u₃ u₄ : ℂ) (X₀ : Matrix I I ℂ) (X₁ X₂ X₃ X₄ : J → Matrix I I ℂ) :
    ∑ j, p j • (X₀ + u₁ • X₁ j + u₂ • X₂ j + u₃ • X₃ j + u₄ • X₄ j)
      = (∑ j, p j) • X₀ + u₁ • (∑ j, p j • X₁ j) + u₂ • (∑ j, p j • X₂ j)
        + u₃ • (∑ j, p j • X₃ j) + u₄ • (∑ j, p j • X₄ j) := by
  have hper : ∀ j : J, p j • (X₀ + u₁ • X₁ j + u₂ • X₂ j + u₃ • X₃ j + u₄ • X₄ j)
      = p j • X₀ + u₁ • (p j • X₁ j) + u₂ • (p j • X₂ j) + u₃ • (p j • X₃ j)
        + u₄ • (p j • X₄ j) := fun j => by module
  rw [Finset.sum_congr rfl fun j _ => hper j, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum,
    ← Finset.smul_sum]

/-- The importance sampled quadratic branch mixture and the quadratic target evolution satisfy
the specified entrywise second order error polynomial under the stated uniform entry bounds
[Campbell2019]. -/
theorem secondOrderErrorRestrictedSubgoal : SecondOrderErrorRestrictedSubgoal := by
  intro J I _ _ _ _ h H Λ hΛ hΛpos dt r hdt _hr cH hcH A hA R S hR hS ρ cρ hcρ a b

  have hΛ0 : Λ ≠ 0 := hΛpos.ne'
  have hpsum : ∑ j, |h j| / Λ = 1 := (qdriftImportanceDist h Λ hΛ hΛpos).sum_one
  have hp0 : ∀ j : J, 0 ≤ |h j| / Λ := (qdriftImportanceDist h Λ hΛ hΛpos).nonneg
  have hpsumC : ∑ j, ((|h j| / Λ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hpsum, Complex.ofReal_one]

  have hu2 : (dt : ℂ) * (dt : ℂ) = ((dt ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, pow_two]
  have hu3 : (dt : ℂ) * ((dt ^ 2 : ℝ) : ℂ) = ((dt ^ 3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    ring
  have hu4 : ((dt ^ 2 : ℝ) : ℂ) * ((dt ^ 2 : ℝ) : ℂ) = ((dt ^ 4 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    ring

  have hcancel : ∑ j, ((|h j| / Λ : ℝ) : ℂ) • A j
      = -(Complex.I) • ∑ j, (h j : ℂ) • H j := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : |h j| / Λ * (Λ * (SignType.sign (h j) : ℝ)) = h j := by
      rw [← mul_assoc, div_mul_cancel₀ _ hΛ0, abs_mul_sign]
    have h2 : ((|h j| / Λ : ℝ) : ℂ) * ((Λ : ℂ) * ((SignType.sign (h j) : ℝ) : ℂ))
        = ((h j : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, h1]
    calc ((|h j| / Λ : ℝ) : ℂ) • A j
        = ((|h j| / Λ : ℝ) : ℂ)
            • ((-(Complex.I) * ((Λ * (SignType.sign (h j) : ℝ)) : ℂ)) • H j) := by
          rw [hA j]
      _ = (((|h j| / Λ : ℝ) : ℂ) * (-(Complex.I) * ((Λ * (SignType.sign (h j) : ℝ)) : ℂ)))
            • H j := smul_smul _ _ _
      _ = (-(Complex.I) * ((h j : ℝ) : ℂ)) • H j := by
          congr 1
          calc ((|h j| / Λ : ℝ) : ℂ)
                * (-(Complex.I) * ((Λ * (SignType.sign (h j) : ℝ)) : ℂ))
              = -(Complex.I) * (((|h j| / Λ : ℝ) : ℂ)
                  * ((Λ : ℂ) * ((SignType.sign (h j) : ℝ) : ℂ))) := by ring
            _ = -(Complex.I) * ((h j : ℝ) : ℂ) := by rw [h2]
      _ = -(Complex.I) • ((h j : ℂ) • H j) := (smul_smul _ _ _).symm
  have hcancel' : ∑ j, ((|h j| / Λ : ℝ) : ℂ) • (A j)ᴴ
      = (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ := by
    have e : ∀ j : J, ((|h j| / Λ : ℝ) : ℂ) • (A j)ᴴ
        = (((|h j| / Λ : ℝ) : ℂ) • A j)ᴴ := fun j => by
      rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal]
    rw [Finset.sum_congr rfl fun j _ => e j, ← Matrix.conjTranspose_sum, hcancel]

  have hF₁ : ∑ j, ((|h j| / Λ : ℝ) : ℂ) • (A j * ρ + ρ * (A j)ᴴ)
      = (-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ
        + ρ * (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ := by
    have e1 : ∑ j, ((|h j| / Λ : ℝ) : ℂ) • (A j * ρ)
        = (∑ j, ((|h j| / Λ : ℝ) : ℂ) • A j) * ρ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => (smul_mul_assoc _ _ _).symm
    have e2 : ∑ j, ((|h j| / Λ : ℝ) : ℂ) • (ρ * (A j)ᴴ)
        = ρ * (∑ j, ((|h j| / Λ : ℝ) : ℂ) • (A j)ᴴ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
    have e0 : ∀ j : J, ((|h j| / Λ : ℝ) : ℂ) • (A j * ρ + ρ * (A j)ᴴ)
        = ((|h j| / Λ : ℝ) : ℂ) • (A j * ρ) + ((|h j| / Λ : ℝ) : ℂ) • (ρ * (A j)ᴴ) :=
      fun j => smul_add _ _ _
    rw [Finset.sum_congr rfl fun j _ => e0 j, Finset.sum_add_distrib, e1, e2,
      hcancel, hcancel']

  have hUexp : ∀ j : J, QdriftBranchU dt A R j * ρ * (QdriftBranchU dt A R j)ᴴ
      = ρ + (dt : ℂ) • (A j * ρ + ρ * (A j)ᴴ)
        + ((dt ^ 2 : ℝ) : ℂ) • (A j * ρ * (A j)ᴴ + (R j * ρ + ρ * (R j)ᴴ))
        + ((dt ^ 3 : ℝ) : ℂ) • (A j * ρ * (R j)ᴴ + R j * ρ * (A j)ᴴ)
        + ((dt ^ 4 : ℝ) : ℂ) • (R j * ρ * (R j)ᴴ) := fun j => by
    rw [qdriftBranchU_conjTranspose dt A R j]
    show (1 + (dt : ℂ) • A j + ((dt ^ 2 : ℝ) : ℂ) • R j) * ρ *
        (1 + (dt : ℂ) • (A j)ᴴ + ((dt ^ 2 : ℝ) : ℂ) • (R j)ᴴ) = _
    rw [conj_expand_mul (dt : ℂ) ((dt ^ 2 : ℝ) : ℂ) (A j) (R j) ρ, hu2, hu3, hu4,
      ← smul_add]
  have hVexp : QdriftTargetV dt (-(Complex.I) • ∑ j, (h j : ℂ) • H j) S * ρ *
        (QdriftTargetV dt (-(Complex.I) • ∑ j, (h j : ℂ) • H j) S)ᴴ
      = ρ + (dt : ℂ) • ((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ
          + ρ * (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ)
        + ((dt ^ 2 : ℝ) : ℂ) • ((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ *
            (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ + (S * ρ + ρ * Sᴴ))
        + ((dt ^ 3 : ℝ) : ℂ) • ((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ * Sᴴ
            + S * ρ * (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ)
        + ((dt ^ 4 : ℝ) : ℂ) • (S * ρ * Sᴴ) := by
    rw [qdriftTargetV_conjTranspose dt (-(Complex.I) • ∑ j, (h j : ℂ) • H j) S]
    show (1 + (dt : ℂ) • (-(Complex.I) • ∑ j, (h j : ℂ) • H j) + ((dt ^ 2 : ℝ) : ℂ) • S)
        * ρ * _ = _
    rw [conj_expand_mul (dt : ℂ) ((dt ^ 2 : ℝ) : ℂ) (-(Complex.I) • ∑ j, (h j : ℂ) • H j)
      S ρ, hu2, hu3, hu4, ← smul_add]

  have hM : ChannelMixture (qdriftImportanceDist h Λ hΛ hΛpos) (QdriftBranchU dt A R) ρ
      = ρ + (dt : ℂ) • ((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ
          + ρ * (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ)
        + ((dt ^ 2 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ)
            • (A j * ρ * (A j)ᴴ + (R j * ρ + ρ * (R j)ᴴ)))
        + ((dt ^ 3 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ)
            • (A j * ρ * (R j)ᴴ + R j * ρ * (A j)ᴴ))
        + ((dt ^ 4 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ) • (R j * ρ * (R j)ᴴ)) := by
    calc ChannelMixture (qdriftImportanceDist h Λ hΛ hΛpos) (QdriftBranchU dt A R) ρ
        = ∑ j, ((|h j| / Λ : ℝ) : ℂ) •
            (QdriftBranchU dt A R j * ρ * (QdriftBranchU dt A R j)ᴴ) := rfl
      _ = ∑ j, ((|h j| / Λ : ℝ) : ℂ) •
            (ρ + (dt : ℂ) • (A j * ρ + ρ * (A j)ᴴ)
              + ((dt ^ 2 : ℝ) : ℂ) • (A j * ρ * (A j)ᴴ + (R j * ρ + ρ * (R j)ᴴ))
              + ((dt ^ 3 : ℝ) : ℂ) • (A j * ρ * (R j)ᴴ + R j * ρ * (A j)ᴴ)
              + ((dt ^ 4 : ℝ) : ℂ) • (R j * ρ * (R j)ᴴ)) :=
          Finset.sum_congr rfl fun j _ => congrArg _ (hUexp j)
      _ = (∑ j, ((|h j| / Λ : ℝ) : ℂ)) • ρ
          + (dt : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ) • (A j * ρ + ρ * (A j)ᴴ))
          + ((dt ^ 2 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ)
              • (A j * ρ * (A j)ᴴ + (R j * ρ + ρ * (R j)ᴴ)))
          + ((dt ^ 3 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ)
              • (A j * ρ * (R j)ᴴ + R j * ρ * (A j)ᴴ))
          + ((dt ^ 4 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ) • (R j * ρ * (R j)ᴴ)) :=
          weighted_sum_expansion _ _ _ _ _ _ _ _ _ _
      _ = ρ + (dt : ℂ) • ((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ
            + ρ * (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ)
          + ((dt ^ 2 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ)
              • (A j * ρ * (A j)ᴴ + (R j * ρ + ρ * (R j)ᴴ)))
          + ((dt ^ 3 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ)
              • (A j * ρ * (R j)ᴴ + R j * ρ * (A j)ᴴ))
          + ((dt ^ 4 : ℝ) : ℂ) • (∑ j, ((|h j| / Λ : ℝ) : ℂ) • (R j * ρ * (R j)ᴴ)) := by
          rw [hpsumC, one_smul, hF₁]

  have hDiff : ChannelMixture (qdriftImportanceDist h Λ hΛ hΛpos) (QdriftBranchU dt A R) ρ
        - QdriftTargetV dt (-(Complex.I) • ∑ j, (h j : ℂ) • H j) S * ρ *
          (QdriftTargetV dt (-(Complex.I) • ∑ j, (h j : ℂ) • H j) S)ᴴ
      = ((dt ^ 2 : ℝ) : ℂ) • ((∑ j, ((|h j| / Λ : ℝ) : ℂ)
            • (A j * ρ * (A j)ᴴ + (R j * ρ + ρ * (R j)ᴴ)))
          - ((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ *
              (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ + (S * ρ + ρ * Sᴴ)))
        + ((dt ^ 3 : ℝ) : ℂ) • ((∑ j, ((|h j| / Λ : ℝ) : ℂ)
            • (A j * ρ * (R j)ᴴ + R j * ρ * (A j)ᴴ))
          - ((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ * Sᴴ
              + S * ρ * (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ))
        + ((dt ^ 4 : ℝ) : ℂ) • ((∑ j, ((|h j| / Λ : ℝ) : ℂ) • (R j * ρ * (R j)ᴴ))
          - S * ρ * Sᴴ) := by
    rw [hM, hVexp]
    module

  have hAb : ∀ (j : J) (a b : I), ‖(A j) a b‖ ≤ Λ * cH := fun j a b => by
    have hsign : |(SignType.sign (h j) : ℝ)| ≤ 1 := by
      rcases SignType.trichotomy (SignType.sign (h j)) with hs | hs | hs <;>
        simp [hs, SignType.coe_neg_one, SignType.coe_zero, SignType.coe_one]
    rw [hA j, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_mul, norm_neg,
      Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛpos.le]
    calc Λ * |(SignType.sign (h j) : ℝ)| * ‖(H j) a b‖
        ≤ Λ * 1 * cH := mul_le_mul (mul_le_mul_of_nonneg_left hsign hΛpos.le)
          (hcH j a b) (norm_nonneg _) (mul_nonneg hΛpos.le zero_le_one)
      _ = Λ * cH := by ring
  have hBb : ∀ (a b : I), ‖(-(Complex.I) • ∑ j, (h j : ℂ) • H j) a b‖ ≤ Λ * cH := by
    intro a b
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
    calc ‖(∑ j, (h j : ℂ) • H j) a b‖
        = ‖∑ j, (h j : ℂ) * (H j) a b‖ := by
          simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      _ ≤ ∑ j, ‖(h j : ℂ) * (H j) a b‖ := norm_sum_le _ _
      _ = ∑ j, |h j| * ‖(H j) a b‖ := Finset.sum_congr rfl fun j _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ j, |h j| * cH := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hcH j a b) (abs_nonneg _)
      _ = Λ * cH := by rw [← Finset.sum_mul, ← hΛ]

  have hW₂ : ∀ (a b : I),
      ‖(∑ j, ((|h j| / Λ : ℝ) : ℂ) • (A j * ρ * (A j)ᴴ + (R j * ρ + ρ * (R j)ᴴ))) a b‖
        ≤ (Fintype.card I : ℝ) ^ 2 * ((Λ * cH) * (cρ * (Λ * cH)))
          + ((Fintype.card I : ℝ) * (r * cρ) + (Fintype.card I : ℝ) * (cρ * r)) := by
    intro a b
    exact norm_entry_weighted_sum_le (fun j => |h j| / Λ) hp0 hpsum _ (fun j a b =>
      norm_entry_add_le a b
        (norm_entry_mul_mul_le_of (A j) ρ (A j)ᴴ (hAb j) hcρ
          (norm_entry_conjTranspose_le (A j) (hAb j)) a b)
        (norm_entry_add_le a b
          (norm_entry_mul_le_of (R j) ρ (hR j) hcρ a b)
          (norm_entry_mul_le_of ρ (R j)ᴴ hcρ
            (norm_entry_conjTranspose_le (R j) (hR j)) a b))) a b
  have hG₂ : ∀ (a b : I),
      ‖((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ *
          (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ + (S * ρ + ρ * Sᴴ)) a b‖
        ≤ (Fintype.card I : ℝ) ^ 2 * ((Λ * cH) * (cρ * (Λ * cH)))
          + ((Fintype.card I : ℝ) * (r * cρ) + (Fintype.card I : ℝ) * (cρ * r)) := by
    intro a b
    exact norm_entry_add_le a b
      (norm_entry_mul_mul_le_of _ ρ _ hBb hcρ
        (norm_entry_conjTranspose_le _ hBb) a b)
      (norm_entry_add_le a b
        (norm_entry_mul_le_of S ρ hS hcρ a b)
        (norm_entry_mul_le_of ρ Sᴴ hcρ (norm_entry_conjTranspose_le S hS) a b))
  have hW₃ : ∀ (a b : I),
      ‖(∑ j, ((|h j| / Λ : ℝ) : ℂ) • (A j * ρ * (R j)ᴴ + R j * ρ * (A j)ᴴ)) a b‖
        ≤ (Fintype.card I : ℝ) ^ 2 * ((Λ * cH) * (cρ * r))
          + (Fintype.card I : ℝ) ^ 2 * (r * (cρ * (Λ * cH))) := by
    intro a b
    exact norm_entry_weighted_sum_le (fun j => |h j| / Λ) hp0 hpsum _ (fun j a b =>
      norm_entry_add_le a b
        (norm_entry_mul_mul_le_of (A j) ρ (R j)ᴴ (hAb j) hcρ
          (norm_entry_conjTranspose_le (R j) (hR j)) a b)
        (norm_entry_mul_mul_le_of (R j) ρ (A j)ᴴ (hR j) hcρ
          (norm_entry_conjTranspose_le (A j) (hAb j)) a b)) a b
  have hG₃ : ∀ (a b : I),
      ‖((-(Complex.I) • ∑ j, (h j : ℂ) • H j) * ρ * Sᴴ
          + S * ρ * (-(Complex.I) • ∑ j, (h j : ℂ) • H j)ᴴ) a b‖
        ≤ (Fintype.card I : ℝ) ^ 2 * ((Λ * cH) * (cρ * r))
          + (Fintype.card I : ℝ) ^ 2 * (r * (cρ * (Λ * cH))) := by
    intro a b
    exact norm_entry_add_le a b
      (norm_entry_mul_mul_le_of _ ρ Sᴴ hBb hcρ
        (norm_entry_conjTranspose_le S hS) a b)
      (norm_entry_mul_mul_le_of S ρ _ hS hcρ
        (norm_entry_conjTranspose_le _ hBb) a b)
  have hW₄ : ∀ (a b : I),
      ‖(∑ j, ((|h j| / Λ : ℝ) : ℂ) • (R j * ρ * (R j)ᴴ)) a b‖
        ≤ (Fintype.card I : ℝ) ^ 2 * (r * (cρ * r)) := by
    intro a b
    exact norm_entry_weighted_sum_le (fun j => |h j| / Λ) hp0 hpsum _ (fun j a b =>
      norm_entry_mul_mul_le_of (R j) ρ (R j)ᴴ (hR j) hcρ
        (norm_entry_conjTranspose_le (R j) (hR j)) a b) a b
  have hG₄ : ∀ (a b : I), ‖(S * ρ * Sᴴ) a b‖
      ≤ (Fintype.card I : ℝ) ^ 2 * (r * (cρ * r)) := fun a b =>
    norm_entry_mul_mul_le_of S ρ Sᴴ hS hcρ (norm_entry_conjTranspose_le S hS) a b

  have hnorm_pow : ∀ k : ℕ, ‖(((dt ^ k : ℝ) : ℂ))‖ = dt ^ k := fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hdt k)]

  rw [hDiff]
  refine (norm_entry_smul3_le (hnorm_pow 2) (hnorm_pow 3) (hnorm_pow 4)
    (pow_nonneg hdt 2) (pow_nonneg hdt 3) (pow_nonneg hdt 4) _ _ _ a b
    (norm_entry_sub_le a b (hW₂ a b) (hG₂ a b))
    (norm_entry_sub_le a b (hW₃ a b) (hG₃ a b))
    (norm_entry_sub_le a b (hW₄ a b) (hG₄ a b))).trans ?_
  exact le_of_eq (by ring)

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
