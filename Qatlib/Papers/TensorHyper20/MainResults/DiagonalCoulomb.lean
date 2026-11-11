/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-!
# Expansion of the diagonal Coulomb expression

Proves finite-sum and scalar-multiplication identities for expanding the diagonal Coulomb
expression in the tensor hypercontraction formulation of [LeeEtAl2021]. The algebraic setting
permits noncommuting operator factors, and every expansion preserves their order.

The theorem `eq12_diagonal_coulomb` expands the spin and auxiliary-index sum into the
corresponding four-orbital-index expression with coefficients built from `χ` and `ζ`.

## Main statements

* `nOp_expand`: expands a product of two weighted creation-annihilation expressions.
* `eq12_diagonal_coulomb`: establishes the complete finite-sum expansion.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.DiagonalCoulomb

open scoped BigOperators

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Multiplication of two real scalar multiples equals the product of their scalars acting on
the ordered product. -/
theorem smul_mul_smul (x y : ℝ) (a b : A) :
    (x • a) * (y • b) = (x * y) • (a * b) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- Extracts the four real scalar factors from a product of four scalar-multiplied algebra
elements. -/
theorem smul_mul_smul_four (x y z w : ℝ) (a b c d : A) :
    (x • a) * (y • b) * (z • c) * (w • d) = (x * y * z * w) • (a * b * c * d) := by
  rw [smul_mul_smul, smul_mul_smul, smul_mul_smul]

omit [Algebra ℝ A] in

/-- Expands the product of four finite sums into an iterated sum of ordered products. -/
theorem sum_prod_expand {ι κ ρ μ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] [Fintype μ]
    (f : ι → A) (g : κ → A) (h : ρ → A) (l : μ → A) :
    ((∑ i, f i) * (∑ j, g j)) * ((∑ k, h k) * (∑ m, l m)) =
      ∑ i, ∑ j, ∑ k, ∑ m, f i * g j * h k * l m := by
  rw [show (∑ i, f i) * (∑ j, g j) = ∑ i, ∑ j, f i * g j from
      Fintype.sum_mul_sum (f := f) (g := g)]
  rw [show (∑ k, h k) * (∑ m, l m) = ∑ k, ∑ m, h k * l m from
      Fintype.sum_mul_sum (f := h) (g := l)]
  rw [show (∑ i, ∑ j, f i * g j) * (∑ k, ∑ m, h k * l m)
        = ∑ i, ∑ k, (∑ j, f i * g j) * (∑ m, h k * l m) from
      Fintype.sum_mul_sum (f := fun i => ∑ j, f i * g j)
        (g := fun k => ∑ m, h k * l m)]
  refine Finset.sum_congr rfl ?_
  intro i _
  trans ∑ k, ∑ j, ∑ m, (f i * g j) * (h k * l m)
  · refine Finset.sum_congr rfl ?_
    intro k _
    exact Fintype.sum_mul_sum (f := fun j => f i * g j) (g := fun m => h k * l m)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro m _
    noncomm_ring

/-- Expands the product of two weighted creation-annihilation pairs into a fourfold sum with
coefficient `χ μ p * χ μ q * χ ν r * χ ν s`. -/
theorem nOp_expand {N2 M : ℕ} (χ : Fin M → Fin N2 → ℝ)
    (aCre aAnn : Fin N2 → Fin 2 → A) (μ ν : Fin M) (σ τ : Fin 2) :
    ((∑ p, χ μ p • aCre p σ) * (∑ q, χ μ q • aAnn q σ)) *
        ((∑ r, χ ν r • aCre r τ) * (∑ s, χ ν s • aAnn s τ)) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (χ μ p * χ μ q * χ ν r * χ ν s) •
          (aCre p σ * aAnn q σ * aCre r τ * aAnn s τ) := by
  rw [sum_prod_expand]
  refine Finset.sum_congr rfl ?_
  intro p _
  refine Finset.sum_congr rfl ?_
  intro q _
  refine Finset.sum_congr rfl ?_
  intro r _
  refine Finset.sum_congr rfl ?_
  intro s _
  exact smul_mul_smul_four (χ μ p) (χ μ q) (χ ν r) (χ ν s)
    (aCre p σ) (aAnn q σ) (aCre r τ) (aAnn s τ)

/-- Expands a single `ζ`-weighted product of two weighted creation-annihilation pairs,
incorporating `ζ μ ν` into each scalar coefficient. -/
theorem eq12_term {N2 M : ℕ} (χ : Fin M → Fin N2 → ℝ) (ζ : Fin M → Fin M → ℝ)
    (aCre aAnn : Fin N2 → Fin 2 → A) (μ ν : Fin M) (σ τ : Fin 2) :
    ζ μ ν • (((∑ p, χ μ p • aCre p σ) * (∑ q, χ μ q • aAnn q σ)) *
        ((∑ r, χ ν r • aCre r τ) * (∑ s, χ ν s • aAnn s τ))) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (χ μ p * χ μ q * χ ν r * χ ν s * ζ μ ν) •
          (aCre p σ * aAnn q σ * aCre r τ * aAnn s τ) := by
  rw [nOp_expand]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl ?_
  intro p _
  refine Finset.sum_congr rfl ?_
  intro q _
  refine Finset.sum_congr rfl ?_
  intro r _
  refine Finset.sum_congr rfl ?_
  intro s _
  congr 1
  ring

/-- The half-weighted spin and auxiliary-index sum of diagonal Coulomb terms equals its
four-orbital-index expansion, with operator order preserved. -/
theorem eq12_diagonal_coulomb (N2 M : ℕ) (χ : Fin M → Fin N2 → ℝ)
    (ζ : Fin M → Fin M → ℝ) (aCre aAnn : Fin N2 → Fin 2 → A) :
    (1 / 2 : ℝ) • (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin M, ∑ ν : Fin M,
        ζ μ ν • (((∑ p, χ μ p • aCre p σ) * (∑ q, χ μ q • aAnn q σ)) *
          ((∑ r, χ ν r • aCre r τ) * (∑ s, χ ν s • aAnn s τ)))) =
      (1 / 2 : ℝ) • (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin M, ∑ ν : Fin M,
        ∑ p : Fin N2, ∑ q : Fin N2, ∑ r : Fin N2, ∑ s : Fin N2,
          (χ μ p * χ μ q * χ ν r * χ ν s * ζ μ ν) •
            (aCre p σ * aAnn q σ * aCre r τ * aAnn s τ)) := by
  congr 1
  simp only [eq12_term]

end Qatlib.Papers.TensorHyper20.MainResults.DiagonalCoulomb
