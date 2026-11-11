/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# MacaulayHHL21 — shared source model

Fixed paper: arXiv:2111.00405, *Limitations of the Macaulay matrix approach for
using the HHL algorithm to solve multivariate polynomial systems*.
PDF `prove/assets/2111.00405.pdf`,
plain text `assets/2111.00405.txt`.

This module fixes the notation that the paper uses before its numbered
results: complex vectors indexed by monomials, their ℓ1/ℓ2 norms, the
support size (`ℓ0`), the predicate "0/1 vector", the Hamming weight, the
complex affine hull and the real convex hull of a finite family of vectors,
the notion of a sparse matrix, the Gram matrix, and the truncated-QLS
condition number `κ_b(M)`.  Every definition below is the paper's own
object; no statement of a numbered result is asserted here.

Boundary: the model is finite-dimensional and real/complex only.  It does
not attempt to formalise polynomial ideals or monomial orderings; those
appear only in the claim files, as explicit hypotheses with inline
provenance.  No axioms, no `sorry` in this file.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults

/-! ## Norms, support and 0/1 vectors -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared ℓ2 norm of a complex vector: `‖v‖₂² = ∑ i, ‖v i‖²`. -/
def l2NormSq (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- ℓ2 norm of a complex vector: `‖v‖₂ = √(∑ i, ‖v i‖²)`. -/
def l2Norm (v : ι → ℂ) : ℝ := Real.sqrt (l2NormSq v)

/-- ℓ1 norm of a complex vector: `‖v‖₁ = ∑ i, ‖v i‖`. -/
def l1Norm (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖

/-- Support size (the paper's `‖v‖₀`): the number of nonzero entries. -/
def supportSize (v : ι → ℂ) : ℕ := (univ.filter (fun i => v i ≠ 0)).card

/-- A vector whose entries are all `0` or `1`. -/
def IsZeroOne (v : ι → ℂ) : Prop := ∀ i, v i = 0 ∨ v i = 1

/-- Hamming weight of a 0/1 vector: the number of entries equal to `1`. -/
def hammingWeight (v : ι → ℂ) : ℕ := (univ.filter (fun i => v i = 1)).card

/-- The ℓ2 norm is the square root of the squared ℓ2 norm. -/
theorem l2Norm_def (v : ι → ℂ) : l2Norm v = Real.sqrt (l2NormSq v) := rfl

/-- The squared ℓ2 norm is nonnegative. -/
theorem l2NormSq_nonneg (v : ι → ℂ) : 0 ≤ l2NormSq v := by
  unfold l2NormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The ℓ2 norm is nonnegative. -/
theorem l2Norm_nonneg (v : ι → ℂ) : 0 ≤ l2Norm v := Real.sqrt_nonneg _

/-- The squared ℓ2 norm is the ℓ2 norm squared. -/
theorem l2Norm_sq (v : ι → ℂ) : l2Norm v ^ 2 = l2NormSq v :=
  Real.sq_sqrt (l2NormSq_nonneg v)

/-- For a 0/1 vector, each entry contributes `1` to the squared ℓ2 norm exactly
when it equals `1`. -/
theorem zeroOne_normSq_entry {v : ι → ℂ} (h : IsZeroOne v) (i : ι) :
    ‖v i‖ ^ 2 = if v i = 1 then (1 : ℝ) else 0 := by
  rcases h i with h0 | h1
  · simp [h0]
  · simp [h1]

/-- A complex number that is `0` or `1` vanishes iff it is not `1`. -/
theorem zeroOne_ne_zero_iff {v : ι → ℂ} (h : IsZeroOne v) (i : ι) :
    v i ≠ 0 ↔ v i = 1 := by
  constructor
  · intro hne
    rcases h i with h0 | h1
    · exact absurd h0 hne
    · exact h1
  · intro h1
    rw [h1]
    exact one_ne_zero

/-- For a 0/1 vector the Hamming weight is the support size. -/
theorem hammingWeight_eq_supportSize {v : ι → ℂ} (h : IsZeroOne v) :
    hammingWeight v = supportSize v := by
  unfold hammingWeight supportSize
  congr 1
  refine Finset.filter_congr ?_
  intro i _
  exact (zeroOne_ne_zero_iff h i).symm

/-- The squared ℓ2 norm of a 0/1 vector equals its Hamming weight. -/
theorem zeroOne_l2NormSq_eq_hammingWeight {v : ι → ℂ} (h : IsZeroOne v) :
    l2NormSq v = (hammingWeight v : ℝ) := by
  unfold l2NormSq hammingWeight
  have hstep : ∀ i : ι, ‖v i‖ ^ 2 = if v i = 1 then (1 : ℝ) else 0 :=
    zeroOne_normSq_entry h
  simp only [hstep, Finset.sum_boole]

/-- The ℓ1 norm of a 0/1 vector equals its Hamming weight. -/
theorem zeroOne_l1Norm_eq_hammingWeight {v : ι → ℂ} (h : IsZeroOne v) :
    l1Norm v = (hammingWeight v : ℝ) := by
  unfold l1Norm hammingWeight
  have hstep : ∀ i : ι, ‖v i‖ = if v i = 1 then (1 : ℝ) else 0 := by
    intro i
    rcases h i with h0 | h1
    · simp [h0]
    · simp [h1]
  simp only [hstep, Finset.sum_boole]

/-- The entry sum of a 0/1 vector equals its Hamming weight, as a complex number. -/
theorem zeroOne_sum_eq_hammingWeight {v : ι → ℂ} (h : IsZeroOne v) :
    (∑ i, v i) = (hammingWeight v : ℂ) := by
  unfold hammingWeight
  have hstep : ∀ i : ι, v i = if v i = 1 then (1 : ℂ) else 0 := by
    intro i
    rcases h i with h0 | h1
    · simp [h0]
    · simp [h1]
  calc (∑ i, v i) = ∑ i, (if v i = 1 then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl (fun i _ => hstep i)
    _ = ((univ.filter (fun i => v i = 1)).card : ℂ) :=
        Finset.sum_boole (fun i => v i = 1) univ

/-! ## Affine and convex hulls -/

/-- The complex affine hull `A = {∑ᵢ wᵢ ⃗yᵢ : ∑ᵢ wᵢ = 1}` of a finite family. -/
def affineHull {t : ℕ} (Y : Fin t → ι → ℂ) : Set (ι → ℂ) :=
  {y | ∃ w : Fin t → ℂ, (∑ i, w i) = 1 ∧ y = fun k => ∑ i, w i * Y i k}

/-- The real convex hull `A = {∑ᵢ wᵢ ⃗yᵢ : wᵢ ≥ 0, ∑ᵢ wᵢ = 1}` of a finite family. -/
def convexHull {t : ℕ} (Y : Fin t → ι → ℂ) : Set (ι → ℂ) :=
  {y | ∃ w : Fin t → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
        y = fun k => ∑ i, (w i : ℂ) * Y i k}

/-! ## Truncated QLS condition number -/

/-- The truncated QLS condition number `κ_b(M) = ‖M‖·‖M⁺b‖ / ‖b‖` of the
Macaulay linear system `M y = b` (pages 7 and 10 of the paper).  `mnSq` is
`‖M⁺b‖²`, `matNorm` is `‖M‖` and `bNorm` is `‖b‖`; all are nonnegative reals. -/
def tqlscn (matNorm mnNorm bNorm : ℝ) : ℝ := matNorm * mnNorm / bNorm

/-- Equation (9) of the paper: when `‖M‖ ≥ 1`, `‖b‖ = 1` and `‖M⁺b‖` is the
ℓ2 norm of the minimum-norm solution, the tQLScn dominates that norm. -/
theorem tqlscn_ge_minNormSolution
    {matNorm mnNorm bNorm : ℝ}
    (hM : 1 ≤ matNorm) (hb : bNorm = 1) (hmn : 0 ≤ mnNorm) :
    mnNorm ≤ tqlscn matNorm mnNorm bNorm := by
  unfold tqlscn
  rw [hb, div_one]
  calc mnNorm = 1 * mnNorm := (one_mul _).symm
    _ ≤ matNorm * mnNorm := mul_le_mul_of_nonneg_right hM hmn

end Qatlib.Papers.MacaulayHHL21.MainResults
