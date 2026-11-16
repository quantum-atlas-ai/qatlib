/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGibbs

@[expose] public section


/-! # Frequency damping and the actual complete comparison matrix

The support of each physical factor determines the frequency of every
nonzero Gram entry. This gives an exact entrywise damping identity on the
complete operator space, including repeated transition frequencies. The
generic identity uses column frequency minus row frequency; the TFIM sech
consumer uses evenness to write the opposite convention.

The difference matrix below is the actual `(3/2) H0 - Hg`. Its entry formula,
Gibbs null vector and sector support do not themselves assert positivity.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- A physical first-order factor changes operator frequency by its own
transition frequency. This support statement uses the actual delta formula. -/
theorem fullFactorMatrix_eq_zero_of_frequency_ne (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (a p q : FullCoord D)
    (hne : fullNu lam p - fullNu lam q ≠ fullNu lam a) :
    fullFactorMatrix lam β A a p q = 0 := by
  have hL : (if p.1 = a.1 then (Real.exp (-(β * fullNu lam a) / 4) : ℂ)
      * (if a.2 = q.1 ∧ p.2 = q.2 then 1 else 0) else 0) = 0 := by
    by_cases h₁ : p.1 = a.1
    · by_cases h₂ : a.2 = q.1 ∧ p.2 = q.2
      · exfalso
        apply hne
        simp only [fullNu, h₁, h₂.1, h₂.2]
        ring
      · simp [h₁, h₂]
    · simp [h₁]
  have hR : (if p.2 = a.2 then (Real.exp (β * fullNu lam a / 4) : ℂ)
      * (if p.1 = q.1 ∧ a.1 = q.2 then 1 else 0) else 0) = 0 := by
    by_cases h₁ : p.2 = a.2
    · by_cases h₂ : p.1 = q.1 ∧ a.1 = q.2
      · exfalso
        apply hne
        simp only [fullNu, h₁, h₂.1, h₂.2]
        ring
      · simp [h₁, h₂]
    · simp [h₁]
  simp only [fullFactorMatrix, hL, hR, sub_self, mul_zero]

/-- Full Factor Matrix frequency for the stated finite source data. -/
theorem fullFactorMatrix_frequency (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (a p q : FullCoord D)
    (hne : fullFactorMatrix lam β A a p q ≠ 0) :
    fullNu lam p - fullNu lam q = fullNu lam a := by
  by_contra h
  exact hne (fullFactorMatrix_eq_zero_of_frequency_ne lam β A a p q h)

/-- A nonzero adjoint-product entry has transition-frequency difference
equal to column frequency minus row frequency. -/
theorem fullFactorGram_eq_zero_of_frequency_ne (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (a b p q : FullCoord D)
    (hne : fullNu lam a - fullNu lam b ≠ fullNu lam q - fullNu lam p) :
    ((fullFactorMatrix lam β A a)ᴴ * fullFactorMatrix lam β A b) p q = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  simp only [Matrix.conjTranspose_apply]
  by_cases ha : fullNu lam r - fullNu lam p = fullNu lam a
  · by_cases hb : fullNu lam r - fullNu lam q = fullNu lam b
    · exact False.elim (hne (by linarith))
    · rw [fullFactorMatrix_eq_zero_of_frequency_ne lam β A b r q hb, mul_zero]
  · rw [fullFactorMatrix_eq_zero_of_frequency_ne lam β A a r p ha, star_zero, zero_mul]

/-- Exact damping of every entry of the complete matrix. Neither the
kernel's evenness nor injectivity of the retained Bohr frequencies is needed. -/
theorem fullGramMatrix_kernel_entry (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (p q : FullCoord D) :
    fullGramMatrix lam β kern A p q =
      (kern (fullNu lam q - fullNu lam p) : ℂ)
        * fullGramMatrix lam β (fun _ => 1) A p q := by
  classical
  simp only [fullGramMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    fullWeight, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  let G := ((fullFactorMatrix lam β (A P) a)ᴴ * fullFactorMatrix lam β (A P) b) p q
  have hk : (kern (fullNu lam a - fullNu lam b) : ℂ) * G =
      (kern (fullNu lam q - fullNu lam p) : ℂ) * G := by
    by_cases h : fullNu lam a - fullNu lam b = fullNu lam q - fullNu lam p
    · rw [h]
    · have hz : G = 0 := fullFactorGram_eq_zero_of_frequency_ne lam β (A P) a b p q h
      rw [hz, mul_zero, mul_zero]
  change ((ckgSourceWeight β (fullNu lam a) (fullNu lam b)
      * kern (fullNu lam a - fullNu lam b) / 2 : ℝ) : ℂ) * G = _
  calc
    _ = ((ckgSourceWeight β (fullNu lam a) (fullNu lam b) / 2 : ℝ) : ℂ)
        * ((kern (fullNu lam a - fullNu lam b) : ℂ) * G) := by push_cast; ring
    _ = ((ckgSourceWeight β (fullNu lam a) (fullNu lam b) / 2 : ℝ) : ℂ)
        * ((kern (fullNu lam q - fullNu lam p) : ℂ) * G) := by rw [hk]
    _ = _ := by ring

/-- Linearity of the actual full matrix in its real damping kernel. -/
theorem fullGramMatrix_kernel_linear (lam : Fin D → ℝ) (β c : ℝ)
    (kern₁ kern₂ : ℝ → ℝ) (A : ι → Operator D) :
    fullGramMatrix lam β (fun ω => c * kern₁ ω - kern₂ ω) A =
      (c : ℂ) • fullGramMatrix lam β kern₁ A - fullGramMatrix lam β kern₂ A := by
  ext p q
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fullGramMatrix_kernel_entry lam β (fun ω => c * kern₁ ω - kern₂ ω) A p q,
    fullGramMatrix_kernel_entry lam β kern₁ A p q,
    fullGramMatrix_kernel_entry lam β kern₂ A p q]
  push_cast
  ring


end Qatlib.Concepts.GibbsSource.SourceForms
