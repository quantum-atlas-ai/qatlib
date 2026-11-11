/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Matrix.Mul

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — source model for Theorem 12 (noisy QSP ensemble average)

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27), Appendix B.

This file contains *definitions and proved lemmas only*.  It models the algebraic
heart of the ensemble-average theorem (Eqs. (B1)–(B13)):

* `zRot θ` is the ideal `Z`-rotation `e^{-i θ Z}`;
* `FinDist`-based finite probability laws describe the random phase errors;
* `IsEvenNoise` encodes the paper's hypothesis that each error `e_j` has an
  *even* probability distribution function (an involution that preserves the
  law and negates the variate);
* `matExpect_zRot` proves the per-rotation expectation `E[e^{-i(φ+e)Z}] =
  (E cos e)·e^{-iφ Z}` (Eqs. (B7)–(B11));
* `matExpect_prod_indep` lifts this to the whole QSP phase product under
  independent errors (`E[∏ M_j] = ∏ E[M_j]`, Eq. (B12)).

Matrix products are *ordered* (matrix multiplication is not commutative), so the
paper's `∏_j M_j` is realised by `matProd`, a noncommutative analogue of
`Finset.prod`, rather than by `Finset.prod` (which needs a `CommMonoid`).

No statement here is weakened; these are the exact algebraic steps the paper
uses, realised on a finite sample space (the paper's "even pdf" is modelled by a
measure-preserving sign-reversing involution, which is the finite analogue of an
even distribution).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The Pauli `Z` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The ideal `Z`-rotation `e^{-i θ Z} = diag(e^{-iθ}, e^{iθ})` (arXiv:2601.20073v1
Eq. (B1), the `e^{-i φ_j Z}` gate of the QSP circuit). -/
noncomputable def zRot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun i : Fin 2 =>
    if i = 0 then Complex.exp (-(θ : ℂ) * Complex.I) else Complex.exp ((θ : ℂ) * Complex.I))

/-- The `(0,0)` entry of `zRot θ`. -/
theorem zRot_00 (θ : ℝ) : zRot θ 0 0 = Complex.exp (-(θ : ℂ) * Complex.I) := by
  simp [zRot, Matrix.diagonal]

/-- The `(1,1)` entry of `zRot θ`. -/
theorem zRot_11 (θ : ℝ) : zRot θ 1 1 = Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [zRot, Matrix.diagonal]

/-- The `(0,1)` entry of `zRot θ` vanishes. -/
theorem zRot_01 (θ : ℝ) : zRot θ 0 1 = 0 := by
  simp [zRot, Matrix.diagonal]

/-- The `(1,0)` entry of `zRot θ` vanishes. -/
theorem zRot_10 (θ : ℝ) : zRot θ 1 0 = 0 := by
  simp [zRot, Matrix.diagonal]

/-- The complex expectation of a complex-valued statistic under a finite law. -/
noncomputable def cexpect (μ : FinDist Ω) (f : Ω → ℂ) : ℂ := ∑ ω, (μ.prob ω : ℂ) * f ω

/-- Entrywise matrix expectation of a random matrix over a finite sample space. -/
noncomputable def matExpect {m n : Type*} (μ : FinDist Ω) (M : Ω → Matrix m n ℂ) :
    Matrix m n ℂ :=
  fun i j => cexpect μ (fun ω => M ω i j)

/-! ### Basic algebra of `zRot` -/

/-- `e^{-i(φ+e)Z} = e^{-iφ Z} · e^{-ie Z}` (diagonal rotation composition). -/
theorem zRot_add (φ e : ℝ) : zRot (φ + e) = zRot φ * zRot e := by
  rw [zRot, zRot, zRot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.diagonal]
  · rw [← Complex.exp_add]; congr 1; ring
  · rw [← Complex.exp_add]; congr 1; ring

/-- The explicit exponential form `e^{-i x Z}_{00}`. -/
theorem exp_neg_I_eq (x : ℝ) :
    Complex.exp (-(x : ℂ) * Complex.I)
      = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  have hx : -(x : ℂ) * Complex.I = ((-x : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_neg]
  rw [hx, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- The explicit exponential form `e^{+i x Z}_{11}`. -/
theorem exp_pos_I_eq (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I)
      = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-! ### Linearity of `cexpect` -/

/-- The expectation of the zero function vanishes. -/
theorem cexpect_zero (μ : FinDist Ω) : cexpect μ (fun _ => 0) = 0 := by
  simp [cexpect]

/-- Expectation is additive: `E[f + g] = E[f] + E[g]`. -/
theorem cexpect_add (μ : FinDist Ω) (f g : Ω → ℂ) :
    cexpect μ (fun ω => f ω + g ω) = cexpect μ f + cexpect μ g := by
  simp only [cexpect, mul_add, Finset.sum_add_distrib]

/-- Expectation is subtractive: `E[f − g] = E[f] − E[g]`. -/
theorem cexpect_sub (μ : FinDist Ω) (f g : Ω → ℂ) :
    cexpect μ (fun ω => f ω - g ω) = cexpect μ f - cexpect μ g := by
  simp only [cexpect, mul_sub, Finset.sum_sub_distrib]

/-- Constants factor out of the expectation: `E[a·f] = a·E[f]`. -/
theorem cexpect_const_mul (μ : FinDist Ω) (a : ℂ) (f : Ω → ℂ) :
    cexpect μ (fun ω => a * f ω) = a * cexpect μ f := by
  simp only [cexpect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- A matrix-constant on the right pulls out of the matrix expectation. -/
theorem matExpect_mul_const {u v w : Type*} [Fintype u] [Fintype v] [Fintype w]
    (μ : FinDist Ω) (M : Ω → Matrix u v ℂ) (R : Matrix v w ℂ) :
    matExpect μ (fun ω => M ω * R) = matExpect μ M * R := by
  ext i k
  simp only [matExpect, Matrix.mul_apply, cexpect, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-! ### Even laws and the vanishing sine expectation -/

/-- A finite noise variable with an *even* probability distribution function:
there is a law-preserving involution of the sample space that negates the
variate (arXiv:2601.20073v1 §B.1, the hypothesis on `e_j` before Eq. (B1)). -/
def IsEvenNoise (μ : FinDist Ω) (e : Ω → ℝ) : Prop :=
  ∃ σ : Equiv.Perm Ω, (∀ ω, μ.prob (σ ω) = μ.prob ω) ∧ (∀ ω, e (σ ω) = - e ω)

/-- Under an even law the mean of `sin e` vanishes (Eq. (B10) of
arXiv:2601.20073v1: "`E f(e_j) = 0` for any odd function `f`"). -/
theorem even_expect_sin_zero {μ : FinDist Ω} {e : Ω → ℝ} (h : IsEvenNoise μ e) :
    μ.expect (fun ω => Real.sin (e ω)) = 0 := by
  unfold FinDist.expect
  obtain ⟨σ, hprob, hneg⟩ := h
  have hS : (∑ ω, μ.prob ω * Real.sin (e ω))
      = ∑ ω, μ.prob (σ ω) * Real.sin (e (σ ω)) :=
    (Equiv.sum_comp σ (fun ω => μ.prob ω * Real.sin (e ω))).symm
  have h2 : ∀ ω, μ.prob (σ ω) * Real.sin (e (σ ω)) =
      -(μ.prob ω * Real.sin (e ω)) := by
    intro ω
    rw [hprob ω, hneg ω, Real.sin_neg]
    ring
  have key : (∑ ω, μ.prob ω * Real.sin (e ω))
      = -(∑ ω, μ.prob ω * Real.sin (e ω)) := by
    calc ∑ ω, μ.prob ω * Real.sin (e ω)
        = ∑ ω, μ.prob (σ ω) * Real.sin (e (σ ω)) := hS
      _ = ∑ ω, -(μ.prob ω * Real.sin (e ω)) :=
            Finset.sum_congr rfl (fun ω _ => h2 ω)
      _ = -(∑ ω, μ.prob ω * Real.sin (e ω)) := by
            rw [Finset.sum_neg_distrib]
  linarith [key]

/-- `cexpect` of a real statistic coerced to `ℂ` equals the real expectation. -/
theorem cexpect_ofReal (μ : FinDist Ω) (g : Ω → ℝ) :
    cexpect μ (fun ω => (g ω : ℂ)) = (μ.expect g : ℂ) := by
  simp only [cexpect, FinDist.expect, Complex.ofReal_sum, Complex.ofReal_mul]

/-- `cexpect` of `g·i` factors the imaginary unit. -/
theorem cexpect_ofReal_mul_I (μ : FinDist Ω) (g : Ω → ℝ) :
    cexpect μ (fun ω => (g ω : ℂ) * Complex.I) = (μ.expect g : ℂ) * Complex.I := by
  unfold cexpect FinDist.expect
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Expectation of `e^{-ie Z}` for an even noise law equals `E cos e` (the scalar
content of Eqs. (B7)–(B11), applied to the `(0,0)` entry). -/
theorem cexpect_exp_neg {μ : FinDist Ω} {e : Ω → ℝ} (h : IsEvenNoise μ e) :
    cexpect μ (fun ω => Complex.exp (-(e ω : ℂ) * Complex.I))
      = (μ.expect (fun ω => Real.cos (e ω)) : ℂ) := by
  have hpt : ∀ ω, Complex.exp (-(e ω : ℂ) * Complex.I)
      = (Real.cos (e ω) : ℂ) - (Real.sin (e ω) : ℂ) * Complex.I :=
    fun ω => exp_neg_I_eq (e ω)
  simp only [hpt, cexpect_sub, cexpect_ofReal, cexpect_ofReal_mul_I,
    even_expect_sin_zero h, Complex.ofReal_zero, zero_mul, sub_zero]

/-- Expectation of `e^{+ie Z}` for an even noise law equals `E cos e`. -/
theorem cexpect_exp_pos {μ : FinDist Ω} {e : Ω → ℝ} (h : IsEvenNoise μ e) :
    cexpect μ (fun ω => Complex.exp ((e ω : ℂ) * Complex.I))
      = (μ.expect (fun ω => Real.cos (e ω)) : ℂ) := by
  have hpt : ∀ ω, Complex.exp ((e ω : ℂ) * Complex.I)
      = (Real.cos (e ω) : ℂ) + (Real.sin (e ω) : ℂ) * Complex.I :=
    fun ω => exp_pos_I_eq (e ω)
  simp only [hpt, cexpect_add, cexpect_ofReal, cexpect_ofReal_mul_I,
    even_expect_sin_zero h, Complex.ofReal_zero, zero_mul, add_zero]

/-! ### Per-rotation expectation (Eqs. (B7)–(B11)) -/

/-- For a single noisy `Z`-rotation with an even error law,
`E[e^{-i(φ+e)Z}] = (E cos e) • e^{-iφZ}` (arXiv:2601.20073v1 Eq. (B11)). -/
theorem matExpect_zRot {μ : FinDist Ω} {e : Ω → ℝ} (h : IsEvenNoise μ e) (φ : ℝ) :
    matExpect μ (fun ω => zRot (φ + e ω))
      = (μ.expect (fun ω => Real.cos (e ω))) • zRot φ := by
  ext i j
  fin_cases i <;> fin_cases j
  · -- (0,0): exp(-(φ+e) i) = exp(-φ i) * E[exp(-e i)]
    simp only [matExpect]
    simp [zRot, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul, cexpect_zero]
    have hp : ∀ ω, Complex.exp ((-↑(e ω) + -↑φ) * Complex.I)
        = Complex.exp (-(↑φ * Complex.I)) * Complex.exp (-((e ω : ℝ) : ℂ) * Complex.I) := by
      intro ω
      rw [show (-↑(e ω) + -↑φ : ℂ) * Complex.I
          = -(↑φ * Complex.I) + -((e ω : ℝ) : ℂ) * Complex.I by ring]
      rw [Complex.exp_add]
    simp only [hp, cexpect_const_mul, cexpect_exp_neg h]
    ring
  · -- (0,1): both sides zero
    simp only [matExpect]
    simp [zRot, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul, cexpect_zero]
  · -- (1,0): both sides zero
    simp only [matExpect]
    simp [zRot, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul, cexpect_zero]
  · -- (1,1): exp((φ+e) i) = exp(φ i) * E[exp(e i)]
    simp only [matExpect]
    simp [zRot, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul, cexpect_zero]
    have hp : ∀ ω, Complex.exp ((↑φ + ↑(e ω)) * Complex.I)
        = Complex.exp (↑φ * Complex.I) * Complex.exp (((e ω : ℝ) : ℂ) * Complex.I) := by
      intro ω
      rw [show (↑φ + ↑(e ω) : ℂ) * Complex.I
          = (↑φ * Complex.I) + ((e ω : ℝ) : ℂ) * Complex.I by ring]
      rw [Complex.exp_add]
    simp only [hp, cexpect_const_mul, cexpect_exp_pos h]
    ring

/-! ### Independent product law over the phase factors -/

/-- Expectation of a constant complex statistic. -/
theorem cexpect_const (μ : FinDist Ω) (c : ℂ) : cexpect μ (fun _ => c) = c := by
  simp only [cexpect, ← Finset.sum_mul]
  have h : (∑ i, (μ.prob i : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, FinDist.sum_one, Complex.ofReal_one]
  rw [h, one_mul]

/-- Entrywise matrix expectation of the constant identity matrix. -/
theorem matExpect_one (μ : FinDist Ω) :
    matExpect μ (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext i j
  simp only [matExpect, cexpect_const]

/-- The product law on `Fin d → Ω` for coordinatewise independent errors. -/
noncomputable def prodLaw {d : ℕ} (μs : Fin d → FinDist Ω) : FinDist (Fin d → Ω) where
  prob ω := ∏ j, (μs j).prob (ω j)
  nonneg ω := Finset.prod_nonneg fun j _ => (μs j).nonneg (ω j)
  sum_one := by
    rw [show (∑ x : Fin d → Ω, ∏ j, (μs j).prob (x j))
        = ∑ x ∈ Fintype.piFinset (fun _ : Fin d => (Finset.univ : Finset Ω)),
            ∏ j, (μs j).prob (x j) from by simp]
    rw [← Finset.prod_univ_sum]
    simp [FinDist.sum_one]

/-- The ordered product of a finite family in a monoid.  Matrix multiplication
is not commutative, so the paper's `∏_j M_j` is captured by this recursion
(in the paper's index order) rather than by `Finset.prod`. -/
def matProd {M : Type*} [One M] [Mul M] : (n : ℕ) → (Fin n → M) → M
  | 0, _ => 1
  | n + 1, f => f 0 * matProd n (fun i => f i.succ)

/-- Unfolding `matProd` at zero. -/
theorem matProd_zero {M : Type*} [One M] [Mul M] (f : Fin 0 → M) : matProd 0 f = 1 := rfl

/-- Unfolding `matProd` at a successor index. -/
theorem matProd_succ {M : Type*} [One M] [Mul M] {n : ℕ} (f : Fin (n + 1) → M) :
    matProd (n + 1) f = f 0 * matProd n (fun i => f i.succ) := rfl

/-- Scalar multiples pass through an ordered matrix product. -/
theorem matProd_smul : ∀ (d : ℕ) (c : Fin d → ℝ) (M : Fin d → Matrix (Fin 2) (Fin 2) ℂ),
    matProd d (fun j => c j • M j) = (∏ j, c j) • matProd d M := by
  intro d
  induction d with
  | zero =>
    intro c M
    simp [matProd_zero]
  | succ d ih =>
    intro c M
    rw [matProd_succ (f := fun j => c j • M j), matProd_succ (f := M),
      Fin.prod_univ_succ]
    rw [ih (fun j : Fin d => c j.succ) (fun j : Fin d => M j.succ)]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    rw [smul_smul]

/-- Fubini step: the expectation of `A(ω 0) * B(tail ω)` over the product law is
`E[A] * E[B]` when the two factors depend on disjoint coordinates
(arXiv:2601.20073v1 Eq. (B12), split off the first coordinate). -/
theorem matExpect_prod_split {d : ℕ} (μs : Fin (d + 1) → FinDist Ω)
    (A : Ω → Matrix (Fin 2) (Fin 2) ℂ)
    (B : (Fin d → Ω) → Matrix (Fin 2) (Fin 2) ℂ) :
    matExpect (prodLaw μs) (fun ω => A (ω 0) * B (fun j => ω j.succ))
      = matExpect (μs 0) A * matExpect (prodLaw (fun j => μs j.succ)) B := by
  ext i k
  simp only [matExpect, cexpect, prodLaw, Matrix.mul_apply]
  conv_lhs => rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => Ω)).sum_comp
    (fun ω => (∏ j, (μs j).prob (ω j)) * (∑ l, A (ω 0) i l * B (fun j => ω j.succ) l k))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
  calc
    ∑ x, ∑ rest, (↑((μs 0).prob x * ∏ j : Fin d, (μs j.succ).prob (rest j)) : ℂ) *
        (∑ l, A x i l * B rest l k)
      = ∑ x, ∑ rest, ∑ l, ((μs 0).prob x : ℂ) * A x i l *
          ((↑(∏ j : Fin d, (μs j.succ).prob (rest j)) : ℂ) * B rest l k) := by
          apply Finset.sum_congr rfl; intro x _
          apply Finset.sum_congr rfl; intro rest _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro l _
          rw [Complex.ofReal_mul]
          ring
    _ = ∑ x, ∑ l, ∑ rest, ((μs 0).prob x : ℂ) * A x i l *
          ((↑(∏ j : Fin d, (μs j.succ).prob (rest j)) : ℂ) * B rest l k) := by
          apply Finset.sum_congr rfl; intro x _
          exact Finset.sum_comm
    _ = ∑ l, ∑ x, ∑ rest, ((μs 0).prob x : ℂ) * A x i l *
          ((↑(∏ j : Fin d, (μs j.succ).prob (rest j)) : ℂ) * B rest l k) :=
          Finset.sum_comm
    _ = (matExpect (μs 0) A * matExpect (prodLaw (fun j => μs j.succ)) B) i k := by
          simp only [matExpect, cexpect, prodLaw, Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro l _
          rw [← Finset.sum_mul_sum]

/-- The matrix expectation of a product of coordinatewise independent random
matrices factors into the product of the individual expectations
(arXiv:2601.20073v1 Eq. (B12), independence across `j`). -/
theorem matExpect_prod_indep : ∀ (d : ℕ) (μs : Fin d → FinDist Ω)
    (M : (j : Fin d) → Ω → Matrix (Fin 2) (Fin 2) ℂ),
    matExpect (prodLaw μs) (fun ω => matProd d (fun j => M j (ω j)))
      = matProd d (fun j => matExpect (μs j) (M j)) := by
  intro d
  induction d with
  | zero =>
    intro μs M
    simp only [matProd_zero]
    exact matExpect_one (prodLaw μs)
  | succ d ih =>
    intro μs M
    have hsplit : ∀ ω : Fin (d + 1) → Ω,
        matProd (d + 1) (fun j => M j (ω j))
          = M 0 (ω 0) * matProd d (fun j : Fin d => M j.succ (ω j.succ)) :=
      fun ω => matProd_succ (f := fun j => M j (ω j))
    simp only [hsplit]
    rw [matExpect_prod_split (A := fun x => M 0 x)
      (B := fun rest => matProd d (fun j : Fin d => M j.succ (rest j)))]
    rw [matProd_succ (f := fun j => matExpect (μs j) (M j))]
    rw [ih (fun j : Fin d => μs j.succ) (fun j : Fin d => M j.succ)]

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
