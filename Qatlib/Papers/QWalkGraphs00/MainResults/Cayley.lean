/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkGraphs00.MainResults.Core
import Qatlib.Papers.QWalkGraphs00.MainResults.Distribution
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Star.BigOperators

/-!
# Character decomposition of Cayley walks

The coined step `cayleyStep` on a finite abelian group reduces on character-product vectors to
the smaller matrix `twistedCoin`. These identities support the uniform limiting-distribution
criterion for Cayley walks in [AharonovEtAl2001Walks], under explicit assumptions on the
eigenvalues, coefficients, and vertex weights.

## Main statements

* `cayleyStep_eigenvector`: lifts a twisted-coin eigenvector to the full walk.
* `uniform_limit_of_uniform_eigenvectors`: gives a uniform limit from uniform vertex weights and
  distinct eigenvalues.
* `cayley_uniform_limit`: specializes the criterion to character-product vectors.

## References

* [Aharonov et al., 2001][AharonovEtAl2001Walks]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.Cayley

open scoped BigOperators Matrix Topology
open Filter
open Qatlib.Papers.QWalkGraphs00.MainResults.Core
open Qatlib.Papers.QWalkGraphs00.MainResults.Distribution

variable {A ι : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
  [Fintype ι] [DecidableEq ι]

variable {Coin V : Type*} [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V]

/-- The coined Cayley step whose entry from `q` to `p` is `C p.1 q.1` when `p.2 = q.2 + shift
q.1`, and zero otherwise. -/
def cayleyStep (C : Matrix ι ι ℂ) (shift : ι → A) : Matrix (ι × A) (ι × A) ℂ :=
  fun p q => C p.1 q.1 * (if p.2 = q.2 + shift q.1 then (1 : ℂ) else 0)

/-- The coin matrix with column `b` multiplied by the character factor `χ (-shift b)`. -/
def twistedCoin (C : Matrix ι ι ℂ) (shift : ι → A) (χ : A → ℂ) : Matrix ι ι ℂ :=
  fun a b => C a b * χ (-(shift b))

/-- On a product of a coin vector and an additive character, the Cayley step acts by the twisted
coin on the coin factor. See [Aharonov et al., Theorem 3.6][AharonovEtAl2001Walks]. -/
theorem cayleyStep_mulVec_character
    (C : Matrix ι ι ℂ) (shift : ι → A) (χ : A → ℂ)
    (hχadd : ∀ v w, χ (v + w) = χ v * χ w)
    (c : ι → ℂ) (v : A) (a : ι) :
    (cayleyStep C shift *ᵥ (fun p : ι × A => c p.1 * χ p.2)) (a, v)
      = (twistedCoin C shift χ *ᵥ c) a * χ v := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp only [cayleyStep]

  have hinner : ∀ b : ι,
      (∑ q : A, (C a b * (if v = q + shift b then (1 : ℂ) else 0)) * (c b * χ q))
        = C a b * c b * χ (-(shift b)) * χ v := by
    intro b
    have hcollapse : (∑ q : A, (C a b * (if v = q + shift b then (1 : ℂ) else 0)) *
        (c b * χ q)) = C a b * (c b * χ (v - shift b)) := by
      have hsingle := Finset.sum_eq_single (s := Finset.univ)
        (f := fun q : A => (C a b * (if v = q + shift b then (1 : ℂ) else 0)) * (c b * χ q))
        (v - shift b) ?_ ?_
      · have hf : (fun q : A => (C a b * (if v = q + shift b then (1 : ℂ) else 0)) *
            (c b * χ q)) (v - shift b) = C a b * (c b * χ (v - shift b)) := by
          simp [sub_add_cancel]
        rw [hsingle]
        simpa [sub_add_cancel] using hf
      · intro q _ hq
        have hvq : v ≠ q + shift b := by
          intro h
          apply hq
          rw [h, add_sub_cancel_right]
        simp only [if_neg hvq, mul_zero, zero_mul]
      · intro hnotmem
        exact absurd (Finset.mem_univ (v - shift b)) hnotmem
    rw [hcollapse, sub_eq_add_neg, hχadd v (-(shift b))]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hinner b), ← Finset.sum_mul]
  simp only [twistedCoin, Matrix.mulVec, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A twisted-coin eigenvector multiplied by its character satisfies the full Cayley-step
eigenvalue equation with the same eigenvalue. See [Aharonov et al., Theorem
3.6][AharonovEtAl2001Walks]. -/
theorem cayleyStep_eigenvector
    (C : Matrix ι ι ℂ) (shift : ι → A) (χ : A → ℂ)
    (hχadd : ∀ v w, χ (v + w) = χ v * χ w)
    (c : ι → ℂ) (μ : ℂ)
    (hc : twistedCoin C shift χ *ᵥ c = μ • c) :
    cayleyStep C shift *ᵥ (fun p : ι × A => c p.1 * χ p.2)
      = μ • (fun p : ι × A => c p.1 * χ p.2) := by
  funext p
  obtain ⟨a, v⟩ := p
  rw [cayleyStep_mulVec_character C shift χ hχadd c v a, hc]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [AddCommGroup A] [Fintype A] [DecidableEq A] [DecidableEq ι] in

/-- The vertex weight of a coin-character product factors as the squared norm of the coin vector
times the squared norm of the character value. -/
theorem nodeWeight_character (c : ι → ℂ) (χ : A → ℂ) (v : A) :
    ∑ a : ι, Complex.normSq (c a * χ v)
      = (∑ a : ι, Complex.normSq (c a)) * Complex.normSq (χ v) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Complex.normSq_mul]

omit [AddCommGroup A] [DecidableEq A] [DecidableEq ι] in

/-- A normalized coin vector multiplied by character values of squared norm `1 / card A` has
uniform vertex weight. See [Aharonov et al., Theorem 3.6][AharonovEtAl2001Walks]. -/
theorem nodeWeight_character_uniform (c : ι → ℂ) (χ : A → ℂ)
    (hc : ∑ a : ι, Complex.normSq (c a) = 1)
    (hχ : ∀ v : A, Complex.normSq (χ v) = (Fintype.card A : ℝ)⁻¹) (v : A) :
    ∑ a : ι, Complex.normSq (c a * χ v) = (Fintype.card A : ℝ)⁻¹ := by
  rw [nodeWeight_character, hc, one_mul, hχ v]

/-- If a state expands in eigenvectors with distinct unit-modulus eigenvalues, uniform vertex
weights, and coefficients of total squared norm one, its averaged vertex probabilities
converge to the uniform distribution. -/
theorem uniform_limit_of_uniform_eigenvectors
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hlam : ∀ j, ‖lam j‖ = 1)
    (hψ : ψ = ∑ j, a j • φ j)
    (hinj : Function.Injective lam)
    (huniform : ∀ (i : Coin × V) (v : V),
      ∑ c : Coin, Complex.normSq (φ i (c, v)) = (Fintype.card V : ℝ)⁻¹)
    (haunit : ∑ i : Coin × V, Complex.normSq (a i) = 1)
    (v : V) :
    Tendsto (fun T : ℕ => avgNodeProb U ψ T v) atTop (𝓝 ((Fintype.card V : ℝ)⁻¹)) := by
  have h := limiting_distribution_distinct_eigenvalues U φ lam a ψ hφ hlam hψ hinj v
  have hlim : (∑ i : Coin × V,
        Complex.normSq (a i) * ∑ c : Coin, Complex.normSq (φ i (c, v)))
      = (Fintype.card V : ℝ)⁻¹ := by
    have hstep : ∀ i : Coin × V,
        Complex.normSq (a i) * ∑ c : Coin, Complex.normSq (φ i (c, v))
          = Complex.normSq (a i) * (Fintype.card V : ℝ)⁻¹ := by
      intro i; rw [huniform i v]
    rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.sum_mul, haunit, one_mul]
  rwa [hlim] at h

omit [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V] in

/-- Under the stated character, normalization, and distinct unit-modulus eigenvalue hypotheses,
the averaged Cayley-walk vertex probabilities converge to `1 / card A`. See [Aharonov et
al., Theorem 3.6][AharonovEtAl2001Walks]. -/
theorem cayley_uniform_limit
    (C : Matrix ι ι ℂ) (shift : ι → A)
    (cv : (ι × A) → ι → ℂ) (chr : (ι × A) → A → ℂ) (mu : (ι × A) → ℂ)
    (a : (ι × A) → ℂ) (ψ : (ι × A) → ℂ)
    (hchr : ∀ i : ι × A, ∀ v w : A, chr i (v + w) = chr i v * chr i w)
    (hcv : ∀ i : ι × A, twistedCoin C shift (chr i) *ᵥ cv i = mu i • cv i)
    (hcunit : ∀ i : ι × A,
      ∑ a' : ι, Complex.normSq (cv i a') = (Fintype.card A : ℝ)⁻¹)
    (hχunit : ∀ (i : ι × A) (v : A), Complex.normSq (chr i v) = 1)
    (hmu : ∀ i : ι × A, ‖mu i‖ = 1)
    (hinj : Function.Injective mu)
    (hψ : ψ = ∑ i, a i • (fun p : ι × A => cv i p.1 * chr i p.2))
    (haunit : ∑ i : ι × A, Complex.normSq (a i) = 1) (v : A) :
    Tendsto (fun T : ℕ => avgNodeProb (cayleyStep C shift) ψ T v) atTop
      (𝓝 ((Fintype.card A : ℝ)⁻¹)) := by
  have hφ : ∀ j : ι × A,
      cayleyStep C shift *ᵥ (fun p : ι × A => cv j p.1 * chr j p.2)
        = mu j • (fun p : ι × A => cv j p.1 * chr j p.2) :=
    fun j => cayleyStep_eigenvector C shift (chr j) (hchr j) (cv j) (mu j) (hcv j)
  have huniform : ∀ (i : ι × A) (w : A),
      ∑ c : ι, Complex.normSq ((fun p : ι × A => cv i p.1 * chr i p.2) (c, w))
        = (Fintype.card A : ℝ)⁻¹ := by
    intro i w
    rw [nodeWeight_character, hcunit i, hχunit i w, mul_one]
  exact uniform_limit_of_uniform_eigenvectors (cayleyStep C shift)
    (fun i => fun p : ι × A => cv i p.1 * chr i p.2) mu a ψ hφ hmu hψ hinj huniform
    haunit v

end Qatlib.Papers.QWalkGraphs00.MainResults.Cayley
