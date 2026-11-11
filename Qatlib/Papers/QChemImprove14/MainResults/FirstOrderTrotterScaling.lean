/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Claim c004 — first-order Trotter energy error scales as `1/n^2`

Hastings--Wecker--Bauer--Troyer, fixed arXiv:1403.1539v2 (23 Mar 2014),
Appendix A "Error Scaling in First Order Trotter-Suzuki", Eqs. (A1)–(A5).

For `H = Σ_j H_j` (Eq. (A1)), an explicit commutator computation (Eq. (A4))
shows that the first-order product `exp(iH₁δ_t)⋯exp(iH_N δ_t)` is, up to
`O(δ_t³)`, the evolution under the *modified* Hamiltonian `H + Δ`, where

  `Δ = i Σ_{j<k} [H_j, H_k] δ_t / 2`.   (Eq. (A5))

If `H` is real with a non-degenerate ground state `ψ_0` (real), then `Δ` is
"pure imaginary", so `⟨ψ_0|Δ|ψ_0⟩` is pure imaginary; being the expectation of
a Hermitian operator it is real, hence it vanishes.  Therefore the first-order
energy shift `E_0' − E_0` is `O(δ_t²)` (no linear-in-`δ_t` term), and with the
step `δ_t = t/n` the ground-state energy error is `O(1/n²)` — better than the
generic `O(1/n)`.

Formalization: `[H_j, H_k] = H_j H_k − H_k H_j` is skew-symmetric for real
symmetric `H_j, H_k`; a skew-symmetric quadratic form on a *real* vector
vanishes.  This is the real-number content of "the `i`-multiplied expectation
is zero".  The remainder estimate is then the standard second-order statement
`E_0' − E_0 = δ_t·μ + δ_t²·R` with `μ = 0` and `|R| ≤ C`.
-/

set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QChemImprove14.MainResults

/-! ## Commutators are skew-symmetric for a real Hamiltonian (Eq. (A5)) -/

/-- For real symmetric `A, B`, the commutator `A B − B A` is skew-symmetric. -/
theorem commutator_skew {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B) :
    (A * B - B * A)ᵀ = -(A * B - B * A) := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hA, hB, neg_sub]

/-- A skew-symmetric real quadratic form vanishes on every real vector:
`v ⬝ᵥ (M *ᵥ v) = 0` whenever `Mᵀ = −M`. -/
theorem skew_quadratic_eq_zero {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hM : Mᵀ = -M) (v : n → ℝ) :
    v ⬝ᵥ (M *ᵥ v) = 0 := by
  have h := dotProduct_transpose_mulVec M v v
  rw [hM, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- The commutator sum `Σ_{j<k} [H_j, H_k]` appearing in Eq. (A5) (without the
outer factor `i δ_t / 2`). -/
noncomputable def commutatorSum {m n : Type*} [Fintype m] [LinearOrder m]
    [Fintype n] (H : m → Matrix n n ℝ) : Matrix n n ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : m × m => p.1 < p.2),
    (H p.1 * H p.2 - H p.2 * H p.1)

/-- **Claim c004 (Eq. (A5))**: the full commutator sum is skew-symmetric when
every `H_j` is real symmetric. -/
theorem commutatorSum_skew {m n : Type*} [Fintype m] [LinearOrder m]
    [Fintype n] [DecidableEq n]
    (H : m → Matrix n n ℝ) (hH : ∀ j, (H j)ᵀ = H j) :
    (commutatorSum H)ᵀ = -(commutatorSum H) := by
  unfold commutatorSum
  rw [Matrix.transpose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Matrix.transpose_sub]
  simp only [Matrix.transpose_mul, hH]
  rw [neg_sub]

/-- The first-order shift `⟨ψ|Δ|ψ⟩` written as a quadratic form
`v ⬝ᵥ (Δ *ᵥ v)`. -/
noncomputable def firstOrderShift {n : Type*} [Fintype n]
    (Δ : Matrix n n ℝ) (v : n → ℝ) : ℝ := v ⬝ᵥ (Δ *ᵥ v)

/-- **Claim c004 (vanishing expectation)**: the ground-state expectation of the
commutator sum in Eq. (A5) vanishes on any real vector `v` (in particular the
real ground state `ψ_0`).  This is the formal "`Δ` is pure imaginary while the
expectation of a Hermitian operator is real, so it is zero". -/
theorem commutator_expectation_zero {m n : Type*} [Fintype m] [LinearOrder m]
    [Fintype n] [DecidableEq n]
    (H : m → Matrix n n ℝ) (hH : ∀ j, (H j)ᵀ = H j) (v : n → ℝ) :
    firstOrderShift (commutatorSum H) v = 0 :=
  skew_quadratic_eq_zero (commutatorSum H) (commutatorSum_skew H hH) v

/-! ## From the vanishing first-order shift to the `1/n²` energy error -/

/-- **Claim c004 (second-order energy shift)**: if the modified ground energy
satisfies `E_0' − E_0 = δ·μ + δ²·R` with first-order coefficient `μ = 0` and
bounded remainder `|R| ≤ C`, then `|E_0' − E_0| ≤ C δ²`.  The hypothesis
`μ = 0` is exactly the vanishing of `⟨ψ_0|Δ|ψ_0⟩` established above. -/
theorem energyShift_secondOrder (E0 E0' μ δ R C : ℝ) (hμ : μ = 0)
    (hrep : E0' - E0 = δ * μ + δ ^ 2 * R) (hR : |R| ≤ C) :
    |E0' - E0| ≤ C * δ ^ 2 := by
  subst hμ
  rw [hrep, show δ * 0 + δ ^ 2 * R = δ ^ 2 * R by ring,
    abs_mul, abs_of_nonneg (sq_nonneg δ)]
  calc δ ^ 2 * |R| ≤ δ ^ 2 * C := mul_le_mul_of_nonneg_left hR (sq_nonneg δ)
    _ = C * δ ^ 2 := by ring

/-- **Claim c004 (main, `1/n²` scaling)**: with the Trotter step `δ_t = t/n`
and the vanishing first-order shift, the ground-state energy error scales as
`C t² / n²`, i.e. `O(1/n²)` in the number of Trotter steps `n`. -/
theorem energyError_oneOverNSq (E0 E0' R C t : ℝ) (n : ℕ) (hn : 0 < n)
    (hrep : E0' - E0 = (t / (n : ℝ)) ^ 2 * R) (hR : |R| ≤ C) :
    |E0' - E0| ≤ C * t ^ 2 / (n : ℝ) ^ 2 := by
  have hbound : |E0' - E0| ≤ C * (t / (n : ℝ)) ^ 2 := by
    refine energyShift_secondOrder E0 E0' 0 (t / (n : ℝ)) R C rfl ?_ hR
    rw [hrep]; ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have heq : C * (t / (n : ℝ)) ^ 2 = C * t ^ 2 / (n : ℝ) ^ 2 := by
    field_simp
  rwa [heq] at hbound

end Qatlib.Papers.QChemImprove14.MainResults
