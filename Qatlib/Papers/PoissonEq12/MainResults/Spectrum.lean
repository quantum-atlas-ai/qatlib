/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PoissonEq12.MainResults.SineApproximation

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2 of *Quantum algorithm and circuit design solving the Poisson equation*
(arXiv:1207.2485, Appendix 2)

The paper's Theorem 2 passes from the one-dimensional error bound of Proposition 2 to the
d-dimensional spectrum of `-Δ_h`, `h = 1 / M`:

`|λ_{j₁,…,j_d} - λ̂_{j₁,…,j_d}| ≤ 17 M ^ 2 d / 2 ^ ν`.

The paper's proof is one sentence: the d-dimensional eigenvalues are sums of the
one-dimensional ones.  Note that the printed statement of Theorem 2 writes the d-dimensional
eigenvalue as `4 M ^ 2 ∏_k sin ^ 2 (j_k π / (2 M))` with `λ̂ = ∑_k ℓ_{j_k}`, which does not fit
that proof: `∑_k 4 M ^ 2 sin ^ 2 (j_k π / (2 M))` is the spectrum of the finite-difference
Laplacian, and it is this sum that `λ̂` approximates.  The statements below use the sum, i.e. the
form assumed by the paper's own proof.
-/

namespace Qatlib.Papers.PoissonEq12.MainResults

set_option autoImplicit false

open scoped BigOperators

/-- **Theorem 2** of arXiv:1207.2485: if each one-dimensional eigenvalue
`4 M ^ 2 sin ^ 2 θ_k` is approximated by `ℓ_k` within `17 M ^ 2 / 2 ^ ν`, then the
d-dimensional eigenvalue `∑_k 4 M ^ 2 sin ^ 2 θ_k` of `-Δ_h` is approximated by `∑_k ℓ_k`
within `17 M ^ 2 d / 2 ^ ν`. -/
theorem theorem2 {d M ν : ℕ} {θ ℓ : Fin d → ℝ}
    (h : ∀ k, |(4 : ℝ) * (M : ℝ) ^ 2 * Real.sin (θ k) ^ 2 - ℓ k|
      ≤ (17 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν) :
    |∑ k, (4 : ℝ) * (M : ℝ) ^ 2 * Real.sin (θ k) ^ 2 - ∑ k, ℓ k|
      ≤ (17 : ℝ) * (M : ℝ) ^ 2 * d / 2 ^ ν := by
  have hsplit : ∑ k, (4 : ℝ) * (M : ℝ) ^ 2 * Real.sin (θ k) ^ 2 - ∑ k, ℓ k
      = ∑ k, ((4 : ℝ) * (M : ℝ) ^ 2 * Real.sin (θ k) ^ 2 - ℓ k) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  have hmass : ∑ _k : Fin d, (17 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν
      = (d : ℝ) * ((17 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc |∑ k, ((4 : ℝ) * (M : ℝ) ^ 2 * Real.sin (θ k) ^ 2 - ℓ k)|
      ≤ ∑ k, |(4 : ℝ) * (M : ℝ) ^ 2 * Real.sin (θ k) ^ 2 - ℓ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, (17 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν :=
        Finset.sum_le_sum fun k _ => h k
    _ = (d : ℝ) * ((17 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν) := hmass
    _ = (17 : ℝ) * (M : ℝ) ^ 2 * d / 2 ^ ν := by ring

/-- **Theorem 2** with the one-dimensional bounds supplied by Proposition 2: for grid points
`θ k` in the range of Proposition 2 and `ν`-bit truncated values `ℓ k`, the d-dimensional
eigenvalue error is at most `17 M ^ 2 d / 2 ^ ν`. -/
theorem theorem2_of_truncation {d M ν s : ℕ} (hν : 1 ≤ ν) (hM : 1 ≤ M)
    (hs : 2 * ν + 9 ≤ s) (T : BitTruncation s) (θ ℓ : Fin d → ℝ)
    (hθ0 : ∀ k, 0 ≤ θ k) (hθ : ∀ k, θ k < Real.pi / 2)
    (hℓ : ∀ k, |ℓ k - (4 : ℝ) * (M : ℝ) ^ 2
        * ((repeatedSquaring T (wQuad (θ k / (2 : ℝ) ^ (ν + 7))) (ν + 7)).im) ^ 2|
        ≤ 1 / 2 ^ ν) :
    |∑ k, (4 : ℝ) * (M : ℝ) ^ 2 * Real.sin (θ k) ^ 2 - ∑ k, ℓ k|
      ≤ (17 : ℝ) * (M : ℝ) ^ 2 * d / 2 ^ ν := by
  refine theorem2 (d := d) (ν := ν) (fun k => ?_)
  have hsin := prop2_sin (s := s) hν hs T (hθ0 k) (hθ k)
  have hk : 0 ≤ θ k := hθ0 k
  have hklt : θ k < Real.pi / 2 := hθ k
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ (ν + 7) := by positivity
  have hx2 : θ k ≤ 2 := by linarith [Real.pi_lt_four, Real.pi_pos]
  have hy1 : θ k / (2 : ℝ) ^ (ν + 7) ≤ 1 := by
    rw [div_le_iff₀ hrpos]
    have : (2 : ℝ) ≤ (2 : ℝ) ^ (ν + 7) := by
      have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (ν + 7) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simpa using h1
    linarith
  have hy0 : 0 ≤ θ k / (2 : ℝ) ^ (ν + 7) := by positivity
  have hW : ‖wQuad (θ k / (2 : ℝ) ^ (ν + 7))‖ ≤ 1 := norm_wQuad_le_one hy0 hy1
  have ht : |(repeatedSquaring T (wQuad (θ k / (2 : ℝ) ^ (ν + 7))) (ν + 7)).im| ≤ 1 :=
    (abs_im_le_norm' _).trans (norm_repeatedSquaring_le_one T hW (ν + 7))
  exact prop2_eigenvalue_truncated hM hsin ht (hℓ k)

end Qatlib.Papers.PoissonEq12.MainResults
