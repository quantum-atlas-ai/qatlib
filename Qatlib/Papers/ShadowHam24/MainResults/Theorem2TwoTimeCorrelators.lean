/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowHam24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2 (arXiv:2407.21775, p. 6, Eqs. (6)–(8))

Two-time correlators `⟨O_m(t) O_{m'}(t')⟩ = tr(ρ O_m(t) O_{m'}(t'))` satisfy
∂_t C = -i (H_S ⊗ 1) C and ∂_{t'} C = -i (1 ⊗ H_S) C.  In the amplitude-matrix
representation `C_{m m'} = ⟨O_m(t)O_{m'}(t')⟩` the two Kronecker actions are
left multiplication by `H_S` and right multiplication by `H_Sᵀ` respectively:
`(H_S ⊗ 1) C = H_S * C` and `(1 ⊗ H_S) C = C * H_Sᵀ`.

Proof follows Supplementary Note 1, Eq. (20): use Heisenberg's equation
`d/dt O(t) = i[H,O(t)]` and the IP.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace Qatlib.Papers.ShadowHam24.MainResults

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

/-- The two-time shadow amplitude matrix `C_{m m'} = tr(ρ O_m(t) O_{m'}(t'))`
of paper Eq. (6). -/
def twoTimeShadow (ρ : Matrix N N ℂ) (A B : ℝ → M → Matrix N N ℂ)
    (t t' : ℝ) : Matrix M M ℂ :=
  fun m m' => (ρ * A t m * B t' m').trace

/-- **Theorem 2** (paper p. 6, Eqs. (7)–(8)): if the operator families `A` and
`B` satisfy Heisenberg's equations and the IP with the same shadow Hamiltonian
`hS`, then the two-time shadow matrix satisfies
`∂_t C = -i (H_S * C)` and `∂_{t'} C = -i (C * H_Sᵀ)`. -/
theorem twoTimeShadow_evolution (ρ : Matrix N N ℂ) (H : Matrix N N ℂ)
    (A B : ℝ → M → Matrix N N ℂ) (hS : Matrix M M ℂ) (t t' : ℝ)
    (hA : ∀ m, HasDerivAt (fun s => A s m)
      (Complex.I • (H * A t m - A t m * H)) t)
    (hB : ∀ m, HasDerivAt (fun s => B s m)
      (Complex.I • (H * B t' m - B t' m * H)) t')
    (hAip : ∀ m, H * A t m - A t m * H = - ∑ m', hS m m' • A t m')
    (hBip : ∀ m, H * B t' m - B t' m * H = - ∑ m', hS m m' • B t' m') :
    (∀ m m', HasDerivAt (fun s => twoTimeShadow ρ A B s t' m m')
        ((-(Complex.I)) * (hS * twoTimeShadow ρ A B t t') m m') t) ∧
    (∀ m m', HasDerivAt (fun s => twoTimeShadow ρ A B t s m m')
        ((-(Complex.I)) * (twoTimeShadow ρ A B t t' * hSᵀ) m m') t') := by
  constructor
  · intro m m'
    have h1 : HasDerivAt (fun s => ρ * A s m)
        (ρ * (Complex.I • (H * A t m - A t m * H))) t :=
      (hA m).const_mul ρ
    have h2 : HasDerivAt (fun s => ρ * A s m * B t' m')
        ((ρ * (Complex.I • (H * A t m - A t m * H))) * B t' m') t :=
      h1.mul_const (B t' m')
    have h3 := hasDerivAt_trace (fun s => ρ * A s m * B t' m') _ t h2
    have heq : ((ρ * (Complex.I • (H * A t m - A t m * H))) * B t' m').trace
        = (-(Complex.I)) * (hS * twoTimeShadow ρ A B t t') m m' := by
      rw [trace_mul_smul_mul, hAip m, trace_mul_neg_sum_smul_mul, Matrix.mul_apply]
      simp only [twoTimeShadow]
      have hs : (∑ k, hS m k * (ρ * A t k * B t' m').trace)
          = (∑ k, hS m k * (ρ * A t k * B t' m').trace) := rfl
      rw [hs]
      ring
    rw [heq] at h3
    simpa [twoTimeShadow] using h3
  · intro m m'
    have h1 : HasDerivAt (fun s => B s m')
        (Complex.I • (H * B t' m' - B t' m' * H)) t' := hB m'
    have h2 : HasDerivAt (fun s => ρ * A t m * B s m')
        (ρ * A t m * (Complex.I • (H * B t' m' - B t' m' * H))) t' :=
      h1.const_mul (ρ * A t m)
    have h3 := hasDerivAt_trace (fun s => ρ * A t m * B s m') _ t' h2
    have heq : (ρ * A t m * (Complex.I • (H * B t' m' - B t' m' * H))).trace
        = (-(Complex.I)) * (twoTimeShadow ρ A B t t' * hSᵀ) m m' := by
      rw [trace_mul_smul, hBip m', trace_mul_neg_sum_smul, Matrix.mul_apply]
      simp only [twoTimeShadow, Matrix.transpose_apply]
      have hs : (∑ k, (ρ * A t m * B t' k).trace * hS m' k)
          = (∑ m'', hS m' m'' * (ρ * A t m * B t' m'').trace) := by
        apply Finset.sum_congr rfl; intro k _
        ring
      rw [hs]
      ring
    rw [heq] at h3
    simpa [twoTimeShadow] using h3

end Qatlib.Papers.ShadowHam24.MainResults
