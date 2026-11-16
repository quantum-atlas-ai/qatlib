/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/


module

public import Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding.HammingStates

@[expose] public section


/-!
# MultivariateEncoding — Propositions 5 and 6
(arXiv:2303.01471v1, Appendix F.3)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
PDF pages 54–56, equations (F.37)–(F.42).
-/

open scoped Matrix BigOperators
open Matrix

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.Multivariate

open Qatlib.Papers.QHamDescent23.MainResults
open Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding

/-- Membership in the one-register Hamming encoding space
`S = span{|H_0⟩, …, |H_n⟩}` (Appendix F.3). -/
def InHammingSpan (n : ℕ) (ψ : Ket (BitString n)) : Prop :=
  ∃ c : Fin (n + 1) → ℂ,
    ∀ b, ψ b = ∑ k : Fin (n + 1), c k * hammingState n (k : ℕ) b

/-- Membership in the `d`-fold tensor product `S^{⊗d}` of the Hamming encoding
space (Appendix F.3). -/
def InTensorSpan (d n : ℕ) (ψ : Ket (Fin d → BitString n)) : Prop :=
  ∃ c : (Fin d → Fin (n + 1)) → ℂ,
    ∀ b, ψ b = ∑ ks : Fin d → Fin (n + 1),
      c ks * ∏ i, hammingState n (ks i : ℕ) (b i)

/-- Applying the operator `A` on the `i`-th register of a `d`-register state
(the tensor product `1 ⊗ … ⊗ A ⊗ … ⊗ 1`). -/
def tensorApply {d n : ℕ} (i : Fin d) (A : Matrix (BitString n) (BitString n) ℂ)
    (ψ : Ket (Fin d → BitString n)) : Ket (Fin d → BitString n) :=
  fun b => ∑ b' : BitString n, A (b i) b' * ψ (Function.update b i b')

/-- A one-register state of the multi-variate Gaussian product form is an
element of the encoding space `S`: the `d`-fold product of one-qubit Gaussian
amplitudes lies in `S^{⊗d}` (Proposition 5, (F.37)). -/
theorem source_proposition5_multivariate_gaussian
    (d n : ℕ) (φ : Fin d → Ket (BitString n))
    (hφ : ∀ i, InHammingSpan n (φ i)) :
    InTensorSpan d n (fun b => ∏ i, φ i (b i)) := by
  choose c hc using hφ
  refine ⟨fun ks => ∏ i, c i (ks i), fun b => ?_⟩
  calc ∏ i, φ i (b i)
      = ∏ i, ∑ k : Fin (n + 1), c i k * hammingState n (k : ℕ) (b i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hc i]
    _ = ∑ ks : Fin d → Fin (n + 1),
          ∏ i, c i (ks i) * hammingState n (ks i : ℕ) (b i) := by
        rw [Finset.prod_univ_sum]
        simp
    _ = ∑ ks : Fin d → Fin (n + 1),
          (∏ i, c i (ks i)) * ∏ i, hammingState n (ks i : ℕ) (b i) := by
        apply Finset.sum_congr rfl
        intro ks hks
        rw [Finset.prod_mul_distrib]


end Qatlib.Papers.QHamDescent23.MainResults.Multivariate
