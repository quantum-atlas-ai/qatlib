/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Lemma 4: locality of unbiasedness for product states

McNulty–Weigert, fixed arXiv:1203.6887v2, Lemma 4, p. 8:

> The product state `|φ, Φ⟩ ∈ C⁶` is MU to the product basis `{|ψᵢ, Ψᵢ⟩}` with
> `i = 1 … 6`, if and only if `|φ⟩` is MU to `|ψᵢ⟩ ∈ C²` and `|Φ⟩` is MU to
> `|Ψᵢ⟩ ∈ C³`.

The proof is the tensor factorization of overlaps
(`⟨φ ⊗ Φ | ψ ⊗ Ψ⟩ = ⟨φ|ψ⟩⟨Φ|Ψ⟩`) together with completeness of the product basis
(Parseval).  Completeness forces the marginal sums `∑ₖ |⟨φ|ψₖ⟩|² = 3` and
`∑ₖ |⟨Φ|Ψₖ⟩|² = 2`; with `|⟨φ|ψₖ⟩|² |⟨Φ|Ψₖ⟩|² = 1/6` pointwise, an elementary
nonnegativity identity pins the local overlaps to `1/2` and `1/3`.  This is the
`a_k = 1/2`, `b_k = 1/3` conclusion used in the paper after Eq. (34).
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Lemma4LocalFactorization

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

/-- **Lemma 4** (arXiv:1203.6887v2, p. 8).  For unit product vectors
`φ ⊗ Φ` and an orthonormal product basis `{ψₖ ⊗ Ψₖ}` of `C² ⊗ C³`, the product
state is MU to the whole basis (all squared overlaps `1/6`) if and only if `φ` is
MU to every `ψₖ` (squared overlaps `1/2`) and `Φ` is MU to every `Ψₖ` (squared
overlaps `1/3`). -/
theorem lemma4_mu_product_iff
    (φ : C2State) (Φ : C3State)
    (ψ : Fin 6 → C2State) (Ψ : Fin 6 → C3State)
    (hφ : Normalized φ) (hΦ : Normalized Φ)
    (hbasis : IsProductBasis ψ Ψ) :
    (∀ k, Complex.normSq (Inner (TensorState φ Φ) (TensorState (ψ k) (Ψ k))) = 1 / 6) ↔
    ((∀ k, Complex.normSq (Inner φ (ψ k)) = 1 / 2) ∧
     (∀ k, Complex.normSq (Inner Φ (Ψ k)) = 1 / 3)) := by
  constructor
  · intro hMU
    let b : Fin 6 → QState (Fin 2 × Fin 3) := fun k => TensorState (ψ k) (Ψ k)
    have hb : ∀ u v : QState (Fin 2 × Fin 3),
        Inner u v = ∑ k, Inner u (b k) * Inner (b k) v := hbasis.2.2
    let a : Fin 6 → ℝ := fun k => Complex.normSq (Inner φ (ψ k))
    let bb : Fin 6 → ℝ := fun k => Complex.normSq (Inner Φ (Ψ k))
    have hprod : ∀ k, a k * bb k = 1 / 6 := by
      intro k
      have h := hMU k
      rw [show Inner (TensorState φ Φ) (TensorState (ψ k) (Ψ k))
            = Inner φ (ψ k) * Inner Φ (Ψ k) from inner_tensorState φ (ψ k) Φ (Ψ k),
          Complex.normSq_mul] at h
      simpa [a, bb] using h
    have ha : ∀ k, 0 < a k := by
      intro k
      have hp := hprod k
      have hge : 0 ≤ a k := Complex.normSq_nonneg _
      have hge2 : 0 ≤ bb k := Complex.normSq_nonneg _
      nlinarith
    -- Marginal sums from Parseval over C³.
    have hnormΨ : ∀ k, ∑ j : Fin 3, Complex.normSq (Ψ k j) = 1 := by
      intro k
      rw [← hbasis.2.1 k]
      apply Finset.sum_congr rfl; intro j _
      rw [Complex.normSq_eq_norm_sq]
    have hrow : ∀ j : Fin 3, ∑ k, a k * Complex.normSq (Ψ k j) = 1 := by
      intro j
      have hu : Normalized (TensorState φ (Ket j)) :=
        normalized_tensorState hφ (normalized_ket j)
      have hp := parseval_normalized hb hu
      rw [show (∑ k, a k * Complex.normSq (Ψ k j))
            = ∑ k, Complex.normSq (Inner (TensorState φ (Ket j)) (b k)) from by
            apply Finset.sum_congr rfl; intro k _
            have hi : Inner (TensorState φ (Ket j)) (b k) = Inner φ (ψ k) * (Ψ k j) := by
              rw [show b k = TensorState (ψ k) (Ψ k) from rfl, inner_tensorState, inner_ket_eq]
            rw [hi, Complex.normSq_mul]]
      exact hp
    have hsa : ∑ k, a k = 3 := by
      have step1 : (∑ k : Fin 6, a k)
          = ∑ k, ∑ j : Fin 3, a k * Complex.normSq (Ψ k j) := by
        apply Finset.sum_congr rfl; intro k _
        rw [← Finset.mul_sum, hnormΨ k, mul_one]
      rw [step1, Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun j _ => hrow j)]
      simp [Fintype.card_fin]
    -- Marginal sums from Parseval over C².
    have hnormψ : ∀ k, ∑ i : Fin 2, Complex.normSq (ψ k i) = 1 := by
      intro k
      rw [← hbasis.1 k]
      apply Finset.sum_congr rfl; intro i _
      rw [Complex.normSq_eq_norm_sq]
    have hrowB : ∀ i : Fin 2, ∑ k, bb k * Complex.normSq (ψ k i) = 1 := by
      intro i
      have hu : Normalized (TensorState (Ket i) Φ) :=
        normalized_tensorState (normalized_ket i) hΦ
      have hp := parseval_normalized hb hu
      rw [show (∑ k, bb k * Complex.normSq (ψ k i))
            = ∑ k, Complex.normSq (Inner (TensorState (Ket i) Φ) (b k)) from by
            apply Finset.sum_congr rfl; intro k _
            have hi : Inner (TensorState (Ket i) Φ) (b k) = (ψ k i) * Inner Φ (Ψ k) := by
              rw [show b k = TensorState (ψ k) (Ψ k) from rfl, inner_tensorState, inner_ket_eq]
            rw [hi, Complex.normSq_mul]
            ring]
      exact hp
    have hsb : ∑ k, bb k = 2 := by
      have step1 : (∑ k : Fin 6, bb k)
          = ∑ k, ∑ i : Fin 2, bb k * Complex.normSq (ψ k i) := by
        apply Finset.sum_congr rfl; intro k _
        rw [← Finset.mul_sum, hnormψ k, mul_one]
      rw [step1, Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun i _ => hrowB i)]
      simp [Fintype.card_fin]
    exact six_term_pin a bb ha hprod hsa hsb
  · rintro ⟨hφMU, hΦMU⟩ k
    rw [inner_tensorState, Complex.normSq_mul, hφMU k, hΦMU k]
    norm_num

end Qatlib.Papers.MUBProduct12.TripleClassify.Lemma4LocalFactorization
