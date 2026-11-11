/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! Power-method trace sandwich for
"Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes" (arXiv:2408.16934v3, 2025).

Lemma 5.1 of the paper: for the reflected Laplacian `H = I − Δ̃_k`
with spectral gap `δ` (the positive eigenvalues of the normalized
Laplacian lie in `[δ, 1]`, and `β_k` counts the zero eigenvalues),
`d ≥ log(1/ε)/δ` implies
`β_k ≤ tr(H^d) ≤ β_k + ε |S_k|`.

The eigenvalue identity `tr(H^d) = ∑_i (1 − w i)^d` (spectral theorem
for the Hermitian `H`) is abstracted: the sandwich is proved for the
eigenvalue sum itself, with `w i = 0` marking the homology (Betti)
directions. Scaling by `|S_k|` recovers the paper's normalized form
`β_k/|S_k| ≤ tr(H^d)/|S_k| ≤ β_k/|S_k| + ε`.

- `one_sub_pow_le_exp` and `exp_neg_mul_le` are the scalar decay
  bounds `(1 − δ)^d ≤ e^{−δd} ≤ ε`.
- `power_sandwich` is the two-sided trace bound.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.BettiNumber25.MainResults.PowerSandwich

/-- Scalar decay, step 1: `(1 − δ)^d ≤ e^{−δd}` for `δ ∈ (0, 1]`. -/
theorem one_sub_pow_le_exp (δ : ℝ) (_hδ : 0 < δ) (hδ1 : δ ≤ 1) (d : ℕ) :
    (1 - δ) ^ d ≤ Real.exp (-(δ * (d : ℝ))) := by
  have h1 : (1 - δ : ℝ) ≤ Real.exp (-δ) := by
    have h := Real.add_one_le_exp (-δ)
    linarith
  have h2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 - δ by linarith) h1 d
  calc (1 - δ) ^ d ≤ Real.exp (-δ) ^ d := h2
    _ = Real.exp (-(δ * (d : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- Scalar decay, step 2: `e^{−δd} ≤ ε` once `d ≥ log(1/ε)/δ`. -/
theorem exp_neg_mul_le (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (d : ℕ)
    (hd : Real.log (1 / ε) / δ ≤ (d : ℝ)) : Real.exp (-(δ * (d : ℝ))) ≤ ε := by
  have hle : Real.log (1 / ε) ≤ δ * (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hd (le_of_lt hδ)
    field_simp at h
    exact h
  have hexp : Real.exp (-(δ * (d : ℝ))) ≤ Real.exp (-(Real.log (1 / ε))) :=
    Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (-(δ * (d : ℝ))) ≤ Real.exp (-(Real.log (1 / ε))) := hexp
    _ = ε := by
        rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε]

/-- **Lemma 5.1, eigenvalue-sum form**: if every normalized Laplacian
eigenvalue `w i` is either `0` (a Betti/homology direction, `β` of
them) or in `[δ, 1]`, and `d ≥ log(1/ε)/δ`, then the trace of
`H^d = (I − Δ̃_k)^d` in eigenvalue form satisfies the two-sided bound
`β ≤ ∑_i (1 − w i)^d ≤ β + ε N` (with `N = |S_k|`; dividing by `N`
gives the paper's normalized sandwich). -/
theorem power_sandwich {N : ℕ} (w : Fin N → ℝ) (δ ε : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hw : ∀ i, w i = 0 ∨ (δ ≤ w i ∧ w i ≤ 1))
    (d : ℕ) (hd : Real.log (1 / ε) / δ ≤ (d : ℝ)) :
    ((Finset.univ.filter fun i => w i = 0).card : ℝ) ≤ ∑ i, (1 - w i) ^ d ∧
      ∑ i, (1 - w i) ^ d ≤ ((Finset.univ.filter fun i => w i = 0).card : ℝ) + (N : ℝ) * ε := by
  classical
  set S : Finset (Fin N) := Finset.univ.filter fun i => w i = 0 with hS
  have hlow : ∀ i ∈ S, (1 - w i) ^ d = 1 := by
    intro i hi
    have h0 : w i = 0 := by simpa [hS] using hi
    simp [h0]
  have hmem : ∀ i, w i ≠ 0 → (1 - w i) ^ d ≤ ε := by
    intro i hne
    rcases hw i with h | ⟨h1, h2⟩
    · exact absurd h hne
    · have hle : (1 - w i) ^ d ≤ (1 - δ) ^ d :=
        pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 - w i by linarith)
          (show 1 - w i ≤ 1 - δ by linarith) d
      calc (1 - w i) ^ d ≤ (1 - δ) ^ d := hle
        _ ≤ Real.exp (-(δ * (d : ℝ))) := one_sub_pow_le_exp δ hδ (le_of_lt hδ1) d
        _ ≤ ε := exp_neg_mul_le δ ε hδ hε d hd
  have hone : ∑ i ∈ S, (1 : ℝ) = S.card := by simp
  constructor
  · calc S.card = ∑ i ∈ S, (1 : ℝ) := hone.symm
      _ = ∑ i ∈ S, (1 - w i) ^ d := Finset.sum_congr rfl fun i hi => (hlow i hi).symm
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)), (1 - w i) ^ d := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset (fun i => w i = 0) (Finset.univ : Finset (Fin N))) ?_
          intro i _ _
          rcases hw i with h | ⟨h1, h2⟩
          · simp [h]
          · exact pow_nonneg (by linarith) d
      _ = ∑ i, (1 - w i) ^ d := rfl
  · have hsplit := Finset.sum_add_sum_compl S (fun i => (1 - w i) ^ d)
    have hScard : (Sᶜ : Finset (Fin N)).card ≤ N := by
      simpa using Finset.card_le_univ (s := Sᶜ)
    have hS1 : ∑ i ∈ S, (1 - w i) ^ d ≤ (S.card : ℝ) := by
      have heq : ∑ i ∈ S, (1 - w i) ^ d = ∑ i ∈ S, (1 : ℝ) :=
        Finset.sum_congr rfl fun i hi => hlow i hi
      rw [heq]
      exact le_of_eq hone
    have hS2 : ∑ i ∈ Sᶜ, (1 - w i) ^ d ≤ (N : ℝ) * ε := by
      have h1 : ∀ i ∈ Sᶜ, (1 - w i) ^ d ≤ ε := fun i hi =>
        hmem i (by simpa [hS] using hi)
      have h2 : ∑ i ∈ Sᶜ, (1 - w i) ^ d ≤ ∑ i ∈ Sᶜ, (ε : ℝ) :=
        Finset.sum_le_sum h1
      have h3 : ∑ i ∈ Sᶜ, (ε : ℝ) = (((Sᶜ : Finset (Fin N)).card : ℕ) : ℝ) * ε := by
        simp
      rw [h3] at h2
      calc ∑ i ∈ Sᶜ, (1 - w i) ^ d ≤ (((Sᶜ : Finset (Fin N)).card : ℕ) : ℝ) * ε := h2
        _ ≤ (N : ℝ) * ε :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) (by positivity)
    calc ∑ i, (1 - w i) ^ d = ∑ i ∈ S, (1 - w i) ^ d + ∑ i ∈ Sᶜ, (1 - w i) ^ d :=
          hsplit.symm
      _ ≤ (S.card : ℝ) + (N : ℝ) * ε := by
          exact add_le_add hS1 hS2

end Qatlib.Papers.BettiNumber25.MainResults.PowerSandwich
