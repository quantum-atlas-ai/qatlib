/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactionMech16.MainResults.Source.Lemma3SmallestEigenvalueStability
import Qatlib.Papers.ReactionMech16.MainResults.Source.Lemma4EvoErrorToGenerator

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1: Trotter-Suzuki simulation error and the ground-state energy

Source: arXiv:1605.03590v2, Appendix D, Theorem 1 (pp.14--15, Eqs. (D6)--(D7)).

Let `H = ∑_{j=1}^{M} H_j` and `H̃ = ∑_{j=1}^{M} H̃_j` be sums of bounded Hermitian
operators with `‖H_j - H̃_j‖₂ ≤ δ`, and suppose the second-order Strang product
deviates from the exact evolution by at most `Δ_{TS}(t) t`.  Then the ground-state
energies of `H` and of the effective Hamiltonian
`H̃(t) = i log(∏ e^{-iH̃_j t/2} ∏ e^{-iH̃_j t/2}) / t` differ by at most
`Δ_{TS}(t) + (2M - 1) δ`.

The formal proof follows the paper's chain:
1. triangle inequality `(D6)`: exact evolution vs Strang product of `H`, plus the
   Strang product of `H` vs that of `H̃` (termwise perturbation, `(D7)`);
2. Lemma 4 (`lemma4_evo_error_to_generator_gap`) converts the evolution error into
   the generator-norm bound `‖H - H̃(t)‖₂ ≤ Δ_{TS}(t) + (2M - 1) δ`;
3. Lemma 3 (`lemma3_smallest_eigenvalue_gap_le`) converts that into the ground-state
   energy gap.

We state the time-dependent bound for all `s ≥ 0`, which is how the paper's
`Δ_{TS}(t)` is used in Lemma 4 (the bound must hold near `t = 0`).  The effective
Hamiltonian is supplied by any Hermitian `K` whose exponential is the Strang
product of the `H̃_j`; this is exactly the defining property of the matrix-log
`H̃(t)` proved in Theorem 1's first paragraph.

The termwise perturbation bound `(D7)` is proved by telescoping the two order-`M`
products: each of the `M` factors differs by at most `δ t / 2`, and all factors are
unitary.  The two halves of the Strang product contribute `2M · δ t / 2 = M δ t`,
which is stronger than the paper's `(2M - 1) δ t`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- Second-order Strang (Trotter-Suzuki) product
`∏_{j=1}^{M} e^{-iH_j t/2} ∏_{j=M}^{1} e^{-iH_j t/2}`. -/
noncomputable def strangProduct {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (Hs : Fin M → Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  (List.ofFn fun j => matrixExpEvo (Hs j) (t / 2)).prod *
    (List.ofFn fun j => matrixExpEvo (Hs (Fin.rev j)) (t / 2)).prod

/-- The smallest eigenvalue, realized as the last (decreasingly ordered) eigenvalue. -/
noncomputable def smallestEigenvalue {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀
    ⟨Fintype.card I - 1, by
      have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
      omega⟩

/-- A finite sum of Hermitian matrices is Hermitian. -/
theorem hermitian_sum {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (Hs : Fin M → Matrix I I ℂ) (hH : ∀ j, (Hs j).IsHermitian) :
    (∑ j : Fin M, Hs j).IsHermitian := by
  classical
  induction (Finset.univ : Finset (Fin M)) using Finset.induction with
  | empty => simpa using (Matrix.isHermitian_zero : (0 : Matrix I I ℂ).IsHermitian)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hH a).add ih

/-- A product of matrices of operator norm at most one has operator norm at most
one. -/
lemma List.norm_prod_le_one {α : Type} [NormedRing α] [NormOneClass α] :
    ∀ {l : List α}, (∀ x ∈ l, ‖x‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simp
  | a :: l, h => by
      rw [List.prod_cons]
      calc
        ‖a * l.prod‖ ≤ ‖a‖ * ‖l.prod‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (h a (by simp))
          (List.norm_prod_le_one (fun x hx => h x (by simp [hx])))
          (norm_nonneg _) zero_le_one
        _ = 1 := by ring

/-- Telescoping estimate for the difference of two products: if the factors have
norm at most one and agree entrywise up to `δ`, the products differ by at most
`length * δ`. -/
lemma List.prod_sub_prod_norm_le {α : Type} [NormedRing α] [NormOneClass α]
    (l₁ l₂ : List α) (δ : ℝ)
    (hlen : l₁.length = l₂.length)
    (h₁ : ∀ x ∈ l₁, ‖x‖ ≤ 1) (h₂ : ∀ x ∈ l₂, ‖x‖ ≤ 1)
    (hδ : 0 ≤ δ)
    (hterm : ∀ k : Fin l₁.length, ‖l₁.get k - l₂.get (Fin.cast hlen k)‖ ≤ δ) :
    ‖l₁.prod - l₂.prod‖ ≤ l₁.length * δ := by
  induction l₁ generalizing l₂ with
  | nil =>
      have h₂nil : l₂ = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst h₂nil
      simp
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          have hlen' : l₁.length = l₂.length := Nat.succ.inj hlen
          have ha : ‖a - b‖ ≤ δ := by
            have h := hterm ⟨0, by simp⟩
            simpa using h
          have htail : ∀ k : Fin l₁.length,
              ‖l₁.get k - l₂.get (Fin.cast hlen' k)‖ ≤ δ := by
            intro k
            have h := hterm ⟨k.1 + 1, by simp⟩
            simpa using h
          have h₁a : ‖a‖ ≤ 1 := h₁ a (by simp)
          have h₁tail : ∀ x ∈ l₁, ‖x‖ ≤ 1 := fun x hx => h₁ x (by simp [hx])
          have h₂b : ‖b‖ ≤ 1 := h₂ b (by simp)
          have h₂tail : ∀ x ∈ l₂, ‖x‖ ≤ 1 := fun x hx => h₂ x (by simp [hx])
          have hrec := ih l₂ hlen' h₁tail h₂tail htail
          have hprod₁ : ‖l₁.prod‖ ≤ 1 := List.norm_prod_le_one h₁tail
          have hdecomp : (a :: l₁).prod - (b :: l₂).prod =
              (a - b) * l₁.prod + b * (l₁.prod - l₂.prod) := by
            simp [List.prod_cons]
            noncomm_ring
          rw [hdecomp]
          calc
            ‖(a - b) * l₁.prod + b * (l₁.prod - l₂.prod)‖
                ≤ ‖(a - b) * l₁.prod‖ + ‖b * (l₁.prod - l₂.prod)‖ :=
                  norm_add_le _ _
            _ ≤ ‖a - b‖ * ‖l₁.prod‖ + ‖b‖ * ‖l₁.prod - l₂.prod‖ :=
                  add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
            _ ≤ δ * 1 + 1 * ((l₁.length : ℝ) * δ) := by
                  apply add_le_add
                  · exact mul_le_mul ha hprod₁ (norm_nonneg _) hδ
                  · exact mul_le_mul h₂b hrec (norm_nonneg _) zero_le_one
            _ = ((l₁.length + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-- Version of `List.prod_sub_prod_norm_le` for products indexed by `Fin M`. -/
lemma prodfn_sub_prodfn_norm_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {M : ℕ} (A B : Fin M → Matrix I I ℂ) (δ s : ℝ)
    (hA : ∀ j, ‖A j‖ ≤ 1) (hB : ∀ j, ‖B j‖ ≤ 1)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s)
    (hterm : ∀ j, ‖A j - B j‖ ≤ δ * s) :
    ‖(List.ofFn A).prod - (List.ofFn B).prod‖ ≤ (M : ℝ) * (δ * s) := by
  have hlen : (List.ofFn A).length = (List.ofFn B).length := by simp
  have hbound := List.prod_sub_prod_norm_le (List.ofFn A) (List.ofFn B) (δ * s)
    hlen (by simpa using hA) (by simpa using hB) (mul_nonneg hδ hs) (by
      intro k
      simp only [List.get_ofFn]
      simpa using hterm (Fin.cast (by simp) k))
  simpa using hbound

/-- arXiv:1605.03590v2, Eq. (D7): termwise errors `‖H_j - H̃_j‖ ≤ δ` propagate to
the two-order Strang products with the sharp constant `(2M - 1) δ t`. -/
theorem strang_product_termwise_perturbation
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {M : ℕ} (hM : 1 ≤ M)
    (Hs Hts : Fin M → Matrix I I ℂ) (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 ≤ δ)
    (hH : ∀ j, (Hs j).IsHermitian) (hHt : ∀ j, (Hts j).IsHermitian)
    (hterm : ∀ j, ‖Hs j - Hts j‖ ≤ δ) :
    ‖strangProduct Hs t - strangProduct Hts t‖ ≤ (2 * (M : ℝ) - 1) * δ * t := by
  let A : Fin M → Matrix I I ℂ := fun j => matrixExpEvo (Hs j) (t / 2)
  let B : Fin M → Matrix I I ℂ := fun j => matrixExpEvo (Hts j) (t / 2)
  let A' : Fin M → Matrix I I ℂ := fun j => matrixExpEvo (Hs (Fin.rev j)) (t / 2)
  let B' : Fin M → Matrix I I ℂ := fun j => matrixExpEvo (Hts (Fin.rev j)) (t / 2)
  have ht2 : 0 ≤ t / 2 := by linarith
  have hA : ∀ j, ‖A j‖ ≤ 1 := fun j => le_of_eq (norm_expEvo (Hs j) (hH j) (t / 2))
  have hB : ∀ j, ‖B j‖ ≤ 1 := fun j => le_of_eq (norm_expEvo (Hts j) (hHt j) (t / 2))
  have hA' : ∀ j, ‖A' j‖ ≤ 1 := fun j =>
    le_of_eq (norm_expEvo (Hs (Fin.rev j)) (hH _) (t / 2))
  have hB' : ∀ j, ‖B' j‖ ≤ 1 := fun j =>
    le_of_eq (norm_expEvo (Hts (Fin.rev j)) (hHt _) (t / 2))
  have htermA : ∀ j : Fin M, ‖A j - B j‖ ≤ δ * (t / 2) := by
    intro j
    calc
      ‖A j - B j‖ ≤ ‖Hs j - Hts j‖ * |t / 2| :=
        norm_expEvo_sub_le (Hs j) (Hts j) (hH j) (hHt j) (t / 2)
      _ = ‖Hs j - Hts j‖ * (t / 2) := by rw [abs_of_nonneg ht2]
      _ ≤ δ * (t / 2) := mul_le_mul_of_nonneg_right (hterm j) ht2
  have htermA' : ∀ j : Fin M, ‖A' j - B' j‖ ≤ δ * (t / 2) := by
    intro j
    calc
      ‖A' j - B' j‖ ≤ ‖Hs (Fin.rev j) - Hts (Fin.rev j)‖ * |t / 2| :=
        norm_expEvo_sub_le (Hs (Fin.rev j)) (Hts (Fin.rev j)) (hH _) (hHt _) (t / 2)
      _ = ‖Hs (Fin.rev j) - Hts (Fin.rev j)‖ * (t / 2) := by rw [abs_of_nonneg ht2]
      _ ≤ δ * (t / 2) := mul_le_mul_of_nonneg_right (hterm (Fin.rev j)) ht2
  have hP := prodfn_sub_prodfn_norm_le A B δ (t / 2) hA hB hδ ht2 htermA
  have hQ := prodfn_sub_prodfn_norm_le A' B' δ (t / 2) hA' hB' hδ ht2 htermA'
  have hQ1 : ‖(List.ofFn A').prod‖ ≤ 1 := List.norm_prod_le_one (by simpa using hA')
  have hP2 : ‖(List.ofFn B).prod‖ ≤ 1 := List.norm_prod_le_one (by simpa using hB)
  have hdecomp : strangProduct Hs t - strangProduct Hts t =
      ((List.ofFn A).prod - (List.ofFn B).prod) * (List.ofFn A').prod +
        (List.ofFn B).prod * ((List.ofFn A').prod - (List.ofFn B').prod) := by
    simp only [strangProduct, A, B, A', B']
    noncomm_ring
  rw [hdecomp]
  calc
    ‖((List.ofFn A).prod - (List.ofFn B).prod) * (List.ofFn A').prod +
        (List.ofFn B).prod * ((List.ofFn A').prod - (List.ofFn B').prod)‖
        ≤ ‖((List.ofFn A).prod - (List.ofFn B).prod) * (List.ofFn A').prod‖ +
          ‖(List.ofFn B).prod * ((List.ofFn A').prod - (List.ofFn B').prod)‖ :=
            norm_add_le _ _
    _ ≤ ‖(List.ofFn A).prod - (List.ofFn B).prod‖ * ‖(List.ofFn A').prod‖ +
          ‖(List.ofFn B).prod‖ * ‖(List.ofFn A').prod - (List.ofFn B').prod‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (M : ℝ) * (δ * (t / 2)) * 1 + 1 * ((M : ℝ) * (δ * (t / 2))) := by
          apply add_le_add
          · exact mul_le_mul hP hQ1 (norm_nonneg _)
              (mul_nonneg (show (0:ℝ) ≤ (M:ℝ) by positivity) (mul_nonneg hδ ht2))
          · exact mul_le_mul hP2 hQ (norm_nonneg _) zero_le_one
    _ ≤ (2 * (M : ℝ) - 1) * δ * t := by
          have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
          nlinarith [mul_nonneg hδ ht, (show (0:ℝ) ≤ (M:ℝ) by positivity)]

/-- The paper's triangle-inequality step `(D6)--(D7)`: the exact evolution of `H` and
the effective evolution `e^{-iKt}` (equal to the Strang product of the `H̃_j`) differ
by at most `(Δ + (2M - 1) δ) t`. -/
theorem strang_product_error_bound
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {M : ℕ} (hM : 1 ≤ M)
    (Hs Hts : Fin M → Matrix I I ℂ) (K : Matrix I I ℂ) (Δ δ : ℝ)
    (_hΔ : 0 ≤ Δ) (hδ : 0 ≤ δ)
    (hH : ∀ j, (Hs j).IsHermitian) (hHt : ∀ j, (Hts j).IsHermitian)
    (hterm : ∀ j, ‖Hs j - Hts j‖ ≤ δ)
    (htrot : ∀ s : ℝ, 0 ≤ s →
      ‖matrixExpEvo (∑ j : Fin M, Hs j) s - strangProduct Hs s‖ ≤ Δ * s)
    (hKexp : ∀ s : ℝ, 0 ≤ s → matrixExpEvo K s = strangProduct Hts s) :
    ∀ s : ℝ, 0 ≤ s →
      ‖matrixExpEvo (∑ j : Fin M, Hs j) s - matrixExpEvo K s‖ ≤
        (Δ + (2 * (M : ℝ) - 1) * δ) * s := by
  intro s hs
  rw [hKexp s hs]
  have hprod := strang_product_termwise_perturbation hM Hs Hts s δ hs hδ hH hHt hterm
  calc
    ‖matrixExpEvo (∑ j : Fin M, Hs j) s - strangProduct Hts s‖
        = ‖(matrixExpEvo (∑ j : Fin M, Hs j) s - strangProduct Hs s) +
            (strangProduct Hs s - strangProduct Hts s)‖ := by
      congr 1
      abel
    _ ≤ ‖matrixExpEvo (∑ j : Fin M, Hs j) s - strangProduct Hs s‖ +
          ‖strangProduct Hs s - strangProduct Hts s‖ := norm_add_le _ _
    _ ≤ Δ * s + (2 * (M : ℝ) - 1) * δ * s := add_le_add (htrot s hs) hprod
    _ = (Δ + (2 * (M : ℝ) - 1) * δ) * s := by ring

/-- arXiv:1605.03590v2, Theorem 1 (pp.14--15): with termwise errors bounded by `δ`
and Strang-product Trotter error bounded by `Δ s`, the ground-state energy of the
effective Hamiltonian `K` (whose evolution is the Strang product of the `H̃_j`)
differs from that of `H = ∑ H_j` by at most `Δ + (2M - 1) δ`. -/
theorem theorem1_trotter_ground_energy
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {M : ℕ} (hM : 1 ≤ M)
    (Hs Hts : Fin M → Matrix I I ℂ)
    (hH : ∀ j, (Hs j).IsHermitian) (hHt : ∀ j, (Hts j).IsHermitian)
    (K : Matrix I I ℂ) (hK : K.IsHermitian) (Δ δ : ℝ) (hΔ : 0 ≤ Δ) (hδ : 0 ≤ δ)
    (hterm : ∀ j, ‖Hs j - Hts j‖ ≤ δ)
    (htrot : ∀ s : ℝ, 0 ≤ s →
      ‖matrixExpEvo (∑ j : Fin M, Hs j) s - strangProduct Hs s‖ ≤ Δ * s)
    (hKexp : ∀ s : ℝ, 0 ≤ s → matrixExpEvo K s = strangProduct Hts s) :
    |smallestEigenvalue (∑ j : Fin M, Hs j) (hermitian_sum Hs hH) -
        smallestEigenvalue K hK| ≤ Δ + (2 * (M : ℝ) - 1) * δ := by
  have hc : 0 ≤ Δ + (2 * (M : ℝ) - 1) * δ := by
    have hM1 : (0 : ℝ) ≤ 2 * (M : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    exact add_nonneg hΔ (mul_nonneg hM1 hδ)
  have hevo := strang_product_error_bound hM Hs Hts K Δ δ hΔ hδ hH hHt hterm htrot hKexp
  have hevo' : ∀ s : ℝ, 0 ≤ s →
      ‖matrixExpEvo (∑ j : Fin M, Hs j) s - matrixExpEvo K s‖ ≤
        s * (Δ + (2 * (M : ℝ) - 1) * δ) := by
    intro s hs
    rw [mul_comm]
    exact hevo s hs
  have hgen : ‖(∑ j : Fin M, Hs j) - K‖ ≤ Δ + (2 * (M : ℝ) - 1) * δ :=
    lemma4_evo_error_to_generator_gap (∑ j : Fin M, Hs j) K
      (hermitian_sum Hs hH) hK (fun _ => Δ + (2 * (M : ℝ) - 1) * δ)
      monotoneOn_const continuousOn_const hevo' 0 le_rfl
  exact lemma3_smallest_eigenvalue_gap_le (∑ j : Fin M, Hs j) K
    (hermitian_sum Hs hH) hK (Δ + (2 * (M : ℝ) - 1) * δ) hgen

end Qatlib.Papers.ReactionMech16.MainResults.Source
