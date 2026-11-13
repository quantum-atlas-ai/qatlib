/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.VarianceScaling.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Non-Faithfulness of the Truncated MMD Loss (Proposition 5)

This module formalizes Proposition 5: expanding the `2k`-body truncated maximum
mean discrepancy (MMD) loss in Pauli-`Z` character sums shows that it depends
only on marginals of order at most `k`, so matching all `≤ k`-body marginals
forces `truncMMDLoss = 0` even when higher-order marginals disagree.

## Main statements

* `agreeOn`, `marg`, `charSum`, `truncMMDLoss`: marginal distributions, Pauli-`Z`
  character expectations, and the `k`-body truncated MMD loss.
* `truncMMDLoss_nonneg`: nonnegativity of `truncMMDLoss` for `0 ≤ pσ ≤ 1`.
* `charSum_eq_of_marginal_eq`: equal `A`-marginals imply equal Pauli-`Z`
  character sums on `A`.
* `proposition5_truncated_loss_zero`: matching marginals up to size `k` implies
  `truncMMDLoss n pσ q p k = 0`.
* `proposition5_not_faithful`: the truncated MMD loss vanishes on distributions
  that match up to order `k` while disagreeing on a higher-order marginal.

## References

* [Rudolph et al., 2024][RudolphEtAl2024], Proposition 5, Eqs. (428)--(436),
  pp. 65--66.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.Trainability23.VarianceScaling.Faithfulness

noncomputable section

/-- `x` and `y` agree on the subset `A` of qubits. -/
def agreeOn {n : ℕ} (A : Finset (Fin n)) (x y : Fin n → Bool) : Prop :=
  ∀ i ∈ A, x i = y i

/-- The marginal `q(y_A)` of a weight function `q` on `n`-bit strings, summing
`q(x)` over all assignments `x` that agree with `y` on `A`. -/
def marg {n : ℕ} (q : (Fin n → Bool) → ℝ) (A : Finset (Fin n)) (y : Fin n → Bool) : ℝ := by
  classical
  exact ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun x => agreeOn A x y), q x

/-- The Pauli-`Z` expectation `⟨Z_A⟩_q = ∑_x q(x) (-1)^{|{i ∈ A : x_i = true}|}`. -/
def charSum {n : ℕ} (q : (Fin n → Bool) → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ x, q x * (-1 : ℝ) ^ (A.filter (fun i => x i = true)).card

/-- The `k`-body truncated MMD loss in Pauli-`Z` character-sum form. -/
def truncMMDLoss (n : ℕ) (pσ : ℝ) (q p : (Fin n → Bool) → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
    (1 - pσ) ^ (n - A.card) * pσ ^ A.card * (charSum q A - charSum p A) ^ 2

/-- Every summand of `truncMMDLoss` is nonnegative when `0 ≤ pσ ≤ 1`. -/
theorem truncMMDLoss_nonneg (n k : ℕ) (pσ : ℝ) (hp0 : 0 ≤ pσ) (hp1 : pσ ≤ 1)
    (q p : (Fin n → Bool) → ℝ) : 0 ≤ truncMMDLoss n pσ q p k := by
  unfold truncMMDLoss
  refine Finset.sum_nonneg fun A _ => ?_
  have h1 : (0 : ℝ) ≤ (1 - pσ) ^ (n - A.card) := pow_nonneg (by linarith) _
  have h2 : (0 : ℝ) ≤ pσ ^ A.card := pow_nonneg hp0 _
  exact mul_nonneg (mul_nonneg h1 h2) (sq_nonneg _)

/-- Restriction of a bitstring `x` to `A` padded by `false` outside `A`. -/
private def restrictTo {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ A then x i else false

/-- Fiberwise expansion of `charSum` in terms of `A`-marginals. -/
private lemma charSum_eq_sum_marg {n : ℕ} (w : (Fin n → Bool) → ℝ) (A : Finset (Fin n)) :
    charSum w A =
      ∑ y ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun y => ∀ i, i ∉ A → y i = false),
        marg w A y * (-1 : ℝ) ^ (A.filter (fun i => y i = true)).card := by
  classical
  unfold charSum
  set T : Finset (Fin n → Bool) :=
    (Finset.univ : Finset (Fin n → Bool)).filter (fun y => ∀ i, i ∉ A → y i = false)
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin n → Bool)), restrictTo A x ∈ T := by
    intro x _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => ?_⟩
    simp [restrictTo, hi]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy_out : ∀ i, i ∉ A → y i = false := (Finset.mem_filter.mp hy).2
  have hfib :
      (Finset.univ : Finset (Fin n → Bool)).filter (fun x => restrictTo A x = y) =
        (Finset.univ : Finset (Fin n → Bool)).filter (fun x => agreeOn A x y) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hxy i hi
      have h1 := congrFun hxy i
      simpa [restrictTo, hi] using h1
    · intro hagree
      funext i
      by_cases hi : i ∈ A
      · simp [restrictTo, hi, hagree i hi]
      · simp [restrictTo, hi, hy_out i hi]
  have hterm :
      ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun x => restrictTo A x = y),
          w x * (-1 : ℝ) ^ (A.filter (fun i => x i = true)).card =
        ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun x => agreeOn A x y),
          w x * (-1 : ℝ) ^ (A.filter (fun i => y i = true)).card := by
    rw [hfib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hagree : agreeOn A x y := (Finset.mem_filter.mp hx).2
    have hfilt : A.filter (fun i => x i = true) = A.filter (fun i => y i = true) :=
      Finset.filter_congr fun i hi => by rw [hagree i hi]
    rw [hfilt]
  rw [hterm, ← Finset.sum_mul]
  rfl

/-- Equal `A`-marginals imply equal Pauli-`Z` character expectations on `A`. -/
theorem charSum_eq_of_marginal_eq (n : ℕ) (q p : (Fin n → Bool) → ℝ) (A : Finset (Fin n))
    (hm : ∀ y, marg q A y = marg p A y) : charSum q A = charSum p A := by
  rw [charSum_eq_sum_marg, charSum_eq_sum_marg]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hm y]

/-- **Proposition 5 (vanishing loss)**: if `q` and `p` agree on all marginals of
order at most `k`, then `truncMMDLoss n pσ q p k = 0`. -/
theorem proposition5_truncated_loss_zero (n k : ℕ) (pσ : ℝ) (q p : (Fin n → Bool) → ℝ)
    (hm : ∀ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
      ∀ y, marg q A y = marg p A y) :
    truncMMDLoss n pσ q p k = 0 := by
  unfold truncMMDLoss
  refine Finset.sum_eq_zero fun A hA => ?_
  rw [charSum_eq_of_marginal_eq n q p A (hm A hA)]
  ring

/-- **Proposition 5 (non-faithfulness)**: if `q` and `p` agree on all marginals of
order at most `k` while disagreeing on some higher-order marginal `|B| > k`, the
truncated MMD loss still vanishes. -/
theorem proposition5_not_faithful (n k : ℕ) (pσ : ℝ) (q p : (Fin n → Bool) → ℝ)
    (hm : ∀ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
      ∀ y, marg q A y = marg p A y)
    (hne : ∃ B : Finset (Fin n), k < B.card ∧ ∃ y, marg q B y ≠ marg p B y) :
    truncMMDLoss n pσ q p k = 0 ∧
      ∃ B : Finset (Fin n), k < B.card ∧ ∃ y, marg q B y ≠ marg p B y :=
  ⟨proposition5_truncated_loss_zero n k pσ q p hm, hne⟩

end

end Qatlib.Papers.Trainability23.VarianceScaling.Faithfulness
