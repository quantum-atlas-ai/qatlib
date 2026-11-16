/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic
public import Qatlib.Papers.Trainability23.VarianceScaling.Faithfulness.SourceFaithfulness

@[expose] public section


/-!
# Marginals and truncated MMD faithfulness

The statements concern the explicit finite Fourier-sum loss. Equality of
low-order marginals kills those Fourier coefficients; a higher-order
disagreement remains undetected. A density-operator representation bridge
is not asserted here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.Trainability23.VarianceScaling.Faithfulness

open Qatlib.Papers.Trainability23.VarianceScaling.Faithfulness

/-

/-- `x` and `y` agree on the subset `A` of qubits. -/
def agreeOn {n : ℕ} (A : Finset (Fin n)) (x y : Fin n → Bool) : Prop :=
  ∀ i ∈ A, x i = y i

/-- The marginal `q(x_A)` of a distribution `q` on bitstrings, evaluated on a full assignment `y`
whose restriction to `A` is the marginal argument: `q(x_A) = Σ_{x : x|_A = y|_A} q(x)`
(cf. Eq. (421)). -/
def marg {n : ℕ} (q : (Fin n → Bool) → ℝ) (A : Finset (Fin n)) (y : Fin n → Bool) : ℝ := by
  classical
  exact ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun x => agreeOn A x y), q x

/-- The Pauli-`Z` expectation `⟨Z_A⟩_q = Σ_{x} q(x)(−1)^{Σ_{i∈A} x_i}` (Eqs. (435)–(436)), written
for a general weight function `q` on bitstrings (so that it applies to both `q_θ` and `p̃`). -/
def charSum {n : ℕ} (q : (Fin n → Bool) → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ x, q x * (-1 : ℝ) ^ (A.filter (fun i => x i = true)).card

/-- The truncated MMD loss in the expanded form of Eq. (433). -/
def truncMMDLoss (n : ℕ) (pσ : ℝ) (q p : (Fin n → Bool) → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
    (1 - pσ) ^ (n - A.card) * pσ ^ A.card * (charSum q A - charSum p A) ^ 2

 -/
/-- **Eq. (433), nonnegativity.**  Every summand of the truncated loss is a nonnegative weight
times a square, so the truncated MMD loss is nonnegative — the side-condition behind "the
distribution `q_θ` *minimises* the truncated MMD loss". -/
theorem trunc_nonneg (n k : ℕ) (pσ : ℝ) (hp0 : 0 ≤ pσ) (hp1 : pσ ≤ 1)
    (q p : (Fin n → Bool) → ℝ) : 0 ≤ truncMMDLoss n pσ q p k := by
  unfold truncMMDLoss
  refine Finset.sum_nonneg fun A _ => ?_
  have h1 : (0 : ℝ) ≤ (1 - pσ) ^ (n - A.card) := pow_nonneg (by linarith) _
  have h2 : (0 : ℝ) ≤ pσ ^ A.card := pow_nonneg hp0 _
  exact mul_nonneg (mul_nonneg h1 h2) (sq_nonneg _)

/-- Equality of the marginal on a subset implies equality of its character coefficient. -/
theorem char_of_marg (n : ℕ) (q p : (Fin n → Bool) → ℝ) (A : Finset (Fin n))
    (hm : ∀ y, marg q A y = marg p A y) : charSum q A = charSum p A := by
  classical
  let project : (Fin n → Bool) → (A → Bool) := fun x i => x i.val
  let extend : (A → Bool) → (Fin n → Bool) :=
    fun y i => if hi : i ∈ A then y ⟨i, hi⟩ else false
  let chi : (Fin n → Bool) → ℝ :=
    fun x => (-1 : ℝ) ^ (A.filter (fun i => x i = true)).card
  have hchar : ∀ x y, agreeOn A x y → chi x = chi y := by
    intro x y hxy
    dsimp [chi]
    congr 1
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right fun hi => iff_of_eq (congrArg (fun b => b = true) (hxy i hi))
  have hfilter (y : A → Bool) :
      (Finset.univ.filter fun x : Fin n → Bool => project x = y) =
        Finset.univ.filter (fun x => agreeOn A x (extend y)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hxy i hi
      have he := congrFun hxy ⟨i, hi⟩
      simpa [project, extend, hi] using he
    · intro hxy
      funext i
      simpa [project, extend, i.property] using hxy i.val i.property
  have hgroup (w : (Fin n → Bool) → ℝ) :
      charSum w A = ∑ y : A → Bool, marg w A (extend y) * chi (extend y) := by
    calc
      charSum w A =
          ∑ y : A → Bool, ∑ x ∈ Finset.univ.filter (fun x => project x = y),
            w x * chi x :=
        (Finset.sum_fiberwise Finset.univ project (fun x => w x * chi x)).symm
      _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hfilter]
        change (∑ x ∈ Finset.univ.filter (fun x => agreeOn A x (extend y)),
          w x * chi x) =
          (∑ x ∈ Finset.univ.filter (fun x => agreeOn A x (extend y)), w x) * chi (extend y)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hchar x (extend y) (Finset.mem_filter.mp hx).2]
  rw [hgroup q, hgroup p]
  exact Finset.sum_congr rfl fun y _ => by rw [hm (extend y)]

/-- **Proposition 5, Eq. (430) ⟹ Eq. (431).**  If `q` and `p` agree on all marginals of order at
most `k`, then the truncated MMD loss vanishes: every bracket in Eq. (433) is zero. -/
theorem truncated_zero (n k : ℕ) (pσ : ℝ) (q p : (Fin n → Bool) → ℝ)
    (hm : ∀ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
      ∀ y, marg q A y = marg p A y) :
    truncMMDLoss n pσ q p k = 0 := by
  unfold truncMMDLoss
  refine Finset.sum_eq_zero fun A hA => ?_
  rw [char_of_marg n q p A (hm A hA)]
  ring

/-- **Proposition 5, Eq. (432): the truncated loss is not faithful.**  If in addition some
higher-order marginal (`|B| > k`) of `q` disagrees with that of `p`, the truncated loss is still
zero — so minimising it does not detect the disagreement. -/
theorem unfaithful (n k : ℕ) (pσ : ℝ) (q p : (Fin n → Bool) → ℝ)
    (hm : ∀ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
      ∀ y, marg q A y = marg p A y)
    (hne : ∃ B : Finset (Fin n), k < B.card ∧ ∃ y, marg q B y ≠ marg p B y) :
    truncMMDLoss n pσ q p k = 0 ∧
      ∃ B : Finset (Fin n), k < B.card ∧ ∃ y, marg q B y ≠ marg p B y :=
  ⟨truncated_zero n k pσ q p hm, hne⟩

end Qatlib.Papers.Trainability23.VarianceScaling.Faithfulness
