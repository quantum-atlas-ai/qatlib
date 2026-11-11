/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenHidShift05.MainResults.MatrixSumMoments
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Exact moments and the abundance argument for matrix-sum fibers (source Lemma 2)

Fixed source: A. M. Childs and W. van Dam, *Quantum algorithm for a generalized
hidden shift problem*, arXiv:quant-ph/0507190v1, Appendix (Eqs. 40–53).

For uniformly random `x ∈ (ZMod N)^k` and `w ∈ ZMod N`, `solCount N M k x w` is
the source quantity `η_w^x`, the number of box points `b ∈ {0,…,M-1}^k` solving
`b · x = w mod N`.

This file formalises the appendix's moment computation and the two
probabilistic inequalities it uses:

* the exact second moment `E[η²]` separated into its diagonal contribution
  `M^k N^k` and an off-diagonal contribution bounded below by
  `M^k (M^k - 1) N^(k-1)` (`sum_sq_split`, `diag_sum_eq`, `offDiag_sum_ge`,
  `totalSq_ge`, `secondMoment_ge`);
* the general finite-uniform-space counting inequality behind the
  Alon–Spencer zero-probability bound (`card_pos_mul_sq_ge`) and Chebyshev's
  inequality (`card_dev_mul_sq_le`);
* the partition of the good instances `{1 ≤ η ≤ 4}` as the complement of the
  zero and large instances (`card_good_eq`);
* the numeric endpoint `1 - 3π²/32 > 0.0747` (`constant_gt`).

The appendix additionally bounds `Σ_{b≠c} gcd(b-c, N)` by a divisor sum of size
`π²/6 + o(1)` and then assembles the bounds into `Pr(1 ≤ η ≤ 4) ≥ 1 - 3π²/32`.
Those two final steps are not formalised here.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.GenHidShift05.FiberStats

open Qatlib.Papers.GenHidShift05.MainResults

variable {k M N : ℕ}

/-! ### The instance space and its moments -/

/-- The total number of matrix-sum solutions over all instances `(x, w)`. -/
def totalSolutions (N M k : ℕ) [NeZero N] : ℕ :=
  ∑ x : Fin k → ZMod N, ∑ w : ZMod N, solCount N M k x w

/-- The total squared matrix-sum solution count over all instances `(x, w)`. -/
def totalSqSolutions (N M k : ℕ) [NeZero N] : ℕ :=
  ∑ x : Fin k → ZMod N, ∑ w : ZMod N, solCount N M k x w ^ 2

/-- The number `N^(k+1)` of matrix-sum instances `(x, w)`. -/
def instanceCard (N k : ℕ) : ℕ := N ^ k * N

/-- The source mean `μ = E[η]` over uniformly random instances. -/
def mean (N M k : ℕ) [NeZero N] : ℝ :=
  (totalSolutions N M k : ℝ) / (instanceCard N k : ℝ)

/-- The source second moment `E[η²]` over uniformly random instances. -/
def secondMoment (N M k : ℕ) [NeZero N] : ℝ :=
  (totalSqSolutions N M k : ℝ) / (instanceCard N k : ℝ)

/-- The source variance `σ² = E[η²] - μ²`. -/
def variance (N M k : ℕ) [NeZero N] : ℝ := secondMoment N M k - (mean N M k) ^ 2

/-- The total solution count is `N^k · M^k`, the normalization behind Eq. (19). -/
theorem totalSolutions_eq [NeZero N] : totalSolutions N M k = N ^ k * M ^ k := by
  unfold totalSolutions
  exact sum_solCount_eq_card (N := N) (M := M) (k := k)

/-- The source mean is `μ = M^k / N`. -/
theorem mean_eq [NeZero N] : mean N M k = (M : ℝ) ^ k / (N : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold mean
  rw [totalSolutions_eq, instanceCard]
  push_cast
  field_simp

/-- The mean is nonnegative. -/
theorem mean_nonneg [NeZero N] : 0 ≤ mean N M k := by
  rw [mean_eq]
  positivity

/-! ### The diagonal/off-diagonal splitting of the second moment -/

/-- The difference vector `b - c` of a box pair, read in `ZMod N`. -/
def pairDiff (N M k : ℕ) (p : (Fin k → Fin M) × (Fin k → Fin M)) : Fin k → ZMod N :=
  fun i => ((p.1 i).val : ZMod N) - ((p.2 i).val : ZMod N)

/-- The diagonal box pairs `b = c`. -/
def diagPairs (M k : ℕ) : Finset ((Fin k → Fin M) × (Fin k → Fin M)) :=
  univ.filter fun p => p.1 = p.2

/-- The off-diagonal box pairs `b ≠ c`. -/
def offDiagPairs (M k : ℕ) : Finset ((Fin k → Fin M) × (Fin k → Fin M)) :=
  univ.filter fun p => p.1 ≠ p.2

/-- The zero difference vector has `gcd(0, …, 0, N) = N`. -/
theorem matrixGcd_zero (N k : ℕ) : matrixGcd N (fun _ : Fin k => (0 : ZMod N)) = N := by
  unfold matrixGcd
  have h : (univ : Finset (Fin k)).gcd (fun _ => (0 : ZMod N).val) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun _ _ => ZMod.val_zero)
  rw [h, Nat.gcd_zero_right]

/-- Eq. (45) cast to the reals: the second moment sum is a sum over box pairs of
`N^(k-1) · gcd(b - c, N)`. -/
theorem sum_sq_cast [NeZero N] (hk : 0 < k) :
    (totalSqSolutions N M k : ℝ)
      = ∑ p : (Fin k → Fin M) × (Fin k → Fin M),
          (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ) := by
  unfold totalSqSolutions
  rw [sum_sq_solCount_eq_gcd (M := M) hk]
  push_cast
  rfl

/-- The second moment sum splits into its diagonal and off-diagonal parts. -/
theorem sum_sq_split [NeZero N] (hk : 0 < k) :
    (totalSqSolutions N M k : ℝ)
      = (∑ p ∈ diagPairs M k,
            (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ))
        + (∑ p ∈ offDiagPairs M k,
            (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ)) := by
  rw [sum_sq_cast (M := M) hk]
  have h := Finset.sum_filter_add_sum_filter_not
    (s := (univ : Finset ((Fin k → Fin M) × (Fin k → Fin M))))
    (p := fun p => p.1 = p.2)
    (f := fun p => (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ))
  simpa [diagPairs, offDiagPairs] using h.symm

/-- The number of diagonal box pairs is `M^k`. -/
theorem card_diagPairs (M k : ℕ) : (diagPairs M k).card = M ^ k := by
  classical
  rw [diagPairs, Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ b : Fin k → Fin M,
      (∑ c : Fin k → Fin M, if b = c then (1 : ℕ) else 0) = 1 := by
    intro b
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hcb
      rw [if_neg (fun h => hcb h.symm)]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  rw [Finset.sum_congr rfl (fun b _ => hinner b), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul, mul_one]

/-- The exact diagonal contribution: `M^k · N^k`. -/
theorem diag_sum_eq [NeZero N] (hk : 0 < k) :
    (∑ p ∈ diagPairs M k,
        (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ))
      = (M : ℝ) ^ k * (N : ℝ) ^ k := by
  classical
  have hterm : ∀ p ∈ diagPairs M k,
      (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ) = (N : ℝ) ^ k := by
    intro p hp
    have hpd : p.1 = p.2 := by
      simp only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hp
    have hdiff : pairDiff N M k p = fun _ => (0 : ZMod N) := by
      funext i
      simp [pairDiff, hpd]
    rw [hdiff, matrixGcd_zero]
    calc (N : ℝ) ^ (k - 1) * (N : ℝ) = (N : ℝ) ^ (k - 1) * (N : ℝ) ^ 1 := by rw [pow_one]
      _ = (N : ℝ) ^ ((k - 1) + 1) := by rw [pow_add]
      _ = (N : ℝ) ^ k := by rw [show (k - 1) + 1 = k by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_diagPairs, nsmul_eq_mul]
  push_cast
  ring

/-- The number of off-diagonal box pairs is `M^k (M^k - 1)`. -/
theorem card_offDiagPairs (M k : ℕ) :
    (offDiagPairs M k).card = M ^ k * (M ^ k - 1) := by
  classical
  have htot : (diagPairs M k).card + (offDiagPairs M k).card
      = Fintype.card ((Fin k → Fin M) × (Fin k → Fin M)) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset ((Fin k → Fin M) × (Fin k → Fin M))))
      (p := fun p => p.1 = p.2)
    simpa [diagPairs, offDiagPairs] using h
  have htot' : M ^ k + (offDiagPairs M k).card = M ^ k * M ^ k := by
    simpa [card_diagPairs, Fintype.card_prod, Fintype.card_fun] using htot
  have hoff : (offDiagPairs M k).card = M ^ k * M ^ k - M ^ k := by
    rw [← htot', Nat.add_sub_cancel_left]
  rw [hoff]
  rcases Nat.eq_zero_or_pos (M ^ k) with h0 | hpos
  · simp [h0]
  · rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Every off-diagonal term is at least `N^(k-1)`, because the gcd of a
difference vector with `N` is positive. -/
theorem offDiag_sum_ge [NeZero N] (hM : 1 ≤ M) (_hk : 0 < k) :
    ((M : ℝ) ^ k * ((M : ℝ) ^ k - 1)) * (N : ℝ) ^ (k - 1)
      ≤ ∑ p ∈ offDiagPairs M k,
          (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ) := by
  classical
  have hterm : ∀ p ∈ offDiagPairs M k,
      (N : ℝ) ^ (k - 1)
        ≤ (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ) := by
    intro p _
    have h1 : (1 : ℝ) ≤ (matrixGcd N (pairDiff N M k p) : ℝ) := by
      have hpos : 0 < matrixGcd N (pairDiff N M k p) := matrixGcd_pos _
      exact_mod_cast Nat.succ_le_of_lt hpos
    calc (N : ℝ) ^ (k - 1) = (N : ℝ) ^ (k - 1) * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
  have hcard : ((offDiagPairs M k).card : ℝ)
      = (M : ℝ) ^ k * ((M : ℝ) ^ k - 1) := by
    rw [card_offDiagPairs, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (Nat.one_le_pow k M hM), Nat.cast_one, Nat.cast_pow]
  calc ((M : ℝ) ^ k * ((M : ℝ) ^ k - 1)) * (N : ℝ) ^ (k - 1)
      = ((offDiagPairs M k).card : ℝ) * (N : ℝ) ^ (k - 1) := by rw [hcard]
    _ = ∑ _p ∈ offDiagPairs M k, (N : ℝ) ^ (k - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ offDiagPairs M k,
          (N : ℝ) ^ (k - 1) * (matrixGcd N (pairDiff N M k p) : ℝ) :=
      Finset.sum_le_sum hterm

/-- The second moment sum is at least `M^k N^k + M^k(M^k-1) N^(k-1)`. -/
theorem totalSq_ge [NeZero N] (hM : 1 ≤ M) (hk : 0 < k) :
    (M : ℝ) ^ k * (N : ℝ) ^ k
        + ((M : ℝ) ^ k * ((M : ℝ) ^ k - 1)) * (N : ℝ) ^ (k - 1)
      ≤ (totalSqSolutions N M k : ℝ) := by
  rw [sum_sq_split (M := M) hk, diag_sum_eq (M := M) hk]
  linarith [offDiag_sum_ge (M := M) (N := N) hM hk]

/-- Eq. (53) at the level of the second moment:
`E[η²] ≥ μ + M^k(M^k-1)/N²`. -/
theorem secondMoment_ge [NeZero N] (hM : 1 ≤ M) (hk : 0 < k) :
    mean N M k + ((M : ℝ) ^ k * ((M : ℝ) ^ k - 1)) / (N : ℝ) ^ 2
      ≤ secondMoment N M k := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hcard : (instanceCard N k : ℝ) = (N : ℝ) ^ k * (N : ℝ) := by
    unfold instanceCard
    push_cast
    rfl
  have htot := totalSq_ge (M := M) (N := N) hM hk
  unfold secondMoment
  rw [hcard]
  have hpos : (0 : ℝ) < (N : ℝ) ^ k * (N : ℝ) := by positivity
  rw [mean_eq, le_div_iff₀ hpos]
  have hB : ((M : ℝ) ^ k * ((M : ℝ) ^ k - 1)) / (N : ℝ) ^ 2 * ((N : ℝ) ^ k * (N : ℝ))
      = ((M : ℝ) ^ k * ((M : ℝ) ^ k - 1)) * (N : ℝ) ^ (k - 1) := by
    rw [show (N : ℝ) ^ k = (N : ℝ) ^ (k - 1) * (N : ℝ) ^ 1 by
      rw [← pow_add]; congr 1; omega, pow_one]
    field_simp
  have hMk : (M : ℝ) ^ k / (N : ℝ) * ((N : ℝ) ^ k * (N : ℝ))
      = (M : ℝ) ^ k * (N : ℝ) ^ k := by
    field_simp
  rw [add_mul, hMk, hB]
  exact htot

/-! ### Finite-uniform-space counting inequalities -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cauchy–Schwarz in counting form: the square of the total of a nonnegative
integer statistic is at most the number of nonzero instances times the second
moment. -/
theorem card_pos_mul_sq_ge (f : ι → ℕ) :
    (∑ i, (f i : ℝ)) ^ 2
      ≤ ((Fintype.card ι - Fintype.card {i : ι // f i = 0} : ℕ) : ℝ)
          * (∑ i, (f i : ℝ) ^ 2) := by
  classical
  set A : Finset ι := univ.filter (fun i => f i ≠ 0) with hA
  have hSA : (∑ i ∈ A, (f i : ℝ)) = ∑ i, (f i : ℝ) := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases h : f i ≠ 0
    · simp [h]
    · have hz : f i = 0 := not_not.mp h
      simp [hz]
  have hQA : (∑ i ∈ A, (f i : ℝ) ^ 2) = ∑ i, (f i : ℝ) ^ 2 := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases h : f i ≠ 0
    · simp [h]
    · have hz : f i = 0 := not_not.mp h
      simp [hz]
  have hcardA : (∑ i ∈ A, (1 : ℝ) ^ 2)
      = ((Fintype.card ι - Fintype.card {i : ι // f i = 0} : ℕ) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, one_pow, mul_one]
    congr 1
    have hAcard : A.card = Fintype.card {i : ι // f i ≠ 0} := by
      rw [hA]
      exact (Fintype.card_subtype (fun i : ι => f i ≠ 0)).symm
    rw [hAcard, Fintype.card_subtype_compl (fun i : ι => f i = 0)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq A (fun i => (f i : ℝ)) (fun _ => (1 : ℝ))
  have h1 : (∑ i ∈ A, (f i : ℝ) * 1) = ∑ i, (f i : ℝ) := by
    simpa using hSA
  rw [h1, hQA, hcardA] at hcs
  simpa [mul_comm] using hcs

/-- Chebyshev's inequality on a finite uniform space. -/
theorem card_dev_mul_sq_le (f : ι → ℝ) (mu D : ℝ) (hD : 0 < D) :
    (Fintype.card {i : ι // D ≤ |f i - mu|} : ℝ) * D ^ 2
      ≤ ∑ i, (f i - mu) ^ 2 := by
  classical
  set A : Finset ι := univ.filter (fun i => D ≤ |f i - mu|) with hA
  have hAcard : A.card = Fintype.card {i : ι // D ≤ |f i - mu|} := by
    rw [hA]
    exact (Fintype.card_subtype (fun i : ι => D ≤ |f i - mu|)).symm
  have h1 : (∑ i ∈ A, D ^ 2) ≤ ∑ i ∈ A, (f i - mu) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have h : D ≤ |f i - mu| := by
      rw [hA] at hi
      simpa using hi
    have hsq : D ^ 2 ≤ |f i - mu| ^ 2 := pow_le_pow_left₀ hD.le h 2
    simpa [sq_abs] using hsq
  have hsumconst : (∑ i ∈ A, D ^ 2)
      = (Fintype.card {i : ι // D ≤ |f i - mu|} : ℝ) * D ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hAcard]
  rw [← hsumconst]
  exact h1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => sq_nonneg _))

/-- The good instances are exactly the complement of the zero and large
instances, as a cardinality identity. -/
theorem card_good_eq (f : ι → ℕ) :
    Fintype.card {i : ι // 1 ≤ f i ∧ f i ≤ 4}
      = Fintype.card ι - Fintype.card {i : ι // f i = 0}
          - Fintype.card {i : ι // 5 ≤ f i} := by
  classical
  have hg : (univ.filter (fun i : ι => 1 ≤ f i ∧ f i ≤ 4))
      = (univ.filter (fun i : ι => f i = 0) ∪ univ.filter (fun i : ι => 5 ≤ f i))ᶜ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_union, not_or]
    omega
  have hdisj : Disjoint (univ.filter (fun i : ι => f i = 0))
      (univ.filter (fun i : ι => 5 ≤ f i)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    omega
  rw [Fintype.card_subtype (fun i : ι => 1 ≤ f i ∧ f i ≤ 4), hg, Finset.card_compl,
    Finset.card_union_of_disjoint hdisj,
    ← Fintype.card_subtype (fun i : ι => f i = 0),
    ← Fintype.card_subtype (fun i : ι => 5 ≤ f i)]
  omega

end Generic

/-- The source's numeric endpoint: `1 - 3π²/32 > 0.0747`. -/
theorem constant_gt : (0.0747 : ℝ) < 1 - 3 * Real.pi ^ 2 / 32 := by
  have hπ : Real.pi < 3.1416 := Real.pi_lt_d4
  have hπ2 : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  nlinarith [hπ2]

end Qatlib.Papers.GenHidShift05.FiberStats
