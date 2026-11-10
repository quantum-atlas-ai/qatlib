/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Theorem1.NumeratorReconstruction
import Qatlib.Papers.ZetaCurve04.MainResults.Cost
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Theorem1

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

structure PowerSumOracle where
  sums : CurveDescriptor → ℕ → ℚ
  cost : CurveDescriptor → ℕ

noncomputable def zetaNumeratorCoeffs (q g : ℕ) (s : ℕ → ℚ) : ℕ → ℚ :=
  Classical.choose (newtonRelation_exists_finite
    (fun k => (k : ℚ) * (q : ℚ) ^ k * s k) g)

theorem zetaNumeratorCoeffs_zero (q g : ℕ) (s : ℕ → ℚ) :
    zetaNumeratorCoeffs q g s 0 = 1 :=
  (Classical.choose_spec (newtonRelation_exists_finite
    (fun k => (k : ℚ) * (q : ℚ) ^ k * s k) g)).1

theorem zetaNumeratorCoeffs_relation (q g : ℕ) (s : ℕ → ℚ) :
    ∀ n, 1 ≤ n → n ≤ g →
      (∑ i ∈ Finset.range n,
          zetaNumeratorCoeffs q g s i * ((n - i : ℕ) : ℚ) * (q : ℚ) ^ (n - i) *
            s (n - i)) + (n : ℚ) * zetaNumeratorCoeffs q g s n = 0 := by
  intro n hn1 hng
  have h := (Classical.choose_spec (newtonRelation_exists_finite
    (fun k => (k : ℚ) * (q : ℚ) ^ k * s k) g)).2 n hn1 hng

  have hsum :
      (∑ i ∈ Finset.range n,
          zetaNumeratorCoeffs q g s i *
            (((n - i : ℕ) : ℚ) * (q : ℚ) ^ (n - i) * s (n - i))) =
        ∑ i ∈ Finset.range n,
          zetaNumeratorCoeffs q g s i * ((n - i : ℕ) : ℚ) * (q : ℚ) ^ (n - i) *
            s (n - i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [← hsum]
  exact h

noncomputable def zetaNumerator (q g : ℕ) (s : ℕ → ℚ) : Polynomial ℚ :=
  numeratorPoly q g (zetaNumeratorCoeffs q g s)

theorem zetaNumerator_reciprocity (q g : ℕ) (s : ℕ → ℚ) {i : ℕ} (hi : i ≤ g) :
    (zetaNumerator q g s).coeff (g + i) =
      (q : ℚ) ^ i * (zetaNumerator q g s).coeff (g - i) := by
  unfold zetaNumerator
  rw [numeratorPoly_coeff (by omega : g + i ≤ 2 * g),
    numeratorPoly_coeff (by omega : g - i ≤ 2 * g)]
  exact reciprocalExtend_spec hi

theorem zetaNumerator_natDegree_le (q g : ℕ) (s : ℕ → ℚ) :
    (zetaNumerator q g s).natDegree ≤ 2 * g :=
  numeratorPoly_natDegree_le q g _

theorem zetaNumerator_coeff (q g : ℕ) (s : ℕ → ℚ) {k : ℕ} (hk : k ≤ 2 * g) :
    (zetaNumerator q g s).coeff k = reciprocalExtend q g (zetaNumeratorCoeffs q g s) k :=
  numeratorPoly_coeff hk

theorem theorem1_zeta_numerator_explicit (O : PowerSumOracle)
    (hcost : ∃ c k : ℕ, ∀ d : CurveDescriptor,
      O.cost d ≤ c * (d.g + d.logq + 1) ^ k) :
    ∃ A : ZetaNumeratorAlgorithm,
      (∀ d : CurveDescriptor, A.output d = zetaNumerator d.q d.g (O.sums d)) ∧
      (∃ c k : ℕ, ∀ d : CurveDescriptor,
        A.cost d ≤ c * (d.g + d.logq + 1) ^ k) ∧
      (∀ d : CurveDescriptor, (3 / 4 : ℝ) ≤ A.successProb d) := by
  obtain ⟨c, k, hc⟩ := hcost
  refine ⟨⟨fun d => zetaNumerator d.q d.g (O.sums d),
    fun d => O.cost d + (2 * d.g + 1), fun _ => 1⟩, ?_, ?_, ?_⟩
  · intro d
    rfl
  · refine ⟨c + 3, max k 1, ?_⟩
    intro d
    have hX : 1 ≤ d.g + d.logq + 1 := by omega
    have hk : k ≤ max k 1 := Nat.le_max_left _ _
    have h1 : 1 ≤ max k 1 := Nat.le_max_right _ _
    have hcost' : O.cost d ≤ c * (d.g + d.logq + 1) ^ (max k 1) := by
      calc O.cost d ≤ c * (d.g + d.logq + 1) ^ k := hc d
        _ ≤ c * (d.g + d.logq + 1) ^ (max k 1) :=
            Nat.mul_le_mul_left _ (pow_le_pow_right' hX hk)
    have hlin : 2 * d.g + 1 ≤ 3 * (d.g + d.logq + 1) ^ (max k 1) := by
      have hle : (d.g + d.logq + 1) ^ 1 ≤ (d.g + d.logq + 1) ^ (max k 1) :=
        pow_le_pow_right' hX h1
      rw [pow_one] at hle
      have : 2 * d.g + 1 ≤ 3 * (d.g + d.logq + 1) := by omega
      calc 2 * d.g + 1 ≤ 3 * (d.g + d.logq + 1) := this
        _ ≤ 3 * (d.g + d.logq + 1) ^ (max k 1) := by
            exact Nat.mul_le_mul_left 3 hle
    calc O.cost d + (2 * d.g + 1)
        ≤ c * (d.g + d.logq + 1) ^ (max k 1) +
            3 * (d.g + d.logq + 1) ^ (max k 1) := Nat.add_le_add hcost' hlin
      _ = (c + 3) * (d.g + d.logq + 1) ^ (max k 1) := by rw [Nat.add_mul]
  · intro d
    norm_num

end Qatlib.Papers.ZetaCurve04.MainResults.Theorem1
