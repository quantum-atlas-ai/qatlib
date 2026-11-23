/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.MatrixAlgebra.TensorDiff

@[expose] public section

/-!
# Energy change under the source sign readout

Section 2.3 of Goh and Müller (arXiv:2609.35131v1) returns the signs of the
final z-spin coordinates. Compare the continuous and rounded energies by
telescoping each ordered monomial, including monomials with repeated sites.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.MainResults

/-- Rounding a spin to a binary sign, with the zero tie assigned to `+1`. -/
noncomputable def roundedSpin (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- A spin inside the unit interval changes by its defect from unit magnitude. -/
theorem abs_sub_roundedSpin {x : ℝ} (hx : |x| ≤ 1) :
    |x - roundedSpin x| = 1 - |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    rw [roundedSpin, ite_eq_left h, abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  · by_cases hzero : x = 0
    · simp [hzero, roundedSpin]
    · have hneg : x < 0 := lt_of_le_of_ne h hzero
      rw [abs_of_nonpos h] at hx ⊢
      rw [roundedSpin, ite_eq_right (not_le.mpr hneg), abs_of_nonneg (by linarith)]
      ring

private theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      have hprod : |∏ j ∈ s, b j| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun j _ => abs_nonneg (b j)) (fun j _ => hb j)
      calc
        |a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j)| =
            |a i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j)) +
              (a i - b i) * (∏ j ∈ s, b j)| := by congr 1; ring
        _ ≤ |a i - b i| + ∑ j ∈ s, |a j - b j| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, add_comm |a i - b i|]
          exact add_le_add ((mul_le_of_le_one_left (abs_nonneg _) (ha i)).trans ih)
            (mul_le_of_le_one_right (abs_nonneg _) hprod)

/-- The energy loss in the final sign projection is bounded by the coefficient-weighted sum of
the rounding defects across the slots of each ordered monomial. -/
theorem tensorEnergy_sign_slot_le {q N : ℕ} (A : Tensor q N) (v : Fin N → ℝ)
    (hv : ∀ i, |v i| ≤ 1) :
    |tensorEnergy A v - tensorEnergy A (fun i => roundedSpin (v i))| ≤
      ∑ k, |A k| * ∑ j : Fin q, (1 - |v (k j)|) := by
  unfold tensorEnergy
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← mul_sub, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hunit : ∀ i, |roundedSpin (v i)| ≤ 1 := by
    intro i
    unfold roundedSpin
    split <;> simp
  simpa only [abs_sub_roundedSpin (hv _)] using
    abs_prod_sub_prod_le Finset.univ (fun j => v (k j)) (fun j => roundedSpin (v (k j)))
      (fun j => hv (k j)) (fun j => hunit (k j))

/-- The final sign projection changes the energy by at most the product of the tensor order,
the entrywise absolute coefficient sum, and the total spin magnitude defect. -/
theorem tensorEnergy_sign_sub_le {q N : ℕ} (A : Tensor q N) (v : Fin N → ℝ)
    (hv : ∀ i, |v i| ≤ 1) :
    |tensorEnergy A v - tensorEnergy A (fun i => roundedSpin (v i))| ≤
      (q : ℝ) * (∑ k, |A k|) * (∑ i, (1 - |v i|)) := by
  refine (tensorEnergy_sign_slot_le A v hv).trans ?_
  have hsite (i : Fin N) : 1 - |v i| ≤ ∑ l, (1 - |v l|) :=
    Finset.single_le_sum (fun l _ => sub_nonneg.mpr (hv l)) (Finset.mem_univ i)
  calc
    (∑ k, |A k| * ∑ j : Fin q, (1 - |v (k j)|)) ≤
        ∑ k, |A k| * ∑ _j : Fin q, ∑ i, (1 - |v i|) :=
      Finset.sum_le_sum fun _ _ =>
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => hsite _) (abs_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.sum_mul]
      ring

end Qatlib.Papers.OverlapGapGoh26.MainResults
