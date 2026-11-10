/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.PairedCategoricalLowerBound
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.PairedCategoricalRisk
open FiniteInformationDivergence FiniteAssouad PairedCategoricalLowerBound
open scoped BigOperators Classical
noncomputable section

def decode {m : ℕ} (estimate : Fin m × Bool → ℝ) : Cube m :=
  fun i => decide (estimate (i,false) ≤ estimate (i,true))

private theorem pair_loss (hi lo x y : ℝ) (bit : Bool) :
    (hi-lo)*(if decide (x≤y) ≠ bit then (1 : ℝ) else 0) ≤
      |x-(if bit then lo else hi)|+|y-(if bit then hi else lo)| := by
  cases bit <;> by_cases h : x≤y <;> simp [h]
  all_goals linarith [le_abs_self (x-hi), neg_le_abs (x-hi), le_abs_self (x-lo),
    neg_le_abs (x-lo), le_abs_self (y-hi), neg_le_abs (y-hi),
    le_abs_self (y-lo), neg_le_abs (y-lo), abs_nonneg (x-hi), abs_nonneg (y-hi),
    abs_nonneg (x-lo), abs_nonneg (y-lo)]

theorem coordinate_loss (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (theta : Cube m) (estimate : Fin m × Bool → ℝ) (i : Fin m) :
    a/(m : ℝ)*(if decode estimate i ≠ theta i then 1 else 0) ≤
      ∑ b : Bool, |estimate (i,b)-(pairedLaw m hm a ha ha1 theta).prob (i,b)| := by
  have h := pair_loss ((1+a)/(2*(m : ℝ))) ((1-a)/(2*(m : ℝ)))
    (estimate (i,false)) (estimate (i,true)) (theta i)
  have hg : (1+a)/(2*(m : ℝ))-(1-a)/(2*(m : ℝ)) = a/(m : ℝ) := by ring
  rw [hg] at h
  dsimp only [pairedLaw]
  rcases Bool.eq_false_or_eq_true (theta i) with ht | ht <;> simpa [decode, ht, add_comm] using h

def risk {m n : ℕ} (P : Cube m → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin m × Bool))
    (estimate : (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ)) (theta : Cube m) : ℝ :=
  (records (P theta) n).expect (fun w => ∑ x, |estimate w x-(P theta).prob x|)

theorem risk_pays_hamming (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (n : ℕ) (estimate : (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ)) (theta : Cube m) :
    a/(m : ℝ)*(∑ i, coordinateRisk (pairedLaw m hm a ha ha1)
      (fun w => decode (estimate w)) theta i) ≤ risk (pairedLaw m hm a ha ha1) estimate theta := by
  let P := pairedLaw m hm a ha ha1
  let hamming := fun w : Fin n → Fin m × Bool =>
    ∑ i, if decode (estimate w) i ≠ theta i then (1 : ℝ) else 0
  have he : (∑ i, coordinateRisk P (fun w => decode (estimate w)) theta i) =
      (records (P theta) n).expect hamming := by
    simp only [coordinateRisk, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter, hamming,
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    rfl
  have hpoint (w : Fin n → Fin m × Bool) :
      a/(m : ℝ)*hamming w ≤ ∑ x, |estimate w x-(P theta).prob x| := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      coordinate_loss m hm a ha ha1 theta (estimate w) i)
    simpa only [hamming, Finset.mul_sum, Fintype.sum_prod_type] using hs
  change a/(m : ℝ)*(∑ i, coordinateRisk P (fun w => decode (estimate w)) theta i) ≤ _
  rw [he]
  calc
    _ = ∑ w, (records (P theta) n).prob w*(a/(m : ℝ)*hamming w) := by
      simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ ≤ risk P estimate theta := Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hpoint w) ((records (P theta) n).nonneg w)

theorem average_l1_lower (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (n : ℕ) (estimate : (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ)) :
    a/2*(1-Real.sqrt ((n : ℝ)*(4*a^2/(m : ℝ))/2)) ≤
      (∑ theta : Cube m, risk (pairedLaw m hm a ha (by linarith)) estimate theta) /
        (Fintype.card (Cube m) : ℝ) := by
  have ha1 : a < 1 := by linarith
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hc : 0 < (Fintype.card (Cube m) : ℝ) := by exact_mod_cast Fintype.card_pos
  let P := pairedLaw m hm a ha ha1
  let dec := fun w => decode (estimate w)
  have hh := average_hamming_lower P (paired_positive m hm a ha ha1)
    (4*a^2/(m : ℝ)) (neighbor_kl_bound m hm a ha ha2) dec
  have hs : a/(m : ℝ)*(∑ theta : Cube m, ∑ i, coordinateRisk P dec theta i) ≤
      ∑ theta : Cube m, risk P estimate theta := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun theta _ => risk_pays_hamming m hm a ha ha1 n estimate theta
  calc
    _ = a/(m : ℝ)*((m : ℝ)/2*(1-Real.sqrt ((n : ℝ)*(4*a^2/(m : ℝ))/2))) := by
      field_simp [hmR.ne']
    _ ≤ a/(m : ℝ)*((∑ theta : Cube m, ∑ i, coordinateRisk P dec theta i) /
        (Fintype.card (Cube m) : ℝ)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (a/(m : ℝ)*(∑ theta : Cube m, ∑ i, coordinateRisk P dec theta i)) /
        (Fintype.card (Cube m) : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hs hc.le

theorem average_l1_budget (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (n : ℕ) (estimate : (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ))
    (hbudget : (n : ℝ)*a^2 ≤ (m : ℝ)/8) :
    a/4 ≤ (∑ theta : Cube m, risk (pairedLaw m hm a ha (by linarith)) estimate theta) /
        (Fintype.card (Cube m) : ℝ) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hb : (n : ℝ)*(4*a^2/(m : ℝ))/2 ≤ 1/4 := by
    calc
      _ = 2*(n : ℝ)*a^2/(m : ℝ) := by ring
      _ ≤ 1/4 := (div_le_iff₀ hmR).mpr (by nlinarith)
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ)*(4*a^2/(m : ℝ))/2 by positivity)
  have hsqrt : Real.sqrt ((n : ℝ)*(4*a^2/(m : ℝ))/2) ≤ 1/2 := by
    nlinarith [Real.sqrt_nonneg ((n : ℝ)*(4*a^2/(m : ℝ))/2)]
  have hh := average_l1_lower m hm a ha ha2 n estimate
  nlinarith

theorem exists_l1_budget (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (n : ℕ) (estimate : (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ))
    (hbudget : (n : ℝ)*a^2 ≤ (m : ℝ)/8) :
    ∃ theta : Cube m, a/4 ≤ risk (pairedLaw m hm a ha (by linarith)) estimate theta := by
  let P := pairedLaw m hm a ha (show a < 1 by linarith)
  have hc : 0 < (Fintype.card (Cube m) : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨theta, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun theta : Cube m => risk P estimate theta) Finset.univ_nonempty
  refine ⟨theta, (average_l1_budget m hm a ha ha2 n estimate hbudget).trans ?_⟩
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _theta : Cube m, risk P estimate theta :=
      Finset.sum_le_sum fun theta' _ => hmax theta' (Finset.mem_univ _)
    _ = risk P estimate theta*(Fintype.card (Cube m) : ℝ) := by simp [mul_comm]

theorem exists_root_rate (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (estimate : (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ)) :
    ∃ p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin m × Bool), (∀ x, 0 < p.prob x) ∧
      Real.sqrt ((m : ℝ)/(8*(n : ℝ)))/4 ≤
        (records p n).expect (fun w => ∑ x, |estimate w x-p.prob x|) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hm hmn)
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  let a := Real.sqrt ((m : ℝ)/(8*(n : ℝ)))
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hs : a^2 = (m : ℝ)/(8*(n : ℝ)) := Real.sq_sqrt (by positivity)
  have ha2 : a ≤ 1/2 := by
    have harg : (m : ℝ)/(8*(n : ℝ)) ≤ 1/4 :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    nlinarith
  have hb : (n : ℝ)*a^2 ≤ (m : ℝ)/8 := by
    rw [hs]
    apply le_of_eq
    field_simp [hnR.ne']
  obtain ⟨theta, ht⟩ := exists_l1_budget m hm a ha ha2 n estimate hb
  refine ⟨pairedLaw m hm a ha (by linarith) theta, ?_, ht⟩
  exact paired_positive m hm a ha (by linarith) theta

def randomizedRisk {R : Type} [Fintype R] {m n : ℕ}
    (coins : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist R) (P : Cube m → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin m × Bool))
    (estimate : R → (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ)) (theta : Cube m) : ℝ :=
  coins.expect (fun r => risk P (estimate r) theta)

theorem average_randomized_budget {R : Type} [Fintype R]
    (coins : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist R) (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (n : ℕ) (estimate : R → (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ))
    (hbudget : (n : ℝ)*a^2 ≤ (m : ℝ)/8) :
    a/4 ≤ (∑ theta : Cube m,
      randomizedRisk coins (pairedLaw m hm a ha (by linarith)) estimate theta) /
        (Fintype.card (Cube m) : ℝ) := by
  have hc : 0 < (Fintype.card (Cube m) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs (r : R) := (le_div_iff₀ hc).mp
    (average_l1_budget m hm a ha ha2 n (estimate r) hbudget)
  have hw := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset R)) =>
    mul_le_mul_of_nonneg_left (hs r) (coins.nonneg r))
  simp only [← Finset.sum_mul, coins.sum_one, one_mul] at hw
  apply (le_div_iff₀ hc).mpr
  simp only [Finset.mul_sum] at hw
  rw [Finset.sum_comm] at hw
  simpa only [randomizedRisk, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect] using hw

theorem exists_randomized_budget {R : Type} [Fintype R]
    (coins : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist R) (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (n : ℕ) (estimate : R → (Fin n → Fin m × Bool) → (Fin m × Bool → ℝ))
    (hbudget : (n : ℝ)*a^2 ≤ (m : ℝ)/8) :
    ∃ theta : Cube m, a/4 ≤
      randomizedRisk coins (pairedLaw m hm a ha (by linarith)) estimate theta := by
  let P := pairedLaw m hm a ha (show a < 1 by linarith)
  have hc : 0 < (Fintype.card (Cube m) : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨theta, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (randomizedRisk coins P estimate) Finset.univ_nonempty
  refine ⟨theta, (average_randomized_budget coins m hm a ha ha2 n estimate hbudget).trans ?_⟩
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _theta : Cube m, randomizedRisk coins P estimate theta :=
      Finset.sum_le_sum fun theta' _ => hmax theta' (Finset.mem_univ _)
    _ = randomizedRisk coins P estimate theta*(Fintype.card (Cube m) : ℝ) := by simp [mul_comm]

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.PairedCategoricalRisk
