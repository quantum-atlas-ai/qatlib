/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation

/-!
# Layered quantum estimation of nonnegative means

The dyadic payoffs `layerPayoff` split a nonnegative observable into bounded layers, with a
residual controlled by its second moment. Explicit choices `layerGrid` and `layerRepetitions`
define the independent record law `layerLaw` and weighted median readout `layerEstimate`.

For second moment at most one and `k ≥ 1`, the estimator achieves error at most 2^(-k) with
probability at least 1 - 2^(-k). An exact amplitude-estimation query ledger accompanies this
finite-dimensional version of the layered construction in [Montanaro2015].

## Main statements

* `layered_payoff_partition_and_second_moment_tail`: dyadic layers are bounded and their tail is
  controlled by the second moment.
* `layered_quantum_mean_actual_guarantee`: the explicit layered estimator has dyadic accuracy
  and confidence.
* `layered_quantum_mean_actual_query_ledger`: the summed counted-circuit query count is
  explicit.

## References

* [Montanaro, 2015][Montanaro2015]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.MonteCarloMean.LayeredMean

open Matrix
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The dyadic layer payoff: layer zero keeps values below one, and layer `l + 1` rescales
values in [2^l, 2^(l + 1)) by 2^(-(l + 1)). -/
noncomputable def layerPayoff {I : Type} (f : I → ℝ) : ℕ → I → ℝ
  | 0, i => if f i < 1 then f i else 0
  | l+1, i => if (2:ℝ)^l ≤ f i ∧ f i < (2:ℝ)^(l+1) then f i / (2:ℝ)^(l+1) else 0

/-- Layer zero equals the original payoff below one and is zero elsewhere. -/
theorem layerPayoff_zero (f : I → ℝ) (i : I) :
    layerPayoff f 0 i = if f i < 1 then f i else 0 := rfl

/-- Layer `l + 1` equals the payoff divided by 2^(l + 1) on [2^l, 2^(l + 1)) and is zero
elsewhere. -/
theorem layerPayoff_succ (f : I → ℝ) (l : ℕ) (i : I) :
    layerPayoff f (l+1) i =
      if (2:ℝ)^l ≤ f i ∧ f i < (2:ℝ)^(l+1) then f i / (2:ℝ)^(l+1) else 0 := rfl

/-- Every dyadic layer of a nonnegative payoff takes values in the closed interval from zero to
one. -/
theorem layerPayoff_mem_Icc (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∀ (l : ℕ) (i : I), layerPayoff f l i ∈ Set.Icc (0:ℝ) 1 := by
  intro l
  match l with
  | 0 =>
    intro i
    by_cases h : f i < 1
    · rw [layerPayoff_zero, if_pos h]
      exact Set.mem_Icc.mpr ⟨hf i, le_of_lt h⟩
    · rw [layerPayoff_zero, if_neg h]
      norm_num
  | l+1 =>
    intro i
    by_cases h : (2:ℝ)^l ≤ f i ∧ f i < (2:ℝ)^(l+1)
    · rw [layerPayoff_succ, if_pos h]
      refine Set.mem_Icc.mpr ⟨div_nonneg (hf i) (by positivity), ?_⟩
      rw [div_le_one (by positivity : (0:ℝ) < (2:ℝ)^(l+1))]
      exact le_of_lt h.2
    · rw [layerPayoff_succ, if_neg h]
      norm_num

/-- The weighted sum of layers zero through `L` equals the payoff when it is below 2^L, and is
zero when it is at least 2^L. -/
private theorem layer_sum_partition (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∀ (L : ℕ) (i : I), (∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i = f i
        ∧ f i < (2:ℝ)^L)
      ∨ (∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i = 0
        ∧ (2:ℝ)^L ≤ f i) := by
  intro L
  induction L with
  | zero =>
    intro i
    by_cases h : f i < 1
    · left
      refine ⟨?_, h⟩
      rw [Finset.sum_range_one, layerPayoff_zero, if_pos h, pow_zero, one_mul]
    · right
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_range_one, layerPayoff_zero, if_neg h, pow_zero, one_mul]
      · rw [pow_zero]
        exact le_of_not_gt (by simpa using h)
  | succ L ih =>
    intro i
    have hsplit : ∑ l ∈ Finset.range (L+2), (2:ℝ)^l * layerPayoff f l i
        = ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i
          + (2:ℝ)^(L+1) * layerPayoff f (L+1) i := by
      rw [Finset.range_add_one, Finset.sum_insert (by simp)]
      ring
    rcases ih i with ⟨hsum, hlt⟩ | ⟨hsum, hge⟩
    · have hterm : (2:ℝ)^(L+1) * layerPayoff f (L+1) i = 0 := by
        rw [layerPayoff_succ, if_neg (fun h => not_le_of_gt hlt h.1), mul_zero]
      by_cases hlt2 : f i < (2:ℝ)^(L+1)
      · exact Or.inl ⟨by rw [hsplit, hsum, hterm]; ring, hlt2⟩
      · exact absurd (lt_of_lt_of_le hlt
          (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega))) hlt2
    · by_cases hlt2 : f i < (2:ℝ)^(L+1)
      · have hterm : (2:ℝ)^(L+1) * layerPayoff f (L+1) i = f i := by
          rw [layerPayoff_succ, if_pos ⟨hge, hlt2⟩]
          field_simp
        exact Or.inl ⟨by rw [hsplit, hsum, hterm]; ring, hlt2⟩
      · exact Or.inr ⟨by rw [hsplit, hsum, layerPayoff_succ,
          if_neg (fun h => hlt2 h.2), mul_zero]; ring, le_of_not_gt hlt2⟩

/-- For nonnegative weights and payoff, the truncated layered mean is at most the full mean,
with residual at most the weighted second moment divided by 2^L. -/
private theorem weighted_layer_residual (w : I → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (L : ℕ) :
    (∑ l ∈ Finset.range (L+1), (2:ℝ)^l * ∑ i, w i * layerPayoff f l i) ≤ ∑ i, w i * f i
      ∧ (∑ i, w i * f i) - (∑ l ∈ Finset.range (L+1), (2:ℝ)^l * ∑ i, w i * layerPayoff f l i)
        ≤ (∑ i, w i * (f i)^2)/(2:ℝ)^L := by
  have hres : ∀ i : I, 0 ≤ f i - ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i
      ∧ f i - ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i ≤ (f i)^2/(2:ℝ)^L := by
    intro i
    rcases layer_sum_partition f hf L i with ⟨hsum, hlt⟩ | ⟨hsum, hge⟩
    · rw [hsum, sub_self]
      exact ⟨by norm_num, by positivity⟩
    · rw [hsum, sub_zero]
      have hfp : (0:ℝ) < (2:ℝ)^L := by positivity
      refine ⟨hf i, ?_⟩
      have h1 : (2:ℝ)^L * f i ≤ f i * f i := mul_le_mul_of_nonneg_right hge (hf i)
      rw [le_div_iff₀ hfp]
      calc f i * (2:ℝ)^L = (2:ℝ)^L * f i := by ring
        _ ≤ f i * f i := h1
        _ = (f i)^2 := (pow_two _).symm
  have hswap : (∑ l ∈ Finset.range (L+1), (2:ℝ)^l * ∑ i, w i * layerPayoff f l i)
      = ∑ i, w i * ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i := by
    calc (∑ l ∈ Finset.range (L+1), (2:ℝ)^l * ∑ i, w i * layerPayoff f l i)
        = ∑ l ∈ Finset.range (L+1), ∑ i, (2:ℝ)^l * (w i * layerPayoff f l i) :=
          Finset.sum_congr rfl fun l _ => Finset.mul_sum _ _ _
      _ = ∑ i, ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * (w i * layerPayoff f l i) :=
          Finset.sum_comm
      _ = ∑ i, w i * ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * (w i * layerPayoff f l i)
              = ∑ l ∈ Finset.range (L+1), w i * ((2:ℝ)^l * layerPayoff f l i) :=
                Finset.sum_congr rfl fun l _ => by ring
            _ = w i * ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i :=
                (Finset.mul_sum _ _ _).symm
  constructor
  · rw [hswap]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sub_nonneg.mp (hres i).1) (hw0 i)
  · rw [hswap, ← Finset.sum_sub_distrib]
    have hdistrib : ∀ i ∈ (Finset.univ : Finset I),
        w i * f i - w i * ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i
          = w i * (f i - ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i) := by
      intro i _; ring
    rw [Finset.sum_congr rfl hdistrib]
    have hle : ∀ i ∈ (Finset.univ : Finset I),
        w i * (f i - ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i)
          ≤ w i * ((f i)^2/(2:ℝ)^L) := fun i _ =>
        mul_le_mul_of_nonneg_left (hres i).2 (hw0 i)
    calc ∑ i, w i * (f i - ∑ l ∈ Finset.range (L+1), (2:ℝ)^l * layerPayoff f l i)
        ≤ ∑ i, w i * ((f i)^2/(2:ℝ)^L) := Finset.sum_le_sum hle
      _ = ∑ i, (w i * (f i)^2)/(2:ℝ)^L :=
            Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm
      _ = (∑ i, w i * (f i)^2)/(2:ℝ)^L := (Finset.sum_div _ _ _).symm

/-- For a nonnegative payoff under a unitary-prepared Born law, all layers lie in [0, 1] and the
truncated mean residual is bounded by its second moment divided by 2^L. This is the dyadic
partition used for [Montanaro2015, Algorithm 2][Montanaro2015]. -/
theorem layered_payoff_partition_and_second_moment_tail (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (L : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) :
    (∀ l i, layerPayoff f l i ∈ Set.Icc (0:ℝ) 1) ∧
    (∑ i, BornProb (ApplyGate A (Ket j)) i*f i)-(∑ l ∈ Finset.range (L+1), (2:ℝ)^l*∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f l i) ≤ (∑ i, BornProb (ApplyGate A (Ket j)) i*(f i)^2)/(2:ℝ)^L :=
  ⟨layerPayoff_mem_Icc f hf,
    (weighted_layer_residual (fun i => BornProb (ApplyGate A (Ket j)) i)
      (fun i => bornProb_nonneg _ _) f hf L).2⟩

/-- The amplitude-estimation grid size 2^(k + 6)(k + 2) used for each dyadic layer. -/
def layerGrid (k : ℕ) : ℕ := 2^(k+6)*(k+2)

/-- The median repetition parameter 8(k + 2) used in each dyadic layer. -/
def layerRepetitions (k : ℕ) : ℕ := 8*(k+2)

/-- The grid size chosen for every precision parameter is strictly positive. -/
theorem layerGrid_pos (k : ℕ) : 0 < layerGrid k := by
  simp only [layerGrid]
  positivity

/-- The chosen layer grid always has at least two points. -/
theorem layerGrid_ge_two (k : ℕ) : 2 ≤ layerGrid k := by
  simp only [layerGrid]
  calc 2 = (2:ℕ)^1 := rfl
    _ ≤ (2:ℕ)^(k+6) := Nat.pow_le_pow_right (by omega : (0:ℕ) < 2) (by omega : (1:ℕ) ≤ k + 6)
    _ ≤ (2:ℕ)^(k+6)*(k+2) := Nat.le_mul_of_pos_right (m := k+2) _ (by omega : 0 < k + 2)

/-- The real constant π is at most 10/3. -/
private theorem pi_le_ten_thirds : Real.pi ≤ 10/3 :=
  le_trans (le_of_lt Real.pi_lt_d2) (by norm_num)

/-- The square of π is strictly less than ten. -/
private theorem pi_sq_lt_ten : Real.pi^2 < 10 := by
  have h1 : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  have h2 : Real.pi * Real.pi ≤ (3.15) * (3.15) :=
    mul_le_mul (le_of_lt Real.pi_lt_d2) (le_of_lt Real.pi_lt_d2) h1 (by norm_num)
  rw [pow_two]
  nlinarith

/-- For a natural `k`, the integer power 2^(-k) equals the natural power (1/2)^k. -/
theorem neg_pow_half_eq (k : ℕ) : (2:ℝ)^(-((k:ℤ))) = ((1:ℝ)/2)^k := by
  rw [show (2:ℝ)^(-(k:ℤ)) = ((2:ℝ)^((k:ℤ)))⁻¹ from _root_.zpow_neg (2:ℝ) (k:ℤ)]
  rw [show ((2:ℝ)^((k:ℤ))) = (2:ℝ)^(k:ℕ) from by rfl, ← inv_pow]
  norm_num

/-- Every natural number `n` is strictly smaller than 2^n. -/
private theorem nat_lt_two_pow_self : ∀ n : ℕ, n < 2^n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- The explicit grid and repetition formulas give a grid of size at least two and combined
layer failure bound at most 2^(-k), as used for [Montanaro2015, Algorithm 2][Montanaro2015]. -/
theorem layered_mean_computed_parameters (k : ℕ) :
    layerGrid k=2^(k+6)*(k+2) ∧ layerRepetitions k=8*(k+2) ∧ 2≤layerGrid k ∧
    ((k+2:ℝ)*(2:ℝ)^(2*layerRepetitions k+1)*(1-8/Real.pi^2)^(layerRepetitions k+1)≤(2:ℝ)^(-((k:ℤ)))) := by
  have hpi2pos : (0:ℝ) < Real.pi^2 := by positivity
  have hp_nonneg : 0 ≤ 1 - 8/Real.pi^2 := by
    have h8 : 8/Real.pi^2 ≤ 1 :=
      (div_le_one hpi2pos).mpr (by nlinarith [Real.pi_gt_three, Real.pi_lt_four])
    linarith
  have hp5 : 1 - 8/Real.pi^2 ≤ 1/5 := by
    have h5 : (4:ℝ)/5 ≤ 8/Real.pi^2 := by
      rw [div_le_div_iff₀ (by norm_num) hpi2pos]
      nlinarith [pi_sq_lt_ten]
    linarith
  have h458 : ((4:ℝ)/5)^8 ≤ 1/4 := by norm_num
  have hk2 : ((k:ℕ):ℝ) + 2 ≤ (2:ℝ)^(k+1) := by
    have h2 : (k+2:ℕ) ≤ 2^(k+1) := by
      have h1 : (k+1:ℕ) < 2^(k+1) := nat_lt_two_pow_self (k+1)
      omega
    have h3 : ((k+2:ℕ):ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast h2
    simpa using h3
  refine ⟨rfl, rfl, layerGrid_ge_two k, ?_⟩
  have hexp1 : (2:ℝ)^(2*layerRepetitions k+1) = 2 * ((2:ℝ)^2)^(layerRepetitions k) := by
    rw [← pow_mul, pow_succ]
    ring
  have hexp2 : ((1:ℝ)/5)^(layerRepetitions k+1)
      = ((1:ℝ)/5)^(layerRepetitions k) * (1/5) := pow_succ _ _
  have hkey : (2:ℝ)^(2*layerRepetitions k+1) * ((1:ℝ)/5)^(layerRepetitions k+1)
      = (2/5) * ((4:ℝ)/5)^(layerRepetitions k) := by
    rw [hexp1, hexp2]
    have hmp : (2:ℝ)^2 * ((1:ℝ)/5) = (4:ℝ)/5 := by norm_num
    calc (2:ℝ) * ((2:ℝ)^2)^(layerRepetitions k)
          * (((1:ℝ)/5)^(layerRepetitions k) * (1/5))
        = (2:ℝ) * (((2:ℝ)^2)^(layerRepetitions k) * ((1:ℝ)/5)^(layerRepetitions k))
            * (1/5) := by ring
      _ = (2:ℝ) * (((2:ℝ)^2 * ((1:ℝ)/5))^(layerRepetitions k)) * (1/5) := by rw [mul_pow]
      _ = (2/5) * ((4:ℝ)/5)^(layerRepetitions k) := by rw [hmp]; ring
  have hsplit : ((4:ℝ)/5)^(layerRepetitions k) = (((4:ℝ)/5)^8)^(k+2) := by
    rw [layerRepetitions, ← pow_mul]
  have hlast : (2:ℝ)^(k+1) * ((1:ℝ)/2)^(2*(k+2)) = ((1:ℝ)/2)^(k+3) := by
    have hsplit2 : ((1:ℝ)/2)^(2*(k+2)) = ((1:ℝ)/2)^(k+1) * ((1:ℝ)/2)^(k+3) := by
      rw [← pow_add]
      congr 1
      omega
    have hmp : ((2:ℝ) * ((1:ℝ)/2)) = 1 := by norm_num
    rw [hsplit2]
    calc (2:ℝ)^(k+1) * (((1:ℝ)/2)^(k+1) * ((1:ℝ)/2)^(k+3))
        = ((2:ℝ)^(k+1) * ((1:ℝ)/2)^(k+1)) * ((1:ℝ)/2)^(k+3) := by ring
      _ = (((2:ℝ) * ((1:ℝ)/2))^(k+1)) * ((1:ℝ)/2)^(k+3) := by rw [mul_pow]
      _ = (1:ℝ) * ((1:ℝ)/2)^(k+3) := by rw [hmp, one_pow]
      _ = ((1:ℝ)/2)^(k+3) := by ring
  have hcoeff : (2/5) * ((1:ℝ)/2)^3 ≤ 1 := by norm_num
  have hhalf4 : ((1:ℝ)/4)^(k+2) = ((1:ℝ)/2)^(2*(k+2)) := by
    have hq : ((1:ℝ)/4) = ((1:ℝ)/2)^2 := by norm_num
    rw [hq, pow_mul]
  rw [neg_pow_half_eq k]
  rw [show (k+2:ℝ)*(2:ℝ)^(2*layerRepetitions k+1)*(1-8/Real.pi^2)^(layerRepetitions k+1)
      = (k+2:ℝ) * ((2:ℝ)^(2*layerRepetitions k+1) * (1-8/Real.pi^2)^(layerRepetitions k+1)) from by ring]
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp_nonneg hp5 _) (by positivity)) (by positivity)) ?_
  rw [hkey, hsplit]
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h458 _) (by positivity))
    (by positivity)) ?_
  rw [hhalf4]
  calc (((k:ℕ):ℝ) + 2) * (((2:ℝ)/5) * ((1:ℝ)/2)^(2*(k+2)))
      ≤ (2:ℝ)^(k+1) * (((2:ℝ)/5) * ((1:ℝ)/2)^(2*(k+2))) :=
        mul_le_mul_of_nonneg_right hk2 (by positivity)
    _ = ((2:ℝ)/5) * ((2:ℝ)^(k+1) * ((1:ℝ)/2)^(2*(k+2))) := by ring
    _ = ((2:ℝ)/5) * ((1:ℝ)/2)^(k+3) := by rw [hlast]
    _ = ((2:ℝ)/5) * (((1:ℝ)/2)^3 * ((1:ℝ)/2)^k) := by rw [pow_add]; ring
    _ = (((2:ℝ)/5) * ((1:ℝ)/2)^3) * ((1:ℝ)/2)^k := by ring
    _ ≤ ((1:ℝ)/2)^k := by
        refine le_trans (mul_le_mul_of_nonneg_right hcoeff (by positivity)) ?_
        exact le_of_eq (by ring)

/-- A finite sum of a product payoff weighted by product masses factors into the product of the
corresponding coordinate sums. -/
private theorem pi_dist_prod {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (q : Fin n → FinDist X) (g : Fin n → X → ℝ) :
    ∑ ω : Fin n → X, (∏ i, (q i).prob (ω i)) * ∏ i, g i (ω i)
      = ∏ i, (∑ x, (q i).prob x * g i x) := by
  have habs : ∀ ω : Fin n → X, (∏ i, (q i).prob (ω i)) * ∏ i, g i (ω i)
      = ∏ i, ((q i).prob (ω i) * g i (ω i)) := by
    intro ω
    rw [← Finset.prod_mul_distrib]
  calc ∑ ω : Fin n → X, (∏ i, (q i).prob (ω i)) * ∏ i, g i (ω i)
      = ∑ ω : Fin n → X, ∏ i, ((q i).prob (ω i) * g i (ω i)) :=
        Finset.sum_congr rfl fun ω _ => habs ω
    _ = ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset X)),
          ∏ i, ((q i).prob (ω i) * g i (ω i)) :=
        Finset.sum_congr rfl fun ω _ => rfl
    _ = ∏ i, (∑ x ∈ Finset.univ, (q i).prob x * g i x) :=
        (Finset.prod_univ_sum
          (t := fun _ : Fin n => (Finset.univ : Finset X))
          (f := fun i x => (q i).prob x * g i x)).symm

/-- The product masses of a finite family of probability distributions sum to one. -/
private theorem pi_dist_sum {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (q : Fin n → FinDist X) : ∑ ω : Fin n → X, ∏ i, (q i).prob (ω i) = 1 := by
  calc ∑ ω : Fin n → X, ∏ i, (q i).prob (ω i)
      = ∑ ω : Fin n → X, (∏ i, (q i).prob (ω i)) * 1 := by simp
    _ = ∑ ω : Fin n → X, (∏ i, (q i).prob (ω i)) * ∏ i, (1:ℝ) := by
        congr 1
        exact funext fun ω => by rw [Finset.prod_const_one]
    _ = ∏ i, (∑ x, (q i).prob x * 1) := pi_dist_prod q (fun _ _ => (1:ℝ))
    _ = ∏ i, (∑ x, (q i).prob x) := Finset.prod_congr rfl fun i _ => by simp
    _ = ∏ i, 1 := Finset.prod_congr rfl fun i _ => (q i).sum_one
    _ = 1 := Finset.prod_const_one

/-- The finite law of `2 * layerRepetitions k + 1` independent amplitude-estimation outcomes for
one bounded dyadic layer. -/
noncomputable def layerTrialLaw {I : Type} [Fintype I] [DecidableEq I] (k : ℕ)
    (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) (l : Fin (k+2)) :
    FinDist (Fin (2*layerRepetitions k+1) → Fin (layerGrid k)) where
  prob u := ∏ n, (meanLaw (layerGrid k) A j (layerPayoff f (l:ℕ)) hA
    (layerPayoff_mem_Icc f hf _) (layerGrid_ge_two k)).prob (u n)
  nonneg u := Finset.prod_nonneg fun n _ =>
    (meanLaw (layerGrid k) A j (layerPayoff f (l:ℕ)) hA
      (layerPayoff_mem_Icc f hf _) (layerGrid_ge_two k)).nonneg _
  sum_one := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf (meanLaw (layerGrid k) A j (layerPayoff f (l:ℕ)) hA
    (layerPayoff_mem_Icc f hf _) (layerGrid_ge_two k)) (2*layerRepetitions k+1)

/-- The product law of the repeated amplitude-estimation records over all `k + 2` dyadic layers. -/
noncomputable def layerLaw {I : Type} [Fintype I] [DecidableEq I] (k : ℕ)
    (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) :
    FinDist (Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k)) where
  prob ω := ∏ l, (layerTrialLaw k A j f hA hf l).prob (ω l)
  nonneg ω := Finset.prod_nonneg fun l _ => (layerTrialLaw k A j f hA hf l).nonneg _
  sum_one := pi_dist_sum (layerTrialLaw k A j f hA hf)

/-- The mass of a full layered record is the product of its individual layer-record masses. -/
theorem layerLaw_prob (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i)
    (ω : Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k)) :
    (layerLaw k A j f hA hf).prob ω
      = ∏ l, (layerTrialLaw k A j f hA hf l).prob (ω l) := rfl

/-- A layer trial-record mass equals the independent record probability under its bounded-payoff
mean-estimation law. -/
theorem layerTrialLaw_probOf (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) (l : Fin (k+2))
    (u : Fin (2*layerRepetitions k+1) → Fin (layerGrid k)) :
    (layerTrialLaw k A j f hA hf l).prob u
      = (meanLaw (layerGrid k) A j (layerPayoff f (l:ℕ)) hA
          (layerPayoff_mem_Icc f hf _) (layerGrid_ge_two k)).probOf u := rfl

/-- The sum of the layerwise median estimates, with layer `l` multiplied by 2^l. -/
noncomputable def layerEstimate (k : ℕ)
    (ω : Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k)) : ℝ :=
  ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * meanMedian (layerRepetitions k) (layerGrid k) (ω l)

/-- An event depending on one layer has the same probability under the full product law as under
that layer's trial law. -/
private theorem layerLaw_marginal (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i)
    (l₀ : Fin (k+2)) (B : (Fin (2*layerRepetitions k+1) → Fin (layerGrid k)) → Prop)
    [DecidablePred B] :
    ∑ ω ∈ (Finset.univ : Finset (Fin (k+2) → Fin (2*layerRepetitions k+1)
        → Fin (layerGrid k))).filter (fun ω => B (ω l₀)), (layerLaw k A j f hA hf).prob ω
      = ∑ u ∈ (Finset.univ : Finset (Fin (2*layerRepetitions k+1)
          → Fin (layerGrid k))).filter B, (layerTrialLaw k A j f hA hf l₀).prob u := by
  classical
  have hstep1 : ∑ ω ∈ (Finset.univ : Finset (Fin (k+2) → Fin (2*layerRepetitions k+1)
        → Fin (layerGrid k))).filter (fun ω => B (ω l₀)), (layerLaw k A j f hA hf).prob ω
      = ∑ ω : Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
          (layerLaw k A j f hA hf).prob ω *
          ∏ l : Fin (k+2),
            ((if l = l₀ then (if B (ω l) then (1:ℝ) else 0) else 1) : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hB : B (ω l₀)
    · rw [if_pos hB]
      have h0 : ∀ b ∈ (Finset.univ : Finset (Fin (k+2))), b ≠ l₀ →
          ((if b = l₀ then (if B (ω b) then (1:ℝ) else 0) else 1) : ℝ) = 1 := by
        intro b _ hbl
        rw [if_neg hbl]
      have h1 : l₀ ∉ (Finset.univ : Finset (Fin (k+2))) →
          ((if l₀ = l₀ then (if B (ω l₀) then (1:ℝ) else 0) else 1) : ℝ) = 1 := by
        intro hcon
        exact absurd (Finset.mem_univ l₀) hcon
      have hprod : ∏ l : Fin (k+2),
          ((if l = l₀ then (if B (ω l) then (1:ℝ) else 0) else 1) : ℝ) = (1:ℝ) := by
        calc ∏ l : Fin (k+2),
              ((if l = l₀ then (if B (ω l) then (1:ℝ) else 0) else 1) : ℝ)
            = ((if l₀ = l₀ then (if B (ω l₀) then (1:ℝ) else 0) else 1) : ℝ) :=
                Finset.prod_eq_single l₀ h0 h1
          _ = (1:ℝ) := by rw [if_pos rfl, if_pos hB]
      rw [hprod, mul_one]
    · rw [if_neg hB]
      have hprod : ∏ l : Fin (k+2),
          (if l = l₀ then (if B (ω l) then (1:ℝ) else 0) else 1) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ l₀) ?_
        rw [if_pos rfl, if_neg hB]
      rw [hprod, mul_zero]
  rw [hstep1]
  calc (∑ ω : Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
          (layerLaw k A j f hA hf).prob ω *
          ∏ l : Fin (k+2), (if l = l₀ then (if B (ω l) then (1:ℝ) else 0) else 1))
      = ∑ ω : Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
          (∏ l, (layerTrialLaw k A j f hA hf l).prob (ω l)) *
          ∏ l : Fin (k+2),
            (fun l u => if l = l₀ then (if B u then (1:ℝ) else 0) else 1) l (ω l) :=
        Finset.sum_congr rfl fun ω _ => rfl
    _ = ∏ l : Fin (k+2), (∑ u : Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
          (layerTrialLaw k A j f hA hf l).prob u *
          (if l = l₀ then (if B u then (1:ℝ) else 0) else 1)) :=
        pi_dist_prod (layerTrialLaw k A j f hA hf)
          (fun l u => if l = l₀ then (if B u then (1:ℝ) else 0) else 1)
    _ = ∑ u : Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
          (layerTrialLaw k A j f hA hf l₀).prob u * (if B u then (1:ℝ) else 0) := by
        rw [Finset.prod_eq_single l₀]
        · simp only [if_true]
        · intro l _ hl
          simp only [if_neg hl, mul_one]
          exact (layerTrialLaw k A j f hA hf l).sum_one
        · intro hcon
          exact absurd (Finset.mem_univ l₀) hcon
  have hite : ∀ u : Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
      (layerTrialLaw k A j f hA hf l₀).prob u * (if B u then (1:ℝ) else 0)
        = if B u then (layerTrialLaw k A j f hA hf l₀).prob u else 0 := by
    intro u
    by_cases hB : B u
    · rw [if_pos hB, if_pos hB, mul_one]
    · rw [if_neg hB, if_neg hB, mul_zero]
  calc (∑ u : Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
          (layerTrialLaw k A j f hA hf l₀).prob u * (if B u then (1:ℝ) else 0))
      = ∑ u, (if B u then (layerTrialLaw k A j f hA hf l₀).prob u else 0) :=
        Finset.sum_congr rfl fun u _ => hite u
    _ = ∑ u ∈ Finset.univ.filter B, (layerTrialLaw k A j f hA hf l₀).prob u := by
        rw [Finset.sum_filter]

/-- The sum of the first `n` nonnegative powers of two is at most 2^n. -/
private theorem geom_two_sum_le : ∀ n : ℕ, ∑ l ∈ Finset.range n, (2:ℝ)^l ≤ (2:ℝ)^n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ∑ l ∈ Finset.range (n+1), (2:ℝ)^l
        = (2:ℝ)^n + ∑ l ∈ Finset.range n, (2:ℝ)^l := by
      rw [Finset.range_add_one, Finset.sum_insert (by simp)]
    have h2 : (2:ℝ)^n + (2:ℝ)^n = (2:ℝ)^(n+1) := by
      rw [pow_succ]
      ring
    rw [hstep]
    calc (2:ℝ)^n + ∑ l ∈ Finset.range n, (2:ℝ)^l
        ≤ (2:ℝ)^n + (2:ℝ)^n := by linarith [ih]
      _ = (2:ℝ)^(n+1) := h2

/-- For a nonnegative payoff and layer index at least one, 2^(2l) times the layer payoff is at
most twice the squared original payoff. -/
private theorem layer_bridge (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (l : ℕ)
    (hl : 1 ≤ l) (i : I) :
    (2:ℝ)^(2*l) * layerPayoff f l i ≤ 2 * (f i)^2 := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m+1 := ⟨l-1, by omega⟩
  rw [layerPayoff_succ]
  by_cases h : (2:ℝ)^m ≤ f i ∧ f i < (2:ℝ)^(m+1)
  · rw [if_pos h]
    have hp : (0:ℝ) < (2:ℝ)^(m+1) := by positivity
    have hcompute : (2:ℝ)^(2*(m+1)) * (f i / (2:ℝ)^(m+1))
        = (2:ℝ)^(m+1) * f i := by
      field_simp [hp.ne']
      rw [show 2*(m+1) = (m+1)+(m+1) from by omega, pow_add]
      ring
    rw [hcompute]
    have hnext : (2:ℝ)^(m+1) = 2*(2:ℝ)^m := by rw [pow_succ]; ring
    nlinarith [h.1, hf i]
  · rw [if_neg h, mul_zero]
    exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg (f i))

/-- Under nonnegative normalized weights and second moment at most one, the rescaled square root
of each layer mean times its complement is at most two. -/
private theorem layer_weighted_sqrt_bound (w : I → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hE : ∑ i, w i * (f i)^2 ≤ 1) (l : ℕ) :
    (2:ℝ)^l * Real.sqrt ((∑ i, w i * layerPayoff f l i)*(1-∑ i, w i * layerPayoff f l i)) ≤ 2 := by
  have hμl0 : (0:ℝ) ≤ ∑ i, w i * layerPayoff f l i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (layerPayoff_mem_Icc f hf l i).1
  have hμl1 : ∑ i, w i * layerPayoff f l i ≤ 1 := by
    have hle : ∀ i ∈ (Finset.univ : Finset I),
        w i * layerPayoff f l i ≤ w i * 1 :=
      fun i _ => mul_le_mul_of_nonneg_left (layerPayoff_mem_Icc f hf l i).2 (hw0 i)
    calc ∑ i, w i * layerPayoff f l i ≤ ∑ i, w i * 1 := Finset.sum_le_sum hle
      _ = ∑ i, w i := by simp
      _ = 1 := hwsum
  have hsub : (∑ i, w i * layerPayoff f l i)*(1-∑ i, w i * layerPayoff f l i)
      ≤ ∑ i, w i * layerPayoff f l i := by
    have h1 : 1 - ∑ i, w i * layerPayoff f l i ≤ 1 := by linarith
    calc (∑ i, w i * layerPayoff f l i)*(1-∑ i, w i * layerPayoff f l i)
        ≤ (∑ i, w i * layerPayoff f l i)*1 :=
          mul_le_mul_of_nonneg_left h1 hμl0
      _ = ∑ i, w i * layerPayoff f l i := by ring
  rcases l with _ | m
  · rw [pow_zero, one_mul]
    have hle1 : (∑ i, w i * layerPayoff f 0 i)*(1-∑ i, w i * layerPayoff f 0 i) ≤ 1 :=
      le_trans hsub hμl1
    exact (Real.sqrt_le_one.mpr hle1).trans (by norm_num)
  · have hpow : ((2:ℝ)^(m+1))^2 = (2:ℝ)^(2*(m+1)) := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    have hcoef : (2:ℝ)^(m+1) * Real.sqrt (∑ i, w i * layerPayoff f (m+1) i)
        = Real.sqrt ((2:ℝ)^(2*(m+1)) * ∑ i, w i * layerPayoff f (m+1) i) := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (2:ℝ)^(m+1)),
        ← Real.sqrt_mul (sq_nonneg ((2:ℝ)^(m+1))), hpow]
    have hbridge : (2:ℝ)^(2*(m+1)) * ∑ i, w i * layerPayoff f (m+1) i
        ≤ 2 * (∑ i, w i * (f i)^2) := by
      rw [Finset.mul_sum]
      have hpt : ∀ i ∈ (Finset.univ : Finset I),
          (2:ℝ)^(2*(m+1)) * (w i * layerPayoff f (m+1) i) ≤ w i * (2 * (f i)^2) := by
        intro i _
        calc (2:ℝ)^(2*(m+1)) * (w i * layerPayoff f (m+1) i)
            = w i * ((2:ℝ)^(2*(m+1)) * layerPayoff f (m+1) i) := by ring
          _ ≤ w i * (2 * (f i)^2) :=
              mul_le_mul_of_nonneg_left (layer_bridge f hf (m+1) (by omega) i) (hw0 i)
      calc ∑ i, (2:ℝ)^(2*(m+1)) * (w i * layerPayoff f (m+1) i)
          ≤ ∑ i, w i * (2 * (f i)^2) := Finset.sum_le_sum hpt
        _ = 2 * (∑ i, w i * (f i)^2) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
    have hE2 : 2 * (∑ i, w i * (f i)^2) ≤ 2 := by linarith
    refine le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsub) (by positivity)) ?_
    rw [hcoef]
    refine le_trans (Real.sqrt_le_sqrt hbridge) ?_
    refine le_trans (Real.sqrt_le_sqrt hE2) ?_
    have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [hs2, sq_nonneg (2 - Real.sqrt 2)]

/-- The combined explicit amplitude-estimation and truncation error terms for the chosen grid
are at most 2^(-k). -/
private theorem layered_numeric_tail (k : ℕ) :
    4*Real.pi*((k+2:ℕ):ℝ)/(layerGrid k:ℝ)
      + Real.pi^2*(2:ℝ)^(k+2)/(layerGrid k:ℝ)^2
      + (1:ℝ)/(2:ℝ)^(k+1)
    ≤ (2:ℝ)^(-(k:ℤ)) := by
  have hy : (0:ℝ) < (2:ℝ)^(k:ℕ) := by positivity
  have hyne : (2:ℝ)^(k:ℕ) ≠ 0 := hy.ne'
  have hk2pos : (0:ℝ) < ((k+2:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < k+2)
  have hk2ne : ((k+2:ℕ):ℝ) ≠ 0 := hk2pos.ne'
  have hMdef : (layerGrid k:ℝ) = (2:ℝ)^(k:ℕ) * 64 * ((k+2:ℕ):ℝ) := by
    rw [layerGrid]
    push_cast
    rw [pow_add]
    norm_num
  have hMpos : (0:ℝ) < (layerGrid k:ℝ) := by rw [hMdef]; positivity
  have hMne : (layerGrid k:ℝ) ≠ 0 := hMpos.ne'
  have hM2ne : ((layerGrid k:ℝ)^2) ≠ 0 := by positivity
  have h2k2 : (2:ℝ)^(k+2) = (2:ℝ)^(k:ℕ) * 4 := by rw [pow_add]; norm_num
  have h2k1 : (2:ℝ)^(k+1) = (2:ℝ)^(k:ℕ) * 2 := by rw [pow_add]; norm_num
  have hy0 : (0:ℝ) ≤ (2:ℝ)^(k:ℕ) := pow_nonneg (by norm_num) _
  have hk20 : (0:ℝ) ≤ ((k+2:ℕ):ℝ) := hk2pos.le
  have hA : 4*Real.pi*((k+2:ℕ):ℝ)/(layerGrid k:ℝ)
      ≤ ((10:ℝ)/3)/((2:ℝ)^(k:ℕ)) / 16 := by
    rw [hMdef]
    rw [show (((10:ℝ)/3)/((2:ℝ)^(k:ℕ)))/16 = (10/3)/(16*((2:ℝ)^(k:ℕ))) from by ring]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(k:ℕ)*64*((k+2:ℕ):ℝ))
      (by positivity : (0:ℝ) < 16*((2:ℝ)^(k:ℕ)))]
    have ht : (0:ℝ) ≤ ((k+2:ℕ):ℝ) * (2:ℝ)^(k:ℕ) := mul_nonneg hk20 hy0
    have hprod : Real.pi * (((k+2:ℕ):ℝ) * (2:ℝ)^(k:ℕ))
        ≤ (10/3) * (((k+2:ℕ):ℝ) * (2:ℝ)^(k:ℕ)) :=
      mul_le_mul_of_nonneg_right pi_le_ten_thirds ht
    nlinarith [hprod]
  have h2le : (2:ℝ) ≤ ((k+2:ℕ):ℝ) := by exact_mod_cast (by omega : (2:ℕ) ≤ k + 2)
  have hsq1 : (1:ℝ) ≤ ((k+2:ℕ):ℝ)^2 := by
    have h2x : (2:ℝ)*((k+2:ℕ):ℝ) ≤ ((k+2:ℕ):ℝ)*((k+2:ℕ):ℝ) :=
      mul_le_mul_of_nonneg_right h2le hk20
    nlinarith [h2x, h2le, hk20]
  have hB : Real.pi^2*(2:ℝ)^(k+2)/(layerGrid k:ℝ)^2
      ≤ (10:ℝ)/(1024*(2:ℝ)^(k:ℕ)) := by
    rw [hMdef, h2k2]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ((2:ℝ)^(k:ℕ)*64*((k+2:ℕ):ℝ))^2)
      (by positivity : (0:ℝ) < 1024*((2:ℝ)^(k:ℕ)))]
    have hy2 : (0:ℝ) ≤ ((2:ℝ)^(k:ℕ))^2 := sq_nonneg _
    have hs2 : (0:ℝ) ≤ (((k+2:ℕ):ℝ))^2 := sq_nonneg _
    have h10s : (10:ℝ) ≤ 10 * (((k+2:ℕ):ℝ)^2) := by
      simpa using mul_le_mul_of_nonneg_left hsq1 (by norm_num : (0:ℝ) ≤ 10)
    have hπs : Real.pi^2 ≤ 10 * (((k+2:ℕ):ℝ)^2) :=
      le_trans pi_sq_lt_ten.le h10s
    have hkey : Real.pi^2 * ((2:ℝ)^(k:ℕ))^2
        ≤ (10 * (((k+2:ℕ):ℝ)^2)) * ((2:ℝ)^(k:ℕ))^2 := by
      nlinarith [hπs, hy2]
    nlinarith [hkey, hy2, hs2]
  have hC : (1:ℝ)/(2:ℝ)^(k+1) = (1:ℝ)/(2*(2:ℝ)^(k:ℕ)) := by rw [h2k1]; ring
  have hcoeff : (10:ℝ)/3/16 + (10:ℝ)/1024 + 1/2 ≤ 1 := by norm_num
  have hd : ((10:ℝ)/3)/((2:ℝ)^(k:ℕ))/16 + (10:ℝ)/(1024*(2:ℝ)^(k:ℕ))
      + (1:ℝ)/(2*(2:ℝ)^(k:ℕ))
      = (((10:ℝ)/3)/16 + (10:ℝ)/1024 + 1/2)/((2:ℝ)^(k:ℕ)) := by
    field_simp
  have hhalf : ((1:ℝ)/2)^k = 1/((2:ℝ)^(k:ℕ)) := by
    rw [one_div, inv_pow, one_div]
  rw [neg_pow_half_eq k, hhalf, hC]
  refine le_trans (add_le_add (add_le_add hA hB) le_rfl) ?_
  rw [hd, le_div_iff₀ hy]
  field_simp
  linarith [hcoeff]

set_option maxHeartbeats 4000000 in

/-- For `k ≥ 1` and a nonnegative payoff with Born second moment at most one, the layered
readout is within 2^(-k) of its mean with probability at least 1 - 2^(-k). This realizes the
finite-law guarantee associated with [Montanaro2015, Lemma 4][Montanaro2015]. -/
theorem layered_quantum_mean_actual_guarantee (k : ℕ) (hk : 1 ≤ k) (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i)
    (hE : (∑ i, BornProb (ApplyGate A (Ket j)) i*(f i)^2) ≤ 1) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i*f i;
    ∑ ω ∈ Finset.univ.filter (fun ω => |layerEstimate k ω-μ|≤(2:ℝ)^(-((k:ℤ)))), (layerLaw k A j f hA hf).prob ω ≥ 1-(2:ℝ)^(-((k:ℤ))) := by
  classical
  (try dsimp only)
  set w := fun i => BornProb (ApplyGate A (Ket j)) i with hwdef
  have hw0 : ∀ i, (0:ℝ) ≤ w i := fun i => bornProb_nonneg _ _
  have hwsum : ∑ i, w i = 1 :=
    measureProb_univ (normalized_applyGate hA (normalized_ket j))
  set μ := ∑ i, w i*f i with hμ

  have hsqrtbound : ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * Real.sqrt
      ((∑ i, w i*layerPayoff f (l:ℕ) i)*(1-∑ i, w i*layerPayoff f (l:ℕ) i))
      ≤ ((k+2:ℕ):ℝ)*2 := by
    refine le_trans (Finset.sum_le_sum fun l _ =>
      layer_weighted_sqrt_bound w hw0 hwsum f hf hE (l:ℕ)) ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hgeom : ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) ≤ (2:ℝ)^(k+2) :=
    le_trans (le_of_eq (Fin.sum_univ_eq_sum_range (fun m : ℕ => (2:ℝ)^m) (k+2)))
      (geom_two_sum_le (k+2))
  have hMpos : (0:ℝ) < (layerGrid k:ℝ) := by
    exact_mod_cast (layerGrid_pos k)
  have hMne : (layerGrid k:ℝ) ≠ 0 := hMpos.ne'
  have hM2ne : ((layerGrid k:ℝ)^2) ≠ 0 := by positivity
  have hεsum : ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * (2*Real.pi*Real.sqrt
        ((∑ i, w i*layerPayoff f (l:ℕ) i)*(1-∑ i, w i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
        +Real.pi^2/(layerGrid k:ℝ)^2)
      ≤ 4*Real.pi*((k+2:ℕ):ℝ)/(layerGrid k:ℝ)
        +Real.pi^2*(2:ℝ)^(k+2)/(layerGrid k:ℝ)^2 := by
    have hdist : ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * (2*Real.pi*Real.sqrt
          ((∑ i, w i*layerPayoff f (l:ℕ) i)*(1-∑ i, w i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
          +Real.pi^2/(layerGrid k:ℝ)^2)
        = (2*Real.pi/(layerGrid k:ℝ)) * ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * Real.sqrt
            ((∑ i, w i*layerPayoff f (l:ℕ) i)*(1-∑ i, w i*layerPayoff f (l:ℕ) i))
          + (Real.pi^2/(layerGrid k:ℝ)^2) * ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      field_simp [hMne, hM2ne]
    rw [hdist]
    calc (2*Real.pi/(layerGrid k:ℝ)) * ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * Real.sqrt
            ((∑ i, w i*layerPayoff f (l:ℕ) i)*(1-∑ i, w i*layerPayoff f (l:ℕ) i))
          + (Real.pi^2/(layerGrid k:ℝ)^2) * ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ)
        ≤ (2*Real.pi/(layerGrid k:ℝ)) * (((k+2:ℕ):ℝ)*2)
            + (Real.pi^2/(layerGrid k:ℝ)^2) * (2:ℝ)^(k+2) :=
          add_le_add (mul_le_mul_of_nonneg_left hsqrtbound
              (div_nonneg (by positivity) hMpos.le))
            (mul_le_mul_of_nonneg_left hgeom (by positivity))
      _ = 4*Real.pi*((k+2:ℕ):ℝ)/(layerGrid k:ℝ)
            +Real.pi^2*(2:ℝ)^(k+2)/(layerGrid k:ℝ)^2 := by
          field_simp [hMne, hM2ne]
          ring

  have hresid := weighted_layer_residual w hw0 f hf (k+1)
  have hRfin : ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i
      = ∑ l ∈ Finset.range (k+2), (2:ℝ)^l * ∑ i, w i*layerPayoff f l i :=
    Fin.sum_univ_eq_sum_range (fun m : ℕ => (2:ℝ)^m * ∑ i, w i*layerPayoff f m i) (k+2)
  have ht0 : (0:ℝ) ≤ μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i := by
    rw [le_sub_iff_add_le, hRfin, hμ, zero_add]
    exact hresid.1
  have htB : μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i
      ≤ (1:ℝ)/(2:ℝ)^(k+1) := by
    have h1 : μ - ∑ l ∈ Finset.range (k+2), (2:ℝ)^l * ∑ i, w i*layerPayoff f l i
        ≤ (∑ i, w i*(f i)^2)/(2:ℝ)^(k+1) := hresid.2
    have h2 : (∑ i, w i*(f i)^2)/(2:ℝ)^(k+1) ≤ (1:ℝ)/(2:ℝ)^(k+1) :=
      div_le_div_of_nonneg_right hE (by positivity)
    rw [hRfin]
    linarith

  have hdet : ∀ ω : Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k),
      (∀ l : Fin (k+2),
        |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
          - ∑ i, w i*layerPayoff f (l:ℕ) i|
        ≤ 2*Real.pi*Real.sqrt
            ((∑ i, w i*layerPayoff f (l:ℕ) i)*(1-∑ i, w i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
          +Real.pi^2/(layerGrid k:ℝ)^2) →
      |layerEstimate k ω-μ| ≤ (2:ℝ)^(-(k:ℤ)) := by
    intro ω hgood
    have hsumdiff : (∑ l : Fin (k+2), (2:ℝ)^(l:ℕ)
          * meanMedian (layerRepetitions k) (layerGrid k) (ω l))
        - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i
        = ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ)
            * (meanMedian (layerRepetitions k) (layerGrid k) (ω l)
              - ∑ i, w i*layerPayoff f (l:ℕ) i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hsplit : layerEstimate k ω-μ
        = (∑ l : Fin (k+2), (2:ℝ)^(l:ℕ)
            * (meanMedian (layerRepetitions k) (layerGrid k) (ω l)
              - ∑ i, w i*layerPayoff f (l:ℕ) i))
          - (μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i) := by
      rw [← hsumdiff]
      simp only [layerEstimate]
      ring
    calc |layerEstimate k ω-μ|
        = |(∑ l : Fin (k+2), (2:ℝ)^(l:ℕ)
            * (meanMedian (layerRepetitions k) (layerGrid k) (ω l)
              - ∑ i, w i*layerPayoff f (l:ℕ) i))
          - (μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i)| := by rw [hsplit]
      _ ≤ |∑ l : Fin (k+2), (2:ℝ)^(l:ℕ)
            * (meanMedian (layerRepetitions k) (layerGrid k) (ω l)
              - ∑ i, w i*layerPayoff f (l:ℕ) i)|
          + |μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i| := by
            have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
              intro a b
              calc |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
                _ ≤ |a| + |-b| := abs_add_le _ _
                _ = |a| + |b| := by rw [abs_neg]
            exact habs _ _
      _ ≤ ∑ l : Fin (k+2), |(2:ℝ)^(l:ℕ)
            * (meanMedian (layerRepetitions k) (layerGrid k) (ω l)
              - ∑ i, w i*layerPayoff f (l:ℕ) i)|
          + (μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i) := by
            refine add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_
            rw [abs_of_nonneg ht0]
      _ = ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ)
            * |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
              - ∑ i, w i*layerPayoff f (l:ℕ) i|
          + (μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i) := by
            have habsmul : ∀ l : Fin (k+2),
                |(2:ℝ)^(l:ℕ) * (meanMedian (layerRepetitions k) (layerGrid k) (ω l)
                  - ∑ i, w i*layerPayoff f (l:ℕ) i)|
                = (2:ℝ)^(l:ℕ)
                  * |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
                    - ∑ i, w i*layerPayoff f (l:ℕ) i| := by
              intro l
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^(l:ℕ))]
            rw [Finset.sum_congr rfl (fun l _ => habsmul l)]
      _ ≤ ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * (2*Real.pi*Real.sqrt
            ((∑ i, w i*layerPayoff f (l:ℕ) i)*(1-∑ i, w i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
            +Real.pi^2/(layerGrid k:ℝ)^2)
          + (μ - ∑ l : Fin (k+2), (2:ℝ)^(l:ℕ) * ∑ i, w i*layerPayoff f (l:ℕ) i) :=
            add_le_add
              (Finset.sum_le_sum fun l _ =>
                mul_le_mul_of_nonneg_left (hgood l) (by positivity))
              le_rfl
      _ ≤ (4*Real.pi*((k+2:ℕ):ℝ)/(layerGrid k:ℝ)
            +Real.pi^2*(2:ℝ)^(k+2)/(layerGrid k:ℝ)^2)
          + (1:ℝ)/(2:ℝ)^(k+1) :=
            add_le_add hεsum htB
      _ ≤ (2:ℝ)^(-(k:ℤ)) := layered_numeric_tail k

  have hper : ∀ l : Fin (k+2),
      (∑ ω ∈ Finset.univ.filter (fun ω =>
        2*Real.pi*Real.sqrt
          ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
            *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
          +Real.pi^2/(layerGrid k:ℝ)^2
        < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
          - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|),
        (layerLaw k A j f hA hf).prob ω)
      ≤ (2:ℝ)^(2*layerRepetitions k+1)*(1-8/Real.pi^2)^(layerRepetitions k+1) := by
    intro l
    have hmain := quantum_mean_sorted_median_amplification (layerGrid k)
      (layerRepetitions k) (layerGrid_ge_two k) A j (layerPayoff f (l:ℕ)) hA
      (layerPayoff_mem_Icc f hf _)
    simp only [] at hmain
    have htarget : (∑ ω ∈ Finset.univ.filter (fun ω =>
        2*Real.pi*Real.sqrt
          ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
            *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
          +Real.pi^2/(layerGrid k:ℝ)^2
        < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
          - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|),
        (layerLaw k A j f hA hf).prob ω)
        = (meanLaw (layerGrid k) A j (layerPayoff f (l:ℕ)) hA
            (layerPayoff_mem_Icc f hf _) (layerGrid_ge_two k)).probEvent
          (fun u => 2*Real.pi*Real.sqrt
            ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
              *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
            +Real.pi^2/(layerGrid k:ℝ)^2
          < |meanMedian (layerRepetitions k) (layerGrid k) u
            - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|) := by
      calc (∑ ω ∈ Finset.univ.filter (fun ω =>
          2*Real.pi*Real.sqrt
            ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
              *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
            +Real.pi^2/(layerGrid k:ℝ)^2
          < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
            - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|),
          (layerLaw k A j f hA hf).prob ω)
          = ∑ u ∈ Finset.univ.filter (fun u =>
              2*Real.pi*Real.sqrt
                ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
                  *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
                +Real.pi^2/(layerGrid k:ℝ)^2
              < |meanMedian (layerRepetitions k) (layerGrid k) u
                - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|),
              (layerTrialLaw k A j f hA hf l).prob u :=
            layerLaw_marginal k A j f hA hf l (fun u =>
              2*Real.pi*Real.sqrt
                ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
                  *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
                +Real.pi^2/(layerGrid k:ℝ)^2
              < |meanMedian (layerRepetitions k) (layerGrid k) u
                - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|)
        _ = (meanLaw (layerGrid k) A j (layerPayoff f (l:ℕ)) hA
            (layerPayoff_mem_Icc f hf _) (layerGrid_ge_two k)).probEvent
            (fun u => 2*Real.pi*Real.sqrt
              ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
                *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
              +Real.pi^2/(layerGrid k:ℝ)^2
            < |meanMedian (layerRepetitions k) (layerGrid k) u
              - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|) := by
            simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent]
            exact Finset.sum_congr rfl fun u _ =>
              layerTrialLaw_probOf k A j f hA hf l u
    rw [htarget]
    exact hmain

  have hub := fintype_union_bound_mass ((layerLaw k A j f hA hf).prob)
    (fun ω => (layerLaw k A j f hA hf).nonneg ω)
    (A := fun (l : Fin (k+2)) ω =>
      2*Real.pi*Real.sqrt
        ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
          *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
        +Real.pi^2/(layerGrid k:ℝ)^2
      < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
        - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|)
  have hsumbound : ∑ l : Fin (k+2),
      (2:ℝ)^(2*layerRepetitions k+1)*(1-8/Real.pi^2)^(layerRepetitions k+1)
      ≤ (2:ℝ)^(-(k:ℤ)) := by
    have hG6 := (layered_mean_computed_parameters k).2.2.2
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, ← mul_assoc]
    push_cast
    exact hG6
  have hunion : (∑ ω ∈ Finset.univ.filter (fun ω => ∃ l : Fin (k+2),
        2*Real.pi*Real.sqrt
          ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
            *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
          +Real.pi^2/(layerGrid k:ℝ)^2
        < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
          - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|),
      (layerLaw k A j f hA hf).prob ω)
      ≤ (2:ℝ)^(-(k:ℤ)) := by
    refine le_trans hub ?_
    exact le_trans (Finset.sum_le_sum fun l _ => hper l) hsumbound

  have hcompl : (∑ ω ∈ Finset.univ.filter (fun ω => ¬∃ l : Fin (k+2),
        2*Real.pi*Real.sqrt
          ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
            *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
          +Real.pi^2/(layerGrid k:ℝ)^2
        < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
          - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|),
      (layerLaw k A j f hA hf).prob ω)
      ≥ 1-(2:ℝ)^(-(k:ℤ)) := by
    have hcombined : ∑ ω ∈ Finset.univ, ((if ∃ l : Fin (k+2),
          2*Real.pi*Real.sqrt
            ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
              *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
            +Real.pi^2/(layerGrid k:ℝ)^2
          < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
            - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|
          then (layerLaw k A j f hA hf).prob ω else 0)
        + (if ¬∃ l : Fin (k+2),
          2*Real.pi*Real.sqrt
            ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
              *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
            +Real.pi^2/(layerGrid k:ℝ)^2
          < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
            - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|
          then (layerLaw k A j f hA hf).prob ω else 0)) = 1 := by
      calc ∑ ω ∈ Finset.univ, ((if ∃ l : Fin (k+2),
              2*Real.pi*Real.sqrt
                ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
                  *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
                +Real.pi^2/(layerGrid k:ℝ)^2
              < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
                - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|
              then (layerLaw k A j f hA hf).prob ω else 0)
            + (if ¬∃ l : Fin (k+2),
              2*Real.pi*Real.sqrt
                ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
                  *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
                +Real.pi^2/(layerGrid k:ℝ)^2
              < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
                - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|
              then (layerLaw k A j f hA hf).prob ω else 0))
          = ∑ ω ∈ Finset.univ, (layerLaw k A j f hA hf).prob ω :=
            Finset.sum_congr rfl fun ω _ => by
              by_cases h : ∃ l : Fin (k+2),
                2*Real.pi*Real.sqrt
                  ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
                    *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
                  +Real.pi^2/(layerGrid k:ℝ)^2
                < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
                  - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|
              <;> simp [h]
        _ = 1 := (layerLaw k A j f hA hf).sum_one
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hcombined
    linarith

  have hsub : Finset.univ.filter (fun ω => ¬∃ l : Fin (k+2),
        2*Real.pi*Real.sqrt
          ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
            *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
          +Real.pi^2/(layerGrid k:ℝ)^2
        < |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
          - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|)
      ⊆ Finset.univ.filter (fun ω => |layerEstimate k ω-μ|≤(2:ℝ)^(-((k:ℤ)))) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hall : ∀ l : Fin (k+2),
        |meanMedian (layerRepetitions k) (layerGrid k) (ω l)
          - ∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i|
        ≤ 2*Real.pi*Real.sqrt
            ((∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i)
              *(1-∑ i, BornProb (ApplyGate A (Ket j)) i*layerPayoff f (l:ℕ) i))/(layerGrid k:ℝ)
            +Real.pi^2/(layerGrid k:ℝ)^2 := by
      intro l
      exact not_lt.mp (not_exists.mp hω.2 l)
    have := hdet ω fun l => by
      rw [hwdef]
      exact hall l
    exact this
  exact le_trans hcompl (Finset.sum_le_sum_of_subset_of_nonneg hsub
    fun ω _ _ => (layerLaw k A j f hA hf).nonneg ω)

/-- Summing `QueryCount` over all layer and repetition circuits gives (k +
2)(2·layerRepetitions(k) + 1)(layerGrid(k) - 1), the explicit ledger for the construction of
[Montanaro2015, Algorithm 2][Montanaro2015]. -/
theorem layered_quantum_mean_actual_query_ledger (k : ℕ) (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) :
    (∑ l : Fin (k+2), ∑ _ : Fin (2*layerRepetitions k+1), QueryCount (countedAECircuit (layerGrid k) (payoffPreparation A (layerPayoff f l.val)) (j,false)))=(k+2)*(2*layerRepetitions k+1)*(layerGrid k-1) := by
  have hterm : ∀ l : Fin (k+2), QueryCount (countedAECircuit (layerGrid k)
      (payoffPreparation A (layerPayoff f l.val)) (j,false)) = layerGrid k - 1 :=
    fun l => (prepared_ae_access_ledger (I := I × Bool) (layerGrid k) (layerGrid_pos k)
      (payoffPreparation A (layerPayoff f l.val)) (j, false)).1
  simp only [hterm, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- For the Hadamard-prepared payoff zero or one half, the mean is 1/4 and second moment is 1/8,
and the layered estimator satisfies the dyadic accuracy guarantee for `k ≥ 1`. This is a
concrete mean-estimation example in the setting of [Montanaro2015]. -/
theorem payoff_hadamard_half_and_layered_consumer :
    let A:=Hadamard; let f : Bool → ℝ:=fun i => if i=false then 0 else 1/2;
    (∑ i, BornProb (ApplyGate A (Ket false)) i*f i)=1/4 ∧
    (∑ i, BornProb (ApplyGate A (Ket false)) i*(f i)^2)=1/8 ∧
    ∀ (k : ℕ) (hk : 1≤k), ∑ ω ∈ Finset.univ.filter (fun ω => |layerEstimate k ω-1/4|≤(2:ℝ)^(-((k:ℤ)))), (layerLaw k A false f hadamard_unitary (by intro i; cases i <;> norm_num [f])).prob ω ≥ 1-(2:ℝ)^(-((k:ℤ))) := by
  have hstate : ∀ i : Bool, ApplyGate Hadamard (Ket false) i = ((Real.sqrt 2 : ℂ))⁻¹ := by
    intro i
    rw [applyGate_eq_mulVec_ket, hadamard_apply_false]
  have hbp : ∀ i : Bool, BornProb (ApplyGate Hadamard (Ket false)) i = 1/2 := by
    intro i
    show ‖ApplyGate Hadamard (Ket false) i‖^2 = 1/2
    rw [hstate i, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ Real.sqrt 2), inv_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  (try dsimp only)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.sum_bool, hbp false, hbp true]
    norm_num
  · rw [Fintype.sum_bool, hbp false, hbp true]
    norm_num
  · intro k hk
    have hmean : (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i
        * (if i = false then 0 else 1/2)) = 1/4 := by
      rw [Fintype.sum_bool, hbp false, hbp true]
      norm_num
    have hsecond : (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i
        * (if i = false then 0 else 1/2)^2) = 1/8 := by
      rw [Fintype.sum_bool, hbp false, hbp true]
      norm_num
    have hmain := layered_quantum_mean_actual_guarantee k hk Hadamard false
      (fun i => if i=false then 0 else 1/2) hadamard_unitary
      (by intro i; cases i <;> norm_num) (by rw [hsecond]; norm_num)
    have hmain' := hmain
    rw [show (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i
        * (if i = false then 0 else 1/2)) = 1/4 from hmean] at hmain'
    exact hmain'

end Qatlib.Concepts.MonteCarloMean.LayeredMean
