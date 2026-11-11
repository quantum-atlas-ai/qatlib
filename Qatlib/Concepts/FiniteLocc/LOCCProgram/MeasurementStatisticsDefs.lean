/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatisticsDefs
import Qatlib.Concepts.ShadowModels.ShadowChannel.StatisticalConfidenceDefs

/-!
# Finite measurement record laws and moments

This module defines means, variances, second and third central moments, and centered statistics
for finite record distributions. It proves factorization of expectations at distinct positions
of independent POVM samples and supplies finite index equivalences for pairs and triples. The
underlying quantum measurement formalism is described in [Wilde2017].

`ensembleOutcomeLaw` mixes the outcome laws of a family of POVMs, while `ensembleRecordLaw` is
the product of the setting law and that mixed outcome law. The module also defines independent
ensemble samples, U-statistic expectation and tuple-deviation data, and a law concentrated on
constant record sequences.

## Main statements

* `centred_mean_zero`: centered statistics have zero expectation.
* `sample_expect_triple`: expectations factor at three pairwise distinct sample positions.
* `UStatisticDeviationBound`: bounds deviations uniformly over injective index tuples.
* `coincidingRecordLaw`: models repeated copies of one sampled outcome.

## References

* [Wilde, 2017][Wilde2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

/-- The expectation of a real-valued record statistic under a finite distribution. -/
noncomputable def recordMean (p : FinDist O) (h : O → ℝ) : ℝ := p.expect h

/-- The variance of a real-valued record statistic under a finite distribution. -/
noncomputable def recordVariance (p : FinDist O) (h : O → ℝ) : ℝ := p.variance h

/-- The expectation of the square of a record statistic. -/
noncomputable def recordSecondMoment (p : FinDist O) (h : O → ℝ) : ℝ :=
  p.expect (fun x => (h x) ^ 2)

/-- The third central moment of a record statistic, defined as the expected cube of its
deviation from the mean. -/
noncomputable def recordThirdCentralMoment (p : FinDist O) (h : O → ℝ) : ℝ :=
  p.expect (fun x => (h x - p.expect h) ^ 3)

/-- The expectation of the absolute value of a record statistic. -/
noncomputable def recordAbsoluteMean (p : FinDist O) (h : O → ℝ) : ℝ :=
  p.expect (fun x => |h x|)

/-- Subtracts the mean of a record statistic from its value at a specified outcome. -/
noncomputable def centredValue (p : FinDist O) (h : O → ℝ) (x : O) : ℝ :=
  h x - p.expect h

/-- A statistic centered by its finite-distribution mean has expectation zero. -/
theorem centred_mean_zero (p : FinDist O) (h : O → ℝ) :
    p.expect (centredValue p h) = 0 := by
  have h1 : p.expect (centredValue p h) = p.expect (fun x => h x - p.expect h) := rfl
  rw [h1]
  simpa [FinDist.expect] using (FinDist.sum_sub_mean p h)

/-- Maps the two indices of `Fin 2` to `i` and `j`, respectively. -/
def pairIndex {n : ℕ} (i j : Fin n) : Fin 2 → Fin n :=
  fun t => if t = 0 then i else j

/-- Maps the three indices of `Fin 3` to `i`, `j`, and `l`, respectively. -/
def tripleIndex {n : ℕ} (i j l : Fin n) : Fin 3 → Fin n :=
  fun t => if t = 0 then i else if t = 1 then j else l

/-- The first entry of `pairIndex i j` is `i`. -/
theorem pairIndex_zero {n : ℕ} (i j : Fin n) : pairIndex i j 0 = i := by
  simp [pairIndex]

/-- The second entry of `pairIndex i j` is `j`. -/
theorem pairIndex_one {n : ℕ} (i j : Fin n) : pairIndex i j 1 = j := by
  simp [pairIndex]

/-- The first entry of `tripleIndex i j l` is `i`. -/
theorem tripleIndex_zero {n : ℕ} (i j l : Fin n) : tripleIndex i j l 0 = i := by
  simp [tripleIndex]

/-- The second entry of `tripleIndex i j l` is `j`. -/
theorem tripleIndex_one {n : ℕ} (i j l : Fin n) : tripleIndex i j l 1 = j := by
  simp [tripleIndex]

/-- The third entry of `tripleIndex i j l` is `l`. -/
theorem tripleIndex_two {n : ℕ} (i j l : Fin n) : tripleIndex i j l 2 = l := by
  simp [tripleIndex]

/-- The two-position index map is injective when its two selected indices are distinct. -/
theorem pairIndex_injective {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (pairIndex i j) := by
  intro a b hab
  have hcases : ∀ t : Fin 2, (pairIndex i j t = i ∧ t = 0) ∨ (pairIndex i j t = j ∧ t = 1) := by
    intro t
    rcases t with ⟨k, hk⟩
    interval_cases k
    · exact Or.inl ⟨pairIndex_zero i j, rfl⟩
    · exact Or.inr ⟨pairIndex_one i j, rfl⟩
  rcases hcases a with ⟨ha, hka⟩ | ⟨ha, hka⟩
  · rcases hcases b with ⟨hb, hkb⟩ | ⟨hb, hkb⟩
    · exact hka.trans hkb.symm
    · exact absurd (hij (ha.symm.trans (hab.trans hb))) (by simp)
  · rcases hcases b with ⟨hb, hkb⟩ | ⟨hb, hkb⟩
    · exact absurd (hij ((ha.symm.trans (hab.trans hb)).symm)) (by simp)
    · exact hka.trans hkb.symm

/-- The three-position index map is injective when its selected indices are pairwise distinct. -/
theorem tripleIndex_injective {n : ℕ} {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    Function.Injective (tripleIndex i j l) := by
  intro a b hab
  have hcases : ∀ t : Fin 3,
      (tripleIndex i j l t = i ∧ t = 0) ∨ (tripleIndex i j l t = j ∧ t = 1)
        ∨ (tripleIndex i j l t = l ∧ t = 2) := by
    intro t
    rcases t with ⟨k, hk⟩
    interval_cases k
    · exact Or.inl ⟨by simp [tripleIndex], rfl⟩
    · exact Or.inr (Or.inl ⟨by simp [tripleIndex], rfl⟩)
    · exact Or.inr (Or.inr ⟨by simp [tripleIndex], rfl⟩)
  rcases hcases a with ⟨ha, hka⟩ | ⟨ha, hka⟩ | ⟨ha, hka⟩
  · rcases hcases b with ⟨hb, hkb⟩ | ⟨hb, hkb⟩ | ⟨hb, hkb⟩
    · exact hka.trans hkb.symm
    · exact absurd (hij (ha.symm.trans (hab.trans hb))) (by simp)
    · exact absurd (hil (ha.symm.trans (hab.trans hb))) (by simp)
  · rcases hcases b with ⟨hb, hkb⟩ | ⟨hb, hkb⟩ | ⟨hb, hkb⟩
    · exact absurd (hij ((ha.symm.trans (hab.trans hb)).symm)) (by simp)
    · exact hka.trans hkb.symm
    · exact absurd (hjl (ha.symm.trans (hab.trans hb))) (by simp)
  · rcases hcases b with ⟨hb, hkb⟩ | ⟨hb, hkb⟩ | ⟨hb, hkb⟩
    · exact absurd (hil ((ha.symm.trans (hab.trans hb)).symm)) (by simp)
    · exact absurd (hjl ((ha.symm.trans (hab.trans hb)).symm)) (by simp)
    · exact hka.trans hkb.symm

/-- Identifies functions on `Fin 2` with ordered pairs of their values. -/
def finTwoEquiv {O : Type} : ((Fin 2 → O) ≃ (O × O)) where
  toFun y := (y 0, y 1)
  invFun p := fun t => if t = 0 then p.1 else p.2
  left_inv y := by
    funext t
    rcases t with ⟨k, hk⟩
    interval_cases k <;> simp
  right_inv p := by
    cases p
    rfl

/-- Identifies functions on `Fin 3` with triples represented as a value paired with a pair. -/
def finThreeEquiv {O : Type} : ((Fin 3 → O) ≃ (O × (O × O))) where
  toFun y := (y 0, (y 1, y 2))
  invFun p := fun t => if t = 0 then p.1 else if t = 1 then p.2.1 else p.2.2
  left_inv y := by
    funext t
    rcases t with ⟨k, hk⟩
    interval_cases k <;> simp
  right_inv p := by
    cases p with
    | mk a bc =>
      cases bc with
      | mk b c => simp

/-- The probability-weighted sum of a product over two independent outcomes factors into the
product of the two weighted sums. -/
theorem productLaw_expect_two {O : Type} [Fintype O] (p : FinDist O) (f g : O → ℝ) :
    (∑ y : (Fin 2 → O), (p.prob (y 0) * p.prob (y 1)) * (f (y 0) * g (y 1)))
      = (∑ x, p.prob x * f x) * (∑ x, p.prob x * g x) := by
  have h1 : (∑ y : (Fin 2 → O), (p.prob (y 0) * p.prob (y 1)) * (f (y 0) * g (y 1)))
      = ∑ pp : O × O, (p.prob pp.1 * p.prob pp.2) * (f pp.1 * g pp.2) := by
    refine Equiv.sum_comp finTwoEquiv
      (fun pp : O × O => (p.prob pp.1 * p.prob pp.2) * (f pp.1 * g pp.2))
  rw [h1, Fintype.sum_prod_type]
  calc (∑ a : O, ∑ b : O, (p.prob a * p.prob b) * (f a * g b))
      = ∑ a : O, (p.prob a * f a) * ∑ b : O, (p.prob b * g b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        calc (∑ b : O, (p.prob a * p.prob b) * (f a * g b))
            = ∑ b : O, (p.prob a * f a) * (p.prob b * g b) := by
              refine Finset.sum_congr rfl fun b _ => ?_
              ring
          _ = (p.prob a * f a) * ∑ b : O, (p.prob b * g b) :=
            (Finset.mul_sum (Finset.univ) (fun b => p.prob b * g b) (p.prob a * f a)).symm
    _ = (∑ a : O, p.prob a * f a) * ∑ b : O, (p.prob b * g b) :=
            (Finset.sum_mul (Finset.univ) (fun a => p.prob a * f a)
              (∑ b : O, (p.prob b * g b))).symm

/-- The probability-weighted sum of a product over three independent outcomes factors into the
product of the three weighted sums. -/
theorem productLaw_expect_three {O : Type} [Fintype O] (p : FinDist O)
    (f g h : O → ℝ) :
    (∑ y : (Fin 3 → O), (p.prob (y 0) * p.prob (y 1) * p.prob (y 2))
        * (f (y 0) * g (y 1) * h (y 2)))
      = (∑ x, p.prob x * f x) * (∑ x, p.prob x * g x) * (∑ x, p.prob x * h x) := by
  have h2 : (∑ bc : O × O, (p.prob bc.1 * p.prob bc.2) * (g bc.1 * h bc.2))
      = (∑ b : O, p.prob b * g b) * (∑ c : O, p.prob c * h c) := by
    calc (∑ bc : O × O, (p.prob bc.1 * p.prob bc.2) * (g bc.1 * h bc.2))
        = ∑ b : O, ∑ c : O, (p.prob b * p.prob c) * (g b * h c) := Fintype.sum_prod_type _
      _ = ∑ b : O, (p.prob b * g b) * ∑ c : O, (p.prob c * h c) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        calc (∑ c : O, (p.prob b * p.prob c) * (g b * h c))
            = ∑ c : O, (p.prob b * g b) * (p.prob c * h c) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              ring
          _ = (p.prob b * g b) * ∑ c : O, (p.prob c * h c) :=
            (Finset.mul_sum (Finset.univ) (fun c => p.prob c * h c) (p.prob b * g b)).symm
      _ = (∑ b : O, p.prob b * g b) * ∑ c : O, (p.prob c * h c) :=
        (Finset.sum_mul (Finset.univ) (fun b => p.prob b * g b)
          (∑ c : O, (p.prob c * h c))).symm
  have h1 : (∑ y : (Fin 3 → O), (p.prob (y 0) * p.prob (y 1) * p.prob (y 2))
        * (f (y 0) * g (y 1) * h (y 2)))
      = ∑ pp : O × (O × O), (p.prob pp.1 * p.prob pp.2.1 * p.prob pp.2.2)
        * (f pp.1 * g pp.2.1 * h pp.2.2) := by
    refine Equiv.sum_comp finThreeEquiv
      (fun pp : O × (O × O) => (p.prob pp.1 * p.prob pp.2.1 * p.prob pp.2.2)
        * (f pp.1 * g pp.2.1 * h pp.2.2))
  rw [h1, Fintype.sum_prod_type]
  calc (∑ a : O, ∑ bc : O × O, (p.prob a * p.prob bc.1 * p.prob bc.2)
        * (f a * g bc.1 * h bc.2))
      = ∑ a : O, (p.prob a * f a)
        * ∑ bc : O × O, (p.prob bc.1 * p.prob bc.2) * (g bc.1 * h bc.2) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        calc (∑ bc : O × O, (p.prob a * p.prob bc.1 * p.prob bc.2)
              * (f a * g bc.1 * h bc.2))
            = ∑ bc : O × O, (p.prob a * f a)
                * ((p.prob bc.1 * p.prob bc.2) * (g bc.1 * h bc.2)) := by
              refine Finset.sum_congr rfl fun bc _ => ?_
              ring
          _ = (p.prob a * f a) * ∑ bc : O × O, (p.prob bc.1 * p.prob bc.2)
                * (g bc.1 * h bc.2) :=
            (Finset.mul_sum (Finset.univ : Finset (O × O))
              (fun bc : O × O => (p.prob bc.1 * p.prob bc.2) * (g bc.1 * h bc.2))
              (p.prob a * f a)).symm
    _ = ∑ a : O, (p.prob a * f a)
        * ((∑ b : O, p.prob b * g b) * (∑ c : O, p.prob c * h c)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [h2]
    _ = ((∑ a : O, p.prob a * f a) * (∑ b : O, p.prob b * g b))
        * (∑ c : O, p.prob c * h c) := by
        have hab := Finset.sum_mul (Finset.univ) (fun a => p.prob a * f a)
          ((∑ b : O, p.prob b * g b) * (∑ c : O, p.prob c * h c))
        rw [← hab]
        ring

/-- At distinct positions of independent POVM samples, the expectation of a product factors into
the two single-record expectations. -/
theorem sample_expect_pair (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (i j : Fin n) (hij : i ≠ j) (f g : O → ℝ) :
    (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => f (ω i) * g (ω j))
      = (∑ x, (povmRecordLaw E ρ hρ).prob x * f x)
          * (∑ x, (povmRecordLaw E ρ hρ).prob x * g x) := by
  classical
  have h := povm_joint_expect (povmRecordLaw E ρ hρ) (pairIndex i j)
    (pairIndex_injective hij) (fun y : (Fin 2 → O) => f (y 0) * g (y 1))
  have hL : (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => f (ω i) * g (ω j))
      = (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
          * (f (ω (pairIndex i j 0)) * g (ω (pairIndex i j 1)))) := by
    show (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
        * (f (ω i) * g (ω j))) = _
    simp only [pairIndex_zero, pairIndex_one]
  rw [hL, h]
  have hprod : ∀ y : (Fin 2 → O),
      (∏ t : Fin 2, (povmRecordLaw E ρ hρ).prob (y t))
        = (povmRecordLaw E ρ hρ).prob (y 0) * (povmRecordLaw E ρ hρ).prob (y 1) := by
    intro y
    rw [Fin.prod_univ_two]
  have hconv : (∑ y : (Fin 2 → O), (∏ t : Fin 2, (povmRecordLaw E ρ hρ).prob (y t))
        * (f (y 0) * g (y 1)))
      = ∑ y : (Fin 2 → O), ((povmRecordLaw E ρ hρ).prob (y 0)
        * (povmRecordLaw E ρ hρ).prob (y 1)) * (f (y 0) * g (y 1)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hprod]
  rw [hconv]
  exact productLaw_expect_two (povmRecordLaw E ρ hρ) f g

/-- At distinct sample positions, the expectation of a squared statistic times another statistic
factors into its second moment and the other's mean. -/
theorem sample_expect_pair_sq (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (i j : Fin n) (hij : i ≠ j) (f g : O → ℝ) :
    (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => (f (ω i)) ^ 2 * g (ω j))
      = (∑ x, (povmRecordLaw E ρ hρ).prob x * (f x) ^ 2)
          * (∑ x, (povmRecordLaw E ρ hρ).prob x * g x) := by
  classical
  have h := povm_joint_expect (povmRecordLaw E ρ hρ) (pairIndex i j)
    (pairIndex_injective hij) (fun y : (Fin 2 → O) => (f (y 0)) ^ 2 * g (y 1))
  have hL : (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => (f (ω i)) ^ 2 * g (ω j))
      = (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
          * ((f (ω (pairIndex i j 0))) ^ 2 * g (ω (pairIndex i j 1)))) := by
    show (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
        * ((f (ω i)) ^ 2 * g (ω j))) = _
    simp only [pairIndex_zero, pairIndex_one]
  rw [hL, h]
  have hprod : ∀ y : (Fin 2 → O),
      (∏ t : Fin 2, (povmRecordLaw E ρ hρ).prob (y t))
        = (povmRecordLaw E ρ hρ).prob (y 0) * (povmRecordLaw E ρ hρ).prob (y 1) := by
    intro y
    rw [Fin.prod_univ_two]
  have hconv : (∑ y : (Fin 2 → O), (∏ t : Fin 2, (povmRecordLaw E ρ hρ).prob (y t))
        * ((f (y 0)) ^ 2 * g (y 1)))
      = ∑ y : (Fin 2 → O), ((povmRecordLaw E ρ hρ).prob (y 0)
        * (povmRecordLaw E ρ hρ).prob (y 1)) * ((f (y 0)) ^ 2 * g (y 1)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hprod]
  rw [hconv]
  exact productLaw_expect_two (povmRecordLaw E ρ hρ) (fun x => (f x) ^ 2) g

/-- At pairwise distinct positions of independent POVM samples, the expectation of a triple
product factors into three single-record expectations. -/
theorem sample_expect_triple (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (f g h : O → ℝ) :
    (povmSampleLaw E ρ hρ).expect
        (fun ω : (Fin n → O) => f (ω i) * g (ω j) * h (ω l))
      = (∑ x, (povmRecordLaw E ρ hρ).prob x * f x)
          * (∑ x, (povmRecordLaw E ρ hρ).prob x * g x)
          * (∑ x, (povmRecordLaw E ρ hρ).prob x * h x) := by
  classical
  have hj := povm_joint_expect (povmRecordLaw E ρ hρ) (tripleIndex i j l)
    (tripleIndex_injective hij hil hjl)
    (fun y : (Fin 3 → O) => f (y 0) * g (y 1) * h (y 2))
  have hL : (povmSampleLaw E ρ hρ).expect
        (fun ω : (Fin n → O) => f (ω i) * g (ω j) * h (ω l))
      = (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
          * (f (ω (tripleIndex i j l 0)) * g (ω (tripleIndex i j l 1))
            * h (ω (tripleIndex i j l 2)))) := by
    show (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
        * (f (ω i) * g (ω j) * h (ω l))) = _
    simp only [tripleIndex_zero, tripleIndex_one, tripleIndex_two]
  rw [hL, hj]
  have hprod : ∀ y : (Fin 3 → O), (∏ t : Fin 3, (povmRecordLaw E ρ hρ).prob (y t))
      = (povmRecordLaw E ρ hρ).prob (y 0) * (povmRecordLaw E ρ hρ).prob (y 1)
        * (povmRecordLaw E ρ hρ).prob (y 2) := by
    intro y
    rw [Fin.prod_univ_succ, Fin.prod_univ_two, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring
  have hconv : (∑ y : (Fin 3 → O), (∏ t : Fin 3, (povmRecordLaw E ρ hρ).prob (y t))
        * (f (y 0) * g (y 1) * h (y 2)))
      = ∑ y : (Fin 3 → O), ((povmRecordLaw E ρ hρ).prob (y 0)
        * (povmRecordLaw E ρ hρ).prob (y 1) * (povmRecordLaw E ρ hρ).prob (y 2))
        * (f (y 0) * g (y 1) * h (y 2)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hprod]
  rw [hconv]
  exact productLaw_expect_three (povmRecordLaw E ρ hρ) f g h

/-- The expectation of a statistic at any one POVM sample position equals its single-record
expectation. -/
theorem sample_expect_single (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (i : Fin n) (f : O → ℝ) :
    (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => f (ω i))
      = ∑ x, (povmRecordLaw E ρ hρ).prob x * f x := by
  show (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω * f (ω i)) = _
  exact FinDist.expect_coord (povmRecordLaw E ρ hρ) i f

/-- The product of two finite sums equals the double sum of their pairwise products. -/
theorem productLaw_sum_prod {n : ℕ} (c d : Fin n → ℝ) :
    (∑ i : Fin n, c i) * (∑ j : Fin n, d j)
      = ∑ i : Fin n, ∑ j : Fin n, c i * d j := by
  calc (∑ i : Fin n, c i) * (∑ j : Fin n, d j)
      = ∑ i : Fin n, c i * (∑ j : Fin n, d j) := by rw [Finset.sum_mul]
    _ = ∑ i : Fin n, ∑ j : Fin n, c i * d j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]

/-- The outcome distribution obtained by mixing the POVM outcome laws with setting probabilities
from `q`. -/
noncomputable def ensembleOutcomeLaw {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) : FinDist O where
  prob x := ∑ s, q.prob s * (povmRecordLaw (E s) ρ hρ).prob x
  nonneg x := Finset.sum_nonneg fun s _ =>
    mul_nonneg (q.nonneg s) ((povmRecordLaw (E s) ρ hρ).nonneg x)
  sum_one := by
    calc (∑ x, ∑ s, q.prob s * (povmRecordLaw (E s) ρ hρ).prob x)
        = ∑ s, ∑ x, q.prob s * (povmRecordLaw (E s) ρ hρ).prob x := Finset.sum_comm
      _ = ∑ s, q.prob s * (∑ x, (povmRecordLaw (E s) ρ hρ).prob x) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ s, q.prob s * 1 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [(povmRecordLaw (E s) ρ hρ).sum_one]
      _ = 1 := by
          rw [← Finset.sum_mul, q.sum_one, mul_one]

/-- The product distribution on settings and outcomes with mass `q.prob s` times the mixed
outcome probability. -/
noncomputable def ensembleRecordLaw {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    FinDist (Fin m × O) where
  prob st := q.prob st.1 * (ensembleOutcomeLaw E q ρ hρ).prob st.2
  nonneg st := mul_nonneg (q.nonneg st.1) ((ensembleOutcomeLaw E q ρ hρ).nonneg st.2)
  sum_one := by
    calc (∑ st : (Fin m × O), q.prob st.1 * (ensembleOutcomeLaw E q ρ hρ).prob st.2)
        = ∑ s : Fin m, ∑ x : O,
            q.prob s * (ensembleOutcomeLaw E q ρ hρ).prob x := Fintype.sum_prod_type _
      _ = ∑ s : Fin m, q.prob s * 1 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.mul_sum, (ensembleOutcomeLaw E q ρ hρ).sum_one, mul_one]
      _ = 1 := by
          rw [← Finset.sum_mul, q.sum_one, mul_one]

/-- The expectation of a record statistic under the mixed ensemble outcome law. -/
noncomputable def ensembleMean {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ) : ℝ :=
  (ensembleOutcomeLaw E q ρ hρ).expect h

/-- The variance of a record statistic under the mixed ensemble outcome law. -/
noncomputable def ensembleVariance {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ) : ℝ :=
  (ensembleOutcomeLaw E q ρ hρ).variance h

/-- The expectation of a record statistic for the POVM at a specified setting. -/
noncomputable def settingMean {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ)
    (s : Fin m) : ℝ :=
  (povmRecordLaw (E s) ρ hρ).expect h

/-- The variance of a record statistic for the POVM at a specified setting. -/
noncomputable def settingVariance {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ)
    (s : Fin m) : ℝ :=
  (povmRecordLaw (E s) ρ hρ).variance h

/-- The second moment of a record statistic for the POVM at a specified setting. -/
noncomputable def settingSecondMoment {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ)
    (s : Fin m) : ℝ :=
  (povmRecordLaw (E s) ρ hρ).expect (fun x => (h x) ^ 2)

/-- The second moment of a record statistic under the mixed ensemble outcome law. -/
noncomputable def ensembleSecondMoment {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ) : ℝ :=
  (ensembleOutcomeLaw E q ρ hρ).expect (fun x => (h x) ^ 2)

/-- The product distribution of independent records drawn from the ensemble outcome law. -/
noncomputable def ensembleSampleLaw {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {n : ℕ} : FinDist (Fin n → O) where
  prob ω := (ensembleOutcomeLaw E q ρ hρ).probOf ω
  nonneg ω := Finset.prod_nonneg fun i _ => (ensembleOutcomeLaw E q ρ hρ).nonneg _
  sum_one := (ensembleOutcomeLaw E q ρ hρ).sum_probOf n

/-- The expectation of the kernel sum over injective index tuples, divided by the number of
distinct tuples. -/
noncomputable def uStatisticExpectation {n k : ℕ} (q : FinDist (Fin n → O))
    (h : (Fin k → O) → ℝ) : ℝ :=
  (∑ ω : (Fin n → O), q.prob ω
      * (∑ t : (Fin k → Fin n),
          (if Function.Injective t then h (fun s => ω (t s)) else 0)))
    / ((distinctTupleCount n k : ℕ) : ℝ)

/-- The U-statistic expectation minus the kernel mean under the reference product law. -/
noncomputable def uStatisticBias {n k : ℕ} (q : FinDist (Fin n → O)) (p : FinDist O)
    (h : (Fin k → O) → ℝ) : ℝ :=
  uStatisticExpectation q h - kernelMeanK p h

/-- The expected kernel value at a specified index tuple minus the kernel mean under the
reference product law. -/
noncomputable def uStatisticTupleDeviation {n k : ℕ} (q : FinDist (Fin n → O))
    (p : FinDist O) (h : (Fin k → O) → ℝ) (t : (Fin k → Fin n)) : ℝ :=
  (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s))) - kernelMeanK p h

/-- The condition that the absolute expected-kernel deviation is at most `Δ` for every injective
index tuple. -/
def UStatisticDeviationBound {n k : ℕ} (q : FinDist (Fin n → O)) (p : FinDist O)
    (h : (Fin k → O) → ℝ) (Δ : ℝ) : Prop :=
  ∀ t : (Fin k → Fin n), Function.Injective t →
    |uStatisticTupleDeviation q p h t| ≤ Δ

/-- Summing the indicator of injectivity over all index maps gives `distinctTupleCount n k`. -/
theorem distinctTupleCount_indicator (n k : ℕ) :
    (∑ t : (Fin k → Fin n), (if Function.Injective t then (1 : ℕ) else 0))
      = distinctTupleCount n k := by
  classical
  have h1 : (∑ t : (Fin k → Fin n), (if Function.Injective t then (1 : ℕ) else 0))
      = ∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)).filter
          (fun t => Function.Injective t), (1 : ℕ) := by
    rw [← Finset.sum_filter]
  rw [h1, Finset.sum_const, nsmul_eq_mul]
  simp [distinctTupleCount]

/-- The distribution on nonempty record sequences concentrated on constant sequences, with the
common outcome distributed according to `p`. -/
noncomputable def coincidingRecordLaw {m : ℕ} (p : FinDist O) :
    FinDist (Fin (m+1) → O) where
  prob ω := if ∀ i, ω i = ω 0 then p.prob (ω 0) else 0
  nonneg ω := by
    by_cases h : ∀ i, ω i = ω 0
    · rw [if_pos h]
      exact p.nonneg (ω 0)
    · rw [if_neg h]
  sum_one := by
    classical
    have h1 := Finset.sum_filter (s := (Finset.univ : Finset (Fin (m+1) → O)))
      (p := fun ω => ∀ i, ω i = ω 0) (f := fun ω => p.prob (ω 0))
    rw [← h1, ← p.sum_one]
    refine Finset.sum_bij
      (s := (Finset.univ : Finset (Fin (m+1) → O)).filter
        (fun ω => ∀ i, ω i = ω 0))
      (t := (Finset.univ : Finset O))
      (f := fun ω => p.prob (ω 0)) (g := fun x => p.prob x)
      (fun ω _ => ω 0) ?_ ?_ ?_ ?_
    · intro ω hω
      exact Finset.mem_univ (ω 0)
    · intro a1 ha1 a2 ha2 hEq
      have h1' : a1 = fun _ => a1 0 := by
        funext i
        exact (Finset.mem_filter.mp ha1).2 i
      have h2' : a2 = fun _ => a2 0 := by
        funext i
        exact (Finset.mem_filter.mp ha2).2 i
      have hEq' : a1 0 = a2 0 := by simpa using hEq
      rw [h1', h2', hEq']
    · intro b hb
      refine ⟨fun _ => b, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by intro i; rfl⟩
      · rfl
    · intro a ha
      rfl

end Qatlib.Concepts.FiniteLocc.LOCCProgram
