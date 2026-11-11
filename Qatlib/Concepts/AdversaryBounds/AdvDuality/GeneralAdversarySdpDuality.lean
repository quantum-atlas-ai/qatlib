/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryInstrumentMinimax
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySourceOptimizers

/-!
# Semidefinite duality for weighted adversary bounds

Relates cost-weighted nonnegative adversary matrices, minimax probability families, and positive
semidefinite Gram certificates. `MinimaxGramFeasible` expresses the Gram constraints, while
`MinimaxSdpPrimalFeasible` expresses the matrix-and-weight formulation; explicit transformations
compare their objectives.

An equality-constrained semidefinite program and a strictly feasible point establish
`advAlphaR_eq_minimax`. The word-domain endpoint `adversary_minimax_word_complete` also supplies
optimizers, formalizing the weighted adversary duality of [HoyerLeeSpalek2007].

## Main statements

* `minimaxGram_feasible_iff_value`: characterize a positive feasible Gram objective by the
  minimax value.
* `minimaxSdpPrimalValue_eq_source` and `minimaxSdpDualValue_eq_minimax`: identify the two SDP
  values.
* `advAlphaR_eq_minimax`: equality of weighted nonnegative adversary and minimax values.
* `adversary_minimax_word_complete`: duality and simultaneous optimizer existence on Boolean
  word domains.
* `source_adversary_composition_upper`: a cost-weighted composition upper bound.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib


open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
noncomputable section

/-- A family of positive semidefinite real matrices with constant cost-weighted diagonal sum `t`
and separating-coordinate sums at least one on different-output pairs. -/
def MinimaxGramFeasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (t : ℝ) (Z : K → Matrix X X ℝ) : Prop :=
  (∀ i, (Z i).PosSemidef) ∧
  (∀ x, ∑ i, alpha i * Z i x x = t) ∧
  ∀ x y, f x ≠ f y → 1 ≤ ∑ i, if input x i ≠ input y i then Z i x y else 0
end
noncomputable section
omit [Fintype X] [Fintype K] [DecidableEq K] in

/-- Each entry of a real positive semidefinite matrix is bounded above by the square root of the
product of its corresponding diagonal entries. -/
theorem real_psd_entry_le_sqrt (Z : Matrix X X ℝ) (hZ : Z.PosSemidef) (x y : X) :
    Z x y ≤ Real.sqrt (Z x x * Z y y) := by
  let e : Fin 2 → X := ![x,y]
  have hd := (hZ.submatrix e).det_nonneg
  have hs : Z y x = Z x y := by simpa using! hZ.1.apply x y
  have hsq : (Z x y)^2 ≤ Z x x * Z y y := by
    simpa [Matrix.det_fin_two,Matrix.submatrix,e,hs,pow_two] using! hd
  have hn : 0 ≤ Z x x * Z y y := mul_nonneg hZ.diag_nonneg hZ.diag_nonneg
  have hroot := Real.sq_sqrt hn
  have hroot0 := Real.sqrt_nonneg (Z x x * Z y y)
  nlinarith [sq_nonneg (Z x y + Real.sqrt (Z x x * Z y y))]
end
noncomputable section

/-- The coordinate matrix with entries `(t / alpha i) * Real.sqrt (p x i) * Real.sqrt (p y i)`. -/
def minimaxRankOne (alpha : K → ℝ) (p : X → K → ℝ) (t : ℝ) (i : K) : Matrix X X ℝ :=
  fun x y => (t / alpha i) * (Real.sqrt (p x i) * Real.sqrt (p y i))
end
noncomputable section

/-- With positive costs and positive `t`, a probability family whose different-output minimax
terms are at least `1 / t` yields a feasible Gram family through `minimaxRankOne`. -/
theorem minimaxRankOne_feasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (p : X → K → ℝ) (hp : IsProbabilityFamily p)
    (t : ℝ) (ht : 0 < t)
    (hpair : ∀ x y, f x ≠ f y → 1/t ≤ advMinimaxTerm input alpha p x y) :
    MinimaxGramFeasible input f alpha t (minimaxRankOne alpha p t) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    have h := (Matrix.posSemidef_vecMulVec_self_star (fun x => Real.sqrt (p x i))).smul
      (div_nonneg ht.le (ha i).le)
    simpa [minimaxRankOne,Matrix.vecMulVec,Pi.star_apply] using! h
  · intro x
    calc
      (∑ i, alpha i * minimaxRankOne alpha p t i x x) = ∑ i, t*p x i := by
        apply Finset.sum_congr rfl
        intro i _
        have hs := Real.mul_self_sqrt (hp.1 x i)
        dsimp only [minimaxRankOne]
        rw [hs]
        field_simp [(ha i).ne',ht.ne']
      _ = t := by rw [← Finset.mul_sum,hp.2 x,mul_one]
  · intro x y hxy
    have he : (∑ i, if input x i ≠ input y i then minimaxRankOne alpha p t i x y else 0) =
        t * advMinimaxTerm input alpha p x y := by
      rw [advMinimaxTerm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : input x i ≠ input y i
      · simp only [if_pos hi,minimaxRankOne]
        rw [Real.sqrt_mul (hp.1 x i)]
        ring
      · simp [hi]
    rw [he]
    have h := (div_le_iff₀ ht).mp (hpair x y hxy)
    nlinarith
end
noncomputable section

/-- The family obtained by dividing each cost-weighted Gram diagonal entry by `t`. -/
def minimaxGramProbability (alpha : K → ℝ) (t : ℝ) (Z : K → Matrix X X ℝ) : X → K → ℝ :=
  fun x i => alpha i * Z i x x / t
end
noncomputable section

/-- With positive costs and positive objective, a feasible Gram family gives a probability
family through its normalized diagonal entries. -/
theorem minimaxGramProbability_family (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (t : ℝ) (ht : 0 < t) (Z : K → Matrix X X ℝ)
    (hZ : MinimaxGramFeasible input f alpha t Z) :
    IsProbabilityFamily (minimaxGramProbability alpha t Z) := by
  refine ⟨fun x i => div_nonneg (mul_nonneg (ha i).le (hZ.1 i).diag_nonneg) ht.le,?_⟩
  intro x
  simp only [minimaxGramProbability,← Finset.sum_div,hZ.2.1 x,div_self ht.ne']
end
noncomputable section
omit [Fintype X] in

/-- The probability family extracted from a feasible Gram family with positive costs and
objective has minimax term at least `1 / t` on different-output pairs. -/
theorem minimaxGramProbability_pair (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (t : ℝ) (ht : 0 < t) (Z : K → Matrix X X ℝ)
    (hZ : MinimaxGramFeasible input f alpha t Z) (x y : X) (hxy : f x ≠ f y) :
    1/t ≤ advMinimaxTerm input alpha (minimaxGramProbability alpha t Z) x y := by
  have he (i : K) :
      Real.sqrt (minimaxGramProbability alpha t Z x i * minimaxGramProbability alpha t Z y i) /
        alpha i = Real.sqrt (Z i x x * Z i y y) / t := by
    have ha0 := (ha i).le
    have halg : minimaxGramProbability alpha t Z x i * minimaxGramProbability alpha t Z y i =
        (alpha i / t)^2 * (Z i x x * Z i y y) := by
      dsimp [minimaxGramProbability]
      ring
    rw [halg,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (div_nonneg ha0 ht.le)]
    field_simp [(ha i).ne',ht.ne']
  calc
    1/t ≤ (∑ i, if input x i ≠ input y i then Z i x y else 0)/t :=
      div_le_div_of_nonneg_right (hZ.2.2 x y hxy) ht.le
    _ ≤ ∑ i, if input x i ≠ input y i then Real.sqrt (Z i x x * Z i y y)/t else 0 := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : input x i ≠ input y i
      · simp only [if_pos hi]
        exact div_le_div_of_nonneg_right (real_psd_entry_le_sqrt (Z i) (hZ.1 i) x y) ht.le
      · simp [hi]
    _ = advMinimaxTerm input alpha (minimaxGramProbability alpha t Z) x y := by
      unfold advMinimaxTerm
      apply Finset.sum_congr rfl
      intro i _
      rw [he i]
end
noncomputable section

/-- For positive costs and positive `t`, Gram feasibility is equivalent to the existence of a
probability family with different-output minimax terms at least `1 / t`. -/
theorem minimaxGram_feasible_iff_probability (input : X → K → Bool) (f : X → Bool)
    (alpha : K → ℝ) (ha : ∀ i, 0 < alpha i) (t : ℝ) (ht : 0 < t) :
    (∃ Z, MinimaxGramFeasible input f alpha t Z) ↔
      ∃ p : X → K → ℝ, IsProbabilityFamily p ∧
        ∀ x y, f x ≠ f y → 1/t ≤ advMinimaxTerm input alpha p x y := by
  constructor
  · rintro ⟨Z,hZ⟩
    exact ⟨minimaxGramProbability alpha t Z,
      minimaxGramProbability_family input f alpha ha t ht Z hZ,
      minimaxGramProbability_pair input f alpha ha t ht Z hZ⟩
  · rintro ⟨p,hp,hpair⟩
    exact ⟨minimaxRankOne alpha p t,minimaxRankOne_feasible input f alpha ha p hp t ht hpair⟩
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
variable [DecidableEq X]
noncomputable section

/-- For a nonconstant output function and positive `t`, lower bounds `1 / t` on all
different-output minimax terms imply witness value at most `ENNReal.ofReal t`. -/
theorem minimaxWitnessValue_le_of_pair (input : X → K → Bool) (f : X → Bool)
    (alpha : K → ℝ) (p : X → K → ℝ) (t : ℝ) (ht : 0 < t)
    (hnc : ∃ x y, f x ≠ f y)
    (hpair : ∀ x y, f x ≠ f y → 1/t ≤ advMinimaxTerm input alpha p x y) :
    minimaxWitnessValue input f alpha p ≤ ENNReal.ofReal t := by
  let J := {xy : X × X // f xy.1 ≠ f xy.2}
  haveI : Nonempty J := let ⟨x,y,h⟩ := hnc; ⟨⟨(x,y),h⟩⟩
  unfold minimaxWitnessValue
  apply ENNReal.inv_le_iff_inv_le.mpr
  rw [← ENNReal.ofReal_inv_of_pos ht]
  apply ENNReal.ofReal_le_ofReal
  apply le_ciInf
  intro xy
  simpa only [one_div] using! hpair xy.1.1 xy.1.2 xy.2
end
noncomputable section

/-- With nonnegative costs and positive `t`, a minimax witness value at most `ENNReal.ofReal t`
forces every different-output term to be at least `1 / t`. -/
theorem pair_of_minimaxWitnessValue_le (input : X → K → Bool) (f : X → Bool)
    (alpha : K → ℝ) (ha : ∀ i, 0 ≤ alpha i) (p : X → K → ℝ) (t : ℝ) (ht : 0 < t)
    (hb : minimaxWitnessValue input f alpha p ≤ ENNReal.ofReal t)
    (x y : X) (hxy : f x ≠ f y) : 1/t ≤ advMinimaxTerm input alpha p x y := by
  let J := {xy : X × X // f xy.1 ≠ f xy.2}
  haveI : Nonempty J := ⟨⟨(x,y),hxy⟩⟩
  have hnon : 0 ≤ ⨅ xy : J, advMinimaxTerm input alpha p xy.1.1 xy.1.2 := by
    apply le_ciInf
    intro xy
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact div_nonneg (Real.sqrt_nonneg _) (ha i)
    · exact le_rfl
  have hi := ENNReal.inv_le_iff_inv_le.mp hb
  rw [← ENNReal.ofReal_inv_of_pos ht] at hi
  have hd : 1/t ≤ ⨅ xy : J, advMinimaxTerm input alpha p xy.1.1 xy.1.2 :=
    by simpa only [one_div] using! (ENNReal.ofReal_le_ofReal_iff hnon).mp hi
  exact hd.trans (ciInf_le (Set.finite_range _).bddBelow (⟨(x,y),hxy⟩ : J))
end
noncomputable section

/-- For a nonconstant function, positive costs, a nonempty coordinate type, and positive `t`, a
feasible Gram family exists exactly when the minimax value is at most `ENNReal.ofReal t`. -/
theorem minimaxGram_feasible_iff_value [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (ha : ∀ i, 0 < alpha i)
    (hnc : ∃ x y, f x ≠ f y) (t : ℝ) (ht : 0 < t) :
    (∃ Z, MinimaxGramFeasible input f alpha t Z) ↔ minimaxAlpha input f alpha ≤ ENNReal.ofReal t := by
  rw [minimaxGram_feasible_iff_probability input f alpha ha t ht]
  constructor
  · rintro ⟨p,hp,hpair⟩
    exact (minimax_value_le_witness input f alpha p hp).trans
      (minimaxWitnessValue_le_of_pair input f alpha p t ht hnc hpair)
  · intro hb
    obtain ⟨p,hp⟩ := minimax_optimal_exists input f alpha hnc
    refine ⟨p,hp.1,?_⟩
    exact pair_of_minimaxWitnessValue_le input f alpha (fun i => (ha i).le) p t ht
      (hp.2.trans_le hb)
end
noncomputable section

/-- For a nonconstant Boolean output function with a nonempty coordinate type, the minimax value
is nonzero. -/
theorem minimaxAlpha_ne_zero [Nonempty K] (input : X → K → Bool) (f : X → Bool)
    (alpha : K → ℝ) (hnc : ∃ x y, f x ≠ f y) : minimaxAlpha input f alpha ≠ 0 := by
  obtain ⟨p,hp⟩ := minimax_optimal_exists input f alpha hnc
  rw [← hp.2,minimaxWitnessValue]
  exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
end
noncomputable section

/-- For a nonconstant function with positive costs and finite minimax value, a Gram family
attains its real-valued minimax objective and minimizes all positive feasible objectives. -/
theorem minimaxGram_optimal_exists_of_finite [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (ha : ∀ i, 0 < alpha i)
    (hnc : ∃ x y, f x ≠ f y) (hfin : minimaxAlpha input f alpha ≠ ⊤) :
    ∃ Z, MinimaxGramFeasible input f alpha (minimaxAlpha input f alpha).toReal Z ∧
      ∀ t W, 0 < t → MinimaxGramFeasible input f alpha t W →
        (minimaxAlpha input f alpha).toReal ≤ t := by
  have ht := ENNReal.toReal_pos (minimaxAlpha_ne_zero input f alpha hnc) hfin
  obtain ⟨Z,hZ⟩ := (minimaxGram_feasible_iff_value input f alpha ha hnc _ ht).mpr
    (le_of_eq (ENNReal.ofReal_toReal hfin).symm)
  refine ⟨Z,hZ,?_⟩
  intro t W ht hW
  have hb := (minimaxGram_feasible_iff_value input f alpha ha hnc t ht).mp ⟨W,hW⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal ht.le] using! h
end
noncomputable section

/-- The real matrix equal to twice the all-ones matrix plus the identity. -/
def minimaxGramStrictMatrix : Matrix X X ℝ := (2 : ℝ) • (fun _ _ => 1) + 1
end
noncomputable section

/-- The matrix `minimaxGramStrictMatrix` is positive definite. -/
theorem minimaxGramStrictMatrix_posDef : (minimaxGramStrictMatrix (X := X)).PosDef := by
  have h : (show Matrix X X ℝ from fun _ _ => 1).PosSemidef := by
    simpa only [Matrix.vecMulVec,Pi.star_apply,star_trivial,mul_one] using!
      Matrix.posSemidef_vecMulVec_self_star (fun _ : X => (1 : ℝ))
  exact Matrix.PosDef.posSemidef_add (h.smul (by norm_num : (0 : ℝ) ≤ 2)) Matrix.PosDef.one
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs, the constant Gram family `minimaxGramStrictMatrix` is positive
definite, has weighted diagonal sum `3 * ∑ i, alpha i`, and has different-output separating
sums strictly greater than one. -/
theorem minimaxGram_strict_point (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (hobs : OutputObservable input f) :
    (∀ _ : K, (minimaxGramStrictMatrix (X := X)).PosDef) ∧
    (∀ x : X, ∑ i, alpha i * minimaxGramStrictMatrix (X := X) x x = 3 * ∑ i, alpha i) ∧
    (∀ x y, f x ≠ f y → 1 < ∑ i : K,
      if input x i ≠ input y i then minimaxGramStrictMatrix (X := X) x y else 0) := by
  refine ⟨fun _ => minimaxGramStrictMatrix_posDef,?_,?_⟩
  · intro x
    have hd : minimaxGramStrictMatrix (X := X) x x = 3 := by
      change (2 : ℝ)*1 + (if x = x then 1 else 0) = 3
      rw [if_pos rfl]
      norm_num
    simp_rw [hd]
    rw [← Finset.sum_mul]
    ring
  · intro x y hxy
    have hne : x ≠ y := fun h => hxy (congrArg f h)
    obtain ⟨i,hi⟩ := hobs x y hxy
    have he : minimaxGramStrictMatrix (X := X) x y = 2 := by
      change (2 : ℝ) * 1 + (if x = y then 1 else 0) = 2
      rw [if_neg hne]
      norm_num
    have hh : (2 : ℝ) ≤ ∑ j : K,
        if input x j ≠ input y j then minimaxGramStrictMatrix (X := X) x y else 0 := by
      rw [he]
      have hh := Finset.single_le_sum
        (f := fun j : K => if input x j ≠ input y j then (2 : ℝ) else 0)
        (fun j _ => by change 0 ≤ if input x j ≠ input y j then (2 : ℝ) else 0; split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [if_pos hi] using! hh
    linarith
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs, the constant strict Gram family is feasible at objective `3 * ∑ i,
alpha i`. -/
theorem minimaxGram_strict_feasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (hobs : OutputObservable input f) :
    MinimaxGramFeasible input f alpha (3 * ∑ i, alpha i)
      (fun _ => minimaxGramStrictMatrix (X := X)) := by
  have h := minimaxGram_strict_point input f alpha hobs
  exact ⟨fun i => (h.1 i).posSemidef,h.2.1,fun x y hxy => (h.2.2 x y hxy).le⟩
end
noncomputable section

/-- For a nonconstant function with positive costs and nonempty coordinate type, the minimax
value is finite exactly when outputs are observable from the input encoding. -/
theorem minimaxAlpha_finite_iff_observable [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (ha : ∀ i, 0 < alpha i)
    (hnc : ∃ x y, f x ≠ f y) : minimaxAlpha input f alpha < ⊤ ↔ OutputObservable input f := by
  constructor
  · intro hfin
    have ht := ENNReal.toReal_pos (minimaxAlpha_ne_zero input f alpha hnc) hfin.ne
    obtain ⟨Z,hZ⟩ := (minimaxGram_feasible_iff_value input f alpha ha hnc _ ht).mpr
      (le_of_eq (ENNReal.ofReal_toReal hfin.ne).symm)
    intro x y hxy
    by_contra hn
    have hn' : ∀ i, input x i = input y i := by
      intro i
      exact not_not.mp (not_exists.mp hn i)
    have h := hZ.2.2 x y hxy
    simp only [hn',ne_eq,not_true_eq_false,↓reduceIte,Finset.sum_const_zero] at h
    norm_num at h
  · intro hobs
    have ht : 0 < 3 * ∑ i, alpha i := mul_pos (by norm_num)
      (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty)
    have hb := (minimaxGram_feasible_iff_value input f alpha ha hnc _ ht).mp
      ⟨_,minimaxGram_strict_feasible input f alpha hobs⟩
    exact hb.trans_lt ENNReal.ofReal_lt_top
end
noncomputable section

/-- For a nonconstant function with observable outputs, positive costs, and nonempty coordinate
type, a Gram family attains the minimax objective and minimizes all positive feasible
objectives. -/
theorem minimaxGram_optimal_exists [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (ha : ∀ i, 0 < alpha i)
    (hnc : ∃ x y, f x ≠ f y) (hobs : OutputObservable input f) :
    ∃ Z, MinimaxGramFeasible input f alpha (minimaxAlpha input f alpha).toReal Z ∧
      ∀ t W, 0 < t → MinimaxGramFeasible input f alpha t W →
        (minimaxAlpha input f alpha).toReal ≤ t := by
  exact minimaxGram_optimal_exists_of_finite input f alpha ha hnc
    ((minimaxAlpha_finite_iff_observable input f alpha ha hnc).mpr hobs).ne
end
noncomputable section

/-- A probability weight and a symmetric entrywise nonnegative matrix vanishing on equal
outputs, with each cost-weighted diagonal matrix minus the corresponding adversary filter
positive semidefinite. -/
def MinimaxSdpPrimalFeasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (w : X → ℝ) (A : Matrix X X ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ (∑ x, w x = 1) ∧ A.IsSymm ∧ (∀ x y, 0 ≤ A x y) ∧
  (∀ x y, f x = f y → A x y = 0) ∧
  ∀ i, (Matrix.diagonal (fun x => alpha i * w x) - genAdvFilter input A i).PosSemidef
end
noncomputable section
omit [DecidableEq X] in

/-- The trace of the product of two real positive semidefinite matrices is nonnegative. -/
theorem real_psd_trace_mul_nonneg (A B : Matrix X X ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ Matrix.trace (A*B) := by
  let HA : HermitianMat X ℝ := ⟨A,hA.1⟩
  let HB : HermitianMat X ℝ := ⟨B,hB.1⟩
  have hh := HermitianMat.inner_ge_zero (A := HA) (B := HB)
    (HermitianMat.zero_le_iff.mpr hA) (HermitianMat.zero_le_iff.mpr hB)
  simpa only [HermitianMat.inner_eq_re_trace,HA,HB,HermitianMat.mat_mk,RCLike.re_to_real] using! hh
end
noncomputable section
omit [DecidableEq K] in

/-- The sum of all entries of a feasible minimax primal matrix is bounded by every feasible Gram
objective. -/
theorem minimaxSdp_weak_duality (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (w : X → ℝ) (A : Matrix X X ℝ) (hA : MinimaxSdpPrimalFeasible input f alpha w A)
    (t : ℝ) (Z : K → Matrix X X ℝ) (hZ : MinimaxGramFeasible input f alpha t Z) :
    (∑ x, ∑ y, A x y) ≤ t := by
  have htrace (i : K) : Matrix.trace (genAdvFilter input A i * Z i) ≤
      ∑ x, alpha i * w x * Z i x x := by
    have h := real_psd_trace_mul_nonneg _ _ (hA.2.2.2.2.2 i) (hZ.1 i)
    rw [Matrix.sub_mul,Matrix.trace_sub] at h
    simpa only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul] using! (sub_nonneg.mp h)
  have hs : (∑ x, ∑ y, A x y) ≤ ∑ i, Matrix.trace (genAdvFilter input A i * Z i) := by
    have he : (∑ i, Matrix.trace (genAdvFilter input A i * Z i)) =
        ∑ x, ∑ y, A x y * (∑ i, if input x i ≠ input y i then Z i x y else 0) := by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hsym : Z i y x = Z i x y := by simpa using! (hZ.1 i).1.apply x y
      change (if input x i ≠ input y i then A x y else 0)*Z i y x =
        A x y*(if input x i ≠ input y i then Z i x y else 0)
      rw [hsym]
      split_ifs <;> ring
    rw [he]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    by_cases hf : f x = f y
    · rw [hA.2.2.2.2.1 x y hf,zero_mul]
    · exact le_mul_of_one_le_right (hA.2.2.2.1 x y) (hZ.2.2 x y hf)
  calc
    (∑ x, ∑ y, A x y) ≤ ∑ i, Matrix.trace (genAdvFilter input A i * Z i) := hs
    _ ≤ ∑ i, ∑ x, alpha i * w x * Z i x x := Finset.sum_le_sum (fun i _ => htrace i)
    _ = ∑ x, w x * (∑ i, alpha i * Z i x x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = t := by simp only [hZ.2.1,← Finset.sum_mul,hA.2.1,one_mul]
end

/-- The absolute real quadratic form of a matrix is bounded by its operator norm times the sum
of squared vector entries. -/
private theorem balancedReal_rayleigh_bound (A : Matrix X X ℝ) (v : X → ℝ) :
    |dotProduct v (A *ᵥ v)| ≤ ‖A‖ * ∑ x, (v x)^2 := by
  let u : EuclideanSpace ℝ X := WithLp.toLp 2 v
  have he : dotProduct v (A *ᵥ v) = inner ℝ u ((EuclideanSpace.equiv X ℝ).symm (A*ᵥu)) := by
    simp [PiLp.inner_apply, RCLike.inner_apply, u, dotProduct, mul_comm]
  rw [he]
  calc
    _ ≤ ‖u‖*‖(EuclideanSpace.equiv X ℝ).symm (A*ᵥu)‖ := by
      simpa only [Real.norm_eq_abs] using!
          norm_inner_le_norm (𝕜 := ℝ) u ((EuclideanSpace.equiv X ℝ).symm (A*ᵥu))
    _ ≤ ‖u‖*(‖A‖*‖u‖) := mul_le_mul_of_nonneg_left (A.l2_opNorm_mulVec u) (norm_nonneg u)
    _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq u]; ring

/-- A Hermitian real matrix on a nonempty finite type possesses a unit vector whose quadratic
form has absolute value equal to its operator norm. -/
private theorem balancedReal_extreme [Nonempty X] (A : Matrix X X ℝ) (hA : A.IsHermitian) :
    ∃ v : X → ℝ, (∑ x, (v x)^2) = 1 ∧ |dotProduct v (A*ᵥv)| = ‖A‖ := by
  classical
  let ev : X → ℝ := hA.eigenvalues
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |ev i|) Finset.univ_nonempty
  have hn : ‖ev‖ = |ev i| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      intro j
      simpa only [Real.norm_eq_abs] using! hi j (Finset.mem_univ j)
    · simpa only [Real.norm_eq_abs] using! norm_le_pi_norm ev i
  have hnorm : ‖A‖ = ‖ev‖ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    change ‖(hA.eigenvectorUnitary : Matrix X X ℝ)*Matrix.diagonal ev*
      (star hA.eigenvectorUnitary : unitary (Matrix X X ℝ))‖ = ‖ev‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  let v : EuclideanSpace ℝ X := hA.eigenvectorBasis i
  have hv : ∑ x, (v x)^2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hA.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have he : A *ᵥ v = ev i • (v : X → ℝ) := hA.mulVec_eigenvectorBasis i
  refine ⟨v, hv, ?_⟩
  rw [he, dotProduct_smul]
  have hs : dotProduct (v : X → ℝ) v = 1 := by simpa only [dotProduct, ← pow_two] using! hv
  rw [hs, smul_eq_mul, mul_one, ← hn, ← hnorm]

/-- An entrywise nonnegative Hermitian real matrix on a nonempty finite type possesses a
nonnegative unit vector whose quadratic form is at least its operator norm. -/
private theorem balancedReal_nonnegative_extreme [Nonempty X] (A : Matrix X X ℝ)
    (hA : A.IsHermitian) (hnn : ∀ x y, 0 ≤ A x y) :
    ∃ δ : X → ℝ, (∀ x, 0 ≤ δ x) ∧ (∑ x, (δ x)^2) = 1 ∧
      ‖A‖ ≤ ∑ x, ∑ y, A x y * δ x * δ y := by
  obtain ⟨v, hv, he⟩ := balancedReal_extreme A hA
  refine ⟨fun x => |v x|, fun x => abs_nonneg _, ?_, ?_⟩
  · simpa only [sq_abs] using! hv
  · rw [← he]
    unfold dotProduct Matrix.mulVec
    simp only [dotProduct, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro x _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro y _
    rw [abs_mul, abs_mul, abs_of_nonneg (hnn x y)]
    exact le_of_eq (by ring)
noncomputable section

/-- If a real Hermitian matrix has norm at most `a`, then `a • 1 - G` is positive semidefinite. -/
theorem real_norm_slack_psd (G : Matrix X X ℝ) (hG : G.IsHermitian) (a : ℝ) (ha : ‖G‖ ≤ a) :
    ((a : ℝ) • (1 : Matrix X X ℝ) - G).PosSemidef := by
  have hh : (a • (1 : Matrix X X ℝ) - G).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro x y
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      star_trivial,Matrix.one_apply]
    have hs : G y x = G x y := by simpa using! hG.apply x y
    rw [hs]
    by_cases h : x = y
    · subst y; rfl
    · rw [if_neg h,if_neg (Ne.symm h)]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro v
  have hb := (le_abs_self _).trans (balancedReal_rayleigh_bound G v)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have he : star v ⬝ᵥ ((a • (1 : Matrix X X ℝ) - G) *ᵥ v) =
      a * (∑ x, (v x)^2) - dotProduct v (G *ᵥ v) := by
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
    change (∑ x, v x*(a*v x - (G *ᵥ v) x)) =
      a*(∑ x, (v x)^2) - ∑ x, v x*(G *ᵥ v) x
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  linarith
end
noncomputable section

/-- The matrix obtained by multiplying each entry `G x y` by the two vector entries `v x` and `v
y`. -/
def sourceAdversaryBalance (G : Matrix X X ℝ) (v : X → ℝ) : Matrix X X ℝ :=
  fun x y => G x y * v x * v y
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- Balancing a feasible cost-weighted nonnegative adversary by a nonnegative unit vector yields
a feasible minimax primal matrix with weights `(v x)^2`. -/
theorem sourceAdversaryBalance_feasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (G : Matrix X X ℝ) (hG : CostAdversaryFeasible input f alpha G)
    (v : X → ℝ) (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∑ x, (v x)^2 = 1) :
    MinimaxSdpPrimalFeasible input f alpha (fun x => (v x)^2) (sourceAdversaryBalance G v) := by
  refine ⟨fun x => sq_nonneg _,hv1,?_,?_,?_,?_⟩
  · ext x y
    have hs : G y x = G x y := congrFun (congrFun hG.1 x) y
    change G y x*v y*v x = G x y*v x*v y
    rw [hs]
    ring
  · intro x y
    exact mul_nonneg (mul_nonneg (hG.2.1 x y) (hv0 x)) (hv0 y)
  · intro x y hxy
    change G x y*v x*v y = 0
    rw [hG.2.2.1 x y hxy,zero_mul,zero_mul]
  · intro i
    have hf : (genAdvFilter input G i).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro x y
      have hs : G y x = G x y := congrFun (congrFun hG.1 x) y
      change star (if input y i ≠ input x i then G y x else 0) =
        if input x i ≠ input y i then G x y else 0
      simp only [star_trivial,hs,ne_comm]
    have hp := (real_norm_slack_psd _ hf (alpha i) (hG.2.2.2 i)).conjTranspose_mul_mul_same
      (Matrix.diagonal v)
    have he : (Matrix.diagonal v)ᴴ * (alpha i • (1 : Matrix X X ℝ) - genAdvFilter input G i) *
        Matrix.diagonal v =
        Matrix.diagonal (fun x => alpha i*(v x)^2) - genAdvFilter input (sourceAdversaryBalance G v) i := by
      ext x y
      simp only [Matrix.diagonal_conjTranspose,star_trivial,Matrix.mul_diagonal,
        Matrix.diagonal_mul]
      change v x*((alpha i)*(if x=y then (1 : ℝ) else 0) -
          (if input x i ≠ input y i then G x y else 0))*v y =
        (if x=y then (alpha i)*(v x)^2 else 0) -
          (if input x i ≠ input y i then G x y*v x*v y else 0)
      by_cases hxy : x=y
      · subst y
        simp only [ne_eq,not_true_eq_false,↓reduceIte]
        ring
      · by_cases hi : input x i ≠ input y i
        · simp only [if_neg hxy,if_pos hi]
          ring
        · simp only [if_neg hxy,if_neg hi]
          ring
    rwa [he] at hp
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- Every nonzero feasible cost-weighted nonnegative adversary yields feasible minimax primal
data whose entry sum is at least its operator norm. -/
theorem sourceAdversary_primal_exists (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (G : Matrix X X ℝ) (hG : CostAdversaryFeasible input f alpha G) (hne : G ≠ 0) :
    ∃ w A, MinimaxSdpPrimalFeasible input f alpha w A ∧ ‖G‖ ≤ ∑ x, ∑ y, A x y := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hne
  letI : Nonempty X := ⟨x⟩
  have hs : G.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro x y
    simpa only [star_trivial] using! congrFun (congrFun hG.1 x) y
  obtain ⟨v,hv0,hv1,hv⟩ := balancedReal_nonnegative_extreme G hs hG.2.1
  exact ⟨fun x => (v x)^2,sourceAdversaryBalance G v,
    sourceAdversaryBalance_feasible input f alpha G hG v hv0 hv1,hv⟩
end
noncomputable section
omit [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] in

/-- A zero diagonal entry of a real positive semidefinite matrix forces the entire corresponding
row to vanish. -/
theorem real_psd_zero_diagonal_row (Z : Matrix X X ℝ) (hZ : Z.PosSemidef)
    (x : X) (hx : Z x x = 0) (y : X) : Z x y = 0 := by
  let e : Fin 2 → X := ![x,y]
  have hd := (hZ.submatrix e).det_nonneg
  have hs : Z y x = Z x y := by simpa using! hZ.1.apply x y
  have hsq : 0 ≤ -(Z x y)^2 := by
    simpa [Matrix.det_fin_two,Matrix.submatrix,e,hs,hx,pow_two] using! hd
  nlinarith [sq_nonneg (Z x y)]
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- For observable outputs, a zero weight in feasible minimax primal data forces the
corresponding matrix row to vanish. -/
theorem minimaxPrimal_zero_weight (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (hobs : OutputObservable input f) (w : X → ℝ) (A : Matrix X X ℝ)
    (hA : MinimaxSdpPrimalFeasible input f alpha w A) (x : X) (hx : w x = 0) (y : X) :
    A x y = 0 := by
  by_cases hf : f x = f y
  · exact hA.2.2.2.2.1 x y hf
  · obtain ⟨i,hi⟩ := hobs x y hf
    let S := Matrix.diagonal (fun z => alpha i * w z) - genAdvFilter input A i
    have hs : S.PosSemidef := hA.2.2.2.2.2 i
    have hdiag : S x x = 0 := by
      change (if x=x then alpha i*w x else 0) - (if input x i ≠ input x i then A x x else 0) = 0
      simp [hx]
    have hh := real_psd_zero_diagonal_row S hs x hdiag y
    have hne : x ≠ y := fun he => hf (congrArg f he)
    change (if x=y then alpha i*w x else 0) - (if input x i ≠ input y i then A x y else 0) = 0 at hh
    rw [if_neg hne,if_pos hi] at hh
    linarith
end
noncomputable section

/-- An entrywise nonnegative Hermitian real matrix with positive semidefinite slack `a • 1 - G`
and nonnegative `a` has norm at most `a`. -/
theorem real_nonnegative_norm_le_of_slack (G : Matrix X X ℝ) (hG : G.IsHermitian)
    (hn : ∀ x y, 0 ≤ G x y) (a : ℝ) (ha : 0 ≤ a)
    (hs : (a • (1 : Matrix X X ℝ) - G).PosSemidef) : ‖G‖ ≤ a := by
  by_cases he : Nonempty X
  · letI : Nonempty X := he
    obtain ⟨v,_,hv1,hv⟩ := balancedReal_nonnegative_extreme G hG hn
    have hp := hs.dotProduct_mulVec_nonneg v
    have heq : star v ⬝ᵥ ((a • (1 : Matrix X X ℝ) - G) *ᵥ v) =
        a * (∑ x, (v x)^2) - ∑ x, ∑ y, G x y*v x*v y := by
      rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
      change (∑ x, v x*(a*v x - (G *ᵥ v) x)) = _
      simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro x _
        ring
      · apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
    rw [heq,hv1,mul_one] at hp
    linarith
  · letI : IsEmpty X := not_nonempty_iff.mp he
    have hz : G = 0 := by ext x; exact isEmptyElim x
    simpa only [hz,norm_zero] using! ha
end
noncomputable section

/-- The matrix formed by dividing `A x y` by `Real.sqrt (w x) * Real.sqrt (w y)`, using Lean's
total division. -/
def minimaxPrimalGamma (w : X → ℝ) (A : Matrix X X ℝ) : Matrix X X ℝ :=
  fun x y => A x y / (Real.sqrt (w x)*Real.sqrt (w y))
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- With nonnegative costs, normalizing feasible minimax primal data by square roots of the
weights gives a feasible cost-weighted nonnegative adversary. -/
theorem minimaxPrimalGamma_feasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 ≤ alpha i) (w : X → ℝ) (A : Matrix X X ℝ)
    (hA : MinimaxSdpPrimalFeasible input f alpha w A) :
    CostAdversaryFeasible input f alpha (minimaxPrimalGamma w A) := by
  have hsym : (minimaxPrimalGamma w A).IsSymm := by
    ext x y
    have hs : A y x = A x y := congrFun (congrFun hA.2.2.1 x) y
    change A y x / (Real.sqrt (w y)*Real.sqrt (w x)) = A x y / (Real.sqrt (w x)*Real.sqrt (w y))
    rw [hs,mul_comm (Real.sqrt (w y))]
  have hn : ∀ x y, 0 ≤ minimaxPrimalGamma w A x y := by
    intro x y
    exact div_nonneg (hA.2.2.2.1 x y) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  refine ⟨hsym,hn,?_,?_⟩
  · intro x y hxy
    change A x y / _ = 0
    rw [hA.2.2.2.2.1 x y hxy,zero_div]
  · intro i
    let D : Matrix X X ℝ := Matrix.diagonal (fun x => (Real.sqrt (w x))⁻¹)
    let B := genAdvFilter input (minimaxPrimalGamma w A) i
    have hb : B.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro x y
      have hs : minimaxPrimalGamma w A y x = minimaxPrimalGamma w A x y :=
        congrFun (congrFun hsym x) y
      change star (if input y i ≠ input x i then minimaxPrimalGamma w A y x else 0) =
        if input x i ≠ input y i then minimaxPrimalGamma w A x y else 0
      simp only [star_trivial,hs,ne_comm]
    have hbn : ∀ x y, 0 ≤ B x y := by
      intro x y
      change 0 ≤ if input x i ≠ input y i then minimaxPrimalGamma w A x y else 0
      split_ifs
      · exact hn x y
      · exact le_rfl
    have hp := (hA.2.2.2.2.2 i).conjTranspose_mul_mul_same D
    have hdiag : (Matrix.diagonal (fun x => if w x = 0 then alpha i else 0) : Matrix X X ℝ).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro x
      change 0 ≤ if w x = 0 then alpha i else 0
      split_ifs
      · exact ha i
      · exact le_rfl
    have he : Dᴴ * (Matrix.diagonal (fun x => alpha i*w x) - genAdvFilter input A i) * D +
        Matrix.diagonal (fun x => if w x = 0 then alpha i else 0) =
        alpha i • (1 : Matrix X X ℝ) - B := by
      ext x y
      dsimp only [D]
      simp only [Matrix.add_apply,Matrix.diagonal_conjTranspose,star_trivial,Matrix.mul_diagonal,Matrix.diagonal_mul]
      change (Real.sqrt (w x))⁻¹ * ((if x=y then alpha i*w x else 0) -
          (if input x i ≠ input y i then A x y else 0)) * (Real.sqrt (w y))⁻¹ +
          (if x=y then (if w x=0 then alpha i else 0) else 0) =
        alpha i*(if x=y then (1 : ℝ) else 0) -
          (if input x i ≠ input y i then A x y/(Real.sqrt (w x)*Real.sqrt (w y)) else 0)
      by_cases hxy : x=y
      · subst y
        simp only [ne_eq,not_true_eq_false,↓reduceIte]
        by_cases hx : w x=0
        · simp [hx]
        · have hr : Real.sqrt (w x) ≠ 0 := Real.sqrt_ne_zero'.mpr
            (lt_of_le_of_ne (hA.1 x) (Ne.symm hx))
          have hsq := Real.sq_sqrt (hA.1 x)
          simp only [if_neg hx]
          field_simp [hr]
          rw [hsq]
          ring
      · by_cases hi : input x i ≠ input y i
        · simp only [if_neg hxy,if_pos hi]
          ring
        · simp only [if_neg hxy,if_neg hi]
          ring
    have hslack : (alpha i • (1 : Matrix X X ℝ) - B).PosSemidef := by
      rw [← he]
      exact hp.add hdiag
    exact real_nonnegative_norm_le_of_slack B hb hbn (alpha i) (ha i) hslack
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- For observable outputs, the sum of the entries of a feasible minimax primal matrix is
bounded by the norm of its normalized adversary matrix. -/
theorem minimaxPrimalGamma_score (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (hobs : OutputObservable input f) (w : X → ℝ) (A : Matrix X X ℝ)
    (hA : MinimaxSdpPrimalFeasible input f alpha w A) :
    (∑ x, ∑ y, A x y) ≤ ‖minimaxPrimalGamma w A‖ := by
  let v : X → ℝ := fun x => Real.sqrt (w x)
  have hv : ∑ x, (v x)^2 = 1 := by
    simp only [v,Real.sq_sqrt (hA.1 _),hA.2.1]
  have he : dotProduct v (minimaxPrimalGamma w A *ᵥ v) = ∑ x, ∑ y, A x y := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : w x = 0
    · rw [minimaxPrimal_zero_weight input f alpha hobs w A hA x hx y]
      simp [v,minimaxPrimalGamma,hx]
    · by_cases hy : w y=0
      · have hs : A x y = 0 := by
          rw [← congrFun (congrFun hA.2.2.1 x) y]
          exact minimaxPrimal_zero_weight input f alpha hobs w A hA y hy x
        rw [hs]
        simp [v,minimaxPrimalGamma,hy]
      · have hrx : Real.sqrt (w x) ≠ 0 := Real.sqrt_ne_zero'.mpr
          (lt_of_le_of_ne (hA.1 x) (Ne.symm hx))
        have hry : Real.sqrt (w y) ≠ 0 := Real.sqrt_ne_zero'.mpr
          (lt_of_le_of_ne (hA.1 y) (Ne.symm hy))
        dsimp only [v,minimaxPrimalGamma]
        field_simp
  have hb := (le_abs_self _).trans (balancedReal_rayleigh_bound (minimaxPrimalGamma w A) v)
  rw [he,hv,mul_one] at hb
  exact hb
end
noncomputable section

/-- The extended nonnegative supremum of the entry sums of feasible minimax primal matrices. -/
def minimaxSdpPrimalValue (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) : ℝ≥0∞ :=
  ⨆ wa : {wa : (X → ℝ) × Matrix X X ℝ // MinimaxSdpPrimalFeasible input f alpha wa.1 wa.2},
    ENNReal.ofReal (∑ x, ∑ y, wa.val.2 x y)
end
noncomputable section

/-- With positive costs, the norm of every feasible cost-weighted nonnegative adversary is
bounded by `advAlphaR`. -/
theorem costAdversary_norm_le_source (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (G : Matrix X X ℝ) (hG : CostAdversaryFeasible input f alpha G) :
    ENNReal.ofReal ‖G‖ ≤ advAlphaR input f alpha := by
  by_cases hne : G=0
  · simp only [hne,norm_zero,ENNReal.ofReal_zero,zero_le]
  · exact (costAdversary_norm_le_witness input f alpha ha G hG).trans
      (le_iSup_of_le ⟨G,hG.1,hG.2.1,hG.2.2.1,hne⟩ le_rfl)
end
noncomputable section

/-- For observable outputs and positive costs, every feasible minimax primal entry sum is
bounded by the real nonnegative adversary value. -/
theorem minimaxSdp_score_le_source (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hobs : OutputObservable input f)
    (w : X → ℝ) (A : Matrix X X ℝ) (hA : MinimaxSdpPrimalFeasible input f alpha w A) :
    ENNReal.ofReal (∑ x, ∑ y, A x y) ≤ advAlphaR input f alpha := by
  exact (ENNReal.ofReal_le_ofReal (minimaxPrimalGamma_score input f alpha hobs w A hA)).trans
    (costAdversary_norm_le_source input f alpha ha _
      (minimaxPrimalGamma_feasible input f alpha (fun i => (ha i).le) w A hA))
end
noncomputable section

/-- For a nonconstant function with observable outputs and positive costs, the minimax SDP
primal value equals `advAlphaR`. -/
theorem minimaxSdpPrimalValue_eq_source (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hobs : OutputObservable input f) (hnc : ∃ x y, f x ≠ f y) :
    minimaxSdpPrimalValue input f alpha = advAlphaR input f alpha := by
  apply le_antisymm
  · apply iSup_le
    intro wa
    exact minimaxSdp_score_le_source input f alpha ha hobs wa.val.1 wa.val.2 wa.property
  · obtain ⟨G,hG,hne,_,he⟩ := advAlphaR_optimal_exists_of_observable input f alpha ha hobs hnc
    obtain ⟨w,A,hA,hscore⟩ := sourceAdversary_primal_exists input f alpha G hG hne
    rw [he]
    exact (ENNReal.ofReal_le_ofReal hscore).trans (le_iSup_of_le ⟨(w,A),hA⟩ le_rfl)
end
noncomputable section

/-- For a nonconstant function with observable outputs and positive costs, feasible minimax
primal data attain `advAlphaR` as their entry sum. -/
theorem minimaxSdp_primal_optimal_exists (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hobs : OutputObservable input f) (hnc : ∃ x y, f x ≠ f y) :
    ∃ w A, MinimaxSdpPrimalFeasible input f alpha w A ∧
      ENNReal.ofReal (∑ x, ∑ y, A x y) = advAlphaR input f alpha := by
  obtain ⟨G,hG,hne,_,he⟩ := advAlphaR_optimal_exists_of_observable input f alpha ha hobs hnc
  obtain ⟨w,A,hA,hscore⟩ := sourceAdversary_primal_exists input f alpha G hG hne
  refine ⟨w,A,hA,le_antisymm (minimaxSdp_score_le_source input f alpha ha hobs w A hA) ?_⟩
  rw [he]
  exact ENNReal.ofReal_le_ofReal hscore
end
noncomputable section

/-- The extended nonnegative infimum of positive objectives possessing a feasible minimax Gram
family. -/
def minimaxSdpDualValue (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) : ℝ≥0∞ :=
  ⨅ zt : {zt : ℝ × (K → Matrix X X ℝ) // 0 < zt.1 ∧ MinimaxGramFeasible input f alpha zt.1 zt.2},
    ENNReal.ofReal zt.val.1
end
noncomputable section

/-- For a nonconstant function with positive costs and nonempty coordinate type, the minimax SDP
dual value equals `minimaxAlpha`. -/
theorem minimaxSdpDualValue_eq_minimax [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (ha : ∀ i, 0 < alpha i)
    (hnc : ∃ x y, f x ≠ f y) : minimaxSdpDualValue input f alpha = minimaxAlpha input f alpha := by
  apply le_antisymm
  · by_cases hf : minimaxAlpha input f alpha = ⊤
    · rw [hf]
      exact le_top
    · have ht := ENNReal.toReal_pos (minimaxAlpha_ne_zero input f alpha hnc) hf
      obtain ⟨Z,hZ,_⟩ := minimaxGram_optimal_exists_of_finite input f alpha ha hnc hf
      calc
        minimaxSdpDualValue input f alpha ≤ ENNReal.ofReal (minimaxAlpha input f alpha).toReal :=
          by
            unfold minimaxSdpDualValue
            exact iInf_le (fun zt : {zt : ℝ × (K → Matrix X X ℝ) //
                0 < zt.1 ∧ MinimaxGramFeasible input f alpha zt.1 zt.2} => ENNReal.ofReal zt.val.1)
              ⟨((minimaxAlpha input f alpha).toReal,Z),ht,hZ⟩
        _ = minimaxAlpha input f alpha := ENNReal.ofReal_toReal hf
  · apply le_iInf
    intro zt
    exact (minimaxGram_feasible_iff_value input f alpha ha hnc zt.val.1 zt.property.1).mp
      ⟨zt.val.2,zt.property.2⟩
end
noncomputable section
omit [DecidableEq K] in

/-- The minimax SDP primal value is bounded by its dual value. -/
theorem minimaxSdp_values_weak_duality (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) :
    minimaxSdpPrimalValue input f alpha ≤ minimaxSdpDualValue input f alpha := by
  apply le_iInf
  intro zt
  apply iSup_le
  intro wa
  exact ENNReal.ofReal_le_ofReal
    (minimaxSdp_weak_duality input f alpha wa.val.1 wa.val.2 wa.property zt.val.1 zt.val.2 zt.property.2)
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
variable [DecidableEq X]
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace
noncomputable section
/-- The subtype of ordered input pairs having different Boolean outputs. -/
abbrev AdversarySdpPairs (f : X → Bool) := {xy : X × X // f xy.1 ≠ f xy.2}
end
noncomputable section
/-- The disjoint union of input-coordinate indices and different-output pair indices used by the
equality SDP. -/
abbrev AdversarySdpIndex (f : X → Bool) (K : Type) := (X × K) ⊕ AdversarySdpPairs f
end
noncomputable section
/-- The disjoint union of input budget constraints and different-output pair constraints. -/
abbrev AdversarySdpConstraints (f : X → Bool) := X ⊕ AdversarySdpPairs f
end
noncomputable section
/-- The cost-weighted sum of real diagonal entries in the input-coordinate block associated with
`x`. -/
def adversarySdpBudget (f : X → Bool) (alpha : K → ℝ)
    (H : HermitianMat (AdversarySdpIndex f K) ℂ) (x : X) : ℝ :=
  ∑ i, alpha i * (H.mat (Sum.inl (x,i)) (Sum.inl (x,i))).re
end
noncomputable section
/-- The sum of real separating-coordinate entries for a different-output pair, minus its
diagonal slack entry. -/
def adversarySdpPair (input : X → K → Bool) (f : X → Bool)
    (H : HermitianMat (AdversarySdpIndex f K) ℂ) (xy : AdversarySdpPairs f) : ℝ :=
  (∑ i, if input xy.val.1 i ≠ input xy.val.2 i then
    (H.mat (Sum.inl (xy.val.1,i)) (Sum.inl (xy.val.2,i))).re else 0) -
      (H.mat (Sum.inr xy) (Sum.inr xy)).re
end
noncomputable section

/-- The real continuous linear map recording budget differences from the reference input and the
different-output pair expressions. -/
def adversarySdpConstraint (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (x0 : X) :
    HermitianMat (AdversarySdpIndex f K) ℂ →L[ℝ] EuclideanSpace ℝ (AdversarySdpConstraints f) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun H => WithLp.toLp 2 (fun c => match c with
      | Sum.inl x => adversarySdpBudget f alpha H x - adversarySdpBudget f alpha H x0
      | Sum.inr xy => adversarySdpPair input f H xy)
    map_add' := by
      intro H G
      ext c
      cases c with
      | inl x =>
        change adversarySdpBudget f alpha (H+G) x - adversarySdpBudget f alpha (H+G) x0 =
          (adversarySdpBudget f alpha H x - adversarySdpBudget f alpha H x0) +
          (adversarySdpBudget f alpha G x - adversarySdpBudget f alpha G x0)
        simp only [adversarySdpBudget,HermitianMat.mat_add,
          Matrix.add_apply,Complex.add_re,mul_add,Finset.sum_add_distrib]
        ring
      | inr xy =>
        change adversarySdpPair input f
            (H+G) xy = adversarySdpPair input f H xy + adversarySdpPair input f G xy
        simp only [adversarySdpPair,HermitianMat.mat_add,
          Matrix.add_apply,Complex.add_re]
        have hh : (∑ i, if input xy.val.1 i ≠ input xy.val.2 i then
            (H.mat (Sum.inl (xy.val.1,i)) (Sum.inl (xy.val.2,i))).re +
            (G.mat (Sum.inl (xy.val.1,i)) (Sum.inl (xy.val.2,i))).re else 0) =
          (∑ i, if input xy.val.1 i ≠ input xy.val.2 i then
            (H.mat (Sum.inl (xy.val.1,i)) (Sum.inl (xy.val.2,i))).re else 0) +
          (∑ i, if input xy.val.1 i ≠ input xy.val.2 i then
            (G.mat (Sum.inl (xy.val.1,i)) (Sum.inl (xy.val.2,i))).re else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> ring
        rw [hh]
        ring
    map_smul' := by
      intro t H
      ext c
      cases c with
      | inl x =>
        change adversarySdpBudget f alpha (t • H) x - adversarySdpBudget f alpha (t • H) x0 =
          t*(adversarySdpBudget f alpha H x - adversarySdpBudget f alpha H x0)
        simp only [adversarySdpBudget,HermitianMat.mat_smul,
          Matrix.smul_apply,Complex.smul_re,smul_eq_mul]
        simp_rw [mul_left_comm (alpha _),← Finset.mul_sum]
        ring
      | inr xy =>
        change adversarySdpPair input f (t • H) xy = t*adversarySdpPair input f H xy
        simp only [adversarySdpPair,HermitianMat.mat_smul,
          Matrix.smul_apply,Complex.smul_re,smul_eq_mul]
        have hh : (∑ i, if input xy.val.1 i ≠ input xy.val.2 i then
            t*(H.mat (Sum.inl (xy.val.1,i)) (Sum.inl (xy.val.2,i))).re else 0) =
          t*(∑ i, if input xy.val.1 i ≠ input xy.val.2 i then
            (H.mat (Sum.inl (xy.val.1,i)) (Sum.inl (xy.val.2,i))).re else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> ring
        rw [hh]
        ring }
end
noncomputable section

/-- The equality-constrained SDP imposing equal input budgets and pair expressions equal to one,
with primal objective the negative reference-input budget. -/
def adversaryEqualityProgram (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (x0 : X) :
    Program (AdversarySdpIndex f K) (EuclideanSpace ℝ (AdversarySdpConstraints f)) where
  constraint := adversarySdpConstraint input f alpha x0
  rhs := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun _ => 1))
  objective := HermitianMat.diagonal ℂ (fun s => match s with
    | Sum.inl (x,i) => if x=x0 then -alpha i else 0
    | Sum.inr _ => 0)
end
noncomputable section

/-- The entrywise real part of a complex positive semidefinite matrix is a real positive
semidefinite matrix. -/
theorem complex_psd_real_part {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.PosSemidef) : (H.map Complex.re).PosSemidef := by
  have hs : (H.map Complex.re).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro x y
    have h := congrArg Complex.re (hH.1.apply x y)
    simpa only [Matrix.map_apply,star_trivial,Complex.star_def,Complex.conj_re] using! h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs
  intro v
  have hp := hH.re_dotProduct_nonneg (fun x => (v x : ℂ))
  change 0 ≤ (star (fun x => (v x : ℂ)) ⬝ᵥ (H *ᵥ (fun x => (v x : ℂ)))).re at hp
  simpa only [dotProduct,Matrix.mulVec,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,Pi.star_apply,star_trivial,
    Complex.star_def,Complex.conj_ofReal,Matrix.map_apply] using! hp
end
noncomputable section
omit [Fintype X] [DecidableEq X] [DecidableEq K] in

/-- For a nonconstant function with positive costs, every feasible Gram objective is strictly
positive. -/
theorem minimaxGram_objective_pos (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ x y, f x ≠ f y)
    (t : ℝ) (Z : K → Matrix X X ℝ) (hZ : MinimaxGramFeasible input f alpha t Z) : 0 < t := by
  obtain ⟨x,y,hxy⟩ := hnc
  by_contra ht
  have ht0 : t=0 := le_antisymm (not_lt.mp ht)
    (by rw [← hZ.2.1 x]; exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i).le (hZ.1 i).diag_nonneg))
  have hz : ∀ i, Z i x y = 0 := by
    intro i
    have hh : ∑ j, alpha j * Z j x x = 0 := (hZ.2.1 x).trans ht0
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset K)) => mul_nonneg (ha j).le (hZ.1 j).diag_nonneg)).mp hh
      i (Finset.mem_univ i)
    have hd : Z i x x = 0 := (mul_eq_zero.mp hi).resolve_left (ha i).ne'
    exact real_psd_zero_diagonal_row (Z i) (hZ.1 i) x hd y
  have hh := hZ.2.2 x y hxy
  simp only [hz,ite_self,Finset.sum_const_zero] at hh
  norm_num at hh
end
noncomputable section

/-- The equality SDP primal score is the negative budget at the reference input. -/
theorem adversaryEquality_primalScore (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (H : HermitianMat (AdversarySdpIndex f K) ℂ) :
    (adversaryEqualityProgram input f alpha x0).primalScore H = -adversarySdpBudget f alpha H x0 := by
  rw [Program.primalScore,HermitianMat.inner_eq_re_trace]
  simp [adversaryEqualityProgram,HermitianMat.diagonal_mat,Matrix.trace,Matrix.diag_apply,
    Matrix.diagonal_mul,Fintype.sum_sum_type,Fintype.sum_prod_type,
    adversarySdpBudget]
end
noncomputable section

/-- Equality SDP primal feasibility is equivalent to positive semidefiniteness, equal input
budgets, and every different-output pair expression being one. -/
theorem adversaryEquality_primal_iff (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (H : HermitianMat (AdversarySdpIndex f K) ℂ) :
    (adversaryEqualityProgram input f alpha x0).PrimalFeasible H ↔
      H.mat.PosSemidef ∧
      (∀ x, adversarySdpBudget f alpha H x = adversarySdpBudget f alpha H x0) ∧
      (∀ xy, adversarySdpPair input f H xy = 1) := by
  constructor
  · rintro ⟨hH,he⟩
    refine ⟨HermitianMat.zero_le_iff.mp hH,?_,?_⟩
    · intro x
      have hx := congrArg (fun v : EuclideanSpace ℝ (AdversarySdpConstraints f) => v (Sum.inl x)) he
      change adversarySdpBudget f alpha H x - adversarySdpBudget f alpha H x0 = 0 at hx
      exact sub_eq_zero.mp hx
    · intro xy
      have hx :=
          congrArg (fun v : EuclideanSpace ℝ (AdversarySdpConstraints f) => v (Sum.inr xy)) he
      exact hx
  · rintro ⟨hH,hbudget,hpair⟩
    refine ⟨HermitianMat.zero_le_iff.mpr hH,?_⟩
    ext c
    cases c with
    | inl x =>
      change adversarySdpBudget f alpha H x - adversarySdpBudget f alpha H x0 = 0
      exact sub_eq_zero.mpr (hbudget x)
    | inr xy => exact hpair xy
end
noncomputable section

/-- A feasible equality SDP matrix yields a feasible real Gram family by taking real parts of
its coordinate principal blocks. -/
theorem adversaryEquality_to_gram (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (H : HermitianMat (AdversarySdpIndex f K) ℂ)
    (hH : (adversaryEqualityProgram input f alpha x0).PrimalFeasible H) :
    MinimaxGramFeasible input f alpha (adversarySdpBudget f alpha H x0)
      (fun i => (H.mat.submatrix (fun x => Sum.inl (x,i)) (fun x => Sum.inl (x,i))).map Complex.re) := by
  have hh := (adversaryEquality_primal_iff input f alpha x0 H).mp hH
  refine ⟨?_,hh.2.1,?_⟩
  · intro i
    exact complex_psd_real_part _ (hh.1.submatrix (fun x => Sum.inl (x,i)))
  · intro x y hxy
    have he := hh.2.2 (⟨(x,y),hxy⟩ : AdversarySdpPairs f)
    have hn : 0 ≤ (H.mat (Sum.inr ⟨(x,y),hxy⟩) (Sum.inr ⟨(x,y),hxy⟩)).re :=
      (Complex.nonneg_iff.mp hh.1.diag_nonneg).1
    change (∑ i, if input x i ≠ input y i then
      (H.mat (Sum.inl (x,i)) (Sum.inl (y,i))).re else 0) -
        (H.mat (Sum.inr ⟨(x,y),hxy⟩) (Sum.inr ⟨(x,y),hxy⟩)).re = 1 at he
    change 1 ≤ ∑ i, if input x i ≠ input y i then
      (H.mat (Sum.inl (x,i)) (Sum.inl (y,i))).re else 0
    linarith
end
noncomputable section

/-- Embeds a real vector into coordinate block `i` of the equality SDP index type, setting all
other entries to zero. -/
def adversaryBlockVector (f : X → Bool) (i : K) (v : X → ℝ) : AdversarySdpIndex f K → ℂ :=
  Sum.elim (fun (x,j) => if j=i then (v x : ℂ) else 0) (fun _ => 0)
end
noncomputable section
/-- The Hermitian outer-product matrix of the vector embedded in coordinate block `i`. -/
def adversaryBlockRankOne (f : X → Bool) (i : K) (v : X → ℝ) : HermitianMat (AdversarySdpIndex f K) ℂ :=
  ⟨Matrix.vecMulVec (adversaryBlockVector f i v) (star (adversaryBlockVector f i v)),
    (Matrix.posSemidef_vecMulVec_self_star _).1⟩
end
noncomputable section
/-- The Hermitian diagonal matrix carrying `r` on different-output pair indices and zero on
input-coordinate indices. -/
def adversarySlackDiagonal (f : X → Bool) (r : AdversarySdpPairs f → ℝ) :
    HermitianMat (AdversarySdpIndex f K) ℂ :=
  HermitianMat.diagonal ℂ (Sum.elim (fun _ => 0) r)
end
noncomputable section
omit [DecidableEq X] in

/-- Every block outer-product matrix is positive semidefinite in the Hermitian matrix order. -/
theorem adversaryBlockRankOne_psd (f : X → Bool) (i : K) (v : X → ℝ) :
    0 ≤ adversaryBlockRankOne f i v :=
  HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_vecMulVec_self_star _)
end
noncomputable section
omit [DecidableEq X] in

/-- The budget of a block outer-product matrix at `x` is `alpha i * (v x)^2`. -/
theorem adversaryBlockRankOne_budget (f : X → Bool) (alpha : K → ℝ) (i : K) (v : X → ℝ) (x : X) :
    adversarySdpBudget f alpha (adversaryBlockRankOne f i v) x = alpha i*(v x)^2 := by
  unfold adversarySdpBudget
  rw [Finset.sum_eq_single i]
  · change alpha i*((if i=i then (v x : ℂ) else 0)*star (if i=i then (v x : ℂ) else 0)).re = alpha i*(v x)^2
    rw [if_pos rfl]
    simp [pow_two]
  · intro j _ hj
    change alpha j*((if j=i then (v x : ℂ) else 0)*star (if j=i then (v x : ℂ) else 0)).re = 0
    rw [if_neg hj]
    norm_num
  · simp
end
noncomputable section
omit [DecidableEq X] in

/-- The pair expression of a block outer-product matrix is the product of the two vector entries
when coordinate `i` separates the pair, and zero otherwise. -/
theorem adversaryBlockRankOne_pair (input : X → K → Bool) (f : X → Bool) (i : K) (v : X → ℝ)
    (xy : AdversarySdpPairs f) :
    adversarySdpPair input f (adversaryBlockRankOne f i v) xy =
      if input xy.val.1 i ≠ input xy.val.2 i then v xy.val.1*v xy.val.2 else 0 := by
  change (∑ j, if input xy.val.1 j ≠ input xy.val.2 j then
      ((if j=i then (v xy.val.1 : ℂ) else 0)*star (if j=i then (v xy.val.2 : ℂ) else 0)).re else 0) - ((0 : ℂ)*star (0 : ℂ)).re = _
  rw [zero_mul,Complex.zero_re,sub_zero,Finset.sum_eq_single i]
  · rw [if_pos rfl]
    by_cases hd : input xy.val.1 i ≠ input xy.val.2 i
    · simp [hd]
    · simp [hd]
  · intro j _ hj
    rw [if_neg hj]
    simp
  · simp
end
noncomputable section
omit [Fintype X] [Fintype K] in

/-- A slack diagonal matrix with nonnegative pair entries is positive semidefinite. -/
theorem adversarySlackDiagonal_psd (f : X → Bool) (r : AdversarySdpPairs f → ℝ)
    (hr : ∀ xy, 0 ≤ r xy) : 0 ≤ adversarySlackDiagonal (K := K) f r := by
  apply HermitianMat.zero_le_iff.mpr
  apply Matrix.PosSemidef.diagonal
  intro c
  cases c with
  | inl _ => exact le_rfl
  | inr xy => exact Complex.nonneg_iff.mpr ⟨hr xy,rfl⟩
end
noncomputable section
omit [Fintype X] in

/-- A slack diagonal matrix contributes zero to every input budget. -/
theorem adversarySlackDiagonal_budget (f : X → Bool) (alpha : K → ℝ)
    (r : AdversarySdpPairs f → ℝ) (x : X) :
    adversarySdpBudget f alpha (adversarySlackDiagonal f r) x = 0 := by
  simp [adversarySdpBudget,adversarySlackDiagonal,HermitianMat.diagonal_mat,-HermitianMat.mat_apply]
end
noncomputable section
omit [Fintype X] in

/-- The pair expression of a slack diagonal matrix is the negative of its corresponding slack
entry. -/
theorem adversarySlackDiagonal_pair (input : X → K → Bool) (f : X → Bool)
    (r : AdversarySdpPairs f → ℝ) (xy : AdversarySdpPairs f) :
    adversarySdpPair input f (adversarySlackDiagonal f r) xy = -r xy := by
  simp [adversarySdpPair,adversarySlackDiagonal,HermitianMat.diagonal_mat,Matrix.diagonal,
    -HermitianMat.mat_apply]
end
noncomputable section
omit [Fintype X] in

/-- The input budget is additive in the Hermitian SDP matrix. -/
theorem adversarySdpBudget_add (f : X → Bool) (alpha : K → ℝ)
    (H G : HermitianMat (AdversarySdpIndex f K) ℂ) (x : X) :
    adversarySdpBudget f alpha (H+G) x = adversarySdpBudget f alpha H x + adversarySdpBudget f alpha G x := by
  simp only [adversarySdpBudget,HermitianMat.mat_add,Matrix.add_apply,Complex.add_re,
    mul_add,Finset.sum_add_distrib]
end
noncomputable section
omit [Fintype X] [DecidableEq X] [DecidableEq K] in

/-- The input budget commutes with real scalar multiplication of the Hermitian SDP matrix. -/
theorem adversarySdpBudget_smul (f : X → Bool) (alpha : K → ℝ)
    (H : HermitianMat (AdversarySdpIndex f K) ℂ) (t : ℝ) (x : X) :
    adversarySdpBudget f alpha (t • H) x = t * adversarySdpBudget f alpha H x := by
  simp only [adversarySdpBudget,HermitianMat.mat_smul,Matrix.smul_apply,Complex.smul_re,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end
noncomputable section
omit [Fintype X] in

/-- The input budget of a finite sum is the sum of the input budgets. -/
theorem adversarySdpBudget_sum {J : Type} [Fintype J] (f : X → Bool) (alpha : K → ℝ)
    (H : J → HermitianMat (AdversarySdpIndex f K) ℂ) (x : X) :
    adversarySdpBudget f alpha (∑ j, H j) x = ∑ j, adversarySdpBudget f alpha (H j) x := by
  simp only [adversarySdpBudget,HermitianMat.mat_finset_sum,Matrix.sum_apply,Complex.re_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
end
noncomputable section

/-- Expands the inner product of the equality SDP dual slack with a Hermitian matrix into
budget-difference, pair-expression, and reference-budget contributions. -/
theorem adversaryEquality_slack_pairing (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (y : EuclideanSpace ℝ (AdversarySdpConstraints f))
    (H : HermitianMat (AdversarySdpIndex f K) ℂ) :
    ⟪(adversaryEqualityProgram input f alpha x0).constraint.adjoint y -
      (adversaryEqualityProgram input f alpha x0).objective,H⟫_ℝ =
      (∑ x, y (Sum.inl x)*(adversarySdpBudget f alpha H x - adversarySdpBudget f alpha H x0)) +
      (∑ xy, y (Sum.inr xy)*adversarySdpPair input f H xy) + adversarySdpBudget f alpha H x0 := by
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
  change ⟪y,(adversaryEqualityProgram input f alpha x0).constraint H⟫_ℝ -
      (adversaryEqualityProgram input f alpha x0).primalScore H = _
  rw [adversaryEquality_primalScore]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_sum_type]
  change (∑ x, (adversarySdpBudget f alpha H x - adversarySdpBudget f alpha H x0)*y (Sum.inl x)) +
      (∑ xy, adversarySdpPair input f H xy*y (Sum.inr xy)) - (-adversarySdpBudget f alpha H x0) = _
  simp only [mul_comm,sub_neg_eq_add]
end
noncomputable section

/-- Evaluates the equality SDP dual slack on a block outer-product matrix as weighted squared
vector entries and separating-coordinate vector products. -/
theorem adversaryEquality_rankOne_slack (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) (i : K) (v : X → ℝ) :
    ⟪(adversaryEqualityProgram input f alpha x0).constraint.adjoint y -
      (adversaryEqualityProgram input f alpha x0).objective,adversaryBlockRankOne f i v⟫_ℝ =
      (∑ x, y (Sum.inl x)*(alpha i*(v x)^2 - alpha i*(v x0)^2)) +
      (∑ xy, y (Sum.inr xy)*(if input xy.val.1 i ≠ input xy.val.2 i then v xy.val.1*v xy.val.2 else 0)) +
      alpha i*(v x0)^2 := by
  rw [adversaryEquality_slack_pairing]
  simp only [adversaryBlockRankOne_budget,adversaryBlockRankOne_pair]
end
noncomputable section

/-- The sum of coordinate block outer products scaled by `c`, together with a pair-index slack
diagonal. -/
def adversaryLiftRankOne (f : X → Bool) (c : K → ℝ) (v : K → X → ℝ)
    (r : AdversarySdpPairs f → ℝ) : HermitianMat (AdversarySdpIndex f K) ℂ :=
  (∑ i, c i • adversaryBlockRankOne f i (v i)) + adversarySlackDiagonal f r
end
noncomputable section

/-- A lifted sum of block outer products and slack diagonal is positive semidefinite when all
coefficients and slack entries are nonnegative. -/
theorem adversaryLiftRankOne_psd (f : X → Bool) (c : K → ℝ) (v : K → X → ℝ)
    (r : AdversarySdpPairs f → ℝ) (hc : ∀ i, 0 ≤ c i) (hr : ∀ xy, 0 ≤ r xy) :
    0 ≤ adversaryLiftRankOne f c v r := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun i _ => smul_nonneg (hc i) (adversaryBlockRankOne_psd f i (v i)))
  · exact adversarySlackDiagonal_psd f r hr
end
noncomputable section

/-- The budget of a lifted matrix at `x` is `∑ i, c i * alpha i * (v i x)^2`. -/
theorem adversaryLiftRankOne_budget (f : X → Bool) (alpha : K → ℝ) (c : K → ℝ) (v : K → X → ℝ)
    (r : AdversarySdpPairs f → ℝ) (x : X) :
    adversarySdpBudget f alpha (adversaryLiftRankOne f c v r) x = ∑ i, c i*alpha i*(v i x)^2 := by
  rw [adversaryLiftRankOne,adversarySdpBudget_add,adversarySlackDiagonal_budget,add_zero,
    adversarySdpBudget_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [adversarySdpBudget_smul,adversaryBlockRankOne_budget]
  ring
end
noncomputable section

/-- The pair expression of a lifted matrix is the weighted sum of separating-coordinate vector
products minus the pair slack. -/
theorem adversaryLiftRankOne_pair (input : X → K → Bool) (f : X → Bool) (x0 : X)
    (c : K → ℝ) (v : K → X → ℝ) (r : AdversarySdpPairs f → ℝ) (xy : AdversarySdpPairs f) :
    adversarySdpPair input f (adversaryLiftRankOne f c v r) xy =
      (∑ i, c i*(if input xy.val.1 i ≠ input xy.val.2 i then v i xy.val.1*v i xy.val.2 else 0)) - r xy := by
  have hm := congrArg (fun z : EuclideanSpace ℝ (AdversarySdpConstraints f) => z (Sum.inr xy))
    ((adversarySdpConstraint input f (fun _ => 0) x0).map_add
      (∑ i, c i • adversaryBlockRankOne f i (v i)) (adversarySlackDiagonal f r))
  change adversarySdpPair input f (adversaryLiftRankOne f c v r) xy =
    adversarySdpPair input f (∑ i, c i • adversaryBlockRankOne f i (v i)) xy +
      adversarySdpPair input f (adversarySlackDiagonal f r) xy at hm
  rw [hm,adversarySlackDiagonal_pair]
  have hs := congrArg (fun z : EuclideanSpace ℝ (AdversarySdpConstraints f) => z (Sum.inr xy))
    (map_sum (adversarySdpConstraint input f (fun _ => 0) x0) (fun i => c i • adversaryBlockRankOne f i (v i)) Finset.univ)
  (try dsimp only at hs)
  simp only [WithLp.ofLp_sum,Finset.sum_apply] at hs
  change adversarySdpPair input f (∑ i, c i • adversaryBlockRankOne f i (v i)) xy =
    ∑ i, adversarySdpPair input f (c i • adversaryBlockRankOne f i (v i)) xy at hs
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he := congrArg (fun z : EuclideanSpace ℝ (AdversarySdpConstraints f) => z (Sum.inr xy))
    ((adversarySdpConstraint input f (fun _ => 0) x0).map_smul (c i) (adversaryBlockRankOne f i (v i)))
  change adversarySdpPair input f (c i • adversaryBlockRankOne f i (v i)) xy =
    c i * adversarySdpPair input f (adversaryBlockRankOne f i (v i)) xy at he
  rw [he,adversaryBlockRankOne_pair]
end
noncomputable section

/-- The equality SDP matrix formed from square roots of probability entries with coefficients `t
/ alpha i` and slack `t * advMinimaxTerm - 1`. -/
def adversaryProbabilityLift (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (p : X → K → ℝ) (t : ℝ) : HermitianMat (AdversarySdpIndex f K) ℂ :=
  adversaryLiftRankOne f (fun i => t/alpha i) (fun i x => Real.sqrt (p x i))
    (fun xy => t*advMinimaxTerm input alpha p xy.val.1 xy.val.2 - 1)
end
noncomputable section

/-- With positive costs and a probability family, every input budget of the probability lift
equals `t`. -/
theorem adversaryProbabilityLift_budget (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (p : X → K → ℝ) (hp : IsProbabilityFamily p) (t : ℝ) (x : X) :
    adversarySdpBudget f alpha (adversaryProbabilityLift input f alpha p t) x = t := by
  rw [adversaryProbabilityLift,adversaryLiftRankOne_budget]
  calc
    (∑ i, (t/alpha i)*alpha i*(Real.sqrt (p x i))^2) = ∑ i, t*p x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.sq_sqrt (hp.1 x i),div_mul_cancel₀ _ (ha i).ne']
    _ = t := by rw [← Finset.mul_sum,hp.2 x,mul_one]
end
noncomputable section

/-- For a probability family, every different-output pair expression of the probability lift
equals one. -/
theorem adversaryProbabilityLift_pair (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (p : X → K → ℝ) (hp : IsProbabilityFamily p) (t : ℝ) (x0 : X) (xy : AdversarySdpPairs f) :
    adversarySdpPair input f (adversaryProbabilityLift input f alpha p t) xy = 1 := by
  rw [adversaryProbabilityLift,adversaryLiftRankOne_pair input f x0]
  have hh : (∑ i, (t/alpha i)*(if input xy.val.1 i ≠ input xy.val.2 i then
      Real.sqrt (p xy.val.1 i)*Real.sqrt (p xy.val.2 i) else 0)) =
      t*advMinimaxTerm input alpha p xy.val.1 xy.val.2 := by
    rw [advMinimaxTerm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : input xy.val.1 i ≠ input xy.val.2 i
    · simp only [if_pos hi]
      rw [Real.sqrt_mul (hp.1 xy.val.1 i)]
      ring
    · simp [hi]
  rw [hh]
  ring
end
noncomputable section

/-- With positive costs and positive `t`, a probability family with different-output terms at
least `1 / t` lifts to feasible equality SDP data of primal score `-t`. -/
theorem adversaryProbabilityLift_feasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (p : X → K → ℝ) (hp : IsProbabilityFamily p)
    (t : ℝ) (ht : 0 < t) (x0 : X)
    (hpair : ∀ x y, f x ≠ f y → 1/t ≤ advMinimaxTerm input alpha p x y) :
    (adversaryEqualityProgram input f alpha x0).PrimalFeasible (adversaryProbabilityLift input f alpha p t) ∧
    (adversaryEqualityProgram input f alpha x0).primalScore (adversaryProbabilityLift input f alpha p t) = -t := by
  have hr (xy : AdversarySdpPairs f) : 0 ≤ t*advMinimaxTerm input alpha p xy.val.1 xy.val.2-1 := by
    have h := (div_le_iff₀ ht).mp (hpair xy.val.1 xy.val.2 xy.property)
    nlinarith
  refine ⟨(adversaryEquality_primal_iff input f alpha x0 _).mpr ⟨?_,?_,?_⟩,?_⟩
  · exact HermitianMat.zero_le_iff.mp (adversaryLiftRankOne_psd f _ _ _
      (fun i => div_nonneg ht.le (ha i).le) hr)
  · intro x
    rw [adversaryProbabilityLift_budget input f alpha ha p hp t x,
      adversaryProbabilityLift_budget input f alpha ha p hp t x0]
  · exact adversaryProbabilityLift_pair input f alpha p hp t x0
  · rw [adversaryEquality_primalScore,adversaryProbabilityLift_budget input f alpha ha p hp t x0]
end
noncomputable section
omit [Fintype X] in

/-- The budget of the identity Hermitian matrix equals the sum of the coordinate costs. -/
theorem adversarySdpBudget_one (f : X → Bool) (alpha : K → ℝ) (x : X) :
    adversarySdpBudget f alpha (1 : HermitianMat (AdversarySdpIndex f K) ℂ) x = ∑ i, alpha i := by
  simp [adversarySdpBudget,-HermitianMat.mat_apply]
end
noncomputable section
omit [Fintype X] in

/-- Every different-output pair expression of the identity Hermitian matrix equals negative one. -/
theorem adversarySdpPair_one (input : X → K → Bool) (f : X → Bool) (xy : AdversarySdpPairs f) :
    adversarySdpPair input f (1 : HermitianMat (AdversarySdpIndex f K) ℂ) xy = -1 := by
  have hh : xy.val.1 ≠ xy.val.2 := fun he => xy.property (congrArg f he)
  simp [adversarySdpPair,hh,-HermitianMat.mat_apply]
end
noncomputable section
/-- The real-valued number of coordinates on which two encoded Boolean inputs differ. -/
def adversaryDifferenceCount (input : X → K → Bool) (x y : X) : ℝ :=
  ∑ i, if input x i ≠ input y i then 1 else 0
end
noncomputable section
omit [Fintype X] [DecidableEq X] [DecidableEq K] in

/-- If outputs are observable from the input encoding, each different-output pair differs in at
least one coordinate. -/
theorem adversaryDifferenceCount_one_le (input : X → K → Bool) (f : X → Bool)
    (hobs : OutputObservable input f) (xy : AdversarySdpPairs f) :
    1 ≤ adversaryDifferenceCount input xy.val.1 xy.val.2 := by
  obtain ⟨i,hi⟩ := hobs xy.val.1 xy.val.2 xy.property
  have hh := Finset.single_le_sum
    (f := fun j => if input xy.val.1 j ≠ input xy.val.2 j then (1 : ℝ) else 0)
    (fun j _ => by change 0 ≤ if input xy.val.1 j ≠ input xy.val.2 j then (1 : ℝ) else 0; split_ifs <;> norm_num)
    (Finset.mem_univ i)
  simpa only [if_pos hi] using! hh
end
noncomputable section

/-- The identity plus a lifted block outer-product matrix with coefficient two and pair slack `2
* adversaryDifferenceCount - 2`. -/
def adversaryEqualityStrict (input : X → K → Bool) (f : X → Bool) :
    HermitianMat (AdversarySdpIndex f K) ℂ :=
  1 + adversaryLiftRankOne f (fun _ => 2) (fun _ _ => 1)
    (fun xy => 2*adversaryDifferenceCount input xy.val.1 xy.val.2 - 2)
end
noncomputable section

/-- For observable outputs, the equality SDP possesses a strictly feasible primal matrix. -/
theorem adversaryEquality_primalSlater (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (hobs : OutputObservable input f) (x0 : X) :
    (adversaryEqualityProgram input f alpha x0).PrimalSlater := by
  have hr (xy : AdversarySdpPairs f) : 0 ≤ 2*adversaryDifferenceCount input xy.val.1 xy.val.2-2 := by
    have hh := adversaryDifferenceCount_one_le input f hobs xy
    linarith
  have hp :=
      adversaryLiftRankOne_psd (K := K) f (fun _ => 2) (fun _ _ => 1) _ (fun _ => by norm_num) hr
  refine ⟨adversaryEqualityStrict input f,?_,?_⟩
  · change ((1 : Matrix (AdversarySdpIndex f K) (AdversarySdpIndex f K) ℂ) +
      (adversaryLiftRankOne f (fun _ => 2) (fun _ _ => 1)
        (fun xy => 2*adversaryDifferenceCount input xy.val.1 xy.val.2-2)).mat).PosDef
    exact Matrix.PosDef.one.add_posSemidef (HermitianMat.zero_le_iff.mp hp)
  · ext c
    cases c with
    | inl x =>
      change adversarySdpBudget f alpha (adversaryEqualityStrict input f) x -
        adversarySdpBudget f alpha (adversaryEqualityStrict input f) x0 = 0
      simp only [adversaryEqualityStrict,adversarySdpBudget_add,adversarySdpBudget_one,
        adversaryLiftRankOne_budget,one_pow,mul_one]
      ring
    | inr xy =>
      have hh := congrArg (fun z : EuclideanSpace ℝ (AdversarySdpConstraints f) => z (Sum.inr xy))
        ((adversarySdpConstraint input f alpha x0).map_add 1
          (adversaryLiftRankOne f (fun _ => 2) (fun _ _ => 1)
            (fun xy => 2*adversaryDifferenceCount input xy.val.1 xy.val.2-2)))
      change adversarySdpPair input f (adversaryEqualityStrict input f) xy = 1
      change adversarySdpPair input f (adversaryEqualityStrict input f) xy =
        adversarySdpPair input f 1 xy +
          adversarySdpPair input f (adversaryLiftRankOne f (fun _ => 2) (fun _ _ => 1)
            (fun xy => 2*adversaryDifferenceCount input xy.val.1 xy.val.2-2)) xy at hh
      rw [hh,adversarySdpPair_one,adversaryLiftRankOne_pair input f x0]
      have he : (∑ i, (2 : ℝ)*(if input xy.val.1 i ≠ input xy.val.2 i then 1*1 else 0)) =
          2*adversaryDifferenceCount input xy.val.1 xy.val.2 := by
        simp only [adversaryDifferenceCount,Finset.mul_sum,one_mul]
      rw [he]
      ring
end
noncomputable section

/-- The input component of a dual vector, corrected at the reference input so that the resulting
weights sum to one. -/
def adversaryDualWeight (f : X → Bool) (x0 : X)
    (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) (x : X) : ℝ :=
  y (Sum.inl x) + if x=x0 then 1-∑ z, y (Sum.inl z) else 0
end
noncomputable section
/-- The dual coefficient of an ordered different-output pair, extended by zero to equal-output
pairs. -/
def adversaryDualPair (f : X → Bool) (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) (x z : X) : ℝ :=
  if h : f x ≠ f z then y (Sum.inr ⟨(x,z),h⟩) else 0
end
noncomputable section
/-- The symmetric real matrix formed by negating the average of the two ordered dual pair
coefficients. -/
def adversaryDualMatrix (f : X → Bool) (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) : Matrix X X ℝ :=
  fun x z => -(adversaryDualPair f y x z + adversaryDualPair f y z x)/2
end
noncomputable section

/-- The corrected dual weights sum to one. -/
theorem adversaryDualWeight_sum (f : X → Bool) (x0 : X)
    (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) : ∑ x, adversaryDualWeight f x0 y x = 1 := by
  simp [adversaryDualWeight,Finset.sum_add_distrib]
end
noncomputable section
omit [Fintype X] [DecidableEq X] in

/-- The real matrix extracted from the dual pair coefficients is symmetric. -/
theorem adversaryDualMatrix_symm (f : X → Bool) (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) :
    (adversaryDualMatrix f y).IsSymm := by
  ext x z
  change -(adversaryDualPair f y z x + adversaryDualPair f y x z)/2 =
    -(adversaryDualPair f y x z + adversaryDualPair f y z x)/2
  ring
end
noncomputable section
omit [Fintype X] [DecidableEq X] in

/-- The extracted dual matrix vanishes on pairs with equal Boolean outputs. -/
theorem adversaryDualMatrix_support (f : X → Bool) (y : EuclideanSpace ℝ (AdversarySdpConstraints f))
    (x z : X) (h : f x = f z) : adversaryDualMatrix f y x z = 0 := by
  simp [adversaryDualMatrix,adversaryDualPair,h]
end
noncomputable section
omit [DecidableEq X] in

/-- A sum over different-output pair indices equals the full double sum using the zero-extended
dual pair coefficients. -/
theorem adversaryDualPair_sum (f : X → Bool) (y : EuclideanSpace ℝ (AdversarySdpConstraints f))
    (F : X → X → ℝ) :
    (∑ xy : AdversarySdpPairs f, y (Sum.inr xy)*F xy.val.1 xy.val.2) =
      ∑ x, ∑ z, adversaryDualPair f y x z*F x z := by
  let p : X × X → Prop := fun xy => f xy.1 ≠ f xy.2
  let g : X × X → ℝ := fun xy => adversaryDualPair f y xy.1 xy.2*F xy.1 xy.2
  have he : (∑ xy ∈ Finset.univ.filter p, g xy) = ∑ xy : X × X, g xy := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro xy _ hn
    have hnp : ¬p xy := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using! hn
    change (if h : f xy.1 ≠ f xy.2 then y (Sum.inr ⟨(xy.1,xy.2),h⟩) else 0)*F xy.1 xy.2 = 0
    rw [dif_neg hnp,zero_mul]
  have hprod : (∑ xy : X × X, g xy) = ∑ x, ∑ z, adversaryDualPair f y x z*F x z := by
    simp only [Fintype.sum_prod_type,g]
  rw [← hprod]
  rw [← he,Finset.sum_subtype (p := p) (Finset.univ.filter p) (by intro xy; simp [p]) g]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [g,adversaryDualPair,dif_pos xy.property]
end
noncomputable section
omit [DecidableEq X] in

/-- For a symmetric real kernel, pairing with the dual pair coefficients equals the negative
entrywise pairing with the extracted dual matrix. -/
theorem adversaryDualMatrix_pairing (f : X → Bool) (y : EuclideanSpace ℝ (AdversarySdpConstraints f))
    (F : X → X → ℝ) (hF : ∀ x z, F x z = F z x) :
    (∑ xy : AdversarySdpPairs f, y (Sum.inr xy)*F xy.val.1 xy.val.2) =
      -(∑ x, ∑ z, adversaryDualMatrix f y x z*F x z) := by
  rw [adversaryDualPair_sum]
  have hf : (∑ x, ∑ z, adversaryDualPair f y z x*F x z) =
      ∑ x, ∑ z, adversaryDualPair f y x z*F x z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    rw [hF z x]
  have he : (-2 : ℝ)*(∑ x, ∑ z, adversaryDualMatrix f y x z*F x z) =
      (∑ x, ∑ z, adversaryDualPair f y x z*F x z) +
      (∑ x, ∑ z, adversaryDualPair f y z x*F x z) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    unfold adversaryDualMatrix
    ring
  rw [hf] at he
  linarith
end
noncomputable section

/-- Combining the dual budget-difference terms with the reference quadratic term yields the
diagonal quadratic form of the corrected dual weights. -/
theorem adversaryDualWeight_quadratic (f : X → Bool) (x0 : X)
    (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) (a : ℝ) (v : X → ℝ) :
    (∑ x, y (Sum.inl x)*(a*(v x)^2-a*(v x0)^2)) + a*(v x0)^2 =
      ∑ x, a*adversaryDualWeight f x0 y x*(v x)^2 := by
  simp only [adversaryDualWeight,mul_add,add_mul,Finset.sum_add_distrib]
  have hh : (∑ x, a*(if x=x0 then 1-∑ z, y (Sum.inl z) else 0)*(v x)^2) =
      a*(1-∑ z, y (Sum.inl z))*(v x0)^2 := by
    simp only [mul_ite,ite_mul]
    simp
  rw [hh]
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  have he : (∑ x, a*y (Sum.inl x)*(v x)^2) = ∑ x, y (Sum.inl x)*(a*(v x)^2) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  ring
end
noncomputable section

/-- Pairing the equality SDP dual slack with a block outer product equals the quadratic form of
the cost-weighted dual diagonal minus the filtered dual matrix. -/
theorem adversaryEquality_dual_quadratic (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) (i : K) (v : X → ℝ) :
    ⟪(adversaryEqualityProgram input f alpha x0).constraint.adjoint y -
      (adversaryEqualityProgram input f alpha x0).objective,adversaryBlockRankOne f i v⟫_ℝ =
      dotProduct v ((Matrix.diagonal (fun x => alpha i*adversaryDualWeight f x0 y x) -
        genAdvFilter input (adversaryDualMatrix f y) i) *ᵥ v) := by
  rw [adversaryEquality_rankOne_slack]
  have hh := adversaryDualMatrix_pairing f y
    (fun x z => if input x i ≠ input z i then v x*v z else 0)
    (fun x z => by by_cases h : input x i = input z i <;> simp [h,eq_comm,mul_comm])
  rw [hh]
  have hdiag := adversaryDualWeight_quadratic f x0 y (alpha i) v
  have he : dotProduct v ((Matrix.diagonal (fun x => alpha i*adversaryDualWeight f x0 y x) -
      genAdvFilter input (adversaryDualMatrix f y) i) *ᵥ v) =
      (∑ x, alpha i*adversaryDualWeight f x0 y x*(v x)^2) -
      ∑ x, ∑ z, adversaryDualMatrix f y x z*(if input x i ≠ input z i then v x*v z else 0) := by
    rw [Matrix.sub_mulVec,dotProduct_sub]
    congr 1
    · simp only [Matrix.mulVec_diagonal,dotProduct]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      change v x*((if input x i ≠ input z i then adversaryDualMatrix f y x z else 0)*v z) = _
      split_ifs <;> ring
  rw [he]
  linarith
end
noncomputable section

/-- Every coordinate slack matrix extracted from feasible equality SDP dual data is positive
semidefinite. -/
theorem adversaryEquality_dual_psd (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (y : EuclideanSpace ℝ (AdversarySdpConstraints f))
    (hy : (adversaryEqualityProgram input f alpha x0).DualFeasible y) (i : K) :
    (Matrix.diagonal (fun x => alpha i*adversaryDualWeight f x0 y x) -
      genAdvFilter input (adversaryDualMatrix f y) i).PosSemidef := by
  have hs : (Matrix.diagonal (fun x => alpha i*adversaryDualWeight f x0 y x) -
      genAdvFilter input (adversaryDualMatrix f y) i).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro x z
    have hs : adversaryDualMatrix f y z x = adversaryDualMatrix f y x z :=
      congrFun (congrFun (adversaryDualMatrix_symm f y) x) z
    change star ((if z=x then alpha i*adversaryDualWeight f x0 y z else 0) -
      (if input z i ≠ input x i then adversaryDualMatrix f y z x else 0)) =
      (if x=z then alpha i*adversaryDualWeight f x0 y x else 0) -
      (if input x i ≠ input z i then adversaryDualMatrix f y x z else 0)
    simp only [star_trivial,ne_comm,hs]
    by_cases h : x=z
    · subst z; rfl
    · rw [if_neg h,if_neg (Ne.symm h)]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs
  intro v
  have hh := HermitianMat.inner_ge_zero hy (adversaryBlockRankOne_psd f i v)
  rw [adversaryEquality_dual_quadratic] at hh
  simpa only [Pi.star_apply,star_trivial] using! hh
end
noncomputable section

/-- Every different-output pair coefficient of a feasible equality SDP dual vector is
nonpositive. -/
theorem adversaryEquality_dual_pair_nonpos (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (y : EuclideanSpace ℝ (AdversarySdpConstraints f))
    (hy : (adversaryEqualityProgram input f alpha x0).DualFeasible y) (xy : AdversarySdpPairs f) :
    y (Sum.inr xy) ≤ 0 := by
  let r : AdversarySdpPairs f → ℝ := Pi.single xy 1
  have hr : ∀ z, 0 ≤ r z := by
    intro z
    simp only [r,Pi.single_apply]
    split_ifs <;> norm_num
  have hh := HermitianMat.inner_ge_zero hy (adversarySlackDiagonal_psd (K := K) f r hr)
  rw [adversaryEquality_slack_pairing] at hh
  simp only [adversarySlackDiagonal_budget,sub_self,mul_zero,Finset.sum_const_zero,
    zero_add,add_zero,adversarySlackDiagonal_pair] at hh
  have he : (∑ z, y (Sum.inr z)*(-r z)) = -y (Sum.inr xy) := by
    simp [r,Pi.single_apply]
  rw [he] at hh
  linarith
end
noncomputable section

/-- With positive costs and a nonempty coordinate type, feasible equality SDP dual data yield
feasible minimax primal data through the corrected weights and extracted matrix. -/
theorem adversaryEquality_dual_to_primal [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) (ha : ∀ i, 0 < alpha i)
    (x0 : X) (y : EuclideanSpace ℝ (AdversarySdpConstraints f))
    (hy : (adversaryEqualityProgram input f alpha x0).DualFeasible y) :
    MinimaxSdpPrimalFeasible input f alpha (adversaryDualWeight f x0 y) (adversaryDualMatrix f y) := by
  have hp := adversaryEquality_dual_psd input f alpha x0 y hy
  have hpair : ∀ x z, adversaryDualPair f y x z ≤ 0 := by
    intro x z
    unfold adversaryDualPair
    split_ifs with h
    · exact adversaryEquality_dual_pair_nonpos input f alpha x0 y hy ⟨(x,z),h⟩
    · exact le_rfl
  refine ⟨?_,adversaryDualWeight_sum f x0 y,adversaryDualMatrix_symm f y,?_,
    adversaryDualMatrix_support f y,hp⟩
  · intro x
    let i : K := Classical.arbitrary K
    have hh := (hp i).diag_nonneg (i := x)
    change 0 ≤ (if x=x then alpha i*adversaryDualWeight f x0 y x else 0) -
      (if input x i ≠ input x i then adversaryDualMatrix f y x x else 0) at hh
    simp only [ne_eq,not_true_eq_false,↓reduceIte,sub_zero] at hh
    nlinarith [ha i]
  · intro x z
    unfold adversaryDualMatrix
    linarith [hpair x z,hpair z x]
end
noncomputable section

/-- The equality SDP dual score is the negative sum of all entries of the extracted dual matrix. -/
theorem adversaryEquality_dualScore (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (x0 : X) (y : EuclideanSpace ℝ (AdversarySdpConstraints f)) :
    (adversaryEqualityProgram input f alpha x0).dualScore y =
      -(∑ x, ∑ z, adversaryDualMatrix f y x z) := by
  have hh := adversaryDualMatrix_pairing f y (fun _ _ => 1) (fun _ _ => rfl)
  simp only [mul_one] at hh
  rw [← hh]
  simp [Program.dualScore,adversaryEqualityProgram,PiLp.inner_apply,RCLike.inner_apply,
    Fintype.sum_sum_type]
end
noncomputable section

/-- With nonnegative costs, the zero dual vector is feasible for the equality SDP. -/
theorem adversaryEquality_zero_dual (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 ≤ alpha i) (x0 : X) :
    (adversaryEqualityProgram input f alpha x0).DualFeasible 0 := by
  unfold Program.DualFeasible
  rw [map_zero,zero_sub]
  apply HermitianMat.zero_le_iff.mpr
  let d : AdversarySdpIndex f K → ℝ := fun s => match s with
    | Sum.inl (x,i) => if x=x0 then -alpha i else 0
    | Sum.inr _ => 0
  have he : (-(adversaryEqualityProgram input f alpha x0).objective).mat =
      Matrix.diagonal (fun s => ((-d s : ℝ) : ℂ)) := by
    ext s t
    by_cases hst : s=t
    · subst t
      simp [adversaryEqualityProgram,d,HermitianMat.diagonal_mat,Matrix.diagonal,-HermitianMat.mat_apply]
    · simp [adversaryEqualityProgram,d,HermitianMat.diagonal_mat,Matrix.diagonal,hst,-HermitianMat.mat_apply]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro s
  cases s with
  | inl xi =>
    obtain ⟨x,i⟩ := xi
    by_cases hx : x=x0
    · change 0 ≤ ((-(if x=x0 then -alpha i else 0) : ℝ) : ℂ)
      rw [if_pos hx,neg_neg]
      exact Complex.nonneg_iff.mpr ⟨ha i,rfl⟩
    · change 0 ≤ ((-(if x=x0 then -alpha i else 0) : ℝ) : ℂ)
      rw [if_neg hx]
      norm_num
  | inr xy => change 0 ≤ ((-(0 : ℝ) : ℝ) : ℂ); norm_num
end
noncomputable section

/-- For a nonconstant function with observable outputs and positive costs, the real nonnegative
adversary value equals the minimax value. -/
theorem advAlphaR_eq_minimax_of_observable (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hobs : OutputObservable input f) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR input f alpha = minimaxAlpha input f alpha := by
  obtain ⟨x0,z0,hxz⟩ := hnc
  obtain ⟨i0,_⟩ := hobs x0 z0 hxz
  letI : Nonempty K := ⟨i0⟩
  have hnc : ∃ x z, f x ≠ f z := ⟨x0,z0,hxz⟩
  have hfin := ((minimaxAlpha_finite_iff_observable input f alpha ha hnc).mpr hobs).ne
  let t := (minimaxAlpha input f alpha).toReal
  have ht : 0 < t := ENNReal.toReal_pos (minimaxAlpha_ne_zero input f alpha hnc) hfin
  have hte : ENNReal.ofReal t = minimaxAlpha input f alpha := ENNReal.ofReal_toReal hfin
  obtain ⟨p,hp⟩ := minimax_optimal_exists input f alpha hnc
  have hpair : ∀ x z, f x ≠ f z → 1/t ≤ advMinimaxTerm input alpha p x z :=
    pair_of_minimaxWitnessValue_le input f alpha (fun i => (ha i).le) p t ht (hp.2.trans hte.symm).le
  have hLift := adversaryProbabilityLift_feasible input f alpha ha p hp.1 t ht x0 hpair
  let P := adversaryEqualityProgram input f alpha x0
  have hlub : IsLUB P.primalValues (-t) := by
    constructor
    · rintro s ⟨H,hH,rfl⟩
      have hg := adversaryEquality_to_gram input f alpha x0 H hH
      have hbudget := minimaxGram_objective_pos input f alpha ha hnc _ _ hg
      have hval := (minimaxGram_feasible_iff_value input f alpha ha hnc _ hbudget).mp ⟨_,hg⟩
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hval
      rw [ENNReal.toReal_ofReal hbudget.le] at hb
      rw [adversaryEquality_primalScore]
      exact neg_le_neg hb
    · intro b hb
      have hmem : P.primalScore (adversaryProbabilityLift input f alpha p t) ∈ P.primalValues :=
        ⟨adversaryProbabilityLift input f alpha p t,hLift.1,rfl⟩
      have h := hb hmem
      rwa [hLift.2] at h
  obtain ⟨s,hs,_,y,hy,hscore⟩ := (Qatlib.Concepts.SdpDuality.StrongDuality.Program.primalSlater_strong_duality P)
    (adversaryEquality_primalSlater input f alpha hobs x0)
    (adversaryEquality_zero_dual input f alpha (fun i => (ha i).le) x0)
  have hsval : s = -t := hs.unique hlub
  have hAprimal := adversaryEquality_dual_to_primal input f alpha ha x0 y hy
  have hAvalue : (∑ x, ∑ z, adversaryDualMatrix f y x z) = t := by
    rw [adversaryEquality_dualScore] at hscore
    linarith
  apply le_antisymm (advAlphaR_le_minimax_of_observable input f alpha ha hobs hnc)
  have hbound := minimaxSdp_score_le_source input f alpha ha hobs
    (adversaryDualWeight f x0 y) (adversaryDualMatrix f y) hAprimal
  rw [hAvalue,hte] at hbound
  exact hbound
end
noncomputable section
omit [DecidableEq X] in

/-- With positive costs, two identically encoded inputs with different outputs force the minimax
value to be infinite. -/
theorem minimaxAlpha_infinite_of_collision (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (x z : X) (hxz : f x ≠ f z) (he : ∀ i, input x i = input z i) :
    minimaxAlpha input f alpha = ⊤ := by
  let J := AdversarySdpPairs f
  haveI : Nonempty J := ⟨⟨(x,z),hxz⟩⟩
  have hden (p : X → K → ℝ) : (⨅ xy : J, advMinimaxTerm input alpha p xy.val.1 xy.val.2) = 0 := by
    apply le_antisymm
    · have hh := ciInf_le (Set.finite_range (fun xy : J => advMinimaxTerm input alpha p xy.val.1 xy.val.2)).bddBelow
        (⟨(x,z),hxz⟩ : J)
      have hz : advMinimaxTerm input alpha p x z = 0 := by simp [advMinimaxTerm,he]
      exact hh.trans_eq hz
    · apply le_ciInf
      intro xy
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact div_nonneg (Real.sqrt_nonneg _) (ha i).le
      · exact le_rfl
  unfold minimaxAlpha
  have hs : (⨆ p : {p : X → K → ℝ // IsProbabilityFamily p}, ENNReal.ofReal
      (⨅ xy : J, advMinimaxTerm input alpha p.val xy.val.1 xy.val.2)) = 0 := by
    apply le_antisymm
    · apply iSup_le
      intro p
      rw [hden p.val,ENNReal.ofReal_zero]
    · exact bot_le
  change (⨆ p : {p : X → K → ℝ // IsProbabilityFamily p}, ENNReal.ofReal
    (⨅ xy : J, advMinimaxTerm input alpha p.val xy.val.1 xy.val.2))⁻¹ = ⊤
  rw [hs,ENNReal.inv_zero]
end
noncomputable section

/-- For every nonconstant Boolean output function and positive coordinate costs, the real
nonnegative adversary and minimax values are equal, as in [HoyerLeeSpalek2007]. -/
theorem advAlphaR_eq_minimax (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR input f alpha = minimaxAlpha input f alpha := by
  by_cases hobs : OutputObservable input f
  · exact advAlphaR_eq_minimax_of_observable input f alpha ha hobs hnc
  · unfold OutputObservable at hobs
    push Not at hobs
    obtain ⟨x,z,hxz,he⟩ := hobs
    rw [(advAlphaR_infinite_of_collision input f alpha ha x z hxz he).2,
      minimaxAlpha_infinite_of_collision input f alpha ha x z hxz he]
end
noncomputable section

/-- On a domain of Boolean words, a nonconstant function with positive coordinate costs has
equal real nonnegative adversary and minimax values. -/
theorem advAlphaR_word_eq_minimax (D : Set (K → Bool)) (f : D → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : D => x.val) f alpha = minimaxAlpha (fun x : D => x.val) f alpha :=
  advAlphaR_eq_minimax _ f alpha ha hnc
end
noncomputable section

/-- On a domain of Boolean words, a nonconstant function with positive costs has equal adversary
and minimax values and possesses both an optimal nonzero nonnegative symmetric adversary
matrix and an optimal probability family, strengthening [Hoyer, Lee, and Spalek, Theorem
18][HoyerLeeSpalek2007] with optimizer existence. -/
theorem adversary_minimax_word_complete (D : Set (K → Bool)) (f : D → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : D => x.val) f alpha = minimaxAlpha (fun x : D => x.val) f alpha ∧
      ∃ (G : Matrix D D ℝ) (p : D → K → ℝ),
        (G.IsSymm ∧ (∀ x z, 0 ≤ G x z) ∧ (∀ x z, f x = f z → G x z = 0) ∧ G ≠ 0 ∧
          advAlphaWitnessR (fun x : D => x.val) alpha G = advAlphaR (fun x : D => x.val) f alpha) ∧
        IsMinimaxOptimal (fun x : D => x.val) f alpha p :=
  ⟨advAlphaR_word_eq_minimax D f alpha ha hnc,adversary_minimax_word_optimizers_exist D f alpha ha hnc⟩
end
noncomputable section

/-- For positive coordinate costs and nonconstant inner and composed functions, finite inner
real nonnegative adversary values give costs under which the outer adversary value bounds
the composed adversary value. -/
theorem source_adversary_composition_upper {k : ℕ} [Nonempty (Fin k)]
    {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (beta : Fin k → ℝ) (ha : ∀ c, 0 < alpha c)
    (hne : ∃ x z, composedFunction g f x ≠ composedFunction g f z)
    (hgne : ∀ i, ∃ a b, g i a ≠ g i b)
    (hbeta : ∀ i, advAlphaR (gin i) (g i) (fun j => alpha ⟨i,j⟩) = ENNReal.ofReal (beta i)) :
    advAlphaR (composedInput gin) (composedFunction g f) alpha ≤
      advAlphaR (fun u : Fin k → Bool => u) f beta := by
  have hobs (i : Fin k) : OutputObservable (gin i) (g i) := by
    apply (advAlphaR_finite_iff_observable (gin i) (g i) (fun j => alpha ⟨i,j⟩)
      (fun j => ha ⟨i,j⟩) (hgne i)).mp
    rw [hbeta i]
    exact ENNReal.ofReal_lt_top
  haveI : ∀ i, Nonempty (Fin (n i)) := fun i => by
    obtain ⟨a,b,hab⟩ := hgne i
    obtain ⟨j,_⟩ := hobs i a b hab
    exact ⟨j⟩
  have hbm (i : Fin k) : minimaxAlpha (gin i) (g i) (fun j => alpha ⟨i,j⟩) = ENNReal.ofReal (beta i) :=
    (advAlphaR_eq_minimax (gin i) (g i) _ (fun j => ha ⟨i,j⟩) (hgne i)).symm.trans (hbeta i)
  have hb (i : Fin k) : 0 < beta i := by
    have hh := minimaxAlpha_ne_zero (gin i) (g i) (fun j => alpha ⟨i,j⟩) (hgne i)
    rw [hbm i] at hh
    exact ENNReal.ofReal_ne_zero_iff.mp hh
  have hfne : ∃ u v, f u ≠ f v := by
    obtain ⟨x,z,hxz⟩ := hne
    exact ⟨fun i => g i (x i),fun i => g i (z i),hxz⟩
  rw [advAlphaR_eq_minimax (composedInput gin) (composedFunction g f) alpha ha hne,
    advAlphaR_eq_minimax (fun u : Fin k → Bool => u) f beta hb hfne]
  exact minimax_composition_upper gin g f alpha beta (fun c => (ha c).le) (fun i => (hb i).le)
    hne hgne hbm
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
