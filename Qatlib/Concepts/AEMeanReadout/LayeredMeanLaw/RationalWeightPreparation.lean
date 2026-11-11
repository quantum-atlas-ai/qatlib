/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffEncoding
import Qatlib.Concepts.BlockEncoding.LCU
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation

/-!
# Preparation of rationally weighted states

This module defines rational weight ratios, two-level rotation words, and their ideal
square-root counterparts. For nonnegative weights of positive total mass, `idealWeightPrepare`
prepares `rationalWeightTarget` exactly, while `rationalWeightPrepare` has an explicit operator
norm error and finite comparison count. These preparations supply the weighted superpositions
used in the LCU framework of [GilyenSuLowWiebe2019].

## Main statements

* `rational_weight_data_ranges_and_actual_comparisons`: bounds the ratios and counts `2*n*k`
  rational comparisons.
* `rational_weight_numerical_word_unitary_and_error`: proves unitarity and error at most
  `32*n/2^k`.
* `rational_weight_ideal_preparation_exact`: identifies the ideal output and proves its
  normalization.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- The sum of all rational weights on `Option (Fin n)`. -/
def rationalWeightMass {n : ℕ} (w : Option (Fin n) → ℚ) : ℚ := ∑ a, w a
/-- The weight at `none` plus the weights at indices greater than or equal to `j`. -/
def rationalWeightTail {n : ℕ} (w : Option (Fin n) → ℚ) (j : Fin n) : ℚ :=
  w none + ∑ i, if j.val ≤ i.val then w (some i) else 0
/-- The ratio of the weight at `some j` to its remaining tail mass. -/
def rationalWeightRatio {n : ℕ} (w : Option (Fin n) → ℚ) (j : Fin n) : ℚ :=
  w (some j) / rationalWeightTail w j
/-- The list of rational rotation coefficient pairs computed from the weight ratios at precision
`k`. -/
def rationalWeightData {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ) :
    List (ℚ × ℚ) := List.ofFn (fun j => rationalPayoffCS (rationalWeightRatio w j) k)
/-- The total comparison count of the square-root bracket computations for all weight ratios and
their complements. -/
def rationalWeightComparisons {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ) : ℕ :=
  (List.ofFn (fun j : Fin n =>
    (rationalSqrtBracket (rationalWeightRatio w j) k).2.2 +
    (rationalSqrtBracket (1-rationalWeightRatio w j) k).2.2)).sum

/-- The matrix with block `[[c, -s], [s, c]]` on the coordinates `none` and `some j`, acting as
the identity elsewhere. -/
noncomputable def weightTwoLevel {n : ℕ} (j : Fin n) (c s : ℂ) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℂ := fun a b =>
  if a = none ∧ b = none then c else
  if a = some j ∧ b = some j then c else
  if a = none ∧ b = some j then -s else
  if a = some j ∧ b = none then s else if a = b then 1 else 0
/-- The two-level gate formed from the rational payoff rotation coefficients for the weight
ratio at `j`. -/
noncomputable def rationalWeightGate {n : ℕ} (w : Option (Fin n) → ℚ)
    (k : ℕ) (j : Fin n) :=
  weightTwoLevel j (rationalPayoffCS (rationalWeightRatio w j) k).1
    (rationalPayoffCS (rationalWeightRatio w j) k).2
/-- The two-level gate whose coefficients are the real square roots of one minus the weight
ratio and of the weight ratio. -/
noncomputable def idealWeightGate {n : ℕ} (w : Option (Fin n) → ℚ) (j : Fin n) :=
  weightTwoLevel j (Real.sqrt (1-(rationalWeightRatio w j : ℝ)))
    (Real.sqrt (rationalWeightRatio w j : ℝ))
/-- The reversed list of rational two-level weight gates, as an adjoint circuit word. -/
noncomputable def rationalWeightWord {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ) :
    List (AdjointStep (Option (Fin n))) :=
  (List.ofFn (fun j => AdjointStep.gate (rationalWeightGate w k j))).reverse
/-- The reversed list of ideal square-root weight gates, as an adjoint circuit word. -/
noncomputable def idealWeightWord {n : ℕ} (w : Option (Fin n) → ℚ) :
    List (AdjointStep (Option (Fin n))) :=
  (List.ofFn (fun j => AdjointStep.gate (idealWeightGate w j))).reverse
/-- The matrix obtained by evaluating the rational weight preparation word with identity oracle. -/
noncomputable def rationalWeightPrepare {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ) :=
  evaluate 1 (rationalWeightWord w k)
/-- The matrix obtained by evaluating the ideal weight preparation word with identity oracle. -/
noncomputable def idealWeightPrepare {n : ℕ} (w : Option (Fin n) → ℚ) :=
  evaluate 1 (idealWeightWord w)
/-- The state whose amplitudes are the square roots of the rational weights divided by their
total mass. -/
noncomputable def rationalWeightTarget {n : ℕ} (w : Option (Fin n) → ℚ) :
    QState (Option (Fin n)) := fun a => Real.sqrt ((w a / rationalWeightMass w : ℚ) : ℝ)
/-- The rational weight preparation word tensored with the identity on the data register `I`. -/
noncomputable def rationalWeightLiftWord {n : ℕ} (I : Type) [Fintype I] [DecidableEq I]
    (w : Option (Fin n) → ℚ) (k : ℕ) : List (AdjointStep (Option (Fin n) × I)) :=
  (List.ofFn (fun j => AdjointStep.gate
    (TensorGate (rationalWeightGate w k j) (1 : Matrix I I ℂ)))).reverse

/-- For nonnegative weights, the tail at `j` is at least the weight at `some j`. -/
theorem rationalWeightTail_ge {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (j : Fin n) : w (some j) ≤ rationalWeightTail w j := by
  have hsum : w (some j) ≤ ∑ i : Fin n, if j.val ≤ i.val then w (some i) else 0 := by
    simpa using! Finset.single_le_sum (f := fun i : Fin n => if j.val ≤ i.val then w (some i) else 0)
      (fun i (_ : i ∈ Finset.univ) => by (try dsimp only); split_ifs; exact hw _; exact le_rfl)
      (Finset.mem_univ j)
  unfold rationalWeightTail
  linarith [hw none]

/-- Every weight ratio lies in `[0, 1]` when all weights are nonnegative. -/
theorem rationalWeightRatio_range {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (j : Fin n) :
    0 ≤ rationalWeightRatio w j ∧ rationalWeightRatio w j ≤ 1 := by
  have hle := rationalWeightTail_ge w hw j
  have ht : 0 ≤ rationalWeightTail w j := (hw (some j)).trans hle
  unfold rationalWeightRatio
  refine ⟨div_nonneg (hw _) ht, ?_⟩
  by_cases hz : rationalWeightTail w j = 0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne ht (Ne.symm hz))).mpr hle

/-- For nonnegative weights, all ratios lie in `[0, 1]`, the coefficient list has length `n`,
and the comparison count is exactly `2*n*k`. -/
theorem rational_weight_data_ranges_and_actual_comparisons : ∀ (n k : ℕ)
    (w : Option (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
    (∀ j, 0 ≤ rationalWeightRatio w j ∧ rationalWeightRatio w j ≤ 1) ∧
    (rationalWeightData w k).length = n ∧ rationalWeightComparisons w k = 2*n*k := by
  intro n k w hw
  refine ⟨rationalWeightRatio_range w hw, by simp [rationalWeightData], ?_⟩
  have hc (j : Fin n) :
      (rationalSqrtBracket (rationalWeightRatio w j) k).2.2 +
      (rationalSqrtBracket (1-rationalWeightRatio w j) k).2.2 = 2*k := by
    obtain ⟨h0, h1⟩ := rationalWeightRatio_range w hw j
    have h := rational_sqrt_bracket_actual_interval_and_comparisons
      (rationalWeightRatio w j) k h0 h1
    have h' := rational_sqrt_bracket_actual_interval_and_comparisons
      (1-rationalWeightRatio w j) k (by linarith) (by linarith)
    rw [h.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.1]
    omega
  simp only [rationalWeightComparisons, hc]
  simp [List.ofFn_const, mul_comm, mul_left_comm, mul_assoc]

/-- The two-level matrix mixes the `none` and `some j` components with coefficients `c` and `s`
and fixes every other component. -/
theorem weightTwoLevel_mulVec {n : ℕ} (j : Fin n) (c s : ℂ)
    (v : Option (Fin n) → ℂ) (a : Option (Fin n)) :
    (weightTwoLevel j c s *ᵥ v) a =
      if a = none then c * v none - s * v (some j) else
      if a = some j then s * v none + c * v (some j) else v a := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
  cases a with
  | none =>
    rw [Finset.sum_eq_single j]
    · simp [weightTwoLevel, sub_eq_add_neg]
    · intro i _ hij
      simp [weightTwoLevel, hij]
    · simp
  | some i =>
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst i; simp [weightTwoLevel, add_comm]
      · simp [weightTwoLevel, hij]
    · intro l _ hli
      by_cases hi : i = j
      · subst i; simp [weightTwoLevel, hli, Ne.symm hli]
      · simp [weightTwoLevel, hi, Ne.symm hli]
    · simp

/-- A two-level matrix with real coefficients satisfying `c²+s²=1` is unitary. -/
theorem weightTwoLevel_unitary {n : ℕ} (j : Fin n) (c s : ℝ)
    (hcs : c^2+s^2=1) :
    weightTwoLevel j c s ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ := by
  classical
  have hc : (c : ℂ)^2+(s : ℂ)^2=1 := by exact_mod_cast hcs
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext a b
  change (weightTwoLevel j c s *ᵥ (fun t => star (weightTwoLevel j c s b t))) a = _
  rw [weightTwoLevel_mulVec]
  cases a with
  | none =>
    cases b with
    | none => simp [weightTwoLevel, Matrix.one_apply]; linear_combination hc
    | some l =>
      by_cases hl : l = j
      · subst l; simp [weightTwoLevel, Matrix.one_apply]; ring
      · simp [weightTwoLevel, hl, Matrix.one_apply]
  | some i =>
    cases b with
    | none =>
      by_cases hi : i = j
      · subst i; simp [weightTwoLevel, Matrix.one_apply]; ring
      · simp [weightTwoLevel, hi, Ne.symm hi, Matrix.one_apply]
    | some l =>
      by_cases hi : i = j <;> by_cases hl : l = j
      · subst i; subst l
        simp [weightTwoLevel, Matrix.one_apply]; linear_combination hc
      · subst i; simp [weightTwoLevel, hl, Ne.symm hl, Matrix.one_apply]
      · subst l; simp [weightTwoLevel, hi, Ne.symm hi, Matrix.one_apply]
      · by_cases hil : i = l
        · subst l; simp [weightTwoLevel, hi, Ne.symm hi, Matrix.one_apply]
        · simp [weightTwoLevel, hi, hl, Ne.symm hi, Ne.symm hl, hil, Ne.symm hil, Matrix.one_apply]

/-- Every rational weight gate is unitary. -/
theorem rationalWeightGate_unitary {n : ℕ} (w : Option (Fin n) → ℚ)
    (k : ℕ) (j : Fin n) : rationalWeightGate w k j ∈ Matrix.unitaryGroup _ ℂ := by
  have hc : ((rationalPayoffCS (rationalWeightRatio w j) k).1 : ℝ)^2 +
      ((rationalPayoffCS (rationalWeightRatio w j) k).2 : ℝ)^2 = 1 := by
    exact_mod_cast rationalPayoffCS_circle (rationalWeightRatio w j) k
  simpa only [rationalWeightGate, Complex.ofReal_ratCast] using! weightTwoLevel_unitary j _ _ hc

/-- Every ideal weight gate is unitary when the weights are nonnegative. -/
theorem idealWeightGate_unitary {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (j : Fin n) : idealWeightGate w j ∈ Matrix.unitaryGroup _ ℂ := by
  obtain ⟨h0, h1⟩ := rationalWeightRatio_range w hw j
  have h0r : (0 : ℝ) ≤ rationalWeightRatio w j := by exact_mod_cast h0
  have h1r : (rationalWeightRatio w j : ℝ) ≤ 1 := by exact_mod_cast h1
  apply weightTwoLevel_unitary
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt h0r]
  ring

/-- The rational weight preparation word is a well-formed adjoint circuit. -/
theorem rationalWeightWord_wellFormed {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ) :
    WellFormedAdjointCircuit (rationalWeightWord w k) := by
  intro V hV
  simp only [rationalWeightWord, List.mem_reverse, List.mem_ofFn] at hV
  obtain ⟨j, hj⟩ := hV
  cases hj
  exact rationalWeightGate_unitary w k j

/-- The ideal weight preparation word is well formed for nonnegative weights. -/
theorem idealWeightWord_wellFormed {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) : WellFormedAdjointCircuit (idealWeightWord w) := by
  intro V hV
  simp only [idealWeightWord, List.mem_reverse, List.mem_ofFn] at hV
  obtain ⟨j, hj⟩ := hV
  cases hj
  exact idealWeightGate_unitary w hw j

/-- A reversed word of `n` fixed gates has zero oracle queries and exactly `n` fixed gates. -/
theorem weight_fixed_word_counts {n : ℕ} (g : Fin n → Matrix (Option (Fin n)) (Option (Fin n)) ℂ) :
    adjointQueryCount (List.ofFn (fun j => AdjointStep.gate (g j))).reverse = 0 ∧
    adjointGateCount (List.ofFn (fun j => AdjointStep.gate (g j))).reverse = n := by
  have h (l : List (AdjointStep (Option (Fin n))))
      (hl : ∀ x ∈ l, ∃ V, x = AdjointStep.gate V) :
      adjointQueryCount l = 0 ∧ adjointGateCount l = l.length := by
    induction l with
    | nil => simp [adjointQueryCount, adjointGateCount]
    | cons c l ih =>
      obtain ⟨V, rfl⟩ := hl c (by simp)
      have htail := ih (fun x hx => hl x (by simp [hx]))
      simp [adjointQueryCount, adjointGateCount, htail]
  simpa using! h (List.ofFn (fun j => AdjointStep.gate (g j))).reverse (by
    intro x hx
    simp only [List.mem_reverse, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨g j, rfl⟩)

/-- Repeating a rational preparation word followed by its adjoint `r` times evaluates to the
identity. The resulting word is well formed, uses no oracle queries, and has `2*r*n` fixed
gates. -/
theorem rational_weight_paid_inverse_reuse : ∀ (n k r : ℕ) (w : Option (Fin n) → ℚ),
    (∀ a, 0 ≤ w a) →
    let word := rationalWeightWord w k ++ adjointCircuit (rationalWeightWord w k);
    evaluate (1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ)
        (repeatAdjointWord word r) = 1 ∧
    adjointQueryCount (repeatAdjointWord word r) = 0 ∧
    adjointGateCount (repeatAdjointWord word r) = 2*r*n ∧
    WellFormedAdjointCircuit (repeatAdjointWord word r) := by
  intro n k r w _
  (try dsimp only)
  obtain ⟨hWF, hE, hQ, hG⟩ := adjointCircuit_roundTrip
    (1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ)
    (rationalWeightWord w k) (by simp) (rationalWeightWord_wellFormed w k)
  have hc := weight_fixed_word_counts (rationalWeightGate w k)
  change adjointQueryCount (rationalWeightWord w k) = 0 ∧
    adjointGateCount (rationalWeightWord w k) = n at hc
  obtain ⟨hrE, hrQ, hrG, hrWF⟩ := repeat_adjoint_word_semantics_cost
    (1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ)
    (rationalWeightWord w k ++ adjointCircuit (rationalWeightWord w k)) r
  refine ⟨by simpa [hE] using! hrE, by simpa [hQ, hc.1] using! hrQ,
    by simpa [hG, hc.2, mul_left_comm, mul_assoc] using! hrG, hrWF hWF⟩

/-- The operator norm difference of two two-level matrices is at most the sum of the absolute
differences of their real coefficients. -/
theorem weightTwoLevel_error {n : ℕ} (j : Fin n) (c s c' s' : ℝ) :
    ‖weightTwoLevel j c s - weightTwoLevel j c' s'‖ ≤ |c-c'| + |s-s'| := by
  classical
  let X : Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
    permMatrix (Equiv.swap none (some j))
  let C : Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
    Matrix.diagonal (fun a => if a = none ∨ a = some j then ((c-c' : ℝ) : ℂ) else 0)
  let S : Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
    Matrix.diagonal (fun a => if a = none then ((-(s-s') : ℝ) : ℂ)
      else if a = some j then ((s-s' : ℝ) : ℂ) else 0)
  have he : weightTwoLevel j c s - weightTwoLevel j c' s' = C + S * X := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, C, S, X,
      permMatrix, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases ha : a = none <;> by_cases haj : a = some j <;>
      by_cases hb : b = none <;> by_cases hbj : b = some j <;>
      by_cases hab : a = b
    all_goals simp_all [weightTwoLevel, Equiv.swap_apply_def, Complex.ofReal_sub]
    all_goals ring
  have hC : ‖C‖ ≤ |c-c'| := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro a
    split_ifs <;> simp only [Complex.norm_real, Real.norm_eq_abs, norm_zero, abs_neg]
    all_goals first | exact le_refl _ | exact abs_nonneg _
  have hS : ‖S‖ ≤ |s-s'| := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro a
    split_ifs <;> simp only [Complex.norm_real, Real.norm_eq_abs, norm_zero, abs_neg]
    all_goals first | exact le_refl _ | exact abs_nonneg _
  have hX : ‖X‖ ≤ 1 := l2_norm_unitary_le_one
    (permMatrix_unitary (Equiv.swap_apply_self none (some j)))
  rw [he]
  calc
    _ ≤ ‖C‖ + ‖S*X‖ := norm_add_le _ _
    _ ≤ |c-c'| + |s-s'| * 1 := add_le_add hC
      ((norm_mul_le _ _).trans (mul_le_mul hS hX (norm_nonneg _) (abs_nonneg _)))
    _ = _ := by ring

/-- For nonnegative weights, each rational weight gate differs from its ideal counterpart by at
most `32/2^k` in operator norm. -/
theorem rationalWeightGate_error {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (k : ℕ) (j : Fin n) :
    ‖rationalWeightGate w k j - idealWeightGate w j‖ ≤ 32/(2 : ℝ)^k := by
  obtain ⟨h0, h1⟩ := rationalWeightRatio_range w hw j
  obtain ⟨hc, hs⟩ := rationalPayoffCS_sqrt_error (rationalWeightRatio w j) k h0 h1
  have h := weightTwoLevel_error j
    ((rationalPayoffCS (rationalWeightRatio w j) k).1 : ℝ)
    ((rationalPayoffCS (rationalWeightRatio w j) k).2 : ℝ)
    (Real.sqrt (1-(rationalWeightRatio w j : ℝ)))
    (Real.sqrt (rationalWeightRatio w j : ℝ))
  simp only [Complex.ofReal_ratCast] at h
  exact h.trans ((add_le_add hc hs).trans_eq (by ring))

/-- Products of corresponding unitary gates with individual error at most `δ` differ by at most
the list length times `δ` in operator norm. -/
theorem weight_gate_product_error {H J : Type} [Fintype H] [DecidableEq H]
    (g h : J → Matrix H H ℂ) (l : List J) (δ : ℝ) (hδ : 0 ≤ δ)
    (hg : ∀ j, g j ∈ Matrix.unitaryGroup H ℂ)
    (hh : ∀ j, h j ∈ Matrix.unitaryGroup H ℂ)
    (he : ∀ j, ‖g j - h j‖ ≤ δ) :
    ‖evaluate 1 ((l.map (fun j => AdjointStep.gate (g j))).reverse) -
      evaluate 1 ((l.map (fun j => AdjointStep.gate (h j))).reverse)‖ ≤ l.length * δ := by
  have hwf (f : J → Matrix H H ℂ) (hf : ∀ j, f j ∈ Matrix.unitaryGroup H ℂ) (l : List J) :
      WellFormedAdjointCircuit ((l.map (fun j => AdjointStep.gate (f j))).reverse) := by
    intro V hV
    simp only [List.mem_reverse, List.mem_map] at hV
    obtain ⟨j, _, hj⟩ := hV
    cases hj
    exact hf j
  induction l with
  | nil => simp [evaluate]
  | cons j l ih =>
    simp only [List.map_cons, List.reverse_cons, evaluate_append, evaluate, instructionMatrix,
      Matrix.mul_one, List.length_cons, Nat.cast_add, Nat.cast_one]
    let A := evaluate (1 : Matrix H H ℂ) ((l.map (fun j => AdjointStep.gate (g j))).reverse)
    let C := evaluate (1 : Matrix H H ℂ) ((l.map (fun j => AdjointStep.gate (h j))).reverse)
    change ‖A*g j-C*h j‖ ≤ _
    have hid : A*g j-C*h j = (A-C)*g j+C*(g j-h j) := by noncomm_ring
    have hC : ‖C‖ ≤ 1 := l2_norm_unitary_le_one ((hwf h hh l).evaluate_unitary (by simp))
    rw [hid]
    calc
      _ ≤ ‖(A-C)*g j‖+‖C*(g j-h j)‖ := norm_add_le _ _
      _ ≤ (l.length : ℝ)*δ*1+1*δ := add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul ih (l2_norm_unitary_le_one (hg j))
          (norm_nonneg _) (by positivity)))
        ((norm_mul_le _ _).trans (mul_le_mul hC (he j) (norm_nonneg _) (by norm_num)))
      _ = _ := by ring

/-- For nonnegative weights, the rational preparation word is well formed and its evaluation is
unitary. Its operator norm distance from the ideal preparation is at most `32*n/2^k`. -/
theorem rational_weight_numerical_word_unitary_and_error : ∀ (n k : ℕ)
    (w : Option (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
    WellFormedAdjointCircuit (rationalWeightWord w k) ∧
    rationalWeightPrepare w k ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ ∧
    ‖rationalWeightPrepare w k - idealWeightPrepare w‖ ≤ 32*(n : ℝ)/2^k := by
  intro n k w hw
  refine ⟨rationalWeightWord_wellFormed w k,
    (rationalWeightWord_wellFormed w k).evaluate_unitary (by simp), ?_⟩
  have h := weight_gate_product_error (rationalWeightGate w k) (idealWeightGate w)
    (List.ofFn (fun j : Fin n => j)) (32/(2 : ℝ)^k) (by positivity)
    (rationalWeightGate_unitary w k) (idealWeightGate_unitary w hw)
    (rationalWeightGate_error w hw k)
  simpa only [List.map_ofFn, List.length_ofFn, Function.comp_def, rationalWeightPrepare,
    idealWeightPrepare, rationalWeightWord, idealWeightWord,
    show (n : ℝ)*(32/2^k)=32*n/2^k by ring] using h

/-- The weight at `none` plus the weights at indices at least `t`. -/
def weightResidual {n : ℕ} (w : Option (Fin n) → ℚ) (t : ℕ) : ℚ :=
  w none + ∑ i, if t ≤ i.val then w (some i) else 0

/-- The partial preparation state with completed square-root amplitudes below `t` and the
residual square-root amplitude at `none`. -/
noncomputable def weightPrefixState {n : ℕ} (w : Option (Fin n) → ℚ) (t : ℕ) :
    QState (Option (Fin n))
  | none => Real.sqrt ((weightResidual w t / rationalWeightMass w : ℚ) : ℝ)
  | some i => if i.val < t then Real.sqrt ((w (some i) / rationalWeightMass w : ℚ) : ℝ) else 0

/-- The residual at `j` splits into the weight at `some j` and the residual after `j`. -/
theorem weightResidual_step {n : ℕ} (w : Option (Fin n) → ℚ) (j : Fin n) :
    weightResidual w j.val = w (some j) + weightResidual w (j.val+1) := by
  have hs : (∑ i : Fin n, if j.val ≤ i.val then w (some i) else 0) =
      w (some j) + ∑ i : Fin n, if j.val+1 ≤ i.val then w (some i) else 0 := by
    calc
      _ = ∑ i : Fin n, ((if i = j then w (some j) else 0) +
          (if j.val+1 ≤ i.val then w (some i) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · subst i; simp
        · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          by_cases hle : j.val ≤ i.val
          · simp [hij, hle, show j.val+1 ≤ i.val by omega]
          · simp [hij, hle, show ¬j.val+1 ≤ i.val by omega]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  unfold weightResidual
  rw [hs]
  ring

/-- Every residual mass is nonnegative when all weights are nonnegative. -/
theorem weightResidual_nonneg {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (t : ℕ) : 0 ≤ weightResidual w t := by
  apply add_nonneg (hw none)
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hw _
  · exact le_rfl

/-- For `0 ≤ b ≤ a` and positive `Z`, the product of the square roots of `b/a` and `a/Z` equals
the square root of `b/Z`. -/
theorem weight_sqrt_transport (a b Z : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hba : b ≤ a) (hZ : 0 < Z) :
    Real.sqrt ((b/a : ℚ) : ℝ) * Real.sqrt ((a/Z : ℚ) : ℝ) =
      Real.sqrt ((b/Z : ℚ) : ℝ) := by
  by_cases hz : a = 0
  · have hbz : b = 0 := by linarith
    simp [hz, hbz]
  · rw [← Real.sqrt_mul (by exact_mod_cast div_nonneg hb ha)]
    congr 1
    push_cast
    have har : (a : ℝ) ≠ 0 := by exact_mod_cast hz
    field_simp

/-- For nonnegative weights of positive mass, the ideal gate at `j` advances the prefix state
from `j` to `j+1`. -/
theorem weightPrefixState_step {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < rationalWeightMass w) (j : Fin n) :
    idealWeightGate w j *ᵥ weightPrefixState w j.val = weightPrefixState w (j.val+1) := by
  have ht := weightResidual_nonneg w hw j.val
  have ht' := weightResidual_nonneg w hw (j.val+1)
  have hstep := weightResidual_step w j
  have hratio : rationalWeightRatio w j = w (some j) / weightResidual w j.val := rfl
  have hs := weight_sqrt_transport (weightResidual w j.val) (w (some j))
    (rationalWeightMass w) ht (hw _) (by linarith) hZ
  have hc : Real.sqrt (1-(rationalWeightRatio w j : ℝ)) *
      Real.sqrt ((weightResidual w j.val / rationalWeightMass w : ℚ) : ℝ) =
      Real.sqrt ((weightResidual w (j.val+1) / rationalWeightMass w : ℚ) : ℝ) := by
    by_cases hz : weightResidual w j.val = 0
    · have hz' : weightResidual w (j.val+1) = 0 := by linarith [hw (some j)]
      simp [hz, hz']
    · have hr : (1-(rationalWeightRatio w j : ℝ)) =
          ((weightResidual w (j.val+1)/weightResidual w j.val : ℚ) : ℝ) := by
        rw [hratio]
        push_cast
        have he : (weightResidual w j.val : ℝ) =
            (w (some j) : ℝ) + (weightResidual w (j.val+1) : ℝ) := by exact_mod_cast hstep
        have hne : (weightResidual w j.val : ℝ) ≠ 0 := by exact_mod_cast hz
        field_simp
        linarith
      rw [hr]
      exact weight_sqrt_transport _ _ _ ht ht' (by linarith [hw (some j)]) hZ
  ext a
  rw [idealWeightGate, weightTwoLevel_mulVec]
  cases a with
  | none =>
    simpa [weightPrefixState, Complex.ofReal_mul] using! congrArg (fun x : ℝ => (x : ℂ)) hc
  | some i =>
    by_cases hij : i = j
    · subst i
      simpa [weightPrefixState, hratio, Complex.ofReal_mul] using!
          congrArg (fun x : ℝ => (x : ℂ)) hs
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have he : (i.val < j.val+1) = (i.val < j.val) := propext (by omega)
      simp [weightPrefixState, hij, he]

/-- When the total weight is positive, the initial prefix state is `Ket none`. -/
theorem weightPrefixState_zero {n : ℕ} (w : Option (Fin n) → ℚ)
    (hZ : 0 < rationalWeightMass w) : weightPrefixState w 0 = Ket none := by
  have hr : weightResidual w 0 = rationalWeightMass w := by
    simp [weightResidual, rationalWeightMass, Fintype.sum_option]
  ext a
  cases a <;> simp [weightPrefixState, hr, ne_of_gt hZ, Ket]

/-- After all `n` coordinates, the prefix state equals the target weighted state. -/
theorem weightPrefixState_final {n : ℕ} (w : Option (Fin n) → ℚ) :
    weightPrefixState w n = rationalWeightTarget w := by
  have hr : weightResidual w n = w none := by
    simp [weightResidual, show ∀ i : Fin n, ¬n ≤ i.val from fun i => by omega]
  ext a
  cases a with
  | none => simp [weightPrefixState, rationalWeightTarget, hr]
  | some i => simp [weightPrefixState, rationalWeightTarget, i.isLt]

/-- For nonnegative weights of positive mass, the first `t ≤ n` ideal gates prepare the
corresponding prefix state from `Ket none`. -/
theorem weight_prefix_exact {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < rationalWeightMass w)
    (t : ℕ) (ht : t ≤ n) :
    evaluate 1 (((List.ofFn (fun j => AdjointStep.gate (idealWeightGate w j))).take t).reverse)
      *ᵥ Ket none = weightPrefixState w t := by
  induction t with
  | zero => simp [evaluate, weightPrefixState_zero w hZ]
  | succ t ih =>
    have hn : t < n := by omega
    have hlen : t < (List.ofFn (fun j => AdjointStep.gate (idealWeightGate w j))).length := by simpa
    rw [List.take_succ_eq_append_getElem hlen, List.getElem_ofFn,
      List.reverse_append, evaluate_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, evaluate,
      instructionMatrix, Matrix.mul_one]
    rw [← Matrix.mulVec_mulVec, ih (by omega)]
    exact weightPrefixState_step w hw hZ ⟨t, hn⟩

/-- For nonnegative weights of positive mass, the ideal preparation is unitary and maps `Ket
none` to the normalized target state. -/
theorem rational_weight_ideal_preparation_exact : ∀ (n : ℕ) (w : Option (Fin n) → ℚ),
    (∀ a, 0 ≤ w a) → 0 < rationalWeightMass w →
    idealWeightPrepare w ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ ∧
    idealWeightPrepare w *ᵥ Ket none = rationalWeightTarget w ∧
    Normalized (rationalWeightTarget w) := by
  intro n w hw hZ
  have hu :=
      (idealWeightWord_wellFormed w hw).evaluate_unitary
      (show (1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) ∈ Matrix.unitaryGroup _ ℂ by simp)
  have he := weight_prefix_exact w hw hZ n le_rfl
  simp only [List.take_of_length_le (by simp : (List.ofFn (fun j => AdjointStep.gate (idealWeightGate w j))).length ≤ n),
    weightPrefixState_final] at he
  change idealWeightPrepare w *ᵥ Ket none = rationalWeightTarget w at he
  refine ⟨hu, he, ?_⟩
  rw [← he]
  exact normalized_applyGate hu (normalized_ket _)

end Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
