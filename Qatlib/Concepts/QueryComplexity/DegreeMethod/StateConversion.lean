/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.StateConversionDefs
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Fractional queries and state-conversion certificates

This module proves unitary and Gram-matrix identities for fractional Boolean phase queries and
constructs filtered certificates for their Gram changes. It also relates record projections to
target overlap and record marginals to matrix and Kraus actions, in the state-conversion
framework of [LeeEtAl2011].

The continuous-time lemmas bound filtered gamma-two values of integrals and supply tangent
factorizations, absolute-continuity results, and inner-product differentiation identities.
Record-block formulas express partial traces as sums of conjugations.

## Main statements

* `fractionalPhaseOracle_filteredCert`: a fractional query has a certificate of cost `Real.pi *
  |lam|`.
* `conversionRecord_noncoherent_iff`: achievable record overlap is characterized by the
  projection norm.
* `continuousConversion_filtered_integral`: uniform certificates bound the integrated matrix.
* `continuousConversionTangent_cert`: local cancellation and mass bounds yield a tangent
  certificate.
* `conversionTraceRecord_frame`: partial tracing a framed conjugation gives its record-block
  sum.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped BigOperators Classical

/-- The fractional phase of a false Boolean input is one. -/
@[simp] theorem fractionalBooleanPhase_false (lam : ℝ) :
    fractionalBooleanPhase lam false = 1 := rfl

/-- The fractional phase of a true Boolean input is `exp (i * pi * lam)`. -/
@[simp] theorem fractionalBooleanPhase_true (lam : ℝ) :
    fractionalBooleanPhase lam true = Complex.exp (Complex.I * (Real.pi * lam : ℝ)) := rfl

/-- Every fractional Boolean phase has complex norm one. -/
@[simp] theorem fractionalBooleanPhase_norm (lam : ℝ) (b : Bool) :
    ‖fractionalBooleanPhase lam b‖ = 1 := by
  cases b
  · exact norm_one
  · exact Complex.norm_exp_I_mul_ofReal (Real.pi * lam)

/-- The phase defect between two Boolean inputs has norm at most `Real.pi * |lam|`. -/
theorem fractionalBooleanPhase_chord_bound (lam : ℝ) (a b : Bool) :
    ‖1 - star (fractionalBooleanPhase lam a) * fractionalBooleanPhase lam b‖ ≤
      Real.pi * |lam| := by
  have h : ‖1 - Complex.exp (Complex.I * (Real.pi * lam : ℝ))‖ ≤ Real.pi * |lam| := by
    rw [norm_sub_rev]
    exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans_eq (by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos])
  cases a <;> cases b
  · simpa using! (show (0 : ℝ) ≤ Real.pi * |lam| by positivity)
  · simpa using! h
  · simp only [fractionalBooleanPhase_true, fractionalBooleanPhase_false, mul_one]
    rw [show (1 : ℂ) - star (Complex.exp (Complex.I * (Real.pi * lam : ℝ))) =
      star (1 - Complex.exp (Complex.I * (Real.pi * lam : ℝ))) by rw [star_sub, star_one],
      norm_star]
    exact h
  · rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, fractionalBooleanPhase_norm]
    norm_num
    positivity

/-- At an active query index, the padded query phase equals the fractional phase of the
corresponding input bit. -/
@[simp] theorem fractionalQueryPhase_active {n : ℕ} (input : Fin n → Bool)
    (lam : ℝ) (i : Fin n) :
    fractionalQueryPhase input lam i.castSucc = fractionalBooleanPhase lam (input i) := by
  simp [fractionalQueryPhase, i.isLt]

/-- The padded query phase at the final idle index is one. -/
@[simp] theorem fractionalQueryPhase_idle {n : ℕ} (input : Fin n → Bool) (lam : ℝ) :
    fractionalQueryPhase input lam (Fin.last n) = 1 := by
  simp [fractionalQueryPhase]

/-- The fractional query phase has norm one at every active or idle index. -/
@[simp] theorem fractionalQueryPhase_norm {n : ℕ} (input : Fin n → Bool)
    (lam : ℝ) (i : Fin (n + 1)) : ‖fractionalQueryPhase input lam i‖ = 1 := by
  unfold fractionalQueryPhase
  split <;> simp

/-- Applying the diagonal fractional oracle multiplies each amplitude by the phase of its query
index. -/
@[simp] theorem fractionalPhaseOracle_apply {W : Type} [Fintype W] [DecidableEq W]
    {n : ℕ} (input : Fin n → Bool) (lam : ℝ)
    (ψ : QState ((Fin (n + 1) × Fin 2) × W)) (p : (Fin (n + 1) × Fin 2) × W) :
    (fractionalPhaseOracle input lam *ᵥ ψ) p =
      fractionalQueryPhase input lam p.1.1 * ψ p := by
  simp [fractionalPhaseOracle, Matrix.mulVec_diagonal]

/-- The complex defect `1 - star (fractionalBooleanPhase lam a) * fractionalBooleanPhase lam b`
between two Boolean phases. -/
def fractionalPhaseDefect (lam : ℝ) (a b : Bool) : ℂ :=
  1 - star (fractionalBooleanPhase lam a) * fractionalBooleanPhase lam b

/-- The fractional phase defect vanishes when the two Boolean inputs agree. -/
@[simp] theorem fractionalPhaseDefect_self (lam : ℝ) (b : Bool) :
    fractionalPhaseDefect lam b b = 0 := by
  unfold fractionalPhaseDefect
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, fractionalBooleanPhase_norm]
  norm_num

/-- A Boolean-coordinate witness supported at `a`, with amplitude equal to the square root of
`w`. -/
private def phaseWitnessLeft (w : ℝ) (a k : Bool) : ℂ :=
  if k = a then (Real.sqrt w : ℂ) else 0

/-- The fractional phase defect divided by the square root of `w`, viewed as a
Boolean-coordinate witness. -/
private def phaseWitnessRight (lam w : ℝ) (b k : Bool) : ℂ :=
  fractionalPhaseDefect lam k b / (Real.sqrt w : ℂ)

/-- For positive `w`, the pairing of the left and right phase witnesses equals the fractional
phase defect. -/
private theorem phaseWitness_pair (lam w : ℝ) (hw : 0 < w) (a b : Bool) :
    (∑ k : Bool, star (phaseWitnessLeft w a k) * phaseWitnessRight lam w b k) =
      fractionalPhaseDefect lam a b := by
  have hs : (Real.sqrt w : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hw).ne'
  cases a <;> simp [phaseWitnessLeft, phaseWitnessRight] <;> field_simp

/-- For nonnegative `w`, the sum of squared norms of the left phase witness is `w`. -/
private theorem phaseWitness_left_mass (w : ℝ) (hw : 0 ≤ w) (a : Bool) :
    (∑ k : Bool, Complex.normSq (phaseWitnessLeft w a k)) = w := by
  cases a <;> simp [phaseWitnessLeft, Complex.normSq_ofReal, Real.mul_self_sqrt hw]

/-- If `w` is positive and bounds `Real.pi * |lam|`, the squared mass of the right phase witness
is at most `w`. -/
private theorem phaseWitness_right_mass (lam w : ℝ) (hw : 0 < w)
    (hc : Real.pi * |lam| ≤ w) (b : Bool) :
    (∑ k : Bool, Complex.normSq (phaseWitnessRight lam w b k)) ≤ w := by
  have hbound (a b : Bool) :
      Complex.normSq (fractionalPhaseDefect lam a b / (Real.sqrt w : ℂ)) ≤ w := by
    rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hw.le,
      div_le_iff₀ hw, Complex.normSq_eq_norm_sq]
    have h := (fractionalBooleanPhase_chord_bound lam a b).trans hc
    change ‖fractionalPhaseDefect lam a b‖ ≤ w at h
    nlinarith [norm_nonneg (fractionalPhaseDefect lam a b)]
  cases b
  · simpa [phaseWitnessRight] using! hbound true false
  · simpa [phaseWitnessRight] using! hbound false true

/-- The diagonal fractional phase oracle is unitary. -/
theorem fractionalPhaseOracle_unitary {W : Type} [Fintype W] [DecidableEq W]
    {n : ℕ} (input : Fin n → Bool) (lam : ℝ) :
    fractionalPhaseOracle (W := W) input lam ∈
      Matrix.unitaryGroup ((Fin (n + 1) × Fin 2) × W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal _ * (Matrix.diagonal _)ᴴ = _
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h (i : (Fin (n + 1) × Fin 2) × W) :
      fractionalQueryPhase input lam i.1.1 * star (fractionalQueryPhase input lam i.1.1) = 1 := by
    rw [mul_comm, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, fractionalQueryPhase_norm]
    norm_num
  simp only [Pi.star_apply, h, Matrix.diagonal_one]

/-- At fractional parameter one, the padded phase equals the Boolean Gram-query sign. -/
theorem fractionalQueryPhase_one {n : ℕ} (input : Fin n → Bool) (i : Fin (n + 1)) :
    fractionalQueryPhase input 1 i = gramQuerySign input i := by
  unfold fractionalQueryPhase gramQuerySign
  split
  · split <;> simp_all [fractionalBooleanPhase, mul_comm Complex.I,
      Complex.exp_pi_mul_I]
  · rfl

/-- The fractional bit frame preserves inner products. -/
theorem fractionalBitFrame_inner {W : Type} [Fintype W] {n : ℕ}
    (ψ φ : QState ((Fin (n + 1) × Fin 2) × W)) :
    Qatlib.Foundations.PureStateMath.Inner (fractionalBitFrame ψ) (fractionalBitFrame φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  have hm : (∑ b : Bool, star (Minus b) * Minus b) = (1 : ℂ) := by
    exact (normalized_iff_inner_self _).mp normalized_minus
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, fractionalBitFrame,
    Fintype.sum_prod_type, star_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  calc
    _ = (star (ψ ((i, a), w)) * φ ((i, a), w)) * ∑ b : Bool, star (Minus b) * Minus b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [hm, mul_one]

/-- The bit oracle on the padded input intertwines the fractional bit frame with the fractional
phase oracle at parameter one. -/
theorem fractionalBitFrame_single_query {W : Type} [Fintype W] [DecidableEq W]
    {n : ℕ} (input : Fin n → Bool)
    (ψ : QState ((Fin (n + 1) × Fin 2) × W)) :
    workspaceBitOracle (W := Fin 2 × W) (fractionalPaddedInput input) *ᵥ
      fractionalBitFrame ψ =
      fractionalBitFrame (fractionalPhaseOracle input 1 *ᵥ ψ) := by
  funext p
  rcases p with ⟨⟨i, b⟩, ⟨a, w⟩⟩
  change ApplyGate (workspaceBitOracle (W := Fin 2 × W) (fractionalPaddedInput input))
    (fractionalBitFrame ψ) ((i, b), (a, w)) = _
  rw [applyGate_workspaceBitOracle_mk]
  simp only [fractionalBitFrame,
    fractionalPhaseOracle_apply, fractionalQueryPhase_one]
  unfold fractionalPaddedInput gramQuerySign
  split
  · split <;> cases b <;> simp_all [Minus, Hadamard]
  · cases b <;> simp_all

/-- Applying a fractional phase oracle preserves normalization of a state. -/
theorem fractionalPhaseOracle_normalized {W : Type} [Fintype W] [DecidableEq W]
    {n : ℕ} (input : Fin n → Bool) (lam : ℝ)
    {ψ : QState ((Fin (n + 1) × Fin 2) × W)} (hψ : Normalized ψ) :
    Normalized (fractionalPhaseOracle input lam *ᵥ ψ) := by
  simpa only [Normalized, fractionalPhaseOracle_apply, norm_mul,
    fractionalQueryPhase_norm, one_mul] using! hψ

/-- The change in the Gram matrix under a fractional oracle is the sum of active-index slice
pairings weighted by their phase defects. -/
private theorem fractionalPhaseOracle_gram_difference {X W : Type}
    [Fintype W] [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (lam : ℝ)
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (x y : X) :
    (gramStateMatrix ρ - gramStateMatrix
      (fun x => fractionalPhaseOracle (input x) lam *ᵥ ρ x)) x y =
      ∑ j : Fin n, fractionalPhaseDefect lam (input x j) (input y j) *
        ∑ bw : Fin 2 × W, star (ρ x ((j.castSucc, bw.1), bw.2)) *
          ρ y ((j.castSucc, bw.1), bw.2) := by
  simp only [Matrix.sub_apply, gramStateMatrix, inner_apply,
    fractionalPhaseOracle_apply, map_mul, ← Finset.sum_sub_distrib,
    Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  simp only [fractionalQueryPhase_idle, map_one, one_mul, sub_self, Finset.sum_const_zero,
    add_zero, fractionalQueryPhase_active]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.mul_sum, fractionalPhaseDefect, RCLike.star_def]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The total squared amplitude mass on active query indices is at most one for a normalized
state. -/
private theorem fractionalActive_mass {X W : Type} [Fintype W] {n : ℕ}
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (x : X)
    (hρ : Normalized (ρ x)) :
    (∑ j : Fin n, ∑ bw : Fin 2 × W,
      Complex.normSq (ρ x ((j.castSucc, bw.1), bw.2))) ≤ 1 := by
  have hm : (∑ j : Fin (n + 1), ∑ b : Fin 2, ∑ w : W,
      Complex.normSq (ρ x ((j, b), w))) = 1 := by
    simpa only [Normalized, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq] using! hρ
  rw [Fin.sum_univ_castSucc] at hm
  simp only [Fintype.sum_prod_type]
  have h := Finset.sum_nonneg (fun b (_ : b ∈ Finset.univ) =>
    Finset.sum_nonneg (fun w (_ : w ∈ Finset.univ) =>
      Complex.normSq_nonneg (ρ x ((Fin.last n, b), w))))
  linarith

/-- Any positive bound on `Real.pi * |lam|` gives a filtered Gram certificate for the change
caused by a fractional oracle on normalized states. -/
private theorem fractionalPhaseOracle_cert_pos {X W : Type}
    [Fintype W] [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (lam w : ℝ) (hw : 0 < w)
    (hc : Real.pi * |lam| ≤ w)
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (hρ : ∀ x, Normalized (ρ x)) :
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix
      (fun x => fractionalPhaseOracle (input x) lam *ᵥ ρ x)) (gramFilterDelta input) w := by
  classical
  let a (j : Fin n) (x : X) (bw : Fin 2 × W) := ρ x ((j.castSucc, bw.1), bw.2)
  let u (j : Fin n) (x : X) (p : Bool × (Fin 2 × W)) :=
    phaseWitnessLeft w (input x j) p.1 * a j x p.2
  let v (j : Fin n) (x : X) (p : Bool × (Fin 2 × W)) :=
    phaseWitnessRight lam w (input x j) p.1 * a j x p.2
  have hmass (x : X) : (∑ j, ∑ bw, Complex.normSq (a j x bw)) ≤ 1 :=
    fractionalActive_mass ρ x (hρ x)
  refine ⟨Bool × (Fin 2 × W), inferInstance, u, v, ?_, ?_, ?_⟩
  · intro x
    change (∑ j, ∑ p : Bool × (Fin 2 × W), Complex.normSq
      (phaseWitnessLeft w (input x j) p.1 * a j x p.2)) ≤ w
    simp only [Fintype.sum_prod_type, Complex.normSq_mul]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, phaseWitness_left_mass w hw.le]
    simpa only [← Finset.mul_sum, mul_one, Fintype.sum_prod_type] using!
      mul_le_mul_of_nonneg_left (hmass x) hw.le
  · intro y
    change (∑ j, ∑ p : Bool × (Fin 2 × W), Complex.normSq
      (phaseWitnessRight lam w (input y j) p.1 * a j y p.2)) ≤ w
    simp only [Fintype.sum_prod_type, Complex.normSq_mul]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    calc
      _ ≤ ∑ j, w * ∑ b : Fin 2, ∑ z : W, Complex.normSq (a j y (b, z)) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right (phaseWitness_right_mass lam w hw hc (input y j))
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
      _ ≤ w := by
        simpa only [← Finset.mul_sum, mul_one, Fintype.sum_prod_type] using!
          mul_le_mul_of_nonneg_left (hmass y) hw.le
  · intro x y
    rw [fractionalPhaseOracle_gram_difference]
    apply Finset.sum_congr rfl
    intro j _
    have he : (star (u j x) ⬝ᵥ v j y) =
        fractionalPhaseDefect lam (input x j) (input y j) *
          ∑ bw, star (a j x bw) * a j y bw := by
      simp only [u, v, dotProduct, Pi.star_apply, star_mul, Fintype.sum_prod_type]
      have ht : (∑ k : Bool, ∑ b : Fin 2, ∑ z : W,
          star (a j x (b, z)) * star (phaseWitnessLeft w (input x j) k) *
            (phaseWitnessRight lam w (input y j) k * a j y (b, z))) =
          (∑ k : Bool, star (phaseWitnessLeft w (input x j) k) *
            phaseWitnessRight lam w (input y j) k) *
              ∑ b : Fin 2, ∑ z : W, star (a j x (b, z)) * a j y (b, z) := by
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro z _
        ring
      rw [ht, phaseWitness_pair lam w hw]
    rw [he]
    by_cases h : input x j = input y j
    · simp [gramFilterDelta, h]
    · simp only [gramFilterDelta, h, if_false, one_mul, a]

/-- The fractional phase oracle at parameter zero is the identity matrix. -/
@[simp] theorem fractionalPhaseOracle_zero {W : Type} [DecidableEq W]
    {n : ℕ} (input : Fin n → Bool) : fractionalPhaseOracle (W := W) input 0 = 1 := by
  classical
  have he : ∀ b : Bool, fractionalBooleanPhase 0 b = 1 := by
    intro b
    cases b <;> simp [fractionalBooleanPhase]
  have hi : ∀ i, fractionalQueryPhase input 0 i = 1 := by
    intro i
    unfold fractionalQueryPhase
    split <;> simp only [he]
  simp only [fractionalPhaseOracle, hi, Matrix.diagonal_one]

/-- The Gram-matrix change caused by a fractional oracle on normalized states has a filtered
certificate of cost `Real.pi * |lam|`. -/
theorem fractionalPhaseOracle_filteredCert {X W : Type}
    [Fintype W] [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (lam : ℝ)
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (hρ : ∀ x, Normalized (ρ x)) :
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix
      (fun x => fractionalPhaseOracle (input x) lam *ᵥ ρ x))
      (gramFilterDelta input) (Real.pi * |lam|) := by
  by_cases hz : lam = 0
  · subst lam
    simpa only [fractionalPhaseOracle_zero, Matrix.one_mulVec, sub_self,
      abs_zero, mul_zero] using! gramFilteredCert_zero (gramFilterDelta input) le_rfl
  · apply fractionalPhaseOracle_cert_pos input lam (Real.pi * |lam|) _ le_rfl ρ hρ
    exact mul_pos Real.pi_pos (abs_pos.mpr hz)

/-- For nonnegative `lam`, the fractional-oracle Gram change has a filtered certificate of cost
`lam * Real.pi * Real.sqrt 2`, in the state-conversion framework of [LeeEtAl2011]. -/
theorem stageB_state_conversion_clause97 {X W : Type}
    [Fintype W] [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (lam : ℝ) (hlam : 0 ≤ lam)
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (hρ : ∀ x, Normalized (ρ x)) :
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix
      (fun x => fractionalPhaseOracle (input x) lam *ᵥ ρ x))
      (gramFilterDelta input) (lam * Real.pi * Real.sqrt 2) := by
  apply gramFilteredCert_mono (fractionalPhaseOracle_filteredCert input lam ρ hρ)
  rw [abs_of_nonneg hlam]
  have hs : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  nlinarith [mul_nonneg Real.pi_pos.le hlam]

/-- Pairing a joint vector with a tensor-product target equals pairing its record projection
with the record vector. -/
theorem conversionRecordProjection_inner {R H : Type} [Fintype R] [Fintype H]
    (v : QState (R × H)) (σ : QState H) (ξ : QState R) :
    Qatlib.Foundations.PureStateMath.Inner v (TensorState ξ σ) = Qatlib.Foundations.PureStateMath.Inner (conversionRecordProjection v σ) ξ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, RCLike.star_def, TensorState,
    conversionRecordProjection, Fintype.sum_prod_type,
    map_sum, map_mul, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- A normalized record vector achieving overlap at least `t` with a fixed system target exists
exactly when the record projection has Euclidean norm at least `t`. -/
theorem conversionRecord_noncoherent_iff {R H : Type}
    [Fintype R] [DecidableEq R] [Fintype H] (r0 : R)
    (v : QState (R × H)) (σ : QState H) (t : ℝ) :
    (∃ ξ : QState R, Normalized ξ ∧ t ≤ ‖Qatlib.Foundations.PureStateMath.Inner v (TensorState ξ σ)‖) ↔
      t ≤ ‖toEuclidean_fromVec (conversionRecordProjection v σ)‖ := by
  let a := conversionRecordProjection v σ
  let d := ‖toEuclidean_fromVec a‖
  constructor
  · rintro ⟨ξ, hξ, ht⟩
    rw [conversionRecordProjection_inner] at ht
    apply ht.trans
    rw [← inner_euclidean_fromVec]
    have hn := (normalized_iff_norm_toEuclidean_fromVec ξ).mp hξ
    simpa only [hn, mul_one] using! norm_inner_le_norm (toEuclidean_fromVec a)
      (toEuclidean_fromVec ξ)
  · intro ht
    by_cases hd : d = 0
    · change t ≤ d at ht
      rw [hd] at ht
      exact ⟨Qatlib.Foundations.PureStateMath.Ket r0, normalized_ket r0,
          ht.trans (norm_nonneg _)⟩
    have hdpos : 0 < d := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    let ξ : QState R := fun r => a r / (d : ℂ)
    have hn : Normalized ξ := by
      change (∑ r, ‖a r / (d : ℂ)‖ ^ 2) = 1
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos,
        div_pow, ← Finset.sum_div]
      rw [← norm_toEuclidean_fromVec_sq]
      exact div_self (pow_ne_zero 2 hd)
    refine ⟨ξ, hn, ?_⟩
    rw [conversionRecordProjection_inner]
    have he : Qatlib.Foundations.PureStateMath.Inner a ξ = (d : ℂ) := by
      change (∑ r, star (a r) * (a r / (d : ℂ))) = _
      simp only [← mul_div_assoc, ← Finset.sum_div]
      have hi : (∑ r, star (a r) * a r) = ((d ^ 2 : ℝ) : ℂ) := by
        change Qatlib.Foundations.PureStateMath.Inner a a = _
        rw [inner_self, ← Complex.ofReal_sum, ← norm_toEuclidean_fromVec_sq]
      rw [hi]
      have hc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
      push_cast
      field_simp
    change t ≤ ‖Qatlib.Foundations.PureStateMath.Inner a ξ‖
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
    exact ht

/-- The quadratic form of the record marginal at a target vector equals the sum of squared norms
of its record-projection coordinates. -/
theorem conversionRecordMarginal_fidelity {R H : Type} [Fintype R] [Fintype H]
    (v : QState (R × H)) (σ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner σ (conversionRecordMarginal v *ᵥ σ) =
      ((∑ r, Complex.normSq (conversionRecordProjection v σ r) : ℝ) : ℂ) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, conversionRecordMarginal, Matrix.mulVec,
    conversionRecordProjection, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    RCLike.star_def, map_sum, map_mul, Complex.conj_conj]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Embedding a word whose known matrices are unitary yields a legal continuous conversion word. -/
theorem continuousConversionWord_legal {H : Type} [Fintype H] [DecidableEq H]
    (C : List (Matrix H H ℂ ⊕ Bool))
    (hC : ∀ s ∈ C, match s with
      | .inl U => U ∈ Matrix.unitaryGroup H ℂ | .inr _ => True) :
    continuousConversionLegal (continuousConversionWord C) := by
  intro s hs
  change s ∈ C.map _ at hs
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hs
  cases v with
  | inl U => exact hC (.inl U) hv
  | inr adj =>
    exact ⟨zero_le_one, fun _ _ => continuous_const.intervalIntegrable 0 1,
      fun _ _ => Matrix.isHermitian_zero⟩

/-- The total duration of an embedded discrete word equals its number of query symbols. -/
theorem continuousConversionWord_time {H : Type} (C : List (Matrix H H ℂ ⊕ Bool)) :
    continuousConversionTime (continuousConversionWord C) =
      (C.countP (fun s => match s with | .inl _ => false | .inr _ => true) : ℝ) := by
  induction C with
  | nil => simp [continuousConversionTime, continuousConversionWord]
  | cons s C ih =>
    cases s <;> simp_all [continuousConversionTime, continuousConversionWord,
      List.map_map, Function.comp_def, add_comm]

/-- If the positive and negative constant evolutions realize `O` and `Oᴴ`, the embedded word
evaluates to the corresponding reverse-ordered discrete matrix product. -/
theorem continuousConversionWord_matrix {H : Type} [Fintype H] [DecidableEq H]
    (L O : Matrix H H ℂ) (C : List (Matrix H H ℂ ⊕ Bool))
    (hf : continuousConversionEndpoint (fun _ => L) 1 = O)
    (hi : continuousConversionEndpoint (fun _ => -L) 1 = Oᴴ) :
    continuousConversionMatrix L (continuousConversionWord C) =
      (C.map (fun s => match s with | .inl U => U | .inr adj => if adj then Oᴴ else O)).reverse.prod := by
  unfold continuousConversionMatrix continuousConversionWord
  rw [List.map_map]
  congr 2
  apply List.map_congr_left
  intro s _
  cases s with
  | inl U => rfl
  | inr adj => cases adj <;> simp [hf, hi]

/-- Applying a matrix to every system slice conjugates the record marginal by that matrix. -/
theorem conversionRecordMarginal_action {R H : Type} [Fintype R] [Fintype H]
    (M : Matrix H H ℂ) (v : QState (R × H)) :
    conversionRecordMarginal (fun p : R × H => (M *ᵥ (fun h => v (p.1,h))) p.2) =
      M * conversionRecordMarginal v * Mᴴ := by
  ext h k
  simp only [conversionRecordMarginal, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Recording the Kraus index yields a system marginal equal to the sum of the individual
conjugated marginals. -/
theorem conversionRecordKraus_marginal {K R H : Type}
    [Fintype K] [Fintype R] [Fintype H]
    (A : K → Matrix H H ℂ) (v : QState (R × H)) :
    conversionRecordMarginal (conversionRecordKraus A v) =
      ∑ k, A k * conversionRecordMarginal v * (A k)ᴴ := by
  ext h j
  simp only [conversionRecordMarginal, conversionRecordKraus, Fintype.sum_prod_type,
    Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact congrFun (congrFun (conversionRecordMarginal_action (A k) v) h) j

section ContinuousIntegral
open scoped Matrix.Norms.L2Operator

local instance continuousMatrixENormed (X : Type) [Fintype X] [DecidableEq X] :
    ENormedAddCommMonoid (Matrix X X ℂ) :=
  @NormedAddCommGroup.toENormedAddCommMonoid _ Matrix.instL2OpNormedAddCommGroup

set_option backward.isDefEq.respectTransparency false in

/-- An interval-integrable matrix family with filtered certificates of uniform nonnegative cost
`C` has integrated filtered gamma-two value at most `C * T` for nonnegative `T`. -/
theorem continuousConversion_filtered_integral {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (Z : Fin n → Matrix X X ℂ) (D : ℝ → Matrix X X ℂ)
    (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hD : IntervalIntegrable D MeasureTheory.volume 0 T)
    (hcert : ∀ t ∈ Set.Icc 0 T, gramFilteredCert (D t) Z C) :
    filteredGamma2 (∫ t in (0 : ℝ)..T, D t) Z ≤ ENNReal.ofReal (C*T) := by
  rw [(filteredGamma2_strong_duality X n _ Z).1]
  apply iSup_le
  intro M
  let l : Matrix X X ℂ →ₗ[ℂ] Matrix X X ℂ :=
    { toFun := fun A => A ⊙ M.1
      map_add' := by intro A B; ext x y; simp [Matrix.hadamard_apply, add_mul]
      map_smul' := by intro c A; ext x y; simp [Matrix.hadamard_apply, mul_assoc] }
  let L : Matrix X X ℂ →L[ℂ] Matrix X X ℂ := l.toContinuousLinearMap
  have he : (∫ t in (0 : ℝ)..T, D t) ⊙ M.1 = ∫ t in (0 : ℝ)..T, D t ⊙ M.1 :=
    (L.intervalIntegral_comp_comm hD).symm
  apply ENNReal.ofReal_le_ofReal
  rw [he]
  have hb (t : ℝ) (ht : t ∈ Set.Icc 0 T) : ‖D t ⊙ M.1‖ ≤ C := by
    have hval := (filteredGamma2_budget_boundary X n (D t) Z C hC).mpr (hcert t ht)
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp
      ((filteredGamma2_dual_ge (D t) Z M.1 M.2).trans hval)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hT
    (Filter.Eventually.of_forall fun t (ht : t ∈ Set.Ioc 0 T) => hb t ⟨ht.1.le,ht.2⟩)
    (intervalIntegrable_const (c := C))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm T C] using! hi

end ContinuousIntegral

/-- The inner product of the Boolean-register tangent witnesses equals `i` times the difference
of the mixed state-tangent pairings. -/
theorem continuousConversionTangent_pair {X H : Type} [Fintype H] {n : ℕ}
    (ψ χ : X → Fin n → QState H) (j : Fin n) (x y : X) :
    Qatlib.Foundations.PureStateMath.Inner (continuousConversionTangentLeft ψ χ j x) (continuousConversionTangentRight ψ χ j y) =
      Complex.I * (Qatlib.Foundations.PureStateMath.Inner (χ x j) (ψ y j) - Qatlib.Foundations.PureStateMath.Inner (ψ x j) (χ y j)) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool,
    continuousConversionTangentLeft, continuousConversionTangentRight,
    Bool.false_eq_true, ite_false, ite_true, Pi.star_apply]
  simp only [← mul_assoc, mul_comm _ Complex.I, mul_comm _ (-Complex.I)]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- The squared mass of the left tangent witness is the sum of the squared masses of its state
and tangent components. -/
theorem continuousConversionTangent_left_mass {X H : Type} [Fintype H] {n : ℕ}
    (ψ χ : X → Fin n → QState H) (j : Fin n) (x : X) :
    (∑ p, Complex.normSq (continuousConversionTangentLeft ψ χ j x p)) =
      (∑ h, Complex.normSq (ψ x j h)) + ∑ h, Complex.normSq (χ x j h) := by
  simp [Fintype.sum_prod_type, continuousConversionTangentLeft, add_comm]

/-- The squared mass of the right tangent witness is the sum of the squared masses of its state
and tangent components. -/
theorem continuousConversionTangent_right_mass {X H : Type} [Fintype H] {n : ℕ}
    (ψ χ : X → Fin n → QState H) (j : Fin n) (x : X) :
    (∑ p, Complex.normSq (continuousConversionTangentRight ψ χ j x p)) =
      (∑ h, Complex.normSq (ψ x j h)) + ∑ h, Complex.normSq (χ x j h) := by
  simp [Fintype.sum_prod_type, continuousConversionTangentRight,
    Complex.normSq_mul]

/-- Under the stated mass and equal-input cancellation conditions, the continuous tangent matrix
has a filtered Gram certificate of cost `P + Q`. -/
theorem continuousConversionTangent_cert {X H A : Type} [Fintype H] [DecidableEq A]
    {n : ℕ} (input : X → Fin n → A) (ψ χ : X → Fin n → QState H) (P Q : ℝ)
    (hψ : ∀ x, (∑ j, ∑ h, Complex.normSq (ψ x j h)) ≤ P)
    (hχ : ∀ x, (∑ j, ∑ h, Complex.normSq (χ x j h)) ≤ Q)
    (hlocal : ∀ x y j, input x j = input y j →
      Qatlib.Foundations.PureStateMath.Inner (χ x j) (ψ y j) = Qatlib.Foundations.PureStateMath.Inner (ψ x j) (χ y j)) :
    gramFilteredCert (continuousConversionTangent ψ χ)
      (fun j x y => if input x j = input y j then 0 else 1) (P + Q) := by
  refine ⟨Bool × H, inferInstance, continuousConversionTangentLeft ψ χ,
    continuousConversionTangentRight ψ χ, ?_, ?_, ?_⟩
  · intro x
    simp_rw [continuousConversionTangent_left_mass]
    rw [Finset.sum_add_distrib]
    exact add_le_add (hψ x) (hχ x)
  · intro x
    simp_rw [continuousConversionTangent_right_mass]
    rw [Finset.sum_add_distrib]
    exact add_le_add (hψ x) (hχ x)
  · intro x y
    change (∑ j, _) = ∑ j, _
    apply Finset.sum_congr rfl
    intro j _
    rw [← continuousConversionTangent_pair]
    change _ = (if input x j = input y j then 0 else 1) * _
    by_cases h : input x j = input y j
    · rw [if_pos h, zero_mul, continuousConversionTangent_pair, hlocal x y j h, sub_self, mul_zero]
    · rw [if_neg h, one_mul]
      rfl

section ContinuousAnalytic
open MeasureTheory Set Filter
open scoped Topology

/-- A constant function is absolutely continuous on every interval. -/
theorem continuousConversion_ac_const {F : Type} [NormedAddCommGroup F] (c : F) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
  simpa [AbsolutelyContinuousOnInterval] using!
    (tendsto_const_nhds : Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0 : ℝ)) _ (𝓝 0))

/-- For an absolutely continuous real function with the specified almost-everywhere derivative,
the interval integral of that derivative equals the endpoint difference. -/
theorem continuousConversion_real_ftc {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (g t) t) :
    (∫ t in a..b, g t) = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae'
  · filter_upwards [hd] with t ht hmem
    exact (ht ⟨(min_le_left _ _).trans hmem.1.le, hmem.2.trans (le_max_right _ _)⟩).deriv.symm
  · filter_upwards [hd] with t ht hmem
    exact (ht ⟨(min_le_right _ _).trans hmem.1.le, hmem.2.trans (le_max_left _ _)⟩).deriv.symm

/-- For a complex function with absolutely continuous real and imaginary parts and an integrable
almost-everywhere derivative, integrating the derivative gives the endpoint difference. -/
theorem continuousConversion_complex_ftc {f g : ℝ → ℂ} {a b : ℝ}
    (hfRe : AbsolutelyContinuousOnInterval (fun t => (f t).re) a b)
    (hfIm : AbsolutelyContinuousOnInterval (fun t => (f t).im) a b)
    (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (g t) t) :
    (∫ t in a..b, g t) = f b - f a := by
  apply Complex.ext
  · have he : (∫ t in a..b, g t).re = ∫ t in a..b, (g t).re :=
      (Complex.reCLM.intervalIntegral_comp_comm hg).symm
    rw [he, Complex.sub_re]
    apply continuousConversion_real_ftc hfRe
    filter_upwards [hd] with t ht hmem
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ht hmem)
  · have he : (∫ t in a..b, g t).im = ∫ t in a..b, (g t).im :=
      (Complex.imCLM.intervalIntegral_comp_comm hg).symm
    rw [he, Complex.sub_im]
    apply continuousConversion_real_ftc hfIm
    filter_upwards [hd] with t ht hmem
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (ht hmem)

/-- The real part of a constant plus an indefinite interval integral is absolutely continuous
when the integrand is interval integrable. -/
theorem continuousConversion_ac_re_integral {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun t => (c + ∫ s in a..t, g s).re) a b := by
  have hgre : IntervalIntegrable (fun s => (g s).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have hI := hgre.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hAC := (continuousConversion_ac_const c.re a b).add hI

  apply (absolutelyContinuousOnInterval_iff _ _ _).mpr
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := (absolutelyContinuousOnInterval_iff _ _ _).mp hAC ε hε
  refine ⟨δ,hδ,?_⟩
  intro E hE hlen
  convert! hbound E hE hlen using 1
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨h1,h2⟩ := hE.1 i hi
  have hsub (t : ℝ) (ht : t ∈ uIcc a b) : IntervalIntegrable g volume a t :=
    hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc (by simp) ht))
  simp only [Pi.add_apply, Complex.add_re]
  have he1 : (∫ s in a..(E.2 i).1, g s).re = ∫ s in a..(E.2 i).1, (g s).re :=
    (Complex.reCLM.intervalIntegral_comp_comm (hsub _ h1)).symm
  have he2 : (∫ s in a..(E.2 i).2, g s).re = ∫ s in a..(E.2 i).2, (g s).re :=
    (Complex.reCLM.intervalIntegral_comp_comm (hsub _ h2)).symm
  rw [he1,he2]

/-- The imaginary part of a constant plus an indefinite interval integral is absolutely
continuous when the integrand is interval integrable. -/
theorem continuousConversion_ac_im_integral {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun t => (c + ∫ s in a..t, g s).im) a b := by
  have hgre : IntervalIntegrable (fun s => (g s).im) volume a b :=
    ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩
  have hI := hgre.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hAC := (continuousConversion_ac_const c.im a b).add hI

  apply (absolutelyContinuousOnInterval_iff _ _ _).mpr
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := (absolutelyContinuousOnInterval_iff _ _ _).mp hAC ε hε
  refine ⟨δ,hδ,?_⟩
  intro E hE hlen
  convert! hbound E hE hlen using 1
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨h1,h2⟩ := hE.1 i hi
  have hsub (t : ℝ) (ht : t ∈ uIcc a b) : IntervalIntegrable g volume a t :=
    hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc (by simp) ht))
  simp only [Pi.add_apply, Complex.add_im]
  have he1 : (∫ s in a..(E.2 i).1, g s).im = ∫ s in a..(E.2 i).1, (g s).im :=
    (Complex.imCLM.intervalIntegral_comp_comm (hsub _ h1)).symm
  have he2 : (∫ s in a..(E.2 i).2, g s).im = ∫ s in a..(E.2 i).2, (g s).im :=
    (Complex.imCLM.intervalIntegral_comp_comm (hsub _ h2)).symm
  rw [he1,he2]

/-- Absolute continuity on an interval transfers to a function that agrees with the original
function on the unoriented closed interval. -/
theorem continuousConversion_ac_congr {F : Type} [NormedAddCommGroup F]
    {f g : ℝ → F} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (heq : EqOn g f (uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  apply (absolutelyContinuousOnInterval_iff _ _ _).mpr
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := (absolutelyContinuousOnInterval_iff _ _ _).mp hf ε hε
  refine ⟨δ,hδ,?_⟩
  intro E hE hlen
  convert! hbound E hE hlen using 1
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨h1,h2⟩ := hE.1 i hi
  rw [heq h1,heq h2]

/-- Derivatives of the real and imaginary parts combine into the corresponding complex
derivative. -/
theorem continuousConversion_complex_derivative {f : ℝ → ℂ} {g : ℂ} {t : ℝ}
    (hr : HasDerivAt (fun t => (f t).re) g.re t)
    (hi : HasDerivAt (fun t => (f t).im) g.im t) : HasDerivAt f g t := by
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hr).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hi).mul_const Complex.I)
  have he : ((fun u => (Complex.ofRealCLM ((f u).re))) +
      (fun u => (Complex.ofRealCLM ((f u).im)) * Complex.I)) = f := by
    funext u
    exact Complex.re_add_im (f u)
  simp only [Function.comp_def] at hd
  rw [he] at hd
  simpa only [Complex.ofRealCLM_apply, Complex.re_add_im] using! hd

/-- An indefinite integral of an interval-integrable complex function has that function as its
derivative almost everywhere on the unoriented interval. -/
theorem continuousConversion_primitive_ae_deriv {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (c : ℂ) :
    ∀ᵐ t, t ∈ uIcc a b → HasDerivAt (fun t => c + ∫ s in a..t, g s) (g t) t := by
  have hgre : IntervalIntegrable (fun t => (g t).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hg.1,Complex.reCLM.integrable_comp hg.2⟩
  have hgim : IntervalIntegrable (fun t => (g t).im) volume a b :=
    ⟨Complex.imCLM.integrable_comp hg.1,Complex.imCLM.integrable_comp hg.2⟩
  filter_upwards [hgre.ae_hasDerivAt_integral,hgim.ae_hasDerivAt_integral,
    (show ∀ᵐ t : ℝ, t ≠ a from by simp [ae_iff]), (show ∀ᵐ t : ℝ, t ≠ b from by simp [ae_iff])]
    with t hr hi hta htb ht
  have hinner : t ∈ Ioo (min a b) (max a b) := by
    constructor <;> rcases le_total a b with hab | hba <;> simp_all [lt_iff_le_and_ne, ne_comm]
  have heqRe : (fun u => (c + ∫ s in a..u, g s).re) =ᶠ[𝓝 t]
      (fun u => c.re + ∫ s in a..u, (g s).re) := by
    filter_upwards [Ioo_mem_nhds hinner.1 hinner.2] with u hu
    have hui : u ∈ uIcc a b := ⟨hu.1.le,hu.2.le⟩
    have hint : IntervalIntegrable g volume a u :=
      hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc (by simp) hui))
    have he := Complex.reCLM.intervalIntegral_comp_comm hint
    change (c + ∫ s in a..u, g s).re = c.re + ∫ s in a..u, (g s).re
    rw [Complex.add_re]
    exact congrArg (fun r : ℝ => c.re + r) he.symm
  have heqIm : (fun u => (c + ∫ s in a..u, g s).im) =ᶠ[𝓝 t]
      (fun u => c.im + ∫ s in a..u, (g s).im) := by
    filter_upwards [Ioo_mem_nhds hinner.1 hinner.2] with u hu
    have hui : u ∈ uIcc a b := ⟨hu.1.le,hu.2.le⟩
    have hint : IntervalIntegrable g volume a u :=
      hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc (by simp) hui))
    have he := Complex.imCLM.intervalIntegral_comp_comm hint
    change (c + ∫ s in a..u, g s).im = c.im + ∫ s in a..u, (g s).im
    rw [Complex.add_im]
    exact congrArg (fun r : ℝ => c.im + r) he.symm
  exact continuousConversion_complex_derivative
    (((hr ht a (by simp)).const_add c.re).congr_of_eventuallyEq heqRe)
    (((hi ht a (by simp)).const_add c.im).congr_of_eventuallyEq heqIm)

/-- A Hermitian matrix can be moved between the two arguments of the finite-dimensional inner
product. -/
theorem continuousConversion_hermitian_pair {H : Type} [Fintype H] [DecidableEq H]
    (L : Matrix H H ℂ) (hL : L.IsHermitian) (ψ φ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (L *ᵥ ψ) φ = Qatlib.Foundations.PureStateMath.Inner ψ (L *ᵥ φ) := by
  simp only [Qatlib.Foundations.PureStateMath.inner_apply, Matrix.mulVec, dotProduct, map_sum,
      map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [starRingEnd_apply]
  rw [hL.apply i j]
  ring

/-- A finite sum of absolutely continuous real functions is absolutely continuous. -/
theorem continuousConversion_ac_sum {I : Type} [Fintype I] {f : I → ℝ → ℝ} {a b : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i, f i t) a b := by
  have hh : ∀ s : Finset I, AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) a b := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using! continuousConversion_ac_const (0 : ℝ) a b
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi, Pi.add_apply] using! (hf i).add ih
  exact hh Finset.univ

/-- The inner product of two vector-valued functions has absolutely continuous real and
imaginary parts when all component parts do. -/
theorem continuousConversion_inner_ac {H : Type} [Fintype H] {ψ φ : ℝ → QState H} {a b : ℝ}
    (hψ : ∀ i, AbsolutelyContinuousOnInterval (fun t => (ψ t i).re) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (ψ t i).im) a b)
    (hφ : ∀ i, AbsolutelyContinuousOnInterval (fun t => (φ t i).re) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (φ t i).im) a b) :
    AbsolutelyContinuousOnInterval (fun t => (Qatlib.Foundations.PureStateMath.Inner (ψ t) (φ t)).re) a b ∧
    AbsolutelyContinuousOnInterval (fun t => (Qatlib.Foundations.PureStateMath.Inner (ψ t) (φ t)).im) a b := by
  constructor
  · have hh := continuousConversion_ac_sum (fun i =>
      ((hψ i).1.mul (hφ i).1).add ((hψ i).2.mul (hφ i).2))
    simpa [Qatlib.Foundations.PureStateMath.inner_apply,Complex.mul_re,Complex.add_re] using!
        hh
  · have hh := continuousConversion_ac_sum (fun i =>
      ((hψ i).1.mul (hφ i).2).sub ((hψ i).2.mul (hφ i).1))
    simpa [Qatlib.Foundations.PureStateMath.inner_apply,Complex.mul_im,Complex.add_im,sub_eq_add_neg,Finset.sum_add_distrib] using! hh

/-- The derivative of an inner product of componentwise differentiable vectors is the sum of the
two differentiated pairings. -/
theorem continuousConversion_inner_deriv {H : Type} [Fintype H]
    {ψ φ : ℝ → QState H} {ψ' φ' : QState H} {t : ℝ}
    (hψ : ∀ i, HasDerivAt (fun t => ψ t i) (ψ' i) t)
    (hφ : ∀ i, HasDerivAt (fun t => φ t i) (φ' i) t) :
    HasDerivAt (fun t => Qatlib.Foundations.PureStateMath.Inner (ψ t) (φ t))
      (Qatlib.Foundations.PureStateMath.Inner ψ' (φ t) + Qatlib.Foundations.PureStateMath.Inner (ψ t) φ') t := by
  have hh := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => (hψ i).star.mul (hφ i))
  simpa only [Qatlib.Foundations.PureStateMath.inner_apply,starRingEnd_apply,Finset.sum_add_distrib] using! hh

/-- Scalar multiplication in the first argument of the inner product produces the conjugate
scalar. -/
theorem continuousConversion_inner_smul_left {H : Type} [Fintype H]
    (a : ℂ) (ψ φ : QState H) : Qatlib.Foundations.PureStateMath.Inner (a • ψ) φ = star a * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp [Qatlib.Foundations.PureStateMath.inner_apply,Pi.smul_apply,map_mul,mul_assoc,Finset.mul_sum]

/-- Scalar multiplication in the second argument of the inner product produces the scalar. -/
theorem continuousConversion_inner_smul_right {H : Type} [Fintype H]
    (a : ℂ) (ψ φ : QState H) : Qatlib.Foundations.PureStateMath.Inner ψ (a • φ) = a * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp [Qatlib.Foundations.PureStateMath.inner_apply,Pi.smul_apply,mul_left_comm,Finset.mul_sum]

/-- The inner product distributes over addition in its first argument. -/
theorem continuousConversion_inner_add_left {H : Type} [Fintype H]
    (ψ φ ξ : QState H) : Qatlib.Foundations.PureStateMath.Inner (ψ + φ) ξ = Qatlib.Foundations.PureStateMath.Inner ψ ξ + Qatlib.Foundations.PureStateMath.Inner φ ξ := by
  simp [Qatlib.Foundations.PureStateMath.inner_apply,Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]

/-- The inner product distributes over addition in its second argument. -/
theorem continuousConversion_inner_add_right {H : Type} [Fintype H]
    (ψ φ ξ : QState H) : Qatlib.Foundations.PureStateMath.Inner ψ (φ + ξ) = Qatlib.Foundations.PureStateMath.Inner ψ φ + Qatlib.Foundations.PureStateMath.Inner ψ ξ := by
  simp [Qatlib.Foundations.PureStateMath.inner_apply,Pi.add_apply,mul_add,Finset.sum_add_distrib]

/-- A common Hermitian driver cancels from the sum of the two evolution pairings, leaving only
the mixed terms involving `χ` and `ξ`. -/
theorem continuousConversion_driver_cancellation {H : Type} [Fintype H] [DecidableEq H]
    (K : Matrix H H ℂ) (hK : K.IsHermitian) (ψ φ χ ξ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner ((-Complex.I) • (K *ᵥ ψ + χ)) φ + Qatlib.Foundations.PureStateMath.Inner ψ ((-Complex.I) • (K *ᵥ φ + ξ)) =
      Complex.I * (Qatlib.Foundations.PureStateMath.Inner χ φ - Qatlib.Foundations.PureStateMath.Inner ψ ξ) := by
  rw [continuousConversion_inner_smul_left,continuousConversion_inner_smul_right,
    continuousConversion_inner_add_left,continuousConversion_inner_add_right,
    continuousConversion_hermitian_pair K hK]
  simp only [star_neg, RCLike.star_def,Complex.conj_I,neg_neg]
  ring

/-- The inner product of two continuous vector-valued functions is continuous on their common
domain. -/
theorem continuousConversion_inner_continuousOn {H : Type} [Fintype H]
    {ψ φ : ℝ → QState H} {S : Set ℝ} (hψ : ContinuousOn ψ S) (hφ : ContinuousOn φ S) :
    ContinuousOn (fun t => Qatlib.Foundations.PureStateMath.Inner (ψ t) (φ t)) S := by
  simp only [Qatlib.Foundations.PureStateMath.inner_apply,starRingEnd_apply]
  exact continuousOn_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp_continuousOn hψ).star.mul
      ((continuous_apply i).comp_continuousOn hφ))

/-- Matrix-vector multiplication of continuous matrix and vector functions is continuous on
their common domain. -/
theorem continuousConversion_mulVec_continuousOn {H : Type} [Fintype H]
    {A : ℝ → Matrix H H ℂ} {ψ : ℝ → QState H} {S : Set ℝ}
    (hA : ContinuousOn A S) (hψ : ContinuousOn ψ S) :
    ContinuousOn (fun t => A t *ᵥ ψ t) S := by
  rw [continuousOn_iff_continuous_restrict] at hA hψ ⊢
  exact hA.matrix_mulVec hψ

end ContinuousAnalytic

/-- Tracing out the record register after conjugation by a frame equals the sum of conjugations
by its record blocks. -/
theorem conversionTraceRecord_frame {R H S : Type} [Fintype R] [Fintype H] [Fintype S]
    (V : Matrix (R × H) S ℂ) (D : Matrix S S ℂ) :
    conversionTraceRecord (V*D*Vᴴ) =
      ∑ r, conversionRecordBlock V r * D * (conversionRecordBlock V r)ᴴ := by
  ext h k
  simp only [conversionTraceRecord,conversionRecordBlock,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sum_apply]

/-- Pulling a framed conjugation back through an isometry and tracing out the record register
gives the sum of conjugations by the original frame blocks. -/
theorem conversionTraceRecord_pullback {R H S W : Type} [Fintype R] [Fintype H]
    [Fintype S] [Fintype W] [DecidableEq R] [DecidableEq H]
    (F : Matrix W (R × H) ℂ) (hF : Fᴴ*F=1)
    (A : Matrix (R × H) S ℂ) (D : Matrix S S ℂ) :
    conversionTraceRecord (Fᴴ*((F*A)*D*(F*A)ᴴ)*F) =
      ∑ r, conversionRecordBlock A r * D * (conversionRecordBlock A r)ᴴ := by
  have hp : Fᴴ*((F*A)*D*(F*A)ᴴ)*F = A*D*Aᴴ := by
    simp only [Matrix.conjTranspose_mul]
    calc
      _ = (Fᴴ*F)*A*D*Aᴴ*(Fᴴ*F) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hF,Matrix.one_mul,Matrix.mul_one]
  rw [hp,conversionTraceRecord_frame]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
