/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Foundations.OperatorErrors.OperatorError
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Sparse Pauli shadow covariance

This module defines compatibility, overlap, and cancellation for Pauli words, together with
sparse Pauli observables and their estimators. Exact cross moments yield an energy variance
formula and a simultaneous sample-mean accuracy bound for observables evaluated on shared
classical-shadow records [HuangKuengPreskill2020].

## Main statements

* `tensor_pauli_actual_cross_moment`: exact cross moment of Pauli-word estimates.
* `sparse_pauli_exact_energy_variance_and_bound`: exact variance and a support-overlap bound.
* `sparse_pauli_many_energies_same_record_accuracy`: simultaneous accuracy from shared records.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowVariance
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 4000000

/-- Two Pauli words are compatible when their axes agree at every position where both factors
are nonidentity. -/
def pauliWordsCompatible {n : ℕ} (u v : Fin n → Option (Fin 3)) : Prop :=
  ∀ i, ∀ a b, u i = some a → v i = some b → a = b

/-- The number of positions where both Pauli words have nonidentity factors. -/
def pauliWordOverlap {n : ℕ} (u v : Fin n → Option (Fin 3)) : ℕ :=
  ∑ i, if (u i).isSome && (v i).isSome then 1 else 0

/-- The word obtained by retaining a lone nonidentity factor and replacing two nonidentity
factors by the identity at each position. -/
def pauliWordCancel {n : ℕ} (u v : Fin n → Option (Fin 3)) (i : Fin n) : Option (Fin 3) :=
  match u i, v i with
  | none, a => a
  | a, none => a
  | some _, some _ => none

/-- The rationally weighted real sum of Pauli-word estimates on a single record. -/
def sparsePauliValue {n m : ℕ} (w : Fin m → Fin n → Option (Fin 3)) (c : Fin m → ℚ)
    (o : Fin n → Fin 3 × Bool) : ℝ := ∑ j, (c j : ℝ) * tensorPauliValue (w j) o

/-- The operator given by a rationally weighted sum of tensor Pauli words. -/
noncomputable def sparsePauliObservable {n m : ℕ}
    (w : Fin m → Fin n → Option (Fin 3)) (c : Fin m → ℚ) : Operator (2 ^ n) :=
  ∑ j, (c j : ℂ) • tensorPauliWord n (w j)

/-- The cross-moment expression: zero for incompatible words and otherwise three to their
overlap times the real state expectation of their cancellation word. -/
noncomputable def sparsePauliMoment {n : ℕ} (ρ : Operator (2 ^ n))
    (u v : Fin n → Option (Fin 3)) : ℝ := by
  classical
  exact if pauliWordsCompatible u v then
    (3 : ℝ) ^ pauliWordOverlap u v *
      (Matrix.trace (tensorPauliWord n (pauliWordCancel u v) * ρ)).re else 0

/-- For compatible local factors, the measurement-effect sum weighted by the product of their
estimates equals the cancellation factor scaled by three when both factors are nonidentity. -/
private theorem local_cross_effect (u v : Option (Fin 3))
    (h : ∀ a b, u = some a → v = some b → a = b) :
    (∑ o : Fin 3 × Bool,
      ((tensorPauliLocalValue u o * tensorPauliLocalValue v o : ℝ) : ℂ) •
        ((1 / 3 : ℂ) • PauliProjector o.1 o.2)) =
    (3 : ℂ) ^ (if u.isSome && v.isSome then 1 else 0) •
      tensorPauliWordFactor (match u, v with
        | none, a => a | a, none => a | some _, some _ => none) := by
  cases u with
  | none =>
    cases v with
    | none =>
      simpa [tensorPauliLocalValue, tensorPauliWordFactor] using
        tensorPauliLocalSecondMomentEffect none
    | some b =>
      fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Fintype.sum_prod_type, Fin.sum_univ_three,
          tensorPauliLocalValue, tensorPauliWordFactor, PauliProjector,
          pauliMatrix_zero, pauliMatrix_one, pauliMatrix_two, pauliX, pauliY, pauliZ] <;>
        norm_num <;> ring
  | some a =>
    cases v with
    | none =>
      fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Fintype.sum_prod_type, Fin.sum_univ_three,
          tensorPauliLocalValue, tensorPauliWordFactor, PauliProjector,
          pauliMatrix_zero, pauliMatrix_one, pauliMatrix_two, pauliX, pauliY, pauliZ] <;>
        norm_num <;> ring
    | some b =>
      have hab := h a b rfl rfl
      subst b
      simpa [pow_two, tensorPauliWordFactor] using tensorPauliLocalSecondMomentEffect (some a)

/-- The cross moment of two tensor Pauli-word estimators equals `sparsePauliMoment`. See
[HuangKuengPreskill2020]. -/
theorem tensor_pauli_actual_cross_moment (n : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (u v : Fin n → Option (Fin 3)) :
    (tensorPauliLaw n ρ hρ).expect (fun o => tensorPauliValue u o * tensorPauliValue v o) =
      sparsePauliMoment ρ u v := by
  classical
  by_cases h : pauliWordsCompatible u v
  · have he : (∑ o : Fin n → Fin 3 × Bool,
        ((tensorPauliValue u o * tensorPauliValue v o : ℝ) : ℂ) •
          ((tensorPauliKraus n o)ᴴ * tensorPauliKraus n o)) =
        (3 : ℂ) ^ pauliWordOverlap u v • tensorPauliWord n (pauliWordCancel u v) := by
      simp_rw [tensorPauliKraus_effect]
      have ht : ∀ o : Fin n → Fin 3 × Bool,
          ((tensorPauliValue u o * tensorPauliValue v o : ℝ) : ℂ) •
            tensorPauliProduct n (fun i => (1 / 3 : ℂ) • PauliProjector (o i).1 (o i).2) =
          tensorPauliProduct n (fun i =>
            ((tensorPauliLocalValue (u i) (o i) * tensorPauliLocalValue (v i) (o i) : ℝ) : ℂ) •
              ((1 / 3 : ℂ) • PauliProjector (o i).1 (o i).2)) := by
        intro o
        rw [tensorPauliProduct_smul n
          (fun i => ((tensorPauliLocalValue (u i) (o i) * tensorPauliLocalValue (v i) (o i) : ℝ) : ℂ))
          (fun i => (1 / 3 : ℂ) • PauliProjector (o i).1 (o i).2)]
        congr 1
        simp only [tensorPauliValue, Complex.ofReal_mul, Complex.ofReal_prod,
          Finset.prod_mul_distrib]
      rw [Finset.sum_congr rfl (fun o _ => ht o)]
      rw [tensorPauliProduct_sum n (fun i o =>
        ((tensorPauliLocalValue (u i) o * tensorPauliLocalValue (v i) o : ℝ) : ℂ) •
          ((1 / 3 : ℂ) • PauliProjector o.1 o.2))]
      simp_rw [local_cross_effect _ _ (h _)]
      rw [tensorPauliProduct_smul, Finset.prod_pow_eq_pow_sum]
      congr 2
      funext i
      split <;> simp_all [pauliWordCancel]
    have ht : (Matrix.trace ((∑ o : Fin n → Fin 3 × Bool,
        ((tensorPauliValue u o * tensorPauliValue v o : ℝ) : ℂ) •
          ((tensorPauliKraus n o)ᴴ * tensorPauliKraus n o)) * ρ)).re =
        (tensorPauliLaw n ρ hρ).expect (fun o => tensorPauliValue u o * tensorPauliValue v o) := by
      rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
        ← tensorPauliLaw_complex_mass n ρ hρ o]
      norm_cast
      ring
    rw [← ht, he, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [show (3 : ℂ) ^ pauliWordOverlap u v =
      (((3 : ℝ) ^ pauliWordOverlap u v : ℝ) : ℂ) by norm_cast]
    simp only [sparsePauliMoment, if_pos h, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  · simp only [pauliWordsCompatible, not_forall] at h
    obtain ⟨i, a, b, hu, hv, hab⟩ := h
    have hz : ∀ o : Fin n → Fin 3 × Bool, tensorPauliValue u o * tensorPauliValue v o = 0 := by
      intro o
      rw [tensorPauliValue, tensorPauliValue, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hu, hv]
      by_cases ha : (o i).1 = a <;> by_cases hb : (o i).1 = b
      · exact False.elim (hab (ha.symm.trans hb))
      all_goals simp [tensorPauliLocalValue, ha, hb, hab, Ne.symm hab]
    have hn : ¬ pauliWordsCompatible u v := fun hh => hab (hh i a b hu hv)
    simp [FinDist.expect, hz, sparsePauliMoment, hn]

/-- Every tensor Pauli word is unitary. -/
theorem sparsePauliWord_unitary (n : ℕ) (w : Fin n → Option (Fin 3)) :
    tensorPauliWord n w ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [tensorPauliWord]
  apply Qatlib.Concepts.GateVocabulary.GateVocab.tensor_product_unitary
  intro i
  cases w i with
  | none => simp [tensorPauliWordFactor]
  | some a =>
    change pauliMatrix a ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [← Qatlib.Concepts.GateVocabulary.GateVocab.pauliAxis_legacy]
    exact Qatlib.Concepts.GateVocabulary.GateVocab.pauliAxis_unitary a

/-- The absolute real expectation of a tensor Pauli word in a density operator is at most one. -/
theorem sparsePauliWord_expectation_abs_le_one (n : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (w : Fin n → Option (Fin 3)) :
    |(Matrix.trace (tensorPauliWord n w * ρ)).re| ≤ 1 := by
  have hr : Matrix.traceNorm ρ = 1 := by
    have hh := Matrix.PosSemidef.traceNorm_eq_trace hρ.1
    have hh' := congrArg Complex.re hh
    simpa [hρ.2] using hh'
  calc _ ≤ ‖Matrix.trace (tensorPauliWord n w * ρ)‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (tensorPauliWord n w * ρ) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖tensorPauliWord n w‖ * Matrix.traceNorm ρ :=
      Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 := by simpa [hr] using l2_norm_unitary_le_one (sparsePauliWord_unitary n w)

/-- The absolute cross-moment expression is at most three to the overlap for compatible words
and zero for incompatible words. -/
private theorem sparsePauliMoment_abs_bound (n : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (u v : Fin n → Option (Fin 3)) :
    |sparsePauliMoment ρ u v| ≤
      if pauliWordsCompatible u v then (3 : ℝ) ^ pauliWordOverlap u v else 0 := by
  classical
  by_cases h : pauliWordsCompatible u v
  · simp only [sparsePauliMoment, if_pos h, abs_mul,
      abs_of_nonneg (show 0 ≤ (3 : ℝ) ^ pauliWordOverlap u v by positivity)]
    exact mul_le_of_le_one_right (by positivity)
      (sparsePauliWord_expectation_abs_le_one n ρ hρ _)
  · simp [sparsePauliMoment, h]

/-- A sparse Pauli estimator is unbiased, its variance is the coefficient-weighted cross-moment
sum minus the squared mean, and its variance is bounded by the displayed
absolute-coefficient overlap sum. See [HuangKuengPreskill2020]. -/
theorem sparse_pauli_exact_energy_variance_and_bound (n m : ℕ)
    (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ)
    (w : Fin m → Fin n → Option (Fin 3)) (c : Fin m → ℚ) :
    let μ := (Matrix.trace (sparsePauliObservable w c * ρ)).re
    let p := tensorPauliLaw n ρ hρ
    p.expect (sparsePauliValue w c) = μ ∧
    p.variance (sparsePauliValue w c) =
      (∑ j, ∑ l, (c j : ℝ) * (c l : ℝ) * sparsePauliMoment ρ (w j) (w l)) - μ ^ 2 ∧
    p.variance (sparsePauliValue w c) ≤
      ∑ j, ∑ l, |(c j : ℝ)| * |(c l : ℝ)| *
        (if pauliWordsCompatible (w j) (w l) then (3 : ℝ) ^ pauliWordOverlap (w j) (w l) else 0) := by
  classical
  (try dsimp only)
  have hm : (tensorPauliLaw n ρ hρ).expect (sparsePauliValue w c) =
      (Matrix.trace (sparsePauliObservable w c * ρ)).re := by
    simpa only [sparsePauliValue, sparsePauliObservable, Complex.ofReal_ratCast] using!
      (tensor_pauli_linear_observable_variance n m ρ hρ w (fun j => (c j : ℝ))).1
  have hs : (tensorPauliLaw n ρ hρ).expect (fun o => sparsePauliValue w c o ^ 2) =
      ∑ j, ∑ l, (c j : ℝ) * (c l : ℝ) * sparsePauliMoment ρ (w j) (w l) := by
    simp only [FinDist.expect, sparsePauliValue, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [← tensor_pauli_actual_cross_moment n ρ hρ (w j) (w l)]
    simp only [FinDist.expect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    ring
  have hv : (tensorPauliLaw n ρ hρ).variance (sparsePauliValue w c) =
      (∑ j, ∑ l, (c j : ℝ) * (c l : ℝ) * sparsePauliMoment ρ (w j) (w l)) -
        (Matrix.trace (sparsePauliObservable w c * ρ)).re ^ 2 := by
    rw [FinDist.variance_eq_expect_sq_sub, hs, hm]
  refine ⟨hm, hv, ?_⟩
  rw [hv]
  apply (sub_le_self _ (sq_nonneg _)).trans
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro l _
  calc _ ≤ |(c j : ℝ) * (c l : ℝ) * sparsePauliMoment ρ (w j) (w l)| := le_abs_self _
    _ = |(c j : ℝ)| * |(c l : ℝ)| * |sparsePauliMoment ρ (w j) (w l)| := by rw [abs_mul, abs_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sparsePauliMoment_abs_bound n ρ hρ _ _) (by positivity)

/-- The probability that any sparse Pauli sample mean exceeds error `ε` is bounded by the sum of
its coefficient-overlap variance bounds divided by `L * ε ^ 2`. See
[HuangKuengPreskill2020]. -/
theorem sparse_pauli_many_energies_same_record_accuracy (n m d L : ℕ)
    (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ)
    (w : Fin d → Fin m → Fin n → Option (Fin 3)) (c : Fin d → Fin m → ℚ)
    (ε : ℝ) (hL : 0 < L) (hε : 0 < ε) :
    let p := tensorPauliLaw n ρ hρ
    p.probEvent (fun ω : Fin L → Fin n → Fin 3 × Bool => ∃ a : Fin d,
      ε < |(∑ i, sparsePauliValue (w a) (c a) (ω i)) / (L : ℝ) -
        (Matrix.trace (sparsePauliObservable (w a) (c a) * ρ)).re|) ≤
      (∑ a, ∑ j, ∑ l, |(c a j : ℝ)| * |(c a l : ℝ)| *
        (if pauliWordsCompatible (w a j) (w a l) then
          (3 : ℝ) ^ pauliWordOverlap (w a j) (w a l) else 0)) / ((L : ℝ) * ε ^ 2) := by
  classical
  (try dsimp only)
  let p := tensorPauliLaw n ρ hρ
  have hden : 0 ≤ (L : ℝ) * ε ^ 2 := by positivity
  calc _ ≤ ∑ a : Fin d, p.probEvent (fun ω : Fin L → Fin n → Fin 3 × Bool =>
        ε < |FinDist.avg (sparsePauliValue (w a) (c a)) ω -
          (Matrix.trace (sparsePauliObservable (w a) (c a) * ρ)).re|) :=
      p.union_bound _
    _ ≤ ∑ a : Fin d, (∑ j, ∑ l, |(c a j : ℝ)| * |(c a l : ℝ)| *
        (if pauliWordsCompatible (w a j) (w a l) then
          (3 : ℝ) ^ pauliWordOverlap (w a j) (w a l) else 0)) / ((L : ℝ) * ε ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      have hh := sparse_pauli_exact_energy_variance_and_bound n m ρ hρ (w a) (c a)
      have hc := p.chebyshev_avg (sparsePauliValue (w a) (c a)) hL ε hε
      rw [hh.1] at hc
      exact hc.trans (div_le_div_of_nonneg_right hh.2.2 hden)
    _ = _ := (Finset.sum_div _ _ _).symm
end Qatlib.Concepts.ShadowModels.ShadowVariance
