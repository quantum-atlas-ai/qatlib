/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.AdversaryBounds.AdvWitness

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.AdversaryBounds.AdvWitness
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.GraphQuery.GcBaselines

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def maskedStar (m : ℕ) (S : Finset (Fin m)) :
    Matrix (Option (Fin m)) (Option (Fin m)) ℂ
  | none, some j => if j ∈ S then 1 else 0
  | some i, none => if i ∈ S then 1 else 0
  | _, _ => 0

/-- Computes the central and leaf coordinates of the masked star matrix acting on a state. -/
private theorem maskedStar_action (m : ℕ) (S : Finset (Fin m)) (v : QState (Option (Fin m))) :
    (maskedStar m S *ᵥ v) none = ∑ i ∈ S, v (some i) ∧
      ∀ i, (maskedStar m S *ᵥ v) (some i) = if i ∈ S then v none else 0 := by
  constructor
  · simp [Matrix.mulVec, dotProduct, maskedStar]
  · intro i
    simp [Matrix.mulVec, dotProduct, maskedStar]

/-- Bounds the norm of `maskedStar` by the square root of the number of selected leaves. -/
theorem maskedStar_norm_le (m : ℕ) (S : Finset (Fin m)) :
    ‖maskedStar m S‖ ≤ Real.sqrt (S.card : ℝ) := by
  refine l2_opNorm_le_of_mulVec_le (Real.sqrt_nonneg _) _ fun v => ?_
  have hsum := norm_sum_le S (fun i => v (some i))
  have hc := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => ‖v (some i)‖)
  have hs : ‖∑ i ∈ S, v (some i)‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖v (some i)‖ ^ 2 := by
    have hp : 0 ≤ ∑ i ∈ S, ‖v (some i)‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact ((sq_le_sq₀ (norm_nonneg _) hp).mpr hsum).trans hc
  have hsub : (∑ i ∈ S, ‖v (some i)‖ ^ 2) ≤ ∑ i : Fin m, ‖v (some i)‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => sq_nonneg _)
  have hcount : (∑ i : Fin m, ‖if i ∈ S then v none else (0 : ℂ)‖ ^ 2) =
      (S.card : ℝ) * ‖v none‖ ^ 2 := by
    have he (i : Fin m) : ‖if i ∈ S then v none else (0 : ℂ)‖ ^ 2 =
        if i ∈ S then ‖v none‖ ^ 2 else 0 := by
      by_cases hi : i ∈ S <;> simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => he i), ← Finset.sum_filter]
    simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg S.card)]
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_option,
    (maskedStar_action m S v).1, (maskedStar_action m S v).2, hcount]
  nlinarith [mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg S.card)]

/-- Bounds each filtered star adversary norm by the square root of the number of leaves whose
input bit differs from the center. -/
theorem starFilter_norm_le {m q : ℕ} (input : Option (Fin m) → Fin q → Bool) (i : Fin q) :
    ‖advFilter input (advStarGamma m) i‖ ≤
      Real.sqrt ((Finset.univ.filter (fun j : Fin m => input (some j) i ≠ input none i)).card : ℝ) := by
  have he : advFilter input (advStarGamma m) i =
      maskedStar m (Finset.univ.filter (fun j : Fin m => input (some j) i ≠ input none i)) := by
    ext x y
    cases x <;> cases y <;> simp [advFilter, advStarGamma, maskedStar, ne_comm]
  rw [he]
  exact maskedStar_norm_le _ _

/-- Bounds the star adversary filter bound by any nonnegative uniform bound on its individual
filters. -/
theorem starFilterBound_le {m q : ℕ} (input : Option (Fin m) → Fin q → Bool)
    (K : ℝ) (hK : 0 ≤ K) (h : ∀ i, ‖advFilter input (advStarGamma m) i‖ ≤ K) :
    advFilterBound input (advStarGamma m) ≤ K := by
  have hf (L : List ℝ) (a : ℝ) (ha : a ≤ K) (hL : ∀ b ∈ L, b ≤ K) : L.foldl max a ≤ K := by
    induction L generalizing a with
    | nil => exact ha
    | cons b L ih =>
      exact ih (max a b) (max_le ha (hL b (by simp))) (fun x hx => hL x (by simp [hx]))
  apply hf _ 0 hK
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact h i

end Qatlib.Concepts.GraphQuery.GcBaselines
