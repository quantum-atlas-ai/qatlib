/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Lemma9LambdaLeQueryCountRestrictedStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeBounds
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

private def sensitivityFlip {N : ℕ} (i : Fin N) (x : Fin N → Bool) : Fin N → Bool :=
  fun j => if j=i then !x j else x j

/-- Flipping a fixed Boolean coordinate is an involution. -/
private theorem sensitivityFlip_involutive {N : ℕ} (i : Fin N) :
    Function.Involutive (sensitivityFlip i) := by
  intro x
  ext j
  by_cases h : j=i <;> simp [sensitivityFlip,h]

/-- If two Boolean vectors differ in exactly one coordinate, flipping that coordinate in either
vector recovers the other. -/
private theorem sensitivity_single_diff {N : ℕ} (x y : Fin N → Bool) (i : Fin N)
    (hc : (Finset.univ.filter (fun j => x j ≠ y j)).card=1) (hi : x i ≠ y i) :
    x=sensitivityFlip i y := by
  classical
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hc
  have hij : i=j := by
    have hm : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [hi]
    rw [hj] at hm
    exact Finset.mem_singleton.mp hm
  subst j
  ext k
  by_cases hk : k=i
  · subst k
    cases hx : x i <;> cases hy : y i <;> simp_all [sensitivityFlip]
  · have he : x k=y k := by
      by_contra he
      have hm : k ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [he]
      rw [hj] at hm
      exact hk (Finset.mem_singleton.mp hm)
    simp [sensitivityFlip,hk,he]

/-- A coordinate flip changes exactly the chosen coordinate. -/
private theorem sensitivity_flip_diff {N : ℕ} (i : Fin N) (y : Fin N → Bool) :
    Finset.univ.filter (fun j => sensitivityFlip i y j ≠ y j)={i} := by
  classical
  ext j
  by_cases hj : j=i
  · subst j
    cases y i <;> simp [sensitivityFlip]
  · simp [sensitivityFlip,hj]

/-- Each coordinate filtered sensitivity adjacency matrix has norm at most one. -/
theorem sensitivity_filter_norm_le_one {N : ℕ} (f : (Fin N → Bool) → Bool) (i : Fin N) :
    ‖advFilter (fun x => x) (sensAdjacency f) i‖ ≤ 1 := by
  classical
  let d : (Fin N → Bool) → ℂ := fun x => if f x ≠ f (sensitivityFlip i x) then 1 else 0
  have hm : advFilter (fun x => x) (sensAdjacency f) i =
      diagonal d * permMatrix (sensitivityFlip i) := by
    ext x y
    by_cases hxy : x=sensitivityFlip i y
    · subst x
      have hi : sensitivityFlip i y i ≠ y i := by
        cases hy : y i <;> simp [sensitivityFlip,hy]
      simp [advFilter,sensAdjacency,sensitivity_flip_diff,hi,Matrix.diagonal_mul,
        permMatrix,d,sensitivityFlip_involutive i y]
    · have hn : ¬ ((Finset.univ.filter (fun j => x j ≠ y j)).card=1 ∧ x i ≠ y i) := by
        rintro ⟨hc,hi⟩
        exact hxy (sensitivity_single_diff x y i hc hi)
      simp only [advFilter,sensAdjacency,Matrix.diagonal_mul,permMatrix,Matrix.of_apply,ite_eq_right hxy,mul_zero]
      by_cases hi : x i=y i <;> simp_all
  have hd : ‖diagonal d‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro x
    dsimp only [d]
    split_ifs <;> norm_num
  rw [hm]
  calc
    _ ≤ ‖diagonal d‖*‖permMatrix (sensitivityFlip i)‖ := norm_mul_le _ _
    _ = ‖diagonal d‖ := by
      rw [l2_norm_unitary_eq_one (permMatrix_unitary (sensitivityFlip_involutive i)),mul_one]
    _ ≤ 1 := hd

/-- The adversary filter bound of the sensitivity adjacency matrix is at most one. -/
theorem sensitivity_filter_bound_le_one {N : ℕ} (f : (Fin N → Bool) → Bool) :
    advFilterBound (fun x => x) (sensAdjacency f) ≤ 1 := by
  classical
  unfold advFilterBound
  have hl : ∀ a ∈ List.ofFn (fun i : Fin N => ‖advFilter (fun x => x) (sensAdjacency f) i‖), a ≤ 1 := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact sensitivity_filter_norm_le_one f i
  have aux (l : List ℝ) (h : ∀ a ∈ l, a ≤ 1) (z : ℝ) (hz : z ≤ 1) :
      l.foldl max z ≤ 1 := by
    induction l generalizing z with
    | nil => exact hz
    | cons a l ih =>
      exact ih (fun b hb => h b (List.mem_cons_of_mem a hb)) _
        (max_le hz (h a (List.mem_cons_self)))
  exact aux _ hl 0 (by norm_num)

/-- The sensitivity adjacency matrix is Hermitian. -/
theorem sensitivity_adversary_hermitian {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) : (sensAdjacency f).IsHermitian := by
  classical
  ext x y
  simp [Matrix.conjTranspose_apply,sensAdjacency,ne_comm]

/-- For a unitary circuit computing the function with success probability at least two thirds,
spectral sensitivity is at most `6 * (3 + 2 * Real.sqrt 2)` times the query count. -/
theorem lemma9LambdaLeQueryCountRestricted : Lemma9LambdaLeQueryCountRestricted := by
  classical
  intro N W _ _ C ψ E f hC hψ hs
  have hz : ∀ x y, f x=f y → sensAdjacency f x y=0 := by
    intro x y h
    simp [sensAdjacency,h]
  have hb := negative_adversary_actual_bounded_error_circuit_lower_bound
    (Fin N → Bool) W N (fun x => x) (sensAdjacency f) f C ψ E (1/3)
    (sensitivity_adversary_hermitian f) hz hC hψ (by norm_num) (by norm_num)
    (fun g => by simpa only [show (1 : ℝ)-1/3=2/3 by norm_num] using hs g)
  have hfilter := sensitivity_filter_bound_le_one f
  have ht : (0 : ℝ) ≤ QueryCount C := Nat.cast_nonneg _
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hr0 := Real.sqrt_nonneg 2
  have hrlt : Real.sqrt 2 < 3/2 := by nlinarith
  have he : Real.sqrt ((1/3 : ℝ)*(1-1/3))=Real.sqrt 2/3 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1/3)*(1-1/3))
    have hnon := Real.sqrt_nonneg ((1/3 : ℝ)*(1-1/3))
    nlinarith
  rw [he] at hb
  have hb' : (1-2*(Real.sqrt 2/3))*spectralSensitivity f ≤ 2*(QueryCount C : ℝ) :=
    hb.trans (mul_le_of_le_one_right (by positivity) hfilter)
  have hp : 0 < 3*(3+2*Real.sqrt 2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hb' hp.le
  nlinarith

end Qatlib.Concepts.QueryComplexity.DegreeBounds
