/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.ClusterPatterns.WireComposition.ClusterWireInstrument
import Mathlib.Algebra.Order.Chebyshev

/-!
# Explicit adversary witnesses for search and parity

This module constructs the star-graph adversary matrix for the promise of zero or one marked
item and the hypercube adjacency matrix for parity. It computes their operator norms and
coordinate-filter norms, then obtains bounded-error circuit query lower bounds in the adversary
framework of [HoyerLeeSpalek2007].

Conjugation by a diagonal unitary preserves a witness's Hermitian property, output-zero
condition, operator norm, and filter bound. The resulting search and parity witnesses give the
respective square-root and linear dependence on the number of input bits.

## Main statements

* `negative_adversary_signed_phase_witness_transport`: preserve witness data under diagonal
  phases.
* `negative_adversary_star_actual_search_witness`: obtain the star witness and search lower
  bound.
* `negative_adversary_cube_actual_parity_witness`: obtain the cube witness and parity lower
  bound.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvWitness
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The Boolean input encoding `none` as the all-false string and `some i` as the string with
its only true bit at `i`. -/
def advStarInput {n : ℕ} (x : Option (Fin n)) (i : Fin n) : Bool := decide (x=some i)

/-- The adjacency matrix of the star with center `none` and leaves `some i`, with entries one
exactly between the center and a leaf. -/
noncomputable def advStarGamma (n : ℕ) : Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
  fun x y => if (x=none ∧ y ≠ none) ∨ (x ≠ none ∧ y=none) then 1 else 0

/-- The Boolean parity of a finite bit string, true exactly when its number of true entries is
odd. -/
def advParity {n : ℕ} (x : Fin n  → Bool) : Bool := decide (((List.ofFn x).count true)%2=1)

/-- The adjacency matrix of the Boolean hypercube, with entry one exactly when the two strings
differ at one coordinate. -/
noncomputable def advCubeGamma (n : ℕ) : Matrix (Fin n  → Bool) (Fin n  → Bool) ℂ :=
  fun x y => if (Finset.univ.filter (fun i => x i ≠ y i)).card=1 then 1 else 0

/-- Conjugating a Hermitian adversary witness by a diagonal matrix of unit-modulus phases
preserves its same-output zero entries, operator norm, and coordinate-filter bound. -/
theorem negative_adversary_signed_phase_witness_transport
    (X : Type) [Fintype X] [DecidableEq X] (n : ℕ) (input : X → Fin n → Bool)
    (Gamma : Matrix X X ℂ) (a : X → ℂ) (f : X → Bool) (hG : Gamma.IsHermitian)
    (ha : ∀ x, ‖a x‖ = 1) (hz : ∀ x y, f x = f y → Gamma x y = 0) :
    let G := Matrix.diagonal a * Gamma * (Matrix.diagonal a)ᴴ
    G.IsHermitian ∧ (∀ x y, f x = f y → G x y = 0) ∧ ‖G‖ = ‖Gamma‖ ∧
      advFilterBound input G = advFilterBound input Gamma := by
  classical
  let D : Matrix X X ℂ := Matrix.diagonal a
  have hD : D ∈ unitary (Matrix X X ℂ) := diagonal_mem_unitaryGroup a ha
  have hnorm : ∀ A : Matrix X X ℂ, ‖D * A * Dᴴ‖ = ‖A‖ := by
    intro A
    change ‖D * A * (star (⟨D, hD⟩ : unitary (Matrix X X ℂ)) : unitary (Matrix X X ℂ))‖ = _
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_mem_unitary_mul _ hD]
  refine ⟨?_, ?_, hnorm Gamma, ?_⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using
      Matrix.isHermitian_conjTranspose_mul_mul Dᴴ hG
  · intro x y hxy
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, hz x y hxy]
  · have hfilter : ∀ i, advFilter input (D * Gamma * Dᴴ) i = D * advFilter input Gamma i * Dᴴ := by
      intro i
      ext x y
      simp only [advFilter, D, Matrix.diagonal_mul, Matrix.diagonal_conjTranspose,
          Matrix.mul_diagonal]
      split <;> simp
    change advFilterBound input (D * Gamma * Dᴴ) = advFilterBound input Gamma
    unfold advFilterBound
    simp_rw [hfilter, hnorm]

/-- The absolute value of a real eigenvalue with a positive-norm eigenvector is bounded by the
matrix operator norm. -/
private theorem adv_eigenvalue_le_norm {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (v : QState I) (lam : ℝ)
    (hv : 0 < ‖toEuclidean_fromVec v‖) (he : A *ᵥ v = (lam : ℂ) • v) : |lam| ≤ ‖A‖ := by
  have h := l2_norm_mulVec_fromVec_le A v
  rw [he, show toEuclidean_fromVec ((lam : ℂ) • v) = (lam : ℂ) • toEuclidean_fromVec v from rfl,
    norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  exact (mul_le_mul_iff_left₀ hv).mp h

/-- The star adjacency matrix sends the center coordinate to the sum of leaf coordinates and
each leaf coordinate to the original center coordinate. -/
private theorem advStarGamma_action (n : ℕ) (v : QState (Option (Fin n))) :
    (advStarGamma n *ᵥ v) none = ∑ i, v (some i) ∧
      ∀ i, (advStarGamma n *ᵥ v) (some i) = v none := by
  constructor
  · simp [Matrix.mulVec, dotProduct, advStarGamma]
  · intro i
    simp [Matrix.mulVec, dotProduct, advStarGamma]

/-- For positive `n`, the star adversary matrix has operator norm `sqrt n`. -/
private theorem advStarGamma_norm (n : ℕ) (hn : 0 < n) : ‖advStarGamma n‖ = Real.sqrt n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply le_antisymm
  · refine l2_opNorm_le_of_mulVec_le (Real.sqrt_nonneg _) _ fun v => ?_
    have hsum := norm_sum_le (Finset.univ : Finset (Fin n)) (fun i => v (some i))
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => ‖v (some i)‖)
    have hs : ‖∑ i, v (some i)‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖v (some i)‖ ^ 2 := by
      have hp : 0 ≤ ∑ i, ‖v (some i)‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
      have hsq := (sq_le_sq₀ (norm_nonneg _) hp).mpr hsum
      simpa using hsq.trans hc
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hn0]
    simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_option,
      (advStarGamma_action n v).1, (advStarGamma_action n v).2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  · let v : QState (Option (Fin n)) := fun x => match x with
      | none => (Real.sqrt n : ℂ)
      | some _ => 1
    have hv : 0 < ‖toEuclidean_fromVec v‖ := by
      apply norm_pos_iff.mpr
      intro hz
      have hh := congrArg (fun z : EuclideanSpace ℂ (Option (Fin n)) => z none) hz
      have hr := Real.sqrt_pos.mpr hnpos
      simp only [toEuclidean_fromVec_apply, v, PiLp.zero_apply, Complex.ofReal_eq_zero] at hh
      linarith
    have he : advStarGamma n *ᵥ v = (Real.sqrt n : ℂ) • v := by
      ext x
      cases x with
      | none =>
        rw [(advStarGamma_action n v).1]
        simp only [v, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, Pi.smul_apply, smul_eq_mul]
        norm_cast
        exact (Real.mul_self_sqrt hn0).symm
      | some i => simp only [(advStarGamma_action n v).2, v, Pi.smul_apply, smul_eq_mul, mul_one]
    simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using adv_eigenvalue_le_norm _ _ _ hv he

/-- The star witness filtered at coordinate `i` exchanges the center and leaf `some i`
amplitudes and sets all other leaf amplitudes to zero. -/
private theorem advStarFilter_action {n : ℕ} (i : Fin n) (v : QState (Option (Fin n))) :
    (advFilter advStarInput (advStarGamma n) i *ᵥ v) none = v (some i) ∧
      ∀ j, (advFilter advStarInput (advStarGamma n) i *ᵥ v) (some j) =
        if j = i then v none else 0 := by
  constructor
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, advFilter, advStarGamma, advStarInput]
    simp
  · intro j
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, advFilter, advStarGamma, advStarInput]
    by_cases h : j = i <;> simp [h]

/-- Every coordinate-filtered star witness has operator norm one. -/
private theorem advStarFilter_norm {n : ℕ} (i : Fin n) :
    ‖advFilter advStarInput (advStarGamma n) i‖ = 1 := by
  apply le_antisymm
  · refine l2_opNorm_le_of_mulVec_le (by norm_num) _ fun v => ?_
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_option,
      (advStarFilter_action i v).1, (advStarFilter_action i v).2]
    have hsum : (∑ j : Fin n, ‖if j = i then v none else 0‖ ^ 2) = ‖v none‖ ^ 2 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    rw [hsum]
    have hi := Finset.single_le_sum (fun j _ => sq_nonneg ‖v (some j)‖) (Finset.mem_univ i)
    linarith
  · have h := l2_norm_mulVec_fromVec_le (advFilter advStarInput (advStarGamma n) i) (Qatlib.Foundations.PureStateMath.Ket none)
    have hout : advFilter advStarInput (advStarGamma n) i *ᵥ Qatlib.Foundations.PureStateMath.Ket none = Qatlib.Foundations.PureStateMath.Ket (some i) := by
      ext x
      cases x with
      | none => simp [(advStarFilter_action i (Qatlib.Foundations.PureStateMath.Ket none)).1, Qatlib.Foundations.PureStateMath.Ket]
      | some j => simp [(advStarFilter_action i (Qatlib.Foundations.PureStateMath.Ket none)).2, Qatlib.Foundations.PureStateMath.Ket]
    rw [hout, (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _),
      (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _), mul_one] at h
    exact h

/-- If the input has a positive number of coordinates and every filtered matrix has norm one,
its adversary filter bound equals one. -/
private theorem advFilterBound_one {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (hn : 0 < n) (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ)
    (h : ∀ i, ‖advFilter input Gamma i‖ = 1) : advFilterBound input Gamma = 1 := by
  unfold advFilterBound
  simp_rw [h]
  rw [List.ofFn_const]
  cases n with
  | zero => omega
  | succ n =>
    simp only [List.replicate_succ, List.foldl_cons, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    have helper : ∀ m : ℕ, (List.replicate m (1 : ℝ)).foldl max 1 = 1 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simpa only [List.replicate_succ, List.foldl_cons, max_self] using ih
    exact helper n

/-- For positive `n`, the star matrix is a Hermitian search witness with norm `sqrt n` and
filter bound one. Any normalized unitary query circuit solving the zero-or-one-marked
promise with error `eps` in `[0, 1/2]` satisfies `(1 - 2 * sqrt(eps * (1 - eps))) * sqrt n ≤
2 * QueryCount C`. -/
theorem negative_adversary_star_actual_search_witness (n : ℕ) (hn : 0 < n) :
    (advStarGamma n).IsHermitian ∧ ‖advStarGamma n‖ = Real.sqrt n ∧
    advFilterBound (advStarInput (n := n)) (advStarGamma n) = 1 ∧
    (∀ x y : Option (Fin n), x.isSome = y.isSome → advStarGamma n x y = 0) ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (C : Circuit ((Fin n × Bool) × W))
      (psi : QState ((Fin n × Bool) × W)) (E : Finset ((Fin n × Bool) × W)) (eps : ℝ),
      IsUnitaryCircuit C → Normalized psi → 0 ≤ eps → eps ≤ 1 / 2 →
      (∀ x : Option (Fin n), 1 - eps ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (advStarInput x)) C psi) (if x.isSome then E else Eᶜ)) →
      (1 - 2 * Real.sqrt (eps * (1 - eps))) * Real.sqrt n ≤ 2 * QueryCount C := by
  have hG : (advStarGamma n).IsHermitian := by
    ext x y
    cases x <;> cases y <;> simp [advStarGamma, Matrix.conjTranspose_apply]
  have hz : ∀ x y : Option (Fin n), x.isSome = y.isSome → advStarGamma n x y = 0 := by
    intro x y h
    cases x <;> cases y <;> simp_all [advStarGamma]
  have hnorm := advStarGamma_norm n hn
  have hfilter := advFilterBound_one hn advStarInput (advStarGamma n) advStarFilter_norm
  refine ⟨hG, hnorm, hfilter, hz, ?_⟩
  intro W _ _ C psi E eps hC hpsi he0 he1 hs
  simpa only [hnorm, hfilter, mul_one] using
    negative_adversary_actual_bounded_error_circuit_lower_bound (Option (Fin n)) W n
      advStarInput (advStarGamma n) Option.isSome C psi E eps hG hz hC hpsi he0 he1 hs

/-- Flip coordinate `i` of a Boolean string and leave its other coordinates unchanged. -/
def advCubeFlip {n : ℕ} (i : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = i then !x j else x j

/-- Flipping the same Boolean coordinate twice gives the original string. -/
private theorem advCubeFlip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (advCubeFlip i) := by
  intro x
  ext j
  by_cases h : j = i <;> simp [advCubeFlip, h]

/-- If two Boolean strings differ at exactly one coordinate and differ at `i`, the first is
obtained by flipping coordinate `i` of the second. -/
private theorem adv_cube_single_diff {n : ℕ} (x y : Fin n → Bool) (i : Fin n)
    (hc : (Finset.univ.filter (fun j => x j ≠ y j)).card = 1) (hi : x i ≠ y i) :
    x = advCubeFlip i y := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  have hij : i = j := by
    have hmem : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [hi]
    rw [hj] at hmem
    exact Finset.mem_singleton.mp hmem
  subst j
  ext k
  by_cases hk : k = i
  · subst k
    cases hx : x i <;> cases hy : y i <;> simp_all [advCubeFlip]
  · have he : x k = y k := by
      by_contra h
      have hm : k ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [h]
      rw [hj] at hm
      exact hk (Finset.mem_singleton.mp hm)
    simp [advCubeFlip, hk, he]

/-- A Boolean string and its coordinate-`i` flip differ at precisely the singleton set `{i}`. -/
private theorem adv_cube_flip_diff {n : ℕ} (i : Fin n) (y : Fin n → Bool) :
    Finset.univ.filter (fun j => advCubeFlip i y j ≠ y j) = {i} := by
  ext j
  by_cases h : j = i
  · subst j
    cases y i <;> simp [advCubeFlip]
  · simp [advCubeFlip, h]

/-- The cube adjacency matrix filtered at coordinate `i` is the permutation matrix for flipping
that coordinate. -/
private theorem advCubeFilter_perm {n : ℕ} (i : Fin n) :
    advFilter (fun x : Fin n → Bool => x) (advCubeGamma n) i = permMatrix (advCubeFlip i) := by
  ext x y
  by_cases h : x = advCubeFlip i y
  · subst x
    have hi : advCubeFlip i y i ≠ y i := by cases hy : y i <;> simp [advCubeFlip, hy]
    simp [advFilter, advCubeGamma, adv_cube_flip_diff, hi, permMatrix]
  · have hh : ¬ ((Finset.univ.filter (fun j => x j ≠ y j)).card = 1 ∧ x i ≠ y i) := by
      rintro ⟨hc, hi⟩
      exact h (adv_cube_single_diff x y i hc hi)
    simp only [advFilter, advCubeGamma, permMatrix, Matrix.of_apply, if_neg h]
    by_cases hi : x i = y i <;> simp_all

/-- The cube adjacency matrix is the sum of its coordinate-filtered matrices. -/
private theorem advCubeGamma_sum (n : ℕ) :
    advCubeGamma n = ∑ i, advFilter (fun x : Fin n → Bool => x) (advCubeGamma n) i := by
  ext x y
  simp only [Matrix.sum_apply, advFilter, advCubeGamma]
  by_cases hc : (Finset.univ.filter (fun j => x j ≠ y j)).card = 1
  · simp only [if_pos hc]
    rw [← Finset.sum_filter]
    simp [hc]
  · simp [hc]

/-- Every coordinate-filtered cube adjacency matrix has operator norm one. -/
private theorem advCubeFilter_norm {n : ℕ} (i : Fin n) :
    ‖advFilter (fun x : Fin n → Bool => x) (advCubeGamma n) i‖ = 1 := by
  rw [advCubeFilter_perm]
  exact l2_norm_unitary_eq_one (permMatrix_unitary (advCubeFlip_involutive i))

/-- The adjacency matrix of the `n`-dimensional Boolean hypercube has operator norm `n`. -/
private theorem advCubeGamma_norm (n : ℕ) : ‖advCubeGamma n‖ = (n : ℝ) := by
  apply le_antisymm
  · rw [advCubeGamma_sum]
    calc _ ≤ ∑ i : Fin n, ‖advFilter (fun x : Fin n → Bool => x) (advCubeGamma n) i‖ := norm_sum_le _ _
      _ = _ := by simp [advCubeFilter_norm]
  · let v : QState (Fin n → Bool) := fun _ => 1
    have hv : 0 < ‖toEuclidean_fromVec v‖ := by
      apply norm_pos_iff.mpr
      intro hz
      have h := congrArg (fun z : EuclideanSpace ℂ (Fin n → Bool) => z (fun _ => false)) hz
      simp [v] at h
    have he : advCubeGamma n *ᵥ v = (n : ℂ) • v := by
      rw [advCubeGamma_sum, Matrix.sum_mulVec]
      simp_rw [advCubeFilter_perm]
      have hp : ∀ i : Fin n, permMatrix (advCubeFlip i) *ᵥ v = v := by
        intro i
        ext x
        exact applyGate_permMatrix (advCubeFlip_involutive i) v x
      simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ext x
      simp [v]
    simpa only [abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] using
        adv_eigenvalue_le_norm _ _ (n : ℝ) hv he

/-- The number of true entries in `List.ofFn x` equals the sum of the Boolean true indicators
over all coordinates. -/
theorem adv_true_count (n : ℕ) (x : Fin n → Bool) :
    (List.ofFn x).count true = ∑ i, if x i then (1 : ℕ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ]
    rw [ih]
    cases x 0 <;> simp [Nat.add_comm]

/-- Boolean strings differing at exactly one coordinate have distinct parity values. -/
private theorem advParity_separates_edge {n : ℕ} (x y : Fin n → Bool)
    (hc : (Finset.univ.filter (fun j => x j ≠ y j)).card = 1) : advParity x ≠ advParity y := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hdiff : x i ≠ y i := by
    have hm : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by rw [hi]; simp
    simpa using hm
  have hsame : ∀ j ∈ Finset.univ.erase i, x j = y j := by
    intro j hj
    by_contra he
    have hm : j ∈ Finset.univ.filter (fun k => x k ≠ y k) := by simp [he]
    rw [hi] at hm
    have hji := Finset.mem_singleton.mp hm
    exact (Finset.mem_erase.mp hj).1 hji
  have hsum : (∑ j ∈ Finset.univ.erase i, if x j then (1 : ℕ) else 0) =
      ∑ j ∈ Finset.univ.erase i, if y j then (1 : ℕ) else 0 :=
    Finset.sum_congr rfl fun j hj => by rw [hsame j hj]
  have hx :=
      Finset.sum_erase_add (s := Finset.univ) (f := fun j => if x j then (1 : ℕ) else 0)
      (Finset.mem_univ i)
  have hy :=
      Finset.sum_erase_add (s := Finset.univ) (f := fun j => if y j then (1 : ℕ) else 0)
      (Finset.mem_univ i)
  unfold advParity
  rw [adv_true_count, adv_true_count]
  intro he
  have hh : ((∑ i, if x i then (1 : ℕ) else 0) % 2 = 1) ↔
      ((∑ i, if y i then (1 : ℕ) else 0) % 2 = 1) := by
    simpa only [decide_eq_true_eq] using
      (show (decide ((∑ i, if x i then (1 : ℕ) else 0) % 2 = 1) = true) ↔
        (decide ((∑ i, if y i then (1 : ℕ) else 0) % 2 = 1) = true) from by rw [he])
  cases hxi : x i <;> cases hyi : y i <;>
    simp only [hxi, hyi, Bool.false_eq_true, if_true, if_false] at hx hy hdiff
  all_goals first | exact hdiff rfl | omega

/-- For positive `n`, the cube matrix is a Hermitian parity witness with norm `n` and filter
bound one. Any normalized unitary query circuit computing parity with error `eps` in `[0,
1/2]` satisfies `(1 - 2 * sqrt(eps * (1 - eps))) * n ≤ 2 * QueryCount C`. -/
theorem negative_adversary_cube_actual_parity_witness (n : ℕ) (hn : 0 < n) :
    (advCubeGamma n).IsHermitian ∧ ‖advCubeGamma n‖ = n ∧
    advFilterBound (fun x : Fin n → Bool => x) (advCubeGamma n) = 1 ∧
    (∀ x y : Fin n → Bool, advParity x = advParity y → advCubeGamma n x y = 0) ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (C : Circuit ((Fin n × Bool) × W))
      (psi : QState ((Fin n × Bool) × W)) (E : Finset ((Fin n × Bool) × W)) (eps : ℝ),
      IsUnitaryCircuit C → Normalized psi → 0 ≤ eps → eps ≤ 1 / 2 →
      (∀ x : Fin n → Bool, 1 - eps ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) x) C psi) (if advParity x then E else Eᶜ)) →
      (1 - 2 * Real.sqrt (eps * (1 - eps))) * (n : ℝ) ≤ 2 * QueryCount C := by
  have hG : (advCubeGamma n).IsHermitian := by
    ext x y
    have he : (Finset.univ.filter (fun i => y i ≠ x i)) =
      Finset.univ.filter (fun i => x i ≠ y i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
    simp [Matrix.conjTranspose_apply, advCubeGamma, he]
  have hz : ∀ x y : Fin n → Bool, advParity x = advParity y → advCubeGamma n x y = 0 := by
    intro x y h
    unfold advCubeGamma
    rw [if_neg]
    exact fun hc => advParity_separates_edge x y hc h
  have hnorm := advCubeGamma_norm n
  have hfilter :=
      advFilterBound_one hn (fun x : Fin n → Bool => x) (advCubeGamma n) advCubeFilter_norm
  refine ⟨hG, hnorm, hfilter, hz, ?_⟩
  intro W _ _ C psi E eps hC hpsi he0 he1 hs
  simpa only [hnorm, hfilter, mul_one] using
    negative_adversary_actual_bounded_error_circuit_lower_bound (Fin n → Bool) W n
      (fun x => x) (advCubeGamma n) advParity C psi E eps hG hz hC hpsi he0 he1 hs

end Qatlib.Concepts.AdversaryBounds.AdvWitness
