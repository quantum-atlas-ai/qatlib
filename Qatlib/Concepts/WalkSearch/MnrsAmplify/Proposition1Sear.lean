/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Proposition1Stat

/-!
# Classical search from a spectral gap

Proves the classical search comparison in [MagniezNayakRolandSantha2011] using weighted finite
paths. Spectral contraction of a primitive symmetric stochastic matrix gives a geometric failure
bound; the prescribed stride and number of checks yield success at least `1 / 2` and explicit
setup, update, and check costs.

## Main statements

* `mnrs_classical_search_proposition_one`: For a primitive symmetric stochastic chain with
  positive absolute gap and a lower bound on nonzero marked density, proves success at least `1
  / 2` for the prescribed strided and every-step scans, together with the explicit update,
  check, and trace-cost bounds [Magniez et al., Proposition 1][MagniezNayakRolandSantha2011].
* `mnrs_classical_search_proposition_one_failure_geometric`: Under symmetry and mean-zero
  contraction of `P ^ a`, bounds failure after `r + 1` checks by `(1 - μ) * (1 - μ / 2) ^ r`,
  where `μ` is the marked fraction.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

open scoped BigOperators

/-- Every state returned by `mnrsRun` belongs to the marked set. -/
lemma mnrs_classical_search_proposition_one_run_support
    {X : Type*} [DecidableEq X] (M : Finset X) (a : ℕ)
    (xs : List X) (x : X) (h : (mnrsRun M a xs).1 = some x) : x ∈ M := by
  induction xs with
  | nil => simp [mnrsRun] at h
  | cons y ys ih =>
    by_cases hy : y ∈ M
    · have he : y = x := by simpa [mnrsRun, hy] using h
      simpa [← he] using hy
    · exact ih (by simpa [mnrsRun, hy] using h)

/-- The marked-state scan returns `none` exactly when every vertex in the input list is
unmarked. -/
lemma mnrs_classical_search_proposition_one_run_none
    {X : Type*} [DecidableEq X] (M : Finset X) (a : ℕ) (xs : List X) :
    (mnrsRun M a xs).1 = none ↔ ∀ x ∈ xs, x ∉ M := by
  induction xs with
  | nil => simp [mnrsRun]
  | cons x xs ih =>
    by_cases hx : x ∈ M <;> simp [mnrsRun, hx, ih]

/-- The update counter is at most `a` times the list length, and the check counter is at most
the list length. -/
lemma mnrs_classical_search_proposition_one_run_counters
    {X : Type*} [DecidableEq X] (M : Finset X) (a : ℕ) (xs : List X) :
    (mnrsRun M a xs).2.1 ≤ a * xs.length ∧
    (mnrsRun M a xs).2.2 ≤ xs.length := by
  induction xs with
  | nil => simp [mnrsRun]
  | cons x xs ih =>
    by_cases hx : x ∈ M
    · simp [mnrsRun, hx]
    · simpa [mnrsRun, hx, Nat.mul_add, Nat.add_comm] using
        And.intro (Nat.add_le_add_left ih.1 a) (Nat.add_le_add_left ih.2 1)

/-- With nonnegative update and check costs, every length-`r` search trace costs at most `S + r
* (a * U + C)`. -/
lemma mnrs_classical_search_proposition_one_trace_cost
    {X : Type*} [DecidableEq X] (M : Finset X) (a r : ℕ)
    (path : Fin (r + 1) → X) (S U C : ℝ) (hU : 0 ≤ U) (hC : 0 ≤ C) :
    mnrsTraceCost M a r path S U C ≤ S + r * (a * U + C) := by
  have h := mnrs_classical_search_proposition_one_run_counters M a
    (List.ofFn (fun i : Fin r => path i.castSucc))
  simp only [List.length_ofFn] at h
  have hu : ((mnrsRunOnPath M a r path).2.1 : ℝ) ≤ (a : ℝ) * r := by
    exact_mod_cast h.1
  have hc : ((mnrsRunOnPath M a r path).2.2 : ℝ) ≤ r := by
    exact_mod_cast h.2
  dsimp [mnrsTraceCost]
  nlinarith [mul_le_mul_of_nonneg_right hu hU, mul_le_mul_of_nonneg_right hc hC]

/-- The absolute spectral-gap condition `mnrsAbsoluteGap P δ` implies `δ ≤ 1`. -/
lemma mnrs_classical_search_proposition_one_gap_le_one
    {X : Type*} [Fintype X] (P : Matrix X X ℝ) (δ : ℝ)
    (hgap : mnrsAbsoluteGap P δ) : δ ≤ 1 := by
  have h : (0 : ℝ) ≤ 1 - δ := hgap.1 (Or.inl rfl)
  linarith

/-- Every sampled-path weight is nonnegative when `P` is row stochastic. -/
lemma mnrs_classical_search_proposition_one_weight_nonneg
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (a r : ℕ)
    (path : Fin (r + 1) → X) : 0 ≤ mnrsPathWeight P a r path := by
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro i _
  exact Matrix.nonneg_of_mem_rowStochastic ((Matrix.rowStochastic ℝ X).pow_mem hP a)

/-- Appending a vertex to a path multiplies its weight by the corresponding final entry of `P ^
a`. -/
lemma mnrs_classical_search_proposition_one_weight_snoc
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (a r : ℕ) (path : Fin (r + 1) → X) (x : X) :
    mnrsPathWeight P a (r + 1) (Fin.snoc path x) =
      mnrsPathWeight P a r path * (P ^ a) (path (Fin.last r)) x := by
  simp only [mnrsPathWeight, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last,
    Fin.succ_castSucc, Fin.succ_last]
  ring

/-- Reindexes a sum over paths of length `r + 1` as a sum over a length-`r` path and its last
vertex. -/
lemma mnrs_classical_search_proposition_one_sum_snoc
    {X : Type*} [Fintype X] (r : ℕ) (f : (Fin (r + 1) → X) → ℝ) :
    ∑ path, f path = ∑ path : Fin r → X, ∑ x : X, f (Fin.snoc path x) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (r + 1) => X)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- For a nonempty finite state space and row-stochastic `P`, the sampled-path weights sum to
one. -/
lemma mnrs_classical_search_proposition_one_weight_sum
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X) (a r : ℕ) :
    ∑ path : Fin (r + 1) → X, mnrsPathWeight P a r path = 1 := by
  induction r with
  | zero =>
    have hn : (Fintype.card X : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [mnrsPathWeight, hn]
  | succ r ih =>
    rw [mnrs_classical_search_proposition_one_sum_snoc]
    simp_rw [mnrs_classical_search_proposition_one_weight_snoc, ← Finset.mul_sum,
      Matrix.sum_row_of_mem_rowStochastic ((Matrix.rowStochastic ℝ X).pow_mem hP a),
      mul_one]
    exact ih

/-- The mass assigned to each optional search output is nonnegative for a row-stochastic
transition matrix. -/
lemma mnrs_classical_search_proposition_one_output_nonneg
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (a r : ℕ) (o : Option X) :
    0 ≤ mnrsOutputMass P M a r o := by
  apply Finset.sum_nonneg
  intro path _
  split_ifs
  · exact mnrs_classical_search_proposition_one_weight_nonneg P hP a r path
  · exact le_rfl

/-- On a nonempty finite state space, the output masses of the sampled-walk search sum to one. -/
lemma mnrs_classical_search_proposition_one_output_sum
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X)
    (M : Finset X) (a r : ℕ) : ∑ o : Option X, mnrsOutputMass P M a r o = 1 := by
  classical
  simp only [mnrsOutputMass]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact mnrs_classical_search_proposition_one_weight_sum P hP a r

/-- An unmarked state has zero search output mass. -/
lemma mnrs_classical_search_proposition_one_output_support
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (M : Finset X) (a r : ℕ) (x : X) (hx : x ∉ M) :
    mnrsOutputMass P M a r (some x) = 0 := by
  apply Finset.sum_eq_zero
  intro path _
  apply if_neg
  intro h
  exact hx (mnrs_classical_search_proposition_one_run_support M a _ x h)

/-- The absolute value of a real eigenvalue different from one is at most `1 - δ` under
`mnrsAbsoluteGap P δ`. -/
lemma mnrs_classical_search_proposition_one_eigenvalue_bound
    {X : Type*} [Fintype X] (P : Matrix X X ℝ) (δ ν : ℝ)
    (hgap : mnrsAbsoluteGap P δ) (v : X → ℝ)
    (hν : ν ≠ 1) (hv : v ≠ 0) (he : P.mulVec v = ν • v) :
    |ν| ≤ 1 - δ :=
  hgap.1 (Or.inr ⟨ν, v, hν, hv, he, rfl⟩)

/-- For `0 < δ ≤ 1`, the stride `Nat.ceil (1 / δ)` is at least one and at most `2 / δ` after
coercion to `ℝ`. -/
lemma mnrs_classical_search_proposition_one_stride_bounds
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ Nat.ceil (1 / δ) ∧ (Nat.ceil (1 / δ) : ℝ) ≤ 2 / δ := by
  constructor
  · exact Nat.one_le_ceil_iff.mpr (by positivity)
  · have h := Nat.ceil_lt_add_one (show 0 ≤ 1 / δ by positivity)
    have hi : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
    simp only [div_eq_mul_inv] at *
    linarith

/-- For positive `ε`, the prescribed number of checks, `Nat.ceil (4 / ε)` when `ε ≤ 1` and zero
otherwise, is at most `5 / ε`. -/
lemma mnrs_classical_search_proposition_one_check_bounds
    (ε : ℝ) (hε : 0 < ε) :
    ((if ε ≤ 1 then Nat.ceil (4 / ε) else 0 : ℕ) : ℝ) ≤ 5 / ε := by
  split_ifs with h
  · have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 / ε by positivity)
    have hi : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using h)
    simp only [div_eq_mul_inv] at *
    linarith
  · simp only [Nat.cast_zero]
    positivity

/-- The marked fraction of a nonempty finite state space is at most one. -/
lemma mnrs_classical_search_proposition_one_density_le_one
    {X : Type*} [Fintype X] [Nonempty X] (M : Finset X) :
    (M.card : ℝ) / Fintype.card X ≤ 1 := by
  apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
  exact_mod_cast Finset.card_le_univ M

/-- If a nonempty marked set would have density at least `ε > 1`, then the marked set is empty. -/
lemma mnrs_classical_search_proposition_one_empty_of_large_density
    {X : Type*} [Fintype X] [Nonempty X] (M : Finset X) (ε : ℝ)
    (hε : 1 < ε) (hM : M.Nonempty → ε ≤ (M.card : ℝ) / Fintype.card X) :
    M = ∅ := by
  by_contra h
  have := hM (Finset.nonempty_iff_ne_empty.mpr h)
  have := mnrs_classical_search_proposition_one_density_le_one M
  linarith

/-- Every vector fixed by `P` is fixed by each natural power of `P`. -/
lemma mnrs_classical_search_proposition_one_fixed_pow
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (v : X → ℝ) (hv : P.mulVec v = v) (k : ℕ) : (P ^ k).mulVec v = v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]

/-- Every real vector fixed by a primitive row-stochastic matrix on a nonempty finite state
space is constant. -/
lemma mnrs_classical_search_proposition_one_fixed_constant
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X)
    (hprim : P.IsPrimitive) (v : X → ℝ) (hv : P.mulVec v = v) :
    ∃ c : ℝ, ∀ x, v x = c := by
  obtain ⟨z, _, hz⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  obtain ⟨k, _, hk⟩ := hprim.exists_pos_pow
  have hp := (Matrix.rowStochastic ℝ X).pow_mem hP k
  have he := congrFun (mnrs_classical_search_proposition_one_fixed_pow P v hv k) z
  have hs : ∑ y, (P ^ k) z y * (v z - v y) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Matrix.sum_row_of_mem_rowStochastic hp, one_mul]
    simpa [Matrix.mulVec, dotProduct] using sub_eq_zero.mpr he.symm
  have hn : ∀ y ∈ (Finset.univ : Finset X),
      0 ≤ (P ^ k) z y * (v z - v y) := by
    intro y hy
    exact mul_nonneg (le_of_lt (hk z y)) (sub_nonneg.mpr (hz y hy))
  refine ⟨v z, fun x => ?_⟩
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs x (Finset.mem_univ x)
  have hd := (mul_eq_zero.mp h0).resolve_left (ne_of_gt (hk z x))
  exact (sub_eq_zero.mp hd).symm

/-- For a row-stochastic chain on a nonempty finite state space, an empty marked set gives
failure mass one. -/
lemma mnrs_classical_search_proposition_one_output_empty
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X) (a r : ℕ) :
    mnrsOutputMass P ∅ a r none = 1 := by
  have hr : ∀ path : Fin (r + 1) → X, (mnrsRunOnPath ∅ a r path).1 = none := by
    intro path
    exact (mnrs_classical_search_proposition_one_run_none ∅ a _).mpr (by simp)
  simp only [mnrsOutputMass, hr, ite_true]
  exact mnrs_classical_search_proposition_one_weight_sum P hP a r

/-- The total marked-state output mass equals one minus the failure mass. -/
lemma mnrs_classical_search_proposition_one_success_mass
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X)
    (M : Finset X) (a r : ℕ) :
    ∑ x ∈ M, mnrsOutputMass P M a r (some x) = 1 - mnrsOutputMass P M a r none := by
  have hs := mnrs_classical_search_proposition_one_output_sum P hP M a r
  rw [Fintype.sum_option] at hs
  have he : ∑ x : X, mnrsOutputMass P M a r (some x) =
      ∑ x ∈ M, mnrsOutputMass P M a r (some x) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ M)
    intro x _ hx
    exact mnrs_classical_search_proposition_one_output_support P M a r x hx
  rw [he] at hs
  linarith

/-- A failure-mass upper bound of `1 - p` for nonempty marked sets yields the full search
guarantee with success threshold `p`. -/
lemma mnrs_classical_search_proposition_one_guarantee_of_failure
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X)
    (M : Finset X) (a r : ℕ) (p : ℝ)
    (hf : M.Nonempty → mnrsOutputMass P M a r none ≤ 1 - p) :
    mnrsSearchGuarantee P M a r p := by
  refine ⟨mnrs_classical_search_proposition_one_output_nonneg P hP M a r,
    mnrs_classical_search_proposition_one_output_sum P hP M a r,
    mnrs_classical_search_proposition_one_output_support P M a r, ?_, ?_⟩
  · intro hM
    subst M
    exact mnrs_classical_search_proposition_one_output_empty P hP a r
  · intro hM
    rw [mnrs_classical_search_proposition_one_success_mass P hP M a r]
    linarith [hf hM]

/-- Bounds both the strided and every-step search trace costs by their stated expressions with
factor `10`, using stride at most `2 / δ` and check count at most `5 / ε`. -/
lemma mnrs_classical_search_proposition_one_cost_bounds
    {X : Type*} [DecidableEq X] (M : Finset X) (δ ε : ℝ)
    (hδ : 0 < δ) (_hε : 0 < ε) (a r : ℕ)
    (ha : (a : ℝ) ≤ 2 / δ) (hr : (r : ℝ) ≤ 5 / ε)
    (S U C : ℝ) (hS : 0 ≤ S) (hU : 0 ≤ U) (hC : 0 ≤ C) :
    (∀ path : Fin (r + 1) → X,
      mnrsTraceCost M a r path S U C ≤
        10 * (S + (1 / ε) * ((1 / δ) * U + C))) ∧
    (∀ path : Fin (a * r + 1) → X,
      mnrsTraceCost M 1 (a * r) path S U C ≤
        10 * (S + (1 / (δ * ε)) * (U + C))) := by
  have har : (a : ℝ) * r ≤ (2 / δ) * (5 / ε) :=
    mul_le_mul ha hr (by positivity) (by positivity)
  have heq : (2 / δ) * (5 / ε) = 10 / (δ * ε) := by ring
  rw [heq] at har
  constructor
  · intro path
    have hc := mnrs_classical_search_proposition_one_trace_cost M a r path S U C hU hC
    have hu := mul_le_mul_of_nonneg_right har hU
    have hcc := mul_le_mul_of_nonneg_right hr hC
    have he : 10 * (S + (1 / ε) * ((1 / δ) * U + C)) =
        10 * S + 10 / (δ * ε) * U + 10 / ε * C := by ring
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev] at *
    nlinarith [mul_nonneg (show 0 ≤ 5 / ε by positivity) hC]
  · intro path
    have hc := mnrs_classical_search_proposition_one_trace_cost M 1 (a * r) path S U C hU hC
    simp only [Nat.cast_mul, Nat.cast_one, one_mul] at hc
    have hu := mul_le_mul_of_nonneg_right har (add_nonneg hU hC)
    have he : 10 * (S + (1 / (δ * ε)) * (U + C)) =
        10 * S + 10 / (δ * ε) * (U + C) := by ring
    rw [he]
    linarith

/-- An eigenvector of `A` with eigenvalue `ν` is an eigenvector of `A ^ k` with eigenvalue `ν ^
k`. -/
lemma mnrs_classical_search_proposition_one_eigen_pow
    {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)
    (v : X → ℝ) (ν : ℝ) (hv : A.mulVec v = ν • v) (k : ℕ) :
    (A ^ k).mulVec v = ν ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih,
      smul_smul, pow_succ, mul_comm ν]

/-- The coordinate of `A ^ k v` along a Hermitian eigenbasis vector equals its original
coordinate multiplied by the corresponding eigenvalue to the power `k`. -/
lemma mnrs_classical_search_proposition_one_spectral_coordinate
    {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)
    (hA : A.IsHermitian) (k : ℕ) (v : EuclideanSpace ℝ X) (i : X) :
    inner ℝ (hA.eigenvectorBasis i) ((A ^ k).toEuclideanLin v) =
      hA.eigenvalues i ^ k * inner ℝ (hA.eigenvectorBasis i) v := by
  have he : (A ^ k).toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i ^ k • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    have hh := congrFun (mnrs_classical_search_proposition_one_eigen_pow A _ _
      (hA.mulVec_eigenvectorBasis i) k) j
    change (A ^ k).mulVec (hA.eigenvectorBasis i) j = _
    exact hh
  rw [← (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.pow k))
    (hA.eigenvectorBasis i) v, he, real_inner_smul_left]

/-- If all eigenbasis coordinates present in `v` correspond to eigenvalues of absolute value at
most `ρ`, then `|⟪v, A ^ k v⟫| ≤ ρ ^ k * ‖v‖ ^ 2`. -/
lemma mnrs_classical_search_proposition_one_spectral_quadratic
    {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)
    (hA : A.IsHermitian) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (v : EuclideanSpace ℝ X)
    (hv : ∀ i, inner ℝ (hA.eigenvectorBasis i) v = 0 ∨ |hA.eigenvalues i| ≤ ρ)
    (k : ℕ) :
    |inner ℝ v ((A ^ k).toEuclideanLin v)| ≤ ρ ^ k * ‖v‖ ^ 2 := by
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner v ((A ^ k).toEuclideanLin v)]
  simp_rw [mnrs_classical_search_proposition_one_spectral_coordinate]
  conv_lhs =>
    arg 1
    arg 2
    ext i
    lhs
    rw [real_inner_comm]
  calc
    |∑ i, inner ℝ (hA.eigenvectorBasis i) v *
        (hA.eigenvalues i ^ k * inner ℝ (hA.eigenvectorBasis i) v)| ≤
        ∑ i, |inner ℝ (hA.eigenvectorBasis i) v *
        (hA.eigenvalues i ^ k * inner ℝ (hA.eigenvectorBasis i) v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ρ ^ k * inner ℝ (hA.eigenvectorBasis i) v ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rcases hv i with hz | hb
      · simp [hz]
      · have he : |inner ℝ (hA.eigenvectorBasis i) v *
              (hA.eigenvalues i ^ k * inner ℝ (hA.eigenvectorBasis i) v)| =
              |hA.eigenvalues i| ^ k * inner ℝ (hA.eigenvectorBasis i) v ^ 2 := by
          rw [show inner ℝ (hA.eigenvectorBasis i) v *
            (hA.eigenvalues i ^ k * inner ℝ (hA.eigenvectorBasis i) v) =
            hA.eigenvalues i ^ k * inner ℝ (hA.eigenvectorBasis i) v ^ 2 by ring]
          simp only [abs_mul, abs_pow, sq_abs]
        rw [he]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hb k)
          (sq_nonneg _)
    _ = ρ ^ k * ‖v‖ ^ 2 := by
      rw [← Finset.mul_sum, hA.eigenvectorBasis.sum_sq_inner_right]

/-- For a primitive symmetric stochastic matrix with absolute gap `δ`, the quadratic form of `P
^ k` on a mean-zero vector is bounded in absolute value by `(1 - δ) ^ k * ‖v‖ ^ 2`. -/
lemma mnrs_classical_search_proposition_one_mean_zero_quadratic
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X)
    (hprim : P.IsPrimitive) (hsymm : P.IsSymm) (δ : ℝ)
    (hgap : mnrsAbsoluteGap P δ) (v : EuclideanSpace ℝ X)
    (hv : ∑ x, v x = 0) (k : ℕ) :
    |inner ℝ v ((P ^ k).toEuclideanLin v)| ≤ (1 - δ) ^ k * ‖v‖ ^ 2 := by
  have hh : P.IsHermitian := Matrix.IsHermitian.ext (fun i j => by simpa using hsymm.apply i j)
  apply mnrs_classical_search_proposition_one_spectral_quadratic P hh (1 - δ)
    (sub_nonneg.mpr (mnrs_classical_search_proposition_one_gap_le_one P δ hgap)) v _ k
  intro i
  by_cases hi : hh.eigenvalues i = 1
  · left
    obtain ⟨c, hc⟩ := mnrs_classical_search_proposition_one_fixed_constant P hP hprim
      (hh.eigenvectorBasis i) (by simpa [hi] using hh.mulVec_eigenvectorBasis i)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
      star_trivial, hc, ← Finset.sum_mul, hv, zero_mul]
  · right
    apply mnrs_classical_search_proposition_one_eigenvalue_bound P δ _ hgap _ hi
      _ (hh.mulVec_eigenvectorBasis i)
    intro hz
    have h0 : hh.eigenvectorBasis i = 0 := PiLp.ext (fun j => congrFun hz j)
    have hn := hh.eigenvectorBasis.orthonormal.1 i
    simp [h0] at hn

/-- For `0 < δ ≤ 1`, taking `Nat.ceil (1 / δ)` steps reduces `(1 - δ)` to a power at most `1 /
2`. -/
lemma mnrs_classical_search_proposition_one_amplification
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ^ Nat.ceil (1 / δ) ≤ (1 / 2 : ℝ) := by
  have hc : (1 : ℝ) ≤ δ * (Nat.ceil (1 / δ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (1 / δ)) hδ.le
    simpa [ne_of_gt hδ] using hh
  calc
    (1 - δ) ^ Nat.ceil (1 / δ) ≤ (Real.exp (-δ)) ^ Nat.ceil (1 / δ) :=
      pow_le_pow_left₀ (sub_nonneg.mpr hδ1) (Real.one_sub_le_exp_neg δ) _
    _ = Real.exp ((Nat.ceil (1 / δ) : ℝ) * (-δ)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le

/-- If `v` vanishes on `M`, its squared coordinate sum is at most the number of unmarked states
times `‖v‖ ^ 2`. -/
lemma mnrs_classical_search_proposition_one_supported_sum_sq
    {X : Type*} [Fintype X] [DecidableEq X] (M : Finset X)
    (v : EuclideanSpace ℝ X) (hv : ∀ x ∈ M, v x = 0) :
    (∑ x, v x) ^ 2 ≤ ((Fintype.card X : ℝ) - M.card) * ‖v‖ ^ 2 := by
  have hs : ∑ x, v x = ∑ x ∈ Mᶜ, v x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    exact hv x (by simpa using hx)
  have hsq : ∑ x ∈ Mᶜ, v x ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Mᶜ (fun _ : X => (1 : ℝ)) (fun x => v x)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [hs]
  calc
    (∑ x ∈ Mᶜ, v x) ^ 2 ≤ (Mᶜ.card : ℝ) * ∑ x ∈ Mᶜ, v x ^ 2 := hc
    _ ≤ (Mᶜ.card : ℝ) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = ((Fintype.card X : ℝ) - M.card) * ‖v‖ ^ 2 := by
      rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ M)]

/-- If a symmetric stochastic matrix contracts mean-zero quadratic forms by `1 / 2`, then its
quadratic form on a vector vanishing on `M` is bounded in absolute value by `(1 - M.card /
Fintype.card X / 2) * ‖v‖ ^ 2`. -/
lemma mnrs_classical_search_proposition_one_supported_quadratic
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (Q : Matrix X X ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ X) (hQsym : Q.IsSymm)
    (hc : ∀ w : EuclideanSpace ℝ X, (∑ x, w x) = 0 →
      |inner ℝ w (Q.toEuclideanLin w)| ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2)
    (M : Finset X) (v : EuclideanSpace ℝ X) (hv : ∀ x ∈ M, v x = 0) :
    |inner ℝ v (Q.toEuclideanLin v)| ≤
      (1 - (M.card : ℝ) / Fintype.card X / 2) * ‖v‖ ^ 2 := by
  let n : ℝ := Fintype.card X
  have hn : 0 < n := by
    have hh : 0 < Fintype.card X := Fintype.card_pos
    dsimp [n]
    exact_mod_cast hh
  let c : ℝ := (∑ x, v x) / n
  let z : EuclideanSpace ℝ X := WithLp.toLp 2 (fun _ => c)
  let w := v - z
  have hsum : ∑ x, w x = 0 := by
    simp only [w, z, c, PiLp.sub_apply, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    change (∑ x, v x) - n * ((∑ x, v x) / n) = 0
    (field_simp; ring)
  have hzw : inner ℝ z w = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, z,
      ← Finset.sum_mul] using congrArg (fun x : ℝ => x * c) hsum
  have hwz : inner ℝ w z = 0 := by rw [real_inner_comm]; exact hzw
  have hQz : Q.toEuclideanLin z = z := by
    apply PiLp.ext
    intro x
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, z,
      ← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hQ]
  have hsym : Q.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.IsHermitian.ext (fun i j => by simpa using hQsym.apply i j))
  have hcross : inner ℝ z (Q.toEuclideanLin w) = 0 := by
    rw [← hsym, hQz, hzw]
  have hvw : v = w + z := (sub_add_cancel v z).symm
  have he : inner ℝ v (Q.toEuclideanLin v) =
      inner ℝ w (Q.toEuclideanLin w) + ‖z‖ ^ 2 := by
    rw [hvw, map_add]
    simp [inner_add_left, inner_add_right, hQz, hcross, hwz]
  have hnorm : ‖v‖ ^ 2 = ‖w‖ ^ 2 + ‖z‖ ^ 2 := by
    rw [hvw, norm_add_sq_real, hwz]
    ring
  have hznorm : n * ‖z‖ ^ 2 = (∑ x, v x) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, z, c]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change n * (n * ((∑ x, v x) / n) ^ 2) = _
    field_simp
  have hzbound : ‖z‖ ^ 2 ≤ (1 - (M.card : ℝ) / n) * ‖v‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hn).mp
    rw [hznorm]
    have hs := mnrs_classical_search_proposition_one_supported_sum_sq M v hv
    (convert! hs using 1; (try field_simp); ring)
  rw [he]
  have hh := abs_add_le (inner ℝ w (Q.toEuclideanLin w)) (‖z‖ ^ 2)
  rw [abs_sq] at hh
  have hw := hc w hsum
  change _ ≤ (1 - (M.card : ℝ) / n / 2) * ‖v‖ ^ 2
  nlinarith

/-- The coordinate mask that replaces entries on the marked set by zero. -/
noncomputable def mnrs_classical_search_proposition_one_mask
    {X : Type*} [DecidableEq X] (M : Finset X) (v : EuclideanSpace ℝ X) :
    EuclideanSpace ℝ X := WithLp.toLp 2 (fun x => if x ∈ M then 0 else v x)

/-- The matrix obtained from `Q` by setting every row and column indexed by the marked set to
zero. -/
noncomputable def mnrs_classical_search_proposition_one_compression
    {X : Type*} [DecidableEq X] (Q : Matrix X X ℝ) (M : Finset X) : Matrix X X ℝ :=
  fun x y => if x ∈ M then 0 else if y ∈ M then 0 else Q x y

/-- The marked-coordinate mask is self-adjoint with respect to the real Euclidean inner product. -/
lemma mnrs_classical_search_proposition_one_mask_inner
    {X : Type*} [Fintype X] [DecidableEq X] (M : Finset X)
    (v w : EuclideanSpace ℝ X) :
    inner ℝ v (mnrs_classical_search_proposition_one_mask M w) =
      inner ℝ (mnrs_classical_search_proposition_one_mask M v) w := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ M <;> simp [mnrs_classical_search_proposition_one_mask, hx]

/-- Masking marked coordinates cannot increase the squared Euclidean norm. -/
lemma mnrs_classical_search_proposition_one_mask_norm
    {X : Type*} [Fintype X] [DecidableEq X] (M : Finset X)
    (v : EuclideanSpace ℝ X) :
    ‖mnrs_classical_search_proposition_one_mask M v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ M <;> simp [mnrs_classical_search_proposition_one_mask, hx, sq_nonneg]

/-- Applying the compressed matrix is the same as masking, applying `Q`, and masking again. -/
lemma mnrs_classical_search_proposition_one_compression_apply
    {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ) (M : Finset X)
    (v : EuclideanSpace ℝ X) :
    (mnrs_classical_search_proposition_one_compression Q M).toEuclideanLin v =
      mnrs_classical_search_proposition_one_mask M
        (Q.toEuclideanLin (mnrs_classical_search_proposition_one_mask M v)) := by
  apply PiLp.ext
  intro x
  change (∑ y, mnrs_classical_search_proposition_one_compression Q M x y * v y) = _
  by_cases hx : x ∈ M
  · simp [mnrs_classical_search_proposition_one_compression,
      mnrs_classical_search_proposition_one_mask, hx]
  · simp only [mnrs_classical_search_proposition_one_compression, hx, ite_false,
      mnrs_classical_search_proposition_one_mask, Matrix.toLpLin_apply]
    change (∑ y, (if y ∈ M then 0 else Q x y) * v y) =
      ∑ y, Q x y * (if y ∈ M then 0 else v y)
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ M <;> simp [hy]

/-- The marked-coordinate compression of a real symmetric matrix is Hermitian. -/
lemma mnrs_classical_search_proposition_one_compression_hermitian
    {X : Type*} [DecidableEq X] (Q : Matrix X X ℝ) (hQ : Q.IsSymm) (M : Finset X) :
    (mnrs_classical_search_proposition_one_compression Q M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  by_cases hx : x ∈ M <;> by_cases hy : y ∈ M <;>
    simp [mnrs_classical_search_proposition_one_compression, hx, hy, hQ.apply]

/-- Under the mean-zero contraction hypothesis, the compressed quadratic form is bounded in
absolute value by `(1 - M.card / Fintype.card X / 2) * ‖v‖ ^ 2`. -/
lemma mnrs_classical_search_proposition_one_compression_quadratic
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (Q : Matrix X X ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ X) (hQsym : Q.IsSymm)
    (hc : ∀ w : EuclideanSpace ℝ X, (∑ x, w x) = 0 →
      |inner ℝ w (Q.toEuclideanLin w)| ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2)
    (M : Finset X) (v : EuclideanSpace ℝ X) :
    |inner ℝ v ((mnrs_classical_search_proposition_one_compression Q M).toEuclideanLin v)| ≤
      (1 - (M.card : ℝ) / Fintype.card X / 2) * ‖v‖ ^ 2 := by
  rw [mnrs_classical_search_proposition_one_compression_apply,
    mnrs_classical_search_proposition_one_mask_inner]
  have hm := mnrs_classical_search_proposition_one_density_le_one M
  have hρ : 0 ≤ 1 - (M.card : ℝ) / Fintype.card X / 2 := by linarith
  exact (mnrs_classical_search_proposition_one_supported_quadratic Q hQ hQsym hc M
    (mnrs_classical_search_proposition_one_mask M v)
    (by intro x hx; simp [mnrs_classical_search_proposition_one_mask, hx])).trans
      (mul_le_mul_of_nonneg_left (mnrs_classical_search_proposition_one_mask_norm M v) hρ)

/-- Under the mean-zero contraction hypothesis, the quadratic form of the `k`th compressed power
is bounded by `(1 - M.card / Fintype.card X / 2) ^ k * ‖v‖ ^ 2`. -/
lemma mnrs_classical_search_proposition_one_compression_power
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (Q : Matrix X X ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ X) (hQsym : Q.IsSymm)
    (hc : ∀ w : EuclideanSpace ℝ X, (∑ x, w x) = 0 →
      |inner ℝ w (Q.toEuclideanLin w)| ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2)
    (M : Finset X) (v : EuclideanSpace ℝ X) (k : ℕ) :
    |inner ℝ v (((mnrs_classical_search_proposition_one_compression Q M) ^ k).toEuclideanLin v)| ≤
      (1 - (M.card : ℝ) / Fintype.card X / 2) ^ k * ‖v‖ ^ 2 := by
  let B := mnrs_classical_search_proposition_one_compression Q M
  have hB : B.IsHermitian := mnrs_classical_search_proposition_one_compression_hermitian Q hQsym M
  have hρ : 0 ≤ 1 - (M.card : ℝ) / Fintype.card X / 2 := by
    have := mnrs_classical_search_proposition_one_density_le_one M
    linarith
  apply mnrs_classical_search_proposition_one_spectral_quadratic B hB _ hρ v _ k
  intro i
  right
  have hi := mnrs_classical_search_proposition_one_compression_quadratic Q hQ hQsym hc M
    (hB.eigenvectorBasis i)
  have he := mnrs_classical_search_proposition_one_spectral_coordinate B hB 1
    (hB.eigenvectorBasis i) i
  simp only [pow_one, real_inner_self_eq_norm_sq,
    hB.eigenvectorBasis.orthonormal.1 i, one_pow, mul_one] at he
  change |inner ℝ (hB.eigenvectorBasis i) (B.toEuclideanLin (hB.eigenvectorBasis i))| ≤ _ at hi
  simpa [he, hB.eigenvectorBasis.orthonormal.1 i] using hi

/-- The recursively defined weight of avoiding `M` for `r` checks starting at a specified
vertex, with zero checks assigned weight one. -/
noncomputable def mnrs_classical_search_proposition_one_avoid
    {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ) (M : Finset X) :
    ℕ → X → ℝ
  | 0, _ => 1
  | r + 1, x => if x ∈ M then 0 else ∑ y, Q x y * mnrs_classical_search_proposition_one_avoid Q M r y

/-- Reindexes a sum over paths of length `r + 1` as a sum over their first vertex and length-`r`
tail. -/
lemma mnrs_classical_search_proposition_one_sum_cons
    {X : Type*} [Fintype X] (r : ℕ) (f : (Fin (r + 1) → X) → ℝ) :
    ∑ path, f path = ∑ x : X, ∑ path : Fin r → X, f (Fin.cons x path) := by
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => X)).sum_comp,
    Fintype.sum_prod_type]
  rfl

/-- Expands the avoidance recursion as a sum of transition products over tails whose checked
vertices are all unmarked. -/
lemma mnrs_classical_search_proposition_one_avoid_expansion
    {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ) (M : Finset X)
    (r : ℕ) (x : X) :
    (∑ tail : Fin r → X,
      if ∀ i : Fin r, (Fin.cons x tail : Fin (r + 1) → X) i.castSucc ∉ M then
        ∏ i : Fin r, Q ((Fin.cons x tail : Fin (r + 1) → X) i.castSucc) ((Fin.cons x tail : Fin (r + 1) → X) i.succ)
      else 0) = mnrs_classical_search_proposition_one_avoid Q M r x := by
  induction r generalizing x with
  | zero => simp [mnrs_classical_search_proposition_one_avoid]
  | succ r ih =>
    rw [mnrs_classical_search_proposition_one_sum_cons]
    simp only [Fin.forall_fin_succ, Fin.castSucc_zero, Fin.cons_zero,
      Fin.cons_succ, Fin.prod_univ_succ]
    by_cases hx : x ∈ M
    · simp [hx, mnrs_classical_search_proposition_one_avoid]
    · simp only [hx, not_false_eq_true, true_and, mnrs_classical_search_proposition_one_avoid,
        ite_false]
      apply Finset.sum_congr rfl
      intro y _
      rw [← ih y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      split_ifs <;> simp_all

/-- The failure output mass equals the uniform average of the avoidance weights for transition
matrix `P ^ a`. -/
lemma mnrs_classical_search_proposition_one_failure_eq_avoid
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (M : Finset X)
    (a r : ℕ) : mnrsOutputMass P M a r none =
      (Fintype.card X : ℝ)⁻¹ * ∑ x, mnrs_classical_search_proposition_one_avoid (P ^ a) M r x := by
  have hr : ∀ path : Fin (r + 1) → X,
      (mnrsRunOnPath M a r path).1 = none ↔ ∀ i : Fin r, path i.castSucc ∉ M := by
    intro path
    simp [mnrsRunOnPath, mnrs_classical_search_proposition_one_run_none, List.mem_ofFn]
  simp only [mnrsOutputMass, hr, mnrsPathWeight]
  rw [mnrs_classical_search_proposition_one_sum_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mnrs_classical_search_proposition_one_avoid_expansion (P ^ a) M r x,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  split_ifs <;> simp

/-- Avoidance weights are nonnegative for a row-stochastic transition matrix. -/
lemma mnrs_classical_search_proposition_one_avoid_nonneg
    {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (r : ℕ) (x : X) :
    0 ≤ mnrs_classical_search_proposition_one_avoid Q M r x := by
  induction r generalizing x with
  | zero => exact zero_le_one
  | succ r ih =>
    dsimp [mnrs_classical_search_proposition_one_avoid]
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg (hQ.1 x y) (ih y))

/-- For a row-stochastic transition matrix, the avoidance weight at a fixed starting vertex is
nonincreasing in the number of checks. -/
lemma mnrs_classical_search_proposition_one_avoid_antitone
    {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (x : X) :
    Antitone (fun r => mnrs_classical_search_proposition_one_avoid Q M r x) := by
  apply antitone_nat_of_succ_le
  intro r
  induction r generalizing x with
  | zero =>
    by_cases hx : x ∈ M <;> simp [mnrs_classical_search_proposition_one_avoid, hx,
      Matrix.sum_row_of_mem_rowStochastic hQ]
  | succ r ih =>
    by_cases hx : x ∈ M
    · simp [mnrs_classical_search_proposition_one_avoid, hx]
    · simp only [mnrs_classical_search_proposition_one_avoid, hx, ite_false]
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih y) (hQ.1 x y))

/-- The avoidance vector after `r + 1` checks equals the `r`th power of the compressed matrix
applied to the indicator of the unmarked set. -/
lemma mnrs_classical_search_proposition_one_avoid_compression
    {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (r : ℕ) :
    WithLp.toLp 2 (mnrs_classical_search_proposition_one_avoid Q M (r + 1)) =
      ((mnrs_classical_search_proposition_one_compression Q M) ^ r).toEuclideanLin
        (mnrs_classical_search_proposition_one_mask M (WithLp.toLp 2 (fun _ => 1))) := by
  induction r with
  | zero =>
    apply PiLp.ext
    intro x
    simp [mnrs_classical_search_proposition_one_avoid,
      mnrs_classical_search_proposition_one_mask, Matrix.sum_row_of_mem_rowStochastic hQ]
  | succ r ih =>
    have hi := congrArg (mnrs_classical_search_proposition_one_compression Q M).toEuclideanLin ih
    have he : ∀ (A B : Matrix X X ℝ) (v : EuclideanSpace ℝ X),
        A.toEuclideanLin (B.toEuclideanLin v) = (A * B).toEuclideanLin v := by
      intro A B v
      apply PiLp.ext
      intro x
      exact congrFun (Matrix.mulVec_mulVec v A B) x
    rw [he, ← pow_succ'] at hi
    rw [← hi, mnrs_classical_search_proposition_one_compression_apply]
    apply PiLp.ext
    intro x
    by_cases hx : x ∈ M
    · simp [mnrs_classical_search_proposition_one_avoid,
        mnrs_classical_search_proposition_one_mask, hx]
    · change _ = if x ∈ M then 0 else (Q.mulVec (fun y => if y ∈ M then 0 else
        mnrs_classical_search_proposition_one_avoid Q M (r + 1) y)) x
      rw [if_neg hx]
      simp only [mnrs_classical_search_proposition_one_avoid, hx, ite_false,
        Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ M <;> simp [hy]

/-- Discarding the first `k` avoidance checks bounds the weight after `k + r` checks by `P ^ k`
applied to the `r`-check avoidance vector. -/
lemma mnrs_classical_search_proposition_one_drop_checks
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (k r : ℕ) (x : X) :
    mnrs_classical_search_proposition_one_avoid P M (k + r) x ≤
      (P ^ k).mulVec (mnrs_classical_search_proposition_one_avoid P M r) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    by_cases hx : x ∈ M
    · have hp := (Matrix.rowStochastic ℝ X).pow_mem hP (k + 1)
      have hh := Matrix.nonneg_mulVec_of_mem_rowStochastic hp
        (mnrs_classical_search_proposition_one_avoid_nonneg P hP M r) x
      simpa [Nat.succ_add, mnrs_classical_search_proposition_one_avoid, hx] using hh
    · rw [Nat.succ_add, mnrs_classical_search_proposition_one_avoid, if_neg hx,
        pow_succ', ← Matrix.mulVec_mulVec]
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih y) (hP.1 x y))

/-- Checking every step for `a * r` checks has avoidance weight at most that of `r` checks under
`P ^ a`, for stride `a ≥ 1`. -/
lemma mnrs_classical_search_proposition_one_avoid_stride_comparison
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (a : ℕ) (ha : 1 ≤ a)
    (r : ℕ) (x : X) :
    mnrs_classical_search_proposition_one_avoid P M (a * r) x ≤
      mnrs_classical_search_proposition_one_avoid (P ^ a) M r x := by
  induction r generalizing x with
  | zero => simp [mnrs_classical_search_proposition_one_avoid]
  | succ r ih =>
    by_cases hx : x ∈ M
    · have hpos : 0 < a * (r + 1) := Nat.mul_pos ha (Nat.succ_pos _)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      simp [hk, mnrs_classical_search_proposition_one_avoid, hx]
    · rw [mnrs_classical_search_proposition_one_avoid, if_neg hx]
      calc
        mnrs_classical_search_proposition_one_avoid P M (a * (r + 1)) x ≤
            (P ^ a).mulVec (mnrs_classical_search_proposition_one_avoid P M (a * r)) x := by
          simpa [Nat.mul_add, Nat.add_comm] using
            mnrs_classical_search_proposition_one_drop_checks P hP M a (a * r) x
        _ ≤ ∑ y, (P ^ a) x y * mnrs_classical_search_proposition_one_avoid (P ^ a) M r y := by
          exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih y)
            (Matrix.nonneg_of_mem_rowStochastic ((Matrix.rowStochastic ℝ X).pow_mem hP a)))

/-- Failure mass with every-step checks through `a * r` is at most failure mass with `r` checks
at stride `a ≥ 1`. -/
lemma mnrs_classical_search_proposition_one_failure_stride_comparison
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (a : ℕ) (ha : 1 ≤ a) (r : ℕ) :
    mnrsOutputMass P M 1 (a * r) none ≤ mnrsOutputMass P M a r none := by
  rw [mnrs_classical_search_proposition_one_failure_eq_avoid,
    mnrs_classical_search_proposition_one_failure_eq_avoid, pow_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun x _ =>
    mnrs_classical_search_proposition_one_avoid_stride_comparison P hP M a ha r x)

/-- For a fixed stochastic transition matrix and stride, failure output mass is nonincreasing in
the number of checks. -/
lemma mnrs_classical_search_proposition_one_failure_antitone
    {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (M : Finset X) (a : ℕ) :
    Antitone (fun r => mnrsOutputMass P M a r none) := by
  intro r s hrs
  simp only [mnrs_classical_search_proposition_one_failure_eq_avoid]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun x _ => mnrs_classical_search_proposition_one_avoid_antitone
    (P ^ a) ((Matrix.rowStochastic ℝ X).pow_mem hP a) M x hrs)

/-- Under symmetry and mean-zero contraction of `P ^ a`, bounds failure after `r + 1` checks by
`(1 - μ) * (1 - μ / 2) ^ r`, where `μ` is the marked fraction. -/
lemma mnrs_classical_search_proposition_one_failure_geometric
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X) (a : ℕ)
    (hsym : (P ^ a).IsSymm)
    (hc : ∀ w : EuclideanSpace ℝ X, (∑ x, w x) = 0 →
      |inner ℝ w ((P ^ a).toEuclideanLin w)| ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2)
    (M : Finset X) (r : ℕ) :
    mnrsOutputMass P M a (r + 1) none ≤
      (1 - (M.card : ℝ) / Fintype.card X) *
        (1 - (M.card : ℝ) / Fintype.card X / 2) ^ r := by
  let d := mnrs_classical_search_proposition_one_mask M (WithLp.toLp 2 (fun _ : X => 1))
  have hQ := (Matrix.rowStochastic ℝ X).pow_mem hP a
  have he : inner ℝ d (WithLp.toLp 2 (mnrs_classical_search_proposition_one_avoid (P ^ a) M (r + 1))) =
      ∑ x, mnrs_classical_search_proposition_one_avoid (P ^ a) M (r + 1) x := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ M <;> simp [d, mnrs_classical_search_proposition_one_mask,
      mnrs_classical_search_proposition_one_avoid, hx]
  have hd : ‖d‖ ^ 2 = (Fintype.card X : ℝ) - M.card := by
    simp only [EuclideanSpace.real_norm_sq_eq, d, mnrs_classical_search_proposition_one_mask]
    simp only [ite_pow, zero_pow (by decide : 2 ≠ 0), one_pow]
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one, zero_add]
    have hf : Finset.univ.filter (fun x => x ∉ M) = Mᶜ := by ext x; simp
    rw [hf, Finset.card_compl, Nat.cast_sub (Finset.card_le_univ M)]
  have hp := mnrs_classical_search_proposition_one_compression_power (P ^ a) hQ hsym hc M d r
  rw [← mnrs_classical_search_proposition_one_avoid_compression (P ^ a) hQ M r, he, hd] at hp
  have hh := (le_abs_self _).trans hp
  rw [mnrs_classical_search_proposition_one_failure_eq_avoid]
  have hi := mul_le_mul_of_nonneg_left hh (show 0 ≤ (Fintype.card X : ℝ)⁻¹ by positivity)
  convert! hi using 1
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  try field_simp

/-- For a nonempty marked set and the stated contraction hypothesis, every finite sum of
positive-check failure masses is at most `2` divided by the marked fraction. -/
lemma mnrs_classical_search_proposition_one_hitting_tail
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X) (a : ℕ)
    (hsym : (P ^ a).IsSymm)
    (hc : ∀ w : EuclideanSpace ℝ X, (∑ x, w x) = 0 →
      |inner ℝ w ((P ^ a).toEuclideanLin w)| ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2)
    (M : Finset X) (hM : M.Nonempty) (r : ℕ) :
    ∑ j ∈ Finset.range r, mnrsOutputMass P M a (j + 1) none ≤
      2 / ((M.card : ℝ) / Fintype.card X) := by
  let μ : ℝ := (M.card : ℝ) / Fintype.card X
  have hμ : 0 < μ := div_pos (by exact_mod_cast hM.card_pos)
    (by exact_mod_cast Fintype.card_pos)
  have hμ1 : μ ≤ 1 := mnrs_classical_search_proposition_one_density_le_one M
  have hρ : 0 ≤ 1 - μ / 2 := by linarith
  calc
    ∑ j ∈ Finset.range r, mnrsOutputMass P M a (j + 1) none ≤
        ∑ j ∈ Finset.range r, (1 - μ / 2) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      have hh := mnrs_classical_search_proposition_one_failure_geometric P hP a hsym hc M j
      have hp := pow_nonneg hρ j
      change _ ≤ (1 - μ) * (1 - μ / 2) ^ j at hh
      nlinarith
    _ ≤ 2 / μ := by
      apply (le_div_iff₀ hμ).mpr
      have hh := geom_sum_mul_neg (1 - μ / 2) r
      have hp := pow_nonneg hρ r
      nlinarith

/-- If the marked fraction is at least positive `ε` and the strided chain satisfies the stated
contraction bound, `Nat.ceil (4 / ε)` checks have failure mass at most `1 / 2`. -/
lemma mnrs_classical_search_proposition_one_failure_half
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X) (a : ℕ)
    (hsym : (P ^ a).IsSymm)
    (hc : ∀ w : EuclideanSpace ℝ X, (∑ x, w x) = 0 →
      |inner ℝ w ((P ^ a).toEuclideanLin w)| ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2)
    (M : Finset X) (hM : M.Nonempty) (ε : ℝ) (hε : 0 < ε)
    (hεM : ε ≤ (M.card : ℝ) / Fintype.card X) :
    mnrsOutputMass P M a (Nat.ceil (4 / ε)) none ≤ (1 / 2 : ℝ) := by
  let r := Nat.ceil (4 / ε)
  let F := mnrsOutputMass P M a r none
  have hF : 0 ≤ F := mnrs_classical_search_proposition_one_output_nonneg P hP M a r none
  have hr : 4 / ε ≤ (r : ℝ) := Nat.le_ceil _
  have ht := mnrs_classical_search_proposition_one_hitting_tail P hP a hsym hc M hM r
  have hm : (r : ℝ) * F ≤ ∑ j ∈ Finset.range r, mnrsOutputMass P M a (j + 1) none := by
    calc
      (r : ℝ) * F = ∑ _j ∈ Finset.range r, F := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj =>
        mnrs_classical_search_proposition_one_failure_antitone P hP M a
          (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
  have hd : 2 / ((M.card : ℝ) / Fintype.card X) ≤ 2 / ε :=
    div_le_div_of_nonneg_left (by norm_num) hε hεM
  have hh : (4 / ε) * F ≤ 2 / ε :=
    (mul_le_mul_of_nonneg_right hr hF).trans (hm.trans (ht.trans hd))
  have hh' := mul_le_mul_of_nonneg_left hh hε.le
  have he1 : ε * ((4 / ε) * F) = 4 * F := by field_simp
  have he2 : ε * (2 / ε) = 2 := by field_simp
  rw [he1, he2] at hh'
  change F ≤ _
  linarith

/-- For a primitive symmetric stochastic chain with positive absolute gap and a lower bound on
nonzero marked density, proves success at least `1 / 2` for the prescribed strided and
every-step scans, together with the explicit update, check, and trace-cost bounds [Magniez
et al., Proposition 1][MagniezNayakRolandSantha2011]. -/
theorem mnrs_classical_search_proposition_one :
  ∀ (δ ε : ℝ),
  0 < δ → 0 < ε →
  let t₁ : ℕ := Nat.ceil (1 / δ);
  let t₂ : ℕ := if ε ≤ 1 then Nat.ceil (4 / ε) else 0;
  let t : ℕ := t₁ * t₂;
  ∀ (X : Type*) [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (M : Finset X),
    P ∈ Matrix.rowStochastic ℝ X →
    P.IsPrimitive →
    P.IsSymm →
    mnrsAbsoluteGap P δ →
    (M.Nonempty → ε ≤ (M.card : ℝ) / (Fintype.card X : ℝ)) →
    (t₁ : ℝ) ≤ 2 / δ ∧
    (t₂ : ℝ) ≤ 5 / ε ∧
    (t : ℝ) ≤ 10 / (δ * ε) ∧
    mnrsSearchGuarantee P M t₁ t₂ (1 / 2) ∧
    mnrsSearchGuarantee P M 1 t (1 / 2) ∧
    (∀ (S U C : ℝ), 0 ≤ S → 0 ≤ U → 0 ≤ C →
      (∀ path : Fin (t₂ + 1) → X,
        mnrsTraceCost M t₁ t₂ path S U C ≤
          10 * (S + (1 / ε) * ((1 / δ) * U + C))) ∧
      (∀ path : Fin (t + 1) → X,
        mnrsTraceCost M 1 t path S U C ≤
          10 * (S + (1 / (δ * ε)) * (U + C)))) := by
  intro δ ε hδ hε
  dsimp only
  intro X _ _ _ P M hP hprim hsym hgap hM
  let a := Nat.ceil (1 / δ)
  let r := if ε ≤ 1 then Nat.ceil (4 / ε) else 0
  have hδ1 := mnrs_classical_search_proposition_one_gap_le_one P δ hgap
  have ha := mnrs_classical_search_proposition_one_stride_bounds δ hδ hδ1
  have hr := mnrs_classical_search_proposition_one_check_bounds ε hε
  have har : ((a * r : ℕ) : ℝ) ≤ 10 / (δ * ε) := by
    have hh := mul_le_mul ha.2 hr (by positivity : (0 : ℝ) ≤ r)
      (by positivity : (0 : ℝ) ≤ 2 / δ)
    have he : (2 / δ) * (5 / ε) = 10 / (δ * ε) := by ring
    simpa only [Nat.cast_mul, he] using hh
  have hc : ∀ w : EuclideanSpace ℝ X, (∑ x, w x) = 0 →
      |inner ℝ w ((P ^ a).toEuclideanLin w)| ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by
    intro w hw
    exact (mnrs_classical_search_proposition_one_mean_zero_quadratic
      P hP hprim hsym δ hgap w hw a).trans
        (mul_le_mul_of_nonneg_right
          (mnrs_classical_search_proposition_one_amplification δ hδ hδ1) (sq_nonneg _))
  have hf : M.Nonempty → mnrsOutputMass P M a r none ≤ (1 / 2 : ℝ) := by
    intro hm
    have hε1 : ε ≤ 1 := (hM hm).trans
      (mnrs_classical_search_proposition_one_density_le_one M)
    dsimp only [r]
    rw [if_pos hε1]
    exact mnrs_classical_search_proposition_one_failure_half
      P hP a (hsym.pow a) hc M hm ε hε (hM hm)
  refine ⟨ha.2, hr, har, ?_, ?_, ?_⟩
  · apply mnrs_classical_search_proposition_one_guarantee_of_failure P hP M a r (1 / 2)
    intro hm
    (convert! hf hm using 1; norm_num)
  · apply mnrs_classical_search_proposition_one_guarantee_of_failure P hP M 1 (a * r) (1 / 2)
    intro hm
    have hh := (mnrs_classical_search_proposition_one_failure_stride_comparison
      P hP M a ha.1 r).trans (hf hm)
    (convert! hh using 1; norm_num)
  · intro S U C hS hU hC
    exact mnrs_classical_search_proposition_one_cost_bounds M δ ε hδ hε a r ha.2 hr
      S U C hS hU hC

example : Proposition1WalkSpec.expected :=
  mnrs_classical_search_proposition_one

end Qatlib.Concepts.WalkSearch.MnrsAmplify
