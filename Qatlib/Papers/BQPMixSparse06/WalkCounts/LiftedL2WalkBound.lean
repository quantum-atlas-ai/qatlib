/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem2PathsReduction
public import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem3DecayIdentity
public import Qatlib.Papers.BQPMixSparse06.MainResults.Lemma3SparseConversion
public import Qatlib.Papers.BQPMixSparse06.GraphLift
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

/-!
# Operator-norm walk bounds for the signed sparse lift

The unsigned lift `blockConvert A` of a signed `{-1, 0, 1}` matrix `A` is a zero-one matrix
whose row and column sums agree with the unsigned degrees of `A`. The real Cauchy-Schwarz
argument of [JanzingWocjan2006] bounds its L2 operator norm by the common degree, and
submultiplicativity then controls every diagonal moment of `A` by `d ^ m`. This is the
degree-based growth bound for the difference-of-walk-counts problem. The degree supplies
one admissible growth parameter for the lift. A smaller parameter may suffice for a given
antisymmetric state. The constant is chosen before the moment order and vertex are quantified.

The matrix norm is the Euclidean operator norm, via the isometry to continuous linear
operators on Euclidean space.

## Main statements

* `blockConvert_l2_opNorm_le`: the L2 operator norm of `blockConvert A` is at most the common
  unsigned degree of `A`.
* `lifted_walk_diagonal_l2_bound`: a uniform positive constant bounds every diagonal moment of
  `realCast A` by `C * d ^ m`.
* `lifted_walk_diagonal_l2_bound_forall`: the explicit instance with `C = 1`.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.BQPMixSparse06.WalkCounts.LiftedL2WalkBound

open Finset Matrix
open Qatlib.Papers.BQPMixSparse06.MainResults
open Qatlib.Papers.BQPMixSparse06.GraphLift

/-- Every entry of `blockConvert A` is nonnegative. -/
lemma blockConvert_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (p q : Fin 2 × Fin N) :
    0 ≤ blockConvert A p q := by
  rcases blockConvert_entry_zero_or_one A hA p q with h | h <;> simp [h]

/-- The unsigned row sum through the lift: summing the entries of one lifted row of
`blockConvert A` counts the nonzero entries of the corresponding row of `A`. -/
lemma blockConvert_row_sum_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (s : Fin 2) (i : Fin N) :
    (∑ q : Fin 2 × Fin N, blockConvert A (s, i) q) = ∑ j : Fin N, |(A i j : ℝ)| := by
  classical
  have h1 : (∑ q : Fin 2 × Fin N, blockConvert A (s, i) q) =
      ∑ j : Fin N, ∑ t : Fin 2, blockConvert A (s, i) (t, j) :=
    Fintype.sum_prod_type_right (γ := ℝ) (fun q : Fin 2 × Fin N => blockConvert A (s, i) q)
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hAi : A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
    rcases hA i j with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hcol : (∑ t : Fin 2, gammaBlock (A i j) s t) = |(A i j : ℝ)| := by
    rcases hAi with h | h | h
    · fin_cases s <;> simp [h, gammaBlock]
    · fin_cases s <;> simp [h, gammaBlock, Matrix.one_apply]
    · fin_cases s <;> simp [h, gammaBlock]
  calc (∑ t : Fin 2, blockConvert A (s, i) (t, j)) = ∑ t : Fin 2, gammaBlock (A i j) s t := by
        refine Finset.sum_congr rfl fun t _ => ?_
        simp [blockConvert]
    _ = |(A i j : ℝ)| := hcol

/-- For a real matrix whose absolute row and column sums are at most `d`, the Euclidean operator
norm is at most `d`. This is the finite Cauchy-Schwarz argument behind the degree bounds of
[JanzingWocjan2006]. -/
theorem l2_opNorm_le_of_abs_row_col_sum_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hrow : ∀ i, ∑ j, |M i j| ≤ d) (hcol : ∀ j, ∑ i, |M i j| ≤ d) :
    ‖M‖ ≤ d := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hd fun x => ?_
  have hcoord : ∀ i : n, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M x) i = ∑ j, M i j * (x : n → ℝ) j := fun i =>
    congrFun (Matrix.ofLp_toEuclideanCLM M x) i
  have hnorm : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M x‖ ^ 2 = ∑ i, (∑ j, M i j * (x : n → ℝ) j) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hcoord i, Real.norm_eq_abs, sq_abs]
  have hcs : ∀ i : n, (∑ j, M i j * (x : n → ℝ) j) ^ 2 ≤
      d * ∑ j, |M i j| * ((x : n → ℝ) j) ^ 2 := by
    intro i
    have habs : (∑ j, M i j * (x : n → ℝ) j) ^ 2 ≤
        (∑ j, |M i j| * |(x : n → ℝ) j|) ^ 2 := by
      have hle : abs (∑ j, M i j * (x : n → ℝ) j) ≤ ∑ j, |M i j| * |(x : n → ℝ) j| :=
        le_trans (Finset.abs_sum_le_sum_abs (fun j => M i j * (x : n → ℝ) j) Finset.univ)
          (Finset.sum_le_sum fun j _ => le_of_eq (abs_mul (M i j) ((x : n → ℝ) j)))
      have hnn : 0 ≤ ∑ j, |M i j| * abs ((x : n → ℝ) j) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hneg : -(∑ j, |M i j| * |(x : n → ℝ) j|) ≤ ∑ j, M i j * (x : n → ℝ) j :=
        le_trans (neg_le_neg hle) (neg_abs_le _)
      have hle' : abs (∑ j, M i j * (x : n → ℝ) j) ≤
          abs (∑ j, |M i j| * abs ((x : n → ℝ) j)) := by
        rw [abs_of_nonneg hnn]
        exact abs_le.mpr ⟨hneg, le_trans (le_abs_self _) hle⟩
      exact sq_le_sq.mpr hle'
    have hsqrt : (∑ j, |M i j| * |(x : n → ℝ) j|) ^ 2 ≤
        (∑ j, |M i j|) * ∑ j, |M i j| * ((x : n → ℝ) j) ^ 2 := by
      have hcs' := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => Real.sqrt (|M i j|)) (fun j => Real.sqrt (|M i j|) * |(x : n → ℝ) j|)
      have hfsq : (∑ j, Real.sqrt (|M i j|) ^ 2) = ∑ j, |M i j| :=
        Finset.sum_congr rfl fun j _ => Real.sq_sqrt (abs_nonneg _)
      have hgsq : (∑ j, (Real.sqrt (|M i j|) * |(x : n → ℝ) j|) ^ 2) =
          ∑ j, |M i j| * ((x : n → ℝ) j) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
      have hfg : (∑ j, Real.sqrt (|M i j|) * (Real.sqrt (|M i j|) * |(x : n → ℝ) j|)) =
          ∑ j, |M i j| * |(x : n → ℝ) j| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
      rw [hfsq, hgsq, hfg] at hcs'
      exact hcs'
    calc (∑ j, M i j * (x : n → ℝ) j) ^ 2
        ≤ (∑ j, |M i j| * |(x : n → ℝ) j|) ^ 2 := habs
      _ ≤ (∑ j, |M i j|) * ∑ j, |M i j| * ((x : n → ℝ) j) ^ 2 := hsqrt
      _ ≤ d * ∑ j, |M i j| * ((x : n → ℝ) j) ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow i)
            (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have hsq : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M x‖ ^ 2 ≤ (d * ‖x‖) ^ 2 := by
    calc ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M x‖ ^ 2
        = ∑ i, (∑ j, M i j * (x : n → ℝ) j) ^ 2 := hnorm
      _ ≤ ∑ i, d * ∑ j, |M i j| * ((x : n → ℝ) j) ^ 2 :=
          Finset.sum_le_sum fun i _ => hcs i
      _ = ∑ i, ∑ j, d * (|M i j| * ((x : n → ℝ) j) ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, d * (|M i j| * ((x : n → ℝ) j) ^ 2) := Finset.sum_comm
      _ = d * ∑ j, (∑ i, |M i j|) * ((x : n → ℝ) j) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
      _ ≤ d * ∑ j, d * ((x : n → ℝ) j) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)) hd
      _ = d * (d * ∑ j, ((x : n → ℝ) j) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = d * (d * ‖x‖ ^ 2) := by
          rw [EuclideanSpace.norm_sq_eq]
          congr 1
          congr 1
          exact Finset.sum_congr rfl fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]
      _ = (d * ‖x‖) ^ 2 := by ring
  have hd' : 0 ≤ d * ‖x‖ := mul_nonneg hd (norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) hd').mp hsq

/-- Powers of a real matrix are norm-submultiplicative in the Euclidean operator norm. -/
lemma l2_opNorm_pow_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (m : ℕ) : ‖M ^ m‖ ≤ ‖M‖ ^ m := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, ← Matrix.l2_opNorm_toEuclideanCLM]
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
      have h1 : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (1 : Matrix n n ℝ) = 1 := map_one _
      rw [h1]
      simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact le_trans (Matrix.l2_opNorm_mul _ _) (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- The Euclidean-space norm of the antisymmetric unit state `psiMinus j` is one. -/
lemma euclideanNorm_psiMinus {N : ℕ} (j : Fin N) :
    ‖(WithLp.toLp 2 (psiMinus j) : EuclideanSpace ℝ (Fin 2 × Fin N))‖ = 1 := by
  have hsq : ‖(WithLp.toLp 2 (psiMinus j) : EuclideanSpace ℝ (Fin 2 × Fin N))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hdot : dot (psiMinus j) (psiMinus j) = 1 := dot_psiMinus_self j
    unfold dot at hdot
    calc (∑ i, ‖(WithLp.toLp 2 (psiMinus j) : EuclideanSpace ℝ (Fin 2 × Fin N)) i‖ ^ 2)
        = ∑ i, psiMinus j i * psiMinus j i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
          ring
      _ = 1 := hdot
  have hnonneg : 0 ≤ ‖(WithLp.toLp 2 (psiMinus j) : EuclideanSpace ℝ (Fin 2 × Fin N))‖ :=
    norm_nonneg _
  calc ‖(WithLp.toLp 2 (psiMinus j) : EuclideanSpace ℝ (Fin 2 × Fin N))‖
      = Real.sqrt (‖(WithLp.toLp 2 (psiMinus j) : EuclideanSpace ℝ (Fin 2 × Fin N))‖ ^ 2) :=
        (Real.sqrt_sq hnonneg).symm
    _ = Real.sqrt 1 := by rw [hsq]
    _ = 1 := Real.sqrt_one

/-- The Euclidean operator norm of `blockConvert A` is at most the common unsigned degree `d`
of `A` [JanzingWocjan2006]. -/
theorem blockConvert_l2_opNorm_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hAsym : ∀ i j, A i j = A j i) (d : ℝ) (hd : 0 ≤ d)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) :
    ‖blockConvert A‖ ≤ d := by
  classical
  refine l2_opNorm_le_of_abs_row_col_sum_le (blockConvert A) d hd ?_ ?_
  · rintro ⟨s, i⟩
    calc (∑ q : Fin 2 × Fin N, |blockConvert A (s, i) q|)
        = ∑ q : Fin 2 × Fin N, blockConvert A (s, i) q :=
          Finset.sum_congr rfl fun q _ =>
            abs_of_nonneg (blockConvert_nonneg A hA (s, i) q)
      _ = ∑ j : Fin N, |(A i j : ℝ)| := blockConvert_row_sum_eq A hA s i
      _ ≤ d := le_of_eq (hrow i)
  · rintro ⟨t, j⟩
    have hcolA : ∑ i : Fin N, |(A i j : ℝ)| = d := by
      calc (∑ i : Fin N, |(A i j : ℝ)|) = ∑ i : Fin N, |(A j i : ℝ)| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hAsym i j]
      _ = d := hrow j
    calc (∑ p : Fin 2 × Fin N, |blockConvert A p (t, j)|)
        = ∑ p : Fin 2 × Fin N, blockConvert A p (t, j) :=
          Finset.sum_congr rfl fun p _ =>
            abs_of_nonneg (blockConvert_nonneg A hA p (t, j))
      _ = ∑ i : Fin N, |(A i j : ℝ)| := by
        have h1 : (∑ p : Fin 2 × Fin N, blockConvert A p (t, j)) =
            ∑ i : Fin N, ∑ s : Fin 2, blockConvert A (s, i) (t, j) :=
          Fintype.sum_prod_type_right (γ := ℝ) (fun p : Fin 2 × Fin N => blockConvert A p (t, j))
        rw [h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hAi : A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
          rcases hA i j with h | h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        have hcol : (∑ s : Fin 2, gammaBlock (A i j) s t) = |(A i j : ℝ)| := by
          rcases hAi with h | h | h
          · fin_cases t <;> simp [h, gammaBlock]
          · fin_cases t <;> simp [h, gammaBlock, Matrix.one_apply]
          · fin_cases t <;> simp [h, gammaBlock]
        calc (∑ s : Fin 2, blockConvert A (s, i) (t, j)) = ∑ s : Fin 2, gammaBlock (A i j) s t := by
              refine Finset.sum_congr rfl fun s _ => ?_
              simp [blockConvert]
          _ = |(A i j : ℝ)| := hcol
      _ ≤ d := le_of_eq hcolA

/-- The diagonal moments of the signed matrix are controlled by the Euclidean operator norm of
its unsigned lift: `|((realCast A) ^ m) j j|` is at most `‖blockConvert A‖ ^ m`. -/
theorem abs_pow_diagonal_le_opNorm_pow {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (m : ℕ) (j : Fin N) :
    |((realCast A) ^ m) j j| ≤ ‖blockConvert A‖ ^ m := by
  rw [eq12_diagonal_entry A hA m j]
  set ψ : EuclideanSpace ℝ (Fin 2 × Fin N) := WithLp.toLp 2 (psiMinus j) with hψ
  set M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ := (blockConvert A) ^ m with hM
  have hMc : ∀ i : Fin 2 × Fin N, (M *ᵥ psiMinus j) i = (Matrix.toEuclideanCLM (n := Fin 2 × Fin N) (𝕜 := ℝ) M ψ) i := fun i =>
    congrFun (Matrix.ofLp_toEuclideanCLM M ψ) i
  have hcs : |dot (psiMinus j) (M *ᵥ psiMinus j)| ≤
      Real.sqrt (∑ i, (psiMinus j i) ^ 2) * Real.sqrt (∑ i, ((M *ᵥ psiMinus j) i) ^ 2) := by
    unfold dot
    have habs : abs (∑ i, psiMinus j i * (M *ᵥ psiMinus j) i) ≤
        ∑ i, |psiMinus j i| * |(M *ᵥ psiMinus j) i| :=
      le_trans (Finset.abs_sum_le_sum_abs (fun i => psiMinus j i * (M *ᵥ psiMinus j) i) Finset.univ)
        (Finset.sum_le_sum fun i _ => le_of_eq (abs_mul (psiMinus j i) ((M *ᵥ psiMinus j) i)))
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => |psiMinus j i|) (fun i => |(M *ᵥ psiMinus j) i|)
    have hsqabs : (∑ i, |psiMinus j i| ^ 2) = ∑ i, (psiMinus j i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => sq_abs _
    have hsqabs2 : (∑ i, |(M *ᵥ psiMinus j) i| ^ 2) = ∑ i, ((M *ᵥ psiMinus j) i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => sq_abs _
    rw [hsqabs, hsqabs2] at hcs0
    have h3 : (∑ i, |psiMinus j i| * |(M *ᵥ psiMinus j) i|) ≤
        Real.sqrt ((∑ i, (psiMinus j i) ^ 2) * (∑ i, ((M *ᵥ psiMinus j) i) ^ 2)) :=
      Real.le_sqrt_of_sq_le hcs0
    calc |∑ i, psiMinus j i * (M *ᵥ psiMinus j) i|
        ≤ ∑ i, |psiMinus j i| * |(M *ᵥ psiMinus j) i| := habs
      _ ≤ Real.sqrt ((∑ i, (psiMinus j i) ^ 2) * (∑ i, ((M *ᵥ psiMinus j) i) ^ 2)) := h3
      _ = Real.sqrt (∑ i, (psiMinus j i) ^ 2) * Real.sqrt (∑ i, ((M *ᵥ psiMinus j) i) ^ 2) :=
          Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _) _
  have hψnorm : Real.sqrt (∑ i, (psiMinus j i) ^ 2) = ‖ψ‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Real.norm_eq_abs, sq_abs, hψ, WithLp.ofLp_toLp]
  have hMnorm : Real.sqrt (∑ i, ((M *ᵥ psiMinus j) i) ^ 2) = ‖Matrix.toEuclideanCLM (n := Fin 2 × Fin N) (𝕜 := ℝ) M ψ‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [hMc, Real.norm_eq_abs, sq_abs]
  rw [hψnorm, hMnorm] at hcs
  calc |dot (psiMinus j) (M *ᵥ psiMinus j)|
      ≤ ‖ψ‖ * ‖Matrix.toEuclideanCLM (n := Fin 2 × Fin N) (𝕜 := ℝ) M ψ‖ := hcs
    _ ≤ ‖ψ‖ * (‖Matrix.toEuclideanCLM (n := Fin 2 × Fin N) (𝕜 := ℝ) M‖ * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖(blockConvert A) ^ m‖ := by
        simp only [Matrix.l2_opNorm_toEuclideanCLM, hψ, euclideanNorm_psiMinus, one_mul, mul_one,
          hM]
    _ ≤ ‖blockConvert A‖ ^ m := l2_opNorm_pow_le _ _

/-- Uniform walk-bound statement: there is a positive constant, chosen before the moment order
and the vertex are quantified, bounding every diagonal moment of `realCast A` by `C * d ^ m`. -/
theorem lifted_walk_diagonal_l2_bound {N : ℕ} [Nonempty (Fin N)]
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hAsym : ∀ i j, A i j = A j i) (d : ℝ) (hd : 0 < d)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ j : Fin N, |((realCast A) ^ m) j j| ≤ C * d ^ m := by
  refine ⟨1, by norm_num, fun m j => ?_⟩
  calc |((realCast A) ^ m) j j|
      ≤ ‖blockConvert A‖ ^ m := abs_pow_diagonal_le_opNorm_pow A hA m j
    _ ≤ d ^ m := pow_le_pow_left₀ (norm_nonneg _)
          (blockConvert_l2_opNorm_le A hA hAsym d hd.le hrow) m
    _ = 1 * d ^ m := (one_mul _).symm

/-- The explicit bound behind `lifted_walk_diagonal_l2_bound`: every diagonal moment is at most
`d ^ m`. -/
theorem lifted_walk_diagonal_l2_bound_forall {N : ℕ} [Nonempty (Fin N)]
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hAsym : ∀ i j, A i j = A j i) (d : ℝ) (hd : 0 < d)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) :
    ∀ m : ℕ, ∀ j : Fin N, |((realCast A) ^ m) j j| ≤ d ^ m := by
  intro m j
  calc |((realCast A) ^ m) j j|
      ≤ ‖blockConvert A‖ ^ m := abs_pow_diagonal_le_opNorm_pow A hA m j
    _ ≤ d ^ m := pow_le_pow_left₀ (norm_nonneg _)
          (blockConvert_l2_opNorm_le A hA hAsym d hd.le hrow) m

/-- The common degree is an admissible growth parameter for the paired walk-count differences
of the lift [JanzingWocjan2006], Theorem 2. -/
theorem lifted_walk_difference_le_degree_pow {N : ℕ} [Nonempty (Fin N)]
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hAsym : ∀ i j, A i j = A j i) (d : ℝ) (hd : 0 < d)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) :
    ∀ m : ℕ, ∀ j : Fin N, |doubledPathDiff ((blockConvert A) ^ m) j| ≤ d ^ m := by
  intro m j
  rw [← theorem2_path_difference A hA hAsym m j]
  exact lifted_walk_diagonal_l2_bound_forall A hA hAsym d hd hrow m j

end Qatlib.Papers.BQPMixSparse06.WalkCounts.LiftedL2WalkBound
