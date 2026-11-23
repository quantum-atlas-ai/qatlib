/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BQPMixSparse06.WalkCounts.LiftedL2WalkBound
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic

@[expose] public section

/-!
# Matrix-exponential heat kernel of the signed sparse lift

This module closes part of the matrix-exponential gap left by the abstract heat-kernel
estimates of [JanzingWocjan2006]. For the unsigned lift `blockConvert A` of a signed
`{-1, 0, 1}` matrix `A` with constant unsigned degree `d`, every row of
`NormedSpace.exp (t • blockConvert A)` sums to `Real.exp (t * d)`. For nonnegative time,
the entries are nonnegative, so the heat kernel
`NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d))` has entries between zero and one.
Its expectation in the antisymmetric state `psiMinus j` equals the diagonal entry of
`Real.exp (-(t * d)) • NormedSpace.exp (t • realCast A)` at the original vertex `j`.

Deriving an exponential decay rate requires control of the spectral weights of the
antisymmetric state.

## Main statements

* `lifted_heatKernel_exp_nonneg`: entries of the lifted heat kernel are nonnegative for
  nonnegative times.
* `lifted_heatKernel_exp_bound`: a uniform positive constant bounds all entries of the lifted
  heat kernel for nonnegative times.
* `lifted_heatKernel_diag_bridge`: the antisymmetric-state heat-kernel expectation equals the
  signed heat-semigroup entry at the original vertex.
* `lifted_heatKernel_difference`: the diagonal-minus-off-diagonal heat-kernel difference
  equals that same signed semigroup entry, as in [JanzingWocjan2006], Equation (15).

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults.LiftedHeatKernel

open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.BQPMixSparse06.MainResults
open Qatlib.Papers.BQPMixSparse06.GraphLift
open Qatlib.Papers.BQPMixSparse06.WalkCounts.LiftedL2WalkBound
  (blockConvert_nonneg blockConvert_row_sum_eq)

/-- Scalar scaling factors out of the paper's `dot` product. -/
lemma dot_smul {ι : Type*} [Fintype ι] (u v : ι → ℝ) (c : ℝ) :
    dot u (c • v) = c * dot u v := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- The exponential series `∑' k, (k !)⁻¹ x ^ k` evaluates to `Real.exp x`. -/
lemma tsum_inv_fact_mul_eq_exp (x : ℝ) :
    ∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) * x ^ k = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ]
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) x
  rw [← h.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [smul_eq_mul]

/-- The matrix exponential is the convergent entrywise power series. -/
lemma exp_eq_tsum_matrix {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    NormedSpace.exp A = ∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) • A ^ k := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := Matrix n n ℝ) A
  rw [← h.tsum_eq]

/-- Entry evaluation of the matrix exponential as a convergent entrywise series. -/
lemma exp_apply' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (p q : n) :
    (NormedSpace.exp A) p q = ∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • A ^ k) p q) := by
  have h1 : (∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) • A ^ k) p =
      ∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • A ^ k) p) :=
    Pi.tsum_apply (NormedSpace.expSeries_summable' A)
  have h2 : (∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • A ^ k) p)) q =
      ∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • A ^ k) p q) :=
    Pi.tsum_apply ((Pi.summable.1 (NormedSpace.expSeries_summable' A)) p)
  rw [exp_eq_tsum_matrix, h1, h2]

/-- Multiplication of a convergent matrix series by a vector distributes over the series. -/
lemma mulVec_tsum {m : Type*} [Fintype m] {n : Type*} [Fintype n]
    (f : ℕ → Matrix m n ℝ) (v : n → ℝ) (hf : Summable f) :
    (∑' k, f k) *ᵥ v = ∑' k, f k *ᵥ v := by
  have hcont : ∀ i : m, Continuous fun M : Matrix m n ℝ => (M *ᵥ v) i := fun i => by
    have hrw : (fun M : Matrix m n ℝ => (M *ᵥ v) i) =
        (fun M : Matrix m n ℝ => ∑ j : n, M i j * v j) := by
      funext M
      simp [Matrix.mulVec, dotProduct]
    rw [hrw]
    refine continuous_finsetSum Finset.univ fun j _ => ?_
    have h1 : Continuous fun g : n → ℝ => g j := continuous_apply j
    have h2 : Continuous fun M : Matrix m n ℝ => M i := continuous_apply i
    exact (h1.comp h2).mul continuous_const
  let g : Matrix m n ℝ →L[ℝ] (m → ℝ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M₁ M₂ => Matrix.add_mulVec M₁ M₂ v
      map_smul' := fun c M => Matrix.smul_mulVec c M v
      cont := continuous_pi hcont }
  exact g.map_tsum hf

/-- A convergent matrix series stays convergent after multiplying every term by a fixed
vector. -/
lemma summable_mulVec {m : Type*} [Fintype m] {n : Type*} [Fintype n]
    (f : ℕ → Matrix m n ℝ) (v : n → ℝ) (hf : Summable f) :
    Summable fun k => f k *ᵥ v := by
  classical
  have hf1 : ∀ i : m, Summable fun k => f k i := Pi.summable.1 hf
  have hf2 : ∀ i : m, ∀ j : n, Summable fun k => f k i j := fun i => Pi.summable.1 (hf1 i)
  rw [Pi.summable]
  intro i
  have key : ∀ s : Finset n, Summable fun k => ∑ j ∈ s, f k i j * v j := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert a s' ha ih =>
        simpa [Finset.sum_insert ha, add_comm] using
          ih.add ((hf2 i a).mul_right (v a))
  simpa [Matrix.mulVec, dotProduct] using key Finset.univ

/-- On the constant-one vector, the lift `blockConvert A` acts as the unsigned degree. -/
lemma blockConvert_mulVec_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (d : ℝ)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) :
    blockConvert A *ᵥ (1 : Fin 2 × Fin N → ℝ) = d • (1 : Fin 2 × Fin N → ℝ) := by
  funext p
  obtain ⟨s, i⟩ := p
  calc (blockConvert A *ᵥ (1 : Fin 2 × Fin N → ℝ)) (s, i)
      = ∑ q : Fin 2 × Fin N, blockConvert A (s, i) q := by
        simp [Matrix.mulVec, dotProduct]
    _ = ∑ j : Fin N, |(A i j : ℝ)| := blockConvert_row_sum_eq A hA s i
    _ = d := hrow i
    _ = (d • (1 : Fin 2 × Fin N → ℝ)) (s, i) := by simp [Pi.smul_apply]

/-- Every power of the lift `blockConvert A` preserves the constant-one eigenvector with
eigenvalue the degree. -/
lemma blockConvert_pow_mulVec_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (d : ℝ)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) (n : ℕ) :
    (blockConvert A) ^ n *ᵥ (1 : Fin 2 × Fin N → ℝ) =
      (d ^ n) • (1 : Fin 2 × Fin N → ℝ) := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_mulVec, pow_zero, one_smul]
  | succ n ih =>
      calc (blockConvert A) ^ (n + 1) *ᵥ (1 : Fin 2 × Fin N → ℝ)
          = ((blockConvert A) ^ n * blockConvert A) *ᵥ
              (1 : Fin 2 × Fin N → ℝ) := by rw [pow_succ]
        _ = (blockConvert A) ^ n *ᵥ (blockConvert A *ᵥ (1 : Fin 2 × Fin N → ℝ)) := by
            rw [Matrix.mulVec_mulVec]
        _ = (blockConvert A) ^ n *ᵥ (d • (1 : Fin 2 × Fin N → ℝ)) :=
            by rw [blockConvert_mulVec_one A hA d hrow]
        _ = d • ((blockConvert A) ^ n *ᵥ (1 : Fin 2 × Fin N → ℝ)) :=
            by rw [Matrix.mulVec_smul]
        _ = d • ((d ^ n) • (1 : Fin 2 × Fin N → ℝ)) := by rw [ih]
        _ = (d ^ (n + 1)) • (1 : Fin 2 × Fin N → ℝ) := by
            rw [pow_succ', mul_smul, smul_comm]

/-- The exponential `NormedSpace.exp (t • blockConvert A)` fixes the constant-one vector up to the
scalar factor `Real.exp (t * d)`. -/
lemma exp_smul_blockConvert_mulVec_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (d : ℝ)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) (t : ℝ) :
    NormedSpace.exp (t • blockConvert A) *ᵥ (1 : Fin 2 × Fin N → ℝ) =
      Real.exp (t * d) • (1 : Fin 2 × Fin N → ℝ) := by
  rw [exp_eq_tsum_matrix]
  rw [mulVec_tsum _ _ (NormedSpace.expSeries_summable' (t • blockConvert A))]
  funext p
  rw [Pi.tsum_apply (summable_mulVec _ _ (NormedSpace.expSeries_summable' (t • blockConvert A)))]
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  have hterm : ∀ k : ℕ,
      ((((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ (1 : Fin 2 × Fin N → ℝ)) p =
        ((Nat.factorial k : ℝ)⁻¹) * (t * d) ^ k := by
    intro k
    obtain ⟨s, i⟩ := p
    calc ((((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ (1 : Fin 2 × Fin N → ℝ)) (s, i)
        = ((Nat.factorial k : ℝ)⁻¹) * (((t • blockConvert A) ^ k) *ᵥ (1 : Fin 2 × Fin N → ℝ)) (s, i) := by
          rw [smul_mulVec, Pi.smul_apply, smul_eq_mul]
      _ = ((Nat.factorial k : ℝ)⁻¹) * (t ^ k * d ^ k) := by
          congr 1
          rw [smul_pow, smul_mulVec, blockConvert_pow_mulVec_one A hA d hrow k]
          simp [Pi.smul_apply, smul_eq_mul]
      _ = ((Nat.factorial k : ℝ)⁻¹) * (t * d) ^ k := by rw [mul_pow]
  calc (∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ (1 : Fin 2 × Fin N → ℝ)) p)
      = ∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) * (t * d) ^ k := tsum_congr hterm
    _ = Real.exp (t * d) := tsum_inv_fact_mul_eq_exp _

/-- Every power of the lift `blockConvert A` is entrywise nonnegative. -/
lemma blockConvert_pow_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (n : ℕ) (p q : Fin 2 × Fin N) :
    0 ≤ ((blockConvert A) ^ n) p q := by
  induction n generalizing p q with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (ih p k) (blockConvert_nonneg A hA k q)

/-- The matrix exponential `NormedSpace.exp (t • blockConvert A)` is entrywise nonnegative for
nonnegative `t`. -/
theorem exp_smul_blockConvert_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (t : ℝ) (ht : 0 ≤ t)
    (p q : Fin 2 × Fin N) :
    0 ≤ NormedSpace.exp (t • blockConvert A) p q := by
  rw [exp_apply']
  refine tsum_nonneg fun k => ?_
  rw [smul_pow, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_nonneg (by positivity)
    (mul_nonneg (pow_nonneg ht k) (blockConvert_pow_nonneg A hA k p q))

/-- Each entry of `NormedSpace.exp (t • blockConvert A)` is at most the corresponding row sum
`Real.exp (t * d)`. -/
theorem exp_smul_blockConvert_le_exp {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (d : ℝ)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) (t : ℝ) (ht : 0 ≤ t) (p q : Fin 2 × Fin N) :
    NormedSpace.exp (t • blockConvert A) p q ≤ Real.exp (t * d) := by
  have hrowsum :
      (∑ q' : Fin 2 × Fin N, NormedSpace.exp (t • blockConvert A) p q') = Real.exp (t * d) := by
    have h := congrFun (exp_smul_blockConvert_mulVec_one A hA d hrow t) p
    rw [Matrix.mulVec, dotProduct] at h
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
    exact h
  calc NormedSpace.exp (t • blockConvert A) p q
      ≤ ∑ q' ∈ Finset.univ, NormedSpace.exp (t • blockConvert A) p q' :=
        Finset.single_le_sum (fun q' _ => exp_smul_blockConvert_nonneg A hA t ht p q')
          (Finset.mem_univ q)
    _ = Real.exp (t * d) := hrowsum

/-- The heat kernel of the lifted Laplacian factors as `Real.exp (-(t * d)) • NormedSpace.exp (t •
blockConvert A)` [JanzingWocjan2006]. -/
theorem exp_neg_smul_graphLaplacian_blockConvert {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (d : ℝ) (t : ℝ) :
    NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d)) =
      Real.exp (-(t * d)) • NormedSpace.exp (t • blockConvert A) := by
  have hone : NormedSpace.exp ((-(t * d)) • (1 : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)) =
      Real.exp (-(t * d)) • (1 : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Pi.exp_def]
    have hc : ((fun _ : Fin 2 × Fin N => NormedSpace.exp (-(t * d))) :
        Fin 2 × Fin N → ℝ) = fun _ => Real.exp (-(t * d)) := by
      funext i
      rw [Real.exp_eq_exp_ℝ]
    rw [hc, ← Matrix.smul_one_eq_diagonal]
  have hdecomp : -(t • graphLaplacian (blockConvert A) d) =
      t • blockConvert A + (-(t * d)) • (1 : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) := by
    ext p q
    simp only [graphLaplacian, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.neg_apply, smul_eq_mul]
    by_cases hpq : p = q <;> ring
  have hcomm : Commute (t • blockConvert A)
      ((-(t * d)) • (1 : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)) := by
    rw [commute_iff_eq]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm, hone, Matrix.mul_smul, Matrix.mul_one]

/-- The exponential `NormedSpace.exp (t • blockConvert A)` preserves the antisymmetric sector: on
lifts `liftVec phiMinus v` it acts exactly like `NormedSpace.exp (t • realCast A)` on `v`
[JanzingWocjan2006]. -/
theorem exp_smul_blockConvert_mulVec_lift {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (t : ℝ) (v : Fin N → ℝ) :
    NormedSpace.exp (t • blockConvert A) *ᵥ liftVec phiMinus v =
      liftVec phiMinus (NormedSpace.exp (t • realCast A) *ᵥ v) := by
  rw [exp_eq_tsum_matrix, exp_eq_tsum_matrix]
  have hA1 : (∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k) *ᵥ v =
      ∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k) *ᵥ v) :=
    mulVec_tsum _ _ (NormedSpace.expSeries_summable' (t • realCast A))
  have hA2 : (∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ liftVec phiMinus v =
      ∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ liftVec phiMinus v) :=
    mulVec_tsum _ _ (NormedSpace.expSeries_summable' (t • blockConvert A))
  rw [hA2, hA1]
  funext p
  obtain ⟨s, i⟩ := p
  have hB1 : (∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ liftVec phiMinus v)) (s, i) =
      ∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ liftVec phiMinus v) (s, i) :=
    Pi.tsum_apply (summable_mulVec (fun k : ℕ => ((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k)
      (liftVec phiMinus v) (NormedSpace.expSeries_summable' (t • blockConvert A)))
  have hB2 : (∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k) *ᵥ v)) i =
      ∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k) *ᵥ v) i :=
    Pi.tsum_apply (summable_mulVec (fun k : ℕ => ((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k)
      v (NormedSpace.expSeries_summable' (t • realCast A)))
  rw [hB1]
  rw [show liftVec phiMinus (∑' k : ℕ,
        ((((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k) *ᵥ v)) (s, i) =
      (∑' k : ℕ, ((((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k) *ᵥ v)) i * phiMinus s
    from rfl]
  rw [hB2]
  rw [← tsum_mul_right]
  refine tsum_congr fun k => ?_
  calc (((((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) *ᵥ liftVec phiMinus v)) (s, i)
      = ((Nat.factorial k : ℝ)⁻¹) * ((((t • blockConvert A) ^ k) *ᵥ liftVec phiMinus v)) (s, i) := by
        rw [smul_mulVec, Pi.smul_apply, smul_eq_mul]
    _ = ((Nat.factorial k : ℝ)⁻¹) * (t ^ k * (((realCast A) ^ k) *ᵥ v) i * phiMinus s) := by
        rw [smul_pow, smul_mulVec, blockConvert_pow_mulVec_lift A hA k v, Pi.smul_apply,
          smul_eq_mul]
        simp only [liftVec]
        ring
    _ = (((Nat.factorial k : ℝ)⁻¹) * t ^ k * (((realCast A) ^ k) *ᵥ v) i) * phiMinus s := by ring
    _ = (((((Nat.factorial k : ℝ)⁻¹) • (t • realCast A) ^ k) *ᵥ v)) i * phiMinus s := by
        simp only [smul_pow, smul_mulVec, Pi.smul_apply, smul_eq_mul]
        ring

/-- Entries of the lifted heat kernel `NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d))`
are nonnegative for nonnegative times. -/
theorem lifted_heatKernel_exp_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (d : ℝ)
    (t : ℝ) (ht : 0 ≤ t) (p q : Fin 2 × Fin N) :
    0 ≤ (NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d))) p q := by
  rw [exp_neg_smul_graphLaplacian_blockConvert, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le (exp_smul_blockConvert_nonneg A hA t ht p q)

/-- A uniform positive constant, chosen before the time and the entries are quantified, bounds
every entry of the lifted heat kernel for nonnegative times. -/
theorem lifted_heatKernel_exp_bound {N : ℕ} [Nonempty (Fin N)]
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (d : ℝ)
    (hrow : ∀ i, ∑ j, |(A i j : ℝ)| = d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ p q : Fin 2 × Fin N,
      |(NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d))) p q| ≤ C := by
  refine ⟨1, by norm_num, fun t ht p q => ?_⟩
  have hnonneg : 0 ≤ (NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d))) p q :=
    lifted_heatKernel_exp_nonneg A hA d t ht p q
  rw [abs_of_nonneg hnonneg]
  calc (NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d))) p q
      = Real.exp (-(t * d)) * NormedSpace.exp (t • blockConvert A) p q := by
        rw [exp_neg_smul_graphLaplacian_blockConvert, Matrix.smul_apply, smul_eq_mul]
    _ ≤ Real.exp (-(t * d)) * Real.exp (t * d) :=
        mul_le_mul_of_nonneg_left (exp_smul_blockConvert_le_exp A hA d hrow t ht p q)
          (Real.exp_pos _).le
    _ = Real.exp (-(t * d) + t * d) := by rw [Real.exp_add]
    _ = 1 := by rw [neg_add_cancel, Real.exp_zero]

/-- The antisymmetric-state heat-kernel expectation on the lift equals the signed heat
semigroup entry at the original vertex: the lifted heat kernel transports to
`Real.exp (-(t * d)) • NormedSpace.exp (t • realCast A)` on the signed matrix
[JanzingWocjan2006]. -/
theorem lifted_heatKernel_diag_bridge {N : ℕ} [Nonempty (Fin N)]
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (d : ℝ) (t : ℝ) (j : Fin N) :
    dot (psiMinus j) (NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d)) *ᵥ psiMinus j) =
      Real.exp (-(t * d)) * (NormedSpace.exp (t • realCast A)) j j := by
  rw [exp_neg_smul_graphLaplacian_blockConvert, smul_mulVec, dot_smul]
  have h2 : dot (liftVec phiMinus (Pi.single j (1 : ℝ)))
      (liftVec phiMinus (NormedSpace.exp (t • realCast A) *ᵥ Pi.single j (1 : ℝ))) =
      (NormedSpace.exp (t • realCast A) *ᵥ Pi.single j (1 : ℝ)) j := dot_psiMinus_lift _ j
  rw [← exp_smul_blockConvert_mulVec_lift A hA t (Pi.single j (1 : ℝ))] at h2
  rw [show psiMinus j = liftVec phiMinus (Pi.single j (1 : ℝ)) from rfl]
  rw [h2, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

/-- The heat-kernel difference for the two lifts of a vertex equals the diagonal entry of
the signed heat semigroup [JanzingWocjan2006], Equation (15). -/
theorem lifted_heatKernel_difference {N : ℕ} [Nonempty (Fin N)]
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hAsym : ∀ i j, A i j = A j i) (d t : ℝ) (j : Fin N) :
    cqrDoubled (NormedSpace.exp (-(t • graphLaplacian (blockConvert A) d))) j =
      Real.exp (-(t * d)) * (NormedSpace.exp (t • realCast A)) j j := by
  rw [exp_neg_smul_graphLaplacian_blockConvert, cqrDoubled]
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  apply congrArg (Real.exp (-(t * d)) * ·)
  rw [exp_apply', exp_apply', exp_apply']
  have hs (q : Fin 2 × Fin N) :
      Summable (fun k : ℕ =>
        (((Nat.factorial k : ℝ)⁻¹) • (t • blockConvert A) ^ k) (0, j) q) :=
    Pi.summable.1 ((Pi.summable.1 (NormedSpace.expSeries_summable'
      (t • blockConvert A))) (0, j)) q
  rw [← (hs (0, j)).tsum_sub (hs (1, j))]
  refine tsum_congr fun k => ?_
  simp only [smul_pow, Matrix.smul_apply, smul_eq_mul, ← mul_sub,
    theorem2_path_difference A hA hAsym k j,
    doubledPathDiff]

end Qatlib.Papers.BQPMixSparse06.MainResults.LiftedHeatKernel
