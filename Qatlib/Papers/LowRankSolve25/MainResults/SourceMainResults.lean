/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option backward.isDefEq.respectTransparency false

/-!
# LowRankSolve25 — paper-layer Lean coverage (`MainResults`)

Fixed paper: **arXiv:2508.13108v1** (2025-08-18),
*A simple analysis of a quantum-inspired algorithm for solving low-rank linear systems*
(Chen, Kim, Ray, Chakrabarti, Herman, Kumar).

This single paper module covers all ten active claims (c001-c010):

* c001 — main result, abstract / (1.3), pp.1-6 (`main_result`);
* c002 — Lemma 1.4, p.6: sparsity and generation cost
  (`lemma14_sparsity`, `lemma14_sample_count`, `lemma14_cost`);
* c003 — Theorem 1.6, p.6-9 (`theorem16_expected_error`);
* c004 — Theorem 1.7, p.7/11 (`theorem17_phi_bound`);
* c005 — Lemma 2.1, p.7/16 (`lemma21_first_moment`, `lemma21_second_moment`);
* c006 — Lemma 2.2, p.7/16-17 (`lemma22_conditional_unbiased`,
  `lemma22_conditional_second_moment`);
* c007 — Lemma 2.3, p.10/17-18 (`lemma23_Du_second_moment`);
* c008 — Lemma 2.4, p.10/18 (`lemma24_Dv_second_moment`);
* c009 — Lemma 2.5, p.10/11 (`lemma25_alpha_squared_bound`);
* c010 — Lemma A.1, p.16 (`lemmaA1_sample_mean_second_moment`).

Reused library vocabulary (fully qualified names):
`Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared`,
`sketchSquared`, `sketchProduct`, `sketchMeanMatrix`, `sketchSampleMatrix`,
`sketchProduct_unbiased_mean`, `sketchMean_eq_product`,
`sketchRowSquared_eq_zero_entry`, `sketch_frobenius_norm_sq`;
probability backbone `Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist`
(`prob`, `nonneg`, `sum_one`, `expect`, `probOf`, `avg`, `variance`, `expect_avg`,
`expect_avg_sub_sq`, `sum_probOf`, `chebyshev_avg`, `union_bound`).

Modelling note: the paper works with real `A`, `b`; the library sketch layer is complex,
so objects are stated for complex matrices and every paper statement is recovered by
specializing `star = id` on real data (then `Aᴴ` is the transpose).  Squared Frobenius
norms are written as `sketchSquared` (equal to `‖·‖_F²` by
`sketch_frobenius_norm_sq`); squared spectral norms use the scoped `L2Operator` norm
(`opNormSq`).
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Papers.LowRankSolve25.MainResults

variable {n d : ℕ}

/-! ## Source model (paper Section 1.3 / 2.1 / 2.2) -/

/-- Squared Euclidean norm of a complex vector, `∑ i ‖v i‖²`. -/
def eNormSq {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- Euclidean norm of a complex vector. -/
def eNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := Real.sqrt (eNormSq v)

/-- Squared column norm `‖A e_c‖²` (the column analogue of `sketchRowSquared`). -/
def sketchColSquared (A : Matrix (Fin n) (Fin d) ℂ) (c : Fin d) : ℝ :=
  ∑ r, Complex.normSq (A r c)

/-- The column energies sum to the total Frobenius energy. -/
theorem sketchColSquared_sum (A : Matrix (Fin n) (Fin d) ℂ) :
    ∑ c, sketchColSquared A c = sketchSquared A := by
  simp only [sketchColSquared, sketchSquared, sketchRowSquared]
  rw [Finset.sum_comm]

/-- Row importance law (1.5): `p_r = ‖e_rᵀA‖² / ‖A‖_F²`.  Requires `A ≠ 0` so that
`‖A‖_F² > 0`; the paper's condition numbers are finite only in that case. -/
def rowDist (A : Matrix (Fin n) (Fin d) ℂ) (hA : sketchSquared A ≠ 0) : FinDist (Fin n) where
  prob r := sketchRowSquared A r / sketchSquared A
  nonneg r := div_nonneg (sketchRowSquared_nonneg A r)
    (le_of_lt (lt_of_le_of_ne (sketchSquared_nonneg A) (Ne.symm hA)))
  sum_one := by
    have h : (∑ r, sketchRowSquared A r / sketchSquared A)
        = (∑ r, sketchRowSquared A r) / sketchSquared A := (Finset.sum_div _ _ _).symm
    rw [h]
    change sketchSquared A / sketchSquared A = 1
    exact div_self hA

/-- Column importance law (1.5): `q_c = ‖A e_c‖² / ‖A‖_F²`. -/
def colDist (A : Matrix (Fin n) (Fin d) ℂ) (hA : sketchSquared A ≠ 0) : FinDist (Fin d) where
  prob c := sketchColSquared A c / sketchSquared A
  nonneg c := div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (le_of_lt (lt_of_le_of_ne (sketchSquared_nonneg A) (Ne.symm hA)))
  sum_one := by
    have h : (∑ c, sketchColSquared A c / sketchSquared A)
        = (∑ c, sketchColSquared A c) / sketchSquared A := (Finset.sum_div _ _ _).symm
    rw [h, sketchColSquared_sum]
    exact div_self hA

/-- Squared spectral norm `‖A‖²` (the paper's `‖A‖` is the operator 2-norm). -/
def opNormSq (A : Matrix (Fin n) (Fin d) ℂ) : ℝ := ‖A‖ ^ 2

/-- `κ_F = ‖A‖_F ‖A⁺‖`; `pinvNorm` is `‖A⁺‖` (the pseudoinverse is not rebuilt here). -/
def kappaF (A : Matrix (Fin n) (Fin d) ℂ) (pinvNorm : ℝ) : ℝ :=
  Real.sqrt (sketchSquared A) * pinvNorm

/-- `κ = ‖A‖ ‖A⁺‖`. -/
def kappa (A : Matrix (Fin n) (Fin d) ℂ) (pinvNorm : ℝ) : ℝ := ‖A‖ * pinvNorm

/-- Paper (1.6), step size `α = 1/‖A‖²`. -/
def paramAlpha (A : Matrix (Fin n) (Fin d) ℂ) : ℝ := 1 / opNormSq A

/-- Paper (1.6), row batch `R ≈ 2κ_F²/κ²`. -/
def paramR (κF κ : ℝ) : ℝ := 2 * κF ^ 2 / κ ^ 2

/-- Paper (1.6), column batch `C ≈ 10κ_F²/ε²`. -/
def paramC (κF ε : ℝ) : ℝ := 10 * κF ^ 2 / ε ^ 2

/-- Paper (1.6), iteration count `K ≈ 4κ² log(1/ε)`. -/
def paramK (κ ε : ℝ) : ℝ := 4 * κ ^ 2 * Real.log (1 / ε)

/-- Entrywise matrix expectation of a single-draw matrix, using real proposal masses. -/
def matrixExpect {X : Type*} [Fintype X]
    (p : FinDist X) (Z : X → Matrix (Fin n) (Fin d) ℂ) : Matrix (Fin n) (Fin d) ℂ :=
  fun i j => ∑ x, (p.prob x : ℂ) * Z x i j

/-- Complex empirical average `(1/L) ∑_k f (ω k)`. -/
def cAvg {X : Type*} {L : ℕ} (f : X → ℂ) (ω : Fin L → X) : ℂ :=
  (∑ k, f (ω k)) / (L : ℂ)

/-- Empirical matrix mean of `m` iid records (entrywise complex average). -/
def matrixSampleMean {X : Type*} [Fintype X] (Z : X → Matrix (Fin n) (Fin d) ℂ)
    (m : ℕ) (ω : Fin m → X) : Matrix (Fin n) (Fin d) ℂ :=
  fun i j => cAvg (fun x => Z x i j) ω

/-- The row-sketch matrix `M_k` of (2.1): the importance-weighted empirical mean of
rank-one records `Aᴴ e_r e_rᵀ A`.  It is the library's `sketchProduct p R A A ω`. -/
def sourceM (A : Matrix (Fin n) (Fin d) ℂ) (p : FinDist (Fin n))
    (R : ℕ) (rows : Fin R → Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  sketchProduct p R A A rows

/-- The column sketch `Â x = (1/C) ∑_c q_c⁻¹ A e_c (e_cᵀ x)` of (2.1). -/
def colSketch (A : Matrix (Fin n) (Fin d) ℂ) (q : FinDist (Fin d))
    (C : ℕ) (cols : Fin C → Fin d) (x : Fin d → ℂ) : Fin n → ℂ :=
  fun i => (1 / (C : ℂ)) * ∑ c : Fin C, (q.prob (cols c) : ℂ)⁻¹ * A i (cols c) * x (cols c)

/-- `z_k` of (2.1): `Aᵀ`-lifted column sketch with row/column importance weights. -/
def sourceZ (A : Matrix (Fin n) (Fin d) ℂ) (p : FinDist (Fin n)) (q : FinDist (Fin d))
    (R C : ℕ) (rows : Fin R → Fin n) (cols : Fin C → Fin d) (x : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (1 / (R : ℂ)) * ∑ r : Fin R, (p.prob (rows r) : ℂ)⁻¹ * star (A (rows r) i) *
    ((1 / (C : ℂ)) * ∑ c : Fin C, (q.prob (cols c) : ℂ)⁻¹ * A (rows r) (cols c) * x (cols c))

/-- `u_k` of (2.32): the row-space column sketch. -/
def sourceU (A : Matrix (Fin n) (Fin d) ℂ) (p : FinDist (Fin n)) (q : FinDist (Fin d))
    (R C : ℕ) (rows : Fin R → Fin n) (cols : Fin C → Fin d) (x : Fin d → ℂ) : Fin n → ℂ :=
  fun i => (1 / (R : ℂ)) * ∑ r : Fin R, (p.prob (rows r) : ℂ)⁻¹ *
    (if rows r = i then
      ((1 / (C : ℂ)) * ∑ c : Fin C, (q.prob (cols c) : ℂ)⁻¹ * A (rows r) (cols c) * x (cols c))
    else 0)

/-- `v_k` of (2.32): the importance-weighted empirical mean of `e_r b_r`. -/
def sourceV (b : Fin n → ℂ) (p : FinDist (Fin n)) (R : ℕ) (rows : Fin R → Fin n) : Fin n → ℂ :=
  fun i => (1 / (R : ℂ)) * ∑ r : Fin R, (p.prob (rows r) : ℂ)⁻¹ *
    (if rows r = i then b (rows r) else 0)

/-- `D = diag(‖e_1ᵀA‖, …, ‖e_nᵀA‖)` of (2.31), as a diagonal matrix. -/
def sourceD (A : Matrix (Fin n) (Fin d) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (sketchRowSquared A i) : ℂ))

/-- `x = Aᵀ y` (complex: `Aᴴ y`), the actual approximate solution of Algorithm 1. -/
def sourceX (A : Matrix (Fin n) (Fin d) ℂ) (y : Fin n → ℂ) : Fin d → ℂ :=
  fun c => ∑ i, star (A i c) * y i

/-- The sampling parameter `φ(y)` of (1.2). -/
def phi (A : Matrix (Fin n) (Fin d) ℂ) (y : Fin n → ℂ) : ℝ :=
  ((Finset.univ.filter (fun i => y i ≠ 0)).card : ℝ) *
    (∑ r, Complex.normSq (y r) * sketchRowSquared A r) / eNormSq (sourceX A y)

/-- One step of Algorithm 1 with the recurrence (1.4): `y_{k+1} = y_k - α (u_k - v_k)`,
written directly in the compressed row-space representation. -/
def sourceStep (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ) (α : ℝ)
    (p : FinDist (Fin n)) (q : FinDist (Fin d)) (R C : ℕ)
    (rows : Fin R → Fin n) (cols : Fin C → Fin d) (y : Fin n → ℂ) : Fin n → ℂ :=
  fun i => y i - (α : ℂ) * ((1 / (R : ℂ)) * ∑ r : Fin R, (p.prob (rows r) : ℂ)⁻¹ *
    (if rows r = i then
      ((1 / (C : ℂ)) * ∑ c : Fin C, (q.prob (cols c) : ℂ)⁻¹ * A (rows r) (cols c) *
        (∑ j, star (A j (cols c)) * y j))
    else 0)) +
    (α : ℂ) * ((1 / (R : ℂ)) * ∑ r : Fin R, (p.prob (rows r) : ℂ)⁻¹ *
      (if rows r = i then b (rows r) else 0))

/-- The `K`-iteration recursion of Algorithm 1 over independent sample batches.
Iteration `0` starts from the all-zero vector `y_0 = 0`; iteration `k+1` applies step `k`
with the fresh batch `(rows k, cols k)`. -/
def sourceIterate (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ) (α : ℝ)
    (p : FinDist (Fin n)) (q : FinDist (Fin d)) (R C : ℕ)
    (rows : ℕ → Fin R → Fin n) (cols : ℕ → Fin C → Fin d) : ℕ → Fin n → ℂ
  | 0 => fun _ => 0
  | k + 1 => sourceStep A b α p q R C (rows k) (cols k) (sourceIterate A b α p q R C rows cols k)

/-- Joint law of the `K × R` row draws and `K × C` column draws. -/
def runProb (p : FinDist (Fin n)) (q : FinDist (Fin d)) (K R C : ℕ)
    (rows : Fin K → Fin R → Fin n) (cols : Fin K → Fin C → Fin d) : ℝ :=
  (∏ k : Fin K, ∏ t : Fin R, p.prob (rows k t)) *
    (∏ k : Fin K, ∏ t : Fin C, q.prob (cols k t))

/-- Expectation of a real statistic of one full run of Algorithm 1. -/
def runExpect (p : FinDist (Fin n)) (q : FinDist (Fin d)) (K R C : ℕ)
    (f : (Fin K → Fin R → Fin n) → (Fin K → Fin C → Fin d) → ℝ) : ℝ :=
  ∑ rows, ∑ cols, runProb p q K R C rows cols * f rows cols

/-- A zero-mass row of the row law has zero energy, hence vanishes entrywise. -/
theorem rowDist_zero_row (A : Matrix (Fin n) (Fin d) ℂ) (hA : sketchSquared A ≠ 0)
    (r : Fin n) (h : (rowDist A hA).prob r = 0) : sketchRowSquared A r = 0 := by
  have hz : sketchRowSquared A r / sketchSquared A = 0 := h
  rcases div_eq_zero_iff.mp hz with h1 | h2
  · exact h1
  · exact absurd h2 hA

/-- The sampling noise `M_k x_k - z_k` of Lemma 2.2 / (2.1), as a vector in `ℂ^d`
(the paper's `Aᵀ` is `Aᴴ` in the library's complex model). -/
def gradNoise (A : Matrix (Fin n) (Fin d) ℂ) (p : FinDist (Fin n)) (q : FinDist (Fin d))
    (R C : ℕ) (rows : Fin R → Fin n) (cols : Fin C → Fin d) (x : Fin d → ℂ) : Fin d → ℂ :=
  (sourceM A p R rows).mulVec x - sourceZ A p q R C rows cols x

/-- Support (nonzero coordinates) of a vector. -/
def supportFinset (y : Fin n → ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => y i ≠ 0)

/-- View a finite batch family `Fin K → Fin R → X` as an `ℕ`-indexed family, repeating
the first batch after `K` (the iterate only reads the first `K` batches). -/
def liftBatch {X : Type*} {K R : ℕ} (hK : 0 < K) (rows : Fin K → Fin R → X) :
    ℕ → Fin R → X := by
  classical
  exact fun t => if h : t < K then rows ⟨t, h⟩ else rows ⟨0, hK⟩

/-- Probability mass of the runs satisfying an event, under the joint row/column law. -/
def runProbEvent (p : FinDist (Fin n)) (q : FinDist (Fin d)) (K R C : ℕ)
    (E : (Fin K → Fin R → Fin n) → (Fin K → Fin C → Fin d) → Prop) : ℝ := by
  classical
  exact ∑ rows, ∑ cols, if E rows cols then runProb p q K R C rows cols else 0

/-! ## c002 — Lemma 1.4, p.6: sparsity and generation cost -/

/-- **Step locality, ingredient of Lemma 1.4, paper p.6 / Section 2 (arXiv:2508.13108v1).**
If `y i = 0` and `i` is not one of the sampled rows of the current batch, then one
Algorithm-1 step does not change coordinate `i` (both importance-weighted sums vanish). -/
theorem sourceStep_eq_of_forall_ne (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (α : ℝ) (p : FinDist (Fin n)) (q : FinDist (Fin d)) (R C : ℕ)
    (rows : Fin R → Fin n) (cols : Fin C → Fin d) (y : Fin n → ℂ) {i : Fin n}
    (hy : y i = 0) (hrow : ∀ r, rows r ≠ i) :
    sourceStep A b α p q R C rows cols y i = 0 := by
  have h0 : (∑ r : Fin R, (p.prob (rows r) : ℂ)⁻¹ *
      (if rows r = i then
        ((1 / (C : ℂ)) * ∑ c : Fin C, (q.prob (cols c) : ℂ)⁻¹ * A (rows r) (cols c) *
          (∑ j, star (A j (cols c)) * y j))
      else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg (hrow r), mul_zero]
  have h1 : (∑ r : Fin R, (p.prob (rows r) : ℂ)⁻¹ *
      (if rows r = i then b (rows r) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg (hrow r), mul_zero]
  simp only [sourceStep, hy]
  rw [h0, h1]
  ring

/-- **Support inclusion, ingredient of Lemma 1.4, paper p.6 (arXiv:2508.13108v1).**
One step can only enlarge the support inside the rows sampled in that step. -/
theorem supportFinset_sourceStep_subset (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (α : ℝ) (p : FinDist (Fin n)) (q : FinDist (Fin d)) (R C : ℕ)
    (rows : Fin R → Fin n) (cols : Fin C → Fin d) (y : Fin n → ℂ) :
    supportFinset (sourceStep A b α p q R C rows cols y)
      ⊆ supportFinset y ∪ Finset.univ.image rows := by
  intro i hi
  by_cases hmem : i ∈ Finset.univ.image rows
  · exact Finset.mem_union_right _ hmem
  · refine Finset.mem_union_left _ ?_
    have hrow : ∀ r, rows r ≠ i := by
      intro r hr
      exact hmem (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩)
    by_contra hnot
    have hy : y i = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    have hz := sourceStep_eq_of_forall_ne A b α p q R C rows cols y hy hrow
    have hi' : sourceStep A b α p q R C rows cols y i ≠ 0 := by
      simpa [supportFinset] using hi
    exact hi' hz

/-- **Support inclusion over `K` iterations, ingredient of Lemma 1.4, paper p.6.**
After `K` iterations the support of `y_K` is contained in the union of the sampled row
batches `rows 0, …, rows (K-1)`. -/
theorem supportFinset_sourceIterate_subset (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (α : ℝ) (p : FinDist (Fin n)) (q : FinDist (Fin d)) (R C : ℕ)
    (rows : ℕ → Fin R → Fin n) (cols : ℕ → Fin C → Fin d) (K : ℕ) :
    supportFinset (sourceIterate A b α p q R C rows cols K)
      ⊆ (Finset.range K).biUnion (fun k => Finset.univ.image (rows k)) := by
  induction K with
  | zero => simp [supportFinset, sourceIterate]
  | succ k ih =>
    intro i hi
    have hi' : i ∈ supportFinset (sourceStep A b α p q R C (rows k) (cols k)
        (sourceIterate A b α p q R C rows cols k)) := hi
    have h1 : i ∈ supportFinset (sourceIterate A b α p q R C rows cols k)
        ∪ Finset.univ.image (rows k) :=
      supportFinset_sourceStep_subset A b α p q R C (rows k) (cols k)
        (sourceIterate A b α p q R C rows cols k) hi'
    rcases Finset.mem_union.mp h1 with h | h
    · have h2 := ih h
      rcases Finset.mem_biUnion.mp h2 with ⟨j, hj, hij⟩
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self k)),
          hij⟩
    · exact Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), h⟩

/-- **Lemma 1.4, sparsity part, paper p.6 (arXiv:2508.13108v1).**
The `K`-th iterate of Algorithm 1 has at most `K·R` nonzero coordinates, because every
step writes only on its `R` freshly sampled rows. -/
theorem lemma14_sparsity (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ) (α : ℝ)
    (p : FinDist (Fin n)) (q : FinDist (Fin d)) (R C K : ℕ)
    (rows : ℕ → Fin R → Fin n) (cols : ℕ → Fin C → Fin d) :
    (supportFinset (sourceIterate A b α p q R C rows cols K)).card ≤ K * R := by
  have hsub := supportFinset_sourceIterate_subset A b α p q R C rows cols K
  calc (supportFinset (sourceIterate A b α p q R C rows cols K)).card
      ≤ ((Finset.range K).biUnion (fun k => Finset.univ.image (rows k))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range K, (Finset.univ.image (rows k)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range K, R := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact le_trans Finset.card_image_le (by simp)
    _ = K * R := by
        simp [Finset.sum_const, Finset.card_range]

/-- **Lemma 1.4, sample-count arithmetic, paper p.6 (arXiv:2508.13108v1).**
With parameters (1.6), the number of stored records `K·R` is exactly
`8 κ_F² log(1/ε)` (the `κ²` factors cancel). -/
theorem lemma14_sample_count (κF κ ε : ℝ) (hκ : κ ≠ 0) :
    paramK κ ε * paramR κF κ = 8 * κF ^ 2 * Real.log (1 / ε) := by
  have hκ2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  simp only [paramK, paramR]
  field_simp
  ring

/-- **Lemma 1.4, generation-cost arithmetic, paper p.6 (arXiv:2508.13108v1).**
The total number of sampled records `K·R·C` at parameters (1.6) is
`80 κ_F⁴ log(1/ε)/ε²`, which is the paper's `Õ(κ_F⁴/ε²)` generation cost. -/
theorem lemma14_cost (κF κ ε : ℝ) (hκ : κ ≠ 0) (hε : ε ≠ 0) :
    paramK κ ε * paramR κF κ * paramC κF ε
      = 80 * κF ^ 4 * Real.log (1 / ε) / ε ^ 2 := by
  have hκ2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε
  simp only [paramK, paramR, paramC]
  field_simp
  ring

/-! ## c003 — Theorem 1.6, p.6-9: expected squared error -/

/-- **Theorem 1.6, paper p.6 (arXiv:2508.13108v1).**
`E‖x* - Aᵀ y_K‖² ≤ 2 ε² ‖x*‖²` for `ε < 1/4` and parameters (1.6)
(`R ≥ 2κ_F²/κ²`, `C ≥ 10κ_F²/ε²`, `K ≥ 4κ² log(1/ε)`).

Paper proof (pp.8-9): using Lemmas 2.1-2.5 and `α = 1/‖A‖²`, the paper proves the
one-step contraction (their equation (2.3))
`E‖x* - x_{k+1}‖² ≤ (1 - 1/κ²) E‖x* - x_k‖² + 10κ⁴/‖A‖⁴ ‖x*‖²`;
unrolling `K` steps and using `(1 - 1/κ²)^K ≤ exp(-K/κ²) ≤ ε⁴` with
`K = 4κ² log(1/ε)` gives the `2ε²` bound.  The contraction uses the exact moments
in `lemma21_second_moment`, `lemma22_conditional_second_moment` and
`lemma25_alpha_squared_bound`, followed by a geometric-series estimate.

Scope note: this declaration defines the expected-error proposition; the
contraction recursion and its iteration are not proved in this file. -/
def theorem16_expected_error (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (hA : sketchSquared A ≠ 0) (ε : ℝ) (hε : 0 < ε) (_hε4 : ε < 1 / 4)
    (pinvNorm : ℝ) (xstar : Fin d → ℂ) (K R C : ℕ) (hK : 0 < K) (hR : 0 < R)
    (hC : 0 < C)
    (hRparam : 2 * kappaF A pinvNorm ^ 2 / kappa A pinvNorm ^ 2 ≤ (R : ℝ))
    (hCparam : 10 * kappaF A pinvNorm ^ 2 / ε ^ 2 ≤ (C : ℝ))
    (hKparam : 4 * (kappa A pinvNorm) ^ 2 * Real.log (1 / ε) ≤ (K : ℝ))
    (hxstar : Aᴴ.mulVec (A.mulVec xstar) = Aᴴ.mulVec b) : Prop :=
    (∑ rows : Fin K → Fin R → Fin n, ∑ cols : Fin K → Fin C → Fin d,
      runProb (rowDist A hA) (colDist A hA) K R C rows cols *
        eNormSq (xstar - sourceX A (sourceIterate A b (paramAlpha A)
          (rowDist A hA) (colDist A hA) R C (liftBatch hK rows) (liftBatch hK cols) K)))
      ≤ 2 * ε ^ 2 * eNormSq xstar

/-! ## c004 — Theorem 1.7, p.7/11: high-probability bound on `φ(y)` -/

/-- **Theorem 1.7, paper p.7 (arXiv:2508.13108v1).**
There is a positive numerical constant `const` such that, with probability at least
`9/10` over the run of Algorithm 1 at parameters (1.6),
`φ(y) ≤ const · κ_F² κ⁶ log³(1/ε)`.

Paper proof (p.11): `φ(y)` is controlled by the mass of `y` relative to `‖Aᵀ y‖²`;
Theorem 1.6-style second-moment bounds give `E[φ(y)] ≤ const·κ_F²κ⁶log³(1/ε)`, and
Markov's inequality turns the mean bound into probability `9/10` after the constants
are inflated; `chebyshev_avg` and `union_bound` provide related finite-law estimates.

Scope note: this declaration defines the probability-bound proposition; the exact
first-moment computation of `φ` and the Markov step over the finite run law are
outside the scope of this file. -/
def theorem17_phi_bound (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (hA : sketchSquared A ≠ 0) (ε : ℝ) (hε : 0 < ε) (_hε4 : ε < 1 / 4)
    (pinvNorm : ℝ) (K R C : ℕ) (hK : 0 < K) (hR : 0 < R) (hC : 0 < C)
    (hRparam : 2 * kappaF A pinvNorm ^ 2 / kappa A pinvNorm ^ 2 ≤ (R : ℝ))
    (hCparam : 10 * kappaF A pinvNorm ^ 2 / ε ^ 2 ≤ (C : ℝ))
    (hKparam : 4 * (kappa A pinvNorm) ^ 2 * Real.log (1 / ε) ≤ (K : ℝ)) : Prop :=
    ∃ const : ℝ, 0 < const ∧
      (9 : ℝ) / 10 ≤ runProbEvent (rowDist A hA) (colDist A hA) K R C
        (fun rows cols =>
          phi A (sourceIterate A b (paramAlpha A) (rowDist A hA) (colDist A hA) R C
            (liftBatch hK rows) (liftBatch hK cols) K)
            ≤ const * kappaF A pinvNorm ^ 2 * (kappa A pinvNorm) ^ 6 *
                (Real.log (1 / ε)) ^ 3)

/-! ## c005 — Lemma 2.1, p.7/16: moments of `M_k` -/

/-- **Lemma 2.1, first moment, paper p.7 (arXiv:2508.13108v1).**
For every entry `(i,j)` the expectation of the row sketch `M_k` is `(Aᴴ A) i j`,
i.e. `E[M_k] = Aᵀ A` in the paper's real notation.

Proof route (paper p.16): expand the weighted empirical mean and use that the row
law is proportional to the squared row norms, so `∑_r p_r (1/p_r) Aᴴ e_r e_rᵀ A = AᵀA`.
In Lean this is the library's `sketchProduct_unbiased_mean` followed by
`sketchMean_eq_product`, with `rowDist_zero_row` discharging the zero-mass rows. -/
theorem lemma21_first_moment (A : Matrix (Fin n) (Fin d) ℂ) (hA : sketchSquared A ≠ 0)
    (R : ℕ) (hR : 0 < R) (i : Fin d) (j : Fin d) :
    (∑ ω : Fin R → Fin n, (((rowDist A hA).probOf ω : ℝ) : ℂ) *
        sourceM A (rowDist A hA) R ω i j) = (Aᴴ * A) i j := by
  have hs : ∀ k, (rowDist A hA).prob k = 0 → ∀ i j, star (A k i) * A k j = 0 := by
    intro k hk i j
    have hz : sketchRowSquared A k = 0 := rowDist_zero_row A hA k hk
    rw [sketchRowSquared_eq_zero_entry A k hz i, sketchRowSquared_eq_zero_entry A k hz j]
    simp
  simp only [sourceM]
  rw [sketchProduct_unbiased_mean (rowDist A hA) R hR A A i j]
  rw [sketchMean_eq_product (rowDist A hA) A A hs]

/-- **Lemma 2.1, second moment, paper p.7 (arXiv:2508.13108v1).**
For every entry `(i,j)`,
`E[(M_k M_k) i j] = (1/R)‖A‖_F² (AᵀA) i j + (1 - 1/R)((AᵀA)²) i j`,
which is the paper's `E[M_k²] = (1/R)‖A‖_F² AᵀA + (1 - 1/R)(AᵀA)²`.

Paper proof: the paper expands
`M_k M_k` into the `R²` pairs `(r, r')` of independent row draws, computes the
diagonal contribution `∑_r p_r⁻² (Aᴴ e_r e_rᵀ A)²` and the off-diagonal contribution
`((R² - R)/R²)(AᵀA)²`, and uses `p_r = ‖e_rᵀ A‖²/‖A‖_F²` to turn the diagonal into
`(1/R)‖A‖_F² AᵀA`.  This is an entrywise decomposition of the product law,
as in `sketchProduct_entry_parts`.

Scope note: this declaration defines the second-moment identity as a proposition;
the independent-draw expansion is not proved in this file. -/
def lemma21_second_moment (A : Matrix (Fin n) (Fin d) ℂ) (hA : sketchSquared A ≠ 0)
    (R : ℕ) (hR : 0 < R) (i : Fin d) (j : Fin d) : Prop :=
    (∑ ω : Fin R → Fin n, (((rowDist A hA).probOf ω : ℝ) : ℂ) *
        ((sourceM A (rowDist A hA) R ω) * (sourceM A (rowDist A hA) R ω)) i j)
      = (1 / (R : ℂ)) * (sketchSquared A : ℂ) * (Aᴴ * A) i j
        + (1 - 1 / (R : ℂ)) * ((Aᴴ * A) * (Aᴴ * A)) i j

/-! ## c006 — Lemma 2.2, p.7/16-17: unbiasedness and variance of the noise -/

/-- **Lemma 2.2, conditional unbiasedness, paper p.7 (arXiv:2508.13108v1).**
For every coordinate `i`, the weighted expectation of the sampling noise over the
independent row and column draws vanishes: `E[M_k x_k - z_k | M_k, x_k] = 0`.

Paper proof (p.16): condition on the rows; each sampled row applies the column
importance sketch to the same row, and the column law `q_c = ‖A e_c‖²/‖A‖_F²` makes
that sketch an unbiased estimator of `e_rᵀ A x_k`.  Reorganizing the finite
double sum as an iterated expectation evaluates each inner sum with
`∑_c q_c (1/q_c) A_{r c} x_c = (A x_k)_r` (zero-mass columns via
`sketchColSquared = 0 ⇒ A · c = 0`).

Scope note: this declaration defines the unbiasedness proposition; the iterated
expectation calculation is not proved in this file. -/
def lemma22_conditional_unbiased (A : Matrix (Fin n) (Fin d) ℂ) (hA : sketchSquared A ≠ 0)
    (R C : ℕ) (hR : 0 < R) (hC : 0 < C) (x : Fin d → ℂ) (i : Fin d) : Prop :=
    (∑ rows : Fin R → Fin n, ∑ cols : Fin C → Fin d,
      (((rowDist A hA).probOf rows * (colDist A hA).probOf cols : ℝ) : ℂ) *
        gradNoise A (rowDist A hA) (colDist A hA) R C rows cols x i) = 0

/-- **Lemma 2.2, conditional second moment, paper p.7 (arXiv:2508.13108v1).**
`E[‖M_k x_k - z_k‖² | x_k] ≤ (‖A‖_F⁴/(RC) + ‖A‖_F²‖A‖²/C) ‖x_k‖²`
(`sketchSquared A` is `‖A‖_F²`, `opNormSq A` is `‖A‖²`).

Paper proof (p.17): the row-sketch variance contributes `‖A‖_F⁴/(RC)‖x‖²` via Lemma A.1
applied entrywise, and the column sketch contributes `‖A‖_F²‖A‖²/C‖x‖²` via the
importance-sampling bound `E‖Â x - Ax‖² ≤ (‖A‖_F²/C)‖x‖²` plus `‖A x‖² ≤ ‖A‖²‖x‖²`.
The argument uses the entrywise variance formula for the importance-weighted column mean and the
operator-norm inequality `eNormSq (A.mulVec x) ≤ opNormSq A * eNormSq x` (from
`Matrix.l2_opNorm_mulVec` and the `EuclideanSpace` bridge).

Scope note: this declaration defines the second-moment bound as a proposition;
the variance and operator-norm estimates are not assembled here. -/
def lemma22_conditional_second_moment (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : sketchSquared A ≠ 0) (R C : ℕ) (hR : 0 < R) (hC : 0 < C) (x : Fin d → ℂ) : Prop :=
    (∑ rows : Fin R → Fin n, ∑ cols : Fin C → Fin d,
      ((rowDist A hA).probOf rows * (colDist A hA).probOf cols) *
        eNormSq (gradNoise A (rowDist A hA) (colDist A hA) R C rows cols x))
      ≤ (sketchSquared A ^ 2 / ((R : ℝ) * (C : ℝ))
          + sketchSquared A * opNormSq A / (C : ℝ)) * eNormSq x

/-! ## c007 — Lemma 2.3, p.10/17-18: second moment of `D u_k` -/

/-- **Lemma 2.3, paper p.10 (arXiv:2508.13108v1).**
`E[‖D u_k‖² | x_k] ≤ (‖A‖_F⁴/(RC) + ‖A‖_F²‖A‖²/R + ‖A‖⁴) ‖x_k‖²`.

Paper proof (pp.17-18): condition on `x_k` and on the row draws; the inner column
sketch of each sampled row has second moment at most `(‖A‖_F²/C)‖x‖²` (importance
sampling), while the row sampling of `D u_k` has second moment at most `‖A‖_F²/R`
times the unsketched row-space norm; finally the exact term is bounded by `‖A‖²` times
the row energy.  The argument combines the column-sketch variance bound and the
row-energy identity with `eNormSq (A.mulVec x) ≤ opNormSq A * eNormSq x`, the
operator-norm estimate supplied by `Matrix.l2_opNorm_mulVec`.

Scope note: this declaration defines the second-moment bound as a proposition;
the combination of these estimates is not proved in this file. -/
def lemma23_Du_second_moment (A : Matrix (Fin n) (Fin d) ℂ) (hA : sketchSquared A ≠ 0)
    (R C : ℕ) (hR : 0 < R) (hC : 0 < C) (x : Fin d → ℂ) : Prop :=
    (∑ rows : Fin R → Fin n, ∑ cols : Fin C → Fin d,
      ((rowDist A hA).probOf rows * (colDist A hA).probOf cols) *
        eNormSq ((sourceD A).mulVec (sourceU A (rowDist A hA) (colDist A hA) R C rows cols x)))
      ≤ (sketchSquared A ^ 2 / ((R : ℝ) * (C : ℝ))
          + sketchSquared A * opNormSq A / (R : ℝ) + opNormSq A ^ 2) * eNormSq x

/-! ## c008 — Lemma 2.4, p.10/18: second moment of `D v_k` -/

/-- **Lemma 2.4, paper p.10 (arXiv:2508.13108v1).**
`E[‖D v_k‖² | x_k] ≤ ‖A‖_F²‖b‖²/R + ‖A‖²‖b‖²`
(`sketchSquared A = ‖A‖_F²`, `opNormSq A = ‖A‖²`, `eNormSq b = ‖b‖²`).

Sharpening over the paper: the bound is stated for every `R > 0` and does not need the
conditioning, because `v_k` does not depend on `x_k`.  The argument uses the iid
second moment of the weighted empirical mean of `b` and the row-energy substitution
`p_i = sketchRowSquared A i / sketchSquared A` (zero-mass rows via `rowDist_zero_row`).
Related expectation identities are `expect_avg` and `expect_prod`.

Scope note: this declaration defines the second-moment bound as a proposition;
the weighted-mean calculation is not proved in this file. -/
def lemma24_Dv_second_moment (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (hA : sketchSquared A ≠ 0) (R : ℕ) (hR : 0 < R) : Prop :=
    (∑ rows : Fin R → Fin n, (rowDist A hA).probOf rows *
        eNormSq ((sourceD A).mulVec (sourceV b (rowDist A hA) R rows)))
      ≤ (sketchSquared A / (R : ℝ) + opNormSq A) * eNormSq b

/-! ## c009 — Lemma 2.5, p.10/11: variance bound for `D(u_k - v_k)` -/

/-- **Lemma 2.5, paper p.10 (arXiv:2508.13108v1).**
For `ε < 1/4`, parameters (1.6) (`R ≥ 2κ_F²/κ²`, `C ≥ 10κ_F²/ε²`), and a
least-squares solution `x*` with `‖b‖ ≤ ‖A‖ ‖x*‖`,
`α² E[‖D(u_k - v_k)‖²] ≤ 10 κ⁴ ‖x*‖²`.

`pinvNorm` carries `‖A⁺‖`, so `kappa A pinvNorm = κ` and
`kappaF A pinvNorm = κ_F`; `hb` is the paper's `‖b‖ = ‖A x*‖ ≤ ‖A‖‖x*‖` for the
consistent/minimum-norm solution.

The argument combines `lemma23_Du_second_moment` and `lemma24_Dv_second_moment`
under the pointwise bound `eNormSq (u - v) ≤ 2 (eNormSq u + eNormSq v)` and the
parameter inequalities, using `paramAlpha A = 1 / opNormSq A` and
`kappaF^2 / kappa^2 = sketchSquared A / opNormSq A`.

Scope note: this declaration defines the variance-bound proposition; the
combination of the component estimates is not proved in this file. -/
def lemma25_alpha_squared_bound (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (hA : sketchSquared A ≠ 0) (ε : ℝ) (hε : 0 < ε) (_hε4 : ε < 1 / 4)
    (pinvNorm : ℝ) (xstar : Fin d → ℂ) (R C : ℕ) (hR : 0 < R) (hC : 0 < C)
    (hRparam : 2 * kappaF A pinvNorm ^ 2 / kappa A pinvNorm ^ 2 ≤ (R : ℝ))
    (hCparam : 10 * kappaF A pinvNorm ^ 2 / ε ^ 2 ≤ (C : ℝ))
    (hb : eNormSq b ≤ opNormSq A * eNormSq xstar) : Prop :=
    (paramAlpha A) ^ 2 * (∑ rows : Fin R → Fin n, ∑ cols : Fin C → Fin d,
      ((rowDist A hA).probOf rows * (colDist A hA).probOf cols) *
        eNormSq ((sourceD A).mulVec
          (sourceU A (rowDist A hA) (colDist A hA) R C rows cols xstar -
            sourceV b (rowDist A hA) R rows)))
      ≤ 10 * (kappa A pinvNorm) ^ 4 * eNormSq xstar

/-! ## c010 — Lemma A.1, p.16: iid matrix sample-mean second moment -/

/-- Real scalar core of Lemma A.1: the second moment of the empirical mean
`(1/m)∑ f(ω_k)` is `(1/m) E[f²] + (1-1/m)(E f)²`. -/
theorem real_avg_second_moment {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (m : ℕ) (hm : 0 < m) :
    (∑ ω : Fin m → X, p.probOf ω * (FinDist.avg f ω) ^ 2)
      = (1 / (m : ℝ)) * (∑ x, p.prob x * (f x) ^ 2)
        + (1 - 1 / (m : ℝ)) * (p.expect f) ^ 2 := by
  have hvar := p.expect_avg_sub_sq f hm
  have hvsq : p.variance f = p.expect (fun x => (f x) ^ 2) - (p.expect f) ^ 2 := by
    set E := p.expect f with hE
    have hsum : (∑ x, p.prob x * f x) = E := hE.symm
    show (∑ x, p.prob x * (f x - E) ^ 2) = (∑ x, p.prob x * (f x) ^ 2) - E ^ 2
    have h1 : ∀ x, p.prob x * (f x - E) ^ 2
        = p.prob x * (f x) ^ 2 - (2 * E) * (p.prob x * f x) + p.prob x * E ^ 2 :=
      fun x => by ring
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsum, ← Finset.sum_mul, p.sum_one, one_mul]
    ring
  have h1 : (∑ ω : Fin m → X, p.probOf ω * (FinDist.avg f ω - p.expect f) ^ 2)
      = (∑ ω : Fin m → X, p.probOf ω * (FinDist.avg f ω) ^ 2)
        - 2 * p.expect f * (∑ ω : Fin m → X, p.probOf ω * FinDist.avg f ω)
        + (p.expect f) ^ 2 * (∑ ω : Fin m → X, p.probOf ω) := by
    calc (∑ ω : Fin m → X, p.probOf ω * (FinDist.avg f ω - p.expect f) ^ 2)
        = ∑ ω : Fin m → X, (p.probOf ω * (FinDist.avg f ω) ^ 2
            - 2 * p.expect f * (p.probOf ω * FinDist.avg f ω)
            + (p.expect f) ^ 2 * p.probOf ω) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
  have h2 : (∑ ω : Fin m → X, p.probOf ω * FinDist.avg f ω) = p.expect f :=
    p.expect_avg f hm
  have h3 : (∑ ω : Fin m → X, p.probOf ω) = 1 := p.sum_probOf m
  have h4 : (∑ ω : Fin m → X, p.probOf ω * (FinDist.avg f ω) ^ 2)
      = (∑ ω : Fin m → X, p.probOf ω * (FinDist.avg f ω - p.expect f) ^ 2)
        + (p.expect f) ^ 2 := by
    rw [h1, h2, h3]
    ring
  rw [h4, hvar, hvsq]
  simp only [FinDist.expect]
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp
  ring

/-- Real part of the complex empirical average. -/
theorem cAvg_re {X : Type*} {m : ℕ} (f : X → ℂ) (ω : Fin m → X) :
    (cAvg f ω).re = FinDist.avg (fun x => (f x).re) ω := by
  simp only [cAvg, FinDist.avg, Complex.div_natCast_re]
  congr 1
  simpa using Complex.re_sum (s := Finset.univ) (f := fun k : Fin m => f (ω k))

/-- Imaginary part of the complex empirical average. -/
theorem cAvg_im {X : Type*} {m : ℕ} (f : X → ℂ) (ω : Fin m → X) :
    (cAvg f ω).im = FinDist.avg (fun x => (f x).im) ω := by
  simp only [cAvg, FinDist.avg, Complex.div_natCast_im]
  congr 1
  simpa using Complex.im_sum (s := Finset.univ) (f := fun k : Fin m => f (ω k))

/-- Complex scalar core of Lemma A.1: the second moment of the complex empirical
mean, in terms of `Complex.normSq`. -/
theorem cAvg_second_moment {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ ω : Fin m → X, p.probOf ω * Complex.normSq (cAvg f ω))
      = (1 / (m : ℝ)) * (∑ x, p.prob x * Complex.normSq (f x))
        + (1 - 1 / (m : ℝ)) * Complex.normSq (∑ x, (p.prob x : ℂ) * f x) := by
  have hprod : ∀ ω : Fin m → X,
      Complex.normSq (cAvg f ω)
        = (FinDist.avg (fun x => (f x).re) ω) ^ 2
          + (FinDist.avg (fun x => (f x).im) ω) ^ 2 := by
    intro ω
    rw [Complex.normSq_apply, ← pow_two, ← pow_two, cAvg_re, cAvg_im]
  have hsum : ∀ x : X,
      Complex.normSq (f x) = (f x).re ^ 2 + (f x).im ^ 2 := by
    intro x
    rw [Complex.normSq_apply, ← pow_two, ← pow_two]
  have hmean : Complex.normSq (∑ x, (p.prob x : ℂ) * f x)
      = (p.expect (fun x => (f x).re)) ^ 2 + (p.expect (fun x => (f x).im)) ^ 2 := by
    have hre : (∑ x, (p.prob x : ℂ) * f x).re = p.expect (fun x => (f x).re) := by
      simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        FinDist.expect]
      apply Finset.sum_congr rfl
      intro x _
      ring
    have him : (∑ x, (p.prob x : ℂ) * f x).im = p.expect (fun x => (f x).im) := by
      simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        FinDist.expect]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [Complex.normSq_apply, hre, him, ← pow_two, ← pow_two]
  simp only [hprod, hsum, hmean]
  have hL : (∑ x : Fin m → X, p.probOf x *
      (FinDist.avg (fun x => (f x).re) x ^ 2 + FinDist.avg (fun x => (f x).im) x ^ 2))
      = (∑ x : Fin m → X, p.probOf x * (FinDist.avg (fun x => (f x).re) x) ^ 2)
        + (∑ x : Fin m → X, p.probOf x * (FinDist.avg (fun x => (f x).im) x) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hR : (∑ i : X, p.prob i * ((f i).re ^ 2 + (f i).im ^ 2))
      = (∑ i : X, p.prob i * (f i).re ^ 2)
        + (∑ i : X, p.prob i * (f i).im ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hL, hR, mul_add, mul_add]
  rw [real_avg_second_moment p (fun x => (f x).re) m hm,
    real_avg_second_moment p (fun x => (f x).im) m hm]
  ring

/-- **Lemma A.1, paper p.16 (arXiv:2508.13108v1).**
`E‖(1/m)∑ Z_i‖_F² = (1/m) E‖Z‖_F² + (1 - 1/m) ‖E[Z]‖_F²` for `m > 0`, with the
expectations taken over the iid product law.

Paper proof: expand the squared Frobenius norm into entries, split the double sum over
draw indices into diagonal (`i = j`) and off-diagonal (`i ≠ j`) parts; independence
factors the off-diagonal expectation into `E[Z]ᵀE[Z]`, and the diagonal part is
`(1/m) E[ZᵀZ]`; combine.  The scalar core is the real identity
`∑_ω p.probOf ω * avg(f ω)^2 = (1/m) E[f²] + (1 - 1/m)(E f)²`, which follows from
`expect_avg_sub_sq` (+ `variance_eq_expect_sq_sub`, `expect_avg`,
`sum_probOf`) by expanding the square; the complex version is obtained from the real
identity applied to the real and imaginary parts (`avg` is `ℝ`-linear and
`Complex.normSq z = z.re² + z.im²`). -/
theorem lemmaA1_sample_mean_second_moment {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (Z : X → Matrix (Fin n) (Fin d) ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ ω : Fin m → X, p.probOf ω * sketchSquared (matrixSampleMean Z m ω))
      = (1 / (m : ℝ)) * (∑ x, p.prob x * sketchSquared (Z x))
        + (1 - 1 / (m : ℝ)) * sketchSquared (matrixExpect p Z) := by
  simp only [sketchSquared, sketchRowSquared, matrixSampleMean, matrixExpect]
  have hL : (∑ ω : Fin m → X, p.probOf ω *
        ∑ i, ∑ j, Complex.normSq (cAvg (fun x => Z x i j) ω))
      = ∑ i, ∑ j, ∑ ω : Fin m → X,
          p.probOf ω * Complex.normSq (cAvg (fun x => Z x i j) ω) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hA : (1 / (m : ℝ)) *
        (∑ x, p.prob x * (∑ i, ∑ j, Complex.normSq (Z x i j)))
      = ∑ i, ∑ j, (1 / (m : ℝ)) * (∑ x, p.prob x * Complex.normSq (Z x i j)) := by
    have h1 : ∀ x, p.prob x * (∑ i, ∑ j, Complex.normSq (Z x i j))
        = ∑ i, ∑ j, p.prob x * Complex.normSq (Z x i j) := by
      intro x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    simp only [h1]
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hB : (1 - 1 / (m : ℝ)) *
        (∑ i, ∑ j, Complex.normSq (∑ x, (p.prob x : ℂ) * Z x i j))
      = ∑ i, ∑ j, (1 - 1 / (m : ℝ)) *
          Complex.normSq (∑ x, (p.prob x : ℂ) * Z x i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hL, hA, hB, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact cAvg_second_moment p (fun x => Z x i j) m hm

/-! ## c001 — main result, abstract / (1.3), pp.1-6 -/

/-- **Main result, paper abstract / (1.3), pp.1-6 (arXiv:2508.13108v1).**
Running Algorithm 1 with parameters (1.6) on a least-squares instance yields a
compressed representation `y_K` such that

1. the representation is `K·R`-sparse (Lemma 1.4; at the parameters this is
   `8κ_F²log(1/ε)`),
2. its generation work `K·R·C` is exactly `80κ_F⁴log(1/ε)/ε²` (the paper's
   `Õ(κ_F⁴/ε²)`),
3. the actual output `x = Aᵀ y_K` satisfies the Theorem 1.6 expected error bound
   `E‖x* - x‖² ≤ 2ε²‖x*‖²`.

The entry-query bound `Õ(κ_F²)` follows from (1) (a query scans the representation) and
the sampling bound `Õ(κ_F⁴κ⁶)` is Theorem 1.7 (claim c004).  The expected-error
conjunct is expressed by `theorem16_expected_error`; the paper's analysis also
uses a tail-to-expectation passage.

Scope note: this declaration defines the combined main-result proposition;
the expected-error analysis and tail-to-expectation passage are not proved here. -/
def main_result (A : Matrix (Fin n) (Fin d) ℂ) (b : Fin n → ℂ)
    (hA : sketchSquared A ≠ 0) (ε : ℝ) (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (pinvNorm : ℝ) (hκ : kappa A pinvNorm ≠ 0) (xstar : Fin d → ℂ)
    (K R C : ℕ) (hK : 0 < K) (hR : 0 < R) (hC : 0 < C)
    (hRparam : 2 * kappaF A pinvNorm ^ 2 / kappa A pinvNorm ^ 2 ≤ (R : ℝ))
    (hCparam : 10 * kappaF A pinvNorm ^ 2 / ε ^ 2 ≤ (C : ℝ))
    (hKparam : 4 * (kappa A pinvNorm) ^ 2 * Real.log (1 / ε) ≤ (K : ℝ))
    (hxstar : Aᴴ.mulVec (A.mulVec xstar) = Aᴴ.mulVec b) : Prop :=
    (∀ rows : Fin K → Fin R → Fin n, ∀ cols : Fin K → Fin C → Fin d,
        (supportFinset (sourceIterate A b (paramAlpha A) (rowDist A hA) (colDist A hA)
          R C (liftBatch hK rows) (liftBatch hK cols) K)).card ≤ K * R) ∧
      (paramK (kappa A pinvNorm) ε * paramR (kappaF A pinvNorm) (kappa A pinvNorm) *
          paramC (kappaF A pinvNorm) ε
        = 80 * (kappaF A pinvNorm) ^ 4 * Real.log (1 / ε) / ε ^ 2) ∧
      (∑ rows : Fin K → Fin R → Fin n, ∑ cols : Fin K → Fin C → Fin d,
        runProb (rowDist A hA) (colDist A hA) K R C rows cols *
          eNormSq (xstar - sourceX A (sourceIterate A b (paramAlpha A)
            (rowDist A hA) (colDist A hA) R C (liftBatch hK rows) (liftBatch hK cols) K)))
        ≤ 2 * ε ^ 2 * eNormSq xstar

end Qatlib.Papers.LowRankSolve25.MainResults
