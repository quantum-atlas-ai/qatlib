/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.SqEstimation.InnerProduct.SQInnerProductEstimation
set_option warningAsError false

set_option autoImplicit false
open Matrix
open scoped Classical BigOperators ComplexOrder
open Qatlib.Concepts.SqEstimation.InnerProduct
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.SqEstimation.TraceBilinear

noncomputable def sqMatrixRowProbability {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (i : Fin n) : ℝ := ∑ j, a.samples.prob (i,j)
noncomputable def sqMatrixColumnProbability {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (i j : Fin n) : ℝ :=
  if sqMatrixRowProbability a i=0 then (if j.val=0 then 1 else 0) else
    a.samples.prob (i,j)/sqMatrixRowProbability a i
noncomputable def sqMatrixRunCalls {n : ℕ} (a : FiniteSQInput (Fin n × Fin n)) (A : Operator n)
    (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin n × Fin n) : List SQCall :=
  (sqRunCalls a (fun p => A p.1 p.2) m r ω).flatMap (fun c =>
    if c=.sampleEnvelope then [.sampleRow,.sampleColumn] else [c])
noncomputable def sqConsumerA : Operator 2 := ![![1,Complex.I],![0,1]]
noncomputable def sqConsumerB : Operator 2 := ![![1,1],![0,2]]

noncomputable def sqBilinearEstimate {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (x y : Fin n → ℂ) (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin n × Fin n) : ℂ :=
  star (sqMedian a (fun p => x p.1*star (y p.2)) m r ω)
noncomputable def sqBilinearRunCalls {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (x y : Fin n → ℂ) (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin n × Fin n) : List SQCall :=
  (sqRunCalls a (fun p => x p.1*star (y p.2)) m r ω).flatMap (fun c =>
    if c=.sampleEnvelope then [.sampleRow,.sampleColumn] else
      if c=.otherEntry then [.leftVectorEntry,.rightVectorEntry] else [c])

theorem sqMatrix_sampler_factorization {n : ℕ} (a : FiniteSQInput (Fin n × Fin n)) :
    ∃ (rows : FinDist (Fin n)) (cols : Fin n → FinDist (Fin n)),
      ∀ i j, rows.prob i = sqMatrixRowProbability a i ∧
        (cols i).prob j = sqMatrixColumnProbability a i j ∧
        a.samples.prob (i,j) = rows.prob i * (cols i).prob j := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    have h := a.envelope_pos
    simp [sqSquaredNorm] at h
  let j0 : Fin n := ⟨0, hn⟩
  have hrow : ∀ i, 0 ≤ sqMatrixRowProbability a i :=
    fun i => Finset.sum_nonneg fun j _ => a.samples.nonneg _
  have hsum : ∑ i, sqMatrixRowProbability a i = 1 := by
    simpa only [sqMatrixRowProbability, ← Fintype.sum_prod_type] using! a.samples.sum_one
  let rows : FinDist (Fin n) := ⟨sqMatrixRowProbability a, hrow, hsum⟩
  have hcolnn : ∀ i j, 0 ≤ sqMatrixColumnProbability a i j := by
    intro i j
    unfold sqMatrixColumnProbability
    split_ifs
    · norm_num
    · norm_num
    · exact div_nonneg (a.samples.nonneg _) (hrow i)
  have hcolsum : ∀ i, ∑ j, sqMatrixColumnProbability a i j = 1 := by
    intro i
    by_cases hi : sqMatrixRowProbability a i = 0
    · simp only [sqMatrixColumnProbability, if_pos hi]
      have hj : ∀ j : Fin n, j.val = 0 ↔ j = j0 := by
        intro j
        simpa only [j0] using! (Fin.ext_iff (a := j) (b := j0)).symm
      simp_rw [hj]
      simp
    · simp only [sqMatrixColumnProbability, if_neg hi]
      rw [← Finset.sum_div]
      exact div_self hi
  let cols : Fin n → FinDist (Fin n) := fun i =>
    ⟨sqMatrixColumnProbability a i, hcolnn i, hcolsum i⟩
  refine ⟨rows, cols, fun i j => ⟨rfl, rfl, ?_⟩⟩
  change a.samples.prob (i,j) = sqMatrixRowProbability a i * sqMatrixColumnProbability a i j
  by_cases hi : sqMatrixRowProbability a i = 0
  · have hz : a.samples.prob (i,j) = 0 := by
      have hle : a.samples.prob (i,j) ≤ sqMatrixRowProbability a i :=
        Finset.single_le_sum (fun k _ => a.samples.nonneg _) (Finset.mem_univ j)
      exact le_antisymm (hi ▸ hle) (a.samples.nonneg _)
    simp [hi, hz]
  · simp [sqMatrixColumnProbability, hi, mul_div_cancel₀ _ hi]

theorem sqInnerTarget_matrix_trace {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (A B : Operator n) (hB : ∀ p, a.target p = B p.1 p.2) :
    sqInnerTarget a.target (fun p => A p.1 p.2) = Matrix.trace (A*Bᴴ) := by
  simp only [sqInnerTarget, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, hB, mul_comm]

theorem sqInnerTarget_bilinear {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (A : Operator n) (hA : ∀ p, a.target p = A p.1 p.2) (x y : Fin n → ℂ) :
    sqInnerTarget a.target (fun p => x p.1 * star (y p.2)) =
      star (∑ i, ∑ j, star (x i)*A i j*y j) := by
  simp only [sqInnerTarget, Fintype.sum_prod_type, hA, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sqSquaredNorm_outer {n : ℕ} (x y : Fin n → ℂ) :
    sqSquaredNorm (fun p : Fin n × Fin n => x p.1*star (y p.2)) =
      sqSquaredNorm x * sqSquaredNorm y := by
  simp only [sqSquaredNorm, Fintype.sum_prod_type, Complex.normSq_mul,
    Complex.star_def, Complex.normSq_conj, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem sq_matrix_calls_counts (xs : List SQCall) :
    (xs.flatMap (fun c => if c = .sampleEnvelope then [.sampleRow,.sampleColumn] else [c])).count .sampleRow =
      xs.count .sampleEnvelope + xs.count .sampleRow ∧
    (xs.flatMap (fun c => if c = .sampleEnvelope then [.sampleRow,.sampleColumn] else [c])).count .sampleColumn =
      xs.count .sampleEnvelope + xs.count .sampleColumn := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    cases c <;> simp_all [List.flatMap_cons] <;> omega

theorem sqMatrixRunCalls_counts {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (A : Operator n) (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin n × Fin n) :
    (sqMatrixRunCalls a A m r ω).count .sampleRow = (2*r+1)*m ∧
    (sqMatrixRunCalls a A m r ω).count .sampleColumn = (2*r+1)*m := by
  have h := sq_matrix_calls_counts (sqRunCalls a (fun p => A p.1 p.2) m r ω)
  simpa [sqMatrixRunCalls, sqRunCalls_count] using! h

theorem finite_sq_matrix_trace_same_record_and_query_consumer (n : ℕ)
    (a : FiniteSQInput (Fin n × Fin n)) (A B : Operator n)
    (hB : ∀ p, a.target p = B p.1 p.2) (m r : ℕ) (ε : ℝ)
    (ω : Fin (2*r+1) → Fin m → Fin n × Fin n) :
    (∃ (rows : FinDist (Fin n)) (cols : Fin n → FinDist (Fin n)),
      ∀ i j, rows.prob i = sqMatrixRowProbability a i ∧
        (cols i).prob j = sqMatrixColumnProbability a i j ∧
        a.samples.prob (i,j) = rows.prob i * (cols i).prob j) ∧
    sqInnerTarget a.target (fun p => A p.1 p.2) = Matrix.trace (A*Bᴴ) ∧
    (sqMatrixRunCalls a A m r ω).count .sampleRow = (2*r+1)*m ∧
    (sqMatrixRunCalls a A m r ω).count .sampleColumn = (2*r+1)*m ∧
    (0 < m → 0 < ε →
      64*sqSquaredNorm a.envelope*sqSquaredNorm (fun p : Fin n × Fin n => A p.1 p.2) ≤
        (m : ℝ)*ε^2 →
      (∑ W ∈ Finset.univ.filter (fun W : Fin (2*r+1) → Fin m → Fin n × Fin n =>
        ε < ‖sqMedian a (fun p => A p.1 p.2) m r W - Matrix.trace (A*Bᴴ)‖),
        ∏ b, a.samples.probOf (W b)) ≤ 2*(2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1)) := by
  refine ⟨sqMatrix_sampler_factorization a, sqInnerTarget_matrix_trace a A B hB,
    (sqMatrixRunCalls_counts a A m r ω).1, (sqMatrixRunCalls_counts a A m r ω).2, ?_⟩
  intro hm hε hb
  simpa only [sqBadMass, sqInnerTarget_matrix_trace a A B hB] using!
    finite_sq_component_median_complex_guarantee _ a (fun p => A p.1 p.2) m r ε hm hε hb

private theorem sq_bilinear_calls_counts (xs : List SQCall) :
    let ys := xs.flatMap (fun c => if c = .sampleEnvelope then [.sampleRow,.sampleColumn] else
      if c = .otherEntry then [.leftVectorEntry,.rightVectorEntry] else [c])
    ys.count .sampleRow = xs.count .sampleEnvelope + xs.count .sampleRow ∧
    ys.count .sampleColumn = xs.count .sampleEnvelope + xs.count .sampleColumn ∧
    ys.count .leftVectorEntry = xs.count .otherEntry + xs.count .leftVectorEntry ∧
    ys.count .rightVectorEntry = xs.count .otherEntry + xs.count .rightVectorEntry := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    cases c <;> simp_all [List.flatMap_cons] <;> omega

theorem sqBilinearRunCalls_counts {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (x y : Fin n → ℂ) (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin n × Fin n) :
    (sqBilinearRunCalls a x y m r ω).count .sampleRow = (2*r+1)*m ∧
    (sqBilinearRunCalls a x y m r ω).count .sampleColumn = (2*r+1)*m ∧
    (sqBilinearRunCalls a x y m r ω).count .leftVectorEntry = (2*r+1)*m ∧
    (sqBilinearRunCalls a x y m r ω).count .rightVectorEntry = (2*r+1)*m := by
  have h := sq_bilinear_calls_counts (sqRunCalls a (fun p => x p.1 * star (y p.2)) m r ω)
  simpa [sqBilinearRunCalls, sqRunCalls_count] using! h

theorem finite_sq_bilinear_query_consumer (n : ℕ) (a : FiniteSQInput (Fin n × Fin n))
    (A : Operator n) (hA : ∀ p, a.target p = A p.1 p.2) (x y : Fin n → ℂ)
    (m r : ℕ) (ε : ℝ) (ω : Fin (2*r+1) → Fin m → Fin n × Fin n) :
    sqInnerTarget a.target (fun p => x p.1*star (y p.2)) =
      star (∑ i, ∑ j, star (x i)*A i j*y j) ∧
    sqSquaredNorm (fun p : Fin n × Fin n => x p.1*star (y p.2)) = sqSquaredNorm x*sqSquaredNorm y ∧
    (sqBilinearRunCalls a x y m r ω).count .leftVectorEntry = (2*r+1)*m ∧
    (sqBilinearRunCalls a x y m r ω).count .rightVectorEntry = (2*r+1)*m ∧
    (sqBilinearRunCalls a x y m r ω).count .sampleRow = (2*r+1)*m ∧
    (sqBilinearRunCalls a x y m r ω).count .sampleColumn = (2*r+1)*m ∧
    (0 < m → 0 < ε →
      64*sqSquaredNorm a.envelope*sqSquaredNorm x*sqSquaredNorm y ≤ (m : ℝ)*ε^2 →
      (∑ W ∈ Finset.univ.filter (fun W : Fin (2*r+1) → Fin m → Fin n × Fin n =>
        ε < ‖sqBilinearEstimate a x y m r W - (∑ i, ∑ j, star (x i)*A i j*y j)‖),
        ∏ b, a.samples.probOf (W b)) ≤ 2*(2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1)) := by
  have hc := sqBilinearRunCalls_counts a x y m r ω
  refine ⟨sqInnerTarget_bilinear a A hA x y, sqSquaredNorm_outer x y,
    hc.2.2.1, hc.2.2.2, hc.1, hc.2.1, ?_⟩
  intro hm hε hb
  have hbudget : 64*sqSquaredNorm a.envelope*
      sqSquaredNorm (fun p : Fin n × Fin n => x p.1*star (y p.2)) ≤ (m : ℝ)*ε^2 := by
    simpa only [sqSquaredNorm_outer, mul_assoc] using! hb
  have h := finite_sq_component_median_complex_guarantee _ a
    (fun p => x p.1*star (y p.2)) m r ε hm hε hbudget
  unfold sqBadMass at h
  have heq : ∀ W : Fin (2*r+1) → Fin m → Fin n × Fin n,
      ‖sqBilinearEstimate a x y m r W - (∑ i, ∑ j, star (x i)*A i j*y j)‖ =
      ‖sqMedian a (fun p => x p.1*star (y p.2)) m r W -
        sqInnerTarget a.target (fun p => x p.1*star (y p.2))‖ := by
    intro W
    rw [sqInnerTarget_bilinear a A hA x y]
    unfold sqBilinearEstimate
    rw [← norm_star, star_sub, star_star]
  simpa only [heq] using! h

noncomputable def sqConsumerInput : FiniteSQInput (Fin 2 × Fin 2) where
  target p := sqConsumerB p.1 p.2
  envelope _ := 2
  samples := {
    prob := fun _ => 1/4
    nonneg := fun _ => by norm_num
    sum_one := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two] }
  cachedEnvelopeSquaredNorm := 16
  norm_spec := by norm_num [sqSquaredNorm, Fintype.sum_prod_type, Fin.sum_univ_two]
  envelope_pos := by norm_num [sqSquaredNorm, Fintype.sum_prod_type, Fin.sum_univ_two]
  domination := by
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> norm_num [sqConsumerB, Complex.normSq_apply]
  sample_spec := by
    intro p
    norm_num [sqSquaredNorm, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem finite_sq_nonreal_two_matrix_consumer :
    ∃ a : FiniteSQInput (Fin 2 × Fin 2),
      (∀ p, a.target p = sqConsumerB p.1 p.2) ∧ (∀ p, a.envelope p = 2) ∧
      (∀ p, a.samples.prob p = 1/4) ∧
      sqInnerTarget a.target (fun p => sqConsumerA p.1 p.2) = 3+Complex.I ∧
      (∀ (m r : ℕ) (ε : ℝ), 0 < m → 0 < ε → (3072 : ℝ) ≤ (m : ℝ)*ε^2 →
        sqBadMass a (fun p => sqConsumerA p.1 p.2) m r ε ≤
          2*(2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1)) := by
  refine ⟨sqConsumerInput, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · norm_num [sqInnerTarget, sqConsumerInput, sqConsumerA, sqConsumerB,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    apply Complex.ext <;> norm_num
  · intro m r ε hm hε hb
    apply finite_sq_component_median_complex_guarantee _ sqConsumerInput
      (fun p => sqConsumerA p.1 p.2) m r ε hm hε
    convert! hb using 1
    norm_num [sqSquaredNorm, sqConsumerInput, sqConsumerA,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]

end Qatlib.Concepts.SqEstimation.TraceBilinear
