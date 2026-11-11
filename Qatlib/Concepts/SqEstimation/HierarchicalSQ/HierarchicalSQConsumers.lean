/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SqEstimation.HierarchicalSQ.HierarchicalSQAccess

/-!
# Hierarchical sample-and-query consumers

This module expands the product RᴴUR entrywise through `closureRUR` and bounds its entries by
`closureRUREnvelopeSq`. It also constructs a two-dimensional matrix-unit example that exhibits
cancellation and computes the output law and resource counts of the hierarchical sampler. For
background, see [ChiaEtAl2022].

## Main statements

* `native_sq_rur_exact_operator_and_cancellation`: identifies RᴴUR, computes its envelope norm,
  and gives a cancellation example.
* `native_sq_rur_same_record_sampler_and_cost`: computes the finite and unbounded sampling laws
  and expected costs for four matrix units.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

set_option autoImplicit false
open Matrix
open scoped Classical BigOperators ENNReal ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.SqEstimation.HierarchicalSQ

/-- The entrywise double-sum expansion of the matrix product RᴴUR. -/
noncomputable def closureRUR {r n : ℕ} (R : Matrix (Fin r) (Fin n) ℂ) (U : Operator r) : Operator n :=
  fun i j => ∑ a, ∑ b, star (R a i)*U a b*R b j
/-- The entrywise squared envelope obtained by multiplying the sum of squared summands in RᴴUR
by r². -/
noncomputable def closureRUREnvelopeSq {r n : ℕ} (R : Matrix (Fin r) (Fin n) ℂ) (U : Operator r) :
    Fin n → Fin n → ℝ :=
  fun i j => (r*r:ℕ)*∑ a, ∑ b, Complex.normSq (star (R a i)*U a b*R b j)
/-- The finite point-mass distribution at `x`, constructed by a constant pushforward of a native
coin distribution. -/
noncomputable def closureDelta {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (x : X) : FinDist X :=
  Classical.choose (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pushforward (rand.coin 0) (fun _ => x))
/-- The two-dimensional matrix unit whose row and column indices are encoded by `t`. -/
noncomputable def closureBasisOuter (t : Fin 4) : Operator 2 :=
  fun i j => if (i,j)=(finProdFinEquiv.symm t : Fin 2 × Fin 2) then 1 else 0
/-- The squared row norm of the matrix unit indexed by `t`, equal to one on its selected row and
zero elsewhere. -/
noncomputable def closureBasisRowNorm (t : Fin 4) (i : Fin 2) : ℝ :=
  if i=(finProdFinEquiv.symm t : Fin 2 × Fin 2).1 then 1 else 0
/-- The point-mass row sampler for the matrix unit indexed by `t`. -/
noncomputable def closureBasisRows (rand : ClosureNativeRandom) (t : Fin 4) : FinDist (Fin 2) :=
  closureDelta rand (finProdFinEquiv.symm t : Fin 2 × Fin 2).1
/-- The point-mass column sampler for the matrix unit indexed by `t`, independent of the
supplied row. -/
noncomputable def closureBasisCols (rand : ClosureNativeRandom) (t : Fin 4) (_i : Fin 2) : FinDist (Fin 2) :=
  closureDelta rand (finProdFinEquiv.symm t : Fin 2 × Fin 2).2

/-- Each squared entry norm of `closureRUR R U` is bounded by `closureRUREnvelopeSq R U`. -/
private theorem closure_rur_bound (r n : ℕ) (R : Matrix (Fin r) (Fin n) ℂ) (U : Operator r)
    (i j : Fin n) : Complex.normSq (closureRUR R U i j) ≤ closureRUREnvelopeSq R U i j := by
  have h := closure_complex_sum_bound (fun p : Fin r × Fin r => star (R p.1 i)*U p.1 p.2*R p.2 j)
  simpa only [closureRUR, closureRUREnvelopeSq, Fintype.sum_prod_type,
    Fintype.card_prod, Fintype.card_fin] using h

/-- The squared envelope for RᴴUR is nonnegative at every entry. -/
private theorem closure_rur_envelope_nonneg {r n : ℕ} (R : Matrix (Fin r) (Fin n) ℂ)
    (U : Operator r) (i j : Fin n) : 0 ≤ closureRUREnvelopeSq R U i j := by
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- The squared Frobenius norm of the square-root envelope equals r² times the sum of |U a b|²
weighted by the squared norms of rows `a` and `b` of `R`. -/
private theorem closure_rur_frob (r n : ℕ) (R : Matrix (Fin r) (Fin n) ℂ) (U : Operator r) :
    closureFrobSq (fun i j => (Real.sqrt (closureRUREnvelopeSq R U i j) : ℂ)) =
      (r*r : ℕ)*∑ a, ∑ b, Complex.normSq (U a b)*closureRowSq R a*closureRowSq R b := by
  have he (i j : Fin n) : Complex.normSq (Real.sqrt (closureRUREnvelopeSq R U i j) : ℂ) =
      closureRUREnvelopeSq R U i j := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (closure_rur_envelope_nonneg R U i j)]
  unfold closureFrobSq closureRowSq
  simp_rw [he, closureRUREnvelopeSq]
  simp_rw [← Finset.mul_sum]
  congr 1
  let f : Fin r → Fin r → Fin n → Fin n → ℝ := fun a b i j =>
    Complex.normSq (star (R a i)*U a b*R b j)
  change (∑ i, ∑ j, ∑ a, ∑ b, f a b i j) = _
  calc _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ i, ∑ j, f a b i j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          simp only [f, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          ring

/-- Identifies `closureRUR` with RᴴUR and proves its entrywise envelope bound and envelope norm
formula. A two-term example has zero target matrix but total squared envelope eight,
illustrating cancellation in the closure construction of [ChiaEtAl2022]. -/
theorem native_sq_rur_exact_operator_and_cancellation (r n : ℕ)
    (R : Matrix (Fin r) (Fin n) ℂ) (U : Operator r) :
    closureRUR R U = Rᴴ*U*R ∧
    (∀ i j, Complex.normSq (closureRUR R U i j) ≤ closureRUREnvelopeSq R U i j) ∧
    closureFrobSq (fun i j => (Real.sqrt (closureRUREnvelopeSq R U i j) : ℂ)) =
      (r*r : ℕ)*∑ a, ∑ b, Complex.normSq (U a b)*closureRowSq R a*closureRowSq R b ∧
    closureMatrixTarget (![1,-1] : Fin 2 → ℂ) (fun _ => (1 : Operator 2)) = 0 ∧
    (∑ i : Fin 2, ∑ j : Fin 2,
      closureMatrixEnvelopeSq (![1,-1] : Fin 2 → ℂ) (fun _ => (1 : Operator 2)) i j) = 8 := by
  refine ⟨?_, closure_rur_bound r n R U, closure_rur_frob r n R U, ?_, ?_⟩
  · ext i j
    simp only [closureRUR, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  · ext i j
    simp [closureMatrixTarget, Fin.sum_univ_two]
  · norm_num [closureMatrixEnvelopeSq, Fin.sum_univ_two]

/-- The point mass `closureDelta rand x` assigns probability one to `x` and zero to every other
value. -/
private theorem closureDelta_prob {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (x y : X) : (closureDelta rand x).prob y = if y = x then 1 else 0 := by
  have h :=
      Classical.choose_spec
      (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pushforward (rand.coin 0) (fun _ => x)) y
  change (closureDelta rand x).prob y = _ at h
  rw [h]
  by_cases hy : y = x
  · subst y
    simpa using (rand.coin 0).sum_one
  · simp [hy, Ne.symm hy]

/-- Each of the four matrix units has squared Frobenius norm one, the specified squared row
norms, and exact row and conditional column sampling laws. -/
private theorem closure_basis_source (rand : ClosureNativeRandom) :
    ∀ t : Fin 4, (0 : ℝ) < 1 ∧ (1 : ℝ) = closureFrobSq (closureBasisOuter t) ∧
      (∀ i, closureBasisRowNorm t i = closureRowSq (closureBasisOuter t) i) ∧
      (∀ i j, Complex.normSq (closureBasisOuter t i j) ≤ Complex.normSq (closureBasisOuter t i j)) ∧
      (∀ i, (closureBasisRows rand t).prob i = closureRowSq (closureBasisOuter t) i/1) ∧
      (∀ i j, 0 < closureRowSq (closureBasisOuter t) i →
        (closureBasisCols rand t i).prob j =
          Complex.normSq (closureBasisOuter t i j)/closureRowSq (closureBasisOuter t) i) := by
  intro t
  refine ⟨by norm_num, ?_, ?_, fun _ _ => le_refl _, ?_, ?_⟩
  · fin_cases t <;> simp only [closureFrobSq, closureRowSq, Fin.sum_univ_two] <;>
      norm_num [closureBasisOuter, finProdFinEquiv, Fin.divNat, Fin.modNat]
  · intro i
    fin_cases t <;> fin_cases i <;> simp only [closureRowSq, Fin.sum_univ_two] <;>
      norm_num [closureBasisRowNorm, closureRowSq, closureBasisOuter, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_two]
  · intro i
    fin_cases t <;> fin_cases i <;> simp only [closureRowSq, Fin.sum_univ_two] <;>
      norm_num [closureBasisRows, closureDelta_prob, closureRowSq, closureBasisOuter, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_two]
  · intro i j hi
    fin_cases t <;> fin_cases i <;> fin_cases j <;> simp only [closureRowSq, Fin.sum_univ_two] at hi ⊢ <;>
      norm_num [closureBasisCols, closureDelta_prob, closureRowSq, closureBasisOuter, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_two] at hi <;>
      norm_num [closureBasisCols, closureDelta_prob, closureRowSq, closureBasisOuter, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_two]

/-- The sum of the four two-dimensional matrix units with unit coefficients is the all-ones
matrix. -/
private theorem closure_basis_target :
    closureMatrixTarget (fun _ : Fin 4 => (1 : ℂ)) closureBasisOuter = (fun _ _ => 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [closureMatrixTarget, Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals norm_num [closureBasisOuter, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_succ]

/-- The squared hierarchical envelope for the four matrix units with unit coefficients is four
at every entry. -/
private theorem closure_basis_envelope (i j : Fin 2) :
    closureMatrixEnvelopeSq (fun _ : Fin 4 => (1 : ℂ)) closureBasisOuter i j = 4 := by
  fin_cases i <;> fin_cases j <;>
    simp only [closureMatrixEnvelopeSq, Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals norm_num [closureBasisOuter, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_succ]

/-- The global coefficient weights of the four matrix units with unit coefficients and unit norm
bounds are all one. -/
private theorem closure_basis_global_weights : closureWeights (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) =
    (fun _ => (1 : ℝ)) := by funext t; norm_num [closureWeights]

/-- The global coefficient-choice acceptance rate for the four equally weighted matrix units is
one. -/
private theorem closure_basis_global_rate :
    closureRate (closureWeights (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1)) = 1 := by
  rw [closure_basis_global_weights]
  norm_num [closureRate, closureSum, closureMax, List.ofFn_succ, List.foldl]

/-- For each row, the sum of the row coefficient weights of the four matrix units is two. -/
private theorem closure_basis_row_sum (i : Fin 2) :
    closureSum (closureRowWeights (fun _ : Fin 4 => (1 : ℂ)) closureBasisRowNorm i) = 2 := by
  fin_cases i <;>
    simp only [closureSum, Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals norm_num [closureRowWeights, closureBasisRowNorm, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_succ]

/-- For each row, the maximum row coefficient weight of the four matrix units is one. -/
private theorem closure_basis_row_max (i : Fin 2) :
    closureMax (closureRowWeights (fun _ : Fin 4 => (1 : ℂ)) closureBasisRowNorm i) = 1 := by
  fin_cases i <;>
    norm_num [closureMax, closureRowWeights, closureBasisRowNorm, finProdFinEquiv, Fin.divNat, Fin.modNat, List.ofFn_succ, List.foldl]

/-- For each row, the coefficient-choice acceptance rate for the four matrix units is one half. -/
private theorem closure_basis_row_rate (i : Fin 2) :
    closureRate (closureRowWeights (fun _ : Fin 4 => (1 : ℂ)) closureBasisRowNorm i) = 1/2 := by
  rw [closureRate, closure_basis_row_sum, closure_basis_row_max]
  norm_num

/-- All global coefficient weights in the four-matrix-unit example are nonnegative. -/
private theorem closure_basis_global_nonneg : ∀ t,
    0 ≤ closureWeights (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) t := by
  intro t
  norm_num [closureWeights]

/-- The sum of the global coefficient weights in the four-matrix-unit example is positive. -/
private theorem closure_basis_global_pos :
    0 < closureSum (closureWeights (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1)) := by
  norm_num [closureSum, closureWeights]

/-- All row coefficient weights in the four-matrix-unit example are nonnegative. -/
private theorem closure_basis_row_nonneg (i : Fin 2) : ∀ t,
    0 ≤ closureRowWeights (fun _ : Fin 4 => (1 : ℂ)) closureBasisRowNorm i t := by
  intro t
  unfold closureRowWeights closureBasisRowNorm
  split_ifs <;> norm_num

/-- Computes the target, envelope, and finite output masses for the four-matrix-unit example;
the unbounded sampler is uniform on the four entries. Its expected counts are three
coefficient attempts, six random calls, and two native sampling calls, providing a concrete
closure example for [ChiaEtAl2022]. -/
theorem native_sq_rur_same_record_sampler_and_cost (rand : ClosureNativeRandom) :
    closureMatrixTarget (fun _ : Fin 4 => (1 : ℂ)) closureBasisOuter = (fun _ _ => 1) ∧
    (∀ i j, closureMatrixEnvelopeSq (fun _ : Fin 4 => (1 : ℂ)) closureBasisOuter i j = 4) ∧
    (∀ Trow Tcol (i j : Fin 2),
      closureMatrixMass rand (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) closureBasisRowNorm
        (closureBasisRows rand) (closureBasisCols rand) Trow Tcol i j =
          if Trow = 0 then 0 else (1-(1/2 : ℝ)^Tcol)/4) ∧
    (∀ i j, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (closureMatrixUnboundedDraw rand (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) closureBasisRowNorm
        (closureBasisRows rand) (closureBasisCols rand)) (fun z => z.1 = some (i,j))).toReal = 1/4) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (closureMatrixUnboundedDraw rand (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) closureBasisRowNorm
        (closureBasisRows rand) (closureBasisCols rand)) (fun z => (z.2.1 : ℝ≥0∞)) = 3 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (closureMatrixUnboundedDraw rand (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) closureBasisRowNorm
        (closureBasisRows rand) (closureBasisCols rand)) (fun z => (closureDrawRandomCalls z : ℝ≥0∞)) = 6 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (closureMatrixUnboundedDraw rand (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) closureBasisRowNorm
        (closureBasisRows rand) (closureBasisCols rand)) (fun z => (z.2.2.1 : ℝ≥0∞)) = 2 := by
  let coeff := fun _ : Fin 4 => (1 : ℂ)
  let W := fun _ : Fin 4 => (1 : ℝ)
  let p := closureUnboundedDraw rand (closureWeights coeff W) (closureBasisRows rand)
  let cp := fun i => closureUnboundedDraw rand (closureRowWeights coeff closureBasisRowNorm i)
    (fun t => closureBasisCols rand t i)
  have hnone : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none) = 0 :=
    closureUnboundedDraw_none rand _ _ closure_basis_global_nonneg closure_basis_global_pos
  have hg := native_sq_hierarchical_matrix_lcu_actual_access 4 2 2 rand coeff
    closureBasisOuter closureBasisOuter W closureBasisRowNorm (closureBasisRows rand) (closureBasisCols rand) 0 0
    (closure_basis_source rand) closure_basis_global_pos
  have hattempt : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (closureMatrixUnboundedDraw rand coeff W closureBasisRowNorm (closureBasisRows rand) (closureBasisCols rand))
      (fun z => (z.2.1 : ℝ≥0∞)) = 3 := by
    rw [closureMatrixUnboundedDraw_prepare]
    have heq := closureMatrixCompose_expectation p cp (fun _ => 4)
      (fun c : ℕ × ℕ × ℕ => (c.1 : ℝ≥0∞)) (by intro c d; simp [Nat.cast_add])
    simp only [Nat.cast_zero, add_zero] at heq
    rw [heq, closureUnboundedDraw_attempts,
      (closure_choice_unbounded_time rand _ closure_basis_global_nonneg closure_basis_global_pos).2.2,
      closure_basis_global_rate]
    norm_num
    have hlocal (i : Fin 2) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (cp i) (fun y => (y.2.1 : ℝ≥0∞)) = 2 := by
      rw [closureUnboundedDraw_attempts,
        (closure_choice_unbounded_time rand _ (closure_basis_row_nonneg i)
          (by rw [closure_basis_row_sum]; norm_num)).2.2, closure_basis_row_rate]
      norm_num
    have hselected : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with
        | none => 0 | some i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (cp i) (fun y => (y.2.1 : ℝ≥0∞))) = 2 := by
      simp_rw [hlocal]
      convert closure_expectation_some_const p hnone 2 using 1
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro z
      cases z.1 <;> simp
    have hend := congrArg (fun c : ℝ≥0∞ => 1+c) hselected
    convert hend using 1 <;> try norm_num
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro z
    cases z.1 with
    | none => rfl
    | some i =>
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      rintro ⟨o,k,reads,queries⟩
      rfl
  refine ⟨closure_basis_target, closure_basis_envelope, ?_, ?_, hattempt, ?_,
      hg.2.2.2.2.2.2.2.2.2.1⟩
  · intro Trow Tcol i j
    have hcap := native_sq_hierarchical_matrix_lcu_actual_access 4 2 2 rand coeff
      closureBasisOuter closureBasisOuter W closureBasisRowNorm (closureBasisRows rand) (closureBasisCols rand) Trow Tcol
      (closure_basis_source rand) closure_basis_global_pos
    rw [hcap.2.2.2.1 i j, closure_basis_envelope]
    have hmax : closureMax (closureWeights coeff W) = 1 := by
      rw [closure_basis_global_weights]
      norm_num [closureMax, List.ofFn_succ, List.foldl]
    have hrowmax : closureMax (closureRowWeights coeff closureBasisRowNorm i) = 1 :=
        closure_basis_row_max i
    have hglobalrate : closureRate (closureWeights coeff W) = 1 := closure_basis_global_rate
    have hrowrate : closureRate (closureRowWeights coeff closureBasisRowNorm i) = 1/2 :=
        closure_basis_row_rate i
    simp only [closureSuccess, hmax, hrowmax, one_ne_zero, if_false, hglobalrate, hrowrate]
    norm_num [closureSum, closureWeights]
    by_cases ht : Trow = 0
    · simp [ht]
    · simp [ht]
      ring
  · intro i j
    rw [hg.2.2.2.2.2.1 i j, closure_basis_envelope]
    norm_num [closureSum, closureWeights]
  · have heq : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (closureMatrixUnboundedDraw rand coeff W closureBasisRowNorm (closureBasisRows rand) (closureBasisCols rand))
        (fun z => (closureDrawRandomCalls z : ℝ≥0∞)) =
        2*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
          (closureMatrixUnboundedDraw rand coeff W closureBasisRowNorm (closureBasisRows rand) (closureBasisCols rand))
          (fun z => (z.2.1 : ℝ≥0∞)) := by
      rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro z
      simp [closureDrawRandomCalls, Nat.cast_mul]
    rw [heq, hattempt]
    norm_num

end Qatlib.Concepts.SqEstimation.HierarchicalSQ
