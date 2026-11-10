/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.GramAction.SketchGramAction
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.SketchArith.GramAction

namespace Qatlib.Concepts.SketchArith.ResidualRidge
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def sketchAugment {K : Type} {n : ℕ} (A : Matrix K (Fin n) ℂ) (b : K  → ℂ) :
    Matrix K (Fin (n+1)) ℂ := fun i j => if h : j.val < n then A i ⟨j.val,h⟩ else b i

noncomputable def sketchAugmentedVector {n : ℕ} (x : QState (Fin n)) : QState (Fin (n+1)) :=
  fun j => if h : j.val < n then x ⟨j.val,h⟩ else -1

noncomputable def sketchResidualValue {K : Type} {n r : ℕ} (d : Fin r  → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (b : K  → ℂ) (x : QState (Fin n)) (lam : ℝ) : ℝ :=
  (∑ t : Fin r,Complex.normSq
    ((d t).2*((∑ j : Fin n,A (d t).1 j*x j)-b (d t).1)))+
    lam*‖toEuclidean_fromVec x‖^2

theorem sketchAugment_mulVec {K : Type} {n : ℕ} (A : Matrix K (Fin n) ℂ) (b : K → ℂ)
    (x : QState (Fin n)) : sketchAugment A b *ᵥ sketchAugmentedVector x=A*ᵥ x-b := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, sketchAugment, sketchAugmentedVector,
      sub_eq_add_neg]

theorem sketchAugmentedVector_norm {n : ℕ} (x : QState (Fin n)) :
    ‖toEuclidean_fromVec (sketchAugmentedVector x)‖^2=‖toEuclidean_fromVec x‖^2+1 := by
  simp [norm_toEuclidean_fromVec_sq, Fin.sum_univ_castSucc, sketchAugmentedVector]

theorem sketch_inner_mulVec {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J ℂ) (v : QState I) (w : QState J) :
    Qatlib.Foundations.PureStateMath.Inner v (A*ᵥ w)=Qatlib.Foundations.PureStateMath.Inner (Aᴴ*ᵥ v) w := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

theorem sketch_gram_inner_energy {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J ℂ) (v : QState J) :
    (Qatlib.Foundations.PureStateMath.Inner v (Aᴴ*ᵥ (A*ᵥ v))).re=‖toEuclidean_fromVec (A*ᵥ v)‖^2 := by
  rw [sketch_inner_mulVec, Matrix.conjTranspose_conjTranspose, norm_toEuclidean_sq_eq_re_inner]

theorem sketch_residual_row {K : Type} {n r : ℕ} (d : Fin r → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (b : K → ℂ) (x : QState (Fin n)) (t : Fin r) :
    ((compactSketched d (sketchAugment A b))*ᵥ sketchAugmentedVector x) t=
      (d t).2*((A*ᵥ x) (d t).1-b (d t).1) := by
  have hs : ((compactSketched d (sketchAugment A b))*ᵥ sketchAugmentedVector x) t =
      (d t).2*((sketchAugment A b)*ᵥ sketchAugmentedVector x) (d t).1 := by
    simp [compactSketched, compactSketchEntry, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_assoc]
  rw [hs, sketchAugment_mulVec]
  rfl

theorem sketch_residual_actual_augmented_gram :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (n r : ℕ) (d : Fin r → K × ℝ)
      (A : Matrix K (Fin n) ℂ) (b : K → ℂ) (x : QState (Fin n)) (lam : ℝ),
      let Z := sketchAugment A b
      let v := sketchAugmentedVector x
      sketchResidualValue d A b x lam=(Qatlib.Foundations.PureStateMath.Inner v ((compactSketched d Z)ᴴ*ᵥ ((compactSketched d Z)*ᵥ v))).re+
        lam*‖toEuclidean_fromVec x‖^2 ∧
      ‖toEuclidean_fromVec v‖^2=‖toEuclidean_fromVec x‖^2+1 := by
  intro K _ _ n r d A b x lam
  (try dsimp only)
  refine ⟨?_, sketchAugmentedVector_norm x⟩
  rw [sketch_gram_inner_energy, norm_toEuclidean_fromVec_sq]
  simp_rw [sketch_residual_row]
  simp only [sketchResidualValue, Complex.normSq_eq_norm_sq, Matrix.mulVec, dotProduct]

theorem sketch_residual_error_eq {K : Type} [Fintype K] [DecidableEq K] {n r : ℕ}
    (p : FinDist K) (omega : Fin r → K) (A : Matrix K (Fin n) ℂ) (b : K → ℂ)
    (x : QState (Fin n)) (lam : ℝ) :
    sketchResidualValue (compactSketchData p r omega) A b x lam-
      (‖toEuclidean_fromVec (A*ᵥ x-b)‖^2+lam*‖toEuclidean_fromVec x‖^2) =
      (Qatlib.Foundations.PureStateMath.Inner (sketchAugmentedVector x)
        ((sketchProduct p r (sketchAugment A b) (sketchAugment A b) omega -
          (sketchAugment A b)ᴴ*(sketchAugment A b))*ᵥ sketchAugmentedVector x)).re := by
  rw [(sketch_residual_actual_augmented_gram K n r (compactSketchData p r omega) A b x lam).1]
  have hp := (compact_sketch_actual_pairs_entries_and_queries K (Fin (n+1)) (Fin (n+1))
    p r (sketchAugment A b) (sketchAugment A b) omega).2.2.2.2.2
  have hsub (u w : QState (Fin (n+1))) :
      Qatlib.Foundations.PureStateMath.Inner (sketchAugmentedVector x) (u-w) =
        Qatlib.Foundations.PureStateMath.Inner (sketchAugmentedVector x) u - Qatlib.Foundations.PureStateMath.Inner (sketchAugmentedVector x) w := by
    simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.sub_apply, mul_sub,
        Finset.sum_sub_distrib]
  rw [hp, Matrix.sub_mulVec, hsub, Complex.sub_re]
  simp only [← Matrix.mulVec_mulVec]
  rw [sketch_gram_inner_energy, sketch_gram_inner_energy, sketchAugment_mulVec]
  ring

theorem sketch_ridge_residual_uniform_same_record_bound :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (n r : ℕ) (p : FinDist K)
      (A : Matrix K (Fin n) ℂ) (b : K → ℂ) (lam phi eps : ℝ), 0 < r → 1 ≤ phi → 0 < eps →
      0 < sketchSquared (sketchAugment A b) →
      (∀ i, sketchRowSquared (sketchAugment A b) i/(phi*sketchSquared (sketchAugment A b)) ≤ p.prob i) →
      (∑ omega ∈ Finset.univ.filter (fun omega : Fin r → K => ∃ x : QState (Fin n),
        eps*(‖toEuclidean_fromVec x‖^2+1) < |sketchResidualValue (compactSketchData p r omega) A b x lam-
          (‖toEuclidean_fromVec (A*ᵥ x-b)‖^2+lam*‖toEuclidean_fromVec x‖^2)|), p.probOf omega) ≤
        phi*(sketchSquared (sketchAugment A b))^2/(r*eps^2) := by
  intro K _ _ n r p A b lam phi eps hr hphi heps hZ hdom
  apply sketch_gram_energy_event_bound (n+1) r p (sketchAugment A b) phi eps hr hphi heps hZ hdom
  intro omega ho
  obtain ⟨x,hbad⟩ := ho
  by_contra h
  have hb := sketch_rayleigh_of_energy_le
    (sketchProduct p r (sketchAugment A b) (sketchAugment A b) omega-(sketchAugment A b)ᴴ*(sketchAugment A b))
    (sketchAugmentedVector x) eps heps (le_of_not_gt h)
  rw [sketchAugmentedVector_norm, ← sketch_residual_error_eq p omega A b x lam] at hb
  exact not_lt_of_ge hb hbad

theorem sketch_gram_reused_word_and_augmented_query_ledger :
    ∀ (K : Type) (n r : ℕ) (d : Fin r → K × ℝ) (A : Matrix K (Fin n) ℂ)
      (b : K → ℂ) (x : QState (Fin n)),
      ((List.finRange r).map (fun t => (sketchCachedRow d (sketchAugment A b) t).length)).sum=(n+1)*r ∧
      (sketchGramCounted d A x).1=(compactSketched d A)ᴴ*ᵥ ((compactSketched d A)*ᵥ x) ∧
      ∀ q : ℕ, (List.replicate q (sketchGramCounted d A x).2.1).sum=q*n*r := by
  intro K n r d A b x
  have h := sketch_gram_actual_cached_rows_and_matrix_free_cost K n r d A x
  refine ⟨?_, h.1, ?_⟩
  · simp [sketchCachedRow_length, mul_comm]
  · intro q
    rw [h.2.1, List.sum_replicate]
    simp [mul_assoc]
end Qatlib.Concepts.SketchArith.ResidualRidge
