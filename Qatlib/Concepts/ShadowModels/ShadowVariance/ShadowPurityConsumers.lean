/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.QuadraticPauliShadows
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowVariance

open Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false

noncomputable def tensorPurityMedian (n L K : ℕ)
    (ω : Fin K → Fin L → Fin n → Fin 3 × Bool) : ℝ :=
  (insertionSortCounted (List.ofFn (fun k => tensorPurityU n (ω k)))).1.getD (K / 2) 0

theorem tensor_purity_same_born_records_median_bound (n L r : ℕ)
    (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ) (ε : ℝ) (hL : 2 ≤ L) (hε : 0 < ε)
    (hbudget : 16 * (4 * (5 : ℝ) ^ n / (L : ℝ) +
      2 * (25 : ℝ) ^ n / ((L : ℝ) * (L - 1 : ℕ))) ≤ ε ^ 2) :
    let p := tensorPauliLaw n ρ hρ
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2 * r + 1) → Fin L → Fin n → Fin 3 × Bool =>
      ε < |tensorPurityMedian n L (2 * r + 1) ω - (Matrix.trace (ρ * ρ)).re|),
        ∏ k, p.probOf (ω k)) ≤ (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ (r + 1) := by
  classical
  (try dsimp only)
  let p := tensorPauliLaw n ρ hρ
  let θ := (Matrix.trace (ρ * ρ)).re
  let Y := Fin L → Fin n → Fin 3 × Bool
  let q : FinDist Y :=
    { prob := p.probOf
      nonneg := fun ω => Finset.prod_nonneg fun _ _ => p.nonneg _
      sum_one := p.sum_probOf L }
  have hU (ω : Y) : tensorPurityU n ω = pairUStatistic (tensorPurityKernel n) ω :=
    (finite_pair_u_statistic_actual_value_and_count _ L _ ω).1
  have hμ : q.expect (tensorPurityU n) = θ := by
    simp only [FinDist.expect, q, hU]
    rw [finite_pair_u_statistic_unbiased _ p L _ hL]
    exact (tensor_purity_actual_pair_kernel_and_mean n (fun _ => (0, false))
      (fun _ => (0, false))).2.2 ρ hρ
  have hv : q.expect (fun ω => (tensorPurityU n ω - q.expect (tensorPurityU n)) ^ 2) ≤ ε ^ 2 / 16 := by
    rw [hμ]
    have hh := (tensor_purity_derived_moment_and_variance_bounds n L ρ hρ hL).2.2
    exact hh.trans (by linarith)
  have hc := heterogeneous_weighted_median_concentration r 1 (fun _ _ => q)
    (fun _ _ => 1) (fun _ _ => tensorPurityU n) θ ε hε
    (fun _ => by simpa only [Fin.sum_univ_one, one_mul] using hμ)
    (fun _ => by simpa only [Fin.sum_univ_one, one_pow, one_mul] using hv)
  let e : (Fin (2 * r + 1) → Y) ≃ (Fin (2 * r + 1) → Fin 1 → Y) :=
    { toFun := fun ω j _ => ω j
      invFun := fun ω j => ω j 0
      left_inv := fun _ => rfl
      right_inv := by
        intro ω
        funext j b
        have hb : b = 0 := Subsingleton.elim _ _
        subst b
        rfl }
  have hblock (ω : Fin (2 * r + 1) → Y) :
      weightedBlock r 1 (fun _ _ => 1) (fun _ _ => tensorPurityU n) (e ω) =
        fun j => tensorPurityU n (ω j) := by
    funext j
    change (∑ _b : Fin 1, (1 : ℝ) * tensorPurityU n (ω j)) = tensorPurityU n (ω j)
    simp only [Fin.sum_univ_one, one_mul]
  have hprob (ω : Fin (2 * r + 1) → Y) :
      (blockRecordLaw r 1 (fun _ _ => q)).prob (e ω) = ∏ j, p.probOf (ω j) := by
    change (∏ j, ∏ _b : Fin 1, p.probOf (ω j)) = _
    simp only [Fin.prod_univ_one]
  rw [Finset.sum_filter] at hc ⊢
  rw [← e.sum_comp] at hc
  simp_rw [hblock, hprob] at hc
  have hdiv : (2 * r + 1) / 2 = r := by omega
  simpa only [tensorPurityMedian, sortedBlockMedian, hdiv, θ, p] using hc

theorem tensorPurityMixedDensity : IsDensityOperator ((1 / 2 : ℂ) • (1 : Operator 2)) := by
  refine ⟨Matrix.PosSemidef.smul Matrix.PosSemidef.one (by norm_num [Complex.nonneg_iff]), ?_⟩
  norm_num [Matrix.trace_smul, Matrix.trace_one]

theorem tensor_purity_real_mixed_consumer_and_work_count (L K : ℕ)
    (hρ : IsDensityOperator ((1 / 2 : ℂ) • (1 : Operator 2))) (_hL : 2 ≤ L) :
    pairKernelMean (tensorPauliLaw 1 ((1 / 2 : ℂ) • (1 : Operator 2)) hρ)
      (tensorPurityKernel 1) = 1 / 2 ∧
      ∀ ω : Fin K → Fin L → Fin 1 → Fin 3 × Bool,
        (∑ k, (pairUCounted (tensorPurityKernel 1) (ω k)).2) = K * L.choose 2 ∧
        tensorPauliFreshResourceCounts 1 L K ω = (K * L, 2 * (K * L), K * L, 0) := by
  have hm := (tensor_purity_actual_pair_kernel_and_mean 1 (fun _ => (0, false))
    (fun _ => (0, false))).2.2 ((1 / 2 : ℂ) • (1 : Operator 2)) hρ
  refine ⟨?_, ?_⟩
  · rw [hm]
    norm_num [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, Matrix.trace_one]
  · intro ω
    constructor
    · simp only [(finite_pair_u_statistic_actual_value_and_count _ L _ _).2,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    · simpa only [mul_one, one_mul] using tensorPauliFreshResourceCounts_spec 1 L K ω

theorem tensorPurityMixed_actual (L K : ℕ) (hL : 2 ≤ L) :
    pairKernelMean (tensorPauliLaw 1 ((1 / 2 : ℂ) • (1 : Operator 2)) tensorPurityMixedDensity)
      (tensorPurityKernel 1) = 1 / 2 ∧
      ∀ ω : Fin K → Fin L → Fin 1 → Fin 3 × Bool,
        (∑ k, (pairUCounted (tensorPurityKernel 1) (ω k)).2) = K * L.choose 2 ∧
        tensorPauliFreshResourceCounts 1 L K ω = (K * L, 2 * (K * L), K * L, 0) :=
  tensor_purity_real_mixed_consumer_and_work_count L K tensorPurityMixedDensity hL

def tensorPurityURationalCounted (n : ℕ) {m : ℕ}
    (ω : Fin m → Fin n → Fin 3 × Bool) : ℚ × ℕ × ℕ :=
  let a := (pairIndexList m).foldl (fun acc ij =>
    let c := tensorPurityKernelCounted n (ω ij.1) (ω ij.2)
    (acc.1 + c.1, acc.2.1 + 1, acc.2.2 + c.2)) (0, 0, 0)
  (a.1 / (m.choose 2 : ℚ), a.2)

private theorem tensorPurity_pair_fold (n m : ℕ) (ω : Fin m → Fin n → Fin 3 × Bool)
    (ps : List (Fin m × Fin m)) (acc : ℚ × ℕ × ℕ) :
    ps.foldl (fun acc ij =>
      let c := tensorPurityKernelCounted n (ω ij.1) (ω ij.2)
      (acc.1 + c.1, acc.2.1 + 1, acc.2.2 + c.2)) acc =
      (acc.1 + (ps.map (fun ij => tensorPurityKernelRational n (ω ij.1) (ω ij.2))).sum,
        acc.2.1 + ps.length, acc.2.2 + n * ps.length) := by
  induction ps generalizing acc with
  | nil => simp
  | cons ij ps ih =>
      simp [ih, (tensorPurityKernelCounted_spec n (ω ij.1) (ω ij.2)).1,
        (tensorPurityKernelCounted_spec n (ω ij.1) (ω ij.2)).2, Nat.mul_succ,
        add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem tensorPurityURationalCounted_spec (n m : ℕ)
    (ω : Fin m → Fin n → Fin 3 × Bool) :
    ((tensorPurityURationalCounted n ω).1 : ℝ) = tensorPurityU n ω ∧
      (tensorPurityURationalCounted n ω).2.1 = m.choose 2 ∧
      (tensorPurityURationalCounted n ω).2.2 = n * m.choose 2 := by
  have hsum (ps : List (Fin m × Fin m)) :
      ((ps.map (fun ij => tensorPurityKernelRational n (ω ij.1) (ω ij.2))).sum : ℝ) =
        (ps.map (fun ij => tensorPurityKernel n (ω ij.1) (ω ij.2))).sum := by
    induction ps with
    | nil => simp
    | cons ij ps ih => simp [ih, tensorPurityKernel]
  simp only [tensorPurityURationalCounted, tensorPurity_pair_fold, zero_add,
    pairIndexList_length, Rat.cast_div, Rat.cast_natCast, hsum]
  refine ⟨?_, trivial, trivial⟩
  exact (finite_pair_u_statistic_actual_value_and_count _ m (tensorPurityKernel n) ω).1.symm

theorem tensorPurityMedian_comparisons (n L K : ℕ)
    (ω : Fin K → Fin L → Fin n → Fin 3 × Bool) :
    (insertionSortCounted (List.ofFn (fun k => tensorPurityU n (ω k)))).2 ≤ K * K := by
  simpa only [List.length_ofFn] using insertionSortCounted_cost_le
    (List.ofFn (fun k => tensorPurityU n (ω k)))

theorem tensorPurityGrouped_classical_counts (n L K : ℕ)
    (ω : Fin K → Fin L → Fin n → Fin 3 × Bool) :
    (∑ k, (tensorPurityURationalCounted n (ω k)).2.1) = K * L.choose 2 ∧
      (∑ k, (tensorPurityURationalCounted n (ω k)).2.2) = K * (n * L.choose 2) := by
  simp only [(tensorPurityURationalCounted_spec n L _).2.1,
    (tensorPurityURationalCounted_spec n L _).2.2, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  exact ⟨trivial, trivial⟩

end Qatlib.Concepts.ShadowModels.ShadowVariance
