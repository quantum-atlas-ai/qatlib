/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement

open scoped BigOperators
open Finset

structure SeparableTwoQubit where
  overlap : ℝ
  traceDist : ℝ
  n : ℕ
  w : Fin n → ℝ
  prodOverlap : Fin n → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1

  prod_overlap_le : ∀ i, prodOverlap i ≤ 1 / 2

  overlap_eq : overlap = ∑ i, w i * prodOverlap i

  traceDist_lb : 2 * (1 - overlap) ≤ traceDist

theorem bell_state_witness (σ : SeparableTwoQubit) :
    σ.overlap ≤ 1 / 2 ∧ 1 ≤ σ.traceDist := by
  have hoverlap : σ.overlap ≤ 1 / 2 := by
    rw [σ.overlap_eq]
    calc ∑ i, σ.w i * σ.prodOverlap i
        ≤ ∑ i, σ.w i * (1 / 2) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact mul_le_mul_of_nonneg_left (σ.prod_overlap_le i) (σ.w_nonneg i)
      _ = (∑ i, σ.w i) * (1 / 2) := by rw [← Finset.sum_mul]
      _ = 1 / 2 := by rw [σ.w_sum]; norm_num
  refine ⟨hoverlap, ?_⟩
  have : 1 ≤ 2 * (1 - σ.overlap) := by linarith
  linarith [σ.traceDist_lb]

structure BoundedSchmidtState (D d : ℕ) where
  overlap : ℝ
  n : ℕ
  w : Fin n → ℝ
  prodOverlap : Fin n → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1

  prod_overlap_le : ∀ i, prodOverlap i ≤ (d : ℝ) / (D : ℝ)
  overlap_eq : overlap = ∑ i, w i * prodOverlap i

theorem singlet_fraction_from_schmidt
    {D d : ℕ} (hD : 0 < D) (_hDd : d ≤ D) (σ : BoundedSchmidtState D d) :
    σ.overlap ≤ (d : ℝ) / (D : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [σ.overlap_eq]
  calc ∑ i, σ.w i * σ.prodOverlap i
      ≤ ∑ i, σ.w i * ((d : ℝ) / (D : ℝ)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left (σ.prod_overlap_le i) (σ.w_nonneg i)
    _ = (∑ i, σ.w i) * ((d : ℝ) / (D : ℝ)) := by rw [← Finset.sum_mul]
    _ = (d : ℝ) / (D : ℝ) := by rw [σ.w_sum, one_mul]

theorem entanglement_contraction
    (m : ℕ) (hm : 1 ≤ m) (κN : ℝ) (hκ0 : 0 < κN) (hκ1 : κN ≤ 1)
    (Echi_before Echi_after : ℝ) (_hbefore : 0 ≤ Echi_before)
    (hRef19 : Echi_after ≤ (1 - κN ^ (m : ℝ)) * Echi_before) :
    0 ≤ 1 - κN ^ (m : ℝ) ∧
      Echi_after ≤ (1 - κN ^ (m : ℝ)) * Echi_before := by
  refine ⟨?_, hRef19⟩
  have hle : κN ^ (m : ℝ) ≤ 1 := Real.rpow_le_one hκ0.le hκ1 (by positivity)
  linarith

theorem entanglement_contraction_iterated
    (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (ms : ℕ → ℕ) (E : ℕ → ℝ)
    (_hE0 : 0 ≤ E 0)
    (hstep : ∀ i : ℕ, E (i + 1) ≤ (1 - κ ^ ((ms i : ℕ) : ℝ)) * E i) :
    ∀ n : ℕ, E n ≤ (∏ i ∈ Finset.range n, (1 - κ ^ ((ms i : ℕ) : ℝ))) * E 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hfactor_nonneg : ∀ i : ℕ, 0 ≤ 1 - κ ^ ((ms i : ℕ) : ℝ) := by
      intro i
      have hle : κ ^ ((ms i : ℕ) : ℝ) ≤ 1 :=
        Real.rpow_le_one hκ0.le hκ1 (by positivity)
      linarith
    calc E (n + 1) ≤ (1 - κ ^ ((ms n : ℕ) : ℝ)) * E n := hstep n
      _ ≤ (1 - κ ^ ((ms n : ℕ) : ℝ)) *
            ((∏ i ∈ Finset.range n, (1 - κ ^ ((ms i : ℕ) : ℝ))) * E 0) :=
          mul_le_mul_of_nonneg_left ih (hfactor_nonneg n)
      _ = ((1 - κ ^ ((ms n : ℕ) : ℝ)) * ∏ i ∈ Finset.range n, (1 - κ ^ ((ms i : ℕ) : ℝ))) * E 0 := by
          ring
      _ = (∏ i ∈ Finset.range (n + 1), (1 - κ ^ ((ms i : ℕ) : ℝ))) * E 0 := by
          rw [Finset.prod_range_succ, mul_comm (1 - κ ^ ((ms n : ℕ) : ℝ))]

structure CompleteErasureData where

  finalOverlap : ℝ

  separable : SeparableTwoQubit

  finalOverlap_eq : finalOverlap = separable.overlap

theorem complete_erasure_removes_entanglement (d : CompleteErasureData) :
    d.finalOverlap ≤ 1 / 2 := by
  rw [d.finalOverlap_eq]
  exact (bell_state_witness d.separable).1

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement
