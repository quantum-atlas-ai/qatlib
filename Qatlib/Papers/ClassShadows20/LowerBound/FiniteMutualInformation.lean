/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.ClassShadows20.LowerBound

open scoped Classical BigOperators Real

variable {C O X : Type*} [Fintype C] [Fintype O] [Fintype X]

noncomputable def finDistEntropy {X : Type*} [Fintype X] (p : FinDist X) : ℝ :=
  ∑ x, Real.negMulLog (p.prob x)

def finDistMixture (μ : FinDist C) (q : C → FinDist O) : FinDist O where
  prob o := ∑ c, μ.prob c * (q c).prob o
  nonneg o := Finset.sum_nonneg (fun c _ => mul_nonneg (μ.nonneg c) ((q c).nonneg o))
  sum_one := by
    have h : ∑ o, ∑ c, μ.prob c * (q c).prob o = ∑ c, μ.prob c * ∑ o, (q c).prob o := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum ..).symm
    rw [h, Finset.sum_congr rfl (fun c _ => by rw [(q c).sum_one, mul_one])]
    exact μ.sum_one

@[simp] theorem finDistMixture_prob (μ : FinDist C) (q : C → FinDist O) (o : O) :
    (finDistMixture μ q).prob o = ∑ c, μ.prob c * (q c).prob o := rfl

noncomputable def finDistCondMutualInfo (μ : FinDist C) (q : C → FinDist O) : ℝ :=
  finDistEntropy (finDistMixture μ q) - ∑ c, μ.prob c * finDistEntropy (q c)

private theorem negMulLog_tangent (M t : ℝ) (hM : 0 < M) (ht : 0 ≤ t) :
    -t * Real.log M - t * (t - M) / M ≤ Real.negMulLog t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [Real.negMulLog]
  · have h1 : Real.log (t / M) ≤ t / M - 1 := Real.log_le_sub_one_of_pos (div_pos ht hM)
    rw [Real.log_div ht.ne' hM.ne'] at h1
    have hconv : t / M - 1 = (t - M) / M := by field_simp
    rw [hconv] at h1
    have h2 : Real.log t ≤ Real.log M + (t - M) / M := by linarith
    have h3 : t * Real.log t ≤ t * Real.log M + t * (t - M) / M :=
      calc t * Real.log t ≤ t * (Real.log M + (t - M) / M) :=
            mul_le_mul_of_nonneg_left h2 ht.le
        _ = t * Real.log M + t * (t - M) / M := by ring
    show -t * Real.log M - t * (t - M) / M ≤ -t * Real.log t
    linarith

theorem finDistCondMutualInfo_le_variance_ratio (μ : FinDist C) (q : C → FinDist O) :
    finDistCondMutualInfo μ q ≤
      ∑ o ∈ Finset.univ.filter (fun o => 0 < (finDistMixture μ q).prob o),
        ((∑ c, μ.prob c * (q c).prob o ^ 2) - (finDistMixture μ q).prob o ^ 2) /
          (finDistMixture μ q).prob o := by
  classical

  have hmass : ∀ o, (∑ c, μ.prob c * (q c).prob o) = (finDistMixture μ q).prob o :=
    fun o => rfl

  have hper : ∀ o, 0 < (finDistMixture μ q).prob o →
      Real.negMulLog ((finDistMixture μ q).prob o)
        - ((∑ c, μ.prob c * (q c).prob o ^ 2) - (finDistMixture μ q).prob o ^ 2) /
            (finDistMixture μ q).prob o
        ≤ ∑ c, μ.prob c * Real.negMulLog ((q c).prob o) := by
    intro o hom
    have hmne : (finDistMixture μ q).prob o ≠ 0 := ne_of_gt hom
    have hpt : ∀ c : C, -((q c).prob o) * Real.log ((finDistMixture μ q).prob o)
        - (q c).prob o * ((q c).prob o - (finDistMixture μ q).prob o) /
            (finDistMixture μ q).prob o
        ≤ Real.negMulLog ((q c).prob o) :=
      fun c => negMulLog_tangent _ _ hom ((q c).nonneg o)
    have hsum : (∑ c, μ.prob c * (-((q c).prob o) * Real.log ((finDistMixture μ q).prob o)
          - (q c).prob o * ((q c).prob o - (finDistMixture μ q).prob o) /
              (finDistMixture μ q).prob o))
        ≤ ∑ c, μ.prob c * Real.negMulLog ((q c).prob o) :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hpt c) (μ.nonneg c)

    have hexp : ∑ c, μ.prob c * (-((q c).prob o) * Real.log ((finDistMixture μ q).prob o)
        - (q c).prob o * ((q c).prob o - (finDistMixture μ q).prob o) /
            (finDistMixture μ q).prob o)
        = -((finDistMixture μ q).prob o * Real.log ((finDistMixture μ q).prob o))
          - ((∑ c, μ.prob c * (q c).prob o ^ 2)
              - (finDistMixture μ q).prob o * (finDistMixture μ q).prob o) /
              (finDistMixture μ q).prob o := by
      have hsplit : ∀ c : C,
          μ.prob c * (-((q c).prob o) * Real.log ((finDistMixture μ q).prob o)
            - (q c).prob o * ((q c).prob o - (finDistMixture μ q).prob o) /
                (finDistMixture μ q).prob o)
          = -(μ.prob c * (q c).prob o) * Real.log ((finDistMixture μ q).prob o)
            - μ.prob c * ((q c).prob o * (q c).prob o) / (finDistMixture μ q).prob o
            + μ.prob c * (q c).prob o * (finDistMixture μ q).prob o /
                (finDistMixture μ q).prob o := by
        intro c
        field_simp
        ring
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
        ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib, hmass o]
      have hsq : ∑ c, μ.prob c * (q c).prob o ^ 2
          = ∑ c, μ.prob c * ((q c).prob o * (q c).prob o) :=
        Finset.sum_congr rfl fun c _ => by rw [sq]
      rw [hsq]
      field_simp
      ring
    rw [hexp] at hsum
    have hnML : Real.negMulLog ((finDistMixture μ q).prob o)
        = -((finDistMixture μ q).prob o * Real.log ((finDistMixture μ q).prob o)) := by
      simp only [Real.negMulLog]
      ring
    have hsq' : (finDistMixture μ q).prob o ^ 2
        = (finDistMixture μ q).prob o * (finDistMixture μ q).prob o := sq _
    rw [hnML, hsq']
    exact hsum

  have hzsum : ∀ o, (finDistMixture μ q).prob o = 0 →
      (∑ c, μ.prob c * Real.negMulLog ((q c).prob o)) = 0 := by
    intro o ho
    have hsumzero : (∑ c, μ.prob c * (q c).prob o) = 0 := by rw [hmass o, ho]
    have hterms : ∀ c : C, μ.prob c * (q c).prob o = 0 :=
      fun c => (Finset.sum_eq_zero_iff_of_nonneg
        (fun c' _ => mul_nonneg (μ.nonneg c') ((q c').nonneg o))).mp hsumzero c
        (Finset.mem_univ c)
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases eq_or_ne (μ.prob c) 0 with hμc | hμc
    · rw [hμc, zero_mul]
    · have ht0 : (q c).prob o = 0 := by
        rcases mul_eq_zero.mp (hterms c) with h | h
        · exact absurd h hμc
        · exact h
      rw [ht0]
      simp [Real.negMulLog]
  have hzneg : ∀ o, (finDistMixture μ q).prob o = 0 →
      Real.negMulLog ((finDistMixture μ q).prob o) = 0 := by
    intro o ho
    rw [ho]
    simp [Real.negMulLog]

  have hMI : finDistCondMutualInfo μ q
      = (∑ o, Real.negMulLog ((finDistMixture μ q).prob o))
        - ∑ c, μ.prob c * ∑ o, Real.negMulLog ((q c).prob o) := by
    simp only [finDistCondMutualInfo, finDistEntropy]
  have hswap : ∑ c, μ.prob c * ∑ o, Real.negMulLog ((q c).prob o)
      = ∑ o, ∑ c, μ.prob c * Real.negMulLog ((q c).prob o) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]

  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset O)
    (fun o => 0 < (finDistMixture μ q).prob o)
    (fun o => Real.negMulLog ((finDistMixture μ q).prob o))
  have hsplitR := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset O)
    (fun o => 0 < (finDistMixture μ q).prob o)
    (fun o => ∑ c, μ.prob c * Real.negMulLog ((q c).prob o))
  have hpos : (∑ o ∈ Finset.univ.filter (fun o => 0 < (finDistMixture μ q).prob o),
        Real.negMulLog ((finDistMixture μ q).prob o))
      - (∑ o ∈ Finset.univ.filter (fun o => 0 < (finDistMixture μ q).prob o),
        ((∑ c, μ.prob c * (q c).prob o ^ 2) - (finDistMixture μ q).prob o ^ 2) /
          (finDistMixture μ q).prob o)
      ≤ ∑ o ∈ Finset.univ.filter (fun o => 0 < (finDistMixture μ q).prob o),
          ∑ c, μ.prob c * Real.negMulLog ((q c).prob o) := by
    have h1 : (∑ o ∈ Finset.univ.filter (fun o => 0 < (finDistMixture μ q).prob o),
          (Real.negMulLog ((finDistMixture μ q).prob o)
            - ((∑ c, μ.prob c * (q c).prob o ^ 2) - (finDistMixture μ q).prob o ^ 2) /
                (finDistMixture μ q).prob o))
        ≤ ∑ o ∈ Finset.univ.filter (fun o => 0 < (finDistMixture μ q).prob o),
            ∑ c, μ.prob c * Real.negMulLog ((q c).prob o) :=
      Finset.sum_le_sum fun o ho => hper o ((Finset.mem_filter.mp ho).2)
    rw [Finset.sum_sub_distrib] at h1
    linarith
  have hzeroL : (∑ o ∈ Finset.univ.filter (fun o => ¬ 0 < (finDistMixture μ q).prob o),
        Real.negMulLog ((finDistMixture μ q).prob o)) = 0 := by
    refine Finset.sum_eq_zero fun o ho => ?_
    exact hzneg o (le_antisymm (not_lt.mp (Finset.mem_filter.mp ho).2)
      ((finDistMixture μ q).nonneg o))
  have hzeroR : (∑ o ∈ Finset.univ.filter (fun o => ¬ 0 < (finDistMixture μ q).prob o),
        ∑ c, μ.prob c * Real.negMulLog ((q c).prob o)) = 0 := by
    refine Finset.sum_eq_zero fun o ho => ?_
    exact hzsum o (le_antisymm (not_lt.mp (Finset.mem_filter.mp ho).2)
      ((finDistMixture μ q).nonneg o))
  rw [hMI, hswap, ← hsplitR, ← hsplit, hzeroL, hzeroR]
  simp only [add_zero]
  linarith

end Qatlib.Papers.ClassShadows20.LowerBound
