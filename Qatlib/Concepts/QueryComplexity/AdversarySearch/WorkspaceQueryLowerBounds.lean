/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation

/-!
# Workspace decision and search query lower bounds

This module derives explicit query lower bounds for circuits with arbitrary finite auxiliary
workspaces using the hybrid estimates of [BennettEtAl1997]. A normalized unitary circuit
distinguishing the null oracle from every singleton with the stated probability gap satisfies N
≤ 144Q²; identifying every singleton with probability at least 2/3 gives N ≤ 64Q² when N ≥ 6.

## Main statements

* `workspace_decision_query_lower_bound`: the decision probability gap implies N ≤ 144Q².
* `workspace_search_query_lower_bound`: successful singleton identification implies N ≤ 64Q².

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.SketchArith.GramAction

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- If a unitary circuit with normalized input accepts the null oracle with probability at most
1/3 and each singleton oracle with probability at least 2/3, the index cardinality is at
most 144 times its squared query count. This is a finite decision bound based on
[BennettEtAl1997]. -/
theorem workspace_decision_query_lower_bound (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (E : Finset ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hnull : MeasureProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) E
      ≤ 1 / 3)
    (hmark : ∀ x : I, MeasureProb
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ) E ≥ 2 / 3) :
    (Fintype.card I : ℝ) ≤ 144 * (QueryCount C : ℝ) ^ 2 := by
  have h1u : (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
      ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ := Submonoid.one_mem _
  have hψ0 : Normalized (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) :=
    hC.normalized_run h1u hψ
  have hdx : ∀ x : I, (1 / 6 : ℝ) ≤ ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
        Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ := by
    intro x
    have hψx : Normalized
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ) :=
      hC.normalized_run (workspaceBitOracle_unitary _) hψ
    have hbound := measureProb_sub_le_two_mul_l2
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ)
      (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) E hψx hψ0
    have hdiff : (1 / 3 : ℝ) ≤
        MeasureProb (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ) E
          - MeasureProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) E := by
      linarith [hmark x, hnull]
    have h2d := le_trans (le_trans hdiff (le_abs_self _)) hbound
    linarith [norm_nonneg (toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
        Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ))]
  have hsum : (Fintype.card I : ℝ) * (1 / 36) ≤ ∑ x : I, ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
        Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2 := by
    have h36 : ∀ x : I, (1 / 36 : ℝ) ≤ ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
          Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2 := by
      intro x
      have hd := hdx x
      have hd0 := norm_nonneg (toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
          Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ))
      nlinarith
    calc (Fintype.card I : ℝ) * (1 / 36)
        = ∑ x : I, (1 / 36 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ x : I, ‖toEuclidean_fromVec
            (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
              Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => h36 x
  have hG4 := workspace_query_hybrid_energy C ψ hC hψ
  nlinarith [hsum, hG4, sq_nonneg ((QueryCount C : ℝ))]

/-- If a unitary circuit with normalized input identifies every singleton mark with probability
at least 2/3 and the index type has at least six elements, its cardinality is at most 64
times the squared query count. This is a finite search bound based on [BennettEtAl1997]. -/
theorem workspace_search_query_lower_bound (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (decode : ((I × Bool) × W) → Option I)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (hcard : 6 ≤ Fintype.card I)
    (hmark : ∀ x : I, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ)
        (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3) :
    (Fintype.card I : ℝ) ≤ 64 * (QueryCount C : ℝ) ^ 2 := by
  have h1u : (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
      ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ := Submonoid.one_mem _
  have hψ0 : Normalized (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) :=
    hC.normalized_run h1u hψ

  have hkey : ∀ x : I, (1 / 3 : ℝ) ≤
      MeasureProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)
        (Finset.univ.filter (fun p => decode p = some x))
        + ‖toEuclidean_fromVec
            (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
              Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2 := by
    intro x
    set ψx := Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ with hψxdef
    set ψ0 := Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ with hψ0def
    set Ex := Finset.univ.filter (fun p : (I × Bool) × W => decode p = some x)
      with hExdef
    have hψxn : Normalized ψx := hC.normalized_run (workspaceBitOracle_unitary _) hψ
    have hsqrt : Real.sqrt (MeasureProb ψx Ex)
        ≤ Real.sqrt (MeasureProb ψ0 Ex) + ‖toEuclidean_fromVec (ψx - ψ0)‖ := by
      have htri : ‖toEuclidean_fromVec (Collapse ψx Ex)‖
          ≤ ‖toEuclidean_fromVec (Collapse ψ0 Ex)‖
            + ‖toEuclidean_fromVec (Collapse ψx Ex) - toEuclidean_fromVec (Collapse ψ0 Ex)‖ :=
        norm_le_norm_add_norm_sub' _ _
      have hcol : ‖toEuclidean_fromVec (Collapse ψx Ex)
            - toEuclidean_fromVec (Collapse ψ0 Ex)‖
          ≤ ‖toEuclidean_fromVec (ψx - ψ0)‖ := by
        have hsub : toEuclidean_fromVec (Collapse ψx Ex) - toEuclidean_fromVec (Collapse ψ0 Ex)
            = toEuclidean_fromVec (Collapse ψx Ex - Collapse ψ0 Ex) := by
          simp only [toEuclidean_fromVec, WithLp.toLp_sub]
        rw [hsub]
        exact norm_toEuclidean_collapse_sub_le ψ0 ψx Ex
      rw [norm_toEuclidean_collapse_eq_sqrt_measureProb,
        norm_toEuclidean_collapse_eq_sqrt_measureProb] at htri
      exact htri.trans (add_le_add le_rfl hcol)
    have hsq : MeasureProb ψx Ex
        ≤ (Real.sqrt (MeasureProb ψ0 Ex) + ‖toEuclidean_fromVec (ψx - ψ0)‖) ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
      rwa [Real.sq_sqrt (measureProb_nonneg _ _)] at h
    have hexpand : (Real.sqrt (MeasureProb ψ0 Ex) + ‖toEuclidean_fromVec (ψx - ψ0)‖) ^ 2
        ≤ 2 * MeasureProb ψ0 Ex + 2 * ‖toEuclidean_fromVec (ψx - ψ0)‖ ^ 2 := by
      have h2ab := two_mul_le_add_sq (Real.sqrt (MeasureProb ψ0 Ex))
        ‖toEuclidean_fromVec (ψx - ψ0)‖
      have hsqq : (Real.sqrt (MeasureProb ψ0 Ex)) ^ 2 = MeasureProb ψ0 Ex :=
        Real.sq_sqrt (measureProb_nonneg _ _)
      nlinarith
    have hpx := hmark x
    nlinarith

  have hqsum : ∑ x : I, MeasureProb
        (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)
        (Finset.univ.filter (fun p => decode p = some x))
      ≤ 1 := by
    have hstep1 : ∑ x : I, MeasureProb
          (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)
          (Finset.univ.filter (fun p => decode p = some x))
        = ∑ x : I, ∑ p : (I × Bool) × W,
            if decode p = some x
              then BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p
              else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [MeasureProb, Finset.sum_filter]
    rw [hstep1, Finset.sum_comm]
    have hinner : ∀ p : (I × Bool) × W,
        (∑ x : I, if decode p = some x
            then BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p
            else 0)
        ≤ BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p := by
      intro p
      cases hd : decode p with
      | none =>
          have hz : (∑ x : I, if (none : Option I) = some x
              then BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p
              else 0) = 0 :=
            Finset.sum_eq_zero fun x _ => if_neg fun hs => (Option.some_ne_none x) hs.symm
          rw [hz]
          exact bornProb_nonneg _ _
      | some a =>
          have hsum : (∑ x : I, if some a = some x
              then BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p
              else 0)
              = BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p := by
            rw [Finset.sum_eq_single a
              (fun x _ hxa => if_neg fun hs => hxa (Option.some.inj hs).symm)
              (fun hna => absurd (Finset.mem_univ a) hna), if_pos rfl]
          exact hsum.le
    calc ∑ p : (I × Bool) × W, (∑ x : I, if decode p = some x
            then BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p
            else 0)
        ≤ ∑ p : (I × Bool) × W,
            BornProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) p :=
          Finset.sum_le_sum fun p _ => hinner p
      _ = 1 := hψ0

  have hsum2 : (Fintype.card I : ℝ) * (1 / 3) - ∑ x : I,
        MeasureProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)
          (Finset.univ.filter (fun p => decode p = some x))
      ≤ ∑ x : I, ‖toEuclidean_fromVec
          (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
            Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2 := by
    calc (Fintype.card I : ℝ) * (1 / 3) - ∑ x : I,
          MeasureProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)
            (Finset.univ.filter (fun p => decode p = some x))
        = ∑ x : I, ((1 / 3 : ℝ) -
            MeasureProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)
              (Finset.univ.filter (fun p => decode p = some x))) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ x : I, ‖toEuclidean_fromVec
            (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
              Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => by linarith [hkey x]
  have hG4 := workspace_query_hybrid_energy C ψ hC hψ
  have hcardR : (6 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast hcard
  nlinarith [hsum2, hqsum, hG4, hcardR, sq_nonneg ((QueryCount C : ℝ))]

end Qatlib.Concepts.QueryComplexity.AdversarySearch
