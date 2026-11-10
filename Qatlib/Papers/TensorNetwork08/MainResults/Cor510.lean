/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Lattice.Basic
import Qatlib.Papers.TensorNetwork08.MainResults.Cor59
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor510

open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
open Qatlib.Papers.TensorNetwork08.MainResults.Norm
open Qatlib.Papers.TensorNetwork08.MainResults.Cor59

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C] [Nonempty C]

noncomputable def differenceScaleTree (h : E → C → ℝ) (β : ℝ)
    (Etr Ecyc : Finset E) : ℝ :=
  (Fintype.card C : ℝ) *
    (Etr.prod (fun e => Finset.univ.sum (fun j : C => |edgeWeight h β e j|))) *
    (Ecyc.prod (fun e =>
      (Finset.univ : Finset C).sup' Finset.univ_nonempty
        (fun j : C => |edgeWeight h β e j|)))

omit [Fintype E] in

theorem corollary5_10_difference_algorithm
    (h : E → C → ℝ) (β : ℝ) (Etr Ecyc : Finset E) :
    differenceScaleTree h β Etr Ecyc
      = (Fintype.card C : ℝ) *
        (Etr.prod (fun e => Finset.univ.sum (fun j : C => |edgeWeight h β e j|))) *
        (Ecyc.prod (fun e =>
          (Finset.univ : Finset C).sup' Finset.univ_nonempty
            (fun j : C => |edgeWeight h β e j|))) := rfl

theorem energy_norm_comparison (w : C → ℝ) :
    (Finset.univ.sup' Finset.univ_nonempty (fun j => |w j|))
        ≤ Real.sqrt (∑ j : C, |w j| ^ 2) ∧
      Real.sqrt (∑ j : C, |w j| ^ 2) ≤ ∑ j : C, |w j| :=
  ⟨sup'_abs_le_sqrt_sum_sq w, sqrt_sum_sq_le_sum_abs w⟩

theorem corollary5_10_le_corollary5_9 [DecidableEq E]
    (h : E → C → ℝ) (β : ℝ) (Etr Ecyc : Finset E)
    (hdisj : Disjoint Etr Ecyc) (hcover : Etr ∪ Ecyc = (Finset.univ : Finset E))
    (hv : 0 < Fintype.card V) (htree : Etr.card = Fintype.card V - 1) :
    differenceScaleTree h β Etr Ecyc
      ≤ differenceScale (Fintype.card C) (Fintype.card V) h β := by
  classical

  set A : ℝ := Etr.prod (fun e => ∑ j : C, |edgeWeight h β e j|) with hA
  set B : ℝ := Ecyc.prod (fun e => (Finset.univ : Finset C).sup'
    Finset.univ_nonempty (fun j : C => |edgeWeight h β e j|)) with hB
  set A' : ℝ := Etr.prod (fun e => energyNorm h β e) with hA'
  set B' : ℝ := Ecyc.prod (fun e => energyNorm h β e) with hB'
  have hq : (0 : ℝ) ≤ Fintype.card C := by positivity
  have hsqrtq : (0 : ℝ) ≤ Real.sqrt (Fintype.card C : ℝ) := Real.sqrt_nonneg _

  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.prod_nonneg (fun e _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hA'0 : 0 ≤ A' := by
    rw [hA']
    exact Finset.prod_nonneg (fun e _ => Real.sqrt_nonneg _)
  have hB'0 : 0 ≤ B' := by
    rw [hB']
    exact Finset.prod_nonneg (fun e _ => Real.sqrt_nonneg _)

  have htree_le : A ≤ (Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * A' := by
    have hle : ∀ e ∈ Etr, (∑ j : C, |edgeWeight h β e j|)
        ≤ Real.sqrt (Fintype.card C : ℝ) * energyNorm h β e := by
      intro e _
      simpa only [energyNorm] using
        sum_abs_le_sqrt_card_mul_sqrt_sum_sq (edgeWeight h β e)
    have h0 : ∀ e ∈ Etr, 0 ≤ ∑ j : C, |edgeWeight h β e j| :=
      fun e _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hprod := Finset.prod_le_prod₀ h0 hle
    have hsplit : Etr.prod (fun e => Real.sqrt (Fintype.card C : ℝ) * energyNorm h β e)
        = (Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * A' := by
      rw [hA', Finset.prod_mul_distrib, Finset.prod_const]
    rw [hA]
    exact hprod.trans_eq hsplit

  have hcyc_le : B ≤ B' := by
    have hle : ∀ e ∈ Ecyc, (Finset.univ : Finset C).sup' Finset.univ_nonempty
        (fun j : C => |edgeWeight h β e j|) ≤ energyNorm h β e := by
      intro e _
      simpa only [energyNorm] using sup'_abs_le_sqrt_sum_sq (edgeWeight h β e)
    have h0 : ∀ e ∈ Ecyc, 0 ≤ (Finset.univ : Finset C).sup' Finset.univ_nonempty
        (fun j : C => |edgeWeight h β e j|) :=
      fun e _ => (Finset.le_sup'_iff (s := (Finset.univ : Finset C))
        Finset.univ_nonempty).mpr
        ⟨Classical.arbitrary C, Finset.mem_univ _, abs_nonneg _⟩
    rw [hB, hB']
    exact Finset.prod_le_prod₀ h0 hle

  have hmerge : A' * B' = ∏ e : E, energyNorm h β e := by
    rw [hA', hB', ← Finset.prod_union hdisj, hcover]

  have hstep : (Fintype.card C : ℝ) * (Real.sqrt (Fintype.card C : ℝ)) ^ (Fintype.card V - 1)
      = (Real.sqrt (Fintype.card C : ℝ)) ^ (Fintype.card V + 1) := by
    have hpow : (Fintype.card C : ℝ) = (Real.sqrt (Fintype.card C : ℝ)) ^ 2 :=
      (Real.sq_sqrt hq).symm
    nth_rewrite 1 [hpow]
    rw [← pow_add]
    congr 1
    omega
  unfold differenceScaleTree differenceScale

  have hcombine : (Fintype.card C : ℝ) * A * B
      ≤ (Fintype.card C : ℝ) * (Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * (A' * B') := by
    have hAB' : B * A ≤ B' * ((Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * A') :=
      mul_le_mul hcyc_le htree_le hA0 hB'0
    have hAB : A * B ≤ ((Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * A') * B' := by
      rw [mul_comm A B, mul_comm ((Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * A') B']
      exact hAB'
    calc (Fintype.card C : ℝ) * A * B
        = (Fintype.card C : ℝ) * (A * B) := by ring
      _ ≤ (Fintype.card C : ℝ)
            * (((Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * A') * B') :=
          mul_le_mul_of_nonneg_left hAB hq
      _ = (Fintype.card C : ℝ) * (Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * (A' * B') := by
          ring
  calc (Fintype.card C : ℝ) * A * B
      ≤ (Fintype.card C : ℝ) * (Real.sqrt (Fintype.card C : ℝ)) ^ Etr.card * (A' * B') :=
        hcombine
    _ = (Fintype.card C : ℝ) * (Real.sqrt (Fintype.card C : ℝ)) ^ (Fintype.card V - 1)
          * ∏ e : E, energyNorm h β e := by rw [htree, hmerge]
    _ = (Real.sqrt (Fintype.card C : ℝ)) ^ (Fintype.card V + 1)
          * ∏ e : E, energyNorm h β e := by rw [hstep]

end Qatlib.Papers.TensorNetwork08.MainResults.Cor510
