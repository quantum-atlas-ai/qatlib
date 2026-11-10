/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9ResourceTeleportationStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
set_option maxHeartbeats 0

private theorem inner_reverse_zero {u v : QState (Fin 2)} (h : Qatlib.Foundations.PureStateMath.Inner u v = 0) :
    Qatlib.Foundations.PureStateMath.Inner v u = 0 := by
  have hc := congrArg (starRingEnd ℂ) h
  simpa [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Fin.sum_univ_two, map_add,
      map_mul, mul_comm] using hc

private def pairColumns (u v : QState (Fin 2)) : Operator 2 :=
  fun i j => if j = 0 then u i else v i

private theorem pair_complete {u v : QState (Fin 2)}
    (hu : Normalized u) (hv : Normalized v) (huv : Qatlib.Foundations.PureStateMath.Inner u v = 0) (i j : Fin 2) :
    u i * starRingEnd ℂ (u j) + v i * starRingEnd ℂ (v j) =
      (1 : Operator 2) i j := by
  have hvu := inner_reverse_zero huv
  have huu := (normalized_iff_inner_self u).mp hu
  have hvv := (normalized_iff_inner_self v).mp hv
  have hg : (pairColumns u v)ᴴ * pairColumns u v = 1 := by
    ext a b
    fin_cases a <;> fin_cases b
    · simpa [pairColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Inner, dotProduct] using huu
    · simpa [pairColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Inner, dotProduct, Matrix.one_apply] using huv
    · simpa [pairColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Inner, dotProduct, Matrix.one_apply] using hvu
    · simpa [pairColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Inner, dotProduct] using hvv
  have hunit : pairColumns u v ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hc := Matrix.mem_unitaryGroup_iff.mp hunit
  rw [Matrix.star_eq_conjTranspose] at hc
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, pairColumns,
    Fin.sum_univ_two] using congrArg (fun A : Operator 2 => A i j) hc

private theorem first_marginal {u v p q : QState (Fin 2)}
    (h : eq9OrthoPairs u v p q) :
    PartialTrace (outerProduct (eq9Resource u v p q)) = (1/2 : ℂ) • (1 : Operator 2) := by
  obtain ⟨hu,hv,hp,hq,huv,hpq⟩ := h
  have hqp := inner_reverse_zero hpq
  have hpp := (normalized_iff_inner_self p).mp hp
  have hqq := (normalized_iff_inner_self q).mp hq
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply,
      Complex.star_def, Fin.sum_univ_two] at hpp hqq hpq hqp
  ext i j
  calc
    _ = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
      ((u i * starRingEnd ℂ (u j)) * (starRingEnd ℂ (p 0) * p 0 + starRingEnd ℂ (p 1) * p 1) +
       (v i * starRingEnd ℂ (v j)) * (starRingEnd ℂ (q 0) * q 0 + starRingEnd ℂ (q 1) * q 1) +
       (u i * starRingEnd ℂ (v j)) * (starRingEnd ℂ (q 0) * p 0 + starRingEnd ℂ (q 1) * p 1) +
       (v i * starRingEnd ℂ (u j)) * (starRingEnd ℂ (p 0) * q 0 + starRingEnd ℂ (p 1) * q 1)) := by
        simp [PartialTrace, outerProduct_apply, eq9Resource, Fin.sum_univ_two,
          map_add, map_mul, Complex.conj_ofReal]
        ring
    _ = _ := by
      rw [hpp,hqq,hpq,hqp,sqrt2_inv_sq]
      simp [pair_complete hu hv huv i j]

private theorem resource_row_inner {u v p q : QState Bool} (h : eq9OrthoPairsB u v p q)
    (b d : Bool) :
    (starRingEnd ℂ (eq9ResourceB u v p q (b,false)) * eq9ResourceB u v p q (d,false) +
     starRingEnd ℂ (eq9ResourceB u v p q (b,true)) * eq9ResourceB u v p q (d,true)) =
       if b = d then (1/2 : ℂ) else 0 := by
  have hf : eq9OrthoPairs (u ∘ boolEquivFin2.symm) (v ∘ boolEquivFin2.symm)
      (p ∘ boolEquivFin2.symm) (q ∘ boolEquivFin2.symm) := by
    simpa [eq9OrthoPairs, eq9OrthoPairsB, Normalized, Qatlib.Foundations.PureStateMath.Inner, dotProduct,
      Fin.sum_univ_two, Fintype.sum_bool, boolEquivFin2, add_comm] using h
  have hm := first_marginal hf
  have he := congrArg (fun A : Operator 2 => A (boolEquivFin2 d) (boolEquivFin2 b)) hm
  cases b <;> cases d <;>
    simpa [PartialTrace, outerProduct_apply, eq9Resource, eq9ResourceB, Fin.sum_univ_two,
    Function.comp_def, Matrix.one_apply, boolEquivFin2, mul_comm, eq_comm] using he

private theorem branch_entry (u v p q : QState Bool) (o : Bool × Bool) (c i : Fin 2) :
    eq9BranchKraus u v p q o c i = (Real.sqrt 2 : ℂ)⁻¹ *
      ((if false = boolEquivFin2.symm i then eq9ResourceB u v p q (o.2,boolEquivFin2.symm c) else 0) +
       (if o.1 then (-1 : ℂ) else 1) *
        (if true = boolEquivFin2.symm i then eq9ResourceB u v p q (!o.2,boolEquivFin2.symm c) else 0)) := by
  let ψ : QState ((Bool × Bool) × Bool) := fun x =>
    if x.1.1 = boolEquivFin2.symm i then eq9ResourceB u v p q (x.1.2,x.2) else 0
  have hc : (fun r => eq9PreparedFrame u v p q r i) = relabelState teleportRegisterEquiv ψ := rfl
  have hd : teleportDecodeGate = relabelGate teleportRegisterEquiv
      (teleportHaB * teleportCnotAbB) := by
    unfold teleportDecodeGate teleportHaGate teleportCnotAbGate
    rw [teleportRelabelGate_mul]
  change (teleportDecodeGate * eq9PreparedFrame u v p q)
    (teleportRegisterEquiv ((o.1,o.2),boolEquivFin2.symm c)) i = _
  rw [matrix_mul_column, hc, hd, applyGate_relabelGate, applyGate_mul,
    teleportHaB_apply, teleportCnotAbB_apply]
  cases o with
  | mk a b => cases a <;> cases b <;> simp [relabelState, ψ]

private theorem branch_gram {u v p q : QState Bool} (h : eq9OrthoPairsB u v p q)
    (o : Bool × Bool) :
    (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o =
      (1/4 : ℂ) • (1 : Operator 2) := by
  have h00 := resource_row_inner h false false
  have h01 := resource_row_inner h false true
  have h10 := resource_row_inner h true false
  have h11 := resource_row_inner h true true
  simp at h00 h01 h10 h11
  have hs := sqrt2_inv_sq
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, branch_entry,
    Matrix.smul_apply, smul_eq_mul]
  rcases o with ⟨a,b⟩
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    simp [boolEquivFin2, Complex.conj_ofReal]
  all_goals first
    | linear_combination (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * h00 + (1/2 : ℂ) * hs
    | linear_combination (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * h11 + (1/2 : ℂ) * hs
    | linear_combination (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * h01
    | linear_combination -(Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * h01
    | linear_combination (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * h10
    | linear_combination -(Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * h10

theorem eq9ResourceTeleportation : Eq9ResourceTeleportation := by
  intro u v p q h o
  have hg := branch_gram h o
  have hc : (2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o =
      (1/2 : ℂ) • (1 : Operator 2) := by
    rw [smul_mul_assoc, hg, smul_smul]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
      smul_mul_assoc, mul_smul_comm, hg, smul_smul, smul_smul]
    norm_num
  · intro ρ
    rw [hc]
    simp [Matrix.conjTranspose_smul, smul_smul]
    norm_num

end Qatlib.Concepts.QuditTeleport.ResourceIff
