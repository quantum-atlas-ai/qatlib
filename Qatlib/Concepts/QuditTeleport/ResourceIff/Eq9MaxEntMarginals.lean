/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.Eq9MaxEntMarginals
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix

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

theorem eq9MaxEntMarginals : Eq9MaxEntMarginals := by
  intro u v p q h
  refine ⟨first_marginal h, ?_⟩
  have hs : relabelGate (Equiv.prodComm (Fin 2) (Fin 2))
      (outerProduct (eq9Resource u v p q)) = outerProduct (eq9Resource p q u v) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    simp [relabelGate, outerProduct_apply, eq9Resource, mul_comm]
  rw [hs]
  exact first_marginal ⟨h.2.2.1,h.2.2.2.1,h.1,h.2.1,h.2.2.2.2.2,h.2.2.2.2.1⟩

end Qatlib.Concepts.QuditTeleport.ResourceIff
