/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsPartEval07.PottsBridge.PottsWeightEnum
import Qatlib.Papers.PottsPartEval07.PottsBridge.KernelComponents
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.PottsBridge

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] (ends : E → V × V)

def subEnds (A : Finset E) : A → V × V := fun e => ends e.1

theorem potts_fk_expansion {q : ℕ} [NeZero q] [DecidableEq V] [DecidableEq E] (v : ℝ) :
    (∑ σ : V → ZMod q,
        ∏ e : E, (1 + v * (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0)))
      = ∑ A ∈ (Finset.univ : Finset E).powerset,
          v ^ A.card * (q : ℝ) ^ componentCount (subEnds ends A) := by
  classical

  have hswap : ∀ σ : V → ZMod q,
      (∏ e : E, (1 + v * (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0)))
        = ∑ A ∈ (Finset.univ : Finset E).powerset,
            ∏ e ∈ A, v * (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0) := by
    intro σ
    simpa using Finset.prod_one_add (s := (Finset.univ : Finset E))
      (f := fun e => v * (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0))
  simp only [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro A _

  have hstep : (∑ σ : V → ZMod q,
        ∏ e ∈ A, v * (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0))
      = v ^ A.card * (∑ σ : V → ZMod q,
          ∏ e ∈ A, (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [hstep]
  congr 1

  have hprod : ∀ σ : V → ZMod q,
      (∏ e ∈ A, (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0))
        = (if (∀ e ∈ A, σ (ends e).1 = σ (ends e).2) then (1 : ℝ) else 0) := by
    intro σ
    by_cases h : ∀ e ∈ A, σ (ends e).1 = σ (ends e).2
    · rw [if_pos h]
      exact Finset.prod_eq_one (fun e he => if_pos (h e he))
    · rw [if_neg h]
      push_neg at h
      obtain ⟨e, heA, hne⟩ := h
      exact Finset.prod_eq_zero heA (if_neg hne)
  have hfilter : (Finset.univ.filter fun σ : V → ZMod q => ∀ e ∈ A, σ (ends e).1 = σ (ends e).2)
      = (Finset.univ.filter fun σ : V → ZMod q => coboundary q (subEnds ends A) σ = 0) := by
    apply Finset.filter_congr
    intro σ _
    constructor
    · intro h
      funext e
      rw [coboundary_apply, Pi.zero_apply, sub_eq_zero]
      exact h e.1 e.2
    · intro h e he
      have := congrFun h ⟨e, he⟩
      rw [coboundary_apply, Pi.zero_apply] at this
      exact sub_eq_zero.mp this
  simp only [hprod]
  rw [show (∑ σ : V → ZMod q, if (∀ e ∈ A, σ (ends e).1 = σ (ends e).2) then (1 : ℝ) else 0)
        = ((Finset.univ.filter fun σ : V → ZMod q => ∀ e ∈ A, σ (ends e).1 = σ (ends e).2).card : ℝ) from by
    simpa using
        Finset.sum_boole (fun σ : V → ZMod q => ∀ e ∈ A, σ (ends e).1 = σ (ends e).2) Finset.univ]
  rw [hfilter]
  rw [show (Finset.univ.filter fun σ : V → ZMod q => coboundary q (subEnds ends A) σ = 0).card
        = kernelSize q (subEnds ends A) from rfl]
  rw [kernelSize_eq_pow]
  rw [Nat.cast_pow]

theorem pottsZ_inv_fk {q : ℕ} [NeZero q] [DecidableEq V] [DecidableEq E] (v : ℝ)
    (hv : (1 + v) ≠ 0) :
    pottsZ q ends ((1 + v)⁻¹)
      = ∑ A ∈ (Finset.univ : Finset E).powerset,
          v ^ A.card * (q : ℝ) ^ componentCount (subEnds ends A) := by
  classical
  rw [← potts_fk_expansion (ends := ends) (q := q) v]
  unfold pottsZ
  refine Finset.sum_congr rfl ?_
  intro σ _

  have hfac : ∀ e : E, (1 + v * (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0))
      = (if (σ (ends e).1 = σ (ends e).2) then (1 + v) else 1) := by
    intro e
    by_cases h : σ (ends e).1 = σ (ends e).2 <;> simp [h]
  have hprod : (∏ e : E, (1 + v * (if σ (ends e).1 = σ (ends e).2 then (1 : ℝ) else 0)))
      = (1 + v) ^ (monochromatic q ends σ).card := by
    rw [Finset.prod_congr rfl (fun e _ => hfac e)]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    congr 1
  rw [hprod]
  rw [inv_pow, inv_inv]

end Qatlib.Papers.PottsPartEval07.PottsBridge
