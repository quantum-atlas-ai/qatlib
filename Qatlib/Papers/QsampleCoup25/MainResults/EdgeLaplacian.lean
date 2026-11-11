/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QsampleCoup25.MainResults.QuantizedCoupling

set_option backward.isDefEq.respectTransparency false

/-!
# Graph-Laplacian structure of the quantized coupling (source §4)

Temme--Wocjan, *Quantized Markov Chain Couplings that Prepare Qsamples*,
arXiv:2504.02651v2, Quantum 9, 1951 (2025). Fixed source PDF SHA-256
`616a3932dd7120d6c178df5869e910d5891e93396e55f7ccd07c11d3110cabf6`.

The convergence analysis of §4 is organised around the edge states
`|−xy⟩ = (|x⟩ - |y⟩)/√2` (source eq. (77)) and the *elementary Laplacians*
`|−xy⟩⟨−xy|` (source eq. (78)). This file records source Proposition 13 (79):

`D^{1/2} Q⊥ D^{1/2} = ∑_{x,y} π_x π_y |−xy⟩⟨−xy|`,

the statement that the rescaled complement projector of the qsample is the
`π_x π_y`-weighted graph Laplacian of the complete graph on `Ω`.

The elementary Laplacian is encoded as `(1/2) • (e_x - e_y)(e_x - e_y)ᵀ` with
unnormalised `e_x`, which is exactly `|−xy⟩⟨−xy|` and keeps the statements free
of `√2` bookkeeping.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QsampleCoup25.MainResults

open Finset BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {P : Matrix Ω Ω ℝ} {π : Ω → ℝ}

/-- The unnormalised basis vector `e_x` of `ℝ^Ω`. -/
def eVec (x : Ω) : Ω → ℝ := fun a => if a = x then 1 else 0

/-- Source eq. (77)--(78): the elementary Laplacian `|−xy⟩⟨−xy|`
`= (1/2)(e_x - e_y)(e_x - e_y)ᵀ`, written with unnormalised `e_x` so that the
`1/2` coming from `|−xy⟩ = (|x⟩-|y⟩)/√2` appears exactly once. -/
def edgeProj (x y : Ω) : Matrix Ω Ω ℝ :=
  fun a b => (1 / 2 : ℝ) * (eVec x a - eVec y a) * (eVec x b - eVec y b)

/-- Picking out the `x = a` term of a single sum against `eVec a`. -/
lemma sum_eVec_mul_left (a : Ω) (g : Ω → ℝ) :
    (∑ x : Ω, eVec x a * g x) = g a := by
  rw [Finset.sum_eq_single a]
  · simp [eVec]
  · intro x _ hx
    have hxa : ¬ (a = x) := fun h => hx h.symm
    simp [eVec, hxa]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- A double sum against a pair of `eVec` factors collapses to the single
coefficient at `(a, b)`. -/
lemma sum_eVec_mul_vec (a b : Ω) (g : Ω → Ω → ℝ) :
    (∑ x, ∑ y, eVec x a * eVec y b * g x y) = g a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [eVec]
    · intro y _ hy
      have hyb : ¬ (b = y) := fun h => hy h.symm
      simp [eVec, hyb]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro x _ hx
    have hxa : ¬ (a = x) := fun h => hx h.symm
    simp [eVec, hxa]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Source Proposition 13 (79): `D^{1/2} Q⊥ D^{1/2} = ∑_{x,y} π_x π_y |−xy⟩⟨−xy|`.
Entrywise the left side is `π_a - π_a π_b` on the diagonal and `-π_a π_b` off it. -/
theorem rescale_orthogonal_proj (hmc : MarkovChain P π) :
    (fun a b => Real.sqrt (π a) * ((1 : Matrix Ω Ω ℝ) a b - qsample π a b) *
        Real.sqrt (π b))
      = ∑ x, ∑ y, (π x * π y) • edgeProj x y := by
  have hsq : ∀ x : Ω, Real.sqrt (π x) * Real.sqrt (π x) = π x := sqrt_mul_self hmc
  funext a b
  have hlhs : Real.sqrt (π a) * ((1 : Matrix Ω Ω ℝ) a b - qsample π a b) * Real.sqrt (π b)
      = (if a = b then π a else 0) - π a * π b := by
    by_cases h : a = b
    · subst h
      simp only [Matrix.one_apply, if_true, qsample]
      have h3 : Real.sqrt (π a) * (Real.sqrt (π a) * Real.sqrt (π a)) * Real.sqrt (π a)
          = π a * π a := by
        calc Real.sqrt (π a) * (Real.sqrt (π a) * Real.sqrt (π a)) * Real.sqrt (π a)
            = (Real.sqrt (π a) * Real.sqrt (π a)) * (Real.sqrt (π a) * Real.sqrt (π a)) := by
              ring
          _ = π a * π a := by rw [hsq a]
      have hsplit : Real.sqrt (π a) * (1 - Real.sqrt (π a) * Real.sqrt (π a)) *
            Real.sqrt (π a)
          = Real.sqrt (π a) * Real.sqrt (π a)
            - Real.sqrt (π a) * (Real.sqrt (π a) * Real.sqrt (π a)) * Real.sqrt (π a) := by
        ring
      rw [hsplit, h3, hsq a]
    · have h3 : Real.sqrt (π a) * (Real.sqrt (π a) * Real.sqrt (π b)) * Real.sqrt (π b)
          = π a * π b := by
        calc Real.sqrt (π a) * (Real.sqrt (π a) * Real.sqrt (π b)) * Real.sqrt (π b)
            = (Real.sqrt (π a) * Real.sqrt (π a)) * (Real.sqrt (π b) * Real.sqrt (π b)) := by
              ring
          _ = π a * π b := by rw [hsq a, hsq b]
      simp only [Matrix.one_apply, if_neg h, qsample, zero_sub]
      rw [show Real.sqrt (π a) * -(Real.sqrt (π a) * Real.sqrt (π b)) * Real.sqrt (π b)
          = - (Real.sqrt (π a) * (Real.sqrt (π a) * Real.sqrt (π b)) * Real.sqrt (π b)) by ring,
        h3]
  have t11 : (∑ x, ∑ y, π x * π y * (eVec x a * eVec x b)) = (if a = b then π a else 0) := by
    have hstep : ∀ x : Ω, (∑ y : Ω, π x * π y * (eVec x a * eVec x b))
        = π x * (eVec x a * eVec x b) := by
      intro x
      rw [show (∑ y : Ω, π x * π y * (eVec x a * eVec x b))
          = (π x * (eVec x a * eVec x b)) * (∑ y : Ω, π y) from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring,
        hmc.pi_sum, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => hstep x),
      show (∑ x : Ω, π x * (eVec x a * eVec x b)) = ∑ x, eVec x a * (eVec x b * π x) from
        Finset.sum_congr rfl fun x _ => by ring,
      sum_eVec_mul_left a (fun x => eVec x b * π x)]
    by_cases hab : a = b
    · subst hab
      simp [eVec]
    · have hba : ¬ (b = a) := fun h => hab h.symm
      simp [eVec, hab, hba]
  have t22 : (∑ x, ∑ y, π x * π y * (eVec x a * eVec y b)) = π a * π b := by
    rw [show (∑ x, ∑ y, π x * π y * (eVec x a * eVec y b))
        = ∑ x, ∑ y, eVec x a * eVec y b * (π x * π y) from
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring]
    exact sum_eVec_mul_vec a b (fun x y => π x * π y)
  have t33 : (∑ x, ∑ y, π x * π y * (eVec y a * eVec x b)) = π b * π a := by
    rw [show (∑ x, ∑ y, π x * π y * (eVec y a * eVec x b))
        = ∑ y, ∑ x, eVec y a * eVec x b * (π x * π y) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      ring]
    exact sum_eVec_mul_vec a b (fun y x => π x * π y)
  have t44 : (∑ x, ∑ y, π x * π y * (eVec y a * eVec y b)) = (if a = b then π b else 0) := by
    have hstep : ∀ x : Ω, (∑ y : Ω, π x * π y * (eVec y a * eVec y b))
        = π x * (eVec a b * π a) := by
      intro x
      rw [show (∑ y : Ω, π x * π y * (eVec y a * eVec y b))
          = π x * (∑ y : Ω, eVec y a * (eVec y b * π y)) from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring,
        sum_eVec_mul_left a (fun y => eVec y b * π y)]
    rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.sum_mul, hmc.pi_sum, one_mul]
    by_cases hab : a = b
    · subst hab
      simp [eVec]
    · have hba : ¬ (b = a) := fun h => hab h.symm
      simp [eVec, hab, hba]
  have hpt : ∀ x y : Ω, π x * π y * edgeProj x y a b
      = (1 / 2 : ℝ) * (π x * π y * (eVec x a * eVec x b))
        - (1 / 2 : ℝ) * (π x * π y * (eVec x a * eVec y b))
        - (1 / 2 : ℝ) * (π x * π y * (eVec y a * eVec x b))
        + (1 / 2 : ℝ) * (π x * π y * (eVec y a * eVec y b)) := by
    intro x y
    simp only [edgeProj]
    ring
  have hsum : (∑ x, ∑ y, (π x * π y) • edgeProj x y) a b
      = (1 / 2 : ℝ) * (∑ x, ∑ y, π x * π y * (eVec x a * eVec x b))
        - (1 / 2 : ℝ) * (∑ x, ∑ y, π x * π y * (eVec x a * eVec y b))
        - (1 / 2 : ℝ) * (∑ x, ∑ y, π x * π y * (eVec y a * eVec x b))
        + (1 / 2 : ℝ) * (∑ x, ∑ y, π x * π y * (eVec y a * eVec y b)) := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hpt,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum, t11, t22, t33, t44, hlhs]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    ring
  · rw [if_neg hab, if_neg hab]
    ring

end Qatlib.Papers.QsampleCoup25.MainResults
