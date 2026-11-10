/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Qatlib.Papers.QWalkGraphs00.MainResults.Core
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.Distribution

open scoped BigOperators Matrix Topology
open Filter
open Qatlib.Papers.QWalkGraphs00.MainResults.Core

variable {Coin V : Type*} [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V]

theorem normSq_sum_finset {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    Complex.normSq (∑ j, f j) = (∑ i, ∑ j, f i * star (f j)).re := by
  have h1 : (∑ j, f j) * star (∑ j, f j) = ∑ i, ∑ j, f i * star (f j) := by
    rw [star_sum]
    exact Finset.sum_mul_sum _ _ _ _
  calc Complex.normSq (∑ j, f j)
      = ((∑ j, f j) * star (∑ j, f j)).re := by
        rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    _ = _ := by rw [h1]

theorem mulVec_pow_eigenvector
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (t : ℕ) (j : Coin × V) :
    ((U ^ t) *ᵥ φ j) = lam j ^ t • φ j := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hφ j, smul_smul,
        pow_succ]

theorem mulVec_pow_state_coord
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hψ : ψ = ∑ j, a j • φ j)
    (t : ℕ) (p : Coin × V) :
    ((U ^ t) *ᵥ ψ) p = ∑ j, a j * lam j ^ t * φ j p := by
  have hpow : ∀ j, ((U ^ t) *ᵥ φ j) = lam j ^ t • φ j :=
    fun j => mulVec_pow_eigenvector U φ lam hφ t j
  rw [hψ, Matrix.mulVec_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec_smul, hpow j]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem nodeProb_eq_spectral
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hψ : ψ = ∑ j, a j • φ j)
    (t : ℕ) (v : V) :
    nodeProb U ψ t v =
      (∑ c : Coin, ∑ i, ∑ j,
        a i * star (a j) * (lam i * star (lam j)) ^ t *
          (φ i (c, v) * star (φ j (c, v)))).re := by
  have hcoord := fun t p => mulVec_pow_state_coord U φ lam a ψ hφ hψ t p
  have hnode_c : ∀ c : Coin, Complex.normSq (((U ^ t) *ᵥ ψ) (c, v)) =
      (∑ i, ∑ j, a i * star (a j) * (lam i * star (lam j)) ^ t *
        (φ i (c, v) * star (φ j (c, v)))).re := by
    intro c
    rw [hcoord t (c, v), normSq_sum_finset]
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [star_mul, star_mul, star_pow, mul_pow]
    ring
  calc nodeProb U ψ t v
      = ∑ c : Coin, Complex.normSq (((U ^ t) *ᵥ ψ) (c, v)) := rfl
    _ = ∑ c : Coin, (∑ i, ∑ j, a i * star (a j) * (lam i * star (lam j)) ^ t *
          (φ i (c, v) * star (φ j (c, v)))).re :=
        Finset.sum_congr rfl (fun c _ => hnode_c c)
    _ = (∑ c : Coin, ∑ i, ∑ j, a i * star (a j) * (lam i * star (lam j)) ^ t *
          (φ i (c, v) * star (φ j (c, v)))).re := by
        rw [Complex.re_sum]

theorem ofReal_inv_mul_re (T : ℕ) (Z : ℂ) :
    (T : ℝ)⁻¹ * Z.re = ((T : ℂ)⁻¹ * Z).re := by
  have hT : (T : ℂ) = ((T : ℝ) : ℂ) := (Complex.ofReal_natCast T).symm
  rw [hT, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem inv_mul_sum_comm {ι : Type*} [Fintype ι]
    (g : ι → ℕ → ℂ) (T : ℕ) :
    (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, (∑ i, g i t)
      = ∑ i, (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, g i t := by
  rw [Finset.mul_sum]
  calc ∑ t ∈ Finset.range T, (T : ℂ)⁻¹ * (∑ i, g i t)
      = ∑ t ∈ Finset.range T, ∑ i, (T : ℂ)⁻¹ * g i t :=
        Finset.sum_congr rfl (fun t _ => Finset.mul_sum _ _ _)
    _ = ∑ i, ∑ t ∈ Finset.range T, (T : ℂ)⁻¹ * g i t := Finset.sum_comm
    _ = ∑ i, (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, g i t := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]

theorem mul_sum_comm {ι : Type*} [Fintype ι]
    (C : ι → ℂ) (g : ι → ℕ → ℂ) (T : ℕ) :
    (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, (∑ i, C i * g i t)
      = ∑ i, C i * ((T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, g i t) := by
  rw [Finset.mul_sum]
  calc ∑ t ∈ Finset.range T, (T : ℂ)⁻¹ * (∑ i, C i * g i t)
      = ∑ t ∈ Finset.range T, ∑ i, (T : ℂ)⁻¹ * (C i * g i t) :=
        Finset.sum_congr rfl (fun t _ => Finset.mul_sum _ _ _)
    _ = ∑ i, ∑ t ∈ Finset.range T, (T : ℂ)⁻¹ * (C i * g i t) := Finset.sum_comm
    _ = ∑ i, C i * ((T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, g i t) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

theorem geomAvg_sum_swap {ι : Type*} [Fintype ι]
    (C z : ι → ℂ) (T : ℕ) :
    (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, (∑ i, C i * z i ^ t)
      = ∑ i, C i * geomAvg (z i) T := by
  rw [mul_sum_comm C (fun i t => z i ^ t) T]
  rfl

theorem geomAvg_sum_swap3 {κ ι ν : Type*} [Fintype κ] [Fintype ι] [Fintype ν]
    (C : κ → ι → ν → ℂ) (z : ι → ν → ℂ) (T : ℕ) :
    (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, (∑ k, ∑ i, ∑ j, C k i j * z i j ^ t)
      = ∑ k, ∑ i, ∑ j, C k i j * geomAvg (z i j) T := by
  rw [inv_mul_sum_comm (fun k t => ∑ i, ∑ j, C k i j * z i j ^ t) T]
  apply Finset.sum_congr rfl
  intro k _
  rw [inv_mul_sum_comm (fun i t => ∑ j, C k i j * z i j ^ t) T]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_sum_comm (C k i) (fun j t => z i j ^ t) T]
  rfl

theorem avgNodeProb_eq_spectral
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hψ : ψ = ∑ j, a j • φ j)
    (T : ℕ) (v : V) :
    avgNodeProb U ψ T v =
      (∑ c : Coin, ∑ i, ∑ j,
        (a i * star (a j) * (φ i (c, v) * star (φ j (c, v)))) *
          geomAvg (lam i * star (lam j)) T).re := by
  set C : Coin → (Coin × V) → (Coin × V) → ℂ :=
    fun c i j => a i * star (a j) * (φ i (c, v) * star (φ j (c, v))) with hC
  set z : (Coin × V) → (Coin × V) → ℂ := fun i j => lam i * star (lam j) with hzdef
  have hnode_t : ∀ t : ℕ, nodeProb U ψ t v =
      (∑ c : Coin, ∑ i, ∑ j, C c i j * z i j ^ t).re := by
    intro t
    rw [nodeProb_eq_spectral U φ lam a ψ hφ hψ t v]
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hC, hzdef]
    ring
  calc avgNodeProb U ψ T v
      = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (∑ c, ∑ i, ∑ j, C c i j * z i j ^ t).re := by
          rw [avgNodeProb]
          apply congrArg (fun x => (T : ℝ)⁻¹ * x)
          exact Finset.sum_congr rfl (fun t _ => hnode_t t)
    _ = (T : ℝ)⁻¹ * ((∑ t ∈ Finset.range T,
          ∑ c, ∑ i, ∑ j, C c i j * z i j ^ t).re) := by
          rw [Complex.re_sum]
    _ = ((T : ℂ)⁻¹ * (∑ t ∈ Finset.range T,
          ∑ c, ∑ i, ∑ j, C c i j * z i j ^ t)).re := by
          rw [ofReal_inv_mul_re]
    _ = (∑ c : Coin, ∑ i, ∑ j, C c i j * geomAvg (z i j) T).re := by
          rw [geomAvg_sum_swap3 C z T]

theorem limiting_distribution_spectral
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hlam : ∀ j, ‖lam j‖ = 1)
    (hψ : ψ = ∑ j, a j • φ j)
    (v : V) :
    Tendsto (fun T : ℕ => avgNodeProb U ψ T v) atTop
      (𝓝 ((∑ i, ∑ j, if lam i = lam j then
            a i * star (a j) * (∑ c : Coin, φ i (c, v) * star (φ j (c, v)))
          else 0).re)) := by
  set C : Coin → (Coin × V) → (Coin × V) → ℂ :=
    fun c i j => a i * star (a j) * (φ i (c, v) * star (φ j (c, v))) with hC
  set z : (Coin × V) → (Coin × V) → ℂ := fun i j => lam i * star (lam j) with hzdef
  have hnormSq : ∀ j, Complex.normSq (lam j) = 1 := by
    intro j
    rw [Complex.normSq_eq_norm_sq, hlam j]
    norm_num
  have hz_norm : ∀ i j : Coin × V, ‖z i j‖ = 1 := by
    intro i j
    have hzi : z i j = lam i * star (lam j) := rfl
    rw [hzi, norm_mul, hlam i, norm_star, hlam j]
    norm_num
  have hz_eq_one : ∀ i j : Coin × V, z i j = 1 ↔ lam i = lam j := by
    intro i j
    have hzi : z i j = lam i * star (lam j) := rfl
    constructor
    · intro h
      have hj : star (lam j) * lam j = 1 := by
        calc star (lam j) * lam j = (Complex.normSq (lam j) : ℂ) := by
              rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
          _ = 1 := by rw [hnormSq j]; norm_num
      calc lam i = lam i * (star (lam j) * lam j) := by rw [hj, mul_one]
        _ = (lam i * star (lam j)) * lam j := by ring
        _ = 1 * lam j := by rw [← hzi, h]
        _ = lam j := one_mul _
    · intro h
      have hj : lam j * star (lam j) = 1 := by
        calc lam j * star (lam j) = (Complex.normSq (lam j) : ℂ) := by
              rw [Complex.star_def, Complex.mul_conj]
          _ = 1 := by rw [hnormSq j]; norm_num
      rw [hzi, h, hj]
  have hterm_lim : ∀ (c : Coin) (i j : Coin × V),
      Tendsto (fun T : ℕ => C c i j * geomAvg (z i j) T) atTop
        (𝓝 (C c i j * (if lam i = lam j then (1 : ℂ) else 0))) := by
    intro c i j
    have h := tendsto_geomAvg (z i j) (hz_norm i j)
    have hif : (if z i j = 1 then (1 : ℂ) else 0) =
        (if lam i = lam j then (1 : ℂ) else 0) := by
      by_cases hEq : lam i = lam j
      · rw [if_pos ((hz_eq_one i j).mpr hEq), if_pos hEq]
      · rw [if_neg (fun hz => hEq ((hz_eq_one i j).mp hz)), if_neg hEq]
    have h' : Tendsto (fun T : ℕ => C c i j * geomAvg (z i j) T) atTop
        (𝓝 (C c i j * (if z i j = 1 then (1 : ℂ) else 0))) :=
      h.const_mul (C c i j)
    rwa [hif] at h'
  have hsum_lim : Tendsto
      (fun T : ℕ => ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * geomAvg (z i j) T) atTop
      (𝓝 (∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * (if lam i = lam j then (1 : ℂ) else 0))) := by
    apply tendsto_finsetSum Finset.univ
    intro c _
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply tendsto_finsetSum Finset.univ
    intro j _
    exact hterm_lim c i j
  have hre_lim : Tendsto
      (fun T : ℕ => (∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * geomAvg (z i j) T).re) atTop
      (𝓝 ((∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * (if lam i = lam j then (1 : ℂ) else 0)).re)) :=
    (Complex.continuous_re.tendsto _).comp hsum_lim
  have hlim_eq : (∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * (if lam i = lam j then (1 : ℂ) else 0))
      = ∑ i : Coin × V, ∑ j : Coin × V,
          if lam i = lam j then
            a i * star (a j) * (∑ c : Coin, φ i (c, v) * star (φ j (c, v)))
          else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hP : lam i = lam j
    · simp only [if_pos hP, mul_one, hC]
      rw [Finset.mul_sum]
    · simp only [if_neg hP, mul_zero, Finset.sum_const, Finset.card_univ, nsmul_zero]
  have havg : ∀ T : ℕ, avgNodeProb U ψ T v =
      (∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * geomAvg (z i j) T).re :=
    fun T => avgNodeProb_eq_spectral U φ lam a ψ hφ hψ T v
  have heq : (fun T : ℕ => (∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * geomAvg (z i j) T).re) =ᶠ[atTop]
      (fun T : ℕ => avgNodeProb U ψ T v) := by
    exact Eventually.of_forall (fun T => (havg T).symm)
  have hfinal : Tendsto (fun T : ℕ => avgNodeProb U ψ T v) atTop
      (𝓝 ((∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        C c i j * (if lam i = lam j then (1 : ℂ) else 0)).re)) :=
    Tendsto.congr' heq hre_lim
  rwa [hlim_eq] at hfinal

theorem limiting_distribution_distinct_eigenvalues
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hlam : ∀ j, ‖lam j‖ = 1)
    (hψ : ψ = ∑ j, a j • φ j)
    (hinj : Function.Injective lam)
    (v : V) :
    Tendsto (fun T : ℕ => avgNodeProb U ψ T v) atTop
      (𝓝 (∑ i : Coin × V,
        Complex.normSq (a i) * ∑ c : Coin, Complex.normSq (φ i (c, v)))) := by
  have h := limiting_distribution_spectral U φ lam a ψ hφ hlam hψ v
  have hlim_eq : (∑ i : Coin × V, ∑ j : Coin × V,
        if lam i = lam j then
          a i * star (a j) * (∑ c : Coin, φ i (c, v) * star (φ j (c, v)))
        else 0).re
      = ∑ i : Coin × V,
          Complex.normSq (a i) * ∑ c : Coin, Complex.normSq (φ i (c, v)) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hsingle : (∑ j : Coin × V,
          if lam i = lam j then
            a i * star (a j) * (∑ c : Coin, φ i (c, v) * star (φ j (c, v)))
          else 0)
        = a i * star (a i) * (∑ c : Coin, φ i (c, v) * star (φ i (c, v))) := by
      have h0 : ∀ b ∈ (Finset.univ : Finset (Coin × V)), b ≠ i →
          (if lam i = lam b then
            a i * star (a b) * (∑ c : Coin, φ i (c, v) * star (φ b (c, v)))
          else 0) = 0 := by
        intro b _ hb
        exact if_neg (fun hEq => hb (hinj hEq).symm)
      have h1 : i ∉ (Finset.univ : Finset (Coin × V)) →
          (if lam i = lam i then
            a i * star (a i) * (∑ c : Coin, φ i (c, v) * star (φ i (c, v)))
          else 0) = 0 := by
        intro hi
        exact absurd (Finset.mem_univ i) hi
      calc (∑ j : Coin × V,
            if lam i = lam j then
              a i * star (a j) * (∑ c : Coin, φ i (c, v) * star (φ j (c, v)))
            else 0)
          = (if lam i = lam i then
              a i * star (a i) * (∑ c : Coin, φ i (c, v) * star (φ i (c, v)))
            else 0) := Finset.sum_eq_single i h0 h1
        _ = a i * star (a i) * (∑ c : Coin, φ i (c, v) * star (φ i (c, v))) := by
            rw [if_pos rfl]
    rw [hsingle]
    have hX : (∑ c : Coin, φ i (c, v) * star (φ i (c, v))).re
        = ∑ c : Coin, Complex.normSq (φ i (c, v)) := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    have hXim : (∑ c : Coin, φ i (c, v) * star (φ i (c, v))).im = 0 := by
      rw [Complex.im_sum]
      apply Finset.sum_eq_zero
      intro c _
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_im]
    have hXreal : (∑ c : Coin, φ i (c, v) * star (φ i (c, v)))
        = ((∑ c : Coin, φ i (c, v) * star (φ i (c, v))).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hXim
    have ha : (a i * star (a i)).re = Complex.normSq (a i) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    calc (a i * star (a i) * (∑ c : Coin, φ i (c, v) * star (φ i (c, v)))).re
        = (a i * star (a i)).re * (∑ c : Coin, φ i (c, v) * star (φ i (c, v))).re := by
            rw [hXreal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
            ring
      _ = Complex.normSq (a i) * ∑ c : Coin, Complex.normSq (φ i (c, v)) := by
            rw [ha, hX]
  rwa [hlim_eq] at h

end Qatlib.Papers.QWalkGraphs00.MainResults.Distribution
