/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.AffineHSP02.HarmonicCore

variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V]

noncomputable def avg (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H] : V →ₗ[ℂ] V :=
  ((Fintype.card H : ℂ)⁻¹) • ∑ h : H, ρ (h : G)

theorem avg_apply (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H] (v : V) :
    avg ρ H v = ((Fintype.card H : ℂ)⁻¹) • ∑ h : H, ρ (h : G) v := by
  unfold avg
  rw [LinearMap.smul_apply, LinearMap.sum_apply]

theorem rho_comp_avg_eq (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H]
    (k : H) : (ρ (k : G)).comp (avg ρ H) = avg ρ H := by
  ext v
  rw [LinearMap.comp_apply, avg_apply, map_smul, map_sum]
  congr 1

  refine Fintype.sum_bijective (fun h : H => k * h) (Equiv.mulLeft k).bijective _ _ ?_
  intro h
  show ((ρ (k : G)) * (ρ (h : G))) v = (ρ ((k * h : H) : G)) v
  rw [← map_mul]
  simp

theorem avg_idem (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H] :
    (avg ρ H).comp (avg ρ H) = avg ρ H := by
  ext v
  rw [LinearMap.comp_apply, avg_apply, avg_apply]

  have hterm : ∀ k : H, ρ (k : G) (((Fintype.card H : ℂ)⁻¹) • ∑ h : H, ρ (h : G) v)
      = ((Fintype.card H : ℂ)⁻¹) • ∑ h : H, ρ ((k * h : H) : G) v := by
    intro k
    rw [map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    show ((ρ (k : G)) * (ρ (h : G))) v = (ρ ((k * h : H) : G)) v
    rw [← map_mul]
    simp
  simp_rw [hterm]
  rw [← Finset.smul_sum, Finset.sum_comm]

  have hinner : ∀ h : H, (∑ k : H, ρ ((k * h : H) : G) v) = ∑ k : H, ρ (k : G) v := by
    intro h
    refine Fintype.sum_bijective (fun k : H => k * h) (Equiv.mulRight h).bijective _ _ ?_
    intro k
    rfl
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ]
  rw [(Nat.cast_smul_eq_nsmul ℂ (Fintype.card H) (∑ k : H, ρ (k : G) v)).symm]
  rw [smul_smul, smul_smul]
  congr 1
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

def invariants (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ h : H, ρ (h : G) v = v}
  zero_mem' := by intro h; exact map_zero _
  add_mem' := by
    intro x y hx hy h
    rw [map_add, hx h, hy h]
  smul_mem' := by
    intro c x hx h
    rw [map_smul, hx h]

theorem avg_eq_self_of_mem_invariants (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G)
    [Fintype H] {v : V} (hv : v ∈ invariants ρ H) : avg ρ H v = v := by
  rw [avg_apply]
  have hconst : ∀ h : H, ρ (h : G) v = v := hv
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ]
  rw [(Nat.cast_smul_eq_nsmul ℂ (Fintype.card H) v).symm]
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [smul_smul]
  field_simp
  simp

theorem avg_mem_invariants (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H]
    (v : V) : avg ρ H v ∈ invariants ρ H := by
  intro k
  rw [← LinearMap.comp_apply, rho_comp_avg_eq]

theorem isProj_avg (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H] :
    LinearMap.IsProj (invariants ρ H) (avg ρ H) where
  map_mem := avg_mem_invariants ρ H
  map_id := by
    intro x hx
    exact avg_eq_self_of_mem_invariants ρ H hx

theorem comp_sum_eq {H : Subgroup G} [Fintype H] (g : V →ₗ[ℂ] V)
    (F : H → V →ₗ[ℂ] V) :
    g.comp (∑ h : H, F h) = ∑ h : H, g.comp (F h) := by
  ext v
  rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  rfl

noncomputable def cosetAvg (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H]
    (c : G) : V →ₗ[ℂ] V :=
  ((Fintype.card H : ℂ)⁻¹) • ∑ h : H, ρ (c * (h : G))

theorem cosetAvg_eq_comp (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H]
    (c : G) : cosetAvg ρ H c = (ρ c).comp (avg ρ H) := by
  unfold cosetAvg avg
  rw [LinearMap.comp_smul, comp_sum_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  exact map_mul ρ c (h : G)

theorem fhat_coset_eq (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H]
    (c : G) :
    Real.sqrt ((Module.finrank ℂ V : ℝ) * (Fintype.card H : ℝ) / (Fintype.card G : ℝ))
        • cosetAvg ρ H c
      = Real.sqrt ((Module.finrank ℂ V : ℝ) * (Fintype.card H : ℝ) / (Fintype.card G : ℝ))
        • (ρ c).comp (avg ρ H) := by
  rw [cosetAvg_eq_comp]

theorem trace_avg_eq_finrank (ρ : G →* (V →ₗ[ℂ] V)) (H : Subgroup G) [Fintype H]
    [Module.Finite ℂ V] [Module.Free ℂ V] :
    LinearMap.trace ℂ V (avg ρ H) = (Module.finrank ℂ (LinearMap.range (avg ρ H)) : ℂ) := by
  have hrange : LinearMap.IsProj (LinearMap.range (avg ρ H)) (avg ρ H) :=
    LinearMap.IsIdempotentElem.isProj_range _ (by
      have h := avg_idem ρ H
      ext v
      exact congrArg (fun f : V →ₗ[ℂ] V => f v) h)
  exact hrange.trace

end Qatlib.Papers.AffineHSP02.HarmonicCore
