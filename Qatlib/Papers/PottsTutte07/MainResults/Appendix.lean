/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions
import Qatlib.Papers.PottsTutte07.MainResults.ComplexityDefs
import Qatlib.Papers.PottsTutte07.MainResults.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

theorem lemmaA_1_bridge_vector
    (F : Type*) [Field F] (C : Type*) [AddCommGroup C] [Module F C] [FiniteDimensional F C]
    (A B : Submodule F C)
    (hsup : A ⊔ B = ⊤) (hinf : A ⊓ B = ⊥)
    (hlt : Module.finrank F A < Module.finrank F B)
    (W : C ≃ₗ[F] C) :
    ∃ b ∈ B, b ≠ 0 ∧ W b ∈ B := by
  classical
  let WB : Submodule F C := B.map (W : C →ₗ[F] C)
  have hWB : Module.finrank F WB = Module.finrank F B :=
    LinearEquiv.finrank_map_eq W B
  have hbot : Module.finrank F ↥(⊥ : Submodule F C) = 0 := by simp
  have hC : Module.finrank F C = Module.finrank F A + Module.finrank F B := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hsup, hinf] at h
    simpa [finrank_top, hbot] using h
  by_contra h
  have hinf' : B ⊓ WB = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, Submodule.mem_map] at hx
    obtain ⟨hxB, b', hb'B, hb'x⟩ := hx
    by_contra hx0
    apply h
    refine ⟨b', hb'B, ?_, ?_⟩
    · intro hb0
      apply hx0
      rw [← hb'x, hb0]
      simp
    · change (W : C →ₗ[F] C) b' ∈ B
      rw [hb'x]
      exact hxB
  have hsup' : Module.finrank F ↥(B ⊔ WB) + Module.finrank F ↥(B ⊓ WB)
      = Module.finrank F B + Module.finrank F WB :=
    Submodule.finrank_sup_add_finrank_inf_eq B WB
  rw [hinf', hWB, hbot, add_zero] at hsup'
  have hle : Module.finrank F ↥(B ⊔ WB) ≤ Module.finrank F C := by
    calc Module.finrank F ↥(B ⊔ WB) ≤ Module.finrank F ↥(⊤ : Submodule F C) :=
          Submodule.finrank_mono le_top
      _ = Module.finrank F C := finrank_top F C
  rw [hC] at hle
  omega

theorem lemmaA_2_transitive_action
    (F : Type*) [Field F] (C : Type*) [AddCommGroup C] [Module F C]
    (ψ φ : C) (hψ : ψ ≠ 0) :
    ∃ T : C →ₗ[F] C, T ψ = φ := by
  classical
  let f : F →ₗ[F] C := LinearMap.toSpanSingleton F C ψ
  have hf : ∀ a : F, f a = a • ψ := fun a => LinearMap.toSpanSingleton_apply F C ψ a
  have hinj : Function.Injective f := by
    intro x y hxy
    have hxy' : x • ψ = y • ψ := by rw [← hf x, ← hf y]; exact hxy
    have h : (x - y) • ψ = 0 := by
      rw [sub_smul, hxy', sub_self]
    rcases smul_eq_zero.mp h with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hψ
  let p : Submodule F C := Submodule.span F {ψ}
  have hmem : ψ ∈ p := Submodule.mem_span_singleton_self ψ
  let e : F ≃ₗ[F] p :=
    (LinearEquiv.ofInjective f hinj).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton (R := F) (M := C) ψ))
  have he1 : e 1 = ⟨ψ, hmem⟩ := by
    apply Subtype.ext
    simp [e, f, LinearMap.toSpanSingleton_apply]
  let g0 : p →ₗ[F] F := e.symm.toLinearMap
  have hg0 : g0 ⟨ψ, hmem⟩ = 1 := by
    show e.symm ⟨ψ, hmem⟩ = 1
    rw [LinearEquiv.symm_apply_eq, he1]
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g0
  have hgψ : g ψ = 1 := by
    have h := congrArg (fun (l : p →ₗ[F] F) => l ⟨ψ, hmem⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h]
    exact hg0
  refine ⟨(LinearMap.toSpanSingleton F C φ).comp g, ?_⟩
  rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, hgψ, one_smul]

theorem lemmaA_3_swap_generator
    (F : Type*) [Field F] (C : Type*) [AddCommGroup C] [Module F C]
    (V : C →ₗ[F] C) (a1 b1 : C)
    (h1 : V a1 = b1) (h2 : V b1 = -a1) :
    V (V a1) = -a1 ∧ V (V b1) = -b1 := by
  constructor
  · rw [h1, h2]
  · rw [h2, map_neg, h1]

theorem lemmaA_4_generate_sl
    (F : Type*) [Field F] (C : Type*) [AddCommGroup C] [Module F C]
    (Gen : Set (C ≃ₗ[F] C)) (S : Submonoid (C ≃ₗ[F] C)) (hS : Gen ⊆ S) :
    Submonoid.closure Gen ≤ S :=
  Submonoid.closure_le.mpr hS

theorem lemmaB_1_polar_stability
    {m : ℕ} (Δ A P : Matrix (Fin m) (Fin m) ℂ)
    (hΔ : Δ = A * P)
    (hA : Matrix.conjTranspose A * A = 1)
    (hP : Matrix.conjTranspose P = P) :
    P = Matrix.conjTranspose A * Δ ∧
      Matrix.conjTranspose Δ * Δ = Matrix.conjTranspose P * P := by
  constructor
  · rw [hΔ, ← Matrix.mul_assoc, hA, Matrix.one_mul]
  · rw [hΔ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.conjTranspose A), hA, Matrix.one_mul, hP]

theorem lemmaB_2_commutator_lipschitz
    {m : ℕ} (V W Vt Wt : Matrix (Fin m) (Fin m) ℂ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hεδ : ε ≤ δ)
    (hV : entryDist V Vt ≤ ε) (hW : entryDist W Wt ≤ ε)
    (hVinv : entryDist V 0 ≤ δ) (hWinv : entryDist W 0 ≤ δ) :
    ∃ C : ℝ, 0 < C ∧
      entryDist (V * W - W * V) (Vt * Wt - Wt * Vt) ≤ C * ε * δ := by
  refine ⟨6 * ((m : ℝ) + 1) ^ 3, by positivity, ?_⟩
  have hcard : (Fintype.card (Fin m) : ℝ) = m := by simp
  have hVt0 : entryDist Vt 0 ≤ δ + ε := by
    calc entryDist Vt 0 ≤ entryDist Vt V + entryDist V 0 := entryDist_triangle Vt V 0
      _ = entryDist V Vt + entryDist V 0 := by rw [entryDist_comm]
      _ ≤ ε + δ := add_le_add hV hVinv
      _ = δ + ε := by ring
  have hWt0 : entryDist Wt 0 ≤ δ + ε := by
    calc entryDist Wt 0 ≤ entryDist Wt W + entryDist W 0 := entryDist_triangle Wt W 0
      _ = entryDist W Wt + entryDist W 0 := by rw [entryDist_comm]
      _ ≤ ε + δ := add_le_add hW hWinv
      _ = δ + ε := by ring
  have hbound := entryDist_commutator_le V W Vt Wt ε δ (δ + ε) (le_of_lt hε) hVinv hWinv
    hVt0 hWt0 hV hW
  rw [hcard] at hbound
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hstep : ε * (2 * δ + ε) ≤ 3 * (ε * δ) := by nlinarith
  have hm3 : (m : ℝ) ^ 3 ≤ ((m : ℝ) + 1) ^ 3 := by nlinarith
  have hεδ0 : 0 ≤ ε * δ := le_of_lt (mul_pos hε hδ)
  have hm30 : 0 ≤ (m : ℝ) ^ 3 := by positivity
  nlinarith [hbound, hstep, hm3, hεδ0, hm30, hm0]

end Qatlib.Papers.PottsTutte07.MainResults
