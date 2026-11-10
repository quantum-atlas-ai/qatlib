/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Lemma41
import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Contraction
import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Unitary
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem lemma61_vector_transitive_self (A B : Submodule ℂ E) (W : E ≃ₗᵢ[ℂ] E)
    (ψ : E) :
    ∃ T : E →L[ℂ] E, ApproximableBy (bridgeGenerators A B W) T ∧ T ψ = ψ :=
  ⟨1, ApproximableBy.id _, by simp⟩

theorem lemma61_preserved_vector {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (hAB : Module.finrank ℂ A < Module.finrank ℂ B) (W : E ≃ₗᵢ[ℂ] E) :
    ∃ v ∈ B, v ≠ 0 ∧ (W v : E) ∈ B :=
  exists_preserved_vector hBA hAB W

theorem lemma61_contraction_geometric {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsBridge A B W) :
    ∃ u ∈ A, ‖u‖ = 1 ∧ ‖A.starProjection (W u)‖ < 1 ∧
      ∀ (c : ℝ), 0 ≤ c → ∀ ε : ℝ, 0 < ε →
        ∃ n : ℕ, c * ‖A.starProjection (W u)‖ ^ n < ε := by
  obtain ⟨u, huA, hu1, hlt⟩ := bridge_contraction_factor hBA W hW
  refine ⟨u, huA, hu1, hlt, fun c _ ε hε => ?_⟩
  exact geom_decay_real ‖A.starProjection (W u)‖ c (norm_nonneg _) hlt ε hε

omit [FiniteDimensional ℂ E] in

theorem lemma61_A_component_decay (u : E) (hu : ‖u‖ = 1) (x : ℕ → ℂ) (a : ℂ)
    (hx : ∀ n, x (n + 1) = a * x n) (ha : ‖a‖ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖(x n) • u‖ < ε :=
  contraction_A_component_decay u hu x a hx ha

omit [FiniteDimensional ℂ E] in

theorem lemma61_contraction_approach (u v : E) (hu : ‖u‖ = 1) (x : ℕ → ℂ) (a β : ℂ)
    (hx : ∀ n, x (n + 1) = a * x n) (ha : ‖a‖ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖(x n) • u + β • v - β • v‖ < ε :=
  contraction_approach_B u v hu x a β hx ha

theorem specialUnitary_fixes_orthogonal {A : Submodule ℂ E} {T : E →L[ℂ] E}
    (hT : T ∈ SpecialUnitary A) {x : E} (hx : x ∈ Aᗮ) : T x = x := by
  obtain ⟨U, _hU, hTx⟩ := hT
  have hP : A.orthogonalProjection x = 0 :=
    (Submodule.orthogonalProjection_eq_zero_iff (K := A)).2 hx
  have hS : A.starProjection x = 0 := by
    rw [Submodule.starProjection_apply, hP]
    simp
  rw [hTx, hP, hS]
  simp

theorem specialUnitary_approximable {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E)
    {T : E →L[ℂ] E} (hT : T ∈ SpecialUnitary A) :
    ApproximableBy (bridgeGenerators A B W) T :=
  ApproximableBy.of_mem (Or.inl (Or.inl hT))

theorem lemma61_step_place {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (hA : 2 ≤ Module.finrank ℂ A) (hB : 2 ≤ Module.finrank ℂ B)
    (W : E ≃ₗᵢ[ℂ] E) {u0 u1 : A} (hu0 : ‖u0‖ = 1) (hu1 : ‖u1‖ = 1)
    {v0 v1 : B} (hv0 : ‖v0‖ = 1) (hv1 : ‖v1‖ = 1) (α β : ℂ) :
    ∃ T : E →L[ℂ] E, ApproximableBy (bridgeGenerators A B W) T ∧
      T (α • (u0 : E) + β • (v0 : E)) = α • (u1 : E) + β • (v1 : E) := by
  obtain ⟨TA, hTA, hTAval⟩ := specialUnitary_sphere_transitive (A := A) hA hu0 hu1
  obtain ⟨TB, hTB, hTBval⟩ := specialUnitary_sphere_transitive (A := B) hB hv0 hv1
  have hAB : Bᗮ = A := by
    rw [← hBA]
    exact Submodule.orthogonal_orthogonal A
  have hTBfix : TB (u0 : E) = (u0 : E) :=
    specialUnitary_fixes_orthogonal hTB (by rw [hAB]; exact u0.2)
  have hTAfix : TA (v1 : E) = (v1 : E) :=
    specialUnitary_fixes_orthogonal hTA (by rw [hBA]; exact v1.2)
  refine ⟨TA.comp TB, ?_, ?_⟩
  · exact ApproximableBy.comp (lemma41_generators_nonExpanding W)
      (fun x => le_of_eq (specialUnitary_norm hTA x))
      (specialUnitary_approximable (A := A) (B := B) W hTA)
      (ApproximableBy.of_mem (Or.inl (Or.inr hTB)))
  · rw [ContinuousLinearMap.comp_apply]
    simp only [map_add, map_smul, hTBval, hTBfix, hTAval, hTAfix]

theorem contraction_factor_of_component {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (x : E) (hx1 : ‖x‖ = 1) {β : E} (hβB : β ∈ B) (hβne : inner ℂ x β ≠ 0) :
    ‖A.starProjection x‖ < 1 := by
  have hβorth : β ∈ Aᗮ := hBA ▸ hβB
  have hwperpB : x - A.starProjection x ∈ Aᗮ := A.sub_starProjection_mem_orthogonal x
  have hPA : A.starProjection x ∈ A := by
    rw [Submodule.starProjection_apply]
    exact Subtype.coe_prop _
  have hwperp_ne : x - A.starProjection x ≠ 0 := by
    intro h0
    apply hβne
    have hx : x = A.starProjection x := sub_eq_zero.mp h0
    rw [hx]
    exact Submodule.inner_right_of_mem_orthogonal (K := A) hPA hβorth
  have horth : inner ℂ (A.starProjection x) (x - A.starProjection x) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := A) hPA hwperpB
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (A.starProjection x) (x - A.starProjection x) horth
  have hsum : A.starProjection x + (x - A.starProjection x) = x := by abel
  rw [hsum, hx1] at hpyth
  have hperp_sq_pos : 0 < ‖x - A.starProjection x‖ ^ 2 := by
    have hpos : 0 < ‖x - A.starProjection x‖ := by
      rw [norm_pos_iff]; exact hwperp_ne
    positivity
  have hPsq : ‖A.starProjection x‖ ^ 2 < 1 := by nlinarith
  nlinarith [norm_nonneg (A.starProjection x)]

theorem lemma61_bridge_normalized {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (hA : 2 ≤ Module.finrank ℂ A) (W : E ≃ₗᵢ[ℂ] E) (hW : IsBridge A B W)
    {v : E} (hWvB : (W v : E) ∈ B) :
    ∃ W' : E →L[ℂ] E, ApproximableBy (bridgeGenerators A B W) W' ∧
      (∀ y, ‖W' y‖ = ‖y‖) ∧ W' v ∈ B ∧
      ∃ u ∈ A, ‖u‖ = 1 ∧ ∃ a b : ℂ, ‖a‖ < 1 ∧
        ∃ w ∈ B, ‖w‖ = 1 ∧ W' u = a • u + b • w := by
  obtain ⟨u0, hu0A, hu01, b0, hb0B, hb0ne⟩ := hW
  set x : E := (W u0 : E) with hxdef
  have hb0ne' : inner ℂ x b0 ≠ 0 := by rw [hxdef]; exact hb0ne
  have hx1 : ‖x‖ = 1 := by rw [hxdef, W.norm_map, hu01]
  have hlt : ‖A.starProjection x‖ < 1 :=
    contraction_factor_of_component hBA x hx1 hb0B hb0ne'
  by_cases hp : A.orthogonalProjection x = 0
  · have hxB : x ∈ B := by
      have horth : x ∈ Aᗮ := (Submodule.orthogonalProjection_eq_zero_iff (K := A)).1 hp
      exact hBA ▸ horth
    refine ⟨(W : E →L[ℂ] E), ApproximableBy.of_mem (Or.inr rfl),
      fun y => W.norm_map y, hWvB, u0, hu0A, hu01, 0, 1, by norm_num, x, hxB,
      hx1, ?_⟩
    simp [hxdef]
  · set p : A := A.orthogonalProjection x with hpdef
    have hpne0 : p ≠ 0 := by rw [hpdef]; exact hp
    have hpnorm : ‖p‖ ≠ 0 := fun h => hpne0 (norm_eq_zero.mp h)
    have hc0 : ((‖p‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpnorm
    set u : A := ((‖p‖ : ℝ) : ℂ)⁻¹ • p with hudef
    have hu1 : ‖u‖ = 1 := by
      rw [hudef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ hpnorm]
    obtain ⟨U, hU, hUval⟩ :=
      specialUnitary_sphere_transitive (A := A) hA (u := u) (v := ⟨u0, hu0A⟩) hu1
        (by simpa using hu01)
    have hsp : (p : E) = A.starProjection x := by
      rw [hpdef, Submodule.starProjection_apply]
    have hpsmul : (p : A) = ((‖p‖ : ℝ) : ℂ) • u := by
      rw [hudef, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    set q : E := x - (p : E) with hqdef
    have hqsplit : x = (p : E) + q := by rw [hqdef]; abel
    have hqorth : q ∈ Aᗮ := by
      rw [hqdef, hsp]
      exact A.sub_starProjection_mem_orthogonal x
    have hqne : q ≠ 0 := by
      intro h0
      apply hb0ne'
      have hxeq : x = (p : E) := by rw [hqsplit, h0, add_zero]
      rw [hxeq]
      exact Submodule.inner_right_of_mem_orthogonal (K := A) p.2 (hBA ▸ hb0B)
    have hqnorm : ‖q‖ ≠ 0 := fun h => hqne (norm_eq_zero.mp h)
    have hd0 : ((‖q‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqnorm
    set w : E := ((‖q‖ : ℝ) : ℂ)⁻¹ • q with hwdef
    have hw1 : ‖w‖ = 1 := by
      rw [hwdef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ hqnorm]
    have hwB : w ∈ B := by
      rw [hwdef]
      exact B.smul_mem _ (hBA ▸ hqorth)
    have hltp : ‖p‖ < 1 := by
      rw [← Submodule.norm_coe p, hsp]
      exact hlt
    have ha_lt : ‖((‖p‖ : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact hltp
    have hcoe_sub : (p : E) = ((‖p‖ : ℝ) : ℂ) • (u : E) := by
      simpa using congrArg (Submodule.subtype A) hpsmul
    have hUp : U (p : E) = ((‖p‖ : ℝ) : ℂ) • (u0 : E) := by
      rw [hcoe_sub, map_smul, hUval]
    have hUq : U q = q := specialUnitary_fixes_orthogonal hU hqorth
    have hW'u : (U.comp W.toContinuousLinearMap : E →L[ℂ] E) (u0 : E) =
        ((‖p‖ : ℝ) : ℂ) • (u0 : E) + ((‖q‖ : ℝ) : ℂ) • w := by
      have happ : (U.comp W.toContinuousLinearMap : E →L[ℂ] E) (u0 : E) = U x := rfl
      rw [happ, hqsplit, map_add, hUp, hUq]
      congr 1
      rw [hwdef, smul_smul, mul_inv_cancel₀ hd0, one_smul]
    have hnorm' : ∀ y, ‖(U.comp W.toContinuousLinearMap : E →L[ℂ] E) y‖ = ‖y‖ := by
      intro y
      have hval : (U.comp W.toContinuousLinearMap : E →L[ℂ] E) y = U (W y : E) := rfl
      rw [hval, specialUnitary_norm hU (W y : E), W.norm_map]
    have hW'v : (U.comp W.toContinuousLinearMap : E →L[ℂ] E) v ∈ B := by
      have hfix : U (W v : E) = (W v : E) :=
        specialUnitary_fixes_orthogonal hU (hBA ▸ hWvB)
      have hval : (U.comp W.toContinuousLinearMap : E →L[ℂ] E) v = U (W v : E) := rfl
      rw [hval, hfix]
      exact hWvB
    have happr : ApproximableBy (bridgeGenerators A B W) (U.comp W.toContinuousLinearMap : E →L[ℂ] E) :=
      ApproximableBy.comp (lemma41_generators_nonExpanding W)
        (fun y => le_of_eq (specialUnitary_norm hU y))
        (specialUnitary_approximable (A := A) (B := B) W hU)
        (ApproximableBy.of_mem (Or.inr rfl))
    exact ⟨(U.comp W.toContinuousLinearMap : E →L[ℂ] E), happr, hnorm', hW'v, u0, hu0A, hu01,
      ((‖p‖ : ℝ) : ℂ), ((‖q‖ : ℝ) : ℂ), ha_lt, w, hwB, hw1, hW'u⟩

end Qatlib.Papers.BQPJonesPoly06.MainResults
