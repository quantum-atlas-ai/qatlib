/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.VanishCharge.ClebschFieldBridge

import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-!
# Full-space helicity and flux at infinity

For globally defined smooth Clebsch potentials with integrable
helicity density, the full-space integral is the limit of the signed
face fluxes. Compact support of the phase is a sufficient condition
for both integrability and vanishing asymptotic flux.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.VanishCharge

open BoxIntegral Filter MeasureTheory Set
open scoped BigOperators Topology

/-- The centered cube of radius `n + 1` in the three spatial coordinates. -/
def clebschExpandingBox (n : ℕ) : Box (Fin 3) where
  lower := fun _ => -((n : ℝ) + 1)
  upper := fun _ => (n : ℝ) + 1
  lower_lt_upper := by
    intro i
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The signed sum of actual Clebsch fluxes through the six box faces. -/
noncomputable def clebschBoxFaceFlux (φ α β : (Fin 3 → ℝ) → ℝ) (I : Box (Fin 3)) : ℝ :=
  ∑ i : Fin 3,
    ((∫ y in (I.face i : Set (Fin 2 → ℝ)), clebschFlux φ α β (i.insertNth (I.upper i) y) i) -
      ∫ y in (I.face i : Set (Fin 2 → ℝ)), clebschFlux φ α β (i.insertNth (I.lower i) y) i)

/-- The centered Clebsch boxes increase with their radii. -/
private theorem monotone_clebschExpandingBox :
    Monotone (fun n => (clebschExpandingBox n : Set (Fin 3 → ℝ))) := by
  intro m n hmn x hx i
  have hle : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have h := (Box.mem_def _).mp ((Box.mem_coe _).mp hx) i
  change -((m : ℝ) + 1) < x i ∧ x i ≤ (m : ℝ) + 1 at h
  change -((n : ℝ) + 1) < x i ∧ x i ≤ (n : ℝ) + 1
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The centered Clebsch boxes exhaust all of Cartesian space. -/
private theorem iUnion_clebschExpandingBox :
    (⋃ n, (clebschExpandingBox n : Set (Fin 3 → ℝ))) = univ := by
  ext x
  simp only [mem_univ, iff_true, mem_iUnion]
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine ⟨n, fun i => ?_⟩
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  obtain ⟨hlo, hhi⟩ := abs_le.mp hi
  change -((n : ℝ) + 1) < x i ∧ x i ≤ (n : ℝ) + 1
  exact ⟨by linarith, by linarith⟩

/-- The full-space helicity is the limit of the actual outward
Clebsch fluxes from an exhaustion by centered boxes. -/
theorem tendsto_clebschBoxFaceFlux_integral (φ α β : (Fin 3 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β)
    (hInt : Integrable (clebschHelicityDensity φ α β)) :
    Tendsto (fun n => clebschBoxFaceFlux φ α β (clebschExpandingBox n)) atTop
      (𝓝 (∫ x, clebschHelicityDensity φ α β x)) := by
  have h := tendsto_setIntegral_of_monotone (μ := volume)
    (fun n => (clebschExpandingBox n).measurableSet_coe) monotone_clebschExpandingBox
    hInt.integrableOn
  rw [iUnion_clebschExpandingBox, setIntegral_univ] at h
  have hbox (n : ℕ) :
      (∫ x in (clebschExpandingBox n : Set (Fin 3 → ℝ)), clebschHelicityDensity φ α β x) =
      clebschBoxFaceFlux φ α β (clebschExpandingBox n) := by
    simpa only [clebschBoxFaceFlux] using
      integral_clebschHelicityDensity_eq_faceFlux φ α β (clebschExpandingBox n) hφ hα hβ
  simpa only [hbox] using h

/-- If the signed fluxes have an asymptotic value, that value
is the integral of the actual Clebsch helicity density. -/
theorem integral_clebschHelicityDensity_eq_farFlux (φ α β : (Fin 3 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β)
    (hInt : Integrable (clebschHelicityDensity φ α β)) {L : ℝ}
    (hL : Tendsto (fun n => clebschBoxFaceFlux φ α β (clebschExpandingBox n)) atTop (𝓝 L)) :
    (∫ x, clebschHelicityDensity φ α β x) = L :=
  tendsto_nhds_unique (tendsto_clebschBoxFaceFlux_integral φ α β hφ hα hβ hInt) hL

/-- The helicity density vanishes off the support of a smooth
phase, where both the phase and its derivative vanish. -/
private theorem clebschHelicityDensity_eq_zero_off_tsupport {φ α β : (Fin 3 → ℝ) → ℝ}
    (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β) {x : Fin 3 → ℝ} (hx : x ∉ tsupport φ) :
    clebschHelicityDensity φ α β x = 0 := by
  have hz (z : Fin 3 → ℝ) (hz : z ∉ tsupport φ) : φ z = 0 :=
    Function.notMem_support.mp fun hn => hz (subset_closure hn)
  have he : φ =ᶠ[𝓝 x] (fun _ => 0) :=
    Filter.Eventually.mono (show ∀ᶠ z in 𝓝 x, z ∉ tsupport φ from
      (isClosed_tsupport φ).isOpen_compl.mem_nhds hx) hz
  have hd : fderiv ℝ φ x = 0 := by
    simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜 := ℝ)
  have htrace := clebschFluxDeriv_trace (φ := φ) (x := x) hα.contDiffAt hβ.contDiffAt
  simpa [clebschFluxDeriv, hz x hx, hd] using htrace.symm

/-- The actual helicity density has compact support when the
globally defined phase has compact support. -/
theorem hasCompactSupport_clebschHelicityDensity {φ α β : (Fin 3 → ℝ) → ℝ}
    (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β) (hφc : HasCompactSupport φ) :
    HasCompactSupport (clebschHelicityDensity φ α β) := by
  apply hφc.of_isClosed_subset (isClosed_tsupport (clebschHelicityDensity φ α β))
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra h
  exact (Function.mem_support.mp hx) (clebschHelicityDensity_eq_zero_off_tsupport hα hβ h)

/-- A compactly supported smooth phase has zero total helicity
in the actual full-space Clebsch model. -/
theorem integral_clebschHelicityDensity_eq_zero_of_hasCompactSupport
    (φ α β : (Fin 3 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β)
    (hφc : HasCompactSupport φ) :
    (∫ x, clebschHelicityDensity φ α β x) = 0 := by
  have hInt : Integrable (clebschHelicityDensity φ α β) :=
    (continuous_clebschHelicityDensity hφ hα hβ).integrable_of_hasCompactSupport
      (hasCompactSupport_clebschHelicityDensity hα hβ hφc)
  apply integral_clebschHelicityDensity_eq_farFlux φ α β hφ hα hβ hInt
  obtain ⟨B, hB⟩ := hφc.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt B
  have he : ∀ᶠ n : ℕ in atTop, clebschBoxFaceFlux φ α β (clebschExpandingBox n) = 0 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNN : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hface (i : Fin 3) (b : ℝ) (hb : |b| = (n : ℝ) + 1) (y : Fin 2 → ℝ) :
        clebschFlux φ α β (i.insertNth b y) i = 0 := by
      have hm : i.insertNth b y ∉ tsupport φ := by
        intro hy
        have hu := hB _ hy
        let z : Fin 3 → ℝ := i.insertNth b y
        have hs : |z i| ≤ ‖z‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
        dsimp only [z] at hs
        rw [Fin.insertNth_apply_same, hb] at hs
        linarith
      have hφ0 : φ (i.insertNth b y) = 0 :=
        Function.notMem_support.mp fun h => hm (subset_closure h)
      simp only [clebschFlux, hφ0, zero_mul]
    have hu (i : Fin 3) (y : Fin 2 → ℝ) :
        clebschFlux φ α β (i.insertNth ((clebschExpandingBox n).upper i) y) i = 0 :=
      hface i ((n : ℝ) + 1) (abs_of_nonneg (by positivity)) y
    have hl (i : Fin 3) (y : Fin 2 → ℝ) :
        clebschFlux φ α β (i.insertNth ((clebschExpandingBox n).lower i) y) i = 0 :=
      hface i (-((n : ℝ) + 1)) (by rw [abs_neg, abs_of_nonneg (by positivity)]) y
    simp only [clebschBoxFaceFlux, hu, hl, MeasureTheory.integral_zero, sub_self, Finset.sum_const_zero]
  exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

end Qatlib.Papers.SuperfluidHel18.VanishCharge
