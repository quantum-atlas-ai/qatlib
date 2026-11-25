/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.LowMemoryReduction
public import Qatlib.Papers.HydroSpinLatt21.GKModel.BesselDerivative

import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A low-memory estimate for the circular-orbit Bessel force

[Saenz2021HydroSpinLattices], equations (14), (15), and (17),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
For two separated circular orbits, the first-order Bessel wave force
projected onto either azimuth varies at a bounded rate with the
neighbor's phase. A uniform bound on the neighbor's angular speed
then controls the full exponential history error. A half turn about
the midpoint exchanges the two orbits and their force projections.
The scalar force prefactor is taken as a parameter.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open MeasureTheory
open scoped Real

/-- The force is continuously differentiable on the full two-phase plane
because the circular orbits are uniformly separated. -/
private theorem contDiff_left_bessel_force (F k r L : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4) :
    ContDiff ℝ 1 (fun q : ℝ × ℝ => leftAzimuthForce F besselJ0Slope k r L q.1 q.2) := by
  have hdistPos (q : ℝ × ℝ) : 0 < pairDist r L q.1 q.2 :=
    (half_pos hL).trans_le (pairDist_ge_half r L q.1 q.2 hL hr hsmall)
  have hsep : ContDiff ℝ 1 (fun q : ℝ × ℝ => pairSepSq r L q.1 q.2) := by
    simp only [pairSepSq_eq]
    fun_prop
  have hdist : ContDiff ℝ 1 (fun q : ℝ × ℝ => pairDist r L q.1 q.2) := by
    refine hsep.sqrt fun q hz => ?_
    have h := hdistPos q
    rw [pairDist, hz, Real.sqrt_zero] at h
    exact (lt_irrefl _) h
  have hprofile : ContDiff ℝ 1 besselJ0Slope :=
    contDiff_one_iff_deriv.2 ⟨differentiable_besselJ0Slope,
      differentiable_besselJ0Curv.continuous⟩
  unfold leftAzimuthForce
  refine (((contDiff_const.mul (hprofile.comp (contDiff_const.mul hdist))).div
    hdist (fun q => (hdistPos q).ne')).neg).mul ?_
  fun_prop

/-- On separated orbits a single derivative bound works for all receiving and
emitting phases. Both phase coordinates reduce to a compact period square. -/
theorem uniform_left_bessel_force_deriv_bound (F k r L : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4) :
    ∃ C ≥ 0, ∀ φ ψ, ‖deriv (fun θ => leftAzimuthForce F besselJ0Slope k r L φ θ) ψ‖ ≤ C := by
  let f := fun q : ℝ × ℝ => leftAzimuthForce F besselJ0Slope k r L q.1 q.2
  have hf : ContDiff ℝ 1 f := contDiff_left_bessel_force F k r L hL hr hsmall
  let d := fun q : ℝ × ℝ => fderiv ℝ f q (0, 1)
  have hd : Continuous d := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hperiod (v : ℝ × ℝ) (hv : ∀ q, f (q + v) = f q) (q : ℝ × ℝ) :
      d (q + v) = d q := by
    unfold d
    rw [← fderiv_comp_add_right v, funext hv]
  have hφ (ψ : ℝ) : Function.Periodic (fun φ => d (φ, ψ)) (2 * π) := by
    intro φ
    have hs := hperiod (2 * π, 0) (fun q => by
      simp only [Prod.fst_add, Prod.snd_add, add_zero, f, leftAzimuthForce, pairDist, pairSepSq_eq,
        Real.cos_add_two_pi, Real.sin_add_two_pi]
      rw [show q.1 + 2 * π - q.2 = q.1 - q.2 + 2 * π by ring, Real.sin_add_two_pi]) (φ, ψ)
    simpa using hs
  have hψ (φ : ℝ) : Function.Periodic (fun ψ => d (φ, ψ)) (2 * π) := by
    intro ψ
    have hs := hperiod (0, 2 * π) (fun q => by
      simp [Prod.fst_add, Prod.snd_add, f, leftAzimuthForce, pairDist, pairSepSq_eq,
        Real.cos_add_two_pi, Real.sin_add_two_pi, sub_add_eq_sub_sub, Real.sin_sub_two_pi]) (φ, ψ)
    simpa using hs
  have hCompact : IsCompact (d '' (Set.Icc 0 (2 * π) ×ˢ Set.Icc 0 (2 * π))) :=
    (isCompact_Icc.prod isCompact_Icc).image hd
  obtain ⟨C, hC, hbound⟩ := hCompact.isBounded.exists_pos_norm_le
  refine ⟨C, hC.le, fun φ ψ => ?_⟩
  obtain ⟨φ', hφ', heφ⟩ := (hφ ψ).exists_mem_Ico₀ Real.two_pi_pos φ
  obtain ⟨ψ', hψ', heψ⟩ := (hψ φ').exists_mem_Ico₀ Real.two_pi_pos ψ
  have hsection : HasDerivAt (fun θ : ℝ => (φ, θ)) (0, 1) ψ :=
    (hasDerivAt_const ψ φ).prodMk (hasDerivAt_id ψ)
  have hpartial : deriv (fun θ => f (φ, θ)) ψ = d (φ, ψ) :=
    (((hf.differentiable (by norm_num) (φ, ψ)).hasFDerivAt).comp_hasDerivAt ψ hsection).deriv
  change ‖deriv (fun θ => f (φ, θ)) ψ‖ ≤ C
  rw [hpartial]
  change d (φ, ψ) = d (φ', ψ) at heφ
  change d (φ', ψ) = d (φ', ψ') at heψ
  rw [heφ, heψ]
  exact hbound _ ⟨(φ', ψ'), ⟨⟨hφ'.1, hφ'.2.le⟩, ⟨hψ'.1, hψ'.2.le⟩⟩, rfl⟩

/-- A uniform derivative bound for an orbit profile controls its exponentially
weighted history along every bounded-speed emitter path. -/
private theorem orbit_memory_error (f profile θ : ℝ → ℝ) (C Ω t T : ℝ)
    (hprofile : ∀ ψ, profile ψ = f ψ)
    (hC : 0 ≤ C) (hf : Differentiable ℝ f) (hbound : ∀ ψ, ‖deriv f ψ‖ ≤ C)
    (hθ : Differentiable ℝ θ) (hΩ : ∀ s, ‖deriv θ s‖ ≤ Ω) (hT : 0 < T) :
    IntegrableOn (fun u => profile (θ (t - u)) * Real.exp (-(u / T))) (Set.Ioi 0) ∧
      |(∫ u in Set.Ioi (0 : ℝ), profile (θ (t - u)) * Real.exp (-(u / T))) / T -
        f (θ t)| ≤ C * Ω * T := by
  let g := fun u => f (θ (t - u))
  have hg (u : ℝ) : HasDerivAt g (deriv f (θ (t - u)) * (-deriv θ (t - u))) u := by
    have hline : HasDerivAt (fun v : ℝ => t - v) (-1) u :=
      (hasDerivAt_id u).const_sub t
    have hh := ((hθ (t - u)).hasDerivAt.comp u hline).congr_deriv
      (by ring : deriv θ (t - u) * (-1) = -deriv θ (t - u))
    change HasDerivAt (f ∘ (θ ∘ fun v : ℝ => t - v)) _ u
    exact (hf (θ (t - u))).hasDerivAt.comp u hh
  have hB (u : ℝ) : ‖deriv g u‖ ≤ C * Ω := by
    rw [(hg u).deriv, norm_mul, norm_neg]
    exact mul_le_mul (hbound _) (hΩ _) (norm_nonneg _) hC
  have hLip (u : ℝ) (hu : 0 ≤ u) : |g u - g 0| ≤ C * Ω * u := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun v _ => (hg v).differentiableAt) (fun v _ => hB v) convex_univ
      (Set.mem_univ 0) (Set.mem_univ u)
    simpa [Real.norm_eq_abs, abs_of_nonneg hu] using h
  have hgc : Continuous g := (show Differentiable ℝ g from fun u => (hg u).differentiableAt).continuous
  simp only [hprofile]
  refine ⟨(full_memory_integral_bound T (C * Ω) hT g hgc hLip).1, ?_⟩
  simpa only [g, sub_zero] using memory_average_error T (C * Ω) hT g hgc hLip

/-- Restricting the smooth two-phase force to a fixed receiving phase
gives a differentiable emitter profile. -/
private theorem differentiable_left_bessel_force_section (F k r L φ : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4) :
    Differentiable ℝ (fun ψ => leftAzimuthForce F besselJ0Slope k r L φ ψ) := by
  have hsection : ContDiff ℝ 1 (fun ψ : ℝ => (φ, ψ)) := contDiff_const.prodMk contDiff_id
  exact ((contDiff_left_bessel_force F k r L hL hr hsmall).comp hsection).differentiable
    (by norm_num)

/-- Integrability and the history error at a particular receiving phase
follow from a bound on its force derivative with respect to emission phase. -/
private theorem left_bessel_memory_of_deriv_bound (F k r L φ C Ω t T : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4) (hC : 0 ≤ C)
    (hbound : ∀ ψ, ‖deriv (fun θ => leftAzimuthForce F besselJ0Slope k r L φ θ) ψ‖ ≤ C)
    (θ : ℝ → ℝ) (hθ : Differentiable ℝ θ) (hΩ : ∀ s, ‖deriv θ s‖ ≤ Ω) (hT : 0 < T) :
    IntegrableOn (fun u => leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u)) *
      Real.exp (-(u / T))) (Set.Ioi 0) ∧
    |(∫ u in Set.Ioi (0 : ℝ), leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u)) *
        Real.exp (-(u / T))) / T -
      leftAzimuthForce F besselJ0Slope k r L φ (θ t)| ≤ C * Ω * T := by
  exact orbit_memory_error
    (fun ψ => leftAzimuthForce F besselJ0Slope k r L φ ψ)
    (fun ψ => leftAzimuthForce (-F) besselJ1Profile k r L φ ψ)
    θ C Ω t T (fun ψ => (azimuth_forces_eq_besselJ1 F k r L φ ψ).1.symm)
    hC (differentiable_left_bessel_force_section F k r L φ hL hr hsmall) hbound hθ hΩ hT

/-- The actual first-order Bessel force for the left circular orbit has
an integrable full past history. If the neighbor phase speed is bounded
by `Ω`, the memory average differs from the instantaneous force by at
most `C Ω T` for every time and positive memory scale. -/
theorem uniform_left_bessel_memory_error (F k r L : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4)
    : ∃ C ≥ 0, ∀ (φ Ω : ℝ) (θ : ℝ → ℝ),
      Differentiable ℝ θ → (∀ s, ‖deriv θ s‖ ≤ Ω) → ∀ t T : ℝ, 0 < T →
      IntegrableOn (fun u => leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u)) *
        Real.exp (-(u / T))) (Set.Ioi 0) ∧
      |(∫ u in Set.Ioi (0 : ℝ), leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u)) *
          Real.exp (-(u / T))) / T -
        leftAzimuthForce F besselJ0Slope k r L φ (θ t)| ≤ C * Ω * T := by
  obtain ⟨C, hC, hbound⟩ := uniform_left_bessel_force_deriv_bound F k r L hL hr hsmall
  refine ⟨C, hC, ?_⟩
  intro φ Ω θ hθ hΩ t T hT
  exact left_bessel_memory_of_deriv_bound F k r L φ C Ω t T hL hr hsmall hC
    (hbound φ) θ hθ hΩ hT

/-- The uniform left-orbit memory estimate specialized to a fixed receiving phase. -/
theorem left_bessel_memory_error (F k r L φ Ω : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4)
    (θ : ℝ → ℝ) (hθ : Differentiable ℝ θ) (hΩ : ∀ s, ‖deriv θ s‖ ≤ Ω) :
    ∃ C ≥ 0, ∀ t T : ℝ, 0 < T →
      IntegrableOn (fun u => leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u)) *
        Real.exp (-(u / T))) (Set.Ioi 0) ∧
      |(∫ u in Set.Ioi (0 : ℝ), leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u)) *
          Real.exp (-(u / T))) / T -
        leftAzimuthForce F besselJ0Slope k r L φ (θ t)| ≤ C * Ω * T := by
  obtain ⟨C, hC, h⟩ := uniform_left_bessel_memory_error F k r L hL hr hsmall
  exact ⟨C, hC, h φ Ω θ hθ hΩ⟩

/-- Exchanging the two wells by a half turn about their midpoint leaves
the exact inter-droplet distance unchanged. -/
theorem pairDist_swap_add_pi (r L φ ψ : ℝ) :
    pairDist r L (ψ + π) (φ + π) = pairDist r L φ ψ := by
  unfold pairDist
  rw [pairSepSq_eq, pairSepSq_eq]
  congr 1
  simp only [Real.cos_add_pi, Real.sin_add_pi]
  ring

/-- In coordinates rotated by a half turn, the right azimuthal projection
becomes the left projection with the observing and emitting wells swapped. -/
theorem rightAzimuthForce_eq_left_swap_add_pi (F : ℝ) (g : ℝ → ℝ)
    (k r L φ ψ : ℝ) :
    rightAzimuthForce F g k r L φ ψ = leftAzimuthForce F g k r L (ψ + π) (φ + π) := by
  unfold rightAzimuthForce leftAzimuthForce
  rw [pairDist_swap_add_pi, Real.sin_add_pi, show ψ + π - (φ + π) = -(φ - ψ) by ring,
    Real.sin_neg]
  ring

/-- The actual first-order Bessel force on the right orbit has an integrable
full past history and normalized memory error bounded by `C Ω T`. -/
theorem uniform_right_bessel_memory_error (F k r L : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4)
    : ∃ C ≥ 0, ∀ (ψ Ω : ℝ) (θ : ℝ → ℝ),
      Differentiable ℝ θ → (∀ s, ‖deriv θ s‖ ≤ Ω) → ∀ t T : ℝ, 0 < T →
      IntegrableOn (fun u => rightAzimuthForce (-F) besselJ1Profile k r L (θ (t - u)) ψ *
        Real.exp (-(u / T))) (Set.Ioi 0) ∧
      |(∫ u in Set.Ioi (0 : ℝ), rightAzimuthForce (-F) besselJ1Profile k r L (θ (t - u)) ψ *
          Real.exp (-(u / T))) / T -
        rightAzimuthForce F besselJ0Slope k r L (θ t) ψ| ≤ C * Ω * T := by
  obtain ⟨C, hC, h⟩ := uniform_left_bessel_memory_error F k r L hL hr hsmall
  refine ⟨C, hC, fun ψ Ω θ hθ hΩ t T hT => ?_⟩
  let shifted := fun s => θ s + π
  have hshift (s : ℝ) : HasDerivAt shifted (deriv θ s) s :=
    (hθ s).hasDerivAt.add_const _
  have h' := h (ψ + π) Ω shifted (fun s => (hshift s).differentiableAt)
    (fun s => by rw [(hshift s).deriv]; exact hΩ s) t T hT
  simpa only [rightAzimuthForce_eq_left_swap_add_pi, shifted] using h'

/-- The uniform right-orbit memory estimate specialized to a fixed receiving phase. -/
theorem right_bessel_memory_error (F k r L ψ Ω : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsmall : r ≤ L / 4)
    (θ : ℝ → ℝ) (hθ : Differentiable ℝ θ) (hΩ : ∀ s, ‖deriv θ s‖ ≤ Ω) :
    ∃ C ≥ 0, ∀ t T : ℝ, 0 < T →
      IntegrableOn (fun u => rightAzimuthForce (-F) besselJ1Profile k r L (θ (t - u)) ψ *
        Real.exp (-(u / T))) (Set.Ioi 0) ∧
      |(∫ u in Set.Ioi (0 : ℝ), rightAzimuthForce (-F) besselJ1Profile k r L (θ (t - u)) ψ *
          Real.exp (-(u / T))) / T -
        rightAzimuthForce F besselJ0Slope k r L (θ t) ψ| ≤ C * Ω * T := by
  obtain ⟨C, hC, h⟩ := uniform_right_bessel_memory_error F k r L hL hr hsmall
  exact ⟨C, hC, h ψ Ω θ hθ hΩ⟩

end Qatlib.Papers.HydroSpinLatt21.BesselModel
