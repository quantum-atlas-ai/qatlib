/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BiotSavartIntegrability

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuity of Biot–Savart helicity

Swapping the two points reverses both the scalar triple product order and
the chord. The resulting symmetry of the whole-space pairing allows both
vorticity factors to vary under a uniform bound and strong L¹ convergence.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter Metric MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open scoped Real Topology

local notation "VorticitySpace" => Fin 3 → ℝ

/-- Exchanging the two points and their vorticity values preserves the full kernel. -/
theorem bsPairKernel_swap (ω φ : VorticitySpace → VorticitySpace) (x y : VorticitySpace) :
    bsPairKernel ω φ x y = bsPairKernel φ ω y x := by
  have hlen : euclideanLength (y - x) = euclideanLength (x - y) := by
    simp only [euclideanLength, WithLp.toLp_sub]
    exact norm_sub_rev _ _
  rw [bsPairKernel, bsPairKernel, hlen]
  congr 1
  simp [dot3, cross3, Pi.sub_apply]
  ring

/-- The continuous Biot–Savart pairing is symmetric by product-measure exchange. -/
theorem crossPairing_comm (ω φ : VorticitySpace → VorticitySpace) :
    crossPairing ω φ = crossPairing φ ω := by
  unfold crossPairing
  calc
    _ = ∫ p : VorticitySpace × VorticitySpace,
        bsPairKernel φ ω p.swap.1 p.swap.2 ∂(volume.prod volume) :=
      integral_congr_ae (Eventually.of_forall fun p => bsPairKernel_swap ω φ p.1 p.2)
    _ = _ := integral_prod_swap (μ := (volume : Measure VorticitySpace))
      (ν := (volume : Measure VorticitySpace))
      (fun p => bsPairKernel φ ω p.1 p.2)

/-- Biot–Savart self-helicity is continuous under strong L¹ convergence
of integrable vorticities with a common pointwise bound. -/
theorem tendsto_crossPairing_self_of_bounded {ι : Type*} {l : Filter ι}
    {φ : VorticitySpace → VorticitySpace} (F : ι → VorticitySpace → VorticitySpace)
    (hmφ : Measurable φ) (hmF : ∀ i, Measurable (F i))
    (hφ : Integrable φ) (hF : ∀ i, Integrable (F i)) {M : ℝ}
    (hboundφ : ∀ x, ‖φ x‖ ≤ M) (hboundF : ∀ i x, ‖F i x‖ ≤ M)
    (hL1 : Tendsto (fun i => ∫ y, ‖F i y - φ y‖) l (𝓝 0)) :
    Tendsto (fun i => crossPairing (F i) (F i)) l (𝓝 (crossPairing φ φ)) := by
  let mass := ∫ x, ‖φ x‖
  let near := M * (∫ z in ball (0 : VorticitySpace) 1, (‖z‖ ^ 2)⁻¹)
  let error := fun i => ∫ y, ‖F i y - φ y‖
  have herror : Tendsto error l (𝓝 0) := hL1
  have hmass : ∀ᶠ i in l, (∫ x, ‖F i x‖) ≤ mass + 1 := by
    filter_upwards [(tendsto_order.1 herror).2 1 zero_lt_one] with i hi
    have hnorm (x : VorticitySpace) : ‖F i x‖ ≤ ‖F i x - φ x‖ + ‖φ x‖ := by
      calc
        ‖F i x‖ = ‖(F i x - φ x) + φ x‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    calc
      (∫ x, ‖F i x‖) ≤ ∫ x, (‖F i x - φ x‖ + ‖φ x‖) :=
        integral_mono (hF i).norm (((hF i).sub hφ).norm.add hφ.norm) hnorm
      _ = error i + mass := integral_add ((hF i).sub hφ).norm hφ.norm
      _ ≤ mass + 1 := (add_le_add_left hi.le mass).trans_eq (add_comm 1 mass)
  have hleft : Tendsto (fun i => crossPairing (F i) (F i) - crossPairing (F i) φ) l (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simp only [Real.dist_eq, sub_zero]
    refine squeeze_zero' (g := fun i => 3 / (2 * π) * (near + (mass + 1)) * error i)
      (Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
    · filter_upwards [hmass] with i hi
      calc
        |crossPairing (F i) (F i) - crossPairing (F i) φ| ≤
            3 / (2 * π) * (near + (∫ x, ‖F i x‖)) * error i :=
          abs_crossPairing_sub_right_le_of_bounded (hmF i) (hmF i) hmφ (hF i) (hF i) hφ (hboundF i)
        _ ≤ 3 / (2 * π) * (near + (mass + 1)) * error i := by
          apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (add_le_add_right hi near) (by positivity)
    · simpa only [mul_zero] using
        (tendsto_const_nhds (x := 3 / (2 * π) * (near + (mass + 1)))).mul herror
  have hright := tendsto_crossPairing_right_of_bounded F hmφ hmφ hmF hφ hφ hF hboundφ hL1
  have hright' : Tendsto (fun i => crossPairing (F i) φ) l (𝓝 (crossPairing φ φ)) := by
    simpa only [crossPairing_comm φ] using hright
  simpa only [zero_add, sub_add_cancel] using hleft.add hright'

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
