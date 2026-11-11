/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordTransport
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.InhomogeneousTransport

set_option backward.isDefEq.respectTransparency false

/-! # Noncircular bounds for pure transverse transport derivatives -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- This estimate only assumes strictly lower derivatives of q. Its highest
word derivative is the forced unknown, and is never assumed bounded. -/
theorem spatialWordPartial_transverse_transport_bound (q K : SpatialPoint → ℍ)
    (hq : ContDiff ℝ ∞ q) (hK : ContDiff ℝ ∞ K)
    (hunit : ∀ x : SpatialPoint, InUnitCube x → ‖q x‖=1)
    (hpure : ∀ x : SpatialPoint, InUnitCube x → (K x).re=0)
    (hode : ∀ x : SpatialPoint, 0 ≤ x 0 ∧ x 0 ≤ 1 → spatialWordPartial q [0] x=q x*K x)
    (c : ℍ) (hplane : ∀ x : SpatialPoint, x 0=0 → q x=c)
    (F G : ℕ → ℝ) (w : List (Fin 3)) (htrans : ∀ i ∈ w, i≠0) (hw : w≠[])
    (hF : ∀ j < w.length, 0 ≤ F j) (hG : ∀ j ≤ w.length, 0 ≤ G j)
    (hqB : ∀ u : List (Fin 3), u.length < w.length → ∀ x, InUnitCube x →
      ‖spatialWordPartial q u x‖ ≤ F u.length)
    (hKB : ∀ u : List (Fin 3), u.length ≤ w.length → ∀ x, InUnitCube x →
      ‖spatialWordPartial K u x‖ ≤ G u.length)
    (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial q w x‖ ≤ wordProductRemainderMajorant F G w.length := by
  let line : ℝ → SpatialPoint := fun t => x+(t-x 0) • EuclideanSpace.single 0 1
  have hlineD (t : ℝ) : HasDerivAt line (EuclideanSpace.single 0 1) t := by
    convert (hasDerivAt_const t x).add (((hasDerivAt_id t).sub_const (x 0)).smul_const
      (EuclideanSpace.single 0 (1 : ℝ))) using 1 <;>
      first | rfl | simp only [sub_zero,one_smul,zero_add]
  have hlineC : Continuous line := continuous_const.add
    ((continuous_id.sub continuous_const).smul continuous_const)
  have hcoord (t : ℝ) : line t 0=t := by simp [line]
  have hcube (t : ℝ) (ht : t ∈ Icc 0 (x 0)) : InUnitCube (line t) := by
    intro i
    fin_cases i
    · simpa [line] using And.intro ht.1 (ht.2.trans (hx 0).2)
    · simpa [line] using hx 1
    · simpa [line] using hx 2
  let z : ℝ → ℍ := fun t => spatialWordPartial q w (line t)
  let f : ℝ → ℍ := fun t => spatialWordPartial (fun y => q y*K y) w (line t)-z t*K (line t)
  have hforceC : Continuous f :=
    ((contDiff_spatialWordPartial _ (hq.mul hK) w).continuous.comp hlineC).sub
      (((contDiff_spatialWordPartial q hq w).continuous.comp hlineC).mul (hK.continuous.comp hlineC))
  have hqd (t : ℝ) (ht : t ∈ Icc 0 (x 0)) :
      HasDerivWithinAt (fun t => q (line t)) (q (line t)*K (line t)) (Icc 0 (x 0)) t := by
    have hd := ((hq.differentiable (by simp) (line t)).hasFDerivAt).comp_hasDerivAt t (hlineD t)
    have hslab : 0 ≤ line t 0 ∧ line t 0 ≤ 1 := (hcube t ht) 0
    change HasDerivAt (fun t => q (line t)) (spatialWordPartial q [0] (line t)) t at hd
    rw [hode _ hslab] at hd
    exact hd.hasDerivWithinAt
  have hzd (t : ℝ) (ht : t ∈ Icc 0 (x 0)) :
      HasDerivWithinAt z (z t*K (line t)+f t) (Icc 0 (x 0)) t := by
    have hd := (((contDiff_spatialWordPartial q hq w).differentiable (by simp) (line t)).hasFDerivAt).comp_hasDerivAt t (hlineD t)
    have hslab : 0 ≤ line t 0 ∧ line t 0 ≤ 1 := (hcube t ht) 0
    change HasDerivAt z (spatialWordPartial q (0::w) (line t)) t at hd
    rw [spatialWordPartial_transport_slab q K hq hK hode w _ hslab] at hd
    convert hd.hasDerivWithinAt using 1
    dsimp only [f]
    abel
  have hz0 : z 0=0 := spatialWordPartial_plane_constant q hq c hplane w htrans hw _ (hcoord 0)
  have he (t : ℝ) (ht : t ∈ Icc 0 (x 0)) :
      ‖f t‖ ≤ wordProductRemainderMajorant F G w.length :=
    spatialWordPartial_mul_remainder_norm_le q K hq hK F G w (line t) hF hG
      (fun u hu => hqB u hu _ (hcube t ht)) (fun u hu => hKB u hu _ (hcube t ht))
  have hE : 0 ≤ wordProductRemainderMajorant F G w.length :=
    (norm_nonneg _).trans (he 0 ⟨le_rfl,(hx 0).1⟩)
  have hbound := inhomogeneous_transport_norm_le (hx 0).1 hforceC.continuousOn hqd hzd
    (fun t ht => hpure _ (hcube t ht)) (fun t ht => hunit _ (hcube t ht)) hz0 he
  have hfinal : (x 0)*wordProductRemainderMajorant F G w.length ≤
      wordProductRemainderMajorant F G w.length := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hx 0).2 hE
  have hzx : z (x 0)=spatialWordPartial q w x := by simp [z,line]
  rw [hzx,sub_zero] at hbound
  exact hbound.trans hfinal

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
