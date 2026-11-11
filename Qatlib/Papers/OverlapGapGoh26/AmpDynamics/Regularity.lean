/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.FiniteAmp

/-!
# Regularity of AMP spin readouts

Establishes boundedness and Euclidean Lipschitz estimates for the rotation-history coordinate
and affine update in [GohMuller2026]. The catalyst coefficient lies between zero and `4 / 27` on
the unit interval.

The definitions `spinReadoutF` and `spinOutput` express the spin readout as an additional
update, with a clipping identity when `M ≥ 1` and joint continuity in the tensor and seed.

## Main statements

* `fCoord_lipschitz_l2`: bounds history sensitivity through a fixed horizon.
* `actual_extra_spin_step`: realizes the spin output by an additional clipped step.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
open Qatlib.Foundations.MatrixGeometry.AxisRotations.History
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity

/-- The rotation-history readout `phi` has absolute value at most one. -/
theorem phi_abs_le_one (s : ℕ → ℝ) (t : ℕ) (x : Fin t → ℝ) : |phi s t x|≤1 := by
  exact (matrix_entry_le_opNorm _ 2 0).trans_eq (history_norm s t x)

/-- For schedules in `[0, 1]` through horizon `T` and `t ≤ T`, the coordinate map `fCoord` has
Euclidean Lipschitz bound `2 * √T` [GohMuller2026]. -/
theorem fCoord_lipschitz_l2 (s : ℕ → ℝ) (T t : ℕ) (ht : t≤T)
    (hs : ∀ r≤T, s r ∈ Set.Icc (0:ℝ) 1) (u v : Fin (t+1) → ℝ) :
    |fCoord s t u-fCoord s t v|≤2*Real.sqrt (T:ℝ)*Real.sqrt (∑ a, (u a-v a)^2) := by
  have hc : (∑ j : Fin t, s (j+1)^2)≤(T:ℝ) := by
    calc
      _ ≤ ∑ _j : Fin t, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hsj := hs (j+1) (by omega)
        nlinarith [hsj.1, hsj.2]
      _ = (t:ℝ) := by simp
      _ ≤ (T:ℝ) := by exact_mod_cast ht
  have hu : (∑ j : Fin t, (u j.succ-v j.succ)^2)≤∑ a : Fin (t+1), (u a-v a)^2 := by
    rw [Fin.sum_univ_succ]
    nlinarith [sq_nonneg (u 0-v 0)]
  exact (phi_difference_l2 s t (fun j => u j.succ) (fun j => v j.succ)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (by norm_num))
      (Real.sqrt_le_sqrt hu) (by positivity) (by positivity))

/-- For `s ∈ [0, 1]`, the catalyst coefficient `s ^ 2 * (1 − s)` lies in `[0, 4 / 27]`
[GohMuller2026]. -/
theorem catalyst_coefficient_bounds (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ s^2*(1-s) ∧ s^2*(1-s)≤4/27 := by
  refine ⟨mul_nonneg (sq_nonneg s) (by linarith [hs.2]), ?_⟩
  have he : (4/27:ℝ)-s^2*(1-s)=(3*s-2)^2*(3*s+1)/27 := by ring
  have hs0 : 0 ≤ s := hs.1
  have hn : 0 ≤ (3*s-2)^2*(3*s+1)/27 := by positivity
  linarith

/-- For `s ∈ [0, 1]`, the affine coordinate map `FCoord` has Euclidean Lipschitz bound `1 + 4 /
27` in the field and history variables. -/
theorem FCoord_lipschitz_l2 (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) {t : ℕ}
    (h h' : ℝ) (u v : Fin (t+1) → ℝ) :
    |FCoord s h u-FCoord s h' v|≤(1+4/27)*
      Real.sqrt ((h-h')^2+∑ a, (u a-v a)^2) := by
  have hc := catalyst_coefficient_bounds s hs
  have hu : (u 0-v 0)^2≤∑ a : Fin (t+1), (u a-v a)^2 :=
    Finset.single_le_sum (fun a _ => sq_nonneg (u a-v a)) (Finset.mem_univ 0)
  have hsum : 0≤∑ a : Fin (t+1), (u a-v a)^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hh : |h-h'|≤Real.sqrt ((h-h')^2+∑ a, (u a-v a)^2) :=
    Real.le_sqrt_of_sq_le (by rw [sq_abs]; linarith)
  have hv : |u 0-v 0|≤Real.sqrt ((h-h')^2+∑ a, (u a-v a)^2) :=
    Real.le_sqrt_of_sq_le (by rw [sq_abs]; nlinarith [sq_nonneg (h-h')])
  have he : FCoord s h u-FCoord s h' v=(h-h')+(s^2*(1-s))*(u 0-v 0) := by unfold FCoord; ring
  rw [he]
  calc
    _ ≤ |h-h'|+|s^2*(1-s)| * |u 0-v 0| := (abs_add_le (h-h') ((s^2*(1-s))*(u 0-v 0))).trans_eq
      (congrArg (fun a => |h-h'|+a) (abs_mul (s^2*(1-s)) (u 0-v 0)))
    _ ≤ Real.sqrt ((h-h')^2+∑ a, (u a-v a)^2)+(4/27)*Real.sqrt ((h-h')^2+∑ a, (u a-v a)^2) :=
      add_le_add hh (mul_le_mul (by simpa only [abs_of_nonneg hc.1] using hc.2) hv (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- The spin-readout coordinate map viewed as an update with an unused field argument. -/
def spinReadoutF (s : ℕ → ℝ) (t : ℕ) (_h : ℝ) (u : Fin (t+1) → ℝ) : ℝ := fCoord s t u

/-- The spin readout of the AMP history at horizon `T`. -/
def spinOutput {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (T : ℕ) : Fin N → ℝ :=
  spinReadout s T (ampHistory M J seed s T)

/-- For `M ≥ 1`, applying the additional spin-readout update and clipping at `M` and then at one
gives the corresponding coordinate of `spinOutput` [GohMuller2026]. -/
theorem actual_extra_spin_step {r N : ℕ} (M : ℝ) (hM : 1≤M)
    (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ) (s : ℕ → ℝ) (T : ℕ) (i : Fin N) :
    clip 1 (clip M (spinReadoutF s T (interaction J (fun _ => 0) i)
      (fun a => ampHistory M J seed s T a i)))=spinOutput M J seed s T i := by
  have hp : |spinOutput M J seed s T i|≤1 := phi_abs_le_one s T _
  have hi : spinOutput M J seed s T i ∈ Set.Icc (-1:ℝ) 1 := abs_le.mp hp
  have hiM : spinOutput M J seed s T i ∈ Set.Icc (-M) M := ⟨by linarith [hi.1], by linarith [hi.2]⟩
  change clip 1 (clip M (spinOutput M J seed s T i))=_
  rw [clip_eq M _ hiM, clip_eq 1 _ hi]

/-- For fixed clipping parameter, schedule, and horizon, `spinOutput` is jointly continuous in
the interaction tensor and seed. -/
theorem continuous_spinOutput {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) :
    Continuous (fun p : (Fin N → (Fin r → Fin N) → ℝ) × (Fin N → ℝ) => spinOutput M p.1 p.2 s T) :=
  (continuous_spinReadout s T).comp (continuous_ampHistory M s T)

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
