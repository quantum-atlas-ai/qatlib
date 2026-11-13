/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.OgpBridge.DensityMargin
import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.NormStability

/-!
# Ground energy bounds forced by overlap gaps

`actual_gap_directions` constructs unit vectors with any prescribed inner product in `(0,1)`
when the dimension is at least two. Small scaled copies of these directions show that an overlap
gap near the cube minimum forces `cubeOpt A + m ≤ 0`; the density version bounds every
interpolated cube minimum density by `-μ`. These geometric consequences clarify the overlap gap
hypotheses used with [GohMuller2026].

## Main statements

* `instance_ogp_ground_ceiling`: For `N ≥ 2` and `0 < ν₁ < ν₂ < 1`, an overlap gap for cube
  vectors within margin `m` of the minimum forces `cubeOpt A + m ≤ 0`.
* `density_ogp_ground_bound`: For `N ≥ 2` and `0 < ν₁ < ν₂ < 1`, the density ensemble overlap
  gap condition forces every interpolated cube minimum density to be at most `-μ`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators RealInnerProductSpace Topology
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.SmallSpin

/-- For `N ≥ 2` and `0 < c < 1`, there exist two unit Euclidean vectors with real inner product
`c`. -/
theorem actual_gap_directions {N : ℕ} (hN : 2≤N) (c : ℝ) (hc0 : 0<c) (hc1 : c<1) :
    ∃ u v : EuclideanSpace ℝ (Fin N),‖u‖=1 ∧ ‖v‖=1 ∧ inner ℝ u v=c := by
  let i : Fin N := ⟨0,by omega⟩
  let j : Fin N := ⟨1,by omega⟩
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have hij : i≠j := by intro h; have he := congrArg Fin.val h; dsimp [i,j] at he; omega
  let u := b i
  let v := c•b i+Real.sqrt (1-c^2)•b j
  have hsq : 0≤1-c^2 := by nlinarith
  have hv : ‖v‖^2=1 := by
    dsimp only [v]
    simp only [norm_add_sq_real,norm_smul,b.norm_eq_one,mul_one,real_inner_smul_left,
      real_inner_smul_right,b.inner_eq_zero hij,mul_zero,add_zero,Real.norm_eq_abs,sq_abs,
      Real.sq_sqrt hsq]
    ring
  refine ⟨u,v,b.norm_eq_one i,?_,?_⟩
  · nlinarith [norm_nonneg v]
  · simp only [u,v,inner_add_right,real_inner_smul_right,b.inner_eq_one,b.inner_eq_zero hij,
      mul_one,mul_zero,add_zero]

/-- A tensor of positive order has zero energy at the zero spin vector. -/
theorem tensorEnergy_zero {r N : ℕ} (A : Tensor (r+1) N) : tensorEnergy A (fun _ => 0)=0 := by
  simp [tensorEnergy]

/-- For `N ≥ 2` and `0 < ν₁ < ν₂ < 1`, an overlap gap for cube vectors within margin `m` of the
minimum forces `cubeOpt A + m ≤ 0`. -/
theorem instance_ogp_ground_ceiling {r N : ℕ} (hN : 2≤N) (A : Tensor (r+1) N)
    (m ν₁ ν₂ : ℝ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1)
    (hogp : ∀ u v : EuclideanSpace ℝ (Fin N),u.ofLp∈hilbertCube N→v.ofLp∈hilbertCube N→
      tensorEnergy A u.ofLp≤cubeOpt A+m→tensorEnergy A v.ofLp≤cubeOpt A+m→
      normalizedOverlap u v≤ν₁ ∨ ν₂≤normalizedOverlap u v) :
    cubeOpt A+m≤0 := by
  by_contra! ht
  let c := (ν₁+ν₂)/2
  have hc0 : 0<c := by dsimp [c]; linarith
  have hc1 : c<1 := by dsimp [c]; linarith
  obtain ⟨u,v,hu,hv,huv⟩ := actual_gap_directions hN c hc0 hc1
  have hcont (z : EuclideanSpace ℝ (Fin N)) : Continuous (fun a : ℝ => tensorEnergy A ((a•z).ofLp)) := by
    unfold tensorEnergy
    fun_prop
  have hzero (z : EuclideanSpace ℝ (Fin N)) : tensorEnergy A (((0:ℝ)•z).ofLp)=0 := by
    simpa only [zero_smul,WithLp.ofLp_zero] using! tensorEnergy_zero A
  have hnear (z : EuclideanSpace ℝ (Fin N)) : ∀ᶠ a in 𝓝 (0:ℝ),tensorEnergy A ((a•z).ofLp)<cubeOpt A+m := by
    exact ((hcont z).tendsto (0:ℝ)).eventually
      (Iio_mem_nhds (by rw [hzero z]; exact ht))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hnear u).and (hnear v))
  let a := min ε 1/2
  have ha : 0<a := by dsimp [a]; positivity
  have haε : a<ε := by have h := min_le_left ε 1; dsimp [a]; linarith
  have ha1 : a≤1 := by have h := min_le_right ε 1; dsimp [a]; linarith
  have hmem : a∈Metric.ball (0:ℝ) ε := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ha] using! haε
  have hE := hball hmem
  have hcube (z : EuclideanSpace ℝ (Fin N)) (hz : ‖z‖=1) : (a•z).ofLp∈hilbertCube N := by
    intro i
    apply abs_le.mp
    change |a*z i|≤1
    have hzi : |z i|≤1 := by simpa only [Real.norm_eq_abs,hz] using! PiLp.norm_apply_le (p:=2) z i
    rw [abs_mul,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left hzi ha.le).trans (by simpa only [mul_one] using! ha1)
  have hvalue : normalizedOverlap (a•u) (a•v)=c := by
    unfold normalizedOverlap
    rw [real_inner_smul_left,real_inner_smul_right,huv,norm_smul,norm_smul,hu,hv,
      Real.norm_eq_abs,abs_of_pos ha,mul_one,abs_of_pos (by positivity : 0<a*(a*c))]
    field_simp
  have hbad := hogp (a•u) (a•v) (hcube u hu) (hcube v hv) hE.1.le hE.2.le
  rw [hvalue] at hbad
  rcases hbad with hbad|hbad <;> dsimp [c] at hbad <;> linarith

/-- For `N ≥ 2` and `0 < ν₁ < ν₂ < 1`, the density ensemble overlap gap condition forces every
interpolated cube minimum density to be at most `-μ`. See [GohMuller2026]. -/
theorem density_ogp_ground_bound {r N : ℕ} (hN : 2≤N)
    (A B : Tensor (r+1) N) (μ ν₁ ν₂ : ℝ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1)
    (hogp : Qatlib.Papers.OverlapGapGoh26.OgpBridge.Density.densityEnsembleOGP A B μ ν₁ ν₂)
    (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    cubeOpt (Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation.interpolate A B τ)/(N:ℝ)≤-μ := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hraw := (Qatlib.Papers.OverlapGapGoh26.OgpBridge.Density.density_ogp_iff_total
    (by omega : 0<N) A B μ ν₁ ν₂).mp hogp
  have hs := instance_ogp_ground_ceiling hN
    (Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation.interpolate A B τ)
    ((N:ℝ)*μ) ν₁ ν₂ hlo hgap hhi (hraw τ hτ τ hτ)
  apply (div_le_iff₀ hn).mpr
  nlinarith

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.SmallSpin
