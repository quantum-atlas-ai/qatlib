/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.FixedTail
import Qatlib.Papers.OverlapGapGoh26.UniformGrid.CubeGround

/-!
# Finite grid reduction for repeated index energies

`cube_product_difference` and `repeated_box_difference` control changes of the repeated index
energy under coordinate approximation. `remainder_grid_inclusion` reduces a large energy
somewhere on the cube to a large tensor entry or a large energy on a finite grid, and
`remainder_grid_tail` bounds these events. These estimates support the Gaussian remainder
analysis associated with [GohMuller2026].

## Main statements

* `remainder_grid_inclusion`: Under the mesh error bound, a repeated index energy of absolute
  value at least `ηN` somewhere on the cube forces either a tensor entry of absolute value at
  least `N` or a grid energy of absolute value at least `ηN/2`.
* `remainder_grid_tail`: For positive `N`, `m`, and `η` satisfying the mesh bound, the
  probability of a repeated index energy of size at least `ηN` somewhere on the cube is bounded
  by the displayed sum of entry and finite grid Gaussian tails.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.CubeGround
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

/-- For two cube vectors differing by at most `ε ≥ 0` in each coordinate, every degree `q`
monomial differs by at most `qε`. -/
theorem cube_product_difference {q N:ℕ} (u v:Fin N→ℝ) (hu:u∈hilbertCube N) (hv:v∈hilbertCube N)
    (ε:ℝ) (hε:0≤ε) (he:∀ i,|u i-v i|≤ε) (k:Fin q→Fin N) :
    |(∏ a,u (k a))-(∏ a,v (k a))|≤(q:ℝ)*ε := by
  let U:=fun a:Fin q=>u (k a)
  let V:=fun a:Fin q=>v (k a)
  have hU : ‖U‖≤1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      (fun a=>by simpa only [Real.norm_eq_abs] using! abs_le.mpr (hu (k a)))
  have hV : ‖V‖≤1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      (fun a=>by simpa only [Real.norm_eq_abs] using! abs_le.mpr (hv (k a)))
  have hd : ‖U-V‖≤ε :=
      (pi_norm_le_iff_of_nonneg hε).mpr
      (fun a=>by simpa only [Pi.sub_apply,Real.norm_eq_abs] using! he (k a))
  have hh:=(ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin q) ℝ).norm_image_sub_le U V
  simp only [ContinuousMultilinearMap.norm_mkPiAlgebra,Fintype.card_fin,one_mul] at hh
  have hp : (max ‖U‖ ‖V‖)^(q-1)≤1 := by
    simpa only [one_pow] using!
        pow_le_pow_left₀ (by positivity : (0:ℝ)≤ max ‖U‖ ‖V‖) (max_le hU hV) (q-1)
  have hb : (q:ℝ)*(max ‖U‖ ‖V‖)^(q-1)≤q := by
    have hq : (0:ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  exact hh.trans (mul_le_mul hb hd (norm_nonneg _) (Nat.cast_nonneg q))

/-- If all tensor coefficients have absolute value at most `B ≥ 0`, then cube vectors within
coordinate distance `ε ≥ 0` have repeated index energies differing by at most `N^q * B * q *
ε`. -/
theorem repeated_box_difference {q N:ℕ} (A:Tensor q N) (B:ℝ) (hB:0≤B) (hA:∀k,|A k|≤B)
    (u v:Fin N→ℝ) (hu:u∈hilbertCube N) (hv:v∈hilbertCube N)
    (ε:ℝ) (hε:0≤ε) (he:∀i,|u i-v i|≤ε) :
    |tensorEnergy (repeated A) u-tensorEnergy (repeated A) v|≤(N:ℝ)^q*B*q*ε := by
  have hR(k:Fin q→Fin N):|repeated A k|≤B := by
    by_cases hk:Function.Injective k <;>simp [repeated,hk,hB,hA k]
  have heq : tensorEnergy (repeated A) u-tensorEnergy (repeated A) v=
      ∑ k,repeated A k*((∏ a,u (k a))-(∏ a,v (k a))) := by
    unfold tensorEnergy
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  calc
    _ ≤ ∑ k:Fin q→Fin N,|repeated A k*((∏ a,u (k a))-(∏ a,v (k a)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k:Fin q→Fin N,B*((q:ℝ)*ε) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hR k) (cube_product_difference u v hu hv ε hε he k) (abs_nonneg _) hB
    _ = _ := by simp;ring

/-- For `N > 0`, every tensor coordinate under `gaussianTensorLaw` satisfies a subgaussian bound
with parameter one. -/
theorem source_entry_subgaussian {r N:ℕ} (hN:0 < N) (k:Fin (r+1)→Fin N) :
    HasSubgaussianMGF (fun A:Tensor (r+1) N=>A k) 1 (gaussianTensorLaw r N) := by
  let v:NNReal:=((N:NNReal)^r)⁻¹
  have hmp := (measurePreserving_eval (fun _ : Fin (r+1)→Fin N=>gaussianReal 0 v) k).map_eq
  have h := gaussian_id_subgaussian v
  rw [← hmp] at h
  have hv:v≤1 := by
    have hn:(1:ℝ)≤N := by exact_mod_cast hN
    apply NNReal.coe_le_coe.mp
    simp only [v,NNReal.coe_inv,NNReal.coe_pow,NNReal.coe_natCast,NNReal.coe_one]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hn)
  have hh : HasSubgaussianMGF (fun A:Tensor (r+1) N=>A k) v (gaussianTensorLaw r N) := by
    simpa only [Function.comp_def,id_eq,gaussianTensorLaw,v] using!
      (HasSubgaussianMGF.of_map (X:=id) (Y:=Function.eval k)
        (μ:=Measure.pi (fun _ : Fin (r+1)→Fin N=>gaussianReal 0 v)) (c:=v)
        (measurable_pi_apply k).aemeasurable h)
  exact subgaussian_enlarge hh hv

/-- For `N > 0`, the probability that some tensor coefficient has absolute value at least `N` is
at most `2N^(r+1) exp(-N²/2)`. -/
theorem entry_box_tail {r N:ℕ} (hN:0 < N) :
    (gaussianTensorLaw r N).real {A|∃k,(N:ℝ)≤|A k|}≤
      2*(N:ℝ)^(r+1)*Real.exp (-(N:ℝ)^2/2) := by
  have he : {A:Tensor (r+1) N|∃k,(N:ℝ)≤|A k|}=
      ⋃ k:Fin (r+1)→Fin N,{A|(N:ℝ)≤|A k|} := by ext A;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ k:Fin (r+1)→Fin N,2*Real.exp (-(N:ℝ)^2/2) :=
      Finset.sum_le_sum (fun k _=>by simpa only [NNReal.coe_one,mul_one] using! subgaussian_abs_tail (source_entry_subgaussian hN k) (N:ℝ) (Nat.cast_nonneg N))
    _ = _ := by simp;ring

/-- For positive mesh parameter `m`, every Hilbert cube vector is within `2/m` in each
coordinate of a grid vector `cubeState m v`. -/
theorem cube_uniform_cover {N m:ℕ} (hm:0 < m) (u:Fin N→ℝ) (hu:u∈hilbertCube N) :
    ∃v:Fin N→Fin (m+1),∀i,|u i-cubeState m v i|≤2/(m:ℝ) := by
  choose v hv using fun i=>coordinate_cover hm (u i) (hu i)
  exact ⟨v,hv⟩

/-- Under the mesh error bound, a repeated index energy of absolute value at least `ηN`
somewhere on the cube forces either a tensor entry of absolute value at least `N` or a grid
energy of absolute value at least `ηN/2`. -/
theorem remainder_grid_inclusion {r N m:ℕ} (hm:0 < m) (η:ℝ)
    (hmesh : (N:ℝ)^(r+1)*(N:ℝ)*(r+1)*(2/(m:ℝ))≤η*(N:ℝ)/2) :
    {A:Tensor (r+1) N|∃u∈hilbertCube N,η*(N:ℝ)≤|tensorEnergy (repeated A) u|}⊆
      {A|∃k,(N:ℝ)≤|A k|}∪
      {A|∃v:Fin N→Fin (m+1),η*(N:ℝ)/2≤|tensorEnergy (repeated A) (cubeState m v)|} := by
  intro A hA
  simp only [Set.mem_union,Set.mem_setOf_eq] at hA ⊢
  by_contra! hbad
  have hbox:∀k,|A k|≤N := fun k=>(hbad.1 k).le
  obtain ⟨u,hu,hRu⟩:=hA
  obtain ⟨v,hv⟩:=cube_uniform_cover hm u hu
  have hd:=repeated_box_difference A (N:ℝ) (Nat.cast_nonneg N) hbox u (cubeState m v) hu (cubeState_mem hm v)
    (2/(m:ℝ)) (by positivity) hv
  simp only [Nat.cast_add,Nat.cast_one] at hd
  have hg:=hbad.2 v
  have ha:=abs_sub_abs_le_abs_sub (tensorEnergy (repeated A) u)
      (tensorEnergy (repeated A) (cubeState m v))
  linarith

/-- For positive `N`, `m`, and `η` satisfying the mesh bound, the probability of a repeated
index energy of size at least `ηN` somewhere on the cube is bounded by the displayed sum of
entry and finite grid Gaussian tails. -/
theorem remainder_grid_tail {r N m:ℕ} (hN:0 < N) (hm:0 < m) (η:ℝ) (hη:0 < η)
    (hmesh : (N:ℝ)^(r+1)*(N:ℝ)*(r+1)*(2/(m:ℝ))≤η*(N:ℝ)/2) :
    (gaussianTensorLaw r N).real {A|∃u∈hilbertCube N,η*(N:ℝ)≤|tensorEnergy (repeated A) u|}≤
      2*(N:ℝ)^(r+1)*Real.exp (-(N:ℝ)^2/2)+
      2*((m+1:ℕ):ℝ)^N*Real.exp (-(η*(N:ℝ)/2)^2/(2*(r+1:ℝ)^2)) := by
  apply (measureReal_mono (remainder_grid_inclusion hm η hmesh)).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add (entry_box_tail hN)
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using!
    repeated_finite_tail hN (cubeState m) (cubeState_mem hm) (η*(N:ℝ)/2) (by positivity)
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
