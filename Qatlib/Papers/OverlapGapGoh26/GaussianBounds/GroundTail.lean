/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LinearTail
import Qatlib.Papers.OverlapGapGoh26.OgpBridge.GaussianObstruction
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTail

def binarySpin {N : ℕ} (z : Fin N → Bool) : Fin N → ℝ := fun i => if z i then 1 else -1

theorem binary_energy_subgaussian {r N : ℕ} (hN : 0<N) (z : Fin N → Bool) :
    HasSubgaussianMGF (fun A : Tensor (r+1) N => tensorEnergy A (binarySpin z))
      (N:NNReal) (gaussianTensorLaw r N) := by
  have h := independent_linear_subgaussian (((N:NNReal)^r)⁻¹)
    (fun k : Fin (r+1) → Fin N => ∏ a, binarySpin z (k a))
  have hw (k : Fin (r+1) → Fin N) : (∏ a, binarySpin z (k a))^2=1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro a _
    unfold binarySpin
    cases z (k a) <;> norm_num
  have hc : (∑ k : Fin (r+1) → Fin N,
      NNReal.mk ((∏ a, binarySpin z (k a))^2) (sq_nonneg _)*((N:NNReal)^r)⁻¹)=(N:NNReal) := by
    simp_rw [hw]
    simp only [show NNReal.mk 1 (by positivity)=1 from rfl, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, one_mul, Nat.cast_pow]
    have hn : (N:NNReal)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
    rw [pow_succ]
    field_simp
  rw [hc] at h
  simpa only [gaussianTensorLaw, tensorEnergy, mul_comm] using h

theorem binary_energy_left_tail {r N : ℕ} (hN : 0<N) (z : Fin N → Bool)
    (a : ℝ) (ha : 0≤a) :
    (gaussianTensorLaw r N).real {A | tensorEnergy A (binarySpin z)≤-a*(N:ℝ)}≤
      Real.exp (-a^2*(N:ℝ)/2) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := (binary_energy_subgaussian (r:=r) hN z).neg.measure_ge_le (show 0≤a*(N:ℝ) by positivity)
  have he : {A : Tensor (r+1) N | tensorEnergy A (binarySpin z)≤-a*(N:ℝ)}=
      {A | a*(N:ℝ)≤-(tensorEnergy A (binarySpin z))} := by ext A; dsimp; constructor <;> intro h <;> linarith
  rw [he]
  refine h.trans_eq ?_
  congr 1
  simp only [NNReal.coe_natCast]
  field_simp

theorem binary_ground_left_tail {r N : ℕ} (hN : 0<N) (a : ℝ) (ha : 0≤a) :
    (gaussianTensorLaw r N).real {A | binaryGround A≤-a*(N:ℝ)}≤
      (2:ℝ)^N*Real.exp (-a^2*(N:ℝ)/2) := by
  have he : {A : Tensor (r+1) N | binaryGround A≤-a*(N:ℝ)}=
      ⋃ z : Fin N → Bool, {A | tensorEnergy A (binarySpin z)≤-a*(N:ℝ)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, binaryGround, Finset.inf'_le_iff,
      Finset.mem_univ, true_and]
    rfl
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _z : Fin N → Bool, Real.exp (-a^2*(N:ℝ)/2) :=
      Finset.sum_le_sum (fun z _ => binary_energy_left_tail hN z a ha)
    _ = _ := by simp

theorem actual_binary_ground_exponential_tail {r N : ℕ} (hN : 0<N) :
    (gaussianTensorLaw r N).real {A | binaryGround A≤-2*(N:ℝ)}≤Real.exp (-(N:ℝ)) := by
  have h := binary_ground_left_tail (r:=r) hN 2 (by norm_num)
  refine h.trans ?_
  have hc : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp : (2:ℝ)^N≤Real.exp (N:ℝ) := by
    calc
      _ ≤ (Real.exp 1)^N := pow_le_pow_left₀ (by norm_num) hc N
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ Real.exp (N:ℝ)*Real.exp (-(2:ℝ)^2*(N:ℝ)/2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem binaryGround_integrable {r N : ℕ} (hN : 0<N) :
    Integrable (fun A : Tensor (r+1) N => binaryGround A) (gaussianTensorLaw r N) := by
  let f := fun z : Fin N → Bool => fun A : Tensor (r+1) N => tensorEnergy A (binarySpin z)
  have hi : Integrable (Finset.univ.inf' Finset.univ_nonempty f) (gaussianTensorLaw r N) := by
    exact Finset.inf'_induction Finset.univ_nonempty f
      (p:=fun g : Tensor (r+1) N → ℝ => Integrable g (gaussianTensorLaw r N))
      (fun _ hf _ hg => hf.inf hg) (fun z _ => (binary_energy_subgaussian (r:=r) hN z).integrable)
  have he : (fun A : Tensor (r+1) N => binaryGround A)=Finset.univ.inf' Finset.univ_nonempty f := by
    funext A
    rw [Finset.inf'_apply]
    rfl
  rw [he]
  exact hi

theorem gaussianGroundDensity_integrable {r N : ℕ} (hN : 0<N) :
    Integrable (fun A : Tensor (r+1) N => binaryGround A/(N:ℝ)) (gaussianTensorLaw r N) :=
  (binaryGround_integrable hN).div_const _

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTail
