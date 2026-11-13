/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

/-!
# Stability of bounded AMP histories

Coordinatewise tensor perturbations propagate through the clipped AMP recursion with an explicit
factor `stabilityBase`. Product, interaction, readout, and clipping estimates give
finite-horizon history and output bounds for the dynamics associated with [GohMuller2026].

## Main statements

* `actual_history_difference`: tensor perturbations control all accumulated history entries.
* `actual_output_difference`: the same exponential-in-time factor controls the AMP output.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
open Qatlib.Foundations.MatrixGeometry.AxisRotations.History
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.Stability

/-- A finite product of real numbers of absolute value at most one also has absolute value at
most one. -/
theorem unit_product_bound {I : Type} [DecidableEq I] (S : Finset I) (u : I → ℝ)
    (hu : ∀ i∈S, |u i|≤1) : |∏ i∈S,u i|≤1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) hu

/-- For two finite families bounded in absolute value by one, the difference of their products
is at most the sum of the coordinatewise differences. -/
theorem unit_product_difference {I : Type} [DecidableEq I] (S : Finset I) (u v : I → ℝ)
    (hu : ∀ i∈S,|u i|≤1) (hv : ∀ i∈S,|v i|≤1) :
    |(∏ i∈S,u i)-(∏ i∈S,v i)|≤∑ i∈S,|u i-v i| := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    have heu : ∀ i∈S,|u i|≤1 := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hev : ∀ i∈S,|v i|≤1 := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have he : u a*(∏ i∈S,u i)-v a*(∏ i∈S,v i)=
        (u a-v a)*(∏ i∈S,u i)+v a*((∏ i∈S,u i)-(∏ i∈S,v i)) := by ring
    rw [he]
    calc
      _ ≤ |u a-v a| *|∏ i∈S,u i|+|v a| *|(∏ i∈S,u i)-(∏ i∈S,v i)| :=
        (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
      _ ≤ |u a-v a| *1+1*(∑ i∈S,|u i-v i|) := add_le_add
        (mul_le_mul_of_nonneg_left (unit_product_bound S u heu) (abs_nonneg _))
        (mul_le_mul (hv a (Finset.mem_insert_self _ _)) (ih heu hev) (abs_nonneg _) (by norm_num))
      _ = _ := by ring

/-- With tensor entries differing by at most `δ`, the second tensor bounded by two, and
unit-bounded spins differing by at most `η`, the interaction difference is at most `N^r * (δ
+ 2 * r * η)`. -/
theorem interaction_difference {r N : ℕ}
    (J K : Fin N → (Fin r → Fin N) → ℝ) (z w : Fin N → ℝ)
    (δ η : ℝ) (hδ : 0≤δ)
    (hJ : ∀ i k, |J i k-K i k|≤δ) (hK : ∀ i k, |K i k|≤2)
    (hz : ∀ i,|z i|≤1) (hw : ∀ i,|w i|≤1) (hzw : ∀ i,|z i-w i|≤η) (i : Fin N) :
    |interaction J z i-interaction K w i|≤(N:ℝ)^r*(δ+2*(r:ℝ)*η) := by
  have he : interaction J z i-interaction K w i=
      ∑ k : Fin r → Fin N, ((J i k-K i k)*(∏ a,z (k a))+K i k*((∏ a,z (k a))-(∏ a,w (k a)))) := by
    unfold interaction
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  calc
    _ ≤ ∑ k : Fin r → Fin N, |(J i k-K i k)*(∏ a,z (k a))+K i k*((∏ a,z (k a))-(∏ a,w (k a)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin r → Fin N, (δ+2*(r:ℝ)*η) := by
      apply Finset.sum_le_sum
      intro k _
      have hp : |(∏ a,z (k a))-(∏ a,w (k a))|≤(r:ℝ)*η := by
        refine (unit_product_difference Finset.univ _ _ (fun a _ => hz (k a)) (fun a _ => hw (k a))).trans ?_
        calc
          _ ≤ ∑ _a : Fin r,η := Finset.sum_le_sum (fun a _ => hzw (k a))
          _ = _ := by simp
      calc
        _ ≤ |J i k-K i k| *|∏ a,z (k a)|+|K i k| *|(∏ a,z (k a))-(∏ a,w (k a))| :=
          (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
        _ ≤ δ*1+2*((r:ℝ)*η) := add_le_add
          (mul_le_mul (hJ i k) (unit_product_bound Finset.univ _ (fun a _ => hz (k a))) (abs_nonneg _) hδ)
          (mul_le_mul (hK i k) hp (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    _ = _ := by simp; ring

/-- For schedules in `[0, 1]` through `T`, histories differing coordinatewise by at most `D`
have spin readouts differing by at most `2 * T * D` at times at most `T`. -/
theorem readout_difference {N T t : ℕ} (s : ℕ → ℝ) (ht : t≤T)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (U V : Fin (t+1) → Fin N → ℝ) (D : ℝ) (hD : 0≤D)
    (hUV : ∀ a i,|U a i-V a i|≤D) (i : Fin N) :
    |spinReadout s t U i-spinReadout s t V i|≤2*(T:ℝ)*D := by
  refine (phi_difference_sum s t (fun a => U a.succ i) (fun a => V a.succ i)).trans ?_
  calc
    _ ≤ ∑ _a : Fin t,2*D := by
      apply Finset.sum_le_sum
      intro a _
      have hsa := hs (a+1) (by omega)
      have hsa' : |s (a+1)|≤1 := abs_le.mpr ⟨by linarith [hsa.1],hsa.2⟩
      have hcoef : 2*|s (a+1)|≤2 := by nlinarith
      exact mul_le_mul hcoef (hUV a.succ i) (abs_nonneg _) (by norm_num)
    _ = 2*(t:ℝ)*D := by simp; ring
    _ ≤ 2*(T:ℝ)*D := by gcongr

/-- The clipping map does not increase absolute differences. -/
theorem clip_difference (M x y : ℝ) : |clip M x-clip M y|≤|x-y| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using (clip_lipschitz M).dist_le_mul x y

/-- Under the stated schedule, tensor, and history bounds, one AMP update differs by at most
`N^r * δ + (4 * r * T * N^r + 1) * D`. -/
theorem ampNext_difference {r N T t : ℕ} (M : ℝ) (s : ℕ → ℝ) (ht : t≤T)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (J K : Fin N → (Fin r → Fin N) → ℝ)
    (U V : Fin (t+1) → Fin N → ℝ) (δ D : ℝ) (hδ : 0≤δ) (hD : 0≤D)
    (hJ : ∀ i k,|J i k-K i k|≤δ) (hK : ∀ i k,|K i k|≤2)
    (hUV : ∀ a i,|U a i-V a i|≤D) (i : Fin N) :
    |ampNext M J s t U i-ampNext M K s t V i|≤
      (N:ℝ)^r*δ+(4*(r:ℝ)*(T:ℝ)*(N:ℝ)^r+1)*D := by
  have hz : ∀ i,|spinReadout s t U i|≤1 := fun _ => phi_abs_le_one s t _
  have hw : ∀ i,|spinReadout s t V i|≤1 := fun _ => phi_abs_le_one s t _
  have hf := interaction_difference J K (spinReadout s t U) (spinReadout s t V)
    δ (2*(T:ℝ)*D) hδ hJ hK hz hw (readout_difference s ht hs U V D hD hUV) i
  have hc := catalyst_coefficient_bounds (s t) (hs t ht)
  have hc' : |(s t)^2*(1-s t)|≤1 := by rw [abs_of_nonneg hc.1]; linarith [hc.2]
  refine (clip_difference M _ _).trans ?_
  have he : FCoord (s t) (interaction J (spinReadout s t U) i) (fun a => U a i)-
      FCoord (s t) (interaction K (spinReadout s t V) i) (fun a => V a i)=
      (interaction J (spinReadout s t U) i-interaction K (spinReadout s t V) i)+
        ((s t)^2*(1-s t))*(U 0 i-V 0 i) := by unfold FCoord; ring
  rw [he]
  calc
    _ ≤ |interaction J (spinReadout s t U) i-interaction K (spinReadout s t V) i|+
        |(s t)^2*(1-s t)| *|U 0 i-V 0 i| := (abs_add_le _ _).trans_eq (by rw [abs_mul])
    _ ≤ (N:ℝ)^r*(δ+2*(r:ℝ)*(2*(T:ℝ)*D))+1*D :=
      add_le_add hf (mul_le_mul hc' (hUV 0 i) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- The explicit history-stability factor `2 + (4 * r * T + 1) * N^r`. -/
def stabilityBase (r T N : ℕ) : ℝ := 2+(4*(r:ℝ)*(T:ℝ)+1)*(N:ℝ)^r

/-- The history-stability factor is at least one. -/
theorem stabilityBase_ge_one (r T N : ℕ) : 1≤ stabilityBase r T N := by
  unfold stabilityBase
  have h : 0≤(4*(r:ℝ)*(T:ℝ)+1)*(N:ℝ)^r := by positivity
  linarith

/-- For a common seed and a schedule in `[0, 1]`, tensor perturbations bounded by `δ` produce
history differences at most `δ * (stabilityBase r T N)^t` through time `T`, provided the
second tensor is bounded by two. -/
theorem actual_history_difference {r N T : ℕ} (M : ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (J K : Fin N → (Fin r → Fin N) → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hJ : ∀ i k,|J i k-K i k|≤δ) (hK : ∀ i k,|K i k|≤2) :
    ∀ t≤T, ∀ a i,|ampHistory M J seed s t a i-ampHistory M K seed s t a i|≤
      δ*(stabilityBase r T N)^t := by
  intro t
  induction t with
  | zero => intro _ a i; simp only [ampHistory,sub_self,abs_zero,pow_zero,mul_one]; exact hδ
  | succ t ih =>
    intro ht a i
    have hprev := ih (by omega)
    have hB := stabilityBase_ge_one r T N
    have hBt : 1≤(stabilityBase r T N)^t := one_le_pow₀ hB
    have hD : 0≤δ*(stabilityBase r T N)^t := by positivity
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simp only [ampHistory,Fin.snoc_last]
      refine (ampNext_difference M s (by omega : t≤T) hs J K _ _ δ _ hδ hD hJ hK hprev i).trans ?_
      have he : (N:ℝ)^r+(4*(r:ℝ)*(T:ℝ)*(N:ℝ)^r+1)≤ stabilityBase r T N := by
        unfold stabilityBase; nlinarith
      calc
        _ ≤ (N:ℝ)^r*(δ*(stabilityBase r T N)^t)+
          (4*(r:ℝ)*(T:ℝ)*(N:ℝ)^r+1)*(δ*(stabilityBase r T N)^t) := by
            gcongr
            nlinarith [mul_nonneg hδ (sub_nonneg.mpr hBt)]
        _ ≤ stabilityBase r T N*(δ*(stabilityBase r T N)^t) := by rw [← add_mul]; gcongr
        _ = _ := by rw [pow_succ]; ring
    · simp only [ampHistory,Fin.snoc_castSucc]
      refine (hprev j i).trans ?_
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.mpr hB) hD]

/-- Under the stated tensor and schedule bounds, the AMP outputs differ coordinatewise by at
most `δ * (stabilityBase r T N)^T`. -/
theorem actual_output_difference {r N T : ℕ} (M : ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (J K : Fin N → (Fin r → Fin N) → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hJ : ∀ i k,|J i k-K i k|≤δ) (hK : ∀ i k,|K i k|≤2) (i : Fin N) :
    |ampOutput M J seed s T i-ampOutput M K seed s T i|≤δ*(stabilityBase r T N)^T :=
  (clip_difference 1 _ _).trans (actual_history_difference M seed s hs J K δ hδ hJ hK T le_rfl (Fin.last T) i)

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.Stability
