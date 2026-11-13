/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.CollisionCount

/-!
# Rounding tensor energies to binary configurations

The energy of `noRepeat A` is affine in each coordinate separately. Successively choosing
endpoints of cube coordinates never increases this energy, so `round_to_binary` produces a
binary configuration and `noRepeat_cube_eq_binary` identifies the cube and binary minima. This
rounding argument supports the optimization comparison used alongside [GohMuller2026].

## Main statements

* `round_to_binary`: Every cube vector has a binary configuration with no greater energy for
  `noRepeat A`.
* `noRepeat_cube_eq_binary`: The Hilbert cube minimum and binary ground energy coincide for the
  tensor `noRepeat A`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTail
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

/-- The energy of `noRepeat A` is the affine interpolation of its values with coordinate `i`
replaced by `-1` and `1`. -/
theorem noRepeat_affine {q N:ℕ} (A:Tensor q N) (u:Fin N→ℝ) (i:Fin N) :
    tensorEnergy (noRepeat A) u=
      ((1-u i)/2)*tensorEnergy (noRepeat A) (Function.update u i (-1))+
      ((1+u i)/2)*tensorEnergy (noRepeat A) (Function.update u i 1) := by
  unfold tensorEnergy
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk:Function.Injective k
  · simp only [noRepeat,if_pos hk]
    by_cases hi:∃ a,k a=i
    · obtain ⟨a,ha⟩ := hi
      have hprod (t:ℝ) : (∏ b,(Function.update u i t) (k b))=
          t*∏ b∈Finset.univ \ {a},u (k b) := by
        have he : (fun b=>(Function.update u i t) (k b))=Function.update (fun b=>u (k b)) a t := by
          funext b
          by_cases hb:b=a
          · subst b
            rw [ha]
            simp
          · have hki : k b≠i := fun h=>hb (hk (h.trans ha.symm))
            simp [Function.update_of_ne,hb,hki]
        rw [he,Finset.prod_update_of_mem (Finset.mem_univ a)]
      have hu := hprod (u i)
      simp only [Function.update_eq_self] at hu
      rw [hu,hprod (-1),hprod 1]
      ring
    · have he (t:ℝ) : (∏ b,(Function.update u i t) (k b))=∏ b,u (k b) := by
        apply Finset.prod_congr rfl
        intro b _
        exact Function.update_of_ne (fun h=>hi ⟨b,h⟩) t u
      rw [he,he]
      ring
  · simp [noRepeat,hk]

/-- For a cube vector, one can replace a chosen coordinate by a binary endpoint without
increasing the energy of `noRepeat A`. -/
theorem round_one {q N:ℕ} (A:Tensor q N) (u:Fin N→ℝ) (hu:u∈hilbertCube N) (i:Fin N) :
    ∃ b:Bool,tensorEnergy (noRepeat A) (Function.update u i (if b then 1 else -1))≤tensorEnergy (noRepeat A) u := by
  have he:=noRepeat_affine A u i
  have ha : 0≤(1-u i)/2 := by linarith [(hu i).2]
  have hb : 0≤(1+u i)/2 := by linarith [(hu i).1]
  have hm : min (tensorEnergy (noRepeat A) (Function.update u i (-1)))
      (tensorEnergy (noRepeat A) (Function.update u i 1))≤tensorEnergy (noRepeat A) u := by
    rw [he]
    calc
      _ = ((1-u i)/2)*min (tensorEnergy (noRepeat A) (Function.update u i (-1)))
          (tensorEnergy (noRepeat A) (Function.update u i 1))+
          ((1+u i)/2)*min (tensorEnergy (noRepeat A) (Function.update u i (-1)))
          (tensorEnergy (noRepeat A) (Function.update u i 1)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
  rcases min_le_iff.mp hm with hlo|hhi
  · exact ⟨false,hlo⟩
  · exact ⟨true,hhi⟩

/-- For any finite set of coordinates, a cube vector can be replaced by another cube vector
whose chosen coordinates are binary and whose `noRepeat A` energy is no greater. -/
theorem round_finite {q N:ℕ} (A:Tensor q N) (S:Finset (Fin N)) (u:Fin N→ℝ) (hu:u∈hilbertCube N) :
    ∃ v:Fin N→ℝ,v∈hilbertCube N ∧ tensorEnergy (noRepeat A) v≤tensorEnergy (noRepeat A) u ∧
      ∀ i∈S,v i=1∨v i= -1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨u,hu,le_rfl,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨v,hv,hE,hbin⟩ := ih
    obtain ⟨b,hb⟩ := round_one A v hv i
    let w:=Function.update v i (if b then (1:ℝ) else -1)
    refine ⟨w,?_,hb.trans hE,?_⟩
    · intro j
      by_cases hj:j=i
      · subst j;cases b <;>norm_num [w]
      · simpa only [w,Function.update_of_ne hj] using hv j
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · cases b <;>simp [w]
      · have hji:j≠i := fun h=>hi (h ▸ hj)
        simpa only [w,Function.update_of_ne hji] using hbin j hj

/-- Every cube vector has a binary configuration with no greater energy for `noRepeat A`. -/
theorem round_to_binary {q N:ℕ} (A:Tensor q N) (u:Fin N→ℝ) (hu:u∈hilbertCube N) :
    ∃ b:Fin N→Bool,tensorEnergy (noRepeat A) (binarySpin b)≤tensorEnergy (noRepeat A) u := by
  obtain ⟨v,hv,hE,hbin⟩ := round_finite A Finset.univ u hu
  let b:=fun i=>decide (v i=1)
  have he:binarySpin b=v := by
    funext i
    rcases hbin i (Finset.mem_univ i) with h|h
    · simp [binarySpin,b,h]
    · norm_num [binarySpin,b,h]
  exact ⟨b,he ▸ hE⟩

/-- The Hilbert cube minimum and binary ground energy coincide for the tensor `noRepeat A`. -/
theorem noRepeat_cube_eq_binary {q N:ℕ} (A:Tensor q N) : cubeOpt (noRepeat A)=binaryGround (noRepeat A) := by
  obtain ⟨u,hu,he⟩ := cubeOpt_attained (noRepeat A)
  obtain ⟨b,hb⟩ := round_to_binary A u hu
  have hlo := (binaryGround_le_energy (noRepeat A) b).trans hb
  rw [he] at hlo
  obtain ⟨v,hv⟩ := binaryGround_attained (noRepeat A)
  have hvc : binarySpin v∈hilbertCube N := by intro i;unfold binarySpin;cases v i <;>norm_num
  have hhi:=cubeOpt_le_energy (noRepeat A) (binarySpin v) hvc
  rw [hv] at hhi
  exact le_antisymm hhi hlo
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
