/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTail

/-!
# Gaussian source tensors and binary ground energies

Identifies the source-tensor image of independent standard Gaussian coordinates and records
attainment of the minimum binary energy. Squared transport estimates control changes in this
minimum, including a normalized bound with coefficient `1 / N`, in the Gaussian model of
[GohMuller2026].

## Main statements

* `binaryGround_attained`: attains the minimum on a binary spin configuration.
* `normalized_binary_ground_transport_sq`: bounds normalized ground-energy changes by the
  squared input distance divided by `N`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTail

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround

/-- The pushforward of independent standard Gaussian tensor coordinates under `sourceTensor` is
`gaussianTensorLaw r N`. -/
theorem sourceTensor_map_standard (r N : ℕ) :
    (Measure.pi (fun _ : Fin (r+1) → Fin N => gaussianReal 0 1)).map sourceTensor=
      gaussianTensorLaw r N := by
  change (Measure.pi (fun _ : Fin (r+1) → Fin N => gaussianReal 0 1)).map
    (fun G k => Real.sqrt (((N:ℝ)^r)⁻¹)*G k)=_
  rw [Measure.pi_map_pi (fun _ => (measurable_const_mul _).aemeasurable)]
  unfold gaussianTensorLaw
  congr 1
  funext k
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast]
  exact Real.sq_sqrt (by positivity)

/-- The binary ground energy is attained by some binary spin configuration. -/
theorem binaryGround_attained {q N : ℕ} (A : Tensor q N) :
    ∃ z : Fin N → Bool, tensorEnergy A (binarySpin z)=binaryGround A := by
  obtain ⟨z,_hz,he⟩ := Finset.exists_mem_eq_inf' (s:=Finset.univ) Finset.univ_nonempty
    (fun z : Fin N → Bool => tensorEnergy A (binarySpin z))
  exact ⟨z,he.symm⟩

/-- The binary ground energy is at most the energy of every binary spin configuration. -/
theorem binaryGround_le_energy {q N : ℕ} (A : Tensor q N) (z : Fin N → Bool) :
    binaryGround A≤tensorEnergy A (binarySpin z) :=
  Finset.inf'_le _ (Finset.mem_univ z)

/-- The squared difference of binary ground energies is at most the sum of squared tensor-entry
differences times `N ^ q`. -/
theorem binary_ground_transport_sq {q N : ℕ} (A B : Tensor q N) :
    (binaryGround A-binaryGround B)^2≤(∑ k, (A k-B k)^2)*(N:ℝ)^q := by
  let C := (∑ k,(A k-B k)^2)*(N:ℝ)^q
  have hC : 0≤C := by positivity
  have hc : ∀ z : Fin N → Bool,binarySpin z∈hilbertCube N := by
    intro z i
    simp only [binarySpin, Set.mem_Icc]
    split <;> norm_num
  obtain ⟨u,heu⟩ := binaryGround_attained A
  obtain ⟨v,hev⟩ := binaryGround_attained B
  have hpos : binaryGround A-binaryGround B≤Real.sqrt C := by
    have h := Real.le_sqrt_of_sq_le (energy_transport_sq A B (binarySpin v) (hc v))
    have hlo := binaryGround_le_energy A v
    rw [hev] at h
    linarith
  have hneg : -(binaryGround A-binaryGround B)≤Real.sqrt C := by
    have he := energy_transport_sq A B (binarySpin u) (hc u)
    have h :=
        Real.le_sqrt_of_sq_le
        (show (-(tensorEnergy A (binarySpin u)-tensorEnergy B (binarySpin u)))^2≤C by simpa only [neg_sq] using he)
    have hlo := binaryGround_le_energy B u
    rw [heu] at h
    linarith
  have hs := Real.sq_sqrt hC
  nlinarith

/-- For positive `N`, the squared difference of source-tensor binary ground energies normalized
by `N` is at most the sum of squared source-input differences divided by `N`. -/
theorem normalized_binary_ground_transport_sq {r N : ℕ} (hN : 0<N)
    (G D : Tensor (r+1) N) :
    (binaryGround (sourceTensor G)/(N:ℝ)-binaryGround (sourceTensor D)/(N:ℝ))^2≤
      (∑ k,(G k-D k)^2)/(N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := binary_ground_transport_sq (sourceTensor G) (sourceTensor D)
  have he : (∑ k,(sourceTensor G k-sourceTensor D k)^2)=
      ((N:ℝ)^r)⁻¹*∑ k,(G k-D k)^2 := by
    simp only [sourceTensor, ← mul_sub, mul_pow, Real.sq_sqrt (by positivity : 0≤((N:ℝ)^r)⁻¹)]
    rw [Finset.mul_sum]
  rw [he] at h
  have hm : ((N:ℝ)^r)⁻¹*(∑ k,(G k-D k)^2)*(N:ℝ)^(r+1)=
      (N:ℝ)*(∑ k,(G k-D k)^2) := by
    rw [pow_succ]
    field_simp
  rw [hm] at h
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg (N:ℝ))
  calc
    _ = (binaryGround (sourceTensor G)-binaryGround (sourceTensor D))^2/(N:ℝ)^2 := by ring
    _ ≤ (N:ℝ)*(∑ k,(G k-D k)^2)/(N:ℝ)^2 := hdiv
    _ = _ := by field_simp

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround
