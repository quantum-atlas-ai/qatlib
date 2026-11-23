/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OverlapGapGoh26.MainResults.SignRounding
public import Qatlib.Papers.OverlapGapGoh26.MainResults.OgpTail

@[expose] public section

/-!
# Final sign projection of the Gaussian MF-AOA output

[GohMuller2026], §2.3 returns the signs of the final z spins. The multilinear tensor norm
controls the change in energy density in terms of the root mean square defect from unit
spin magnitude. A Gaussian comparison uses the existing norm tail and isolates the remaining
defect probability needed to transfer the continuous obstruction to the binary output.

[arXiv:2609.35131v1](https://arxiv.org/abs/2609.35131v1)
-/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.NormRegion
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.MainResults
open Qatlib.Papers.OverlapGapGoh26.MainResults.BinaryNoGo
open Qatlib.Foundations.MatrixGeometry.AxisRotations.History
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
open Qatlib.Papers.OverlapGapGoh26.MainResults

namespace Qatlib.Papers.OverlapGapGoh26.SignReadout

/-- The binary output obtained by applying the sign map to the final raw spins,
with zero ties assigned to `+1`. -/
def signOutput {r N : ℕ} (s : ℕ → ℝ) (T : ℕ) (x : Input r N) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => roundedSpin (rawSpin s T (tensorCoords x) (seedCoords x) i))

/-- Every coordinate returned by the sign readout is binary. -/
theorem signOutput_binary {r N : ℕ} (s : ℕ → ℝ) (T : ℕ) (x : Input r N) (i : Fin N) :
    signOutput s T x i = 1 ∨ signOutput s T x i = -1 := by
  change roundedSpin _ = 1 ∨ roundedSpin _ = -1
  unfold roundedSpin
  split <;> simp

/-- The energy density of the final binary output for the same source tensor. -/
def signedEnergy {r N : ℕ} (s : ℕ → ℝ) (T : ℕ) (x : Input r N) : ℝ :=
  tensorEnergy (sourceTensor (tensorCoords x).ofLp) (signOutput s T x).ofLp / (N : ℝ)

/-- The root mean square distance between the continuous spins and their binary signs. -/
def roundingDefect {r N : ℕ} (s : ℕ → ℝ) (T : ℕ) (x : Input r N) : ℝ :=
  ‖rawSpin s T (tensorCoords x) (seedCoords x) - signOutput s T x‖ / Real.sqrt (N : ℝ)

/-- The Euclidean rounding defect equals the root mean square deficit in spin magnitude. -/
theorem roundingDefect_eq {r N : ℕ} (s : ℕ → ℝ) (T : ℕ) (x : Input r N) :
    roundingDefect s T x =
      Real.sqrt (∑ i, (1 - |rawSpin s T (tensorCoords x) (seedCoords x) i|) ^ 2) /
        Real.sqrt (N : ℝ) := by
  unfold roundingDefect
  rw [EuclideanSpace.norm_eq]
  refine congrArg (fun a : ℝ => Real.sqrt a / Real.sqrt (N : ℝ)) ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [PiLp.sub_apply, Real.norm_eq_abs]
  exact congrArg (fun d : ℝ => d ^ 2) (abs_sub_roundedSpin (rawSpin_cube s T _ _ i))

/-- At depth one the source schedule uses only a rotation about the z axis, so the initial
spin in the xy plane has zero z component. The root mean square rounding defect is exactly one
for every input in positive dimension. -/
theorem roundingDefect_source_one {r N : ℕ} (hN : 0 < N) (x : Input r N) :
    roundingDefect (ActualMF.sourceSchedule 1) 1 x = 1 := by
  have hspin (i : Fin N) : rawSpin (ActualMF.sourceSchedule 1) 1 (tensorCoords x) (seedCoords x) i = 0 := by
    change feedbackState id _ _ (ActualMF.sourceSchedule 1) 1 i 2 = 0
    rw [actual_feedback_phi]
    simp [phi, historyProduct, ActualMF.sourceSchedule, rotationStep, driverAngle, problemAngle,
      Matrix.mul_apply, Fin.sum_univ_three]
  rw [roundingDefect_eq]
  simp only [hspin, abs_zero, sub_zero, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN)))

/-- On the scaled tensor-norm region, the sign projection changes energy density by at most
`K * (r + 1)` times the root mean square spin defect. The coefficient is independent of `N`. -/
theorem signedEnergy_sub_le {r N : ℕ} (hr : 0 < r) (hN : 0 < N)
    (s : ℕ → ℝ) (T : ℕ) (K : ℝ) (x : Input r N) (hx : normScale x ≤ K) :
    |energy s T x - signedEnergy s T x| ≤ K * (r + 1 : ℕ) * roundingDefect s T x := by
  have hbinary (i : Fin N) : |signOutput s T x i| ≤ 1 := by
    rcases signOutput_binary s T x i with hi | hi <;> rw [hi] <;> norm_num
  have h := source_energy_spin_difference hr hN (tensorCoords x)
    (rawSpin s T (tensorCoords x) (seedCoords x)) (signOutput s T x)
    (rawSpin_cube s T _ _) hbinary K hx
  unfold energy rawEnergyDensity signedEnergy roundingDefect
  exact h.trans_eq (by ring)

/-- The input event where the final binary output is within `a` of the binary maximum. -/
def nearSigned {r N : ℕ} (s : ℕ → ℝ) (T : ℕ) (a : ℝ) : Set (Input r N) :=
  {x | binaryMaximum x - signedEnergy s T x ≤ a}

/-- Successful binary output implies continuous success at the relaxed margin, unless the
scaled tensor norm or the root mean square rounding defect exceeds its threshold. -/
theorem nearSigned_subset {r N : ℕ} (hr : 0 < r) (hN : 0 < N)
    (s : ℕ → ℝ) (T : ℕ) (a δ : ℝ) :
    nearSigned (r := r) (N := N) s T a ⊆
      (nearBinary s T (a + normBound r * (r + 1 : ℕ) * δ) ∪
        {x | normBound r < normScale x}) ∪ {x | δ < roundingDefect s T x} := by
  intro x hx
  by_cases hnorm : normBound r < normScale x
  · exact Or.inl (Or.inr hnorm)
  by_cases hdefect : δ < roundingDefect s T x
  · exact Or.inr hdefect
  left
  left
  have h := signedEnergy_sub_le hr hN s T (normBound r) x (le_of_not_gt hnorm)
  have hcoef : 0 ≤ normBound r * (r + 1 : ℕ) :=
    mul_nonneg (normBound_pos r).le (Nat.cast_nonneg _)
  have hdiff := (neg_le_neg
    (h.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hdefect) hcoef))).trans
      (neg_abs_le (energy s T x - signedEnergy s T x))
  change binaryMaximum x - signedEnergy s T x ≤ a at hx
  change binaryMaximum x - energy s T x ≤ _
  linarith

/-- The probability of the actual sign-output success event is bounded by the probability of
continuous success at the relaxed margin, an explicit Gaussian norm tail, and the defect tail. -/
theorem nearSigned_probability_le {r N : ℕ} (hr : 0 < r) (hN : 0 < N)
    (s : ℕ → ℝ) (T : ℕ) (a δ : ℝ) :
    (stdGaussian (Input r N)).real (nearSigned s T a) ≤
      (stdGaussian (Input r N)).real (nearBinary s T (a + normBound r * (r + 1 : ℕ) * δ)) +
        2 * Real.exp (-(N : ℝ)) +
        (stdGaussian (Input r N)).real {x | δ < roundingDefect s T x} := by
  refine (measureReal_mono (nearSigned_subset hr hN s T a δ)).trans ?_
  refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
  exact (measureReal_union_le _ _).trans (add_le_add le_rfl (normBound_tail hr hN))

/-- At fixed positive depth and even interaction order at least four, the source sign output
has vanishing near-optimal success probability if model OGP failures have an exponential tail
and the probability of exceeding the displayed root mean square defect threshold tends to zero. -/
theorem signed_source_nogo_of_ogp_tail {r T : ℕ} (hr : Odd r) (hq : 3 ≤ r) (hT : 0 < T)
    {μ ν₁ ν₂ c : ℝ} (hμ : 0 < μ) (hlo : 0 < ν₁) (hgap : ν₁ < ν₂) (hhi : ν₂ < 1)
    (hc : 0 < c) (hogp : ∀ᶠ N : ℕ in atTop,
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real
        (RawNoGo.modelOgp r N μ ν₁ ν₂)ᶜ ≤ Real.exp (-c * (N : ℝ)))
    (hdefect : Tendsto (fun N : ℕ => (stdGaussian (Input r N)).real
      {x | μ / (32 * (normBound r * (r + 1 : ℕ))) < roundingDefect (ActualMF.sourceSchedule T) T x})
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (stdGaussian (Input r N)).real
      (nearSigned (ActualMF.sourceSchedule T) T (μ / 32))) atTop (𝓝 0) := by
  let δ := μ / (32 * (normBound r * (r + 1 : ℕ)))
  have hcoef : 0 < normBound r * (r + 1 : ℕ) := mul_pos (normBound_pos r) (by positivity)
  have hmargin : μ / 32 + normBound r * (r + 1 : ℕ) * δ = μ / 16 := by
    have hδ : δ * (32 * (normBound r * (r + 1 : ℕ))) = μ :=
      div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hcoef.ne')
    calc
      _ = (μ + δ * (32 * (normBound r * (r + 1 : ℕ)))) / 32 := by ring
      _ = μ / 16 := by rw [hδ]; ring
  have hcontinuous := source_mf_nogo_of_ogp_tail hr hT hμ hlo hgap hhi hc hogp
  have hnorm : Tendsto (fun N : ℕ => 2 * Real.exp (-(N : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
  have htotal := (hcontinuous.add hnorm).add hdefect
  simp only [zero_add] at htotal
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ htotal
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [hmargin] using
    nearSigned_probability_le (r := r) (N := N) (by omega) hN (ActualMF.sourceSchedule T) T (μ / 32) δ

end Qatlib.Papers.OverlapGapGoh26.SignReadout
