/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.PatchMemory.Im2col
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# The forward convolution and activation sampling law

[KerenidisLandmanPrakash2020], Section D.1, evaluates each convolution entry
as a normalized patch–filter inner product times the two norms. A separate
amplitude preparation encodes the square root of the activation. Its
measurement law is proportional to activation values. The proofs account
for the exact inner product and measurement probabilities for supplied
estimates. Estimation error and runtime require the quantum estimation
algorithm and its resource bounds.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QCNN20.Forward

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Qatlib.Papers.QCNN20.PatchMemory
open scoped BigOperators

variable {positions window output : ℕ}

/-- Compute the convolution entry by rescaling the inner product of prepared amplitudes. -/
noncomputable def convolutionEntry (patch filter : Tree ℝ window) : ℝ :=
  Real.sqrt (mass patch) * Real.sqrt (mass filter) *
    ∑ slot, pathAmplitude patch slot * pathAmplitude filter slot

/-- Rescaling the two normalized states gives the classical dot product, including zero patches. -/
theorem convolution_entry_eq (patch filter : Tree ℝ window) (hPatch : Valid patch)
    (hFilter : Valid filter) :
    convolutionEntry patch filter = ∑ slot, read patch slot * read filter slot := by
  by_cases hPatchZero : mass patch = 0
  · simp [convolutionEntry, hPatchZero, read_eq_zero_of_mass_eq_zero patch hPatch hPatchZero]
  by_cases hFilterZero : mass filter = 0
  · simp [convolutionEntry, hFilterZero, read_eq_zero_of_mass_eq_zero filter hFilter hFilterZero]
  have hp : Real.sqrt (mass patch) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (mass_nonneg patch hPatch) (Ne.symm hPatchZero)))
  have hf : Real.sqrt (mass filter) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (mass_nonneg filter hFilter) (Ne.symm hFilterZero)))
  rw [convolutionEntry, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  rw [path_amplitude_eq patch hPatch, path_amplitude_eq filter hFilter]
  field_simp

/-- The exact preactivation matrix of a convolution layer. -/
noncomputable def preactivation {Filter : Type*} (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (position : Address positions) (filter : Filter) : ℝ :=
  convolutionEntry (patchTree memory position) (filters filter)

/-- The preactivation on initialized patch memory equals the im2col expression for the input image. -/
theorem preactivation_eq_im2col {Pixel Filter : Type*}
    (layout : Layout Pixel positions window) (image : Pixel → ℝ)
    (filters : Filter → Tree ℝ window) (hFilters : ∀ filter, Valid (filters filter))
    (position : Address positions) (filter : Filter) :
    preactivation (initializePatches layout image) filters position filter =
      ∑ slot, image (layout.pixelAt (joinAddress positions position slot)) * read (filters filter) slot := by
  unfold preactivation patchTree
  rw [convolution_entry_eq _ _
    (valid_subtree positions (initializePatches layout image) position (valid_ofFn _ _)) (hFilters filter)]
  simp only [read_subtree, initializePatches, read_ofFn, Function.comp_apply]

/-- A nonnegative capped ReLU used for bounded activation values. -/
noncomputable def cappedRelu (cap value : ℝ) : ℝ := max 0 (min cap value)

/-- Capped ReLU is nonnegative at every input. -/
theorem capped_relu_nonneg (cap input : ℝ) : 0 ≤ cappedRelu cap input :=
  le_max_left _ _

/-- Capping and rectifying never amplify an additive forward estimation error. -/
theorem capped_relu_error_le (cap estimate actual : ℝ) :
    |cappedRelu cap estimate - cappedRelu cap actual| ≤ |estimate - actual| := by
  have hLip : LipschitzWith 1 (cappedRelu cap) :=
    (LipschitzWith.id.const_min cap).const_max 0
  simpa [Real.dist_eq] using hLip.dist_le_mul estimate actual

/-- Build a measurement state whose squared unnormalized amplitudes are the activations. -/
noncomputable def activationTree (activate : ℝ → ℝ) (estimate : Address output → ℝ) :
    Tree ℝ output :=
  ofFn output (fun address => Real.sqrt (activate (estimate address)))

/-- The squared activation amplitude is proportional to activation, including at zeros. -/
theorem activation_probability (activate : ℝ → ℝ) (estimate : Address output → ℝ)
    (h : ∀ address, 0 ≤ activate (estimate address)) (address : Address output) :
    pathAmplitude (activationTree activate estimate) address ^ 2 =
      activate (estimate address) / ∑ slot, activate (estimate slot) := by
  have hValid : Valid (activationTree activate estimate) := valid_ofFn _ _
  have hMass : mass (activationTree activate estimate) = ∑ slot, activate (estimate slot) := by
    rw [mass_eq_sum _ hValid]
    simp only [activationTree, read_ofFn, Real.sq_sqrt (h _)]
  rw [path_amplitude_eq _ hValid, div_pow,
    Real.sq_sqrt (mass_nonneg _ hValid), hMass, activationTree, read_ofFn, Real.sq_sqrt (h address)]

/-- Positive total activation supplies a normalized state for sampling an output pixel. -/
theorem activation_state_normalized (activate : ℝ → ℝ) (estimate : Address output → ℝ)
    (hNonneg : ∀ address, 0 ≤ activate (estimate address))
    (hPos : 0 < ∑ address, activate (estimate address)) :
    ∑ address, pathAmplitude (activationTree activate estimate) address ^ 2 = 1 := by
  simp_rw [activation_probability activate estimate hNonneg]
  rw [← Finset.sum_div, div_self hPos.ne']

end Qatlib.Papers.QCNN20.Forward
