/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseTesting
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.RateExtraction

set_option backward.isDefEq.respectTransparency false

/-!
# Original Lower

The actual original weak-input family forces the full physical copy lower rate at every original confidence, including zero and one candidate copies, after arbitrary common quantum processing and arbitrary real-output event measurement.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseTesting
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.RateExtraction

/-- The actual original weak-input family forces the full physical copy lower rate at every original confidence, including zero and one candidate copies, after arbitrary common quantum processing and arbitrary real-output event measurement. -/
theorem actual_family_all_confidence_lower (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (hd : d+1=2 ∨ d+1=3) (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ)
    (hacc : FamilyAccurate d N h4 Q K T P δ) :
    (N : ℝ)^2*Real.log (1/δ)+(N : ℝ)*Real.sqrt ((N^(d+1) : ℕ)*Real.log (1/δ))≤131072*(Q : ℝ) := by
  have hM : (0 : ℝ)<(N^(d+1) : ℕ) := by
    exact_mod_cast (pow_pos (show 0<N by omega) (d+1))
  by_cases hL : Real.log (1/δ)≤(N^(d+1) : ℕ)/(N : ℝ)^2
  · have hf := (original_physical_full_fidelity d N hN h4 Q).trans
      (actual_prior_fidelity_upper d N hN h4 hd δ hδ hmax hL Q K T P hacc)
    exact collision_sum_rate N Q _ δ hN hM hδ hmax hf
  · have hf := actual_dense_testing d N hN h4 δ Q K T P hacc
    exact dense_sum_rate N Q _ δ hN hM hδ hmax (le_of_not_ge hL) (hf.trans (by linarith))

/-- The literal original full-domain estimation guarantee entails the original all-confidence physical copy lower bound, with every normalization, public promise, full loss, prior, actual real risk and testing reduction proved internally. -/
theorem original_all_confidence_lower (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (hd : d+1=2 ∨ d+1=3) (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ)
    (hacc : AllOriginalAccurate d N h4 Q K T P δ) :
    (N : ℝ)^2*Real.log (1/δ)+(N : ℝ)*Real.sqrt ((N^(d+1) : ℕ)*Real.log (1/δ))≤131072*(Q : ℝ) :=
  actual_family_all_confidence_lower d N hN h4 hd δ hδ hmax Q K T P
    (allOriginalAccurate_family d N hN h4 Q K T P δ hacc)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
