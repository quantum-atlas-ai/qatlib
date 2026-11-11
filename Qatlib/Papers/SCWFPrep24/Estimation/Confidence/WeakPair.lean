/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

set_option backward.isDefEq.respectTransparency false

/-!
# Original conditional weak-pair information

This is the source's conditional spin-pair estimate at its actual public
excitation b=128/N² and correlations 3/4 and -3/4. The shared-phase coherent
Q-copy input and the complete high-confidence loss theorem are separate
obligations; no count law or final fidelity certificate is supplied here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

/-- The original public grid size makes its fixed weak excitation a legal physical spin parameter. -/
theorem original_weak_excitation (N : ℕ) (hN : 256 ≤ N) :
    0 ≤ 128/((N : ℝ)^2) ∧ 128/((N : ℝ)^2) ≤ 1/2 := by
  have hNr : (256 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0<(N : ℝ)^2 := by positivity
  constructor
  · positivity
  · apply (div_le_iff₀ hpos).2
    nlinarith [sq_nonneg ((N : ℝ)-256)]

/-- The source's two actual conditional quantum pair states satisfy the original copy-sensitive information bound. -/
theorem original_conditional_pair_information (N r s : ℕ) (hN : 256 ≤ N) :
    1-Froot (physicalPairMixture (128/((N : ℝ)^2)) r s (3/4))
      (physicalPairMixture (128/((N : ℝ)^2)) r s (-3/4)) ≤
        (54/7 : ℝ)*(128/((N : ℝ)^2))*(min r s : ℕ) := by
  have hb := original_weak_excitation N hN
  have h := physical_pair_original_information (128/((N : ℝ)^2)) r s (3/4) (3/4) (-3/4)
    hb.1 hb.2 (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num
  ring

/-- The original conditional states have a uniform actual root-fidelity floor, independently of both copy counts. -/
theorem original_conditional_pair_floor (N r s : ℕ) (hN : 256 ≤ N) :
    (1/4 : ℝ) ≤ Froot (physicalPairMixture (128/((N : ℝ)^2)) r s (3/4))
      (physicalPairMixture (128/((N : ℝ)^2)) r s (-3/4)) := by
  have hb := original_weak_excitation N hN
  have h := physical_pair_fidelity_floor (128/((N : ℝ)^2)) r s (3/4) (3/4) (-3/4)
    hb.1 (by linarith : 128/((N : ℝ)^2) ≤ 1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- A zero count on either matched label leaves the original conditional states exactly indistinguishable. -/
theorem original_conditional_pair_zero_count (N r s : ℕ) (hN : 256 ≤ N) (hz : r=0 ∨ s=0) :
    Froot (physicalPairMixture (128/((N : ℝ)^2)) r s (3/4))
      (physicalPairMixture (128/((N : ℝ)^2)) r s (-3/4))=1 := by
  have hb := original_weak_excitation N hN
  exact physical_pair_zero_count (128/((N : ℝ)^2)) r s (3/4) (3/4) (-3/4)
    hb.1 hb.2 (by norm_num) (by norm_num) (by norm_num) hz

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence
