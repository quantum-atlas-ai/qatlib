/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EntangleTrans99.MainResults.Majorization.Basic
import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC

/-!
# Entropy and the two-dimensional spectral criterion

This module proves that majorization of two-entry probability vectors is equivalent to the
reverse ordering of their Shannon entropies. It rewrites entropy as `Real.binEntropy` of the
larger entry and uses its monotonicity on the interval from one half to one.

The theorem `qubit_entropy_criterion` specializes this equivalence to Schmidt spectra of
normalized bipartite pure states with a two-dimensional first subsystem, giving the spectral
entropy criterion discussed in [Nielsen1999].

## Main statements

* `majorizes_two_iff_entropy`: equates two-dimensional majorization with an entropy inequality.
* `qubit_entropy_criterion`: expresses the Schmidt-spectrum comparison as nonincrease of Schmidt
  entropy.

## References

* [Nielsen, 1999][Nielsen1999]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.Majorization

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

/-- For two real entries summing to one, their sum of `Real.negMulLog` values equals the binary
entropy of their maximum [Nielsen1999]. -/
theorem entropy_eq_binEntropy_max (a : Fin 2 → ℝ) (ha : a 0 + a 1 = 1) :
    (∑ j, Real.negMulLog (a j)) = Real.binEntropy (max (a 0) (a 1)) := by
  rw [Fin.sum_univ_two]
  rcases le_total (a 0) (a 1) with hle | hle
  · rw [max_eq_right hle]
    have h0 : a 0 = 1 - a 1 := by linarith
    rw [h0, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    ring
  · rw [max_eq_left hle]
    have h1 : a 1 = 1 - a 0 := by linarith
    rw [h1, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- The larger entry of a nonnegative two-entry vector with sum one lies in `[1/2, 1]`. -/
theorem max_mem_Icc_of_sum_one {a : Fin 2 → ℝ}
    (h0 : 0 ≤ a 0) (h1 : 0 ≤ a 1) (ha : a 0 + a 1 = 1) :
    max (a 0) (a 1) ∈ Set.Icc (2⁻¹) 1 := by
  constructor
  · rcases le_total (a 0) (a 1) with hle | hle
    · rw [max_eq_right hle]; linarith
    · rw [max_eq_left hle]; linarith
  · exact max_le (by linarith) (by linarith)

/-- If one two-entry probability vector majorizes another, its Shannon entropy is no larger
[Nielsen1999]. -/
theorem entropy_le_entropy_of_majorizes {a b : Fin 2 → ℝ}
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) (ha : a 0 + a 1 = 1)
    (hb0 : 0 ≤ b 0) (hb1 : 0 ≤ b 1) (hb : b 0 + b 1 = 1)
    (hmaj : Majorizes a b) :
    (∑ j, Real.negMulLog (a j)) ≤ ∑ j, Real.negMulLog (b j) := by
  rw [entropy_eq_binEntropy_max a ha, entropy_eq_binEntropy_max b hb]
  have hmax : max (b 0) (b 1) ≤ max (a 0) (a 1) :=
    (majorizes_two_iff_max_of_sum_one ha hb).1 hmaj
  have hanti : AntitoneOn Real.binEntropy (Set.Icc (2⁻¹) 1) :=
    Real.binEntropy_strictAntiOn.antitoneOn
  exact hanti (max_mem_Icc_of_sum_one hb0 hb1 hb) (max_mem_Icc_of_sum_one ha0 ha1 ha) hmax

/-- For two-entry probability vectors, `Majorizes a b` is equivalent to the Shannon entropy of
`a` being at most that of `b` [Nielsen1999]. -/
theorem majorizes_two_iff_entropy {a b : Fin 2 → ℝ}
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) (ha : a 0 + a 1 = 1)
    (hb0 : 0 ≤ b 0) (hb1 : 0 ≤ b 1) (hb : b 0 + b 1 = 1) :
    Majorizes a b ↔ (∑ j, Real.negMulLog (a j)) ≤ ∑ j, Real.negMulLog (b j) := by
  rw [majorizes_two_iff_max_of_sum_one ha hb]
  rw [entropy_eq_binEntropy_max a ha, entropy_eq_binEntropy_max b hb]
  have hb_mem := max_mem_Icc_of_sum_one hb0 hb1 hb
  have ha_mem := max_mem_Icc_of_sum_one ha0 ha1 ha
  constructor
  · intro hmax
    have hanti : AntitoneOn Real.binEntropy (Set.Icc (2⁻¹) 1) :=
      Real.binEntropy_strictAntiOn.antitoneOn
    exact hanti hb_mem ha_mem hmax
  · intro hent
    by_contra hnot
    have hlt : max (a 0) (a 1) < max (b 0) (b 1) := lt_of_not_ge hnot
    have hstrict := Real.binEntropy_strictAntiOn ha_mem hb_mem hlt
    linarith

/-- For normalized bipartite pure states with a two-dimensional first subsystem, majorization of
the source Schmidt spectrum by the target spectrum is equivalent to nonincrease of Schmidt
entropy [Nielsen1999]. -/
theorem qubit_entropy_criterion {E : ℕ} (ψ φ : QState (Fin 2 × Fin E))
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    Majorizes (schmidtSpectrum φ hφ) (schmidtSpectrum ψ hψ) ↔
      schmidtEntropy ψ hψ ≥ schmidtEntropy φ hφ := by
  have hsumψ : schmidtSpectrum ψ hψ 0 + schmidtSpectrum ψ hψ 1 = 1 := by
    rw [← Fin.sum_univ_two]
    exact schmidtSpectrum_sum_eq_one ψ hψ
  have hsumφ : schmidtSpectrum φ hφ 0 + schmidtSpectrum φ hφ 1 = 1 := by
    rw [← Fin.sum_univ_two]
    exact schmidtSpectrum_sum_eq_one φ hφ
  have h := majorizes_two_iff_entropy
    (a := schmidtSpectrum φ hφ) (b := schmidtSpectrum ψ hψ)
    (schmidtSpectrum_nonneg φ hφ 0) (schmidtSpectrum_nonneg φ hφ 1) hsumφ
    (schmidtSpectrum_nonneg ψ hψ 0) (schmidtSpectrum_nonneg ψ hψ 1) hsumψ
  simpa [schmidtEntropy, ge_iff_le] using h

end Qatlib.Papers.EntangleTrans99.MainResults.Majorization
