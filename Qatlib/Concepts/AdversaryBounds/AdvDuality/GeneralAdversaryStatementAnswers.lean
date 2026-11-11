/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix

/-!
# General Adversary Witnesses and Label Measurements

This module collects witness comparisons, attainment statements, and measurement facts for the
general adversary method of [HoyerLeeSpalek2007] and its filtered norm formulation in
[LeeEtAl2011]. The results compare individual adversary matrices with `generalAdversaryValue`,
`advPmValue`, and `filteredGamma2`, including the case of a vanishing maximum filter norm.

The label measurement lemmas identify computational basis outcome probabilities with `povmProb`
and supply the corresponding final progress estimate. The numbered
`stageA_general_adversary_clause16` through `stageA_general_adversary_clause21` package these
statements for subsequent use.

## Main statements

* `adversary_ratio_le_sdp` bounds a witness norm ratio by the general adversary value.
* `stageA_general_adversary_clause18` includes attainment by a real symmetric feasible matrix
  when the value is finite.
* `stageA_general_adversary_clause20` compares the adversary value and feasible witnesses with
  the filtered gamma-two norm.
* `labelPovm_orthogonal`, `labelPovm_idem`, and `stageA_general_adversary_clause21` describe the
  projective label measurement.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger.
* [Lee et al., 2011][LeeEtAl2011], Quantum Query Complexity of State Conversion.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
noncomputable section

/-- The POVM induced by a basis labeling satisfies the final adversary progress bound for
function evaluation. -/
theorem povm_final_progress_label {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (Gamma : Matrix X X ℂ) (f : X → Y) (label : H → Y) (eps : ℝ) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.PovmFinalProgressBound Gamma f (labelPovm label) eps := by
  intro weight states hG hw hs hz he0 he1 _hout hsuccess
  have hsuccess' : ∀ x, 1 - eps ≤
      MeasureProb (states x) (Finset.univ.filter (fun h => label h = f x)) := by
    intro x
    have hx := hsuccess x
    rw [labelPovm_povmProb] at hx
    exact hx
  exact multioutput_adversary_actual_final_progress X H Y Gamma weight states f label eps hG hw hs
    hz he0 he1 hsuccess'
end
noncomputable section
set_option linter.unusedVariables false in

/-- Packages the final progress bound for label POVMs and its explicit estimate with coefficient
`2 * sqrt (eps * (1 - eps)) + 2 * eps` for error between zero and one half. -/
theorem stageA_general_adversary_clause16 :
    (∀ {X H Y : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      [Fintype Y] [DecidableEq Y] (Gamma : Matrix X X ℂ) (f : X → Y) (label : H → Y)
      (eps : ℝ),
      Qatlib.Concepts.AdversaryBounds.AdvDuality.PovmFinalProgressBound Gamma f (labelPovm label) eps) ∧
    (∀ {X H Y : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      [Fintype Y] [DecidableEq Y] (Gamma : Matrix X X ℂ) (weight : QState X)
      (states : X → QState H) (f : X → Y) (label : H → Y) (eps : ℝ)
      (hG : Gamma.IsHermitian) (hw : Normalized weight) (hs : ∀ x, Normalized (states x))
      (hz : ∀ x y, f x = f y → Gamma x y = 0) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
      (hsuccess : ∀ x, 1 - eps ≤ povmProb (labelPovm label) (f x) (states x)),
      |advProgress Gamma weight states| ≤
        (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Gamma‖) := by
  constructor
  · intro X H Y _ _ _ _ _ _ Gamma f label eps
    exact povm_final_progress_label Gamma f label eps
  · intro X H Y _ _ _ _ _ _ Gamma weight states f label eps hG hw hs hz he0 he1 hsuccess
    exact povm_final_progress_label Gamma f label eps weight states hG hw hs hz he0 he1
      (isPovm_labelPovm label) hsuccess
end
set_option linter.unusedVariables false in
noncomputable section

/-- The norm ratio of a Hermitian adversary matrix vanishing on equal outputs is bounded by
`generalAdversaryValue` when its maximum filter norm is positive. -/
theorem adversary_ratio_le_sdp {X E : Type} [Fintype X] [DecidableEq X] [Fintype E]
    [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hm : 0 < maxFilterNorm input Gamma) :
    ENNReal.ofReal (‖Gamma‖ / maxFilterNorm input Gamma) ≤ generalAdversaryValue input f := by
  set m := maxFilterNorm input Gamma with hmdef
  have hmpos : 0 < m := hm
  set c : ℂ := ((1 / m : ℝ) : ℂ) with hc
  set Gamma' : Matrix X X ℂ := c • Gamma with hG'
  have hnorm : ‖Gamma'‖ = ‖Gamma‖ / m := by
    rw [hG', l2_opNorm_def, l2_opNorm_def, map_smul, norm_smul]
    rw [hc, show ‖((1 / m : ℝ) : ℂ)‖ = |1 / m| from RCLike.norm_ofReal (1 / m : ℝ),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    field_simp
  have hG'herm : Gamma'.IsHermitian := by
    have hGadj : Gammaᴴ = Gamma := hG
    have hGadj' : ∀ i j, star (Gamma j i) = Gamma i j := by
      intro i j
      have h := congrArg (fun M : Matrix X X ℂ => M i j) hGadj
      simpa [Matrix.conjTranspose_apply] using! h
    ext i j
    simp [hG', Matrix.conjTranspose_apply, Matrix.smul_apply, hc, Complex.conj_ofReal, hGadj']
  have hz' : ∀ x y, f x = f y → Gamma' x y = 0 := by
    intro x y hxy
    simp [hG', Matrix.smul_apply, hc]
    rw [hz x y hxy]
    simp
  have hfilter : ∀ j, ‖gramFilterDelta input j ⊙ Gamma'‖ ≤ 1 := by
    intro j
    have hhad : gramFilterDelta input j ⊙ Gamma' = c • (gramFilterDelta input j ⊙ Gamma) := by
      ext x y
      simp [hG', Matrix.hadamard_apply, Matrix.smul_apply]
      ring
    rw [hhad, l2_opNorm_def, map_smul, norm_smul]
    rw [hc, show ‖((1 / m : ℝ) : ℂ)‖ = |1 / m| from RCLike.norm_ofReal (1 / m : ℝ),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m), ← l2_opNorm_def]
    have hle : ‖gramFilterDelta input j ⊙ Gamma‖ ≤ m := by
      rw [← genAdvFilter_eq_filterDelta]
      exact genAdvFilter_le_maxFilterNorm input Gamma j
    have hmul : (1 / m : ℝ) * ‖gramFilterDelta input j ⊙ Gamma‖ ≤ (1 / m : ℝ) * m :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    calc (1 / m : ℝ) * ‖gramFilterDelta input j ⊙ Gamma‖ ≤ (1 / m : ℝ) * m := hmul
      _ = 1 := by field_simp
  refine le_iSup_of_le ⟨Gamma', hG'herm, hz', hfilter⟩ ?_
  rw [hnorm]
end
noncomputable section
set_option linter.unusedVariables false in

/-- The norm of a Hermitian matrix vanishing on pairs of equal outputs and with all query filter
norms at most one is bounded by `generalAdversaryValue`. -/
theorem adversary_witness_le_sdp {X E : Type} [Fintype X] [DecidableEq X] [Fintype E]
    [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hfilter : ∀ j, ‖gramFilterDelta input j ⊙ Gamma‖ ≤ 1) :
    ENNReal.ofReal ‖Gamma‖ ≤ generalAdversaryValue input f := by
  refine le_iSup_of_le ⟨Gamma, hG, hz, hfilter⟩ ?_
  show ENNReal.ofReal ‖Gamma‖ ≤ ENNReal.ofReal ‖Gamma‖
  exact ENNReal.ofReal_le_ofReal le_rfl
end
noncomputable section
set_option linter.unusedVariables false in

/-- Every query-filtered matrix is zero when the maximum filter norm of the adversary matrix is
zero. -/
theorem adversary_degenerate_filter {X E : Type} [Fintype X] [DecidableEq X] [Fintype E]
    [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0) (hne : Gamma ≠ 0)
    (hm : maxFilterNorm input Gamma = 0) :
    ∀ j, genAdvFilter input Gamma j = 0 := by
  intro j
  have hj : ‖genAdvFilter input Gamma j‖ = 0 := by
    have hle := genAdvFilter_le_maxFilterNorm input Gamma j
    rw [hm] at hle
    exact le_antisymm hle (by simp)
  exact norm_eq_zero.mp hj
end
noncomputable section
set_option linter.unusedVariables false in

/-- Collects the normalized witness and positive-denominator ratio comparisons with
`generalAdversaryValue`, the zero-filter conclusion, and the comparison of an individual
witness value with `advPmValue`. -/
theorem stageA_general_adversary_clause17 :
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
      (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
      (hfilter : ∀ j, ‖gramFilterDelta input j ⊙ Gamma‖ ≤ 1),
      ENNReal.ofReal ‖Gamma‖ ≤ generalAdversaryValue input f) ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
      (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
      (hm : 0 < maxFilterNorm input Gamma),
      ENNReal.ofReal (‖Gamma‖ / maxFilterNorm input Gamma) ≤ generalAdversaryValue input f) ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
      (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0) (hne : Gamma ≠ 0)
      (hm : maxFilterNorm input Gamma = 0),
      ∀ j, genAdvFilter input Gamma j = 0) ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
      (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0) (hne : Gamma ≠ 0),
      advPmWitnessValue input Gamma ≤ advPmValue input f) := by
  refine ⟨adversary_witness_le_sdp, adversary_ratio_le_sdp, adversary_degenerate_filter, ?_⟩
  intro X E _ _ _ _ n input f Gamma hG hz hne
  unfold advPmValue
  exact le_iSup
    (fun Gamma : {Gamma : Matrix X X ℂ // Gamma.IsHermitian ∧
      (∀ x y, f x = f y → Gamma x y = 0) ∧ Gamma ≠ 0} => advPmWitnessValue input Gamma.1)
    ⟨Gamma, hG, hz, hne⟩
end
noncomputable section

/-- A nonzero adversary matrix with zero maximum filter norm has infinite `advPmWitnessValue`. -/
theorem stageA_general_adversary_clause17_degenerate
    {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0) (hne : Gamma ≠ 0)
    (hm : maxFilterNorm input Gamma = 0) :
    advPmWitnessValue input Gamma = ⊤ := by
  have hnorm : (‖Gamma‖ : ℝ) > 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
    have hxy : (0 : ℝ) < ‖Gamma x y‖ := by
      rw [norm_pos_iff]
      simpa using! hy
    have hle := gamma2_operator_entry_bound Gamma x y
    exact lt_of_lt_of_le hxy hle
  unfold advPmWitnessValue
  rw [hm, ENNReal.ofReal_zero, ENNReal.div_eq_top]
  exact Or.inl ⟨ENNReal.ofReal_ne_zero_iff.mpr hnorm, rfl⟩
end
noncomputable section
set_option linter.unusedVariables false in

/-- Combines the comparison of individual witnesses with `advPmValue` and attainment of a finite
`generalAdversaryValue` by a real symmetric feasible matrix. -/
theorem stageA_general_adversary_clause18 :
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
      (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0) (hne : Gamma ≠ 0),
      advPmWitnessValue input Gamma ≤ advPmValue input f) ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E),
      generalAdversaryValue input f < ⊤ →
      ∃ Gamma : Matrix X X ℂ, Gamma.IsSymm ∧ (∀ x y, (Gamma x y).im = 0) ∧
        (∀ x y, f x = f y → Gamma x y = 0) ∧
        (∀ j, ‖gramFilterDelta input j ⊙ Gamma‖ ≤ 1) ∧
        generalAdversaryValue input f = ENNReal.ofReal ‖Gamma‖) := by
  refine ⟨?_, ?_⟩
  · intro X E _ _ _ _ n input f Gamma hG hz hne
    unfold advPmValue
    exact le_iSup
      (fun Gamma : {Gamma : Matrix X X ℂ // Gamma.IsHermitian ∧
        (∀ x y, f x = f y → Gamma x y = 0) ∧ Gamma ≠ 0} => advPmWitnessValue input Gamma.1)
      ⟨Gamma, hG, hz, hne⟩
  · intro X E _ _ _ _ n input f hfin
    exact generalAdversaryValue_real_attained input f hfin
end
noncomputable section

/-- The condition that an adversary matrix vanish on pairs of equal outputs is invariant under
an equivalence of output types. -/
theorem adversary_feasible_relabel {X E E' : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']
    (sigma : E ≃ E') (f : X → E) (Gamma : Matrix X X ℂ) :
    (∀ x y, f x = f y → Gamma x y = 0) ↔
      (∀ x y, (sigma ∘ f) x = (sigma ∘ f) y → Gamma x y = 0) := by
  constructor
  · intro h x y hxy
    have hsigma : sigma (f x) = sigma (f y) := by
      simpa only [Function.comp_apply] using! hxy
    exact h x y (sigma.injective hsigma)
  · intro h x y hxy
    have hsigma : (sigma ∘ f) x = (sigma ∘ f) y := by
      simpa only [Function.comp_apply] using! congrArg sigma hxy
    exact h x y hsigma
end
noncomputable section
set_option linter.unusedVariables false in

/-- Pairs invariance of adversary feasibility under output relabeling with the identity
implication for a zero maximum filter norm. -/
theorem stageA_general_adversary_clause19 :
    (∀ {X E E' : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
      [Fintype E'] [DecidableEq E'] (sigma : E ≃ E') (f : X → E) (Gamma : Matrix X X ℂ),
      (∀ x y, f x = f y → Gamma x y = 0) ↔
        (∀ x y, (sigma ∘ f) x = (sigma ∘ f) y → Gamma x y = 0)) ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ)
      (hG : Gamma.IsHermitian) (hne : Gamma ≠ 0),
      maxFilterNorm input Gamma = 0 → maxFilterNorm input Gamma = 0) := by
  refine ⟨adversary_feasible_relabel, ?_⟩
  intro X E _ _ _ _ n input Gamma _hG _hne hzero
  exact hzero
end
noncomputable section
set_option linter.unusedVariables false in

/-- Bounds `generalAdversaryValue` and the norm of every normalized feasible Hermitian witness
by the filtered gamma-two norm of the function evaluation matrix. -/
theorem stageA_general_adversary_clause20 :
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E),
      generalAdversaryValue input f ≤
        filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input)) ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E) (Gamma : Matrix X X ℂ)
      (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
      (hfilter : ∀ j, ‖gramFilterDelta input j ⊙ Gamma‖ ≤ 1),
      ENNReal.ofReal ‖Gamma‖ ≤ filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input)) := by
  refine ⟨generalAdversaryValue_le_queryDelta, ?_⟩
  intro X E _ _ _ _ n input f Gamma _hG hz hfilter
  exact adversary_le_filteredGamma2_queryDelta input f Gamma hz hfilter
end
noncomputable section

/-- Effects for distinct outputs of a basis-label POVM have zero product. -/
theorem labelPovm_orthogonal {H E : Type} [Fintype H] [DecidableEq H] [Fintype E]
    [DecidableEq E] (label : H → E) (y y' : E) (hne : y ≠ y') :
    labelPovm label y * labelPovm label y' = 0 := by
  ext h h'
  by_cases hh : h = h'
  · subst hh
    by_cases hy : label h = y
    · have hy' : label h ≠ y' := by simpa [hy] using! hne
      simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single h]
      · simp [labelPovm, hy, hne]
      · intro b _ hb
        simp [labelPovm, Matrix.diagonal_apply, Ne.symm hb]
      · simp
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single h]
      · simp [labelPovm, hy]
      · intro b _ hb
        simp [labelPovm, Matrix.diagonal_apply, Ne.symm hb]
      · simp
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single h]
    · simp [labelPovm, hh]
    · intro b _ hb
      simp [labelPovm, Matrix.diagonal_apply, Ne.symm hb]
    · simp
end
noncomputable section

/-- Each effect of a basis-label POVM is idempotent. -/
theorem labelPovm_idem {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) (y : E) : labelPovm label y * labelPovm label y = labelPovm label y := by
  ext h h'
  by_cases hh : h = h'
  · subst hh
    simp [labelPovm, Matrix.diagonal_apply, Matrix.mul_apply]
  · simp [labelPovm, Matrix.diagonal_apply, Matrix.mul_apply, hh]
end
noncomputable section

/-- Collects the POVM property, orthogonality of distinct label effects, and equality of POVM
probabilities with the corresponding basis-event probabilities. -/
theorem stageA_general_adversary_clause21 :
    (∀ {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
      (label : H → E), IsPovm (labelPovm label)) ∧
    (∀ {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
      (label : H → E) (y y' : E) (hne : y ≠ y'),
      labelPovm label y * labelPovm label y' = 0) ∧
    (∀ {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
      (label : H → E) (y : E) (psi : QState H),
      povmProb (labelPovm label) y psi = MeasureProb psi (outcomeEvent label y)) := by
  refine ⟨isPovm_labelPovm, labelPovm_orthogonal, labelPovm_povmProb⟩
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
