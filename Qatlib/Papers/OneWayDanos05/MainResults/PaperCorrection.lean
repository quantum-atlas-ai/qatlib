/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneWayDanos05.MainResults.FlowRewrite
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore

/-!
# Outcome-dependent corrections in the paper convention

The operator `paperCorrection` applies X when an active predecessor flows to the wire and Z
according to the parity of `zContributors`. The module proves its Pauli form and causal
dependence, then obtains both properties from output-masked graph flow witnesses. These
definitions express the correction pattern of [DanosKashefi2006].

## Main statements

* `paperCorrection_pauliWire`: Every paper-convention correction is a Pauli wire operator.
* `paperCorrection_causal`: If flow successors and their other neighbors are later in `prec`,
  the paper-convention corrections depend causally on outcomes.
* `paperFlowCorrection_pauli_causal`: An MBQC flow possesses strict-order witnesses for which
  the output-masked paper corrections are Pauli wire operators and are causal.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

variable {n : ℕ}

/-- The true-outcome vertices whose flow successor is adjacent to `u`, excluding `u` itself as a
contributor. -/
def zContributors (G : MbqcGraph n) (f : Fin n → Option (Fin n)) (s : Fin n → Bool)
    (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => s v = true ∧
    ∃ w : Fin n, f v = some w ∧ u ≠ v ∧ mbqcAdj G w u)

/-- The product of an X correction triggered by an active flow predecessor and a Z correction
triggered by odd contributor parity. -/
noncomputable def paperCorrection (G : MbqcGraph n) (f : Fin n → Option (Fin n))
    (s : Fin n → Bool) (u : Fin n) : Operator 2 :=
  (if ∃ v : Fin n, s v = true ∧ f v = some u then pauliX else (1 : Operator 2)) *
  (if Odd (zContributors G f s u).card then pauliZ else (1 : Operator 2))

/-- Every paper-convention correction is a Pauli wire operator [DanosKashefi2006]. -/
theorem paperCorrection_pauliWire (G : MbqcGraph n) (f : Fin n → Option (Fin n))
    (s : Fin n → Bool) (u : Fin n) :
    MbqcPauliWire (paperCorrection G f s u) := by
  unfold paperCorrection
  by_cases hx : ∃ v : Fin n, s v = true ∧ f v = some u
  · rw [if_pos hx]
    by_cases hz : Odd (zContributors G f s u).card
    · rw [if_pos hz]
      exact Or.inr (Or.inr (Or.inr rfl))
    · rw [if_neg hz, mul_one]
      exact Or.inr (Or.inl rfl)
  · rw [if_neg hx, one_mul]
    by_cases hz : Odd (zContributors G f s u).card
    · rw [if_pos hz]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [if_neg hz]
      exact Or.inl rfl

/-- If flow successors and their other neighbors are later in `prec`, the paper-convention
corrections depend causally on outcomes [DanosKashefi2006]. -/
theorem paperCorrection_causal (G : MbqcGraph n) (f : Fin n → Option (Fin n))
    (prec : Fin n → Fin n → Prop)
    (hF2 : ∀ v u : Fin n, f v = some u → prec v u)
    (hF3 : ∀ v w u : Fin n, f v = some w → u ≠ v → mbqcAdj G w u → prec v u) :
    MbqcCausalCorrection prec (paperCorrection G f) := by
  intro s s' u hagree
  unfold paperCorrection
  have hx : (∃ v : Fin n, s v = true ∧ f v = some u) ↔
      (∃ v : Fin n, s' v = true ∧ f v = some u) := by
    constructor
    · rintro ⟨v, hv, hf⟩
      exact ⟨v, by rw [← hagree v (hF2 v u hf)]; exact hv, hf⟩
    · rintro ⟨v, hv, hf⟩
      exact ⟨v, by rw [hagree v (hF2 v u hf)]; exact hv, hf⟩
  have hset : zContributors G f s u = zContributors G f s' u := by
    apply Finset.filter_congr
    intro v _
    constructor
    · rintro ⟨hv, w, hfw, hne, hadj⟩
      have hprec : prec v u := hF3 v w u hfw hne hadj
      exact ⟨by rw [← hagree v hprec]; exact hv, w, hfw, hne, hadj⟩
    · rintro ⟨hv, w, hfw, hne, hadj⟩
      have hprec : prec v u := hF3 v w u hfw hne hadj
      exact ⟨by rw [hagree v hprec]; exact hv, w, hfw, hne, hadj⟩
  rw [if_congr hx rfl rfl, hset]

/-- An MBQC flow possesses strict-order witnesses for which the output-masked paper corrections
are Pauli wire operators and are causal [DanosKashefi2006]. -/
theorem paperFlowCorrection_pauli_causal {n : ℕ} (G : MbqcGraph n)
    (I O : Finset (Fin n)) (h : MbqcHasFlow G I O) :
    ∃ (f : Fin n → Option (Fin n)) (prec : Fin n → Fin n → Prop),
      IsStrictOrder (Fin n) prec ∧
      (∀ v : Fin n, v ∉ O → ∃ w : Fin n,
        f v = some w ∧ mbqcAdj G v w ∧ w ∉ I ∧ prec v w ∧
          ∀ k : Fin n, mbqcAdj G w k → k ≠ v → prec v k) ∧
      (∀ s : Fin n → Bool, ∀ u : Fin n,
        MbqcPauliWire (paperCorrection G (clause6Aux_outMaskedFlow f O) s u)) ∧
      MbqcCausalCorrection prec (paperCorrection G (clause6Aux_outMaskedFlow f O)) := by
  obtain ⟨f, prec, _dp, hord, hF⟩ := h
  refine ⟨f, prec, hord, hF, ?_,
    paperCorrection_causal G (clause6Aux_outMaskedFlow f O) prec ?_ ?_⟩
  · intro s u
    exact paperCorrection_pauliWire G (clause6Aux_outMaskedFlow f O) s u
  · intro v u hfu
    by_cases hv : v ∈ O
    · simp [clause6Aux_outMaskedFlow, hv] at hfu
    · have hf' : f v = some u := by simpa [clause6Aux_outMaskedFlow, hv] using hfu
      obtain ⟨w, hw, _, _, hprec, _⟩ := hF v hv
      have hwu : w = u := by
        have hsame : some w = some u := hw.symm.trans hf'
        simpa using hsame
      rw [hwu] at hprec
      exact hprec
  · intro v w u hfw hne hadj
    by_cases hv : v ∈ O
    · simp [clause6Aux_outMaskedFlow, hv] at hfw
    · have hf' : f v = some w := by simpa [clause6Aux_outMaskedFlow, hv] using hfw
      obtain ⟨w', hw', _, _, _, hF3⟩ := hF v hv
      have hww : w' = w := by
        have hsame : some w' = some w := hw'.symm.trans hf'
        simpa using hsame
      rw [hww] at hF3
      exact hF3 u hadj hne

end Qatlib.Papers.OneWayDanos05.MainResults
