/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSource.DenseHistoryOracleWord

/-!
# Substitution of words with multiple oracle sources

`substitute` expands a single-oracle adjoint circuit into a word using three oracle sources,
inserting the body or its adjoint for each oracle access. The module proves evaluation
compatibility, well formedness, and exact source query and known gate counts for the expanded
word and its inverse. See [BrassardEtAl2002] for background.

## Main statements

* `evaluate_substitute`: Evaluating the substituted word equals evaluating the outer circuit
  with the evaluated body as its oracle matrix.
* `queryCount_substitute`: For each source, the substituted query count is the outer adjoint
  query count times the body query count for that source.
* `inverse_resources`: The inverse substituted word is well formed and preserves the per-source
  query product and the stated gate count formula.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution

open Matrix
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord
open scoped Classical

variable {H : Type}

/-- The instruction type for a word with three distinguished oracle sources. -/
abbrev ThreeSourceStep :=
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step

/-- Expands a known gate to itself, a forward oracle use to `body`, and an inverse oracle use to
the adjoint body. -/
noncomputable def expand (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H → List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)
  | .gate V => [.gate V]
  | .forward => body
  | .backward => Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord body

/-- Replaces each oracle instruction of `outer` by the body or its adjoint and retains the known
gates. -/
noncomputable def substitute (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H) := outer.flatMap (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand body)

/-- Substitution into an empty outer word produces the empty word. -/
@[simp] theorem substitute_nil (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body [] = [] := rfl

/-- Substitution into a word beginning with `c` concatenates the expansion of `c` with the
substituted tail. -/
theorem substitute_cons (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (c : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)
    (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body (c :: outer) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand body c ++ Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer := rfl

/-- Substitution distributes over concatenation of outer words. -/
theorem substitute_append (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer tail : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body (outer ++ tail) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer ++ Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body tail := by
  exact List.flatMap_append

/-- For each source, the substituted query count is the outer adjoint query count times the body
query count for that source. -/
theorem queryCount_substitute (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount outer * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s body := by
  induction outer with
  | nil => simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount]
  | cons c outer ih =>
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute_cons, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_append, ih]
    cases c with
    | gate V => simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryFlag, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
    | forward => simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]; ring
    | backward => simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_adjointWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]; ring

/-- The substituted gate count is the outer known gate count plus the outer query count times
the body gate count. -/
theorem gateCount_substitute (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount outer + Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount outer * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount body := by
  induction outer with
  | nil => simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
  | cons c outer ih =>
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute_cons, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_append, ih]
    cases c with
    | gate V => simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateFlag, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]; omega
    | forward => simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]; ring
    | backward =>
      simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_adjointWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
      ring

section Semantics

variable [Fintype H] [DecidableEq H]

/-- Evaluating the substituted word equals evaluating the outer circuit with the evaluated body
as its oracle matrix. -/
theorem evaluate_substitute (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H))
    (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O body) outer := by
  induction outer with
  | nil => rfl
  | cons c outer ih =>
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute_cons, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_append, ih]
    cases c <;> simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate,
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.instructionMatrix, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate,
      Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_adjointWord]

/-- Substituting a well formed body into a well formed outer adjoint circuit gives a well formed
word. -/
theorem substitute_wellFormed (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hbody : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed body) (houter : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit outer) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer) := by
  intro c hc
  obtain ⟨d, hd, hm⟩ := List.mem_flatMap.mp hc
  cases d with
  | gate V =>
    have he : c = .gate V := by
      simpa [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand] using hm
    subst c
    exact houter V hd
  | forward => exact hbody c hm
  | backward => exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord_wellFormed body hbody) c hm

/-- The inverse substituted word is well formed and preserves the per-source query product and
the stated gate count formula. -/
theorem inverse_resources (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hbody : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed body) (houter : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit outer) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer)) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer)) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount outer * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s body) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer)) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount outer + Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount outer * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount body := by
  refine ⟨Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord_wellFormed _ (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute_wellFormed body outer hbody houter), ?_, ?_⟩
  · intro s
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_adjointWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.queryCount_substitute]
  · rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_adjointWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.gateCount_substitute]

/-- The inverse substituted word evaluates to the conjugate transpose of the outer circuit
evaluated with the body matrix as oracle. -/
theorem evaluate_inverse (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H))
    (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer)) =
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O body) outer)ᴴ := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_adjointWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.evaluate_substitute]

end Semantics

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution
