/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSource.DenseHistoryOracleWord
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution

open Matrix
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord
open scoped Classical

variable {H : Type}

abbrev ThreeSourceStep :=
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step

noncomputable def expand (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H → List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)
  | .gate V => [.gate V]
  | .forward => body
  | .backward => Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord body

noncomputable def substitute (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H) := outer.flatMap (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand body)

@[simp] theorem substitute_nil (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body [] = [] := rfl

theorem substitute_cons (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (c : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)
    (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body (c :: outer) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand body c ++ Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer := rfl

theorem substitute_append (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H)) (outer tail : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body (outer ++ tail) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer ++ Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body tail := by
  exact List.flatMap_append

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

theorem evaluate_inverse (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.ThreeSourceStep H))
    (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer)) =
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O body) outer)ᴴ := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_adjointWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.evaluate_substitute]

end Semantics

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution
