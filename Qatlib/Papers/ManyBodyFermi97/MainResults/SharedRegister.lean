/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Hopping
import Qatlib.Papers.ManyBodyFermi97.MainResults.OnsiteWord
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.SharedRegister
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical BigOperators

abbrev Shared (m : ℕ) :=
  Qatlib.Papers.ManyBodyFermi97.MainResults.OnsiteWord.Basis m

def modeEquiv (m : ℕ) : Fin (2*m) ≃ (Fin m × Bool) :=
  (finCongr (by ring : 2*m = m*2)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin m))
      (Fintype.equivOfCardEq (by simp [Fintype.card_bool]))).trans finProdFinEquiv).symm

def stateEquiv (m : ℕ) : Reg (2*m) ≃ Shared m :=
  Equiv.arrowCongr (modeEquiv m) (Equiv.refl Bool)

def relabel {I J : Type*} (e : I ≃ J) (U : Matrix I I ℂ) : Matrix J J ℂ :=
  U.submatrix (⇑e.symm) (⇑e.symm)

theorem relabel_unitary {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    relabel e U ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  unfold relabel
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [← Matrix.star_eq_conjTranspose]
  rw [Matrix.submatrix_mul_equiv (star U) U (⇑e.symm) e.symm (⇑e.symm), hU]
  exact Matrix.submatrix_one_equiv e.symm

theorem applyGate_relabel {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ)
    (ψ : QState J) (x : J) :
    ApplyGate (relabel e U) ψ x = ApplyGate U (fun z => ψ (e z)) (e.symm x) := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, relabel, Matrix.submatrix,
    Matrix.of_apply]
  rw [Fintype.sum_equiv e.symm
    (fun y : J => U (e.symm x) (e.symm y) * ψ y)
    (fun z : I => U (e.symm x) z * ψ (e z))]
  intro y
  simp

def relabelWord {I J : Type*} (e : I ≃ J) (C : Circuit I) : Circuit J :=
  C.map (fun s => match s with
    | .gate U => .gate (relabel e U)
    | .query => .query)

theorem relabelWord_gate {I J : Type*} (e : I ≃ J) (U : Matrix I I ℂ)
    (rest : Circuit I) :
    relabelWord e (Step.gate U :: rest) =
      Step.gate (relabel e U) :: relabelWord e rest := rfl

theorem relabelWord_query {I J : Type*} (e : I ≃ J) (rest : Circuit I) :
    relabelWord e (Step.query :: rest) = Step.query :: relabelWord e rest := rfl

theorem queryCount_relabelWord {I J : Type*} (e : I ≃ J) (C : Circuit I) :
    QueryCount (relabelWord e C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | gate U => rw [relabelWord_gate]; simp [ih]
    | query => rw [relabelWord_query]; simp [ih]

theorem gateCount_relabelWord {I J : Type*} (e : I ≃ J) (C : Circuit I) :
    GateCount (relabelWord e C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | gate U => rw [relabelWord_gate]; simp [ih]
    | query => rw [relabelWord_query]; simp [ih]

theorem relabelWord_unitary {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) {C : Circuit I}
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (relabelWord e C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s rest ih =>
    cases s with
    | gate U =>
      have h := (isUnitaryCircuit_gate U rest).mp hC
      rw [relabelWord_gate, isUnitaryCircuit_gate]
      exact ⟨relabel_unitary e h.1, ih h.2⟩
    | query =>
      have h := (isUnitaryCircuit_query rest).mp hC
      rw [relabelWord_query, isUnitaryCircuit_query]
      exact ih h

theorem run_relabelWord {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (C : Circuit I) (ψ : QState J) :
    Run 1 (relabelWord e C) ψ = fun x => Run 1 C (fun z => ψ (e z)) (e.symm x) := by
  induction C generalizing ψ with
  | nil => simp [relabelWord]
  | cons s rest ih =>
    cases s with
    | gate U =>
      funext x
      rw [relabelWord_gate]
      simp only [Run]
      rw [ih]
      rw [show (fun z => ApplyGate (relabel e U) ψ (e z)) =
          ApplyGate U (fun z => ψ (e z)) from by
        funext z
        rw [applyGate_relabel]
        simp]
    | query =>
      funext x
      rw [relabelWord_query]
      simp only [Run, applyGate_one]
      rw [ih]

def onsiteWord (m : ℕ) (V : Fin m → ℝ) (time : ℝ) : Circuit (Shared m) :=
  OnsiteWord.word (Finset.univ.toList) V time

def hoppingWord (m : ℕ) (t : ℝ) : Circuit (Shared m) :=
  relabelWord (stateEquiv m) (Hopping.hopPassWord (2*m) t)

theorem hoppingWord_correct (m : ℕ) (t : ℝ) :
    IsUnitaryCircuit (hoppingWord m t) ∧ QueryCount (hoppingWord m t) = 0 ∧
      GateCount (hoppingWord m t) = (chainPairs (2*m)).card := by
  obtain ⟨hu, hq, hg⟩ := Hopping.hopPassWord_correct (2*m) t
  refine ⟨relabelWord_unitary (stateEquiv m) hu, ?_, ?_⟩
  · rw [hoppingWord, queryCount_relabelWord, hq]
  · rw [hoppingWord, gateCount_relabelWord, hg]

def fullWord (m : ℕ) (V : Fin m → ℝ) (t time : ℝ) : Circuit (Shared m) :=
  onsiteWord m V time ++ hoppingWord m t

theorem fullWord_correct (m : ℕ) (V : Fin m → ℝ) (t time : ℝ) :
    IsUnitaryCircuit (fullWord m V t time) ∧
      QueryCount (fullWord m V t time) = 0 ∧
      GateCount (fullWord m V t time) = m + (chainPairs (2*m)).card ∧
      GateCount (fullWord m V t time) ≤ 3*m ∧
      ∀ ψ : QState (Shared m),
        Run 1 (fullWord m V t time) ψ =
          Run 1 (hoppingWord m t) (Run 1 (onsiteWord m V time) ψ) := by
  obtain ⟨huo, hqo, hgo⟩ := OnsiteWord.full_pass_resources m V time
  obtain ⟨huh, hqh, hgh⟩ := hoppingWord_correct m t
  have hfull : GateCount (fullWord m V t time) = m + (chainPairs (2*m)).card := by
    rw [fullWord, gateCount_append]
    simp only [onsiteWord]
    rw [hgo, hgh]
  refine ⟨?_, ?_, hfull, ?_, ?_⟩
  · rw [fullWord, isUnitaryCircuit_append]
    exact ⟨huo, huh⟩
  · rw [fullWord, queryCount_append]
    simp only [onsiteWord]
    rw [hqo, hqh]
  · rw [hfull]
    have hcard := chainPairs_card (2*m)
    omega
  · intro ψ
    rw [fullWord, run_append]

end Qatlib.Papers.ManyBodyFermi97.MainResults.SharedRegister
