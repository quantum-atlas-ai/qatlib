/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

def effectiveAdjointStep : EffectiveStep → EffectiveStep
  | .fixed g => .fixed (finiteCodeAdjoint g)
  | .phase w a b axis => .phase w (-a) b axis
  | .query slot ws cs adj => .query slot ws cs (!adj)
  | .postselect ws => .postselect ws

def effectiveAdjointProgram (p : EffectiveProgram) : EffectiveProgram :=
  ⟨p.width,(p.steps.map effectiveAdjointStep).reverse⟩

theorem effectiveAdjointStep_legal (n : ℕ) (s : EffectiveStep) :
    effectiveStepLegal n (effectiveAdjointStep s) ↔ effectiveStepLegal n s := by
  cases s with
  | fixed g => cases g <;> simp [effectiveAdjointStep,effectiveStepLegal,finiteCodeAdjoint,finiteCodeLegal]
  | phase w a b axis => rfl
  | query slot ws cs adj => rfl
  | postselect ws => rfl

theorem effectiveAdjointProgram_legal (p : EffectiveProgram) (hp : effectiveLegal p) :
    effectiveLegal (effectiveAdjointProgram p) := by
  intro s hs
  simp only [effectiveAdjointProgram,List.mem_reverse,List.mem_map] at hs
  obtain ⟨t,ht,rfl⟩ := hs
  exact (effectiveAdjointStep_legal p.width t).mpr (hp t ht)

theorem effectiveAdjointProgram_queries (p : EffectiveProgram) :
    effectiveQueries (effectiveAdjointProgram p) = effectiveQueries p := by
  rcases p with ⟨n,l⟩
  simp only [effectiveQueries,effectiveAdjointProgram,List.filter_reverse,List.length_reverse]
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp_all [effectiveAdjointStep]

theorem effectiveAdjointProgram_gates (p : EffectiveProgram) :
    effectiveGates (effectiveAdjointProgram p) = effectiveGates p := by
  rcases p with ⟨n,l⟩
  simp only [effectiveGates,effectiveAdjointProgram,List.filter_reverse,List.length_reverse]
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp_all [effectiveAdjointStep]

theorem effectiveOAA_error_budget (ε : ℝ) (hε : 0≤ε) (hsmall : ε≤1/16) :
    0 ≤ Qatlib.Concepts.CoherentSim.CoherentOAA.coherentOAAError ε ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.coherentOAAError ε ≤ 4*ε := by
  unfold Qatlib.Concepts.CoherentSim.CoherentOAA.coherentOAAError
  constructor
  · positivity
  · have hsq : ε^2 ≤ (1/16 : ℝ)^2 := pow_le_pow_left₀ hε hsmall 2
    have hc : 3+(3/2 : ℝ)*ε+(1/2 : ℝ)*ε^2 ≤ 4 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hc hε)

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
