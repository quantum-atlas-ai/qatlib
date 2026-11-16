/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FermionicQFT14.MainResults.ScatteringAlgorithm
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! # A zero-cost inhabitant diagnoses the simulator record boundary
The record stores labels and a free numerical cost. These conditions do not
connect an executed circuit to a scattering distribution or its cost.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.FermionicQFT14.MainResults
open Qatlib.Papers.FermionicQFT14.MainResults

/-- The archived record admits positive model parameters and zero assigned cost. -/
def freeSimulator : GrossNeveuSimulator :=
  ⟨1, 1, 1, paperPipeline, fun _ _ => 0⟩

/-- All the record's model and pipeline predicates hold for the zero-cost witness. -/
theorem freeContract : IsMassiveGrossNeveuModel freeSimulator ∧
    ImplementsPaperPipeline freeSimulator ∧
      PolynomialGateScaling freeSimulator.gateCount := by
  refine ⟨⟨by norm_num [IsMassiveGrossNeveuModel, freeSimulator],
    by norm_num [IsMassiveGrossNeveuModel, freeSimulator]⟩, rfl, ?_⟩
  refine ⟨0, le_rfl, 1, 1, zero_lt_one, le_rfl, ?_⟩
  intro ε p _ _ _
  simp [freeSimulator]

end Qatlib.Papers.FermionicQFT14.MainResults
