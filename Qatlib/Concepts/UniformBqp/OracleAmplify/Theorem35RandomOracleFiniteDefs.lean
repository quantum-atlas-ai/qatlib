/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
set_option warningAsError false

open Qatlib

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.UniformBqp.OracleAmplify

def allOnes {K : Type} : K → Bool := fun _ => true

def bitQueryOf {K : Type} (A : (K → Bool) → (K → Bool)) :
    ((K → Bool) × K) → Bool := fun p => A p.1 p.2

abbrev QueryRegister (K W : Type) := ((((K → Bool) × K) × Bool) × W)

noncomputable def acceptProb {K W : Type} [Fintype K] [DecidableEq K] [Fintype W]
    [DecidableEq W] (C : Circuit (QueryRegister K W)) (ψ : QState (QueryRegister K W))
    (E : Finset (QueryRegister K W)) (A : (K → Bool) → (K → Bool)) : ℝ :=
  MeasureProb (Run (workspaceBitOracle (W := W) (bitQueryOf A)) C ψ) E

def decidesAtAllOnes {K : Type} [Fintype K] [DecidableEq K] (p : ℝ)
    (A : (K → Bool) → (K → Bool)) : Prop :=
  ((allOnes ∈ Finset.univ.image A) → 2 / 3 ≤ p) ∧
    ((allOnes ∉ Finset.univ.image A) → p ≤ 1 / 3)
end Qatlib.Concepts.UniformBqp.OracleAmplify
