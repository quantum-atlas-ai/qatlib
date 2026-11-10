/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithmQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.NativeSingleSolutionQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonDataQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

def Theorem3Statement : Prop :=
  ∀ (k : ℕ), 2 ≤ k →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M : ℕ) [NeZero M], 0 < N → 0 < M →
        ∃ A : Qatlib.Concepts.WalkFind.SearchAlgorithm.RandomQueryAlgorithm N M k,
          Qatlib.Concepts.WalkFind.SearchAlgorithm.algorithmCorrect A ∧
            ∀ s, (QueryCount (A.program s) : ℝ) ≤ C * (N : ℝ) ^ ((k : ℝ) / (k + 1))

def Theorem3RestrictedStatement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexity

theorem theorem3_restricted : Theorem3RestrictedStatement :=
  Qatlib.Concepts.WalkFind.UniqueCollision.queryComplexity_answer

def Theorem4Statement : Prop :=
  Qatlib.Concepts.WalkFind.SearchAlgorithm.GeneralQueryMemoryContract

def Theorem4RestrictedStatement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithm ∧
    Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexity

theorem theorem4_restricted : Theorem4RestrictedStatement :=
  ⟨Qatlib.Concepts.WalkFind.UniqueCollision.elementDistinctnessAlgorithm_answer,
    Qatlib.Concepts.WalkFind.UniqueCollision.queryComplexity_answer⟩

def Theorem5Statement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.NativeSingleSolution

theorem theorem5 : Theorem5Statement :=
  Qatlib.Concepts.WalkFind.UniqueCollision.nativeSingleSolution_answer

def Algorithm1Statement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonData

theorem algorithm1 : Algorithm1Statement :=
  Qatlib.Concepts.WalkFind.UniqueCollision.nativeJohnsonData_answer

def Algorithm2Statement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonData ∧
    Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithm

theorem algorithm2 : Algorithm2Statement :=
  ⟨Qatlib.Concepts.WalkFind.UniqueCollision.nativeJohnsonData_answer,
    Qatlib.Concepts.WalkFind.UniqueCollision.elementDistinctnessAlgorithm_answer⟩

end Qatlib.Concepts.WalkFind.UniqueCollision
