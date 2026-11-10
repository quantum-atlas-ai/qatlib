/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Defs

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

def mnrsAbsoluteGap {X : Type*} [Fintype X]
    (P : Matrix X X ℝ) (δ : ℝ) : Prop :=
  IsLUB
    {b : ℝ | b = 0 ∨
      ∃ (ν : ℝ) (v : X → ℝ),
        ν ≠ 1 ∧ v ≠ 0 ∧ P.mulVec v = ν • v ∧ b = |ν|}
    (1 - δ)
def mnrsRun {X : Type*} [DecidableEq X]
    (M : Finset X) (a : ℕ) : List X → Option X × ℕ × ℕ
  | [] => (none, 0, 0)
  | x :: xs =>
      if x ∈ M then (some x, 0, 1)
      else
        let z := mnrsRun M a xs;
        (z.1, a + z.2.1, 1 + z.2.2)
def mnrsRunOnPath {X : Type*} [DecidableEq X]
    (M : Finset X) (a r : ℕ) (path : Fin (r + 1) → X) :
    Option X × ℕ × ℕ :=
  mnrsRun M a (List.ofFn (fun i : Fin r => path i.castSucc))
noncomputable def mnrsPathWeight {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (a r : ℕ) (path : Fin (r + 1) → X) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ *
    ∏ i : Fin r, (P ^ a) (path i.castSucc) (path i.succ)
noncomputable def mnrsOutputMass {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (M : Finset X) (a r : ℕ) (o : Option X) : ℝ :=
  ∑ path : Fin (r + 1) → X,
    if (mnrsRunOnPath M a r path).1 = o
    then mnrsPathWeight P a r path else 0
def mnrsSearchGuarantee {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (M : Finset X) (a r : ℕ) (p : ℝ) : Prop :=
  (∀ o : Option X, 0 ≤ mnrsOutputMass P M a r o) ∧
  (∑ o : Option X, mnrsOutputMass P M a r o) = 1 ∧
  (∀ x : X, x ∉ M → mnrsOutputMass P M a r (some x) = 0) ∧
  (M = ∅ → mnrsOutputMass P M a r none = 1) ∧
  (M.Nonempty → p ≤ ∑ x ∈ M, mnrsOutputMass P M a r (some x))
noncomputable def mnrsTraceCost {X : Type*} [DecidableEq X]
    (M : Finset X) (a r : ℕ) (path : Fin (r + 1) → X)
    (S U C : ℝ) : ℝ :=
  let z := mnrsRunOnPath M a r path;
  S + (z.2.1 : ℝ) * U + (z.2.2 : ℝ) * C

end Qatlib.Concepts.WalkSearch.MnrsAmplify
