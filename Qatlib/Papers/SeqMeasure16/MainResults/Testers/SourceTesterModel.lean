/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Shared tester interfaces for Harrow--Lin--Montanaro (arXiv:1607.03236v3)

This file fixes the vocabulary used by the paper-layer statements for
*Sequential measurements, disturbance and property testing*.

The paper studies four kinds of procedures:

* `ε`-testers for a property of an unknown state (Section 1.2, Theorem 4);
* `ε`-testers for a property of an unknown unitary (Corollary 5);
* `ε`-testers for `S`-isomorphism of unitaries (Theorem 6);
* `ε`-testers for `G`-isomorphism of functions (Section 1.1, Theorem 2).

The legacy structures below are semantic specifications: their real-valued
acceptance maps satisfy completeness and soundness, but their budgets are
independent labels. They do not require probability ranges, measurements or
query circuits, and their existence alone is not a resource bound.
`TesterModel` supplies external program semantics and charged call traces.
The four `Realizes...` predicates require one program to match both acceptance
and the declared budget. Physical validity and complete accounting of calls
are assumptions on the supplied model. No such physical model or tester
implementation is constructed in this file; the other probability inequalities
in this paper do not provide these realization certificates.

Distances follow the paper:
* pure-state trace distance, equation (1), page 5:
  `‖|ψ⟩⟨ψ| - |φ⟩⟨φ|‖_tr = sqrt (1 - |⟨ψ|φ⟩|²)`;
* unitary Hilbert--Schmidt distance, page 5:
  `D(U,V) = sqrt (1 - |⟨U,V⟩|²)`, `⟨U,V⟩ = tr(U†V)/d`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SeqMeasure16.MainResults.Testers

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

variable {D : ℕ}

/-- Pure-state trace distance of equation (1) (arXiv:1607.03236v3, page 5):
`‖|ψ⟩⟨ψ| − |φ⟩⟨φ|‖_tr = sqrt (1 − |⟨ψ|φ⟩|²)`. -/
noncomputable def pureTraceDistance {I : Type*} [Fintype I] (ψ φ : QState I) : ℝ :=
  Real.sqrt (1 - ‖star ψ ⬝ᵥ φ‖ ^ 2)

/-- Born probability `⟨ψ|Λ|ψ⟩` of a two-outcome measurement element `Λ`. -/
noncomputable def bornExpectation {I : Type*} [Fintype I]
    (Λ : Matrix I I ℂ) (ψ : QState I) : ℝ :=
  (star ψ ⬝ᵥ (Λ *ᵥ ψ)).re

/-- Unitary Hilbert--Schmidt overlap `⟨U,V⟩ = tr(U†V)/d` (page 5). -/
noncomputable def unitaryOverlap {d : ℕ}
    (U V : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  Matrix.trace (Uᴴ * V) / (d : ℂ)

/-- Unitary distance `D(U,V) = sqrt (1 − |⟨U,V⟩|²)` (page 5). -/
noncomputable def unitaryDistance {d : ℕ}
    (U V : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.sqrt (1 - ‖unitaryOverlap U V‖ ^ 2)

/-- A matrix is unitary when `U†U = UU† = I`. -/
def IsUnitary {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- Semantic state-property specification (Theorem 4). Its budget and acceptance
map require a separate `RealizesStateTester` certificate in a supplied model. -/
structure StatePropertyTester (d : ℕ) (P : Finset (QState (Fin d))) (ε : ℝ) where
  /-- Declared copy budget; no copy consumption is certified by this field. -/
  copies : ℕ
  /-- Acceptance probability of the tester on a given input state. -/
  acceptProb : QState (Fin d) → ℝ
  /-- Every normalized member of `P` is accepted with probability at least `2/3`. -/
  accepts_member : ∀ ψ, ψ ∈ P → Normalized ψ → (2 : ℝ) / 3 ≤ acceptProb ψ
  /-- Every normalized state at trace distance at least `ε` from all of `P`
  is accepted with probability at most `1/3`. -/
  rejects_far : ∀ ψ, Normalized ψ →
    (∀ φ, φ ∈ P → Normalized φ → ε ≤ pureTraceDistance ψ φ) → acceptProb ψ ≤ 1 / 3

/-- Semantic unitary-property specification (Corollary 5); physical realization
and resource consumption are separate obligations. -/
structure UnitaryPropertyTester (d : ℕ) (P : Finset (Matrix (Fin d) (Fin d) ℂ))
    (ε : ℝ) where
  /-- Declared unitary-use budget, requiring a realization certificate. -/
  uses : ℕ
  /-- Acceptance probability of the tester on a given input unitary. -/
  acceptProb : Matrix (Fin d) (Fin d) ℂ → ℝ
  /-- Every unitary member of `P` is accepted with probability at least `2/3`. -/
  accepts_member : ∀ U, U ∈ P → IsUnitary U →
    (2 : ℝ) / 3 ≤ acceptProb U
  /-- Every unitary at distance at least `ε` from all of `P` is accepted with
  probability at most `1/3`. -/
  rejects_far : ∀ U, IsUnitary U →
    (∀ V, V ∈ P → ε ≤ unitaryDistance U V) → acceptProb U ≤ 1 / 3

/-- Semantic specification for unitary `S`-isomorphism (page 6, Theorem 6): the
property is `∃ U ∈ S, U V U† = W`, and the far case is
`∀ U ∈ S, D(U V U†, W) ≥ ε`. -/
structure UnitaryIsomorphismTester (d : ℕ)
    (S : Finset (Matrix (Fin d) (Fin d) ℂ)) (ε : ℝ) where
  /-- Declared total use budget for `V` and `W`, requiring realization. -/
  uses : ℕ
  /-- Acceptance probability of the tester on input `(V, W)`. -/
  acceptProb : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ → ℝ
  /-- If some `U ∈ S` conjugates `V` into `W`, accept with probability at least `2/3`. -/
  accepts_isomorphic : ∀ V W, IsUnitary V → IsUnitary W →
    (∃ U, U ∈ S ∧ U * V * Uᴴ = W) → (2 : ℝ) / 3 ≤ acceptProb V W
  /-- If every `U ∈ S` is `ε`-far from conjugating `V` into `W`, reject with
  probability at least `2/3`. -/
  rejects_far : ∀ V W, IsUnitary V → IsUnitary W →
    (∀ U, U ∈ S → ε ≤ unitaryDistance (U * V * Uᴴ) W) → acceptProb V W ≤ 1 / 3

/-- Semantic specification for `G`-isomorphism of functions `f, g : X → Y`
(Section 1.1, page 3; Theorem 2).  `G` is an arbitrary finite set of
permutations of `X` (the paper stresses that `G` need not be a group).  The
`queries` field is only a label until `RealizesGTester` is supplied. -/
structure GIsomorphismTester (X Y : Type*) [Fintype X] [Fintype Y] [DecidableEq Y]
    (G : Finset (Equiv.Perm X)) (ε : ℝ) where
  /-- Declared query budget for `f` and `g`, requiring realization. -/
  queries : ℕ
  /-- Acceptance probability of the tester on input `(f, g)`. -/
  acceptProb : (X → Y) → (X → Y) → ℝ
  /-- If `g = f ∘ σ` for some `σ ∈ G`, accept with probability at least `2/3`. -/
  accepts_isomorphic : ∀ f g, (∃ σ, σ ∈ G ∧ ∀ x, g x = f (σ x)) →
    (2 : ℝ) / 3 ≤ acceptProb f g
  /-- If for every `σ ∈ G` the functions differ on at least an `ε` fraction of
  `X`, reject with probability at least `2/3`. -/
  rejects_far : ∀ f g, (∀ σ, σ ∈ G →
      ε * (Fintype.card X : ℝ) ≤
        (((Finset.univ : Finset X).filter (fun x => g x ≠ f (σ x))).card : ℝ)) →
    acceptProb f g ≤ 1 / 3

/-- External tester semantics. The model provider must justify that `accept`
is the program's physical acceptance probability and `calls` lists all consumed
copies or oracle uses. This interface itself supplies no such justification. -/
structure TesterModel (Input : Type*) where
  Program : Type
  Call : Type
  calls : Program → List Call
  accept : Program → Input → ℝ

/-- Matching output semantics and trace length in an explicitly supplied model. -/
def TesterModel.Realizes {Input : Type*} (M : TesterModel Input)
    (budget : ℕ) (accept : Input → ℝ) : Prop :=
  ∃ p : M.Program, (M.calls p).length = budget ∧ ∀ x, M.accept p x = accept x

/-- Transfer any semantic correctness predicate to a program, conditional on
its realization certificate. No program is synthesized by this theorem. -/
theorem TesterModel.correct_of_realizes {Input : Type*} {M : TesterModel Input}
    {budget : ℕ} {accept : Input → ℝ} (h : M.Realizes budget accept)
    (Correct : (Input → ℝ) → Prop) (hCorrect : Correct accept) :
    ∃ p : M.Program, (M.calls p).length = budget ∧ Correct (M.accept p) := by
  obtain ⟨p, hc, hp⟩ := h
  have heq : M.accept p = accept := funext hp
  exact ⟨p, hc, heq.symm ▸ hCorrect⟩

/-- Conditional realization with one trace entry per input-state copy. -/
def RealizesStateTester {d : ℕ} {P : Finset (QState (Fin d))} {ε : ℝ}
    (T : StatePropertyTester d P ε) (M : TesterModel (QState (Fin d))) : Prop :=
  M.Realizes T.copies T.acceptProb

/-- Conditional realization with one trace entry per unitary use. -/
def RealizesUnitaryTester {d : ℕ} {P : Finset (Matrix (Fin d) (Fin d) ℂ)} {ε : ℝ}
    (T : UnitaryPropertyTester d P ε)
    (M : TesterModel (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  M.Realizes T.uses T.acceptProb

/-- Conditional realization counting uses of both unknown unitaries. -/
def RealizesUnitaryIsomorphismTester {d : ℕ}
    {S : Finset (Matrix (Fin d) (Fin d) ℂ)} {ε : ℝ}
    (T : UnitaryIsomorphismTester d S ε)
    (M : TesterModel (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  M.Realizes T.uses (fun x => T.acceptProb x.1 x.2)

/-- Conditional realization counting queries to both functions. -/
def RealizesGTester {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {G : Finset (Equiv.Perm X)} {ε : ℝ} (T : GIsomorphismTester X Y G ε)
    (M : TesterModel ((X → Y) × (X → Y))) : Prop :=
  M.Realizes T.queries (fun x => T.acceptProb x.1 x.2)

end Qatlib.Papers.SeqMeasure16.MainResults.Testers
