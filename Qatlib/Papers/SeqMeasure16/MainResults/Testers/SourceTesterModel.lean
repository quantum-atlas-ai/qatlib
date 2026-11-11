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

In each case a tester is a procedure which (i) has a fixed resource budget
(queries to the unknown function, or copies/uses of the unknown state or
unitary), and (ii) accepts with probability at least `2/3` on inputs having
the property and at most `1/3` on inputs promised to be `ε`-far from it.  The
structures below record exactly these two attributes: the acceptance
probability is the actual output probability of the procedure on the input,
and the budget field is the number of queries/copies/uses it consumes.  The
structures are interfaces, not executable circuits; the paper's algorithms
are asserted to exist with the stated budgets.

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

/-- A quantum `ε`-tester for a finite set `P` of pure states (Section 1.2,
page 5; Theorem 4).  `copies` is the number of copies of the input state used;
`acceptProb ψ` is the acceptance probability of the procedure on input `ψ`.
The two correctness fields are the paper's completeness and soundness
requirements (success probability `2/3`, trace distance at least `ε` from `P`). -/
structure StatePropertyTester (d : ℕ) (P : Finset (QState (Fin d))) (ε : ℝ) where
  /-- Number of copies of the unknown state consumed by the tester. -/
  copies : ℕ
  /-- Acceptance probability of the tester on a given input state. -/
  acceptProb : QState (Fin d) → ℝ
  /-- Every normalized member of `P` is accepted with probability at least `2/3`. -/
  accepts_member : ∀ ψ, ψ ∈ P → Normalized ψ → (2 : ℝ) / 3 ≤ acceptProb ψ
  /-- Every normalized state at trace distance at least `ε` from all of `P`
  is accepted with probability at most `1/3`. -/
  rejects_far : ∀ ψ, Normalized ψ →
    (∀ φ, φ ∈ P → Normalized φ → ε ≤ pureTraceDistance ψ φ) → acceptProb ψ ≤ 1 / 3

/-- A quantum `ε`-tester for a finite set `P` of unitary operators
(Corollary 5, page 13).  `uses` is the number of uses of the input unitary. -/
structure UnitaryPropertyTester (d : ℕ) (P : Finset (Matrix (Fin d) (Fin d) ℂ))
    (ε : ℝ) where
  /-- Number of uses of the unknown unitary operator. -/
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

/-- A quantum `ε`-tester for unitary `S`-isomorphism (page 6, Theorem 6): the
property is `∃ U ∈ S, U V U† = W`, and the far case is
`∀ U ∈ S, D(U V U†, W) ≥ ε`. -/
structure UnitaryIsomorphismTester (d : ℕ)
    (S : Finset (Matrix (Fin d) (Fin d) ℂ)) (ε : ℝ) where
  /-- Number of uses of the unknown unitaries `V` and `W`. -/
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

/-- A quantum `ε`-tester for `G`-isomorphism of functions `f, g : X → Y`
(Section 1.1, page 3; Theorem 2).  `G` is an arbitrary finite set of
permutations of `X` (the paper stresses that `G` need not be a group).  The
`queries` field counts queries to `f` and `g`. -/
structure GIsomorphismTester (X Y : Type*) [Fintype X] [Fintype Y] [DecidableEq Y]
    (G : Finset (Equiv.Perm X)) (ε : ℝ) where
  /-- Number of queries made to `f` and `g`. -/
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

end Qatlib.Papers.SeqMeasure16.MainResults.Testers
