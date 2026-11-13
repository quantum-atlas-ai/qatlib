/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup

/-!
# Finite encodings and query bounds for hidden subgroups

`BlackBoxEncoding` supplies a finite token space surjecting onto a group. `IsHSOracle` describes
Boolean functions constant exactly on hidden-subgroup cosets, while `HSPSolver` returns finite
generating sets. Query bounds are measured by the size of a fixed determining set of tokens and
are polynomial in token cardinality. See [InuiLeGall2007] for the mathematical setting.

## Main statements

* `HSPSolver.HasQueryBound`: requires output to depend on a determining set of at most `q`
  tokens.
* `HasPolynomialQueryHSPSolver`: requires a polynomial token-cardinality bound for every finite
  encoding.

## References

* [Inui and Le Gall, 2007][InuiLeGall2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Model

/-- A finite token type with decidable equality and a surjective encoding into `G`. -/
structure BlackBoxEncoding (G : Type*) where

  Token : Type

  fintype : Fintype Token

  decEq : DecidableEq Token

  enc : Token → G

  surj : Function.Surjective enc

/-- The cardinality of the finite token type of an encoding. -/
def BlackBoxEncoding.size {G : Type*} (e : BlackBoxEncoding G) : ℕ :=
  @Fintype.card e.Token e.fintype

/-- Two tokens have the same Boolean oracle value exactly when their encoded elements differ by
right multiplication by an element of `H`. -/
def IsHSOracle {G : Type*} [Group G] (e : BlackBoxEncoding G) (H : Subgroup G)
    (f : e.Token → Bool) : Prop :=
  ∀ a b : e.Token, (f a = f b ↔ ∃ h : H, e.enc a * h = e.enc b)

/-- An oracle-to-finite-set map whose output generates the hidden subgroup whenever the oracle
satisfies `IsHSOracle`. -/
structure HSPSolver {G : Type*} [Group G] (e : BlackBoxEncoding G) where

  output : (e.Token → Bool) → Finset G

  correct : ∀ (H : Subgroup G) (f : e.Token → Bool),
    IsHSOracle e H f → Subgroup.closure (↑(output f) : Set G) = H

/-- The solver output is determined by oracle values on some fixed set of at most `q` tokens. -/
def HSPSolver.HasQueryBound {G : Type*} [Group G] {e : BlackBoxEncoding G}
    (s : HSPSolver e) (q : ℕ) : Prop :=
  ∃ S : Finset e.Token, S.card ≤ q ∧
    ∀ (f g : e.Token → Bool), (∀ x ∈ S, f x = g x) → s.output f = s.output g

/-- The encoding possesses a correct hidden-subgroup solver with a query bound given by a
natural power of its token cardinality. -/
def HasPolyQuerySolverFor {G : Type*} [Group G] (e : BlackBoxEncoding G) : Prop :=
  ∃ (s : HSPSolver e) (c : ℕ), s.HasQueryBound (e.size ^ c)

/-- Every finite encoding of `G` possesses a solver satisfying `HasPolyQuerySolverFor`. -/
def HasPolynomialQueryHSPSolver (G : Type*) [Group G] : Prop :=
  ∀ e : BlackBoxEncoding G, HasPolyQuerySolverFor e

end Qatlib.Papers.SemiDirectHSP04.MainResults.Model
