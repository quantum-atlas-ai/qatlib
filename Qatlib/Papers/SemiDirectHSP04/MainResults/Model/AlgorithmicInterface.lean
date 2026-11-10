/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Model

structure BlackBoxEncoding (G : Type*) where

  Token : Type

  fintype : Fintype Token

  decEq : DecidableEq Token

  enc : Token → G

  surj : Function.Surjective enc

def BlackBoxEncoding.size {G : Type*} (e : BlackBoxEncoding G) : ℕ :=
  @Fintype.card e.Token e.fintype

def IsHSOracle {G : Type*} [Group G] (e : BlackBoxEncoding G) (H : Subgroup G)
    (f : e.Token → Bool) : Prop :=
  ∀ a b : e.Token, (f a = f b ↔ ∃ h : H, e.enc a * h = e.enc b)

structure HSPSolver {G : Type*} [Group G] (e : BlackBoxEncoding G) where

  output : (e.Token → Bool) → Finset G

  correct : ∀ (H : Subgroup G) (f : e.Token → Bool),
    IsHSOracle e H f → Subgroup.closure (↑(output f) : Set G) = H

def HSPSolver.HasQueryBound {G : Type*} [Group G] {e : BlackBoxEncoding G}
    (s : HSPSolver e) (q : ℕ) : Prop :=
  ∃ S : Finset e.Token, S.card ≤ q ∧
    ∀ (f g : e.Token → Bool), (∀ x ∈ S, f x = g x) → s.output f = s.output g

def HasPolyQuerySolverFor {G : Type*} [Group G] (e : BlackBoxEncoding G) : Prop :=
  ∃ (s : HSPSolver e) (c : ℕ), s.HasQueryBound (e.size ^ c)

def HasPolynomialQueryHSPSolver (G : Type*) [Group G] : Prop :=
  ∀ e : BlackBoxEncoding G, HasPolyQuerySolverFor e

end Qatlib.Papers.SemiDirectHSP04.MainResults.Model
