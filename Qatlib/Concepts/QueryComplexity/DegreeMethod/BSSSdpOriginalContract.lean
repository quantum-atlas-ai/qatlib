/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.BSSSdp

/-!
# Original symmetry contracts for query SDP families

This module names two proposed symmetry statements for the query matrix feasibility predicate
`bssFamilyFeasible`. `BssConjugateOriginalContract` specifies simultaneous reindexing of a
feasible family, while `BssInvariantOriginalContract` specifies existence of an invariant family
under a finite group. General background on semidefinite formulations is provided by
[Watrous2018].

These declarations define propositions for separate analysis; this module does not establish
either proposition.

## Main statements

* `BssConjugateOriginalContract`: the proposed feasibility preservation statement under
  simultaneous symmetry reindexing.
* `BssInvariantOriginalContract`: the proposed existence statement for an invariant feasible
  family.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

set_option autoImplicit false
open scoped ComplexOrder
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The proposition that simultaneously reindexing inputs, query indices, and output labels by a
`Bss` symmetry preserves feasibility of every matrix family. -/
def BssConjugateOriginalContract : Prop :=
  ∀ {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {m : ℕ}
    (bit : X → Fin m → Bool) (f : X → Y) (k : ℕ) (ε : ℝ)
    (π : Equiv.Perm X) (ρ : Equiv.Perm (Fin m)) (σ : Equiv.Perm Y),
    IsBssSymmetry bit f π ρ σ →
    ∀ (M : Fin m → ℕ → Matrix X X ℂ) (N : ℕ → Matrix X X ℂ) (Γ : Y → Matrix X X ℂ),
    bssFamilyFeasible bit f k ε M N Γ →
    bssFamilyFeasible bit f k ε
      (fun i t => Matrix.of fun x x' => M (ρ i) t (π x) (π x'))
      (fun t => Matrix.of fun x x' => N t (π x) (π x'))
      (fun y => Matrix.of fun x x' => Γ (σ y) (π x) (π x'))

/-- The proposition that every feasible query SDP with a finite symmetry group possesses a
feasible matrix family invariant under the specified input, query, and output actions. -/
def BssInvariantOriginalContract : Prop :=
  ∀ {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {m : ℕ}
    (bit : X → Fin m → Bool) (f : X → Y) (k : ℕ) (ε : ℝ)
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (π : G →* Equiv.Perm X) (ρ : G →* Equiv.Perm (Fin m)) (σ : G →* Equiv.Perm Y),
    (∀ g,IsBssSymmetry bit f (π g) (ρ g) (σ g)) → bssFeasible bit f k ε →
    ∃ M : Fin m → ℕ → Matrix X X ℂ,∃ N : ℕ → Matrix X X ℂ,∃ Γ : Y → Matrix X X ℂ,
      bssFamilyFeasible bit f k ε M N Γ ∧
      (∀ g i t x x',M (ρ g i) t (π g x) (π g x')=M i t x x') ∧
      (∀ g t x x',N t (π g x) (π g x')=N t x x') ∧
      (∀ g y x x',Γ (σ g y) (π g x) (π g x')=Γ y x x')
end Qatlib.Concepts.QueryComplexity.DegreeMethod
