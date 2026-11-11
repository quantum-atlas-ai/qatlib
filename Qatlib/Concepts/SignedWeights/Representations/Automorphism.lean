/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs

/-!
# Automorphisms of Adversary Instances

This module defines input symmetries for Boolean functions on finite words. `IsAutomorphism`
preserves pairs with different function values, `IsFTransitive` expresses transitivity within
each output fiber, and `IsIndexTransitive` expresses transitivity of coordinate equality tests
through `SendsIndexTo`. These predicates organize the symmetry statements associated with the
negative-weight adversary method in [HoyerLeeSpalek2007].

`theorem9AutomorphismSpec` and `corollary10IndexTransitiveSpec` are proposition specifications:
they formulate the existence of optimal symmetric adversary matrices, with additional
eigenvector or equal-filter-norm conclusions under the corresponding transitivity assumptions.

## Main statements

- `isAutomorphism_id` and `isAutomorphism_comp` establish identity and composition closure.
- `sendsIndexTo_id` verifies the identity coordinate action.
* `theorem9AutomorphismSpec` specifies an invariant optimal witness and an output-fiber-constant
  eigenvector.
* `corollary10IndexTransitiveSpec` specifies an optimal witness with equal coordinate filter
  norms.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Automorphism

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- An input map is an automorphism of `f` when it sends every pair with different outputs to
another pair with different outputs. -/
def IsAutomorphism {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (π : (Fin n → Fin q) → (Fin n → Fin q)) : Prop :=
  ∀ x y, f x ≠ f y → f (π x) ≠ f (π y)

/-- Requires every member of the finite family `G` to be a bijective automorphism of `f`,
together with the identity, closure under composition, and a left inverse in `G` for every
member. -/
def IsAutomorphismGroup {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))) : Prop :=
  (∀ π ∈ G, Function.Bijective π ∧ IsAutomorphism f π) ∧
  (id ∈ G) ∧
  (∀ π ∈ G, ∀ σ ∈ G, (π ∘ σ) ∈ G) ∧
  (∀ π ∈ G, ∃ ρ ∈ G, ∀ x, ρ (π x) = x)

/-- Requires `G` to send any input to any other input in the same output fiber of `f`. -/
def IsFTransitive {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))) : Prop :=
  ∀ x y, f x = f y → ∃ π ∈ G, π x = y

/-- Says that equality of inputs at coordinate `i` is equivalent to equality of their images
under `π` at coordinate `j`. -/
def SendsIndexTo {n q : ℕ} (π : (Fin n → Fin q) → (Fin n → Fin q))
    (i j : Fin n) : Prop :=
  ∀ x y, (x i = y i ↔ π x j = π y j)

/-- Requires every ordered pair of coordinates to be related by a map in `G` satisfying
`SendsIndexTo`. -/
def IsIndexTransitive {n q : ℕ}
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))) : Prop :=
  ∀ i j : Fin n, ∃ π ∈ G, SendsIndexTo π i j

/-- The identity input map preserves every pair of distinct outputs of `f`. -/
theorem isAutomorphism_id {n q : ℕ} (f : (Fin n → Fin q) → Bool) :
    IsAutomorphism f (fun x => x) := by
  intro x y h
  exact h

/-- The composition of two automorphisms of `f` is again an automorphism of `f`. -/
theorem isAutomorphism_comp {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (π σ : (Fin n → Fin q) → (Fin n → Fin q))
    (hπ : IsAutomorphism f π) (hσ : IsAutomorphism f σ) :
    IsAutomorphism f (π ∘ σ) := by
  intro x y h
  exact hπ (σ x) (σ y) (hσ x y h)

/-- The identity input map sends each coordinate equality test to itself. -/
theorem sendsIndexTo_id {n q : ℕ} (i : Fin n) :
    SendsIndexTo (n := n) (q := q) (fun x => x) i i := by
  intro x y
  rfl

/-- Defines the proposition asserting the existence of a nonzero optimal Hermitian adversary
witness invariant under an automorphism group. It additionally asks for a nonzero
eigenvector constant on output fibers when the group is `IsFTransitive`, following Theorem 9
of [HoyerLeeSpalek2007]. -/
def theorem9AutomorphismSpec : Prop :=
  ∀ {n q : ℕ}
    (f : (Fin n → Fin q) → Bool)
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))),
    IsAutomorphismGroup f G →
    ∃ Γ : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ,
      Γ.IsHermitian ∧ (∀ x y, f x = f y → Γ x y = 0) ∧ Γ ≠ 0 ∧
      advPmWitnessValue (fun x : Fin n → Fin q => x) Γ =
        advPmValue (fun x : Fin n → Fin q => x) f ∧
      (∀ π ∈ G, ∀ x y, Γ x y = Γ (π x) (π y)) ∧
      (IsFTransitive f G →
        ∃ β : QState (Fin n → Fin q), β ≠ 0 ∧
          Γ *ᵥ β = ((‖Γ‖ : ℝ) : ℂ) • β ∧
          ∀ x y, f x = f y → β x = β y)

/-- Defines the proposition asserting the existence of a nonzero optimal Hermitian adversary
witness with equal coordinate filter norms for an index-transitive automorphism group,
following Corollary 10 of [HoyerLeeSpalek2007]. -/
def corollary10IndexTransitiveSpec : Prop :=
  ∀ {n q : ℕ}
    (f : (Fin n → Fin q) → Bool)
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))),
    IsAutomorphismGroup f G → IsIndexTransitive G →
    ∃ Γ : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ,
      Γ.IsHermitian ∧ (∀ x y, f x = f y → Γ x y = 0) ∧ Γ ≠ 0 ∧
      advPmWitnessValue (fun x : Fin n → Fin q => x) Γ =
        advPmValue (fun x : Fin n → Fin q => x) f ∧
      (∀ i j : Fin n,
        ‖genAdvFilter (fun x : Fin n → Fin q => x) Γ i‖ =
          ‖genAdvFilter (fun x : Fin n → Fin q => x) Γ j‖)

end

end Qatlib.Concepts.SignedWeights.Representations.Automorphism
