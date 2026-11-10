/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Automorphism

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

def IsAutomorphism {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (π : (Fin n → Fin q) → (Fin n → Fin q)) : Prop :=
  ∀ x y, f x ≠ f y → f (π x) ≠ f (π y)

def IsAutomorphismGroup {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))) : Prop :=
  (∀ π ∈ G, Function.Bijective π ∧ IsAutomorphism f π) ∧
  (id ∈ G) ∧
  (∀ π ∈ G, ∀ σ ∈ G, (π ∘ σ) ∈ G) ∧
  (∀ π ∈ G, ∃ ρ ∈ G, ∀ x, ρ (π x) = x)

def IsFTransitive {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))) : Prop :=
  ∀ x y, f x = f y → ∃ π ∈ G, π x = y

def SendsIndexTo {n q : ℕ} (π : (Fin n → Fin q) → (Fin n → Fin q))
    (i j : Fin n) : Prop :=
  ∀ x y, (x i = y i ↔ π x j = π y j)

def IsIndexTransitive {n q : ℕ}
    (G : Finset ((Fin n → Fin q) → (Fin n → Fin q))) : Prop :=
  ∀ i j : Fin n, ∃ π ∈ G, SendsIndexTo π i j

theorem isAutomorphism_id {n q : ℕ} (f : (Fin n → Fin q) → Bool) :
    IsAutomorphism f (fun x => x) := by
  intro x y h
  exact h

theorem isAutomorphism_comp {n q : ℕ} (f : (Fin n → Fin q) → Bool)
    (π σ : (Fin n → Fin q) → (Fin n → Fin q))
    (hπ : IsAutomorphism f π) (hσ : IsAutomorphism f σ) :
    IsAutomorphism f (π ∘ σ) := by
  intro x y h
  exact hπ (σ x) (σ y) (hσ x y h)

theorem sendsIndexTo_id {n q : ℕ} (i : Fin n) :
    SendsIndexTo (n := n) (q := q) (fun x => x) i i := by
  intro x y
  rfl

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
