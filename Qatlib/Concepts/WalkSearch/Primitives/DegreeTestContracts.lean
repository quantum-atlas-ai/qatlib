/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleSearchCorrectedDefinitions
set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

def fact2DegreeTestCorrected : Prop :=
  ∀ (n : ℕ) (δ : ℝ),64≤n→0<δ→δ<1→
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    0<c→∀ (G : UGraph n) (v : Fin n),
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v ∧ degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n) ∧
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10) ∧ ¬degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n)

def fact2DegreeTestAllPositive : Prop :=
  ∀ (n : ℕ) (δ : ℝ),0<n→0<δ→δ<1→
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    0<c→∀ (G : UGraph n) (v : Fin n),
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v ∧ degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n) ∧
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10) ∧ ¬degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n)

end Qatlib.Concepts.WalkSearch.Primitives
