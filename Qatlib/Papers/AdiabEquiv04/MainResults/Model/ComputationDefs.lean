/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.HistoryConstruction
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Classical
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def innerVec (a b : Vector ι) : ℂ := (star a) ⬝ᵥ b

def PhaseClose (ψ φ : Vector ι) (ε : ℝ) : Prop :=
  ∃ c : ℂ, Complex.normSq c = 1 ∧ l2Dist (c • ψ) φ ≤ ε

def StateClose (ρ : Matrix ι ι ℂ) (φ : Vector ι) (ε : ℝ) : Prop :=
  ∃ h : (ρ - ketDensity φ).IsHermitian, traceDistance ρ (ketDensity φ) h ≤ ε

def hamNorm (H : Hamiltonian ι) : ℝ := ∑ i : Fin (Fintype.card ι), |eigvals H i|

structure AdiabaticComputation (ι : Type) [Fintype ι] [DecidableEq ι] where

  Hinit : Hamiltonian ι

  Hfinal : Hamiltonian ι

  output : Matrix ι ι ℂ

  output_density : IsDensityMatrix output

  locality : ℕ

def AdiabaticRunsTo (ε : ℝ) (A : AdiabaticComputation ι) (ψ : Vector ι) : Prop :=
  IsGroundVector A.Hfinal ψ ∧ StateClose A.output ψ ε

def HasTermDescription (bound : ℕ) (H : Matrix ι ι ℂ) : Prop :=
  ∃ terms : List (Matrix ι ι ℂ), H = terms.sum ∧ terms.length ≤ bound

def HasPolyTermDescription (H : Hamiltonian ι) : Prop :=
  ∃ C d : ℕ, HasTermDescription (C * (Fintype.card ι + 1) ^ d) H.mat

def RowPolynomialSparse (H : Matrix ι ι ℂ) : Prop :=
  ∃ C d : ℕ, ∀ i : ι, (Finset.univ.filter (fun j => H i j ≠ 0)).card ≤
    C * (Fintype.card ι + 1) ^ d

def ExplicitSparseFamily (H : ℝ → Hamiltonian ι) : Prop :=
  (∀ s : ℝ, RowPolynomialSparse (H s).mat) ∧
    ∃ d : ℕ, ∀ s : ℝ, HasTermDescription ((Fintype.card ι + 1) ^ d) (H s).mat

abbrev Particle6 := Fin 6

abbrev GridPos (n R : ℕ) := Fin n × Fin (R + 1)

abbrev GridBasis (n R : ℕ) := GridPos n R → Particle6

def Neighbor {n R : ℕ} (a b : GridPos n R) : Prop :=
  (a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
  (a.2 = b.2 ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

def SupportedOn {n R : ℕ} (t : Finset (GridPos n R))
    (A : Matrix (GridBasis n R) (GridBasis n R) ℂ) : Prop :=
  ∀ x y : GridBasis n R, (∃ a : GridPos n R, a ∉ t ∧ x a ≠ y a) → A x y = 0

def IsTwoLocalNeighborTerm {n R : ℕ} (t : Finset (GridPos n R))
    (A : Matrix (GridBasis n R) (GridBasis n R) ℂ) : Prop :=
  t.card ≤ 2 ∧ (∀ a ∈ t, ∀ b ∈ t, a ≠ b → Neighbor a b) ∧ SupportedOn t A

def IsTwoLocalNearestNeighbor {n R : ℕ}
    (H : Matrix (GridBasis n R) (GridBasis n R) ℂ) : Prop :=
  ∃ terms : List (Finset (GridPos n R) × Matrix (GridBasis n R) (GridBasis n R) ℂ),
    (∀ p ∈ terms, IsTwoLocalNeighborTerm p.1 p.2) ∧ H = (terms.map Prod.snd).sum

def AcceptProb (m : ℕ) (ρ : Matrix (CompBasis (m + 1)) (CompBasis (m + 1)) ℂ) : ℝ :=
  ∑ x : CompBasis (m + 1), if x ⟨0, Nat.succ_pos m⟩ = 1 then (ρ x x).re else 0

def CircuitAcceptProb (m Lg : ℕ) (gates : GateSeq (m + 1)) : ℝ :=
  AcceptProb m (ketDensity (prefixU gates Lg *ᵥ zeroBasis (m + 1)))

def CircuitDecider (Lang : Set (List Bool)) : Prop :=
  ∃ C d : ℕ, ∀ x : List Bool,
    ∃ (m Lg : ℕ) (_hm : m + 1 ≤ C * (x.length + 1) ^ d)
      (gates : GateSeq (m + 1)),
      Lg ≤ C * (x.length + 1) ^ d ∧
      (x ∈ Lang → 2 / 3 ≤ CircuitAcceptProb m Lg gates) ∧
      (x ∉ Lang → CircuitAcceptProb m Lg gates ≤ 1 / 3)

def AdiabaticDecider (k : ℕ) (Lang : Set (List Bool)) : Prop :=
  ∃ C d : ℕ, ∀ x : List Bool,
    ∃ (m : ℕ) (A : AdiabaticComputation (CompBasis (m + 1))) (T : ℝ),
      A.locality = k ∧ 0 < T ∧
      m + 1 ≤ C * (x.length + 1) ^ d ∧
      T ≤ C * (x.length + 1) ^ d ∧
      (x ∈ Lang → 2 / 3 ≤ AcceptProb m A.output) ∧
      (x ∉ Lang → AcceptProb m A.output ≤ 1 / 3)

def SparseAdiabaticDecider (Lang : Set (List Bool)) : Prop :=
  ∃ C d : ℕ, ∀ x : List Bool,
    ∃ (m : ℕ) (H : ℝ → Hamiltonian (CompBasis (m + 1))) (T : ℝ) (ψ : Vector (CompBasis (m + 1))),
      ExplicitSparseFamily H ∧ 0 < T ∧
      m + 1 ≤ C * (x.length + 1) ^ d ∧
      T ≤ C * (x.length + 1) ^ d ∧
      IsGroundVector (H 1) ψ ∧
      (x ∈ Lang → 2 / 3 ≤ AcceptProb m (ketDensity ψ)) ∧
      (x ∉ Lang → AcceptProb m (ketDensity ψ) ≤ 1 / 3)

def AdiabaticPolyClass (k : ℕ) : Set (Set (List Bool)) :=
  {Lang | AdiabaticDecider k Lang}

def SparseAdiabaticPolyClass : Set (Set (List Bool)) :=
  {Lang | SparseAdiabaticDecider Lang}

def StandardCircuitPolyClass : Set (Set (List Bool)) :=
  {Lang | CircuitDecider Lang}

def TwoLocalGridSimulatesCircuits : Prop :=
  ∀ (n L : ℕ), 2 ≤ L → ∀ (gates : GateSeq n) (ε : ℝ), 0 < ε →
    ∃ (R : ℕ) (A : AdiabaticComputation (GridBasis n R)) (T : ℝ),
      A.locality = 2 ∧ 0 < T ∧
      IsTwoLocalNearestNeighbor A.Hinit.mat ∧
      IsTwoLocalNearestNeighbor A.Hfinal.mat ∧
      (∃ C : ℝ, 0 < C ∧ ∃ d e : ℕ,
        T ≤ C * ((L : ℝ) + 1) ^ d * (1 / ε) ^ e) ∧
      (∃ ψ : Vector (GridBasis n R), AdiabaticRunsTo ε A ψ) ∧
      (∃ (out : Matrix (CompBasis n) (CompBasis n) ℂ),
        IsDensityMatrix out ∧ StateClose out (prefixU gates L *ᵥ zeroBasis n) ε) ∧
      HasPolyTermDescription A.Hinit ∧ HasPolyTermDescription A.Hfinal

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
