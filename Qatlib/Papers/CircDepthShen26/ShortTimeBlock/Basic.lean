/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option backward.isDefEq.respectTransparency false

/-!
# Shared model for arXiv:2610.01839v2

Toward Optimal Circuit Depth for Geometrically Local Hamiltonian Simulation
(Shen, Wu, Yao, Yuan, Zhang; fixed arXiv:2610.01839v2, first submitted 2026-10-01).

This file fixes the paper-layer vocabulary used by every claim module:

* `IsHermitian`, `IsUnitary`, and the normalized evolution `evolutionH H t = e^{-i H t}`;
* a gate-level nearest-neighbor circuit model (`Gate`, `Layer`, `Circuit`) with
  parallel layers of disjoint-support gates, resource counters `depth` and
  `gateCount`, and bounded ancilla density;
* `Simulates`, the operator-norm statement of Eq. (3),
  `‖U ι₀ - ι₀ e^{-iHT}‖ ≤ ε`, where `ι₀` is the isometry initializing ancillary wires;
* `LocalTerm`/`localHamiltonian` together with the local-strength bound of Eq. (1).

The circuit model records gates as matrices together with the finite set of wires
on which they may act nontrivially (`fixes_off_support`).  A layer is a list of
gates with pairwise disjoint supports, so all gates in a layer are executed in
parallel; `Circuit.depth` is the number of layers and `Circuit.gateCount` the
total number of gates.  This is exactly the costing convention of Section 1.1:
"a depth layer consists of gates on disjoint qubits".

We do not formalize the paper's physical routing/refinement combinatorics here;
those constructions are stated per claim and left as explicit residuals where
they are not proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

/-! ## Hilbert-space level notions -/

section Core

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A Hamiltonian is a Hermitian matrix (Eq. (1) of the source). -/
def IsHermitian (H : Matrix I I ℂ) : Prop := Hᴴ = H

/-- A unitary matrix. -/
def IsUnitary (U : Matrix I I ℂ) : Prop := Uᴴ * U = 1

/-- The normalized unitary evolution `e^{-i H t}` (Eq. (2) of the source). -/
def evolutionH (H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • H)

/-- Evolution H zero: the paper model identity or bound. -/
@[simp] theorem evolutionH_zero (H : Matrix I I ℂ) : evolutionH H 0 = 1 := by
  simp [evolutionH]

end Core

/-! ## Gate-level nearest-neighbor circuit model -/

/-- A single gate: a unitary matrix together with a finite support on which it may
act nontrivially.  `fixes_off_support` is the locality certificate: vectors
vanishing on the support are fixed. -/
structure Gate (W : Type*) [Fintype W] [DecidableEq W] where
  matrix : Matrix W W ℂ
  unitary : IsUnitary matrix
  support : Finset W
  fixes_off_support : ∀ x : W → ℂ, (∀ i ∈ support, x i = 0) → matrix *ᵥ x = x

/-- Two finite sets are disjoint (formulated without a `DecidableEq` assumption). -/
def FinsetDisjoint {W : Type*} (s t : Finset W) : Prop := ∀ x ∈ s, x ∈ t → False

/-- A parallel layer: a list of gates whose supports are pairwise disjoint. -/
structure Layer (W : Type*) [Fintype W] [DecidableEq W] where
  gates : List (Gate W)
  pairwiseDisjoint : (gates.map (fun g => g.support)).Pairwise FinsetDisjoint

/-- Matrix of a layer (gates commute because their supports are disjoint; the
list product is the chosen serialization). -/
def Layer.matrix {W : Type*} [Fintype W] [DecidableEq W] (L : Layer W) :
    Matrix W W ℂ :=
  (L.gates.map (fun g => g.matrix)).prod

/-- A circuit: an ordered list of parallel layers. -/
structure Circuit (W : Type*) [Fintype W] [DecidableEq W] where
  layers : List (Layer W)

/-- Circuit depth: number of parallel layers. -/
def Circuit.depth {W : Type*} [Fintype W] [DecidableEq W] (C : Circuit W) : ℕ :=
  C.layers.length

/-- Circuit gate count: total number of gates over all layers. -/
def Circuit.gateCount {W : Type*} [Fintype W] [DecidableEq W] (C : Circuit W) : ℕ :=
  (C.layers.map (fun L => L.gates.length)).sum

/-- The unitary matrix realized by the circuit (execution order: first layer acts
first on the right). -/
def Circuit.matrix {W : Type*} [Fintype W] [DecidableEq W] (C : Circuit W) :
    Matrix W W ℂ :=
  (C.layers.map (fun L => L.matrix)).prod

/-- All gates connect equal or `adj`-neighboring wires: the nearest-neighbor
condition of the source, relative to the physical adjacency relation `adj`. -/
def Circuit.IsNearestNeighbor {W : Type*} [Fintype W] [DecidableEq W]
    (C : Circuit W) (adj : W → W → Prop) : Prop :=
  ∀ L ∈ C.layers, ∀ g ∈ L.gates, ∀ i ∈ g.support, ∀ j ∈ g.support,
    i = j ∨ adj i j

/-- Bounded ancilla density: at most `q` wires are assigned to any original site. -/
def BoundedAncillaDensity {W S : Type*} [Fintype W] [Fintype S] [DecidableEq S]
    (siteOf : W → S) (q : ℕ) : Prop :=
  ∀ s : S, (Finset.univ.filter (fun w : W => siteOf w = s)).card ≤ q

/-- Eq. (3) of the source: the circuit, started from ancillas initialized by the
isometry `ι`, approximates `e^{-i H T}` in operator norm to error `ε`. -/
def Simulates {J : Type*} [Fintype J] [DecidableEq J] {N : ℕ}
    (ι : Matrix (Fin N) J ℂ) (C : Circuit (Fin N))
    (H : Matrix J J ℂ) (T ε : ℝ) : Prop :=
  ‖C.matrix * ι - ι * evolutionH H T‖ ≤ ε

/-- The circuit implements a target operator `V` on the sector initialized by `ι`
(ancillas and auxiliary registers are returned to their initial state). -/
def Implements {J : Type*} [Fintype J] [DecidableEq J] {N : ℕ}
    (ι : Matrix (Fin N) J ℂ) (C : Circuit (Fin N)) (V : Matrix J J ℂ) : Prop :=
  C.matrix * ι = ι * V

/-! ## Local Hamiltonians (Eq. (1)) -/

/-- A local interaction term: a matrix with a declared finite support. -/
structure LocalTerm (W : Type*) [Fintype W] where
  support : Finset W
  matrix : Matrix W W ℂ

/-- The Hamiltonian obtained by summing the declared local terms. -/
def localHamiltonian {W : Type*} [Fintype W] (Λ : List (LocalTerm W)) : Matrix W W ℂ :=
  (Λ.map (fun t => t.matrix)).sum

/-- All interaction terms are Hermitian. -/
def LocalHermitian {W : Type*} [Fintype W] (Λ : List (LocalTerm W)) : Prop :=
  ∀ t ∈ Λ, t.matrixᴴ = t.matrix

/-- Local-strength bound of Eq. (1): for every site, the sum of the operator norms
of the terms containing that site is at most `J`. -/
def LocalStrengthLe {W : Type*} [Fintype W] [DecidableEq W]
    (Λ : List (LocalTerm W)) (J : ℝ) : Prop :=
  ∀ x : W, ((Λ.filter (fun t => x ∈ t.support)).map (fun t => ‖t.matrix‖)).sum ≤ J

/-- Range bound: every declared support has at most `R` sites. -/
def SupportBounded {W : Type*} [Fintype W] (Λ : List (LocalTerm W)) (R : ℕ) : Prop :=
  ∀ t ∈ Λ, t.support.card ≤ R

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
