/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ShortPathOpt18 — source model

Hastings, *A Short Path Quantum Algorithm for Exact Optimization*,
fixed arXiv:1802.10124 (Quantum 2, 78 (2018)).

This module fixes the paper-level objects shared by all claim files:

* the computational basis `Config N = Fin N → Bool`;
* the diagonal Hamiltonian `H_Z`, its energies and the density of states `W(E)`;
* the transverse-field operator `X = ∑ᵢ Xᵢ` and the short-path family
  `H_s = H_Z − s B (X/N)^K` (Eq. (6), p. 6);
* real amplitudes, expectation values, and the computational-basis entropy
  `S^(comp)` in bits (Eq. (49), p. 16);
* the degeneracy assumption of Section I A (p. 2).

Everything is finite-dimensional and real: a state is a real amplitude
function on the computational basis.  This is exactly the paper's setting,
where every Hamiltonian is real symmetric in the computational basis and all
states are real.  `Real.log` is the natural logarithm; every entropy in this
paper is measured in bits, so all entropies use `log2 = log / log 2`.

Boundary: this is the paper layer only.  It does not add shared
Foundations/Concepts objects, does not modify metadata, and does not claim
algorithmic cost semantics beyond the explicit cost fields used in the
measurement-algorithm and main-theorem files.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShortPathOpt18.MainResults

/-- The computational basis on `N` qubits. -/
abbrev Config (N : ℕ) : Type := Fin N → Bool

/-- Flip the `i`-th spin of a computational basis state. -/
def bitFlip {N : ℕ} (i : Fin N) (u : Config N) : Config N :=
  Function.update u i (Bool.not (u i))

/-- The `bitFlip_apply_self` result for the ShortPathOpt18 paper model. -/
@[simp]
theorem bitFlip_apply_self {N : ℕ} (i : Fin N) (u : Config N) :
    bitFlip i u i = Bool.not (u i) := by
  simp [bitFlip]

/-- The `bitFlip_involutive` result for the ShortPathOpt18 paper model. -/
theorem bitFlip_involutive {N : ℕ} (i : Fin N) (u : Config N) :
    bitFlip i (bitFlip i u) = u := by
  funext j
  by_cases h : j = i
  · subst h
    simp [bitFlip]
  · simp [bitFlip, h]

/-- The transverse-field operator `X = ∑ᵢ Xᵢ` in the computational basis:
the entry `(u,v)` is the number of spin flips taking `u` to `v`
(zero or one on a hypercube, and zero on the diagonal). -/
def xMatrix (N : ℕ) : Matrix (Config N) (Config N) ℝ :=
  fun u v => ∑ i : Fin N, if v = bitFlip i u then (1 : ℝ) else 0

/-- The diagonal Hamiltonian `H_Z` in the computational basis. -/
def hzMatrix {N : ℕ} (energy : Config N → ℝ) : Matrix (Config N) (Config N) ℝ :=
  Matrix.diagonal energy

/-- The short-path Hamiltonian `H_s = H_Z - s B (X/N)^K`, Eq. (6), p. 6. -/
def hsMatrix {N : ℕ} (energy : Config N → ℝ) (B : ℝ) (K : ℕ) (s : ℝ) :
    Matrix (Config N) (Config N) ℝ :=
  hzMatrix energy - (s * B * ((N : ℝ) ^ K)⁻¹) • (xMatrix N ^ K)

/-- Expectation of `H_Z` on a (real) state, `∑ᵤ ψ(u)² Eᵤ`. -/
def hzExp {N : ℕ} (energy : Config N → ℝ) (ψ : Config N → ℝ) : ℝ :=
  ∑ u, ψ u * (energy u * ψ u)

/-- Expectation of `(X/N)^K` on a (real) state. -/
def xPowExp (N K : ℕ) (ψ : Config N → ℝ) : ℝ :=
  ((N : ℝ) ^ K)⁻¹ * ∑ u, ψ u * ((xMatrix N ^ K).mulVec ψ) u

/-- The all-false computational basis state `|0⟩`. -/
def zeroConfig (N : ℕ) : Config N := fun _ => false

/-- The basis vector `|u⟩` as a real amplitude function. -/
def basisVec {N : ℕ} (u : Config N) : Config N → ℝ :=
  fun v => if v = u then 1 else 0

/-- Expectation of `X = ∑ᵢ Xᵢ` on a state, `⟨ψ|X|ψ⟩` (no `1/N` factor,
unlike `xPowExp`). -/
def xExp (N : ℕ) (ψ : Config N → ℝ) : ℝ :=
  ∑ u, ψ u * (xMatrix N).mulVec ψ u

/-- Expectation of the short-path Hamiltonian `H_s`. -/
def hsExp {N : ℕ} (energy : Config N → ℝ) (B : ℝ) (K : ℕ) (s : ℝ)
    (ψ : Config N → ℝ) : ℝ :=
  hzExp energy ψ - s * B * xPowExp N K ψ

/-- The normalized goal state `|+⟩^{⊗N} = ψ₊`, Eq. (8) and Section II. -/
def plusState (N : ℕ) : Config N → ℝ :=
  fun _ => (2 : ℝ) ^ (-(N : ℝ) / 2)

/-- Squared norm of a real amplitude function. -/
def normSq {N : ℕ} (ψ : Config N → ℝ) : ℝ :=
  ∑ u, ψ u ^ 2

/-- Real inner product (`⟨ψ|φ⟩` for real amplitudes). -/
def overlap {N : ℕ} (ψ φ : Config N → ℝ) : ℝ :=
  ∑ u, ψ u * φ u

/-- The overlap `P_ov = |⟨ψ₊|ψ_{0,1}⟩|²` of Eq. (8), p. 6. -/
def plusOverlap (N : ℕ) (ψ : Config N → ℝ) : ℝ :=
  overlap (plusState N) ψ

/-- `log₂`.  The paper measures all entropies in bits (p. 3 and p. 16). -/
def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Entropy in bits of a real probability mass function on basis states,
Eq. (49), p. 16.  For `p(u) = 0` the term is `0` (Mathlib's `Real.log 0 = 0`). -/
def compEntropyOfProb {N : ℕ} (p : Config N → ℝ) : ℝ :=
  -∑ u, p u * log2 (p u)

/-- The computational-basis entropy `S^(comp)(ψ)` of a state, Eq. (49). -/
def compEntropy {N : ℕ} (ψ : Config N → ℝ) : ℝ :=
  compEntropyOfProb (fun u => ψ u ^ 2)

/-- Expectation value of `H_Z` under a probability mass function. -/
def pmfMean {N : ℕ} (energy : Config N → ℝ) (p : Config N → ℝ) : ℝ :=
  ∑ u, p u * energy u

/-- `W(E)`: the number of computational basis states with energy `E`
(p. 2, line 127). -/
def W {N : ℕ} (energy : Config N → ℝ) (E : ℝ) : ℕ := by
  classical
  exact Fintype.card {u : Config N // energy u = E}

/-- The degeneracy assumption of Section I A (p. 2): `H_Z` has a unique ground
state for odd `D`, and a doubly degenerate ground state for even `D`; `E0` is
the ground energy.  The model records the resulting cardinality of the ground
eigenspace together with minimality of `E0`. -/
def DegeneracyAssumption {N : ℕ} (energy : Config N → ℝ) (E0 : ℝ) : Prop :=
  (Fintype.card {u : Config N // energy u = E0} = 1 ∨
      Fintype.card {u : Config N // energy u = E0} = 2) ∧
    ∀ u, E0 ≤ energy u

/-- `ψ` is a (nonzero) eigenvector of the matrix `A` with eigenvalue `E`. -/
def IsEigenpair {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (ψ : ι → ℝ) (E : ℝ) : Prop :=
  ψ ≠ 0 ∧ A.mulVec ψ = E • ψ

/-- `E0` is the ground-state energy of the self-adjoint operator `A`. -/
def IsGroundEnergy {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (E0 : ℝ) : Prop :=
  (∃ ψ, IsEigenpair A ψ E0) ∧ ∀ ψ E, IsEigenpair A ψ E → E0 ≤ E

/-- `ψ` lies in the range of the orthogonal projection `Q`. -/
def InRangeOf {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (ψ : ι → ℝ) : Prop :=
  Q.mulVec ψ = ψ

/-- Eigenpairs of `A` restricted to the range of the projection `Q`. -/
def IsEigenpairOnRange {ι : Type*} [Fintype ι] (Q A : Matrix ι ι ℝ) (ψ : ι → ℝ)
    (E : ℝ) : Prop :=
  InRangeOf Q ψ ∧ ψ ≠ 0 ∧ A.mulVec ψ = E • ψ

/-- `E` is the smallest eigenvalue of `A` on the range of `Q`
(the quantity `E^Q_{0,s}` of Section V, p. 11). -/
def IsGroundEnergyOnRange {ι : Type*} [Fintype ι] (Q A : Matrix ι ι ℝ) (E : ℝ) : Prop :=
  (∃ ψ, IsEigenpairOnRange Q A ψ E) ∧
    ∀ ψ E', IsEigenpairOnRange Q A ψ E' → E ≤ E'

/-- `A` has a spectral gap at least `δ` above its ground energy `E0`:
there is a ground state at `E0` and no eigenvalue strictly between `E0` and
`E0 + δ`. -/
def HasSpectralGap {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (E0 δ : ℝ) : Prop :=
  IsGroundEnergy A E0 ∧ ∀ ψ E, IsEigenpair A ψ E → E0 < E → E0 + δ ≤ E

/-- A state is normalized (`|ψ|² = 1`). -/
def IsUnit {N : ℕ} (ψ : Config N → ℝ) : Prop :=
  normSq ψ = 1

/-- `p` is a probability distribution on computational basis states. -/
def IsProbability {N : ℕ} (p : Config N → ℝ) : Prop :=
  (∀ u, 0 ≤ p u) ∧ (∑ u, p u = 1)

/-- The all-false basis state is a unit vector. -/
theorem basisVec_zero_isUnit (N : ℕ) : IsUnit (basisVec (zeroConfig N)) := by
  classical
  unfold IsUnit normSq basisVec
  rw [Finset.sum_eq_single (zeroConfig N)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (zeroConfig N)) h

end Qatlib.Papers.ShortPathOpt18.MainResults
