/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Registers and solver predicates for lattice reductions

This module defines the integer register models, lattice vector and separation predicates, and
solver specifications used in the reductions. It also introduces modular subset sum routines and
counts of legal inputs and legal inputs receiving a returned subset. See [Regev2004] for the
paper context.

## Main statements

* `SolvesDCP`: The requirement that the routine return the second integer minus the first on
  every DCP register.
* `SolvesTwoPoint`: The requirement that the routine return `TwoPointRegister.delta` on every
  two-point register.
* `IsUniqueShortest`: A nonzero lattice vector `u` satisfies this predicate when every nonzero
  lattice vector outside its integer multiples has norm at least `γ n * norm u`.
* `SolvesSubsetSum`: The property that some input-length function and everywhere positive
  fraction bound below the proportion of legal inputs on which the routine returns some subset,
  for every positive modulus.

## References

* [Regev, 2004][Regev2004]
-/

set_option autoImplicit false

open scoped Classical
attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.QLattice03.MainResults

/-- An integer pair used as a DCP register, with modulus parameter `N`. -/
abbrev DCPRegister (_N : ℕ) := ℤ × ℤ

/-- The requirement that the routine return the second integer minus the first on every DCP
register. -/
def SolvesDCP (A : ∀ N : ℕ, DCPRegister N → ℤ) : Prop :=
  ∀ (N : ℕ) (r : DCPRegister N), A N r = r.2 - r.1

/-- A pair of length-`n` vectors whose coordinates lie in `Fin M`. -/
structure TwoPointRegister (n M : ℕ) where
  a : Fin n → Fin M
  a' : Fin n → Fin M

/-- The coordinatewise integer difference of the second vector and the first. -/
def TwoPointRegister.delta {n M : ℕ} (r : TwoPointRegister n M) : Fin n → ℤ :=
  fun i => (r.a' i : ℤ) - (r.a i : ℤ)

/-- The requirement that the routine return `TwoPointRegister.delta` on every two-point
register. -/
def SolvesTwoPoint (A : ∀ n M : ℕ, TwoPointRegister n M → (Fin n → ℤ)) : Prop :=
  ∀ (n M : ℕ) (r : TwoPointRegister n M), A n M r = r.delta

/-- A family of `n` integer vectors with `n` coordinates each. -/
abbrev LatticeBasis (n : ℕ) := Fin n → Fin n → ℤ

/-- The property that `v` is an integer linear combination of the vectors in `b`. -/
def IsLatticeVector {n : ℕ} (b : LatticeBasis n) (v : Fin n → ℤ) : Prop :=
  ∃ c : Fin n → ℤ, ∀ j : Fin n, v j = ∑ i : Fin n, c i * b i j

/-- The sum of the squares of the integer coordinates, viewed as a real number. -/
def normsq {n : ℕ} (v : Fin n → ℤ) : ℝ := ∑ i : Fin n, (v i : ℝ) ^ 2

/-- The real square root of `normsq`, giving the Euclidean norm of the integer vector. -/
noncomputable def norm {n : ℕ} (v : Fin n → ℤ) : ℝ := Real.sqrt (normsq v)

/-- A nonzero lattice vector `u` satisfies this predicate when every nonzero lattice vector
outside its integer multiples has norm at least `γ n * norm u`. -/
def IsUniqueShortest {n : ℕ} (γ : ℕ → ℝ) (b : LatticeBasis n) (u : Fin n → ℤ) : Prop :=
  IsLatticeVector b u ∧ u ≠ 0 ∧
    ∀ v : Fin n → ℤ, IsLatticeVector b v → v ≠ 0 →
      (¬ ∃ k : ℤ, ∀ j, v j = k * u j) → γ n * norm u ≤ norm v

/-- The requirement that the routine return every vector `u` satisfying `IsUniqueShortest γ b u`
for the supplied lattice family `b`. -/
def SolvesUniqueSVP (γ : ℕ → ℝ)
    (A : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ)) : Prop :=
  ∀ (n : ℕ) (b : LatticeBasis n) (u : Fin n → ℤ), IsUniqueShortest γ b u → A n b = u

/-- The condition that equal function values occur exactly for identical pairs or pairs related
by adding `s` to the residue and flipping the Boolean component. -/
def HidesSlope (N : ℕ) (f : ZMod N × Bool → Bool) (s : ZMod N) : Prop :=
  ∀ p q : ZMod N × Bool, f p = f q ↔ q = p ∨ q = (p.1 + s, !p.2)

/-- The requirement that the routine recover `s` from every function satisfying `HidesSlope N f
s`. -/
def SolvesDihedralHSP (A : ∀ N : ℕ, (ZMod N × Bool → Bool) → ZMod N) : Prop :=
  ∀ (N : ℕ) (f : ZMod N × Bool → Bool) (s : ZMod N), HidesSlope N f s → A N f = s

/-- The property that some subset of the input coordinates sums to the target residue modulo
`N`. -/
def SubsetSumLegal (N r : ℕ) (a : Fin r → ZMod N) (t : ZMod N) : Prop :=
  ∃ B : Finset (Fin r), ∑ i ∈ B, a i = t

/-- A routine taking a modulus, input length, residue vector, and target residue, and returning
an optional subset of coordinate indices. -/
abbrev SubsetSumRoutine := ∀ (N r : ℕ), (Fin r → ZMod N) → ZMod N → Option (Finset (Fin r))

/-- The number of residue-vector and target pairs satisfying `SubsetSumLegal`. -/
noncomputable def legalCard (N r : ℕ) [NeZero N] : ℕ :=
  Fintype.card {p : (Fin r → ZMod N) × ZMod N // SubsetSumLegal N r p.1 p.2}

/-- The number of legal residue-vector and target pairs on which `S` returns some subset. -/
noncomputable def solvedCard (S : SubsetSumRoutine) (N r : ℕ) [NeZero N] : ℕ :=
  Fintype.card {p : (Fin r → ZMod N) × ZMod N //
    SubsetSumLegal N r p.1 p.2 ∧ (S N r p.1 p.2).isSome}

/-- The property that some input-length function and everywhere positive fraction bound below
the proportion of legal inputs on which the routine returns some subset, for every positive
modulus. -/
def SolvesSubsetSum (S : SubsetSumRoutine) : Prop :=
  ∃ (r : ℕ → ℕ) (frac : ℕ → ℝ), (∀ N, 0 < frac N) ∧
    ∀ N : ℕ, ∀ (hN : 0 < N),
      frac N * (@legalCard N (r N) ⟨Nat.pos_iff_ne_zero.mp hN⟩ : ℝ) ≤
        (@solvedCard S N (r N) ⟨Nat.pos_iff_ne_zero.mp hN⟩ : ℝ)

end Qatlib.Papers.QLattice03.MainResults
