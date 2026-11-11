/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Diagonal-entry promise and resource predicates

This module defines real symmetric matrix-power instances and the two sides of the
diagonal-entry promise. It also introduces size, polynomial-growth, decision-cost, and reduction
predicates used to express the estimation problem; these predicates record the displayed maps
and bounds.

These constructions accompany the results of [JanzingWocjan2006a].

## Main statements

* `DiagEntryInstance`: stores a matrix, power, diagonal index, scale, threshold, and tolerance.
* `DiagEntryPromise`: requires one of the two separated diagonal-entry inequalities.
* `DiagonalEntryEstimationInBQP`: records a correct Boolean decision map with a polynomially
  bounded cost function.
* `DiagonalEntryEstimationBQPHardZeroOne`: records reductions with entries restricted to zero
  and signed one.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006a]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.Defs

open Matrix

/-- A real symmetric matrix-power instance with a nonnegative scale parameter, exponent,
diagonal index, threshold, and positive tolerance. -/
structure DiagEntryInstance where

  N : ℕ

  A : Matrix (Fin N) (Fin N) ℝ

  hA : A.IsHermitian

  b : ℝ

  hb : 0 ≤ b

  m : ℕ

  j : Fin N

  g : ℝ

  ε : ℝ

  hε : 0 < ε

/-- The condition that the selected matrix-power diagonal entry is at least the threshold plus
the scaled tolerance. -/
def DiagEntryYes (I : DiagEntryInstance) : Prop :=
  I.g + I.ε * I.b ^ I.m ≤ (I.A ^ I.m) I.j I.j

/-- The condition that the selected matrix-power diagonal entry is at most the threshold minus
the scaled tolerance. -/
def DiagEntryNo (I : DiagEntryInstance) : Prop :=
  (I.A ^ I.m) I.j I.j ≤ I.g - I.ε * I.b ^ I.m

/-- The disjunction of the upper-threshold and lower-threshold conditions for a diagonal-entry
instance. -/
def DiagEntryPromise (I : DiagEntryInstance) : Prop :=
  DiagEntryYes I ∨ DiagEntryNo I

/-- The condition that a natural-valued function is bounded by `(n + 1) ^ c + c` for some
natural exponent `c`. -/
def PolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, f n ≤ (n + 1) ^ c + c

/-- The sum of the matrix dimension and the power exponent of the instance. -/
def InstanceSize (I : DiagEntryInstance) : ℕ := I.N + I.m

/-- The existence of a Boolean decision map and a cost function bounded polynomially in
`InstanceSize`, with the map true exactly on yes instances satisfying the promise. -/
def DiagonalEntryEstimationInBQP : Prop :=
  ∃ (decide : DiagEntryInstance → Bool) (cost : DiagEntryInstance → ℕ),
    (∃ c : ℕ, ∀ I, cost I ≤ (InstanceSize I + 1) ^ c + c) ∧
      ∀ I, DiagEntryPromise I → (decide I = true ↔ DiagEntryYes I)

/-- The condition that every language with the displayed acceptance gap has an encoding with
polynomially bounded dimension and exponent, mapping members to no instances and nonmembers
to yes instances. -/
def DiagonalEntryEstimationBQPHard : Prop :=
  ∀ (L : List Bool → Prop) (accept : List Bool → ℝ),
    (∀ x, L x → 2 / 3 ≤ accept x) →
      (∀ x, ¬ L x → accept x ≤ 1 / 3) →
        ∃ (enc : List Bool → DiagEntryInstance) (c : ℕ),
          (∀ x, (enc x).N ≤ (x.length + 1) ^ c + c ∧
            (enc x).m ≤ (x.length + 1) ^ c + c) ∧
            (∀ x, L x → DiagEntryNo (enc x)) ∧
              (∀ x, ¬ L x → DiagEntryYes (enc x))

/-- The analogous encoding condition with matrix entries restricted to minus one, zero, and one,
and with language members mapped to no instances and nonmembers to yes instances. -/
def DiagonalEntryEstimationBQPHardZeroOne : Prop :=
  ∀ (L : List Bool → Prop) (accept : List Bool → ℝ),
    (∀ x, L x → 2 / 3 ≤ accept x) →
      (∀ x, ¬ L x → accept x ≤ 1 / 3) →
        ∃ (enc : List Bool → DiagEntryInstance) (c : ℕ),
          (∀ x, (enc x).N ≤ (x.length + 1) ^ c + c ∧
            (enc x).m ≤ (x.length + 1) ^ c + c) ∧
            (∀ x, ∀ i k, (enc x).A i k = -1 ∨ (enc x).A i k = 0 ∨
              (enc x).A i k = 1) ∧
              (∀ x, L x → DiagEntryNo (enc x)) ∧
                (∀ x, ¬ L x → DiagEntryYes (enc x))

end Qatlib.Papers.DiagPowerBQP06.MainResults.Defs
