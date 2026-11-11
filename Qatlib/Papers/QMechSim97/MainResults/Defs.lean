/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Fintype.Card

/-!
# Parameters and resource expressions for lattice simulation

This module defines the collision parameters, Bloch symbol, mass coefficients, and
potential-phase matrices for the lattice simulation framework of [BoghosianTaylor1998]. The
predicate `IsUnitaryPair` records the normalization and cross-term constraints on the
one-dimensional collision coefficients.

The remaining definitions give occupation counts and explicit lattice-size expressions for
qubits, propagation, kinetic and interaction costs, and the classical component count. These are
the quantities used by subsequent algebraic and resource-bound results.

## Main statements

* `IsUnitaryPair`: the two constraints on collision coefficients.
* `symbolMatrix`: the two-by-two momentum-dependent Bloch symbol.
* `externalPotential`: the negative external-potential phase matrix.
* `totalQuantumGates`: the sum of the three defined gate-count expressions.

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.Defs

open Complex

/-- The conditions `normSq a + normSq b = 1` and `a * conjugate b + conjugate a * b = 0` on
collision coefficients. -/
def IsUnitaryPair (a b : ℂ) : Prop :=
  Complex.normSq a + Complex.normSq b = 1 ∧
    a * (starRingEnd ℂ) b + (starRingEnd ℂ) a * b = 0

/-- The one-dimensional mass parameter `b * i / a`. -/
def particleMass1D (a b : ℂ) : ℂ := b * I / a

/-- The Schrödinger coefficient `i / (2 * m)` associated with a complex mass parameter. -/
def schrodingerCoeff (m : ℂ) : ℂ := I / (2 * m)

/-- The dispersion coefficient `a / (2 * b)`. -/
def dispersionCoeff (a b : ℂ) : ℂ := a / (2 * b)

/-- The two-by-two collision matrix with diagonal entries `b` and off-diagonal entries `a`. -/
def collision2 (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![b, a; a, b]

/-- The two-by-two Bloch symbol with diagonal entries `b ^ 2 + a ^ 2 * exp(∓2ix)` and
off-diagonal entries `a * b * (exp(ix) + exp(-ix))`. -/
def symbolMatrix (a b : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![b ^ 2 + a ^ 2 * Complex.exp (-(2 * x) * I),
       a * b * (Complex.exp (x * I) + Complex.exp (-(x * I)));
     a * b * (Complex.exp (x * I) + Complex.exp (-(x * I))),
       b ^ 2 + a ^ 2 * Complex.exp (2 * x * I)]

/-- The number of indices whose Boolean occupation value is true. -/
def occupationCount {ι : Type*} [Fintype ι] (occ : ι → Bool) : ℕ :=
  Fintype.card {i : ι // occ i = true}

/-- The mass parameter `i / (2 * ((ν / (μ - ν) + 1 / 2) / d))` determined by the mode
parameters. -/
def massFromPhases (d μ ν : ℂ) : ℂ :=
  I / (2 * ((ν / (μ - ν) + 1 / 2) / d))

/-- The two-by-two diagonal matrix with entries one and `exp(-iθ)`. -/
def externalPotential (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else Complex.exp (-θ * I))

/-- The four-by-four diagonal matrix with entry `exp(-iθ)` at label three and one at the other
labels. -/
def pairPotential (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun i => if i = 3 then Complex.exp (-θ * I) else 1)

/-- The lattice qubit-count expression `2 * d * l ^ d`. -/
def qubitCount (d l : ℕ) : ℕ := 2 * d * l ^ d

/-- The propagation gate-count expression `d * l ^ d`. -/
def propagationGates (d l : ℕ) : ℕ := d * l ^ d

/-- The kinetic gate-count expression `d ^ 2 * l ^ d`. -/
def kineticGates (d l : ℕ) : ℕ := d ^ 2 * l ^ d

/-- The interaction gate-count expression `d ^ 2 * l ^ (2 * d)`. -/
def interactionGates (d l : ℕ) : ℕ := d ^ 2 * l ^ (2 * d)

/-- The sum of the defined propagation, kinetic, and interaction gate-count expressions. -/
def totalQuantumGates (d l : ℕ) : ℕ :=
  propagationGates d l + kineticGates d l + interactionGates d l

/-- The classical component-count expression `l ^ (d * n)` for `n` particles. -/
def classicalComponents (d l n : ℕ) : ℕ := l ^ (d * n)

end Qatlib.Papers.QMechSim97.MainResults.Defs
