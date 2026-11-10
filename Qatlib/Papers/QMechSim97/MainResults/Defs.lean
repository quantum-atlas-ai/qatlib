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

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.Defs

open Complex

def IsUnitaryPair (a b : ℂ) : Prop :=
  Complex.normSq a + Complex.normSq b = 1 ∧
    a * (starRingEnd ℂ) b + (starRingEnd ℂ) a * b = 0

def particleMass1D (a b : ℂ) : ℂ := b * I / a

def schrodingerCoeff (m : ℂ) : ℂ := I / (2 * m)

def dispersionCoeff (a b : ℂ) : ℂ := a / (2 * b)

def collision2 (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![b, a; a, b]

def symbolMatrix (a b : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![b ^ 2 + a ^ 2 * Complex.exp (-(2 * x) * I),
       a * b * (Complex.exp (x * I) + Complex.exp (-(x * I)));
     a * b * (Complex.exp (x * I) + Complex.exp (-(x * I))),
       b ^ 2 + a ^ 2 * Complex.exp (2 * x * I)]

def occupationCount {ι : Type*} [Fintype ι] (occ : ι → Bool) : ℕ :=
  Fintype.card {i : ι // occ i = true}

def massFromPhases (d μ ν : ℂ) : ℂ :=
  I / (2 * ((ν / (μ - ν) + 1 / 2) / d))

def externalPotential (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else Complex.exp (-θ * I))

def pairPotential (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun i => if i = 3 then Complex.exp (-θ * I) else 1)

def qubitCount (d l : ℕ) : ℕ := 2 * d * l ^ d

def propagationGates (d l : ℕ) : ℕ := d * l ^ d

def kineticGates (d l : ℕ) : ℕ := d ^ 2 * l ^ d

def interactionGates (d l : ℕ) : ℕ := d ^ 2 * l ^ (2 * d)

def totalQuantumGates (d l : ℕ) : ℕ :=
  propagationGates d l + kineticGates d l + interactionGates d l

def classicalComponents (d l n : ℕ) : ℕ := l ^ (d * n)

end Qatlib.Papers.QMechSim97.MainResults.Defs
