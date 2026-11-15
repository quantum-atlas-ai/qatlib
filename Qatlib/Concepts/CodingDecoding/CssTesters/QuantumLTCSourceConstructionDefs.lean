/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.FieldBinaryMatrix
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.CodingDecoding.CssTesters

def fixedGammaLower (τ : ℝ) : ℝ := (1 - 2 * τ) ^ 4 - 2 * τ ^ 2

def fixedMiddleUpper (τ : ℝ) : ℝ := 4 * τ ^ 2 + 16 * τ + 4

def fixedAdjacentUpper (τ : ℝ) : ℝ := 16 * τ ^ 2 + 20 * τ + 4

def fixedStartingExponent : ℕ := 2 ^ 15

def edgeBoundary {V E : Type*} [DecidableEq V] (start finish : E → V) :
    Matrix V E (ZMod 2) :=
  fun v e => (if start e = v then 1 else 0) + (if finish e = v then 1 else 0)

def squareBoundary {E Q : Type*} [DecidableEq E] (edges : Q → Fin 4 → E) :
    Matrix E Q (ZMod 2) :=
  fun e q => (Pi.single (edges q 0) 1 + Pi.single (edges q 1) 1 +
    Pi.single (edges q 2) 1 + Pi.single (edges q 3) 1 : E → ZMod 2) e

noncomputable def evaluationWeight {F : Type*} [Field F] (S : Finset F)
    (p : Polynomial F) : ℕ := by
  classical
  exact (S.filter fun x => p.eval x ≠ 0).card

noncomputable def cubicalCellCount (t j : ℕ) (n : Fin t → ℕ)
    (m : Fin t → Fin 2 → ℕ) : ℕ :=
  (Finset.univ.filter fun s : Finset (Fin t) => s.card = j).sum fun s =>
    (s.prod fun i => m i 0 + m i 1) * (sᶜ.prod fun i => n i)

end Qatlib.Concepts.CodingDecoding.CssTesters
