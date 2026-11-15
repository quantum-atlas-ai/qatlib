/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib

open scoped Matrix

def ExactSamplerPermanentReadout : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ), 0 < ε →
    (∀ v : Fin n → ℂ,
      ε * Real.sqrt (∑ i, Complex.normSq ((X *ᵥ v) i))
        ≤ Real.sqrt (∑ i, Complex.normSq (v i))) →
    ∀ W : Matrix (Fin (2 * n)) (Fin n) ℂ, Wᴴ * W = 1 →
      (∀ i j, W (Fin.castLE (by omega) i) j = (ε : ℂ) * X i j) →
      ∀ (L : ℕ) (O : (Fin L → Bool) → FockOccupation (2 * n) n),
        (∀ S : FockOccupation (2 * n) n,
          (∑ r : (Fin L → Bool), if O r = S then (1 : ℝ) else 0) / (2 ^ L : ℝ)
            = bosonWeight W S) →
        (∑ r : (Fin L → Bool), if O r = bosonOneState n then (1 : ℝ) else 0)
            / (2 ^ L : ℝ)
          = (ε ^ 2) ^ n * Complex.normSq (Matrix.permanent X)

end Qatlib.Concepts.BosonFock.PermAnalysis
