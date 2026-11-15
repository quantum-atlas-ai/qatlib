/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiSeparabilityDefs

@[expose] public section

open scoped Matrix

namespace Qatlib.Concepts.GramQueryCore.QfiCompletion

def MqfiRationalGramFactorization : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℚ),
    H.IsSymm → (H.map (algebraMap ℚ ℝ)).PosSemidef →
    ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) ℚ), B * Bᵀ = H

end Qatlib.Concepts.GramQueryCore.QfiCompletion
