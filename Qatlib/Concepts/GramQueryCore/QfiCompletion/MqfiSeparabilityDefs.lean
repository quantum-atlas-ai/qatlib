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

@[expose] public section

open scoped Matrix

namespace Qatlib.Concepts.GramQueryCore.QfiCompletion

def RealSeparable {p r : ℕ} (H : Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ) (z : Fin m → Fin p → ℝ) (w : Fin m → Fin r → ℝ),
    (∀ a, 0 ≤ c a) ∧
      ∀ x y : Fin p × Fin r,
        H x y = ∑ a, c a * (z a x.1 * z a y.1) * (w a x.2 * w a y.2)

def mqfiBlocks {p r q : ℕ} (B : Fin p → Matrix (Fin r) (Fin q) ℝ) :
    Matrix (Fin p × Fin r) (Fin p × Fin r) ℝ :=
  Matrix.of fun x y => (B x.1 * (B y.1)ᵀ) x.2 y.2

def mqfiPadCols {r q n : ℕ} (M : Matrix (Fin r) (Fin q) ℝ) :
    Matrix (Fin r) (Fin (q + n)) ℝ :=
  Matrix.of fun s k => if h : (k : ℕ) < q then M s ⟨k, h⟩ else 0

noncomputable def mqfiCompletion {p r q n : ℕ} (B : Fin p → Matrix (Fin r) (Fin q) ℝ)
    (K : Fin p → Matrix (Fin (q + n)) (Fin (q + n)) ℂ) (α : Fin p) :
    Matrix (Fin r ⊕ Fin (q + n)) (Fin r ⊕ Fin (q + n)) ℂ :=
  Matrix.fromBlocks 0 ((mqfiPadCols (B α)).map (algebraMap ℝ ℂ))
    (((mqfiPadCols (B α)).map (algebraMap ℝ ℂ))ᴴ) (K α)

def HasMqfiCompletion {p r q : ℕ} (B : Fin p → Matrix (Fin r) (Fin q) ℝ) : Prop :=
  ∃ (n : ℕ) (K : Fin p → Matrix (Fin (q + n)) (Fin (q + n)) ℂ),
    (∀ α, (K α).IsHermitian) ∧
      ∀ α β, mqfiCompletion B K α * mqfiCompletion B K β
        = mqfiCompletion B K β * mqfiCompletion B K α

end Qatlib.Concepts.GramQueryCore.QfiCompletion
