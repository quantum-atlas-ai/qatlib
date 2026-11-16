/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Encoding
open Matrix Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Matrix.Norms.L2Operator
variable {J K I : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I]

/-- Multiplying the two supplied block encodings on independent ancillas encodes `A * B` with error `alpha * epsilon + beta * delta + delta * epsilon`. This uses the conservative product estimate from `Qatlib.Concepts.BlockEncoding.EncodingCore.independent_ancilla_blockEncoding_product`; no smaller general error is asserted. -/
theorem lemma4_product_block_encoding
    (j₀ : J) (k₀ : K) (A B : Matrix I I ℂ)
    (U : Matrix (J × I) (J × I) ℂ) (V : Matrix (K × I) (K × I) ℂ)
    (α β ε δ : ℝ)
    (hU : BlockEncoding A U (encodingFiber j₀) (encodingFiber j₀) α δ)
    (hV : BlockEncoding B V (encodingFiber k₀) (encodingFiber k₀) β ε) :
    BlockEncoding (A * B) (independentLiftLeft U * independentLiftRight V)
      (jointEncodingFiber j₀ k₀) (jointEncodingFiber j₀ k₀) (α * β)
      (α * ε + β * δ + δ * ε) := by
  have h := independent_ancilla_blockEncoding_product j₀ k₀ A B U V α β δ ε hU hV
  have heq : β * δ + α * ε + δ * ε = α * ε + β * δ + δ * ε := by ring
  rwa [heq] at h

/-- **Lemma 4, printed error `αε + βδ`.**  When one encoding error is zero the
nonnegative product term `δε` vanishes and the paper's printed bound holds. -/
theorem lemma4_product_block_encoding_paper_error
    (j₀ : J) (k₀ : K) (A B : Matrix I I ℂ)
    (U : Matrix (J × I) (J × I) ℂ) (V : Matrix (K × I) (K × I) ℂ)
    (α β ε δ : ℝ)
    (hU : BlockEncoding A U (encodingFiber j₀) (encodingFiber j₀) α δ)
    (hV : BlockEncoding B V (encodingFiber k₀) (encodingFiber k₀) β ε)
    (hδ : δ = 0 ∨ ε = 0) :
    BlockEncoding (A * B) (independentLiftLeft U * independentLiftRight V)
      (jointEncodingFiber j₀ k₀) (jointEncodingFiber j₀ k₀) (α * β)
      (α * ε + β * δ) := by
  have h := lemma4_product_block_encoding j₀ k₀ A B U V α β ε δ hU hV
  rcases hδ with h0 | h0
  · subst h0; simpa using h
  · subst h0; simpa using h

end Qatlib.Papers.BlockEncMatPw18.MainResults.Encoding
