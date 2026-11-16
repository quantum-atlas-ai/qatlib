/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Foundations.PureStateMath.KernelGap.SpectralMass
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section


/-!
# Theorem 8.9 with a nonzero kernel witness

This realizes Eq. (8.19) of arXiv:0904.2759v1 on actual finite complex matrices.
The nonzero witness condition repairs the literal printed contract; the
missing-condition original is retained and refuted in `RankOneGap.lean`.
Included modes have strictly positive eigenvalues, so the sum does not exploit
Lean's totalized division by zero. A complete orthonormal spectral basis is a
special case of the orthonormal eigenfamily used here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath.KernelGap

namespace Qatlib.Papers.SpanProgReich09.MainResults

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Every selected source-sum mode has positive eigenvalue under the corrected witness contract. -/
theorem includedPos (X : Matrix I I ℂ) (hX : X.PosSemidef)
    (t φ : I → ℂ) (δ : ℝ) (hδ : 0 < δ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2)
    (W : Matrix I J ℂ) (lam : J → ℝ)
    (heig : (X + Matrix.vecMulVec t (fun i => star (t i))) * W =
      W * Matrix.diagonal (fun i => (lam i : ℂ)))
    (hlam : ∀ i, 0 ≤ lam i) (Λ : ℝ) (i : J)
    (hi : lam i ≤ Λ ∧ colOverlap t W i ≠ 0) : 0 < lam i := by
  by_contra h
  have hz : lam i = 0 := le_antisymm (le_of_not_gt h) (hlam i)
  exact hi.2 (zeroColOverlap X hX.1 t φ δ hδ hn hker hover W lam heig i hz)

/-- Corrected Theorem 8.9 proves the exact weighted sum and its positive-denominator boundary. -/
theorem theorem89 (X : Matrix I I ℂ) (hX : X.PosSemidef)
    (t φ : I → ℂ) (δ : ℝ) (hδ : 0 < δ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2)
    (W : Matrix I J ℂ) (lam : J → ℝ) (hW : Wᴴ * W = 1)
    (heig : (X + Matrix.vecMulVec t (fun i => star (t i))) * W =
      W * Matrix.diagonal (fun i => (lam i : ℂ)))
    (hlam : ∀ i, 0 ≤ lam i) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    (∀ i, lam i ≤ Λ ∧ colOverlap t W i ≠ 0 → 0 < lam i) ∧
      δ * (∑ i, if lam i ≤ Λ ∧
        Qatlib.Foundations.PureStateMath.Inner t (fun r => W r i) ≠ 0 then
        ‖Qatlib.Foundations.PureStateMath.Inner t (fun r => W r i)‖ ^ 2 / lam i
        else 0) ≤ 4 * Λ := by
  constructor
  · exact includedPos X hX t φ δ hδ hn hker hover W lam heig hlam Λ
  · have hb := invMassBound X hX.1 t φ δ hδ hn hker hover W lam hW heig hlam Λ hΛ
    change δ * invMass t W lam Λ ≤ 4 * Λ
    exact hb.trans (by nlinarith)

end Qatlib.Papers.SpanProgReich09.MainResults
