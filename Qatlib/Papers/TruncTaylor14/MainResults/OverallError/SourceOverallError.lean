/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Ln2SegmentationCorrectedSimu

set_option backward.isDefEq.respectTransparency false

/-!
# Source p. 3 — overall simulation error `≤ ε` from `r` reset/discard segments

arXiv:1412.4687v1, p. 3, paragraph after Eq. (21) (and Eqs. (16), (18)–(19)).
The source runs `r = max 1 ⌈Λt / ln 2⌉` segments; at each step the segment
ancilla is initialized in `|0⟩`, the amplified word `A` is applied, and the
ancilla is traced out.  If `K` is chosen so that the per-segment error is
`O(ε/r)` (`δ = O(ε/r)` in Eq. (16), ensured by the factorial tail budget
Eq. (19)), subadditivity over the `r` steps gives final error `≤ ε` against
`U|ψ⟩ = e^{-iHt}|ψ⟩`.

Frozen FQN reused:
`QuantumAlgorithm.Papers.TruncTaylor14.ResetDiscard.ln2Segmentation`
(`Ln2SegmentationCorrected`, `Statements/...`), which proves the concrete
trace-norm bound `≤ ε` after all `r` corrected reset/discard iterations,
for every density matrix.  The frozen statement assumes a supplied block
encoding `W` of the truncated ln-2 segment and a factorial tail budget
`Σ_{j} (ln2)^{K+1+j}/(K+1+j)! ≤ ε/(69 r)`; both are exactly the paper's
`δ = O(ε/r)` choices.  The paid actual-word variant is
`QuantumAlgorithm.Papers.TruncTaylor14.SourceDiscard.sourceDiscardActualSimulation`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.ResetDiscard
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.TruncTaylor14.MainResults.OverallError

/-- arXiv:1412.4687v1 p. 3: after `r = max 1 ⌈Λt/ln 2⌉` segments with the
ancilla reset and discarded at each step, the final state is `ε`-close in trace
norm to `e^{-iHt} ρ e^{iHt}` for every density matrix `ρ`, provided the
factorial tail budget of Eq. (19) holds. -/
theorem source_overall_error
    (I : Type) [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t ε Λ : ℝ) (K : ℕ)
    (J : Type) [Fintype J] [DecidableEq J]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (hH : H.IsHermitian) (ht : 0 ≤ t) (hΛ : ‖H‖ ≤ Λ) (hΛpos : 0 < Λ)
    (hK : 2 ≤ K) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hW : IsBlockEncoding W j₀
      (truncatedSegment H (t / (max 1 (Nat.ceil (Λ * t / Real.log 2)))) K) (ln2Scale K))
    (htail :
      (∑' j : ℕ, (Real.log 2) ^ (K + 1 + j) / (((K + 1 + j).factorial : ℕ) : ℝ)) ≤
        ε / (69 * (max 1 (Nat.ceil (Λ * t / Real.log 2)))))
    (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) (htr : Matrix.trace ρ = 1) :
    Matrix.traceNorm
        ((ResetDiscardStepCorrected W j₀)^[max 1 (Nat.ceil (Λ * t / Real.log 2))] ρ -
          HamiltonianEvolution H t * ρ * (HamiltonianEvolution H t)ᴴ) ≤ ε :=
  ln2Segmentation I H t ε Λ K J W j₀ hH ht hΛ hΛpos hK hε0 hε1 hW htail ρ hρ htr

end Qatlib.Papers.TruncTaylor14.MainResults.OverallError
