/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.Definitions

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — Lemma `lem:three-mub-six`

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`introduction.tex` lines 160--210 (Section 1.3, "The elementary lower bound"),
Lemma `lem:three-mub-six`.

The paper constructs the three bases as the columns of `A_r ⊗ B_r` for
`r = 0,1,2`, with `A_0 = I_2`, `A_1 = (1/√2)[[1,1],[1,-1]]`,
`A_2 = (1/√2)[[1,1],[i,-i]]` and `B_0 = I_3`, `B_1 = F` (the qutrit Fourier
matrix) and `B_2 = D F` with `D = diag(1, ω, ω)`; the relative overlaps
`A_r^* A_s` and `B_r^* B_s` have all entries of squared modulus `1/2` and `1/3`,
so `U_r^* U_s` has all entries of squared modulus `1/6`.

Reused FQN: `Mub6Maximum.ThreeBasis.threeBasesExist`
(in `.../ThreeBasis/MUBProductBases/MUBProductBases.lean`). That theorem builds the
two explicit `6 × 6` Hadamard matrices `H` (qubit `X/Y` tensor qutrit Fourier) and
`K` (qubit `X/Y` tensor qutrit chirp), proves `HᴴH = KᴴK = 6 • 1`, all entry moduli
one, and `normSq ((HᴴK)ᵢⱼ) = 6`; after the exact `1/√6` normalization the three
column families satisfy the full `IsFamily` contract. It is the same construction as
the paper's tensor product `A_r ⊗ B_r` (the two matrices coincide after the standard
qubit Hadamard relabelling), so no new proof obligation remains here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- Lemma `lem:three-mub-six` (`introduction.tex` lines 166--210): there exist
three pairwise mutually unbiased orthonormal bases in `ℂ^6`. -/
theorem three_mub_bases_in_dimension_six : HasMUBFamily 3 :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.threeBasesExist

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
