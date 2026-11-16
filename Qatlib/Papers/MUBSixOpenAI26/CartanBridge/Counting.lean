/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.ThreeBasis

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — the cardinality consequence of Theorem 1.1

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
Section 1 (`introduction.tex` lines 10--18): `N(d)` is the largest number of
pairwise mutually unbiased orthonormal bases in `ℂ^d`, and Theorem `thm:main`
concludes `N(6) = 3`.

The paper's argument for the equality from the computer-assisted exclusion is
elementary: any family of at least four bases contains a four-element subfamily,
which the exclusion forbids; three exist by `lem:three-mub-six`. The proof below
performs the subfamily restriction with `Fin.castLE` and the Frobenius-free
counting argument, no spectral or computer-search input.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- If no four pairwise mutually unbiased orthonormal bases exist in `ℂ^6`, then
no family of `m ≥ 4` bases exists either (paper's "Consequently" step of
Theorem 1.1). -/
theorem le_three_of_no_four (hno : NoFourMUBs) {m : ℕ} (hm : HasMUBFamily m) :
    m ≤ 3 := by
  by_contra hle
  have h4 : 4 ≤ m := by omega
  obtain ⟨B, hB⟩ := hm
  apply hno
  refine ⟨fun r => B (Fin.castLE h4 r), ?_⟩
  refine ⟨fun r => hB.1 (Fin.castLE h4 r), ?_⟩
  intro r s hrs i j
  exact hB.2 (Fin.castLE h4 r) (Fin.castLE h4 s)
    (fun he => hrs (Fin.castLE_injective h4 he)) i j

/-- Theorem 1.1 (`thm:main`, `introduction.tex` lines 13--18): under the
arithmetic/compiler and execution contract, `N(6) = 3`, stated as `NoFourMUBs`
plus existence of three bases. -/
theorem maximum_three_of_no_four (hno : NoFourMUBs) : MaximumNumberIs 3 :=
  ⟨three_mub_bases_in_dimension_six, fun _ hm => le_three_of_no_four hno hm⟩

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
