/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StabRank21.ExactRank.Theorem11ExactStabilizerRankLowe

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1.1 of Peleg–Shpilka–Volk (arXiv:2106.03214v2, p.3, §1.2)

`χ(H^{⊗n}) = Ω(n)` and `χ(R^{⊗n}) = Ω(n)`, at the amplitude-function level of
the paper's §2.1.  The printed Ω(n) lower bound is the explicit statement
`n/100 < χ(·)` proved in §3 (Lemma 3.1 + Theorem 3.2); it is already available
in the pinned Frozen release as
`StabilizerRank.ExactRank.theorem11ExactStabilizerRank`
(file `.../ExactRank/Theorem11ExactStabilizerRankLowe/Theorem11ExactStabilizerRank.lean`),
whose proof chain is `exact_rank_collision → rank_bound_of_layers` and the
Hamming-layer injectivity of the `magicH`/`magicR` amplitudes.  This file is the
paper-layer bridge; no statement is weakened: the paper's `χ(H^{⊗n})` and
`χ(R^{⊗n})` are represented by `stabilizerRank (magicH n)` and
`stabilizerRank (magicR n)` where `magicH`/`magicR` are the paper's amplitude
functions of §3.
-/

set_option autoImplicit false

namespace Qatlib.Papers.StabRank21.MainResults.Theorem11ExactRank

open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Papers.StabRank21.ExactRank

/-- **Theorem 1.1** (arXiv:2106.03214v2, p.3; restated as Theorem 3.2, p.8).
For every `n`, the exact stabilizer ranks of the `|H^⊗n⟩` and `|R^⊗n⟩`
amplitude functions both exceed `n/100`; this is the explicit constant form of
the paper's `χ(H^⊗n) = Ω(n)`, `χ(R^⊗n) = Ω(n)`.

Reuses Frozen
`StabilizerRank.ExactRank.theorem11ExactStabilizerRank`
with the same type; the proof is complete (no `sorry`). -/
theorem theorem_1_1_exact_stabilizer_rank_lower_bound (n : ℕ) :
    n / 100 < stabilizerRank (magicH n) ∧ n / 100 < stabilizerRank (magicR n) :=
  theorem11ExactStabilizerRank n

end Qatlib.Papers.StabRank21.MainResults.Theorem11ExactRank
