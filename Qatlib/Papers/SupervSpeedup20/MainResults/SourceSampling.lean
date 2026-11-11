/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SupervSpeedup20.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 7 — classical sampling from a concept in `C`

Fixed source: arXiv:2010.02174 (v1, 5 Oct 2020), Lemma 7, p. 10, Eq. (B2).

For every concept `f_s ∈ C` there is an efficient classical algorithm producing
samples `(x, f_s(x))` with `x` uniform on `Z_p^*`.  The algorithm draws a
uniform `y ∈ Z_N` and outputs `(g^y, b)` where `b = +1` iff
`y ∈ [s, s + (p-3)/2]`; the push-forward identity is
`DlogWorld.pushforward_eq_dataLaw` (Definitions.lean), and the cost annotation
is the polynomial bound of `DlogWorld.ClassicalSampler`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SupervSpeedup20.MainResults

open Finset DlogWorld
open scoped BigOperators

/-- **Lemma 7 (source p. 10, Eq. (B2)).**  For every concept `f_s ∈ C` there is
an efficient classical algorithm that generates samples `(x, f_s(x))` with `x`
uniformly random in `Z_p^*`: it induces exactly the data law
(`DlogWorld.pushforward_eq_dataLaw`) and runs in polynomial time in the
security parameter. -/
theorem source_lemma7 (W : DlogWorld) (s : ZMod W.N) :
    ∃ S : W.ClassicalSampler (W.conceptClass s),
      (∀ z : W.X × Bool,
        (∑ y : S.seed, if S.run y = z then (Fintype.card S.seed : ℝ)⁻¹ else 0) =
          W.dataLaw (W.conceptClass s) z) ∧
      (∃ c k : ℕ, ∀ n : ℕ, S.cost n ≤ c * n ^ k + c) := by
  obtain ⟨S, -⟩ := W.exists_classical_sampler s
  exact ⟨S, S.hlaw, S.hcost⟩

end Qatlib.Papers.SupervSpeedup20.MainResults
