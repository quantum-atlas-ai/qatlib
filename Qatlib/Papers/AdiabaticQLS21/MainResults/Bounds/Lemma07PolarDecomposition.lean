/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 7: polar-decomposition form of the step unitary

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 7 / Eq. (45)--(47), page 10.

The claim is the identity

`V_T(s) = F_T(s) [I + DP_T(s) (2 P_T(s) - I)]`,  where
`F_T(s) = [I - (DP_T(s))²]^{-1/2}`.

The paper's proof (Eq. (47)) rewrites the polar-decomposition step operator
`S_T(s + 1/T, s) = P_T(s + 1/T) P_T(s) + Q_T(s + 1/T) Q_T(s)` as
`I - P_T(s) - P_T(s + 1/T) + 2 P_T(s + 1/T) P_T(s)` and then as
`I + (P_T(s + 1/T) - P_T(s)) (2P_T(s) - I)`.  This is pure algebra in the
projector `P_T(s)` and its complement, which is what `Sstep_eq` records; the
inverse square root is the paper's definition of `v_T^{-1}` (Eqs. (22), (46)),
so it is part of the model rather than the content of the lemma.

`V_T(s)` is modelled as `F_T(s) * S_T(s+1/T, s)` (Eq. (23) with
`v_T^{-1} = F_T`), exposed through the definitional hypothesis `hV`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

/-- Fixed arXiv:2111.08152, Lemma 7 (Eqs. (45)--(47), p. 10): the step unitary
`V_T(s)` of the left polar decomposition equals
`F_T(s) [I + DP_T(s)(2P_T(s) - I)]`, where `F_T(s) = [I - (DP_T(s))²]^{-1/2}`
is the inverse square root of `I - (DP_T(s))²` and `2P_T(s) - I` is the
reflection written as `P_T(s) + P_T(s) - 1`. -/
theorem source_lemma7 {R : Type*} [Ring R]
    (T : ℝ) (P F V : ℝ → R) (s : ℝ)
    (hP : ∀ t, P t * P t = P t)
    (hV : ∀ t, V t = F t * Sstep P T t) :
    V s = F s * (1 + diff T P s * refl (P s)) := by
  rw [hV s, Sstep]
  rw [Sstep_eq (P := P s) (P' := P (s + 1 / T)) (hP s)]
  simp only [diff]

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
