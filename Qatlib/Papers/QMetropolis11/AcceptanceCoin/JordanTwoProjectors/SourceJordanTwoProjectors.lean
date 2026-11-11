/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.JordanTwoProjectorsStat
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.JordanTwoProjectorsQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Jordan 1875 two-projector normal form (Temme et al. 2011, Sec. 7, Eq. (73))

Fixed source: arXiv:0911.3635v2, Section 7 "Binary measurements and pairs of
subspaces", printed page 23.

The paper states: for two projectors `P₁` and `Q₁` of ranks `p` and `q` on
`ℂⁿ` with `p + q ≤ n` and (w.l.o.g.) `q ≥ p`, there is a basis in which `P₁` is
the projection onto the first `p` coordinates and `Q₁` has the block form
displayed in Eq. (73), with a `p × p` diagonal matrix `D` whose real diagonal
entries satisfy `0 ≤ d₁ ≤ … ≤ d_p ≤ 1`.

The frozen semantic layer encodes the *coordinate-free and rank-agnostic*
content of this normal form as the predicate `JordanTwoProjectors`: it retains
all `P`-range axes, normalizes only the interior partners `0 < d_i < 1`,
lets the endpoint partners (`d_i ∈ {0,1}`) be zero, and carries the remaining
one-dimensional sectors by an orthogonal projection `W` commuting with `Q`.
The module docstring of that file records why the literal printed rank
hypotheses cannot be imposed at arbitrary ranks.  This paper-layer file only
re-exports the frozen result and unpacks it in the paper's own symbols.

Reused FQNs (namespace `QuantumAlgorithm.Concepts.MixedInstrument.RewindAlgebra`):
* `JordanTwoProjectors` (definition, Eq. (73));
* `jordanTwoProjectors` (the lemma itself).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin.JordanTwoProjectors

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Qatlib.Concepts.MixedInstrument.RewindAlgebra.Temme2011

/-- **c015, Sec. 7 Lemma "Jordan 1875" (Eq. (73), printed p. 23).**  The
frozen contract: every pair of Hermitian idempotents has the diagonal
block normal form (73) together with the complete Parseval decomposition and
the two block actions of `Q` on the range and partner axes.  Reused FQN:
`...RewindAlgebra.jordanTwoProjectors`. -/
theorem source_jordanTwoProjectors : JordanTwoProjectors :=
  jordanTwoProjectors

/-- **c015, Eq. (73), unpacked.**  The normal-form statement in the paper's
symbols: for Hermitian idempotents `P` and `Q` there are `k` normalized
`P`-range vectors `u`, partner vectors `v`, real weights `d ∈ [0,1]`, and an
orthogonal projection `W` commuting with `Q`, such that `P` projects onto the
`u` axes, `Q` acts as `d` on `u` plus the off-diagonal `√(d(1-d))` coupling to
`v`, and `{u, v, ran W}` is a complete orthonormal decomposition of the
space.  Reused FQN: `...RewindAlgebra.jordanTwoProjectors`. -/
theorem source_jordan_normal_form (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P * P = P) (hQs : Q.IsHermitian) (hQi : Q * Q = Q) :
    ∃ (k : ℕ) (u v : Fin k → QState (Fin D)) (d : Fin k → ℝ) (W : Operator D),
      (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧
      (∀ i j, Inner (u i) (u j) = if i = j then 1 else 0) ∧
      (∀ i j, Inner (v i) (v j) = if i = j then
        (if 0 < d i ∧ d i < 1 then 1 else 0) else 0) ∧
      (∀ i j, Inner (u i) (v j) = 0) ∧
      W.IsHermitian ∧ W * W = W ∧ W * Q = Q * W ∧
      (∀ x : QState (Fin D),
          (∑ i, Inner (u i) x • u i + ∑ i, Inner (v i) x • v i) + W *ᵥ x = x) ∧
      (∀ x : QState (Fin D), P *ᵥ x = ∑ i, Inner (u i) x • u i) ∧
      (∀ i, Q *ᵥ (u i) = d i • u i + Real.sqrt (d i * (1 - d i)) • v i) ∧
      (∀ i, Q *ᵥ (v i) = Real.sqrt (d i * (1 - d i)) • u i + (1 - d i) • v i) :=
  jordanTwoProjectors D P Q hPs hPi hQs hQi

end Qatlib.Papers.QMetropolis11.AcceptanceCoin.JordanTwoProjectors
