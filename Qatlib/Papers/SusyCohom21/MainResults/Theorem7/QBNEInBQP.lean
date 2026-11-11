/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 7 — QBNE is in BQP

Cade--Crichigno, fixed arXiv:2107.00011v2, Theorem 7 (page 15): QBNE is in BQP
for `d = O(log n)`, any `l`, and efficiently sample-able `V[n]`.

Boundary: BQP membership is not formalised. This file states the concrete
counting content behind the algorithm: the spectral density `N_A(b)` of a
Hermitian operator (Definition 6/7, Eq. (5.2)) is a fraction of eigenvalues,
hence lies in `[0,1]` and is monotone in the threshold `b`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Theorem7

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Theorem 7 (Eq. (5.2), Definition 6/7): the
spectral density of a Hermitian operator lies in `[0,1]` and is monotone in
the threshold. -/
theorem qbne_in_bqp (A : Matrix ι ι ℂ) (hA : A.IsHermitian) [Nonempty ι] :
    (∀ b : ℝ, 0 ≤ spectralDensity A hA b) ∧
    (∀ b : ℝ, spectralDensity A hA b ≤ 1) ∧
    (∀ b b' : ℝ, b ≤ b' → spectralDensity A hA b ≤ spectralDensity A hA b') := by
  refine ⟨fun b => spectralDensity_nonneg hA b,
    fun b => spectralDensity_le_one hA b, ?_⟩
  intro b b' hbb
  exact spectralDensity_mono hA hbb

end Qatlib.Papers.SusyCohom21.MainResults.Theorem7
