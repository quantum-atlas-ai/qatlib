/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeProd19.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1: differentiation rule for the adjoint representation

Childs--Su--Tran--Wiebe--Zhu, *Nearly optimal lattice simulation by product formulas*,
fixed arXiv:1901.00564v2, Proposition 1, p.6, Eq. (40).

The statement is over an arbitrary complex Banach algebra, which instantiates both
bounded operators on a finite-dimensional Hilbert space and the matrix model of
`SourceModel`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatticeProd19.MainResults.AdjointCalculus

open Qatlib.Papers.LatticeProd19.MainResults.SourceModel

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- Proposition 1, Eq. (40), p.6: the derivative of `t ↦ Ad_{e^{tX}}(Y(t))` is
`Ad_{e^{tX}}(ad_X(Y(t))) + Ad_{e^{tX}}(Y'(t))`.  Here `AdExp X t Z = e^{tX} Z e^{-tX}`
and `ad X Z = X Z - Z X` are the paper's `Ad` and `ad` (Eqs. (38)--(39), p.6). -/
theorem proposition1_differentiation_rule
    (X : 𝔸) (Y : ℝ → 𝔸) (hY : ContDiff ℝ ⊤ Y) :
    deriv (fun s : ℝ => AdExp X s (Y s))
      = fun s => AdExp X s (ad X (Y s)) + AdExp X s (deriv Y s) := by
  funext t
  have hYd : DifferentiableAt ℝ Y t :=
    (hY.differentiable (by simp)).differentiableAt
  exact (AdExp_hasDerivAt X Y (deriv Y t) t hYd.hasDerivAt).deriv

end Qatlib.Papers.LatticeProd19.MainResults.AdjointCalculus
