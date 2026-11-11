/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.Model

set_option backward.isDefEq.respectTransparency false

/-!
# arXiv:2606.03407v1 — shared model of the hyperbolic block

Fixed version: **arXiv:2606.03407v1**, §5 (PDF pp.33–44).

The hyperbolic PDE is the Klein–Gordon-type equation

`u_tt = Δu + Σ_l c_l u_{x_l} − c₀² u + f(x,t)`

with the same mixed Dirichlet/Neumann/periodic boundary conditions (56–58) as
the parabolic problem.  After the method of lines and the similarity transform
the semi-discrete system is the second-order linear ODE (60)

`w_tt = −Ã w − c₀² w + P b(t)`,

which is written as the first-order extended system `W' = i H W + B̃` with the
Hermitian matrix `H` of (65).  This file records the algebraic objects shared
by the hyperbolic claims: the semi-discrete hyperbolic operator matrix and the
top-left block of the extended propagator used in Lemma 14.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source

open Matrix
open scoped BigOperators

/-- The semi-discrete hyperbolic spatial operator `−(Ã + c₀² I)` appearing in
the second-order ODE (60) (arXiv:2606.03407v1, §5.3, PDF p.38). -/
noncomputable def hyperbolicOpMatrix {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (c0 : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  -(A + (c0 ^ 2) • (1 : Matrix (Fin N) (Fin N) ℝ))

end Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source
