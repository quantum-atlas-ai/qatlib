/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.ReducedBlocks

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemmaE2Interior — Lemma E.2 (interior maximiser and strict auxiliary inequalities)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Lemma E.2, p. 36
(txt lines 1921-1962), Eqs. (177)-(189).

**Statement.**  Let `(x,y,z)` maximise `F_ε` over `x,y,z ≥ 0`,
`x^2 + y^2 + z^2 = 1`, and let `μ := F_ε(x,y,z)`.  For every `0 < ε < 1`,

```
x > 0,   y > 0,   z > 0,   μ > s,   z > y,
```

and

```
Δ := μ - ε s - s^2/μ = ε s (z/y - 1) > 0.
```

**Paper proof.**  Compactness gives a maximiser; the boundary cases `x = 0`,
`y = 0`, `z = 0` are excluded by the first-order perturbations (180)-(186).  The
interior stationarity (Lagrange) equations are (187), giving after using the
first equation in the other two,

```
μ = s^2/μ + ε s (z/y),    μ = (s^4/μ)(y/z) + ε s (y/z + 1)
```

(Eq. (188)).  Subtracting and using `1 - s^2 = ε` gives Eq. (189), and since
`μ > s` the inequality `z > y` follows, whence Eq. (179).

**Modelling boundary.**  The problem is the reduced variational problem
`max F_ε` over `sphereNN` (`Model/AmplitudeDamping.lean`).  The interior-
maximiser statement (boundary exclusions and the Lagrange multiplier
derivation, Eqs. (177)-(187)) is not formalised; its statement lives in the
branch history of this file.  What is proved here is the *algebraic* content of
Eq. (188) → Eq. (179) and the strict positivity of `Δ` under the stationarity
relation.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- Eq. (188) → Eq. (179), p. 37: if the first stationarity relation
`μ - s^2/μ = ε s (z/y)` holds, then `Δ = μ - ε s - s^2/μ = ε s (z/y - 1)`. -/
theorem source_lemma_E2_delta_identity (μ ε sε z y : ℝ)
    (hstat : μ - sε ^ 2 / μ = ε * sε * (z / y)) :
    μ - ε * sε - sε ^ 2 / μ = ε * sε * (z / y - 1) := by
  have h : ε * sε * (z / y - 1) = ε * sε * (z / y) - ε * sε := by ring
  linarith [h]

/-- Eq. (179), p. 37: under the stationarity relation and `z > y > 0`,
`ε, s > 0`, the quantity `Δ` is strictly positive. -/
theorem source_lemma_E2_delta_pos (μ ε sε z y : ℝ)
    (hε : 0 < ε) (hs : 0 < sε) (hy : 0 < y) (hzy : y < z)
    (hstat : μ - sε ^ 2 / μ = ε * sε * (z / y)) :
    0 < μ - ε * sε - sε ^ 2 / μ := by
  rw [source_lemma_E2_delta_identity μ ε sε z y hstat]
  have h1 : 1 < z / y := (one_lt_div hy).mpr hzy
  have h2 : 0 < z / y - 1 := by linarith
  exact mul_pos (mul_pos hε hs) h2

end Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations
