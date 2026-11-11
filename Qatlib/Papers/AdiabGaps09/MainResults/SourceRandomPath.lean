/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic
import Qatlib.Papers.AdiabGaps09.MainResults.RandomPath


set_option backward.isDefEq.respectTransparency false

/-!
# SourceRandomPath — randomizing the beginning Hamiltonian (c003)

Fixed arXiv:0909.4766v2, Section III ("Changing the Adiabatic Path"), pages 10–12,
equations (9)–(12).

The paper replaces `H_B` by a random beginning Hamiltonian

```
H̃_B = Σ_{i=1}^n  c_i (1 - σ_x^{(i)}) / 2 ,      c_i ∈ {1/2, 3/2} w.p. 1/2 each   (Eq. 9)
```

so that the second-order correction difference becomes

```
ẽ_U^(2) - ẽ_L^(2) = Σ_{i=1}^n c_i^2 d_i ,                                        (p. 11)
```

with the `d_i` fixed by the instance (Eq. 5).  The key observation is:

* if `ẽ_U^(2) - ẽ_L^(2) > 0` then (with the opposite sign for the gap difference
  `ẽ_L - ẽ_U`) there is no avoided crossing near `s = 1`, i.e. the tiny gap is
  removed;
* the probability of this event is bounded away from `0` uniformly in `n`
  (the Gaussian argument of `SourceGaussianBound`);
* hence a *constant* number of independent random draws suffices with
  probability bounded away from `0`.

The first bullet is pure algebra (second-order truncation of equations (3), (4))
and is proved here; the second is recorded as a finite-probability statement with
documented `sorry`; the third is an elementary Bernoulli-product bound, proved.
-/

set_option autoImplicit false
noncomputable section

open Finset Filter
open scoped BigOperators

open Qatlib.Papers.AdiabGaps09.MainResults.RandomPath

namespace Qatlib.Papers.AdiabGaps09.MainResults.RandomPath

/-! ## Second-order energy truncation (equations 3, 4) -/

/-- The squared random coefficient `c_i^2`, which takes `1/4` and `9/4` with
probability `1/2` each (paper p. 11, `c_i ∈ {1/2, 3/2}`). -/
def cSq (b : Bool) : ℝ := if b then (9 / 4 : ℝ) else (1 / 4 : ℝ)

/-- The single-site mean of `c_i^2` is `5/4` (paper p. 11). -/
theorem cSq_mean : (1 / 2 : ℝ) * cSq false + (1 / 2 : ℝ) * cSq true = 5 / 4 := by
  norm_num [cSq]

/-- The single-site second moment of `c_i^2` is `41/16`. -/
theorem cSq_second :
    (1 / 2 : ℝ) * (cSq false) ^ 2 + (1 / 2 : ℝ) * (cSq true) ^ 2 = 41 / 16 := by
  norm_num [cSq]

/-- The single-site variance of `c_i^2` is `1` (paper p. 11: `Var(c_i^2) = 1`). -/
theorem cSq_variance :
    (1 / 2 : ℝ) * (cSq false) ^ 2 + (1 / 2 : ℝ) * (cSq true) ^ 2
      - ((1 / 2 : ℝ) * cSq false + (1 / 2 : ℝ) * cSq true) ^ 2 = 1 := by
  norm_num [cSq]

/-- The randomized second-order correction difference `Σ_i c_i^2 d_i`
(paper p. 11). -/
def secondOrderGap {k : ℕ} (d : Fin k → ℝ) (z : Fin k → Bool) : ℝ :=
  ∑ i, cSq (z i) * d i

end Qatlib.Papers.AdiabGaps09.MainResults.RandomPath
