/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.QuantumIntegration
import Qatlib.Papers.HeatEquation20.MainResults.ClassicalSampling

/-!
# HeatEquation20 — quantum methods (pp. 18–24)

Fixed source: arXiv:2004.06516v2.

* **Theorem 17** (p. 18, eqs. (71)–(72)): quantum linear equations method,
  cost `O(B L^d 3^{-d/2} log²((Tdα)^{d/2+2}(ζ/ε)^{d/2+1})
  log³((Tdα)²ζ/ε) log²B log log B)`, with the piecewise `B` of (72).
* **Theorem 19** (p. 21, eq. (90)): fast-forwarded random-walk method,
  cost `O((d^{5/2}Tαζ^{1/2}/ε^{3/2})(100L²dTαζ/(3^5ε))^{d/4}
  log(L²dαζT/ε)√log(L²dαζT/ε))`.
* **Theorem 20** (p. 21, eqs. (92)–(93)): diagonalisation-and-postselection
  method, cost `O((100L²dTαζ/3^5)^{d/4} ε^{-d/4-1} (log²D)
  (log log D + log(T²d²α²ζ/ε)))`, with the `D` of (93).
* **Theorem 21** (p. 23): amplitude-estimation integration, cost
  `O((Tαd³ζ(αT+L²)/ε²) log(L√(dζ(αT+L²)/ε)))`.
* **Theorem 22** (p. 24): amplitude-amplification integration, cost
  `O((d/ε) log(T L α d^{5/2} ζ^{3/2} ((αT+L²)/ε)^{3/2}))`.

Following the repository convention for algorithmic complexity claims, the
displayed runtimes are introduced as explicit real-valued definitions.  The
recording theorems were not carried into this port: their earlier
formalisations contained unproven gaps (the quantum algorithms of Theorems 15,
16 and 18 of the cited literature and the repetition/amplitude-estimation
arguments are not reconstructed in Lean) and were dropped; the claims remain
registered in `metadata/papers/HeatEquation20.json`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators

/-! ## Theorem 17 (pp. 18, eqs. (71)–(72)) -/

/-- The piecewise constant `B` of Theorem 17, eq. (72), p. 18. -/
def thm17B (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  if d = 1 then
    (T * α) ^ ((5 : ℝ) / 2) * ζ ^ ((3 : ℝ) / 2) / ε ^ ((5 : ℝ) / 2)
      * (L + Real.sqrt (T * α))
  else if d = 2 then
    (T * α) ^ ((5 : ℝ) / 2) * ζ ^ ((3 : ℝ) / 2) * L / ε ^ ((5 : ℝ) / 2)
      * Real.sqrt (Real.log (T * L ^ 2 * α * ζ / ε))
  else
    (T * α) ^ ((d : ℝ) / 4 + 2) * L ^ ((d : ℝ) / 2) * (d : ℝ) ^ ((d : ℝ) / 2 + 2)
      * ζ ^ ((d : ℝ) / 4 + 1)
      * (Real.sqrt 20 * (3 : ℝ) ^ (-(5 : ℝ) / 4) * (Real.pi : ℝ) ^ (-(1 : ℝ) / 4)) ^ d
      / ε ^ ((d : ℝ) / 4 + 2)

/-- The displayed complexity (71) of Theorem 17, p. 18, with the parameter `B`. -/
def thm17Bound (d : ℕ) (T L α ζ ε B : ℝ) : ℝ :=
  B * L ^ d * (3 : ℝ) ^ (-(d : ℝ) / 2)
    * (Real.log ((T * (d : ℝ) * α) ^ ((d : ℝ) / 2 + 2) * (ζ / ε) ^ ((d : ℝ) / 2 + 1))) ^ 2
    * (Real.log ((T * (d : ℝ) * α) ^ 2 * ζ / ε)) ^ 3
    * (Real.log B) ^ 2 * Real.log (Real.log B)

/-- The cost model of the quantum linear-equations method of Theorem 17: the
displayed bound (71) evaluated at the piecewise `B` of (72). -/
def thm17Cost (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  thm17Bound d T L α ζ ε (thm17B d T L α ζ ε)

/-- The displayed complexity (90) of Theorem 19, p. 21. -/
def thm19Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  ((d : ℝ) ^ ((5 : ℝ) / 2) * T * α * Real.sqrt ζ / ε ^ ((3 : ℝ) / 2))
    * ((100 * L ^ 2 * (d : ℝ) * T * α * ζ / ((3 : ℝ) ^ 5 * ε)) ^ ((d : ℝ) / 4))
    * Real.log (L ^ 2 * (d : ℝ) * α * ζ * T / ε)
    * Real.sqrt (Real.log (L ^ 2 * (d : ℝ) * α * ζ * T / ε))

/-- The cost model of the fast-forwarded random-walk method of Theorem 19. -/
def thm19Cost (d : ℕ) (T L α ζ ε : ℝ) : ℝ := thm19Bound d T L α ζ ε

/-- The parameter `D` of Theorem 20, eq. (93), p. 21. -/
def thm20D (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  (Real.sqrt 10 * L / (3 : ℝ) ^ ((5 : ℝ) / 4)) ^ d
    * (T * (d : ℝ) * α) ^ ((d : ℝ) / 4 + 2) * ζ ^ ((d : ℝ) / 4 + 1)
    / ε ^ ((d : ℝ) / 4 + 2)

/-- The displayed complexity (92) of Theorem 20, p. 21. -/
def thm20Bound (d : ℕ) (T L α ζ ε D : ℝ) : ℝ :=
  (100 * L ^ 2 * (d : ℝ) * T * α * ζ / (3 : ℝ) ^ 5) ^ ((d : ℝ) / 4)
    * ε ^ (-(d : ℝ) / 4 - 1)
    * (Real.log D) ^ 2
    * (Real.log (Real.log D) + Real.log (T ^ 2 * (d : ℝ) ^ 2 * α ^ 2 * ζ / ε))

/-- The cost model of Theorem 20: the displayed bound (92) at the parameter `D` of (93). -/
def thm20Cost (d : ℕ) (T L α ζ ε : ℝ) : ℝ := thm20Bound d T L α ζ ε (thm20D d T L α ζ ε)

/-- The displayed complexity of Theorem 21, p. 23. -/
def thm21Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  (T * α * (d : ℝ) ^ 3 * ζ * (α * T + L ^ 2) / ε ^ 2)
    * Real.log (L * Real.sqrt ((d : ℝ) * ζ * (α * T + L ^ 2) / ε))

/-- The cost model of the amplitude-estimation integration of Theorem 21:
`O(1/ε)` repetitions (quadratic improvement over the `1/ε²` of Theorem 10),
each a chain of Lemma 9 samples. -/
def thm21Cost (d m n : ℕ) (ε : ℝ) : ℝ := (4 / ε) * lemma9Cost d m n

/-- The displayed complexity of Theorem 22, p. 24. -/
def thm22Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  ((d : ℝ) / ε)
    * Real.log (T * L * α * (d : ℝ) ^ ((5 : ℝ) / 2) * ζ ^ ((3 : ℝ) / 2)
        * ((α * T + L ^ 2) / ε) ^ ((3 : ℝ) / 2))

/-- The cost model of the amplitude-amplification integration of Theorem 22:
`O(1/ε)` repetitions of the fast sampler of Lemma 11. -/
def thm22Cost (d n m : ℕ) (ε : ℝ) : ℝ := (1 / ε) * lemma11Cost d n m

end Qatlib.Papers.HeatEquation20.MainResults
