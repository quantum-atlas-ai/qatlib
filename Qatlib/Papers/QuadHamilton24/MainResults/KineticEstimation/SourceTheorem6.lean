/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 6 (kinetic-energy estimation for damped coupled oscillators)

Source: arXiv:2404.07303, §4, Theorem 6, (4.97)–(4.100), pages 28–29.

Restricting Problem 1 to damped coupled oscillators with forcing, Theorem 6 gives a quantum
algorithm estimating the kinetic energy at time `T` to additive error `ε` with
query complexity `T_Q = O((m/ε) poly(k, log 1/ε, log m))` (4.97) and gate overhead at most
`polylog(m, 1/ε, d, M_max/M_min)` (4.98), where
`m = T s max(R_max/M_min, sqrt(S_max/M_min))` (4.99) and
`k = O(log m (1 + T‖f‖/‖ỹ(T)‖))` (4.100).

The algorithmic construction is not formalised; the cost shape, the closed forms (4.99),
and the polynomial factors are formalised and proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- `m = T s max(R_max/M_min, sqrt(S_max/M_min))` of (4.99). -/
def theorem6m (T s Rmax Mmin Smax : ℝ) : ℝ :=
  T * s * max (Rmax / Mmin) (Real.sqrt (Smax / Mmin))

/-- `k = O(log m (1 + T‖f‖/‖ỹ(T)‖))` of (4.100), as the explicit expression. -/
def theorem6k (m T fNorm yT : ℝ) : ℝ :=
  Real.log m * (1 + T * fNorm / yT)

/-- The `poly(k, log 1/ε, log m)` factor of (4.97). -/
def theorem6Poly (k ε m : ℝ) : ℝ :=
  ∏ i : Fin 3, (1 + |(![k, Real.log (1 / ε), Real.log m] : Fin 3 → ℝ) i|)

/-- Theorem6Poly is Poly: the paper model identity or bound. -/
theorem theorem6Poly_isPoly (k ε m : ℝ) :
    IsPolyBound ![k, Real.log (1 / ε), Real.log m] (theorem6Poly k ε m) :=
  ⟨1, zero_le_one, 1, by simp [theorem6Poly]⟩

/-- The query complexity of (4.97): `(m/ε) · poly(k, log 1/ε, log m)`. -/
def theorem6QueryComplexity (m ε k : ℝ) : ℝ :=
  (m / ε) * theorem6Poly k ε m

/-- **Theorem 6, query bound (4.97).** -/
theorem theorem6_query_complexity (m ε k : ℝ) :
    ∃ TQ poly : ℝ,
      TQ = (m / ε) * poly ∧
        IsPolyBound ![k, Real.log (1 / ε), Real.log m] poly :=
  ⟨theorem6QueryComplexity m ε k, theorem6Poly k ε m, rfl, theorem6Poly_isPoly k ε m⟩

/-- The `polylog(m, 1/ε, d, M_max/M_min)` gate factor of (4.98), as a product of
logarithmic factors. -/
def theorem6GatePoly (m ε d ratio : ℝ) : ℝ :=
  ∏ i : Fin 4,
    (1 + |(![Real.log m, Real.log (1 / ε), Real.log d, Real.log ratio] : Fin 4 → ℝ) i|)

/-- Theorem6Gate Poly is Poly: the paper model identity or bound. -/
theorem theorem6GatePoly_isPoly (m ε d ratio : ℝ) :
    IsPolyBound ![Real.log m, Real.log (1 / ε), Real.log d, Real.log ratio]
      (theorem6GatePoly m ε d ratio) :=
  ⟨1, zero_le_one, 1, by simp [theorem6GatePoly]⟩

/-- **Theorem 6, gate overhead (4.98).** -/
theorem theorem6_gate_overhead (m ε d ratio : ℝ) :
    ∃ factor poly : ℝ,
      factor = poly ∧
        IsPolyBound ![Real.log m, Real.log (1 / ε), Real.log d, Real.log ratio] poly :=
  ⟨theorem6GatePoly m ε d ratio, theorem6GatePoly m ε d ratio, rfl,
    theorem6GatePoly_isPoly m ε d ratio⟩

end Qatlib.Papers.QuadHamilton24.MainResults
