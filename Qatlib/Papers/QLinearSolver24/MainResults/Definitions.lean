/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver24 — shared definitions of the paper layer

Fixed source: *A shortcut to an optimal quantum linear system solver*,
arXiv:2406.12086 (the version pinned for card `QLinearSolver24`, PR #731).

This module fixes the paper's symbols so that every claim module of
`QuantumAlgorithmDev.Papers.QLinearSolver24.MainResults` refers to one and the
same object:

* the Chebyshev kernel-projection filter `F_{Δ,ℓ}` of Eq. (52) (p. 19);
* the kernel-reflection polynomial `K_{Δ,ℓ}` of Eq. (62) (p. 21);
* the degree choices of Eq. (51) (p. 19) and Eq. (72) (p. 22);
* the angle `θ_t = arctan(‖x‖/t)` of Theorem 1 (p. 22);
* the numerical query-count bounds displayed in Corollary 1 (Eq. (81)),
  Lemma 4 (Eq. (82)–(84)), Lemma 5 (Eq. (103)–(105)), Theorem 2 (Eq. (118)),
  Theorem 3 (Eq. (129)) and Theorem 4 (Eq. (133)).

Nothing here asserts an algorithm; the modules state the paper's conclusions
as theorems about these quantities and prove the analytic/algebraic steps that
the paper's own proofs carry out.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults

open Polynomial

/-- `chebT ℓ x` is the Chebyshev polynomial of the first kind `T_ℓ` evaluated
at `x` (paper Eq. (53), p. 19). -/
def chebT (ℓ : ℕ) (x : ℝ) : ℝ := (Polynomial.Chebyshev.T ℝ (ℓ : ℤ)).eval x

/-- The Chebyshev argument of the kernel-projection filter,
`(1 + Δ² - 2x²)/(1 - Δ²)` (paper Eq. (52), p. 19). -/
def filterArg (Δ x : ℝ) : ℝ := (1 + Δ ^ 2 - 2 * x ^ 2) / (1 - Δ ^ 2)

/-- The normalising denominator `T_ℓ((1 + Δ²)/(1 - Δ²))` of Eq. (52). -/
def filterDenom (Δ : ℝ) (ℓ : ℕ) : ℝ := chebT ℓ ((1 + Δ ^ 2) / (1 - Δ ^ 2))

/-- The kernel-projection filter `F_{Δ,ℓ}` of Eq. (52), p. 19. -/
def F (Δ : ℝ) (ℓ : ℕ) (x : ℝ) : ℝ := chebT ℓ (filterArg Δ x) / filterDenom Δ ℓ

/-- The kernel-reflection polynomial `K_{Δ,ℓ}` of Eq. (62), p. 21, written in
the equivalent expanded form `(2T_ℓ(z(x)) - D_Δ + 1)/(D_Δ + 1)` where
`D_Δ = T_ℓ((1 + Δ²)/(1 - Δ²))`.  It agrees with
`(2 F_{Δ,ℓ}(x) - 1 + F_{Δ,ℓ}(Δ))/(1 + F_{Δ,ℓ}(Δ))` because
`F_{Δ,ℓ}(Δ) = 1 / D_Δ`. -/
def K (Δ : ℝ) (ℓ : ℕ) (x : ℝ) : ℝ :=
  (2 * chebT ℓ (filterArg Δ x) - filterDenom Δ ℓ + 1) / (filterDenom Δ ℓ + 1)

/-- The degree choice of Eq. (51) (p. 19) for accuracy parameter `η` and filter
width `Δ`. -/
def kpDegree (Δ η : ℝ) : ℕ :=
  Nat.ceil (Real.arcosh η⁻¹ / Real.arcosh ((1 + Δ ^ 2) / (1 - Δ ^ 2)))

/-- The degree choice of Eq. (72) (p. 22): `Δ = κ⁻¹`. -/
def algorithm1Degree (κ η : ℝ) : ℕ :=
  Nat.ceil (Real.arcosh η⁻¹ / Real.arcosh ((1 + κ ^ (-2 : ℤ)) / (1 - κ ^ (-2 : ℤ))))

/-- The angle `θ_t = arctan(‖x‖/t)` of Theorem 1 (p. 22). -/
def theta (t xnorm : ℝ) : ℝ := Real.arctan (xnorm / t)

/-- The `KP` precision `η_ΚΡ = ε√(1-μ²)/(μ√(1-ε²))` of Eq. (116), p. 29. -/
def etaKP (ε μ : ℝ) : ℝ := ε * Real.sqrt (1 - μ ^ 2) / (μ * Real.sqrt (1 - ε ^ 2))

/-- The parameter `μ = η/(1-η) · √(3 + 2 ln((R²+L²)/(2L²)))` of Eq. (117),
p. 29. -/
def muOfEta (η L R : ℝ) : ℝ :=
  η / (1 - η) * Real.sqrt (3 + 2 * Real.log ((R ^ 2 + L ^ 2) / (2 * L ^ 2)))

/-- `2^{-d}` as a real number, used for the discretisation error in Lemma 5
(Eq. (103)–(105), p. 28). -/
def negPowTwo (d : ℕ) : ℝ := (1 / 2 : ℝ) ^ d

/-- The expected-query bound of Corollary 1, Eq. (81), p. 24. -/
def corollary1QueryBound (β κ ε : ℝ) : ℝ :=
  ((β ^ 2 + 1) ^ 2 / β ^ 2) *
    ((1 + ε / (2 * Real.sqrt (β ^ 2 + 1))) /
      (1 - ε / (2 * Real.sqrt (β ^ 2 + 1)))) ^ 2 *
    ((Nat.ceil (κ / 2 * Real.log (4 * Real.sqrt (β ^ 2 + 1) / ε)) : ℕ) : ℝ)

/-- The success-probability lower bound of Lemma 4, Eq. (82), p. 25. -/
def lemma4SuccessLower (η L R : ℝ) : ℝ :=
  (1 - η) ^ 2 / ((1 + η) ^ 2 * (Real.log (R / L) + 1))

/-- The bad-estimate probability upper bound of Lemma 4, Eq. (83), p. 25. -/
def lemma4BadEstimateBound (η L R β : ℝ) : ℝ :=
  (1 + η) ^ 2 / (1 - η) ^ 2 * (4 / (β ^ 2 + 1)) +
    (2 * η ^ 2 * (2 * Real.log (R / L) + 1 - 4 * Real.log β)) / (1 - η) ^ 2

/-- The output-overlap lower bound of Lemma 4, Eq. (84), p. 25. -/
def lemma4OverlapBound (η L R : ℝ) : ℝ :=
  1 - (2 * η ^ 2 / (1 - η) ^ 2) * (3 / 2 + Real.log ((R ^ 2 + L ^ 2) / (2 * L ^ 2)))

/-- The query-count bound of Lemma 5, Eq. (105), p. 28. -/
def lemma5QueryBound (η L R δ κ : ℝ) (d : ℕ) : ℝ :=
  (2 * ((Nat.ceil
      (((1 + η) * Real.sqrt (Real.log (R / L) + 1)) / (2 * (1 - η)) *
        (1 - (Real.log (R / L)) ^ 2 * negPowTwo (d + 1)) ^ (-(1 / 2 : ℝ)) *
        Real.log (2 / Real.sqrt δ) - 1 / 2) : ℕ) : ℝ) + 1) *
    2 * ((Nat.ceil (κ / 2 * Real.log (2 / η)) : ℕ) : ℝ)

/-- The query-count bound of Theorem 2, Eq. (118), p. 30, with the KP
precision of Eq. (116)/(120). -/
def theorem2QueryBound (η L R ε κ : ℝ) : ℝ :=
  (2 * (1 + η) ^ 2 * (Real.log (R / L) + 1)) / (1 - η) ^ 2 *
      ((Nat.ceil (κ / 2 * Real.log (2 / η)) : ℕ) : ℝ) +
    (1 / (1 - η ^ 2 / (1 - η) ^ 2 * (3 + 2 * Real.log ((R ^ 2 + L ^ 2) / (2 * L ^ 2))))) *
      (2 * ((Nat.ceil (κ / 2 * Real.log (2 / etaKP ε (muOfEta η L R))) : ℕ) : ℝ))

/-- The query-count bound of Theorem 3, Eq. (129), p. 31, with the KP
precision of Eq. (116)/(120). -/
def theorem3QueryBound (η L R δ ε κ : ℝ) (d : ℕ) : ℝ :=
  ((1 / (1 - δ)) *
      (2 * ((Nat.ceil
          (((1 + η) * Real.sqrt (Real.log (R / L) + 1)) / (2 * (1 - η)) *
            (1 - (Real.log (R / L)) ^ 2 * negPowTwo (d + 1)) ^ (-(1 / 2 : ℝ)) *
            Real.log (2 / Real.sqrt δ) - 1 / 2) : ℕ) : ℝ) + 1) *
        2 * ((Nat.ceil (κ / 2 * Real.log (2 / η)) : ℕ) : ℝ) +
      2 * ((Nat.ceil (κ / 2 * Real.log (2 / etaKP ε (muOfEta η L R))) : ℕ) : ℝ)) /
    (1 - η ^ 2 / (1 - η) ^ 2 *
      (3 + 2 * Real.log ((R ^ 2 + L ^ 2) / (2 * L ^ 2)) + (Real.log (R / L)) ^ 2 * negPowTwo (d - 1)) *
      (1 - (Real.log (R / L)) ^ 2 * negPowTwo (d + 1))⁻¹)

/-- The query-count bound of Theorem 4, Eq. (133), p. 32. -/
def theorem4QueryBound (κ ε : ℝ) : ℝ :=
  56.0 * κ + 1.05 * κ * Real.log (Real.sqrt (1 - ε ^ 2) / ε) +
    2.78 * (Real.log κ) ^ 3 + 3.17

end Qatlib.Papers.QLinearSolver24.MainResults
