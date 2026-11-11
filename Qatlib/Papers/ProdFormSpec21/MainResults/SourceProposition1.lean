/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProdFormSpec21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 (Trotter error decomposition) — paper-layer Lean

Source: *Spectral Analysis of Product Formulas for Quantum Simulation*,
arXiv:2102.12655v2, **Proposition 1**, p.6–7, Eq (34)–(35); proof in Appendix F
(p.13–14).

Paper statement.  Worst-case error of `M`-step Trotterization of the adiabatic
evolution, measured in trace distance, splits as

  `ε_tro ≤ ε'_adb + ε'_tot`                                  (Eq (34))

into an **adiabatic** error `ε'_adb = O(D/(Tlam³))` (`D = ‖Hi − Hf‖`) and a
**Trotter** error `ε'_tot`; combining Lemma 2 with Lemma 4 gives the leading bound

  `ε'_tot ≲ (1/(Tlam³)) (D + 3C₁ T/(2M))²`                     (Eq (35))

in the regime `D/lam ≫ 1`, `(C₀ + 3D/2) T < M/4`.

Appendix F derives Eq (34) by the triangle inequality in matrix (Schatten-1) norm,
`‖Ad · P · Ad† − Tt · P · Tt†‖ ≤ ‖Ad P Ad† − P‖ + ‖P − Tt P Tt†‖`, and Eq (35) by
inserting the Lemma 2 (`ε_adb`) and Lemma 4 (`ε_tot = O(M δt²) = O(1/M)` at
`δt = O(1/M)`) estimates.

We prove Eq (34) outright as the matrix triangle inequality, and Eq (35) as the
combination step taking the Lemma 2 / Lemma 4 estimates as hypotheses (the paper's
own "combine Lemma 2 with Lemma 4").  The analytic derivation of those two
estimates is the residual (annotated below); no active Claim corresponds to
Lemma 2 / Lemma 4 individually, so Proposition 1's content is the combination.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The **adiabatic error** `‖Ad(t) P Ad(t)† − P̃‖` of the ideal adiabatic evolution
`Ad` against the target projector `P̃`. -/
noncomputable def adiabaticError (Ad P Pf : Matrix I I ℂ) : ℝ :=
  ‖Ad * P * Adᴴ - Pf‖

/-- The **Trotter error** `‖Tt(t) P Tt(t)† − P̃‖` of the Trotterized evolution `Tt`
against the target projector `P̃`. -/
noncomputable def trotterErr (Tt P Pf : Matrix I I ℂ) : ℝ :=
  ‖Tt * P * Ttᴴ - Pf‖

/-- The **total Trotterization error** `‖Ad P Ad† − Tt P Tt†‖` between the ideal and
Trotterized evolutions in matrix (operator) norm. -/
noncomputable def totalTrotterError (Ad Tt P : Matrix I I ℂ) : ℝ :=
  ‖Ad * P * Adᴴ - Tt * P * Ttᴴ‖

/-- **Proposition 1, Eq (34) — the triangle split `ε_tro ≤ ε'_adb + ε'_tot`.**
For any ideal adiabatic evolution `Ad`, Trotterized evolution `Tt`, initial projector
`P` and target projector `P̃`,
`‖Ad P Ad† − Tt P Tt†‖ ≤ ‖Ad P Ad† − P̃‖ + ‖Tt P Tt† − P̃‖`,
by the triangle inequality
`Ad P Ad† − Tt P Tt† = (Ad P Ad† − P̃) + (P̃ − Tt P Tt†)`.  -/
theorem proposition1_triangle (Ad Tt P Pf : Matrix I I ℂ) :
    totalTrotterError Ad Tt P
      ≤ adiabaticError Ad P Pf + trotterErr Tt P Pf := by
  have hsplit : Ad * P * Adᴴ - Tt * P * Ttᴴ
      = (Ad * P * Adᴴ - Pf) + (Pf - Tt * P * Ttᴴ) := by abel
  unfold totalTrotterError adiabaticError trotterErr
  rw [hsplit]
  have h := norm_add_le (Ad * P * Adᴴ - Pf) (Pf - Tt * P * Ttᴴ)
  rw [norm_sub_rev Pf (Tt * P * Ttᴴ)] at h
  exact h

/-- **Proposition 1, Eq (35) — the leading `ε'_tot` bound.**  Taking the Lemma 2
adiabatic estimate `ε'_adb ≤ D²/(Tlam³)` and the Lemma 4 Trotter estimate
`ε'_tot ≤ C₁²T/(M²lam³)` (both in the regime `D/lam ≫ 1`,
`(C₀ + 3D/2)T < M/4`), the combined error is

  `ε_tro ≤ D²/(Tlam³) + C₁²T/(M²lam³)`,

which is the `O((1/(Tlam³))(D + 3C₁T/(2M))²)`-type leading term advertised in Eq (35)
in the `D ≫ 1` regime, since the cross term `3C₁D/(Mlam³)` is subleading.

Residual (annotated): deriving `hadb` and `htot` from Lemmas 2 and 4 is the analytic
core (Appendix F); they are not themselves active Claims, so we state Eq (35) as the
combination step with those estimates as hypotheses. -/
theorem proposition1_leading_bound
    (εtro εadb εtot D C1 lam T M : ℝ)
    (hlam : 0 < lam) (hD : 0 < D) (hC1 : 0 < C1) (hT : 0 < T) (hM : 0 < M)
    (htri : εtro ≤ εadb + εtot)
    (hadb : εadb ≤ D ^ 2 / (T * lam ^ 3))
    (htot : εtot ≤ C1 ^ 2 * T / (M ^ 2 * lam ^ 3)) :
    εtro ≤ D ^ 2 / (T * lam ^ 3) + C1 ^ 2 * T / (M ^ 2 * lam ^ 3) := by
  linarith [htri, hadb, htot]

end Qatlib.Papers.ProdFormSpec21.MainResults
