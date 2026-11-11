/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermionicQFT14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults: the total gate count Eq. (20) of arXiv:1404.7115v1

Claim `c001` of the paper layer: the total gate count of the scattering
algorithm satisfies

  `Gtotal = O(ε ^ (-8 - o(1)))` as `ε → 0`, and
  `Gtotal = O(p ^ (9 + o(1)))` as `p → ∞`

(arXiv:1404.7115v1, Eq. (20), p. 7).

The route follows the paper's §2.3 bookkeeping verbatim:

* the two adiabatic state-preparation steps each cost the base of Eq. (16)/(18),
  which becomes `O(ε ^ (-7-o(1)))` after the high-precision substitution
  `a ∼ ε` (`SourceModel.prepBase_highPrecision`), and `O(p ^ (9+o(1)))` after
  `a ∼ 1/p`, `L ∼ p` (`SourceModel.prepBase_highMomentum`);
* the wavepacket excitation step costs `ε ^ (-4-o(1))` (Eq. (19a)) and
  `p ^ (3+o(1))` (Eq. (19b));
* sums keep the dominant exponent (`max 7 4 = 7` and `max 9 3 = 9`);
* in the high-precision limit the `1/ε` postselection repetition factor
  (§2.3, sentence after Eq. (19)) adds one to the exponent: `7 + 1 = 8`;
* in the high-momentum limit the excitation step is lower order and the total
  exponent is `9`.

All theorems in this file are fully proved; there is no `sorry`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FermionicQFT14.MainResults

/-! ## 1. Component bounds -/

/-- Eq. (16)/(18) in the high-precision limit: one adiabatic preparation step is
`O(ε ^ (-7-o(1)))`. This is the `(1 + o(1))`-powered monomial base
`c * ε ^ (-7)` of `SourceModel.highPrecisionPrepGateCount`. -/
theorem highPrecisionPrepGateCount_hasUpperBound {c : ℝ} (hc : 0 ≤ c)
    {η : ℝ → ℝ} (hη : VanishesAtZero η) :
    HasUpperBoundAtZero (highPrecisionPrepGateCount c η) 7 := by
  exact hasUpperBoundAtZero_rpow_one_add_slack (c := c) (e := 7) hc hη

/-- Eq. (19a) in the high-precision limit: the excitation step is
`O(ε ^ (-4-o(1)))`. -/
theorem highPrecisionExciteGateCount_hasUpperBound {c : ℝ} (hc : 0 ≤ c)
    {η : ℝ → ℝ} (hη : VanishesAtZero η) :
    HasUpperBoundAtZero (highPrecisionExciteGateCount c η) 4 := by
  exact hasUpperBoundAtZero_rpow_one_add_slack (c := c) (e := 4) hc hη

/-- Eq. (16)/(18) in the high-momentum limit (`a ∼ 1/p`, `L ∼ p`): one adiabatic
preparation step is `O(p ^ (9+o(1)))`. -/
theorem highMomentumPrepGateCount_hasUpperBound {c : ℝ} (hc : 0 ≤ c)
    {η : ℝ → ℝ} (hη : VanishesAtTop η) :
    HasUpperBoundAtTop (highMomentumPrepGateCount c η) 9 := by
  exact hasUpperBoundAtTop_rpow_one_add_slack (c := c) (e := 9) hc hη

/-- Eq. (19b) in the high-momentum limit: the excitation step is
`O(p ^ (3+o(1)))`. -/
theorem highMomentumExciteGateCount_hasUpperBound {c : ℝ} (hc : 0 ≤ c)
    {η : ℝ → ℝ} (hη : VanishesAtTop η) :
    HasUpperBoundAtTop (highMomentumExciteGateCount c η) 3 := by
  exact hasUpperBoundAtTop_rpow_one_add_slack (c := c) (e := 3) hc hη

/-! ## 2. Sums of the algorithm's steps -/

/-- The two adiabatic preparation steps plus the excitation step, high-precision
limit: sums keep the dominant exponent, `max 7 4 = 7`. -/
theorem highPrecisionSteps_hasUpperBound {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} (hη : VanishesAtZero η) :
    HasUpperBoundAtZero
      (fun ε => 2 * highPrecisionPrepGateCount cprep η ε
        + highPrecisionExciteGateCount cexc η ε) 7 := by
  have htwo : HasUpperBoundAtZero
      (fun ε => 2 * highPrecisionPrepGateCount cprep η ε) 7 :=
    hasUpperBoundAtZero_const_mul 2
      (highPrecisionPrepGateCount_hasUpperBound hcprep hη)
  have hexc : HasUpperBoundAtZero (highPrecisionExciteGateCount cexc η) 4 :=
    highPrecisionExciteGateCount_hasUpperBound hcexc hη
  have hsum := hasUpperBoundAtZero_add htwo hexc
  rwa [show max (7 : ℝ) 4 = 7 by norm_num] at hsum

/-- Two adiabatic preparation steps plus the lower-order excitation step,
high-momentum limit: `max 9 3 = 9`. -/
theorem highMomentumSteps_hasUpperBound {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} (hη : VanishesAtTop η) :
    HasUpperBoundAtTop
      (fun p => 2 * highMomentumPrepGateCount cprep η p
        + highMomentumExciteGateCount cexc η p) 9 := by
  have htwo : HasUpperBoundAtTop
      (fun p => 2 * highMomentumPrepGateCount cprep η p) 9 :=
    hasUpperBoundAtTop_const_mul 2
      (highMomentumPrepGateCount_hasUpperBound hcprep hη)
  have hexc : HasUpperBoundAtTop (highMomentumExciteGateCount cexc η) 3 :=
    highMomentumExciteGateCount_hasUpperBound hcexc hη
  have hsum := hasUpperBoundAtTop_add htwo hexc
  rwa [show max (9 : ℝ) 3 = 9 by norm_num] at hsum

/-! ## 3. Eq. (20) -/

/-- Eq. (20), high-precision branch: the `1/ε` postselection repetition factor of
§2.3 multiplies the steps bound, raising the exponent from `7` to `7 + 1 = 8`.
Hence `Gtotal = O(ε ^ (-8-o(1)))` as `ε → 0`. -/
theorem eq20_highPrecision {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} (hη : VanishesAtZero η) :
    HasUpperBoundAtZero (highPrecisionTotalGateCount cprep cexc η) 8 := by
  have hsteps := highPrecisionSteps_hasUpperBound hcprep hcexc hη
  have hprod : HasUpperBoundAtZero
      (fun ε =>
        (2 * highPrecisionPrepGateCount cprep η ε
          + highPrecisionExciteGateCount cexc η ε) * ε⁻¹) (7 + 1) :=
    hasUpperBoundAtZero_mul hsteps hasUpperBoundAtZero_inv
  rwa [show (7 : ℝ) + 1 = 8 by norm_num] at hprod

/-- Eq. (20), high-momentum branch: the excitation step is lower order than the
two preparation steps, so `Gtotal = O(p ^ (9+o(1)))` as `p → ∞`. -/
theorem eq20_highMomentum {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} (hη : VanishesAtTop η) :
    HasUpperBoundAtTop (highMomentumTotalGateCount cprep cexc η) 9 := by
  have hsum := highMomentumSteps_hasUpperBound hcprep hcexc hη
  exact hsum

/-- **Claim `c001`**, Eq. (20), p. 7 of arXiv:1404.7115v1, in both limits:

  `Gtotal = O(ε ^ (-8-o(1)))` as `ε → 0`, and
  `Gtotal = O(p ^ (9+o(1)))` as `p → ∞`.

`η` is the `o(1)` correction of the Suzuki–Trotter exponent; it vanishes in the
relevant limit. The two gate-count functions are the explicit cost model of
`SourceModel`, built from Eqs. (16), (18) and (19). -/
theorem totalGateCount_eq20 {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} (hη0 : VanishesAtZero η)
    (hηp : VanishesAtTop η) :
    HasUpperBoundAtZero (highPrecisionTotalGateCount cprep cexc η) 8 ∧
    HasUpperBoundAtTop (highMomentumTotalGateCount cprep cexc η) 9 :=
  ⟨eq20_highPrecision hcprep hcexc hη0, eq20_highMomentum hcprep hcexc hηp⟩

end Qatlib.Papers.FermionicQFT14.MainResults
