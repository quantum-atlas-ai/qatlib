/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDataFit12.SparseHHL.DataFittingDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Source cost vocabulary for the QDataFit12 active claims

Fixed paper: Wiebe–Braun–Lloyd, *Quantum Data Fitting*, arXiv:1204.5242v2 (3 Jul 2012).

This module fixes the exact scalar vocabulary that the three active claims of the paper
talk about, so that the claim modules can state their conclusions without re-deriving the
cost expressions:

* `fitQualityCost` — Algorithm 2, Eq. (14): `Õ(log N · s³κ⁴/(εδ²))`;
* `tomographyHeadlineCost` — the compressed-sensing tomography term Eq. (17):
  `Õ(log N · s³ M′²κ⁶/ε³)`;
* `compressedSensingMeasurements` — the total number of compressed-sensing measurements
  `M′²log(M′)²/ε²` quoted on p.5;
* `sampleCountForDelta` — the `O(1/δ²)` swap-test sample count of Algorithm 2 (p.4);
* `swapTestOneProbability` — the swap-test outcome-1 probability `(1 − |⟨y|ψ⟩|²)/2` (p.4).

The exact headline cost expressions `fitHeadlineCost`, `simulationHeadlineCost` and
`readoutHeadlineCost` are already fixed in `DataFittingNextModel`; the definitions here
only add the pieces that the paper states separately for Algorithms 2 and 3.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims

open Qatlib.Papers.QDataFit12.SparseHHL Qatlib.Papers.QDataFit12.SparseHHL

/-- Algorithm 2 (Estimating Fit Quality), Eq. (14): the headline query complexity
`Õ(log(N) · s³ κ⁴ / (ε δ²))`. -/
noncomputable def fitQualityCost (N s κ : ℕ) (ε δ : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 4 / (ε * δ ^ 2)

/-- Algorithm 3, Eq. (17): the compressed-sensing tomography term
`Õ(log(N) · s³ M′² κ⁶ / ε³)`. -/
noncomputable def tomographyHeadlineCost (N s κ M' : ℕ) (ε : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) ^ 3 * ((M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3)

/-- p.5, §3: the total number of compressed-sensing measurements
`M′² log(M′)² / ε²` — `M′ log(M′)²` settings with `M′/ε²` measurements per setting. -/
noncomputable def compressedSensingMeasurements (M' : ℕ) (ε : ℝ) : ℝ :=
  (M' : ℝ) ^ 2 * Real.log (M' + 1) ^ 2 / ε ^ 2

/-- p.4, §2: the `O(1/δ²)` swap-test sample count needed to estimate the overlap to
error `δ` at failure probability `η` (Chebyshev, variance at most `1/4`). -/
noncomputable def sampleCountForDelta (δ η : ℝ) : ℝ :=
  1 / (4 * δ ^ 2 * η)

/-- p.4, §2: the swap-test outcome-1 probability for overlap squared `c = |⟨y|ψ⟩|²`,
namely `(1 − c)/2`. -/
noncomputable def swapTestOneProbability (c : ℝ) : ℝ := (1 - c) / 2

end Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims
