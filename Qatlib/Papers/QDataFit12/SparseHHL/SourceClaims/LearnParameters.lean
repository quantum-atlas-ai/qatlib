/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims.SourceCostModel
import Qatlib.Papers.QDataFit12.SparseHHL.DataFitting

set_option backward.isDefEq.respectTransparency false

/-!
# Claim c002 — Algorithm 3 (Learning λ), query complexity

Fixed paper: Wiebe–Braun–Lloyd, *Quantum Data Fitting*, arXiv:1204.5242v2 (3 Jul 2012).

Source: p.5, §3 "Learning λ". The algorithm prepares `|λ⟩` by Algorithm 1, measures it
`O(M′)` times to select the `M′` most significant fit functions, reconstructs `|λ⟩` by
compressed-sensing tomography to precision `ε`, and finally estimates the fit quality by
Algorithm 2 to precision `δ`. The display on p.5 gives

```
Õ( log(N) · s³ · (κ⁴/(ε δ²) + M′²κ⁶/ε³) ) .
```

The two summands are exactly Eq. (16) (the `I(F)⁻¹I(F†)` preparation, times `1/δ²` for the
Algorithm-2 sampling) and Eq. (17) (the tomography `log N · s³ M′²κ⁶/ε³`). This module states
the total cost, proves the decomposition, and proves the compressed-sensing measurement
budget `M′²log(M′)²/ε²` of p.5.

The cost `readoutHeadlineCost` is already fixed in the reusable model
`Qatlib.Papers.QDataFit12.SparseHHL`; the monotonicity in `N, s, κ, M′` is the
reusable theorem `clause23_readout_headline_mono`, which this module reuses.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims

open Qatlib.Papers.QDataFit12.SparseHHL

/-! ## §1 The total cost and its decomposition into (17) + (16) -/

/-- **c002 cost decomposition.**  The Algorithm-3 total cost of p.5 is the sum of the
Algorithm-2 quality term `log(N)·s³κ⁴/(εδ²)` (Eq. (16) multiplied by `1/δ²`) and the
compressed-sensing tomography term `log(N)·s³M′²κ⁶/ε³` (Eq. (17)). -/
theorem readoutHeadlineCost_eq_fitQuality_add_tomography
    (N s κ M' : ℕ) (ε δ : ℝ) :
    readoutHeadlineCost N s κ M' ε δ
      = fitQualityCost N s κ ε δ + tomographyHeadlineCost N s κ M' ε := by
  unfold readoutHeadlineCost fitQualityCost tomographyHeadlineCost
  have h : Real.log (N + 1) * (s : ℝ) ^ 3 *
        ((κ : ℝ) ^ 4 / (ε * δ ^ 2) + (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3)
      = Real.log (N + 1) * (s : ℝ) ^ 3 * ((κ : ℝ) ^ 4 / (ε * δ ^ 2))
        + Real.log (N + 1) * (s : ℝ) ^ 3 * ((M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3) := by
    ring
  rw [h]; ring

/-! ## §2 The compressed-sensing measurement budget of p.5 -/

/-- **c002 compressed-sensing settings times per-setting count.**  The p.5 statement
`M′·log(M′)²` settings with `M′/ε²` measurements per setting totals `M′²log(M′)²/ε²`. -/
theorem compressedSensingMeasurements_eq_settings_mul_perSetting
    (M' : ℕ) (ε : ℝ) :
    compressedSensingMeasurements M' ε
      = conciseTomographySettings M' * ((M' : ℝ) / ε ^ 2) := by
  unfold compressedSensingMeasurements conciseTomographySettings
  ring

/-- **c002 the total compressed-sensing measurement count `M′²log(M′)²/ε²` is
non-negative.** -/
theorem compressedSensingMeasurements_nonneg (M' : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ compressedSensingMeasurements M' ε := by
  unfold compressedSensingMeasurements
  have hlog : 0 ≤ Real.log (M' + 1) ^ 2 := sq_nonneg _
  have hM : (0 : ℝ) ≤ (M' : ℝ) ^ 2 := sq_nonneg _
  positivity

/-- **c002 the compressed-sensing measurement count is monotone in `M′`.**  More significant
terms cannot lower the number of measurements at a fixed precision. -/
theorem compressedSensingMeasurements_mono_M' (M' M'' : ℕ) (hM : M' ≤ M'')
    {ε : ℝ} (hε : 0 < ε) :
    compressedSensingMeasurements M' ε ≤ compressedSensingMeasurements M'' ε := by
  rw [compressedSensingMeasurements_eq_settings_mul_perSetting,
    compressedSensingMeasurements_eq_settings_mul_perSetting]
  have hset : conciseTomographySettings M' ≤ conciseTomographySettings M'' :=
    (clause22_concise_tomography_budget M' M'' 0 0 hM (le_refl 0)).1
  have hMle : (M' : ℝ) ≤ (M'' : ℝ) := by exact_mod_cast hM
  have hper : (M' : ℝ) / ε ^ 2 ≤ (M'' : ℝ) / ε ^ 2 :=
    _root_.div_le_div_of_nonneg_right hMle (sq_nonneg ε)
  have hset0 : 0 ≤ conciseTomographySettings M' := by
    unfold conciseTomographySettings; positivity
  have hset0'' : 0 ≤ conciseTomographySettings M'' := by
    unfold conciseTomographySettings; positivity
  have hper0 : 0 ≤ (M' : ℝ) / ε ^ 2 := by positivity
  exact mul_le_mul hset hper hper0 hset0''

/-! ## §3 The headline query complexity of Algorithm 3 -/

/-- **c002 headline monotonicity.**  The Algorithm-3 total cost of p.5 is monotone in the
dimension `N`, the sparsity `s`, the condition number `κ` and the number of significant
terms `M′`, at fixed target precisions `ε`, `δ`.  Reuses the reusable theorem
`Qatlib.Papers.QDataFit12.SparseHHL.clause23_readout_headline_mono`. -/
theorem learnLambda_cost_mono (N N' s s' κ κ' M M' : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hN : N ≤ N') (hs : s ≤ s') (hκ : κ ≤ κ') (hM : M ≤ M') :
    readoutHeadlineCost N s κ M ε δ ≤ readoutHeadlineCost N' s' κ' M' ε δ :=
  clause23_readout_headline_mono N N' s s' κ κ' M M' ε δ hε hδ hN hs hκ hM

/-! ## §4 The claim statement -/

/-- **c002 (Algorithm 3, Learning λ) — query complexity, arXiv:1204.5242v2 p.5.**

The Algorithm-3 cost is the sum of the Eq. (16)-with-`1/δ²` quality term and the Eq. (17)
tomography term; its compressed-sensing budget is `M′log(M′)²` settings and `M′²log(M′)²/ε²`
measurements in total; and the total cost is monotone in `N, s, κ, M′`.

*Proved:* the cost decomposition, the measurement budget and its monotonicity in `M′`, and
the monotonicity of the total cost.
*Not modelled here:* the compressed-sensing reconstruction of `|λ⟩`, the identification of
the global phase of the output bit string, and the sparse-oracle program realising the
cost (these are recorded as residuals of the `SparseHHL` block). -/
theorem claim_c002 :
    (∀ (N s κ M' : ℕ) (ε δ : ℝ),
        readoutHeadlineCost N s κ M' ε δ
          = fitQualityCost N s κ ε δ + tomographyHeadlineCost N s κ M' ε) ∧
      (∀ (M' : ℕ) (ε : ℝ),
        compressedSensingMeasurements M' ε
          = conciseTomographySettings M' * ((M' : ℝ) / ε ^ 2)) ∧
      (∀ (M' M'' : ℕ), M' ≤ M'' → ∀ (ε : ℝ), 0 < ε →
        compressedSensingMeasurements M' ε ≤ compressedSensingMeasurements M'' ε) ∧
      (∀ (N N' s s' κ κ' M M' : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
        N ≤ N' → s ≤ s' → κ ≤ κ' → M ≤ M' →
          readoutHeadlineCost N s κ M ε δ ≤ readoutHeadlineCost N' s' κ' M' ε δ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N s κ M' ε δ
    exact readoutHeadlineCost_eq_fitQuality_add_tomography N s κ M' ε δ
  · intro M' ε
    exact compressedSensingMeasurements_eq_settings_mul_perSetting M' ε
  · intro M' M'' hM ε hε
    exact compressedSensingMeasurements_mono_M' M' M'' hM hε
  · intro N N' s s' κ κ' M M' ε δ hε hδ hN hs hκ hM
    exact learnLambda_cost_mono N N' s s' κ κ' M M' ε δ hε hδ hN hs hκ hM

end Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims
