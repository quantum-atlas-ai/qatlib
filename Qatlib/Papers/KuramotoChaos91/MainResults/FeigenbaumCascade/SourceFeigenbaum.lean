/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KuramotoChaos91.MainResults.KSSetting

set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic diagnostics for the reported period-doubling cascade

Bibliographic reference: Papageorgiou and Smyrlis, *The route to chaos for the
Kuramoto–Sivashinsky equation* (1991), DOI `10.1007/BF00271514`.
The available NASA/ICASE Report 90-78 Table 5 prints the last ratio as 4.88.
The checks below show that this decimal lies outside the stated 4% band
around the quoted decimal 4.669201609. No version equivalence with the journal
article, validated numerical integration, or dynamical existence is asserted.
`PeriodDoublingExperiment` is only an abstract sequence of lengths: it is not
connected to the KS flow and is not evidence for claim c002.
-/

set_option autoImplicit false

namespace Qatlib.Papers.KuramotoChaos91.MainResults.FeigenbaumCascade

noncomputable section

open Qatlib.Papers.KuramotoChaos91.MainResults.KSSetting

/-! ## Feigenbaum's universal constant -/

/-- The finite decimal 4.669201609 quoted in the source. This definition does
not identify the decimal with the exact Feigenbaum constant. -/
def FeigenbaumDelta : ℝ := 4669201609 / 1000000000

/-- The truncated universal constant is positive.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
theorem feigenbaumDelta_pos : 0 < FeigenbaumDelta := by
  unfold FeigenbaumDelta
  norm_num

/-- The truncated universal constant exceeds `1`, as required for a shrinking
subwindow cascade to have ratios larger than one.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
theorem feigenbaumDelta_gt_one : 1 < FeigenbaumDelta := by
  unfold FeigenbaumDelta
  norm_num

/-- The last printed ratio in Report 90-78 Table 5 exceeds the upper 4% band
endpoint for the quoted decimal approximation. This is a decimal arithmetic
check, not a certified bifurcation computation. -/
theorem printed_last_ratio_exceeds_four_percent :
    FeigenbaumDelta * (104 / 100 : ℝ) < (488 / 100 : ℝ) := by
  norm_num [FeigenbaumDelta]

/-- The printed last ratio cannot satisfy the relative 4% inequality against
4.669201609. This diagnoses the reported decimals without identifying that
finite decimal with the exact Feigenbaum constant. -/
theorem printed_last_ratio_outside_four_percent :
    ¬ (|(488 / 100 : ℝ) - FeigenbaumDelta| ≤
      (4 / 100 : ℝ) * FeigenbaumDelta) := by
  norm_num [FeigenbaumDelta]

/-! ## The recorded period-doubling experiment -/

/-- The numerical record of the period-doubling cascade in the paper:
the cascade window, the number of period doublings seen by the direct method
and by the `36`-mode Galerkin truncation, and the measured subwindow lengths.
The lengths are positive and strictly shrinking with the subwindow index.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15) and body (extract
line 345). -/
structure PeriodDoublingExperiment where
  /-- The viscosity window `[0.0299756, 0.0343]` containing the cascade. -/
  cascadeWindow : ViscosityWindow
  /-- Number of period doublings found by the direct method: `5`. -/
  directDoublings : ℕ
  /-- Number of period doublings found with the `36`-mode Galerkin method: `8`. -/
  galerkinDoublings : ℕ
  /-- The Galerkin resolution: `36` modes. -/
  galerkinModes : ℕ
  /-- Measured subwindow lengths, indexed from the first subwindow. -/
  subwindowLength : ℕ → ℝ
  /-- Every measured subwindow has positive length. -/
  subwindow_pos : ∀ k : ℕ, 0 < subwindowLength k
  /-- The subwindow lengths shrink as the cascade develops. -/
  subwindow_shrinking : ∀ k : ℕ, subwindowLength (k + 1) < subwindowLength k

/-- The successive bifurcation ratio `l_k / l_{k+1}` of the cascade.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
def PeriodDoublingExperiment.ratio (X : PeriodDoublingExperiment) (k : ℕ) : ℝ :=
  X.subwindowLength k / X.subwindowLength (k + 1)

/-! ## Arithmetic consequences -/

/-- **Relative `4%` tolerance as an interval.**  Saying that a ratio `r` is
within `4%` of `FeigenbaumDelta` is equivalent to saying that
`r ∈ [0.96 δ, 1.04 δ]`.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15)
(the "error of at most 4%" statement); formal arithmetic consequence. -/
theorem relative_tolerance_iff (r : ℝ) :
    |r - FeigenbaumDelta| ≤ (4 / 100 : ℝ) * FeigenbaumDelta ↔
      FeigenbaumDelta * (96 / 100 : ℝ) ≤ r ∧
        r ≤ FeigenbaumDelta * (104 / 100 : ℝ) := by
  have hpos : 0 < FeigenbaumDelta := feigenbaumDelta_pos
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-- **Shrinking subwindows give ratios larger than one.**  Because every
subwindow length is positive and the lengths strictly decrease, each
successive ratio `l_k / l_{k+1}` exceeds `1`.  Source:
Papageorgiou–Smyrlis 1991, abstract (p. 15); formal consequence of the
record fields `subwindow_pos` and `subwindow_shrinking`. -/
theorem ratio_gt_one (X : PeriodDoublingExperiment) (k : ℕ) :
    1 < X.ratio k := by
  unfold PeriodDoublingExperiment.ratio
  rw [one_lt_div (X.subwindow_pos (k + 1))]
  exact X.subwindow_shrinking k

/-- **A ratio inside the paper's `4%` band exceeds one.**  The lower band
endpoint `0.96 δ` is already larger than `1` (since `δ = 4.669…`), so any
bifurcation ratio reported within `4%` of Feigenbaum's constant is a genuine
shrinking ratio.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15); formal
consequence of `relative_tolerance_iff` and `feigenbaumDelta_gt_one`. -/
theorem ratio_gt_one_of_feigenbaum_tolerance {r : ℝ}
    (h : |r - FeigenbaumDelta| ≤ (4 / 100 : ℝ) * FeigenbaumDelta) :
    1 < r := by
  have hlow : FeigenbaumDelta * (96 / 100 : ℝ) ≤ r :=
    ((relative_tolerance_iff r).mp h).1
  have hband : (1 : ℝ) < FeigenbaumDelta * (96 / 100 : ℝ) := by
    unfold FeigenbaumDelta
    norm_num
  linarith

/-- **The cascade window is a legitimate viscosity window.**  The two quoted
endpoints `0.0299756` and `0.0343` are positive and strictly ordered, so they
form a `ViscosityWindow` in the sense of `KSSetting`.  Source:
Papageorgiou–Smyrlis 1991, abstract (p. 15) and body (extract line 345);
formal arithmetic consequence. -/
theorem cascade_window_valid :
    (0 : ℝ) < 299756 / 10 ^ 7 ∧
      (299756 / 10 ^ 7 : ℝ) < 343 / 10 ^ 4 := by
  constructor <;> norm_num

/-- **The cascade window `[0.0299756, 0.0343]` packaged as a
`ViscosityWindow`.**  Used to connect the numerical record of `c002` to the
window vocabulary of `KSSetting`.  Source: Papageorgiou–Smyrlis 1991, abstract
(p. 15) and body (extract line 345). -/
def cascadeViscosityWindow : ViscosityWindow where
  lo := 299756 / 10 ^ 7
  hi := 343 / 10 ^ 4
  lo_pos := cascade_window_valid.1
  lo_lt_hi := cascade_window_valid.2

/-- The packaged cascade window has the paper's endpoints.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15) and body (extract
line 345). -/
theorem cascadeViscosityWindow_lo :
    cascadeViscosityWindow.lo = (299756 / 10 ^ 7 : ℝ) := rfl

/-- The packaged cascade window has the paper's upper endpoint.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15) and body (extract
line 345). -/
theorem cascadeViscosityWindow_hi :
    cascadeViscosityWindow.hi = (343 / 10 ^ 4 : ℝ) := rfl

/-- **The width of the `4%` Feigenbaum band** is `(8/100) δ`, i.e. the
admissible interval `[0.96 δ, 1.04 δ]` has length `0.08 δ`.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15); formal arithmetic
consequence. -/
theorem feigenbaum_interval_width :
    FeigenbaumDelta * (104 / 100 : ℝ) - FeigenbaumDelta * (96 / 100 : ℝ) =
      (8 / 100 : ℝ) * FeigenbaumDelta := by
  ring

/-- **The last computed subwindow is far shorter than the whole cascade
window.**  The paper's window `0.0299756 ≤ ν ≤ 0.0343` has width
`0.0043244`, while the last accurately computed subwindow has length
`1.3 × 10⁻⁷`.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15) and body
(extract line 345); formal arithmetic consequence. -/
theorem lastSubwindow_lt_cascadeWidth :
    (13 / 10 ^ 8 : ℝ) < 343 / 10 ^ 4 - 299756 / 10 ^ 7 := by
  norm_num

end

end Qatlib.Papers.KuramotoChaos91.MainResults.FeigenbaumCascade
