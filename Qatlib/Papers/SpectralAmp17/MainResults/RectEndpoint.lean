/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralAmp17.MainResults.Analytic
public import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PolynomialToolkit
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! # A counterinstance at the included endpoint of the source rectangle band

The official original arXiv:1707.05391v1 PDF, Appendix A, printed/PDF page 25,
Lemma 11 and Equation (59), includes the point |x| = w/2 while defining
rect(1/2) = 1/2. The same formula and endpoint convention occur in the archived
Lean contract. At w = kappa = 1, the actual shifted erf smoother is near one
there, so the claimed error cannot be at most every allowed positive epsilon.

The historical source comment cites a nonexistent v2 dated 9 Oct 2017;
the official history lists only v1. This counterexample preserves the exact
archived mathematical contract and is checked against the actual v1 PDF.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpectralAmp17.MainResults.RectBoundary

open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel
open Qatlib.Papers.SpectralAmp17.MainResults.Analytic

/-- At the included right endpoint, both shifted error-function arguments are on their positive bands. -/
theorem endpoint_lower (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) :
    1 - ε ≤ fRect 1 1 ε (1 / 2) := by
  have ha := positive_sign_error 1 ε (3 / 2) (by norm_num) hε0 hε (by norm_num)
  have hb := positive_sign_error 1 ε (1 / 2) (by norm_num) hε0 hε (by norm_num)
  have hal := (abs_le.mp ha).1
  have hbl := (abs_le.mp hb).1
  have hform : fRect 1 1 ε (1 / 2) =
      (1 / 2 : ℝ) * (fSgn 1 ε (3 / 2) + fSgn 1 ε (1 / 2)) := by
    norm_num [fRect, fSgn]
  rw [hform]
  linarith

/-- The half-valued rectangle target at the included endpoint has error strictly larger than epsilon. -/
theorem endpoint_error (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) (hsmall : ε < 1 / 4) :
    ε < |fRect 1 1 ε (1 / 2) - rectFun ((1 / 2 : ℝ) / 1)| := by
  have hlower := endpoint_lower ε hε0 hε
  have hrect : rectFun ((1 / 2 : ℝ) / 1) = 1 / 2 := by
    norm_num [rectFun]
  rw [hrect]
  have hnonneg : 0 ≤ fRect 1 1 ε (1 / 2) - 1 / 2 := by linarith
  rw [abs_of_nonneg hnonneg]
  linarith

/-- The complete original Lemma 11 contract is false with all of its original parameter assumptions. -/
theorem lemma11_counterexample :
    ¬ (∀ (κ w ε : ℝ) (_hκ : 0 < κ) (_hw : 0 < w) (_hε0 : 0 < ε)
      (_hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))),
      (∀ x : ℝ, |fRect w κ ε x| ≤ 1) ∧
        (∀ x : ℝ, (|x| ≤ w / 2 ∨ w / 2 + κ ≤ |x|) →
          |fRect w κ ε x - rectFun (x / w)| ≤ ε)) := by
  intro h
  let cap : ℝ := Real.sqrt (2 / (Real.exp 1 * Real.pi))
  have hcap : 0 < cap := by
    dsimp [cap]
    exact Real.sqrt_pos.2
      (div_pos (by norm_num) (mul_pos (Real.exp_pos 1) Real.pi_pos))
  let ε : ℝ := min (cap / 2) (1 / 8)
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact lt_min (by positivity) (by norm_num)
  have hεhalf : ε ≤ cap / 2 := min_le_left _ _
  have hεcap : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi)) := by
    change ε ≤ cap
    linarith
  have hεeighth : ε ≤ 1 / 8 := min_le_right _ _
  have hsmall : ε < 1 / 4 := by linarith
  have hfull := h 1 1 ε (by norm_num) (by norm_num) hε0 hεcap
  have herror := hfull.2 (1 / 2) (Or.inl (by norm_num))
  exact (not_le_of_gt (endpoint_error ε hε0 hεcap hsmall)) herror

end Qatlib.Papers.SpectralAmp17.MainResults.RectBoundary
