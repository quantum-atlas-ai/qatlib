/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 16: Definition-1 coefficients for the block-encoded QLSP walk

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 16 / Eqs. (130)--(131), pages 20--21.

With `W_T(s)` the walk encoded from the block encoding (124) of `H(s)` and the
reflection `R(s)` of Eq. (127), the paper shows that Definition 1 holds with

`c₁(s) = 2T (f(s+1/T) - f(s))`,                                    (130)

`c₂(s) = 2 max_{τ∈{s,s+1/T,s+2/T}} (2|f'(τ)|² + |f''(τ)|)`
for `0 ≤ s ≤ 1 - 2/T`, and the two-point maximum at `s = 1 - 1/T`.  (131)

The block encoding itself is not modelled in this paper layer.  The
first- and second-difference estimates of the encoded walk are therefore the
hypotheses `hEnc1` and `hEnc2` (the output of the paper's block-encoding
analysis); the lemma concludes the Definition-1 shape with the coefficients
`c₁, c₂` of Eqs. (130)--(131), which is the paper's "it is consistent with
Definition 1 to choose ...".
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R]

/-- Fixed arXiv:2111.08152, Lemma 16 (Eqs. (130)--(131), pp. 20--21):
with the block-encoding estimates `‖DW_T(s)‖ ≤ 2(f(s+1/T)-f(s))` and
`‖D^(2)W_T(s)‖ ≤ c₂(s)/T²`, the choices (130) and (131) satisfy
Definition 1. -/
theorem source_lemma16
    (T : ℝ) (W : ℝ → R) (f f' f'' : ℝ → ℝ) (c1 c2 : ℝ → ℝ) (s : ℝ)
    (hT : 0 < T)
    (hc1 : c1 s = 2 * T * (f (s + 1 / T) - f s))
    (hc2 : c2 s = if s ≤ 1 - 2 / T then
        2 * max (max (2 * |f' s| ^ 2 + |f'' s|)
              (2 * |f' (s + 1 / T)| ^ 2 + |f'' (s + 1 / T)|))
          (2 * |f' (s + 2 / T)| ^ 2 + |f'' (s + 2 / T)|)
      else
        2 * max (2 * |f' s| ^ 2 + |f'' s|)
          (2 * |f' (s + 1 / T)| ^ 2 + |f'' (s + 1 / T)|))
    (hEnc1 : ‖diff T W s‖ ≤ 2 * (f (s + 1 / T) - f s))
    (hEnc2 : ‖diff2 T W s‖ ≤ c2 s / T ^ 2) :
    ‖diff T W s‖ ≤ c1 s / T ∧ ‖diff2 T W s‖ ≤ c2 s / T ^ 2 := by
  constructor
  · rw [hc1]
    have hEq : 2 * T * (f (s + 1 / T) - f s) / T = 2 * (f (s + 1 / T) - f s) := by
      field_simp
    rw [hEq]
    exact hEnc1
  · rw [hc2] at hEnc2 ⊢
    exact hEnc2

end Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp
