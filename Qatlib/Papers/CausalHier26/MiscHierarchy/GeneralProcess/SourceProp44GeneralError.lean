/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.ReducedBlocks

set_option backward.isDefEq.respectTransparency false

/-!
# SourceProp44GeneralError — Proposition 4.4 (exact general-process error)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Proposition 4.4,
p. 16 (txt lines 820-828).

**Statement (Eq. (78)).**  For every `0 < ε < 1`, with `s = sqrt (1 - ε)` and
`R_ε = sqrt (ε^2 + 1 - ε)`,

```
D^Gen_MISC (N_AD^ε, N_AD^ε; I) = (1/2) [1 - s (ε + R_ε)].
```

**Paper proof.**  The general-process feasible set on the fixed resource tuple is
parameterised by Eq. (80), `x_c(t) = 2 s (ε t + s sqrt (t (1 - t)))` for
`t ∈ [0,1]`.  Cauchy–Schwarz bounds `x_c(t) ≤ s (ε + R_ε)` for every `t`, and the
bound is attained at the value `t*` of Eq. (82), `t* = (1/2)(1 + ε/R_ε)`.

**What is proved here.**  This file proves the whole proposition at the reduced
level, from the explicit family: the pointwise bound (via the exact
sum-of-squares identity `(s(1-2t) + 2εu)^2`, `u = sqrt (t(1-t))`), the location
of `t*` in `[0,1]`, the identity `x_c(t*) = s (ε + R_ε)`, and hence the supremum.
The reduction of the general-process SDP to the one-parameter family Eq. (80) is
the content of the Appendix F certificate (claim `c021`, Lemma F.1).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.GeneralProcess

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- The Cauchy–Schwarz step of Proposition 4.4, p. 16: for `t ∈ [0,1]`,
`x_c(t) ≤ s (ε + R_ε)`.

The key algebraic ingredient is the exact identity
`(s(1-2t) + 2εu)^2 = ε^2 + s^2 - (2εt + 2su - ε)^2`, where `u = sqrt (t(1-t))`
and `ε^2 + s^2 = R_ε^2`. -/
theorem genXc_le (ε t : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    genXc ε t ≤ muGenClosed ε := by
  have hs : 0 < s ε := s_pos h0 h1
  have hR : 0 ≤ Rε ε := R_nonneg ε
  have hR2 : Rε ε ^ 2 = ε ^ 2 + (s ε) ^ 2 := R_sq_eq h0 h1
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hnn : 0 ≤ t * (1 - t) := by nlinarith
  have hu2 : (Real.sqrt (t * (1 - t))) ^ 2 = t * (1 - t) := Real.sq_sqrt hnn
  have hu0 : 0 ≤ Real.sqrt (t * (1 - t)) := Real.sqrt_nonneg _
  -- squared Cauchy–Schwarz inequality
  have hsq : (2 * ε * t + 2 * s ε * Real.sqrt (t * (1 - t)) - ε) ^ 2 ≤ (Rε ε) ^ 2 := by
    nlinarith [sq_nonneg ((s ε) * (1 - 2 * t) + 2 * ε * Real.sqrt (t * (1 - t))),
      hu2, hR2]
  have hXle : 2 * ε * t + 2 * s ε * Real.sqrt (t * (1 - t)) - ε ≤ Rε ε := by
    have habs : |2 * ε * t + 2 * s ε * Real.sqrt (t * (1 - t)) - ε| ≤ Rε ε := by
      have h' := (sq_le_sq.mp hsq)
      rwa [abs_of_nonneg hR] at h'
    linarith [le_abs_self (2 * ε * t + 2 * s ε * Real.sqrt (t * (1 - t)) - ε)]
  have harg' : 2 * ε * t + 2 * s ε * Real.sqrt (t * (1 - t)) ≤ ε + Rε ε := by linarith
  have hfinal :
      s ε * (2 * ε * t + 2 * s ε * Real.sqrt (t * (1 - t))) ≤ s ε * (ε + Rε ε) :=
    mul_le_mul_of_nonneg_left harg' (le_of_lt hs)
  unfold genXc muGenClosed
  nlinarith [hfinal]

/-- `t* = (1/2)(1 + ε/R_ε)` lies in the unit interval (Eq. (82), p. 16). -/
theorem tStar_mem (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    tStar ε ∈ Set.Icc (0 : ℝ) 1 := by
  have hRpos : 0 < Rε ε := R_pos h0 h1
  have hR2 : Rε ε ^ 2 = ε ^ 2 + (s ε) ^ 2 := R_sq_eq h0 h1
  have hs : 0 < s ε := s_pos h0 h1
  have hRgt : ε < Rε ε := by
    have hfac : 0 < (Rε ε - ε) * (Rε ε + ε) := by nlinarith
    have hsum : 0 ≤ Rε ε + ε := by linarith
    nlinarith [pos_of_mul_pos_left hfac hsum]
  constructor
  · unfold tStar
    have : 0 ≤ ε / Rε ε := div_nonneg (le_of_lt h0) (le_of_lt hRpos)
    linarith
  · unfold tStar
    have hle : ε / Rε ε ≤ 1 := by
      rw [div_le_one hRpos]
      exact le_of_lt hRgt
    linarith

/-- The bound is attained: `x_c(t*) = s (ε + R_ε)` (Eq. (82)-(83), p. 16). -/
theorem genXc_tStar (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    genXc ε (tStar ε) = muGenClosed ε := by
  have hs : 0 < s ε := s_pos h0 h1
  have hRpos : 0 < Rε ε := R_pos h0 h1
  have hR2 : Rε ε ^ 2 = ε ^ 2 + (s ε) ^ 2 := R_sq_eq h0 h1
  have hRne : Rε ε ≠ 0 := ne_of_gt hRpos
  have hprod : tStar ε * (1 - tStar ε) = (s ε / (2 * Rε ε)) ^ 2 := by
    unfold tStar
    field_simp
    nlinarith [hR2]
  have hsqrt : Real.sqrt (tStar ε * (1 - tStar ε)) = s ε / (2 * Rε ε) := by
    rw [hprod]
    exact Real.sqrt_sq (by positivity)
  have harg : ε * tStar ε + s ε * (s ε / (2 * Rε ε)) = (ε + Rε ε) / 2 := by
    unfold tStar
    field_simp
    nlinarith [hR2]
  unfold genXc muGenClosed
  rw [hsqrt]
  nlinarith [harg]

/-- Fixed arXiv:2609.08639v1, Proposition 4.4, p. 16, Eq. (78)-(79): the
general-process MISC optimum equals the closed form `s (ε + R_ε)`. -/
theorem source_prop_44_general_process_optimum (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    muGen ε = muGenClosed ε := by
  have hne : (genAchievable ε).Nonempty :=
    ⟨genXc ε 0, ⟨0, ⟨le_refl 0, by norm_num⟩, rfl⟩⟩
  have hub : ∀ y ∈ genAchievable ε, y ≤ muGenClosed ε := by
    rintro y ⟨t, ht, rfl⟩
    exact genXc_le ε t h0 h1 ht
  have hbdd : BddAbove (genAchievable ε) := ⟨muGenClosed ε, hub⟩
  apply le_antisymm
  · exact csSup_le hne hub
  · have hmem : genXc ε (tStar ε) ∈ genAchievable ε :=
      ⟨tStar ε, tStar_mem ε h0 h1, rfl⟩
    calc muGenClosed ε = genXc ε (tStar ε) := (genXc_tStar ε h0 h1).symm
      _ ≤ muGen ε := le_csSup hbdd hmem

/-- Fixed arXiv:2609.08639v1, Proposition 4.4, p. 16, Eq. (78): the exact
general-process transformation error is `(1 - s(ε + R_ε))/2`. -/
theorem source_prop_44_general_process_error (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    Dgen ε = (1 - s ε * (ε + Rε ε)) / 2 := by
  unfold Dgen
  rw [source_prop_44_general_process_optimum ε h0 h1]
  unfold muGenClosed
  rfl

end Qatlib.Papers.CausalHier26.MiscHierarchy.GeneralProcess
