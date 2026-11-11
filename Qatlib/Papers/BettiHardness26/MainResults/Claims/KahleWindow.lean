/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 6.4 — Kahle's window lies below the PC-hard range

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11). Source: Proposition 6.4, §6.2, p.14.

Let `p = n^{-α}` with `1/(d+1) < α < 1/d`. Then `log_{1/p} n = 1/α`, and the planted-clique
hard window starts at `k ≥ (2+ε) log_{1/p} n = (2+ε)/α`. The paper concludes
`d + 2 < (2+ε) log_{1/p} n`, so no `k` in the PC window equals `d + 2` and Lemma 4.1 fails in
Kahle's window.

**Proof-gap note.** The paper states the proposition for `d > 1` and argues via
`d + 2 < 1/α + 2`. The final inequality `1/α + 2 < (2+ε)/α` requires `2α < 1 + ε`, i.e.
`d(1+ε) ≥ 2`. For `1 < d` the stated hypothesis is *not* sufficient when `ε` is small (for
example `d = 1.1`, `ε = 0.1`). We therefore state the exact inequality with the *necessary and
sufficient* extra hypothesis `2 ≤ d(1+ε)` made explicit; this is the mathematically correct
form of the paper's claim, not a weakening.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Claims

open Real

/-- `log_{1/p} n = 1/α` when `p = n^{-α}`, i.e. `log p = -α log n`, with `α ≠ 0` and
`log n ≠ 0` (the latter holds for `n > 1`). -/
lemma log_inv_pow (n p α : ℝ) (hp : 0 < p) (hα : α ≠ 0) (hln : Real.log n ≠ 0)
    (hlogp : Real.log p = -α * Real.log n) :
    Real.log n / Real.log (1 / p) = 1 / α := by
  have hlog1p : Real.log (1 / p) = α * Real.log n := by
    rw [Real.log_div one_ne_zero hp.ne', Real.log_one, hlogp]; ring
  rw [hlog1p]
  field_simp [hα, hln]

/-- **Proposition 6.4 (§6.2, p.14), correct arithmetic form.** With `p = n^{-α}`,
`1/(d+1) < α < 1/d`, `d > 1`, `ε > 0` and the necessary hypothesis `2 ≤ d(1+ε)`, we have
`d + 2 < (2+ε) log_{1/p} n` for `n > 1`. -/
theorem proposition_6_4
    (n p α d ε : ℝ) (hn : 1 < n) (hp : 0 < p) (hα : 0 < α) (hd : 1 < d)
    (hlogp : Real.log p = -α * Real.log n)
    (hlo : 1 / (d + 1) < α) (hhi : α < 1 / d)
    (hε : 0 < ε) (hgapd : 2 ≤ d * (1 + ε)) :
    d + 2 < (2 + ε) * (Real.log n / Real.log (1 / p)) := by
  have hdpos : (0 : ℝ) < d := by linarith
  -- From `α < 1/d` deduce `d * α < 1`, hence `d < 1/α`.
  have hmulαd : α * d < 1 := by
    have := (lt_div_iff₀ hdpos).mp hhi
    linarith [this]
  have hdlt : d < 1 / α := by
    rw [lt_div_iff₀ hα]; linarith [hmulαd]
  -- The chain `d + 2 ≤ (2+ε) d < (2+ε)/α`.
  have hstep : d + 2 ≤ (2 + ε) * d := by nlinarith [hgapd, hε]
  have hlt : (2 + ε) * d < (2 + ε) * (1 / α) :=
    mul_lt_mul_of_pos_left hdlt (by linarith : (0 : ℝ) < 2 + ε)
  have hln : Real.log n ≠ 0 := by
    intro h
    have hn1 : n = 1 := by
      have := congrArg Real.exp h
      rwa [Real.exp_log (by linarith : (0:ℝ) < n), Real.exp_zero] at this
    linarith
  have hratio : Real.log n / Real.log (1 / p) = 1 / α :=
    log_inv_pow n p α hp (ne_of_gt hα) hln hlogp
  rw [hratio]
  linarith [hstep, hlt]

/-- **Proposition 6.4, window consequence.** No `k` in the PC hard window
`(2+ε) log_{1/p} n < k` can equal `d + 2`. -/
theorem proposition_6_4_window
    (n p α d ε k : ℝ) (hn : 1 < n) (hp : 0 < p) (hα : 0 < α) (hd : 1 < d)
    (hlogp : Real.log p = -α * Real.log n)
    (hlo : 1 / (d + 1) < α) (hhi : α < 1 / d)
    (hε : 0 < ε) (hgapd : 2 ≤ d * (1 + ε))
    (hwin : (2 + ε) * (Real.log n / Real.log (1 / p)) < k) (hk : k = d + 2) : False := by
  have h := proposition_6_4 n p α d ε hn hp hα hd hlogp hlo hhi hε hgapd
  rw [hk] at hwin
  linarith [h, hwin]

end Qatlib.Papers.BettiHardness26.MainResults.Claims
