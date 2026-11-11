/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LiftingWu25.ProtocolSetup.SensitivityEntropic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# DegreeTradeoff — the classical-quantum trade-off of Theorem 5.2

Wu--Yang--Yao, fixed arXiv:2511.17227v2, Section 5.

Theorem 5.1 yields a deterministic decision tree with at most `200c/b` queried
coordinates such that every leaf restricts the outer function to one with
approximate degree `O(q/b)`. Theorem 5.2 walks down that tree: by the entropic
property of `deg(·)` (Proposition 2.4, consumed here through the abstract
iteration Lemma `entropic_iterate` of Proposition 2.3) every query can lower the
degree by at most one, so at each leaf `deg(f_{J,z}) ≥ deg(f) - |J̄|`.

This module isolates the resulting arithmetic chain. It consumes

* the query bound `qc ≤ 200c/b` (Lemma 4.2),
* the restricted degree loss `deg f - qc ≤ dd`, where `dd = deg(f_{J,z})`
  (Proposition 2.3 applied to the entropic measure `deg`),
* the approximate-degree/degree relation `κ·√dd ≤ deg_{1/3}(f_{J,z})`
  (`[ABK+21, Theorem 4]`, an external result, or the block-sensitivity form
  `[NS94, Lemma 3.8]`),
* the cost relation `deg_{1/3}(f_{J,z}) ≤ K·q/b` (Theorem 5.1's `O(q/b)`).

The conclusion is the paper's `q = Ω(√(deg f) · b)`, with the explicit constant
`κ / (K√3)`.

Boundary: the communication-theoretic steps (Theorem 5.1, Lemma 4.2) and the
external approximate-degree relation enter only through the numerically stated
inequalities above, with explicit constants; they are not re-proved here. The
factor `√b ≤ b` uses `b ≥ 1`, i.e. the paper's `b = 20 log n` with `n ≥ 2`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LiftingWu25.Tradeoff

/-- Theorem 5.2, degree form: if the decision tree queries `qc` coordinates with
`qc ≤ 200c/b`, the restricted function has degree `dd ≥ deg f - qc`, its
approximate degree is at least `κ·√dd` and at most `K·q/b`, and the classical
budget satisfies `c ≤ deg f · b / 300`, then the quantum communication satisfies
`q ≥ (κ/(K√3))·√(deg f)·√b`. -/
theorem theorem52_degree_core {degf c b q dd dq qc κ K : ℝ}
    (hb : 0 < b) (hb1 : 1 ≤ b) (hdeg : 0 < degf)
    (hκ : 0 < κ) (hK : 0 < K)
    (hc : c ≤ degf * b / 300)
    (hqc : qc ≤ 200 * c / b)
    (hdegloss : degf - qc ≤ dd)
    (happrox : κ * Real.sqrt dd ≤ dq)
    (hcost : dq ≤ K * q / b) :
    (κ / (K * Real.sqrt 3)) * Real.sqrt degf * Real.sqrt b ≤ q := by
  -- the classical budget is at most two thirds of the degree
  have hbudget : 200 * c / b ≤ 2 * degf / 3 := by
    have h1 : 200 * c / b ≤ 200 * (degf * b / 300) / b := by gcongr
    have h2 : 200 * (degf * b / 300) / b = 2 * degf / 3 := by
      field_simp
      ring
    exact le_trans h1 (le_of_eq h2)
  -- so at least a third of the degree survives in the restricted function
  have hdd : degf / 3 ≤ dd := by linarith
  have hsq : Real.sqrt (degf / 3) ≤ Real.sqrt dd := Real.sqrt_le_sqrt hdd
  have hstep : κ * Real.sqrt (degf / 3) ≤ K * q / b := by
    have h1 : κ * Real.sqrt (degf / 3) ≤ κ * Real.sqrt dd :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hκ)
    linarith
  -- solve the resulting linear inequality for `q`
  have hq : κ * Real.sqrt (degf / 3) * b / K ≤ q := by
    have h1 : κ * Real.sqrt (degf / 3) * b ≤ K * q := by
      have h := mul_le_mul_of_nonneg_left hstep (le_of_lt hb)
      have hKq : K * q / b * b = K * q := by field_simp
      linarith
    rw [div_le_iff₀ hK]
    linarith
  rw [Real.sqrt_div (le_of_lt hdeg) 3] at hq
  have hconv : κ * (Real.sqrt degf / Real.sqrt 3) * b / K
      = κ / (K * Real.sqrt 3) * Real.sqrt degf * b := by
    field_simp
  rw [hconv] at hq
  -- replace one factor of `b` by `√b`, using `√b ≥ 1`
  have hsqb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt (le_of_lt hb)
  have hsqb1 : 1 ≤ Real.sqrt b := by
    have h := Real.sqrt_le_sqrt hb1
    rwa [Real.sqrt_one] at h
  calc κ / (K * Real.sqrt 3) * Real.sqrt degf * Real.sqrt b
      = (κ / (K * Real.sqrt 3) * Real.sqrt degf * Real.sqrt b) * 1 := (mul_one _).symm
    _ ≤ (κ / (K * Real.sqrt 3) * Real.sqrt degf * Real.sqrt b) * Real.sqrt b :=
        mul_le_mul_of_nonneg_left hsqb1 (by positivity)
    _ = κ / (K * Real.sqrt 3) * Real.sqrt degf * (Real.sqrt b * Real.sqrt b) := by ring
    _ = κ / (K * Real.sqrt 3) * Real.sqrt degf * b := by rw [hsqb]
    _ ≤ q := hq

/-- The block-sensitivity form of Theorem 5.2: the same arithmetic chain with
`bs(f)` in place of `deg(f)`, where at the leaf `deg_{1/3}(f_{J,z}) = Ω(√(bs f_{J,z}))`
and `bs` is entropic (Proposition 2.5). -/
theorem theorem52_blockSensitivity_core {bsf c b q db dq qc κ K : ℝ}
    (hb : 0 < b) (hb1 : 1 ≤ b) (hbs : 0 < bsf)
    (hκ : 0 < κ) (hK : 0 < K)
    (hc : c ≤ bsf * b / 300)
    (hqc : qc ≤ 200 * c / b)
    (hbsloss : bsf - qc ≤ db)
    (happrox : κ * Real.sqrt db ≤ dq)
    (hcost : dq ≤ K * q / b) :
    (κ / (K * Real.sqrt 3)) * Real.sqrt bsf * Real.sqrt b ≤ q :=
  theorem52_degree_core hb hb1 hbs hκ hK hc hqc hbsloss happrox hcost

end Qatlib.Papers.LiftingWu25.Tradeoff
