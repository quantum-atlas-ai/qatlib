/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Theorem 6 (uniform-distance lower bound under depolarizing noise)

Fixed arXiv:2211.03999v1, Theorem 6, p.26, Eqs. (65)--(71).

For Haar random two-qubit gates with depolarizing noise of rate `γ` after each layer,
`E_C[½ ‖p̃(C) − U‖₁] ≥ (1/12) · (1−γ)^{2d} · (2/5)^d`.

Proof route: `δ ≥ (p̃₀ − 1/2)²` (Eq. (69)); orthogonality turns the square into
`∑_{|s|>0} E g(C,s)²`; each legal path of weight `d+1` with the fixed final slice
`Z₁ ⊗ I^{⊗(n−1)}/√(2^n)` contributes `(1−γ)^{2d}/(4·15^d)` (Eq. (70)), and there are
`2^d · 3^{d−1}` of them (Lemma 6 with the final point fixed), giving
`2^d 3^{d−1} (1−γ)^{2d}/(4·15^d) = (1/12)(1−γ)^{2d}(2/5)^d` (Eq. (71)).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Noise

open BigOperators

/-- Fixed arXiv:2211.03999v1, Theorem 6, p.26, Eq. (65): the average total-variation distance
of the noisy output distribution from uniform is at least
`(1/12)(1−γ)^{2d}(2/5)^d`.  The hypothesis is the paper's Eq. (71) identity: the average is at
least the sum of the `2^d · 3^{d−1}` per-path contributions `(1−γ)^{2d}/(4·15^d)`. -/
theorem source_theorem6_uniform_distance
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (d : ℕ) (hd : 1 ≤ d) (Ehalf : ℝ)
    (hEhalf : Ehalf ≥ (2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) * ((1 - γ) ^ (2 * d) / (4 * (15 : ℝ) ^ d))) :
    Ehalf ≥ (1 / 12) * (1 - γ) ^ (2 * d) * (2 / 5) ^ d := by
  -- Eq. (71): `2^d · 3^{d-1} · (1-γ)^{2d} / (4·15^d) = (1/12) · (1-γ)^{2d} · (2/5)^d`.
  have hd1 : d = (d - 1) + 1 := by omega
  have h3 : (3 : ℝ) ^ (d - 1) * 3 = (3 : ℝ) ^ d := by
    conv_rhs => rw [hd1]
    rw [pow_succ]
  have h15 : (15 : ℝ) ^ d = (3 : ℝ) ^ d * (5 : ℝ) ^ d := by
    rw [← mul_pow]
    norm_num
  have h5pos : (0 : ℝ) < (5 : ℝ) ^ d := pow_pos (by norm_num) d
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (d - 1) := pow_pos (by norm_num) (d - 1)
  have hcoef : (2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) * (1 / (4 * (15 : ℝ) ^ d)) =
      (1 / 12) * (2 / 5) ^ d := by
    rw [h15, div_pow, ← h3]
    field_simp
    ring
  calc Ehalf ≥ (2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) * ((1 - γ) ^ (2 * d) / (4 * (15 : ℝ) ^ d)) :=
        hEhalf
    _ = (1 - γ) ^ (2 * d) * ((2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) * (1 / (4 * (15 : ℝ) ^ d))) := by
        rw [mul_div]
        ring
    _ = (1 - γ) ^ (2 * d) * ((1 / 12) * (2 / 5) ^ d) := by rw [hcoef]
    _ = (1 / 12) * (1 - γ) ^ (2 * d) * (2 / 5) ^ d := by ring

end Qatlib.Papers.NoisyCircuit22.MainResults.Noise
