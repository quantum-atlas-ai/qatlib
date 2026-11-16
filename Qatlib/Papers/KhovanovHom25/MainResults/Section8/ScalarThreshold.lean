/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


section

set_option backward.isDefEq.respectTransparency false

/-!
# Scalar threshold arithmetic

Source: arXiv:2501.12378v2, Section 8.4, Theorem 39 and Corollary 41,
pp. 54-56. These rational and real scalar identities are independent of the
unfinished knot-graph construction. The original scalar definitions are retained.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.KhovanovHom25.MainResults

/-- The paper's `Ψ_S = (loop(S) + cut(S))/|S|` (Section 8.4, p. 54). -/
def psiQ (A m : ℚ) : ℚ :=
  A / m

/-- **Theorem 39** (arXiv:2501.12378v2, p. 54, eq. (8.8)-(8.9)).  For
`S ⊂ S' ⊂ V` with `A = loop(S') + cut(S')`, `t = loop(S'/S) - cut(S,S') +
cut(S'-S, V-S)`, `m = |S'|` and `d = |S'-S|`:

`Ψ_S = (A - t)/(m - d) < Ψ_{S'} = A/m  ↔  t > d · Ψ_{S'}`.

This is eq. (8.9) together with the paper's final algebraic step. -/
theorem theorem39 (A t : ℚ) (m d : ℕ) (hm : 0 < m) (hdm : d < m) :
    psiQ (A - t) ((m : ℚ) - (d : ℚ)) < psiQ A (m : ℚ) ↔
      (d : ℚ) * psiQ A (m : ℚ) < t := by
  have hm' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hmd' : (0 : ℚ) < (m : ℚ) - (d : ℚ) := by
    have : (d : ℚ) < (m : ℚ) := by exact_mod_cast hdm
    linarith
  simp only [psiQ]
  rw [div_lt_div_iff₀ hmd' hm']
  constructor
  · intro h
    rw [← mul_div_assoc, div_lt_iff₀ hm']
    nlinarith
  · intro h
    rw [← mul_div_assoc, div_lt_iff₀ hm'] at h
    nlinarith

/-- The paper's `Ψ_V = k(k-1)/(2(N+1))` (eq. (8.7)), as a real number. -/
def psiV (N k : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) + 1))

/-- **Corollary 41, the constant `(1/16)(k(k-1)/(N+1))²`.**  The paper's displayed
`Ψ_V²/(4d*) = (1/16)(k(k-1)/(N+1))²` is exact precisely when the maximal degree is
`d* = 1` (the cases `k = 0` and `k = 1`, where both sides vanish, are the ones used
in the corollary); in general `Ψ_V²/(4d*) = (1/16)(k(k-1)/(N+1))²/d*`, which is the
weaker bound `Ψ_V²/(4d*) ≤ (1/16)(k(k-1)/(N+1))²` for `d* ≥ 1`.  (For `k = 2` the
paper's own Example 42, `N = 3`, has `d* = 3` and displays `Ψ_V²/(4d*) = 1/192`,
while `(1/16)(k(k-1)/(N+1))² = 1/64`; the inequality, not the equality, is what
the proof uses.) -/
theorem corollary41_const (N k : ℕ) (dStar : ℝ) (hd : dStar = 1) :
    psiV N k ^ 2 / (4 * dStar) = (1 / 16) * ((k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) + 1)) ^ 2 := by
  subst hd
  unfold psiV
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

end Qatlib.Papers.KhovanovHom25.MainResults
