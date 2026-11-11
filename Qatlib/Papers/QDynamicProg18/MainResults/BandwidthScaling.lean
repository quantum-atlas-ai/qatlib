/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamicProg18.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 7 — the scaling inequality for the forbidden-vertex base

Section 3.3 of the paper (pp. 7–8) runs the Hypercube Path algorithm with
`μ n` valid vertices.  For a fixed level assignment `α` the exponential part of
the running time is `max(c, √(μ · t²))` (Eq. (4), p. 8), where `c` is the
classical-preprocessing base (independent of `μ`) and `t` is the per-vertex
quantum base.  The optimised base `γ_μ` is the infimum of this quantity over all
level assignments; it satisfies `γ_{μ₀} = μ₀` at the break-even point
`μ₀ ≈ 1.734622` (Figure 1, p. 9).

Proposition 7 (p. 11) says `γ_μ² / μ ≤ μ₀` for all `μ ∈ [μ₀, 2]`.  The paper's
proof observes `γ_{q μ₀} ≤ √q · γ_{μ₀}` (run the `μ₀`-optimal assignment with
`q μ₀ n` valid vertices) and substitutes `γ_{μ₀} = μ₀`.  Both steps are proved
below: `gamma_scaling` is the scaling inequality for the model `gamma`, and
`proposition7` is the resulting numerical inequality.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical
open scoped Pointwise

set_option autoImplicit false

noncomputable section

/-! ## §1 The cost model of Eq. (4) -/

/-- One level assignment of the Hypercube Path algorithm: its
classical-preprocessing base and its per-vertex quantum base. -/
structure LevelAssignment where
  /-- exponential base of the classical preprocessing (independent of `μ`) -/
  classicalBase : ℝ
  /-- per-vertex exponential base of the quantum part -/
  quantumBase : ℝ
  /-- bases are nonnegative -/
  classicalBase_nonneg : 0 ≤ classicalBase
  /-- bases are nonnegative -/
  quantumBase_nonneg : 0 ≤ quantumBase

/-- The exponential base of one level assignment with `μ n` valid vertices
(Eq. (4), p. 8): `max(c, √(μ · t²))`. -/
def levelBase (a : LevelAssignment) (μ : ℝ) : ℝ :=
  max a.classicalBase (Real.sqrt (μ * a.quantumBase ^ 2))

/-- The optimised exponential base `γ_μ`: the infimum of `levelBase` over all
level assignments (Section 3.3, pp. 7–8). -/
def gamma (assignments : Set LevelAssignment) (μ : ℝ) : ℝ :=
  sInf ((fun a => levelBase a μ) '' assignments)

/-! ## §2 Basic facts -/

/-- Every level base is nonnegative. -/
theorem levelBase_nonneg (a : LevelAssignment) (μ : ℝ) : 0 ≤ levelBase a μ :=
  a.classicalBase_nonneg.trans (le_max_left _ _)

/-- The infimum `γ_μ` is nonnegative. -/
theorem gamma_nonneg {assignments : Set LevelAssignment} (hA : assignments.Nonempty)
    (μ : ℝ) : 0 ≤ gamma assignments μ := by
  unfold gamma
  refine le_csInf (hA.image (fun a => levelBase a μ)) ?_
  rintro _ ⟨a, _, rfl⟩
  exact levelBase_nonneg a μ

/-- **Scaling of one level base.**  For `q ≥ 1` and `μ ≥ 0`, running the same
level assignment with `q μ n` valid vertices costs at most `√q` times as much
in the exponential base. -/
theorem levelBase_scaling (a : LevelAssignment) {μ q : ℝ} (_hμ : 0 ≤ μ) (hq : 1 ≤ q) :
    levelBase a (q * μ) ≤ Real.sqrt q * levelBase a μ := by
  unfold levelBase
  apply max_le
  · have h1 : (1 : ℝ) ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
    have hc : a.classicalBase ≤ Real.sqrt q * a.classicalBase := by
      nlinarith [a.classicalBase_nonneg]
    exact hc.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg q))
  · have hsqrt : Real.sqrt (q * μ * a.quantumBase ^ 2)
        = Real.sqrt q * Real.sqrt (μ * a.quantumBase ^ 2) := by
      rw [show q * μ * a.quantumBase ^ 2 = q * (μ * a.quantumBase ^ 2) by ring]
      exact Real.sqrt_mul (by linarith) (μ * a.quantumBase ^ 2)
    rw [hsqrt]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg q)

/-! ## §3 The scaling inequality for the optimised base -/

/-- **Scaling of `γ`.**  For a nonempty family of level assignments, `μ ≥ 0`
and `q ≥ 1`, `γ_{q μ} ≤ √q · γ_μ` — the paper's key step in the proof of
Proposition 7 (p. 11): the assignment that is optimal for `μ` can be reused
for `q μ`, at a cost of at most a factor `√q`. -/
theorem gamma_scaling {assignments : Set LevelAssignment} (hA : assignments.Nonempty)
    {μ q : ℝ} (hμ : 0 ≤ μ) (hq : 1 ≤ q) :
    gamma assignments (q * μ) ≤ Real.sqrt q * gamma assignments μ := by
  unfold gamma
  set T : Set ℝ := (fun a => levelBase a μ) '' assignments with hT
  set U : Set ℝ := (fun a => levelBase a (q * μ)) '' assignments with hU
  have hTne : T.Nonempty := hA.image _
  have hUne : U.Nonempty := hA.image _
  have hUbdd : BddBelow U := ⟨0, fun _ hb => by
    obtain ⟨a, _, rfl⟩ := hb
    exact levelBase_nonneg a _⟩
  have hstep : sInf U ≤ Real.sqrt q * sInf T := by
    have hb : ∀ w ∈ Real.sqrt q • T, sInf U ≤ w := by
      intro w hw
      rw [Set.mem_smul_set] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      obtain ⟨a, ha, rfl⟩ := ht
      calc sInf U ≤ levelBase a (q * μ) := csInf_le hUbdd ⟨a, ha, rfl⟩
        _ ≤ Real.sqrt q * levelBase a μ := levelBase_scaling a hμ hq
    have hne : (Real.sqrt q • T).Nonempty := by
      obtain ⟨t, ht⟩ := hTne
      exact ⟨Real.sqrt q • t, Set.smul_mem_smul_set ht⟩
    calc sInf U ≤ sInf (Real.sqrt q • T) := le_csInf hne hb
      _ = Real.sqrt q * sInf T := by
          rw [Real.sInf_smul_of_nonneg (Real.sqrt_nonneg q) T]
          rfl
  exact hstep

/-! ## §4 Proposition 7 -/

/-- **Proposition 7, p. 11.**  For all `μ ∈ [μ₀, 2]`, `γ_μ² / μ ≤ μ₀`,
where `γ_{μ₀} = μ₀` is the break-even point of the classical and quantum
running times (Figure 1, p. 9).

The statement is the paper's `μ ∈ [μ₀, 2]`; the upper endpoint `2` is not used
by the proof and is therefore omitted, so the result holds on all of
`[μ₀, ∞)`.

Source: arXiv:1807.05209v1, Proposition 7, page 11. -/
theorem proposition7 {assignments : Set LevelAssignment} {μ₀ μ : ℝ}
    (hA : assignments.Nonempty) (hμ0 : 0 < μ₀)
    (hgamma0 : gamma assignments μ₀ = μ₀) (hμ : μ₀ ≤ μ) :
    gamma assignments μ ^ 2 / μ ≤ μ₀ := by
  have hq : 1 ≤ μ / μ₀ := (one_le_div hμ0).mpr hμ
  have hμeq : (μ / μ₀) * μ₀ = μ := by field_simp
  have hscale : gamma assignments μ ≤ Real.sqrt (μ / μ₀) * μ₀ := by
    have h := gamma_scaling hA (le_of_lt hμ0) hq
    rw [hμeq, hgamma0] at h
    exact h
  have hpos : 0 < μ := lt_of_lt_of_le hμ0 hμ
  have hnonneg : 0 ≤ gamma assignments μ := gamma_nonneg hA μ
  have hsq : gamma assignments μ ^ 2 ≤ (μ / μ₀) * μ₀ ^ 2 := by
    have h1 : (Real.sqrt (μ / μ₀) * μ₀) ^ 2 = (μ / μ₀) * μ₀ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ μ / μ₀)]
    calc gamma assignments μ ^ 2 ≤ (Real.sqrt (μ / μ₀) * μ₀) ^ 2 :=
          pow_le_pow_left₀ hnonneg hscale 2
      _ = (μ / μ₀) * μ₀ ^ 2 := h1
  rw [div_le_iff₀ hpos]
  calc gamma assignments μ ^ 2 ≤ (μ / μ₀) * μ₀ ^ 2 := hsq
    _ = μ₀ * μ := by field_simp

end

end Qatlib.Papers.QDynamicProg18.MainResults
