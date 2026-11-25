/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.VanishCharge.ClebschAlgebra
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Uniform writhe suppression and the classical limit of centerline helicity

[Kedia2018SuperfluidHelicity], Section V, Eqs. (6)–(8),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
This module proves the kinematic half of the classical-limit argument for centerline
helicity, in the exact formulation of the public algebra of
`Qatlib.Papers.SuperfluidHel18.VanishCharge`: for a bundle of `n` vortices with equal
circulation `κ` and uniformly bounded writhe `|Wr i| ≤ W`, the rescaled self term of the
centerline helicity deviates from the rescaled pairwise linking term by at most `W / n`,
and any bundle sequence whose rescaled linking part converges has its rescaled centerline
helicity converging to the same limit, with the error bound uniform in the sequence.

The linking numbers entering the limit are real input data of topological origin; their
invariance and the actual vortex dynamics are hypotheses of the paper's argument, not
results proved here. Uniform bounds are proved for equal circulations only; non-uniform
bundles are not covered.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open Filter
open scoped BigOperators Topology

/-- The self (writhe) part of centerline helicity for equal circulations extracts the mean
writhe times the squared common circulation. -/
theorem writhePart_const_apply {n : ℕ} (κ : ℝ) (wr : Fin n → ℝ) :
    writhePart (fun _ => κ) wr = κ ^ 2 * ∑ i, wr i := by
  simp only [writhePart, Finset.mul_sum]

/-- Uniform writhe bound: the self term of a bundle with equal circulations is at most
`W` times the bundle size times `κ²`. -/
theorem writhePart_const_abs_le {n : ℕ} (κ W : ℝ) (wr : Fin n → ℝ)
    (hwr : ∀ i, |wr i| ≤ W) :
    |writhePart (fun _ => κ) wr| ≤ W * (n : ℝ) * κ ^ 2 := by
  rw [writhePart_const_apply]
  have hκ : 0 ≤ κ ^ 2 := sq_nonneg κ
  have h1 : |∑ i, wr i| ≤ ∑ i, |wr i| := Finset.abs_sum_le_sum_abs wr Finset.univ
  have h2 : ∑ i, |wr i| ≤ ∑ i, W := Finset.sum_le_sum fun i _ => hwr i
  have h3 : ∑ i : Fin n, W = (n : ℝ) * W := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc |κ ^ 2 * ∑ i, wr i| = κ ^ 2 * |∑ i, wr i| := by
        rw [abs_mul, abs_of_nonneg hκ]
    _ ≤ κ ^ 2 * ((n : ℝ) * W) := by
        exact mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3.le)) hκ
    _ = W * (n : ℝ) * κ ^ 2 := by ring

/-- Rescaled writhe suppression (Eq. (7) of the paper, equal-circulation form): after
dividing the centerline helicity of `n` equal-circulation vortices by `(n κ)²`, the self
contribution is at most `W / n`, uniformly in the bundle. -/
theorem rescaled_writhe_error (n : ℕ) (κ W : ℝ) (hW : 0 ≤ W) (wr : Fin n → ℝ)
    (hwr : ∀ i, |wr i| ≤ W) :
    |writhePart (fun _ => κ) wr| / ((n : ℝ) * κ) ^ 2 ≤ W / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    simp [writhePart_const_apply]
  rcases eq_or_ne κ 0 with hκ0 | hκ0
  · subst hκ0
    have h0 : writhePart (fun _ : Fin n => (0 : ℝ)) wr = 0 := by
      simp [writhePart_const_apply]
    rw [h0]
    simp only [abs_zero, zero_div]
    exact div_nonneg hW (by positivity)
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hden : (0 : ℝ) < ((n : ℝ) * κ) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt hpos) hκ0)
  rw [div_le_iff₀ hden]
  have hWn : W / (n : ℝ) * (((n : ℝ) * κ) ^ 2) = W * (n : ℝ) * κ ^ 2 := by
    field_simp
  rw [hWn]
  exact writhePart_const_abs_le κ W wr hwr

/-- The rescaled centerline helicity of an equal-circulation bundle differs from its
rescaled pairwise linking term by the uniformly suppressed writhe error. -/
theorem rescaled_centerline_near_linking (n : ℕ) (κ W : ℝ) (hW : 0 ≤ W)
    (L : Fin n → Fin n → ℝ) (wr : Fin n → ℝ) (hwr : ∀ i, |wr i| ≤ W) :
    |centerlineHelicity (fun _ => κ) L wr / ((n : ℝ) * κ) ^ 2
        - linkingPart (fun _ => κ) L / ((n : ℝ) * κ) ^ 2| ≤ W / (n : ℝ) := by
  have h : centerlineHelicity (fun _ => κ) L wr / ((n : ℝ) * κ) ^ 2
      - linkingPart (fun _ => κ) L / ((n : ℝ) * κ) ^ 2
      = writhePart (fun _ => κ) wr / ((n : ℝ) * κ) ^ 2 := by
    rw [centerlineHelicity, linkingPart]
    ring
  rw [h, abs_div, abs_of_nonneg (sq_nonneg ((n : ℝ) * κ))]
  exact rescaled_writhe_error n κ W hW wr hwr

/-- The classical limit of rescaled centerline helicity (Eq. (8) of the paper,
equal-circulation bundle form): if a bundle sequence has uniformly bounded writhe and its
rescaled pairwise linking sums converge to `H`, then the rescaled centerline helicity
converges to the same limit. This is a purely kinematic statement: the topological input
is carried by the linking data and the convergence hypothesis, and no vortex dynamics,
reconnection or singular-core analysis is invoked. -/
theorem classical_limit (κ W : ℝ) (hW : 0 ≤ W)
    (h ch : ℕ → ℝ) (H : ℝ) (hh : Tendsto h atTop (𝓝 H))
    (hch : ∀ n : ℕ, ∃ L : Fin n → Fin n → ℝ, ∃ wr : Fin n → ℝ,
      (∀ i, |wr i| ≤ W) ∧
        ch n = centerlineHelicity (fun _ => κ) L wr / ((n : ℝ) * κ) ^ 2 ∧
        h n = linkingPart (fun _ => κ) L / ((n : ℝ) * κ) ^ 2) :
    Tendsto ch atTop (𝓝 H) := by
  have hbnd : Tendsto (fun n : ℕ => W / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat W
  have habs : Tendsto (fun n => |ch n - h n|) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hbnd
    obtain ⟨L, wr, hwr, hchn, hhn⟩ := hch n
    rw [hchn, hhn]
    exact rescaled_centerline_near_linking n κ W hW L wr hwr
  have hdiff : Tendsto (fun n => ch n - h n) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero fun n => ch n - h n).mpr habs
  have hgoaleq : ch = fun n => (ch n - h n) + h n := by funext n; ring
  have hfin : Tendsto (fun n : ℕ => (ch n - h n) + h n) atTop (𝓝 (0 + H)) := hdiff.add hh
  rw [hgoaleq]
  simpa using hfin

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
