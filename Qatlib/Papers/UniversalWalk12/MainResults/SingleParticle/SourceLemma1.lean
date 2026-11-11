/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 1 — boundedness of single-particle scattering amplitudes

Childs--Gosset--Webb, *Universal computation by multi-particle quantum walk*,
fixed arXiv:1205.3782v2, Appendix A, Lemma 1, p.15 (txt line 685).

Paper statement: *Given `Ĝ`, there exists a constant `λ ∈ ℝ` such that
`|⟨v | sc_j(k)⟩| < λ` for all `k ∈ [−π, π)`, `j ∈ {1, …, N}` and `v ∈ Ĝ`.*

Paper route: in Appendix A the S-matrix and the internal amplitudes `Ψ(k)` are
shown to be rational functions of `z = e^{ik}` with no poles on the unit circle
(`det γ(z)/(1 - z⁻²) ≠ 0` for `|z| = 1`). Hence each matrix element
`k ↦ ⟨v | sc_j(k)⟩` is continuous on the compact momentum circle, so it is bounded.

The Lean formalisation below isolates exactly the analytic core: the amplitude
table is a continuous (in `k`) family over the compact interval `[-π, π]`, and it
is bounded there. Finiteness of `{j} × Ĝ` (a `Fintype`) lets us take a uniform
bound over all `(j, v)`. The no-poles/rational-function step is the paper's own
argument and is documented but not re-formalised here.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace Qatlib.Papers.UniversalWalk12.MainResults.SingleParticle

/-- The table of scattering amplitudes `⟨v | sc_j(k)⟩` of the single-particle
Hamiltonian `H_G^{(1)}` of eq. (3), abstracted by its momentum regularity.

`amp k j v` is the amplitude at momentum `k` on path `j` and vertex/index `v`;
`continuous_amp` is the Appendix A fact that these have no poles on the unit
circle and are therefore continuous in `k` on `[-π, π]`. -/
structure ScatteringAmplitudes (N : ℕ) (ι : Type*) where
  /-- the amplitude `k ↦ ⟨v | sc_j(k)⟩` -/
  amp : ℝ → Fin N → ι → ℂ
  /-- continuity in the momentum on the closed momentum interval -/
  continuous_amp : ∀ j v, ContinuousOn (fun k => amp k j v) (Icc (-Real.pi) Real.pi)

/-- **Lemma 1** (arXiv:1205.3782v2, p.15): the single-particle scattering
amplitudes are uniformly bounded. There is `λ ∈ ℝ` with
`|⟨v | sc_j(k)⟩| < λ` for all `k ∈ [−π, π)`, all paths `j` and all vertices `v`.

Proof: on the compact interval `Icc (-π) π` each amplitude function is the image
of a compact set under a continuous map, hence bounded; finitely many `(j, v)`
give a uniform bound `Σ B_{jv}`, and adding `1` makes the inequality strict.
The conclusion is stated on the half-open `Ico (-π) π`, as in the paper. -/
theorem source_lemma1_bounded_amplitudes
    {ι : Type*} [Fintype ι] {N : ℕ} (A : ScatteringAmplitudes N ι) :
    ∃ lam : ℝ, ∀ k ∈ Ico (-Real.pi) Real.pi, ∀ j v, ‖A.amp k j v‖ < lam := by
  have hb : ∀ p : Fin N × ι, ∃ B : ℝ, 0 ≤ B ∧
      ∀ k ∈ Icc (-Real.pi) Real.pi, ‖A.amp k p.1 p.2‖ ≤ B := by
    rintro ⟨j, v⟩
    have hcomp : IsCompact ((fun k => A.amp k j v) '' Icc (-Real.pi) Real.pi) :=
      isCompact_Icc.image_of_continuousOn (A.continuous_amp j v)
    obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hcomp.isBounded
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro k hk
    have hm : (fun k => A.amp k j v) k ∈ (fun k => A.amp k j v) '' Icc (-Real.pi) Real.pi :=
      mem_image_of_mem _ hk
    have hdist := hB hm
    simp only [Metric.mem_closedBall, dist_zero_right] at hdist
    exact hdist.trans (le_max_left _ _)
  choose B hB0 hB using hb
  refine ⟨(∑ p : Fin N × ι, B p) + 1, ?_⟩
  intro k hk j v
  have hmem : k ∈ Icc (-Real.pi) Real.pi := ⟨hk.1, le_of_lt hk.2⟩
  have h1 : ‖A.amp k j v‖ ≤ B ⟨j, v⟩ := hB ⟨j, v⟩ k hmem
  have h2 : B ⟨j, v⟩ ≤ ∑ p : Fin N × ι, B p :=
    Finset.single_le_sum (f := B) (fun p _ => hB0 p) (Finset.mem_univ _)
  have h3 : (∑ p : Fin N × ι, B p) < (∑ p : Fin N × ι, B p) + 1 := lt_add_one _
  linarith

end Qatlib.Papers.UniversalWalk12.MainResults.SingleParticle
