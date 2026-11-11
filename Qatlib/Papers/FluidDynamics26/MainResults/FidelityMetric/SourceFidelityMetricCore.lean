/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — pure-state distance bounds and the copy lower bound

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026).

Claims formalised in this file:

* c002 = Lemma 3, Eq. (23), p. 10 — the upper half `D(ρ_ψ, ρ_φ) ≤ d(|ψ⟩,|φ⟩)` of the
  comparison between the Euclidean distance `d` of pure states and the trace distance
  `D` of their density matrices;
* c008 = Lemma 10, Eq. (85), p. 17 — the copy lower bound
  `k ≥ ((ε_f - 2δ)/ε_0)^2`.

The upper half of Lemma 3 is proved from the frozen `pure_trace_distance_le_re_inner`;
the lower half and Lemma 4 (c003) would need the pure-state identity
`D(|ψ⟩⟨ψ|,|φ⟩⟨φ|) = sqrt(1 - |⟨ψ|φ⟩|²)` (Eq. (22), p. 10), a spectral computation for a
rank-two difference of projectors that is not formalized; those statements are preserved
in this branch's history.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open scoped BigOperators

/-! ## Overlap of two normalized pure states is a number in `[0,1]` -/

/-- For normalized pure states, `|⟨u|v⟩| ≤ 1` (Cauchy–Schwarz).  Used by both halves of
Lemma 3, Eq. (23), p. 10, and by the separation estimates of Lemma 13/14. -/
theorem norm_inner_le_one {I : Type} [Fintype I] [DecidableEq I]
    {u v : QState I} (hu : Normalized u) (hv : Normalized v) :
    ‖Inner u v‖ ≤ 1 := by
  have hsum : ‖Inner u v‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    rw [inner_apply]
    calc ‖∑ i, (starRingEnd ℂ) (u i) * v i‖ ≤ ∑ i, ‖(starRingEnd ℂ) (u i) * v i‖ :=
          norm_sum_le _ _
      _ = ∑ i, ‖u i‖ * ‖v i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul]
          congr 1
          simpa using norm_star (u i)
  have hcs : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤
      (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hnorm : (∑ i, ‖u i‖ ^ 2) = 1 := hu
  have hnorm' : (∑ i, ‖v i‖ ^ 2) = 1 := hv
  rw [hnorm, hnorm', mul_one] at hcs
  have h0 : 0 ≤ ∑ i, ‖u i‖ * ‖v i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hinner : 0 ≤ ‖Inner u v‖ := norm_nonneg _
  nlinarith

/-! ## c002 — Lemma 3, Eq. (23), p. 10 -/

/-- A unit phase does not change the density matrix: `|c·ψ⟩⟨c·ψ| = |ψ⟩⟨ψ|` for `‖c‖ = 1`. -/
theorem outerProduct_smul_of_norm_one {I : Type} [Fintype I] [DecidableEq I]
    (c : ℂ) (hc : ‖c‖ = 1) (v : QState I) :
    outerProduct (c • v) = outerProduct v := by
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    have h := Complex.mul_conj c
    rw [Complex.normSq_eq_norm_sq, hc] at h
    simpa using h
  ext i j
  simp only [outerProduct_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  calc (c * v i) * ((starRingEnd ℂ) c * (starRingEnd ℂ) (v j))
      = (c * (starRingEnd ℂ) c) * (v i * (starRingEnd ℂ) (v j)) := by ring
    _ = v i * (starRingEnd ℂ) (v j) := by rw [hcc, one_mul]

/-- **c002, Lemma 3, Eq. (23), p. 10**, upper half: `D(ρ_ψ, ρ_φ) ≤ d(|ψ⟩,|φ⟩)`.

This half is independent of `pureState_traceDistanceG_eq`.  Multiplying `|v⟩` by the phase
`c` with `c·⟨u|v⟩ = |⟨u|v⟩|` does not change `D` (`outerProduct_smul_of_norm_one`), and the
frozen `pure_trace_distance_le_re_inner` applied to `u` and `c·v` gives
`D ≤ sqrt(1 - |⟨u|v⟩|²) ≤ sqrt(2 - 2|⟨u|v⟩|) = d`. -/
theorem lemma3_upper_bound {n : ℕ} (u v : QState (Fin n))
    (hu : Normalized u) (hv : Normalized v) :
    traceDistance (outerProduct u) (outerProduct v) ≤ pureDistance u v := by
  obtain ⟨c, hc, hcz⟩ := Complex.exists_norm_eq_mul_self (Inner u v)
  have hinner : Inner u (c • v) = c * Inner u v := by
    rw [inner_apply, inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hval : Inner u (c • v) = ((‖Inner u v‖ : ℝ) : ℂ) := by
    rw [hinner, hcz]
  have hre : (Inner u (c • v)).re = ‖Inner u v‖ := by
    rw [hval]
    simp
  have hv' : Normalized (c • v) := by
    simpa only [Normalized, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hc,
      one_pow, one_mul] using hv
  have hb := pure_trace_distance_le_re_inner u (c • v) hu hv'
  rw [outerProduct_smul_of_norm_one c hc v, hre] at hb
  have hb' : traceDistance (outerProduct u) (outerProduct v) ≤
      Real.sqrt (1 - ‖Inner u v‖ ^ 2) := hb
  have h3 : Real.sqrt (1 - ‖Inner u v‖ ^ 2) ≤ pureDistance u v := by
    have hx0 : 0 ≤ ‖Inner u v‖ := norm_nonneg _
    have hx1 : ‖Inner u v‖ ≤ 1 := norm_inner_le_one hu hv
    rw [pureDistance]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (‖Inner u v‖ - 1)]
  linarith [hb', h3]

/-! ## c008 — Lemma 10, Eq. (85), p. 17 -/

/-- **c008, Lemma 10, Eq. (85), p. 17**: any quantum algorithm implementing `M` to
precision `δ < ε_f/2` uses at least `k ≥ ((ε_f - 2δ)/ε_0)^2` copies.

`ε_0` is the initial trace distance `D(ρ_ψ,ρ_φ)`, `ε_f` the final one
`D(M(ρ_ψ),M(ρ_φ))`.  The proof of the paper combines (i) the precision guarantee with
the triangle inequality, giving `ε_f ≤ 2δ + D(M_k(ρ_ψ), M_k(ρ_φ))` for the algorithm's
outputs, and (ii) Lemma 4, Eq. (24) applied to the `k`-copy inputs, giving
`D(M_k(ρ_ψ), M_k(ρ_φ)) ≤ sqrt k · ε_0`.  This yields `ε_f ≤ 2δ + sqrt k · ε_0` — the
hypothesis `hchain` below — and the remaining step, proved here, is the arithmetic
consequence. -/
theorem lemma10_copy_lower_bound (k : ℕ) {ε₀ εf δ : ℝ}
    (hε0 : 0 < ε₀) (hδ : δ < εf / 2)
    (hchain : εf ≤ 2 * δ + Real.sqrt (k : ℝ) * ε₀) :
    ((εf - 2 * δ) / ε₀) ^ 2 ≤ (k : ℝ) := by
  have hpos : 0 < εf - 2 * δ := by linarith
  have hstep : εf - 2 * δ ≤ Real.sqrt (k : ℝ) * ε₀ := by linarith
  have hdiv : (εf - 2 * δ) / ε₀ ≤ Real.sqrt (k : ℝ) := by
    rw [div_le_iff₀ hε0]
    linarith
  have hnonneg : 0 ≤ (εf - 2 * δ) / ε₀ := div_nonneg (le_of_lt hpos) (le_of_lt hε0)
  calc ((εf - 2 * δ) / ε₀) ^ 2 ≤ (Real.sqrt (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hnonneg hdiv 2
    _ = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)

end Qatlib.Papers.FluidDynamics26.MainResults
