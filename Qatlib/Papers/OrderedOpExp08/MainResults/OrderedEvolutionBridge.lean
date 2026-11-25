/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OrderedOpExp08.MainResults.ErrorBounds

@[expose] public section

/-!
# Frozen-generator alignment of midpoint sampling and the ordered evolution

Connecting the two models of [WiebeEtAl2010], Theorem 1: the ordered exponential
`U(μ + Δλ, μ)` of the time-dependent generator field and the Suzuki word built from generators
sampled at the interval midpoint. The paper compares them by matching truncated series, which
requires the sampled generator list to describe the field throughout the segment. This module
isolates that case: when the field is frozen at its midpoint value, the ordered evolution is an
explicit matrix exponential, so the segment selection of Lemma 5 applies verbatim and the
midpoint word reaches the ordered evolution within the requested tolerance.

## Main statements

* `orderedEvolution_constantGenerator`: a constant generator gives a matrix exponential.
* `orderedEvolution_frozenGenerator`: the ordered evolution of a frozen field is the
  exponential of `Δλ •` the midpoint generator.
* `suzukiMass_ltsGenerators_le` and `orderedGenerator_norm_le_midpoint`: the `Λ` control of the
  sampled mass and of the midpoint generator.
* `frozen_segment_alignment`: with a single tolerance `ε`, the selected midpoint segment word is
  within `ε` of the ordered evolution of the paper's generator.

## Boundary

Everything here is conditional on the field being frozen at the midpoint. For a genuinely
time-dependent field the two truncated series no longer coincide, and comparing them needs an
estimate identifying the Dyson prefix of `U(μ + Δλ, μ)` with the Taylor prefix of the word; that
estimate is not in the library, so no statement about a varying field is made. The sign is the
library convention: `orderedEvolution A` solves `U' = -A * U`, hence the paper's generator `G`
enters as `-G`.

## References

* [Wiebe et al., 2010][WiebeEtAl2010], Theorem 1, Eq. (11), pp. 4-5,
  [arXiv:0812.0562](https://arxiv.org/abs/0812.0562)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

open Matrix
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.OrderedOpExp08.MainResults

open Qatlib.Papers.OrderedOpExp08.MainResults

/-- A constant generator field gives the ordinary matrix exponential: the solution of
`U' = -A * U` with `U(s) = 1` is `exp ((t - s) • (-A))`. -/
theorem orderedEvolution_constantGenerator {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (s t : ℝ) :
    orderedEvolution (fun _ => A) s t = NormedSpace.exp ((t - s) • (-A)) := by
  have he := ordered_matrix_ode_unique (fun _ => A) continuous_const
    (orderedEvolution (fun _ => A) s)
    (fun u : ℝ => NormedSpace.exp ((u - s) • (-A))) s
    (by simp [orderedEvolution_self])
    (orderedEvolution_hasDerivAt _ continuous_const s) (fun u => ?_)
  · exact congrFun he t
  have hd : HasDerivAt (fun v : ℝ => NormedSpace.exp ((v - s) • (-A)))
      ((-A) * NormedSpace.exp ((u - s) • (-A))) u := by
    convert! (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) (u - s)).scomp u
      ((hasDerivAt_id u).sub_const s) using 1
    simp
  simpa only [neg_mul] using! hd

/-- If the generator field is frozen at its midpoint value, the ordered evolution over the
segment is the exponential of the midpoint generator. -/
theorem orderedEvolution_frozenGenerator {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (μ dlam : ℝ)
    (hfrozen : ∀ u : ℝ, orderedGenerator H u = orderedGenerator H (μ + dlam / 2)) :
    orderedEvolution (fun u => -orderedGenerator H u) μ (μ + dlam) =
      NormedSpace.exp (dlam • orderedGenerator H (μ + dlam / 2)) := by
  have hA : (fun u => -orderedGenerator H u) =
      fun _ => -orderedGenerator H (μ + dlam / 2) := by
    funext u
    rw [hfrozen u]
  rw [hA, orderedEvolution_constantGenerator]
  congr 1
  rw [show μ + dlam - μ = dlam from by ring, neg_neg]

/-- The midpoint generator has norm at most `Λ` under the `Λ`-smoothness hypothesis. -/
theorem orderedGenerator_norm_le_midpoint {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (μ dlam Λ : ℝ) (k : ℕ)
    (hdlam : 0 ≤ dlam)
    (hsmooth : LambdaSmooth H Λ μ (μ + dlam) (2 * k)) :
    ‖orderedGenerator H (μ + dlam / 2)‖ ≤ Λ := by
  have hmem : μ + dlam / 2 ∈ Set.Icc μ (μ + dlam) := by
    refine ⟨by linarith, by linarith⟩
  have h0 := hsmooth 0 (Nat.zero_le _) (μ + dlam / 2) hmem
  have hsum : ∑ j : Fin m, ‖H j (μ + dlam / 2)‖ ≤ Λ := by
    simpa [iteratedDeriv_zero] using! h0
  exact (norm_sum_le _ _).trans hsum

/-- The midpoint-sampled recursive Suzuki word has mass at most `3 ^ (k - 1) * Λ`. -/
theorem suzukiMass_ltsGenerators_le {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (μ dlam Λ : ℝ) (k : ℕ)
    (hdlam : 0 ≤ dlam)
    (hsmooth : LambdaSmooth H Λ μ (μ + dlam) (2 * k)) :
    suzukiMass (ltsGenerators H μ dlam (k - 1)) ≤ (3 : ℝ) ^ (k - 1) * Λ := by
  have hmem : μ + dlam / 2 ∈ Set.Icc μ (μ + dlam) := by
    refine ⟨by linarith, by linarith⟩
  have hbase : suzukiMass (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))) ≤ Λ := by
    have h0 := hsmooth 0 (Nat.zero_le _) (μ + dlam / 2) hmem
    have h0' : ∑ j : Fin m, ‖H j (μ + dlam / 2)‖ ≤ Λ := by
      simpa [iteratedDeriv_zero] using! h0
    simpa [suzukiMass, sum_ofFn_eq] using! h0'
  have h := (recursive_suzuki_length_and_mass I
    (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))) (k - 1)).2
  exact h.trans (mul_le_mul_of_nonneg_left hbase (by positivity))

/-- Frozen-generator alignment: when the generator field is frozen at its midpoint value, the
midpoint-sampled segment word with the selected segment count reproduces the ordered evolution
of the paper's generator within the requested tolerance `ε` [WiebeEtAl2010]. -/
theorem frozen_segment_alignment {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (μ dlam : ℝ) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ)
    (hε : 0 < ε)
    (hfrozen : ∀ u : ℝ, orderedGenerator H u = orderedGenerator H (μ + dlam / 2))
    (hhs : ∀ j : Fin m, (H j (μ + dlam / 2))ᴴ = -H j (μ + dlam / 2)) :
    ‖(segmentWord (ltsGenerators H μ dlam (k - 1)) dlam
          (orderedSegments (ltsGenerators H μ dlam (k - 1)) (2 * k) dlam ε)).prod -
        orderedEvolution (fun u => -orderedGenerator H u) μ (μ + dlam)‖ ≤ ε := by
  have hsum : (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))).sum =
      orderedGenerator H (μ + dlam / 2) := by
    simp [orderedGenerator, List.sum_ofFn]
  have hbase : ∀ X ∈ List.ofFn (fun j : Fin m => H j (μ + dlam / 2)), Xᴴ = -X := by
    intro X hX
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hX
    exact hhs j
  have hc : ∀ n : ℕ, n ≤ 2 * k →
      suzukiSeries (ltsGenerators H μ dlam (k - 1)) n =
        ((n.factorial : ℝ)⁻¹) • orderedGenerator H (μ + dlam / 2) ^ n := by
    intro n hn
    have hn' : n ≤ 2 * ((k - 1) + 1) := by omega
    have h := recursive_suzuki_all_even_order_coefficients I
      (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))) (k - 1) n hn'
    rwa [hsum] at h
  have hH : (orderedGenerator H (μ + dlam / 2))ᴴ = -orderedGenerator H (μ + dlam / 2) := by
    show (∑ j : Fin m, H j (μ + dlam / 2))ᴴ = -(∑ j : Fin m, H j (μ + dlam / 2))
    rw [Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hhs j
  rw [orderedEvolution_frozenGenerator H μ dlam hfrozen]
  exact (selected_segment_error (ltsGenerators H μ dlam (k - 1))
    (orderedGenerator H (μ + dlam / 2)) (2 * k) dlam ε (by omega) hε hc
    (recursiveSuzukiGenerators_antiHermitian _ (k - 1) hbase) hH).2

end Qatlib.Papers.OrderedOpExp08.MainResults
