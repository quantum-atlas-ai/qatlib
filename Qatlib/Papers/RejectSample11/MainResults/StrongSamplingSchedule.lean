/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweightingDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Strong quantum rejection sampling: ratio-only schedule (Lemma 4)

Fixed source: Ozols–Roetteler–Roland, *Quantum rejection sampling*,
arXiv:1103.2774v4, Section 4.3 (Lemma 4, Eq. (17), and the geometric schedule
of Eqs. (18)–(20)).

Lemma 4 concerns the strong problem `SQSampling_τ` of Definition 4, where the
amplitudes `π` are unknown and only the ratios `τ_k = σ_k/π_k · ‖π∘τ‖₂` are
known.  The source algorithm needs the clip `ε = r·ε(γ)` only through the
ratios `ε_k/π_k` (the rotation angles of `R_ε`), and the proof observes that
with the water level `γ = α‖π∘τ‖₂` those ratios have the closed form

`ε_k/π_k = r·min{1, ατ_k}`   (Eq. (17)),

which is completely determined by the known `τ`.  For `α = 1` the clip is
`ε = r·(π∘τ)`, and because `σ = (π∘τ)/‖π∘τ‖₂` the success parameter
`p_ε = (σᵀε/‖ε‖₂)²` equals one.

This module formalises

* `strongSigma` and `strongClip` — the Definition-4 target amplitudes and the
  Definition-5 clip in the ratio-only setting;
* `strongClip_ratio` — Eq. (17), the ratio `ε_k/π_k` depends on `τ` alone;
* `strongClip_alphaOne` and `strongSampling_alphaOne_success` — the `α = 1`
  clause of Lemma 4: the clip is `r·(π∘τ)` and the success parameter is one;
* `strongSchedule_geometricCondition` — the convergence condition
  `c·p̄ < 1 ⟺ c < 2/(1+2Δ)` that makes the geometric series of Eq. (19)
  converge.

Not formalised here: the amplitude-doubling schedule `T_l = ⌈c^l⌉` and its
monotonicity, the single-round failure bound of Eq. (18), and the resulting
expected-query bound `128/‖ε(γ)‖₂` of Eq. (20).  In particular the statement
"the expected number of queries is `O(1/‖ε(γ)‖₂)`" is *not* derived here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Concepts.Waterfill.LevelFidelity

open scoped BigOperators

namespace Qatlib.Papers.RejectSample11.MainResults

/-! ## Definition 4: target amplitudes from the known ratio vector -/

/-- Source Definition 4: the target amplitudes `σ_k = π_k τ_k/‖π∘τ‖₂` of the
strong resampling problem, written so that only the ratio vector `τ` is needed
once `π∘τ` has unit norm. -/
noncomputable def strongSigma {m : ℕ} (π τ : Fin m → ℝ) : Fin m → ℝ :=
  fun k => π k * τ k / l2Norm (fun j => π j * τ j)

/-- Source Definition 5 in the ratio-only setting: the water-filling clip
`ε(γ) = min{π, γσ}` with `σ = strongSigma π τ`. -/
noncomputable def strongClip {m : ℕ} (π τ : Fin m → ℝ) (γ : ℝ) : Fin m → ℝ :=
  fun k => min (π k) (γ * strongSigma π τ k)

/-! ## Eq. (17): the clip ratio is determined by `τ` -/

/-- Source Eq. (17): at the water level `γ = α‖π∘τ‖₂` the rotation angle of the
strong-sampling clip is `ε_k/π_k = r·min{1, ατ_k}`, which is fixed by the known
ratio vector `τ` and does not require the unknown amplitudes `π`. -/
theorem strongClip_ratio {m : ℕ} (π τ : Fin m → ℝ) (hπ : ∀ k, 0 < π k)
    (hL : 0 < l2Norm (fun j => π j * τ j)) (α r : ℝ) (k : Fin m) :
    r * strongClip π τ (α * l2Norm (fun j => π j * τ j)) k / π k =
      r * min 1 (α * τ k) := by
  have hLne : l2Norm (fun j => π j * τ j) ≠ 0 := ne_of_gt hL
  have hπne : π k ≠ 0 := ne_of_gt (hπ k)
  have hscale : (α * l2Norm (fun j => π j * τ j)) *
      (π k * τ k / l2Norm (fun j => π j * τ j)) = α * (π k * τ k) := by
    field_simp
  have hclip : strongClip π τ (α * l2Norm (fun j => π j * τ j)) k =
      min (π k) (α * (π k * τ k)) := by
    unfold strongClip strongSigma
    rw [hscale]
  rw [hclip, mul_div_assoc, ← min_div_div_right (le_of_lt (hπ k))]
  congr 1
  rw [div_self hπne]
  field_simp

/-! ## The `α = 1` clause of Lemma 4 -/

/-- For `α = 1` the strong-sampling clip is the unscaled ratio vector,
`ε_k = π_k τ_k` for every `k` with `τ_k ≤ 1`. -/
theorem strongClip_alphaOne {m : ℕ} (π τ : Fin m → ℝ) (hπ : ∀ k, 0 < π k)
    (hτ1 : ∀ k, τ k ≤ 1)
    (hL : 0 < l2Norm (fun j => π j * τ j)) (k : Fin m) :
    strongClip π τ (l2Norm (fun j => π j * τ j)) k = π k * τ k := by
  have hLne : l2Norm (fun j => π j * τ j) ≠ 0 := ne_of_gt hL
  have hval : strongClip π τ (l2Norm (fun j => π j * τ j)) k =
      min (π k) (π k * τ k) := by
    unfold strongClip strongSigma
    rw [mul_div_cancel₀ _ hLne]
  rw [hval, min_eq_right]
  have := hπ k
  have := hτ1 k
  nlinarith

/-- Lemma 4, `α = 1`: the strong-sampling success parameter
`p_ε = (σᵀε/‖ε‖₂)²` is exactly one, because `σ = (π∘τ)/‖π∘τ‖₂` and the clip
is `π∘τ` up to the scaling `r`. -/
theorem strongSampling_alphaOne_success {m : ℕ} (π τ : Fin m → ℝ)
    (hL : 0 < l2Norm (fun j => π j * τ j)) :
    (∑ k, strongSigma π τ k * (π k * τ k)) ^ 2 = ∑ k, (π k * τ k) ^ 2 := by
  have hLne : l2Norm (fun j => π j * τ j) ≠ 0 := ne_of_gt hL
  have hsum : (∑ j, (π j * τ j) ^ 2) = l2Norm (fun j => π j * τ j) ^ 2 := by
    unfold l2Norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hdot : (∑ k, strongSigma π τ k * (π k * τ k)) =
      (∑ k, (π k * τ k) ^ 2) / l2Norm (fun j => π j * τ j) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by
      unfold strongSigma
      ring
  rw [hdot, hsum, sq]
  field_simp

/-! ## The geometric schedule condition of Eqs. (18)–(20) -/

/-- The source's convergence condition for the geometric series of Eq. (19):
with `p̄ = 1/2 + Δ` the requirement `c·p̄ < 1` is equivalent to
`c < 2/(1+2Δ)`. -/
theorem strongSchedule_geometricCondition {c Δ : ℝ} (hΔ : 0 < Δ) :
    c * (1 / 2 + Δ) < 1 ↔ c < 2 / (1 + 2 * Δ) := by
  have hpos : (0 : ℝ) < 1 + 2 * Δ := by linarith
  constructor
  · intro h
    rw [lt_div_iff₀ hpos]
    nlinarith
  · intro h
    rw [lt_div_iff₀ hpos] at h
    nlinarith

end Qatlib.Papers.RejectSample11.MainResults
