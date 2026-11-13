/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineCoordinateReadoutOpti
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

/-!
# ReadoutTools — Lemma 20 (source gradient readout on the almost-affine grid)

Fixed source: arXiv:1711.00465v3, *Optimizing quantum optimization algorithms
via faster quantum gradient computation*, Lemma 20 (§5.1, p.26).

Lemma 20: let `N = 2^n`, `c ∈ ℝ`, `g ∈ ℝ^d` with `‖g‖_∞ ≤ 1/3`, and let
`f : G_n^d → ℝ` satisfy `|f(x) − g·x − c| ≤ 1/(42πN)` at all but a `1/1000`
fraction of grid points.  Then the output `(k_1,…,k_d)` of Algorithm 2 obeys
`Pr[|k_i − g_i| > 4/N] ≤ 1/3` for every coordinate `i`.

This file states the paper conclusion against the actual single-query word
(`gradientReadout`) and obtains it from
`Qatlib.Concepts.GradientOracle.ReadoutTools.almostAffineCoordinateReadout`.
The bridge is the affine reparametrisation of the
centred source grid `G_n` of Definition 17 (p.24):
`(x_j).val = N · sourceGradientGridPoint n (x_j) + N/2 − 1/2`, so the constant
`N·c` of the scaled phase table absorbs the centring shift.  Queries, gates and
the actual word are exactly those of the shared readout; no extra assumption is
introduced.
-/

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GradientOracle.ReadoutTools
open scoped BigOperators

namespace Qatlib.Papers.QGradient17.ReadoutTools.Readout

/-- Lemma 20 of arXiv:1711.00465v3 (§5.1, p.26).

On the centred dyadic grid `G_n` (`sourceGradientGridPoint`), if `f` is affine
up to `1/(42πN)` on all but a `1/1000` fraction of points, then the actual
one-query gradient readout of Algorithm 2 has, for every coordinate, failure
probability at most `1/3` of producing an estimate outside `4/N`.  Reuses
`almostAffineCoordinateReadout`; the paper's `c` and the grid centring combine
into `c' = N·c − (N/2 − 1/2)·Σ_j g_j`. -/
theorem source_lemma_twenty
    (d n : ℕ) (hN : 0 < 2 ^ n) (f : GradientGrid d (2 ^ n) → ℝ)
    (g : Fin d → ℝ) (c : ℝ) (S : Finset (GradientGrid d (2 ^ n)))
    (hg : ∀ j, |g j| ≤ 1 / 3)
    (hbad : ((Finset.univ \ S).card : ℝ) ≤ ((2 : ℝ) ^ n) ^ d / 1000)
    (hgood : ∀ x ∈ S,
      |f x - (c + ∑ j : Fin d, g j * sourceGradientGridPoint n (x j))|
        ≤ 1 / (42 * Real.pi * (2 : ℝ) ^ n)) :
    ∀ j : Fin d,
      MeasureProb (gradientReadout d (2 ^ n) hN (fun x => (2 : ℝ) ^ n * f x))
        (Finset.univ.filter fun z =>
          4 / (2 : ℝ) ^ n <
            |signedGridValue (2 ^ n) (z j) - g j|) ≤ 1 / 3 := by
  -- The scaled phase table and the affine constant that absorb the grid centring.
  set N : ℝ := (2 : ℝ) ^ n with hNdef
  have hNpos : 0 < N := by positivity
  let φ : GradientGrid d (2 ^ n) → ℝ := fun x => N * f x
  let c' : ℝ := N * c - (N / 2 - 1 / 2) * ∑ j : Fin d, g j
  -- The paper's hypothesis becomes the shared good-grid hypothesis.
  have hgood' : ∀ x ∈ S, |φ x - (c' + ∑ j : Fin d, g j * (x j).val)| ≤ 1 / (42 * Real.pi) := by
    intro x hx
    have hx' := hgood x hx
    have hval : ∀ j : Fin d,
        (x j).val = N * sourceGradientGridPoint n (x j) + (N / 2 - 1 / 2) := by
      intro j
      unfold sourceGradientGridPoint
      field_simp
      ring
    have hrewrite : φ x - (c' + ∑ j : Fin d, g j * (x j).val)
        = N * (f x - (c + ∑ j : Fin d, g j * sourceGradientGridPoint n (x j))) := by
      simp only [φ, c']
      rw [Finset.mul_sum] at *
      have : ∑ j : Fin d, g j * ((x j).val : ℝ)
          = ∑ j : Fin d, g j * (N * sourceGradientGridPoint n (x j) + (N / 2 - 1 / 2)) := by
        exact Finset.sum_congr rfl fun j _ => by rw [hval j]
      rw [this]
      ring_nf
      rw [Finset.mul_sum]
      ring_nf
      have hsum :
          (∑ i : Fin d, (N * g i * (1 / 2) + g i * (-1 / 2)))
            - (∑ i : Fin d,
                (N * g i * (1 / 2) + N * g i * sourceGradientGridPoint n (x i)
                  + g i * (-1 / 2)))
          = -(∑ i : Fin d, N * g i * sourceGradientGridPoint n (x i)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      linarith [hsum]
    rw [hrewrite, abs_mul, abs_of_pos hNpos]
    have hkey : N * |f x - (c + ∑ j : Fin d, g j * sourceGradientGridPoint n (x j))|
        ≤ N * (1 / (42 * Real.pi * N)) := by
      exact mul_le_mul_of_nonneg_left hx' (le_of_lt hNpos)
    have hNne : N ≠ 0 := ne_of_gt hNpos
    calc N * |f x - (c + ∑ j : Fin d, g j * sourceGradientGridPoint n (x j))|
        ≤ N * (1 / (42 * Real.pi * N)) := hkey
      _ = 1 / (42 * Real.pi) := by field_simp
  -- The readout theorem gives simultaneous `2/3` mass for every coordinate.
  have hmain := almostAffineCoordinateReadout d n hN φ g c' S hg hbad hgood'
  obtain ⟨hmass, -, -, -⟩ := hmain
  -- The actual readout is a normalized state of the unitary word.
  have hword : IsUnitaryCircuit (gradientWord d (2 ^ n)) :=
    (gradient_coordinate_qft_word_unitarity d (2 ^ n) hN).1
  have hnorm : Normalized (gradientReadout d (2 ^ n) hN φ) := by
    unfold gradientReadout
    exact hword.normalized_run (gradientPhase_unitary d (2 ^ n) φ) (normalized_ket _)
  intro j
  have hsucc : 2 / 3 ≤
      MeasureProb (gradientReadout d (2 ^ n) hN φ)
        (Finset.univ.filter fun z =>
          |signedGridValue (2 ^ n) (z j) - g j| ≤ 4 / (2 : ℝ) ^ n) := hmass j
  -- Complement the success event; `Normalized` makes the two masses sum to one.
  have hsplit :
      MeasureProb (gradientReadout d (2 ^ n) hN φ)
          (Finset.univ.filter fun z =>
            ¬ (4 / (2 : ℝ) ^ n < |signedGridValue (2 ^ n) (z j) - g j|))
        + MeasureProb (gradientReadout d (2 ^ n) hN φ)
          (Finset.univ.filter fun z =>
            4 / (2 : ℝ) ^ n < |signedGridValue (2 ^ n) (z j) - g j|) = 1 := by
    unfold MeasureProb
    rw [add_comm, Finset.sum_filter_add_sum_filter_not]
    exact bornProb_sum_eq_one hnorm
  have hsame :
      ((Finset.univ : Finset (GradientGrid d (2 ^ n))).filter fun z =>
        |signedGridValue (2 ^ n) (z j) - g j| ≤ 4 / (2 : ℝ) ^ n)
        = ((Finset.univ : Finset (GradientGrid d (2 ^ n))).filter fun z =>
            ¬ (4 / (2 : ℝ) ^ n < |signedGridValue (2 ^ n) (z j) - g j|)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> linarith
  rw [hsame] at hsucc
  linarith

end Qatlib.Papers.QGradient17.ReadoutTools.Readout
