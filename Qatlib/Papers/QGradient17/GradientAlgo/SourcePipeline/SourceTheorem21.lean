/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Qatlib.Concepts.GradientOracle.GradientAlgo.AlmostAffineGradientOpti

set_option backward.isDefEq.respectTransparency false

/-!
# GradientAlgo — Theorem 21 (full-vector gradient estimate with the symmetric grid)

Fixed source: arXiv:1711.00465v3, *Optimizing quantum optimization algorithms
via faster quantum gradient computation*, Theorem 21 (§5.2, p.26).

Theorem 21: given a `r,ε,L,δ`-accurate almost-affine table on the symmetric
grid `r · G_n^d`, Algorithm 2 with fresh-oracle median repetitions outputs, with
probability at least `1−δ`, an estimate of the gradient `g` up to `ε` in every
coordinate, using `2k+1` fresh oracle calls (`k = k(d,δ)`) and `2d(2k+1)` fixed
gates; the precision `n` is the sum of the signed dyadic precisions
`n_ε = ⌈log₂ 4/(rε)⌉` and `n_L = ⌈log₂ 3rL⌉`.

This is the source-scaling form of the paper's Theorem 21 and is a bridge to
the library theorem `sourceAlmostAffineGradient`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.GradientOracle.GradientAlgo
open Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.Postselection.FreshStep
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open scoped Classical BigOperators

namespace Qatlib.Papers.QGradient17.GradientAlgo.SourcePipeline

/-- Theorem 21 of arXiv:1711.00465v3 (§5.2, p.26): the source-scaled full-vector
gradient guarantee — with `n = n_ε + n_L` (`n_ε = ⌈log₂ 4/(rε)⌉`,
`n_L = ⌈log₂ 3rL⌉`), `2k+1` fresh-oracle median repetitions, success probability
`≥ 1−δ`, coordinate accuracy `ε`, query count `2k+1`, no input queries,
`2d(2k+1)` fixed gates and per-branch median query budget `d·10⁴(2k+1)`.
Reuses `sourceAlmostAffineGradient`. -/
theorem source_theorem_twentyone
    (d : ℕ) (c r ε L : ℝ) (δ : ℚ) (g : Fin d → ℝ)
    (hr : 0 < r) (hε : 0 < ε) (hεL : ε < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hg : ∀ j, |g j| ≤ L) :
    let nε : ℤ := ⌈Real.logb 2 (4 / (r * ε))⌉
    let nL : ℤ := ⌈Real.logb 2 (3 * r * L)⌉
    let n : ℕ := (nε + nL).toNat
    let NL : ℝ := (2 : ℝ) ^ nL
    ∀ (f : GradientGrid d (2 ^ n) → ℝ) (S : Finset (GradientGrid d (2 ^ n))),
      ((Finset.univ \ S).card : ℝ) ≤ ((2 : ℝ) ^ n) ^ d / 1000 →
      (∀ x ∈ S, |f x - (c + ∑ j, g j * (r * sourceGradientGridPoint n (x j)))|
        ≤ ε * r / (8 * 42 * Real.pi)) →
      let φ := fun x => (2 : ℝ) ^ nε * f x
      let hN : 0 < 2 ^ n := Nat.pow_pos (by decide)
      let k := gradientMedianRepetitions d δ
      (nε + nL = (n : ℤ) ∧ 4 ≤ n) ∧
      (1 - (δ : ℝ) ≤
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2 * k + 1) → GradientGrid d (2 ^ n) =>
          ∀ j, |(NL / r) * ((gradientMedianCounted k ω j).1 : ℝ) - g j| ≤ ε),
          gradientFreshMass d (2 ^ n) hN φ ω) ∧
      freshDataQueries (gradientFreshWord d (2 ^ n) (2 * k + 1)) = 2 * k + 1 ∧
      freshInputQueries (gradientFreshWord d (2 ^ n) (2 * k + 1)) = 0 ∧
      freshFixedGates (gradientFreshWord d (2 ^ n) (2 * k + 1)) = 2 * d * (2 * k + 1) ∧
      (∀ ω : Fin (2 * k + 1) → GradientGrid d (2 ^ n),
        (∑ j, (gradientMedianCounted k ω j).2) ≤ d * 10000 * (2 * k + 1)) :=
  sourceAlmostAffineGradient d c r ε L δ g hr hε hεL hδ hδ1 hg

end Qatlib.Papers.QGradient17.GradientAlgo.SourcePipeline
