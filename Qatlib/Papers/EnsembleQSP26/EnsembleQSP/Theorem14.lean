/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnsembleQSP26.EnsembleQSP.Definitions
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Mathlib.Algebra.Order.Floor.Semiring

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — Theorem 14 (Hadamard-test observable estimation, Algorithm 3)

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27), Theorem 14 (Eqs. (C11)–(C20)).

Algorithm 3 estimates `⟨ψ| E Õ |ψ⟩` by a Hadamard test whose single-run outcome `o`
is bounded in `[-1,1]` and satisfies `E[o] = ⟨ψ| E Õ |ψ⟩` (the unbiasedness of the
Hadamard test, Eqs. (C14)–(C17)).  Averaging `M` independent runs therefore drives
the estimate to the target; this file proves that the `M`-sample empirical mean is an
`ε`-approximation with probability at least `1 - δ` for
`M = O(log(1/δ)/ε²)`, using finite Hoeffding's inequality
(`finite_iid_bounded_average_tail`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

attribute [local instance] Classical.propDecidable

/-- **Theorem 14 (arXiv:2601.20073v1 p.14, Eqs. (C11)–(C20), Algorithm 3).**
Let a single Hadamard-test run produce an outcome statistic `o : X → ℝ` with
`|o x| ≤ 1` and mean `E[o] = μ` (the paper's target `⟨ψ| E Õ |ψ⟩`, Eqs. (C14)–(C17)).
Then for every `ε, δ > 0` there is `M = O(log(1/δ)/ε²)` such that the `M`-run
empirical average `avg o` is within `ε` of `μ` with probability at least `1 - δ`.

Technical note: the finite outcome space is taken in universe `Type` because the
reusable finite-Hoeffding lemma `finite_iid_bounded_average_tail` is stated there;
this is a Lean universe artefact, not a restriction on the mathematics (every
finite type is equivalent to `Fin n`). -/
theorem theorem14_hadamard_test
    {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (o : X → ℝ) (μ ε δ : ℝ)
    (hbound : ∀ x, |o x| ≤ 1) (hmean : p.expect o = μ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ 4 * Real.log (2 / δ) / ε ^ 2 + 2 ∧
      p.probEvent (fun seeds : Fin M → X => ε ≤ |FinDist.avg o seeds - μ|) ≤ δ := by
  have hLpos : 0 < Real.log (2 / δ) :=
    Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have harg0 : (0 : ℝ) ≤ 2 * Real.log (2 / δ) / ε ^ 2 := by positivity
  refine ⟨Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1, Nat.succ_pos _, ?_, ?_⟩
  · -- complexity bound: M = ceil(2L/ε²) + 1 ≤ 4L/ε² + 2
    have hceil_lt : ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) : ℕ) : ℝ) <
        2 * Real.log (2 / δ) / ε ^ 2 + 1 := Nat.ceil_lt_add_one harg0
    have hstep : 2 * Real.log (2 / δ) / ε ^ 2 ≤ 4 * Real.log (2 / δ) / ε ^ 2 := by
      have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
      rw [div_le_div_iff_of_pos_right hε2]
      nlinarith [hLpos]
    have hMeq : ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ)
        = ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hMeq]
    linarith
  · -- concentration via finite Hoeffding on the shifted statistic o + 1 ∈ [0,2]
    have hMpos : 0 < Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 := Nat.succ_pos _
    have hMge : 2 * Real.log (2 / δ) / ε ^ 2 ≤
        ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ) := by
      have h1 := Nat.le_ceil (2 * Real.log (2 / δ) / ε ^ 2)
      have h2 : ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) : ℕ) : ℝ) ≤
          ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      linarith
    have hMposR : (0 : ℝ) < ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hMpos
    have hu_le_eps : Real.sqrt (2 ^ 2 * Real.log (2 / δ) /
        (2 * ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ))) ≤ ε := by
      have harg : 2 ^ 2 * Real.log (2 / δ) /
            (2 * ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ))
          = 2 * Real.log (2 / δ) /
            ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ) := by
        have hne : (((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ)) ≠ 0 :=
          ne_of_gt hMposR
        field_simp
      rw [harg]
      have hle : 2 * Real.log (2 / δ) /
          ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ) ≤ ε ^ 2 := by
        rw [div_le_iff₀ hMposR]
        have hm := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hMge
        nlinarith [hm]
      calc Real.sqrt (2 * Real.log (2 / δ) /
              ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ))
          ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hle
        _ = ε := Real.sqrt_sq hε.le
    have hgIcc : ∀ x : X, o x + 1 ∈ Set.Icc 0 2 := by
      intro x
      have hx := abs_le.mp (hbound x)
      constructor <;> linarith [hx.1, hx.2]
    have hhoef := finite_iid_bounded_average_tail (X := X) (p := p) (f := fun x => o x + 1)
      (Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1) 2 δ hMpos (by norm_num) hδ hδ1 hgIcc
    calc p.probEvent (fun seeds : Fin (Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1) → X =>
            ε ≤ |FinDist.avg o seeds - μ|)
        ≤ p.probEvent (fun seeds : Fin (Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1) → X =>
            Real.sqrt (2 ^ 2 * Real.log (2 / δ) /
              (2 * ((Nat.ceil (2 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ))) ≤
              |FinDist.avg (fun x => o x + 1) seeds - p.expect (fun x => o x + 1)|) := by
            apply probEvent_mono
            intro ω hω
            have hs : |FinDist.avg (fun x => o x + 1) ω - p.expect (fun x => o x + 1)|
                = |FinDist.avg o ω - μ| := by
              rw [avg_add_const hMpos o 1 ω, expect_add_const p o 1, hmean]
              congr 1; ring
            rw [hs]
            exact le_trans hu_le_eps hω
      _ ≤ δ := hhoef

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
