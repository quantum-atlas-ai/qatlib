/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ImagDBrak24.MainResults.SourceDynamics
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# Iterated Derivative of Exponentially Conjugated Matrices via Nested Commutators

This module proves Lemma 6: for square complex matrices `W` and `H`, the `n`-th
derivative of `u ↦ e^{uW} H e^{-uW}` at `s` equals `e^{sW} [(W)^n, H] e^{-sW}`.

## Main statements

* `lemma6_nestedCommutatorDerivative`: `n`-th iterated derivative identity for
  matrix exponential conjugation.

## References

* [Gluza et al., 2024][GluzaEtAl2024ImagDBrak], Lemma 6, Eqs. (61)--(68), p. 17.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.ImagDBrak24.MainResults

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius

private theorem iteratedDeriv_exp_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W H : Matrix ι ι ℂ) (n : ℕ) :
    iteratedDeriv n
        (fun u : ℝ => NormedSpace.exp ((u : ℂ) • W) * H *
          NormedSpace.exp (((-u : ℝ) : ℂ) • W))
      = fun s : ℝ => NormedSpace.exp ((s : ℂ) • W) * nestedCommutator W n H *
          NormedSpace.exp (((-s : ℝ) : ℂ) • W) := by
  induction n with
  | zero => simp [nestedCommutator]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have hpos : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • W))
        (NormedSpace.exp ((s : ℂ) • W) * W) s := by
      simpa [Function.comp_def] using
        (hasDerivAt_exp_smul_const (𝕂 := ℂ) W (s : ℂ)).scomp
          (x := s) Complex.ofRealCLM.hasDerivAt
    have hneg : HasDerivAt (fun u : ℝ => NormedSpace.exp (((-u : ℝ) : ℂ) • W))
        (-(W * NormedSpace.exp (((-s : ℝ) : ℂ) • W))) s := by
      simpa [Function.comp_def, smul_neg, neg_smul] using
        (hasDerivAt_exp_smul_const' (𝕂 := ℂ) (-W) (s : ℂ)).scomp
          (x := s) Complex.ofRealCLM.hasDerivAt
    simpa only [Pi.mul_def, nestedCommutator, commutator, sub_eq_add_neg, mul_add,
      add_mul, mul_neg, neg_mul, mul_assoc] using
      ((hpos.mul_const (nestedCommutator W n H)).mul hneg).deriv

/-- **Lemma 6**: the `n`-th iterated derivative of `u ↦ e^{uW} H e^{-uW}` at `s`
equals `e^{sW} [(W)^n, H] e^{-sW}`. -/
theorem lemma6_nestedCommutatorDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W H : Matrix ι ι ℂ) (_hW : Wᴴ = -W) (n : ℕ) (s : ℝ) :
    iteratedDeriv n
        (fun u : ℝ => NormedSpace.exp ((u : ℂ) • W) * H *
          NormedSpace.exp (((-u : ℝ) : ℂ) • W)) s
      = NormedSpace.exp ((s : ℂ) • W) * nestedCommutator W n H *
          NormedSpace.exp (((-s : ℝ) : ℂ) • W) := by
  have hneg : ∀ t : ℝ, ((-t : ℝ) : ℂ) • W = (t : ℂ) • Wᴴ := by
    intro t
    rw [_hW, smul_neg, ← neg_smul]
    simp
  simp_rw [hneg]
  simpa only [← hneg] using congrFun (iteratedDeriv_exp_conj W H n) s

end Qatlib.Papers.ImagDBrak24.MainResults
