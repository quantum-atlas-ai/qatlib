/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampling25.MainResults.Entropy.WeakEntropyFactorization
public import Qatlib.Concepts.QuantumEntropy.EntropyCalculus

@[expose] public section

/-!
# Reducing the weak entropy factorization to a marginal bound

`Qatlib.Papers.GibbsSampling25.MainResults.Entropy.weak_entropy_factorization`
records Lemma 2.5 of arXiv:2412.01732v1 (p.5, eq. (5)) as a predicate: for
states `ρ, σ` on `H_A ⊗ H_B ⊗ H_C ⊗ H_D` with `σ > 0`,

`D_ABC(ρ‖σ) ≤ D_AB(ρ‖σ) + D_BC(ρ‖σ) + ‖H_σ(A:C|D)‖∞`,

where `D_X` is the conditional relative entropy of Definition 2.4, eq. (4).
Every summand of the three `D_X` shares the unconditional term `D(ρ‖σ)`, so the
claim is equivalent to a bound on the relative entropies of the two marginals
`ρ_AB`, `ρ_BC` against the marginals of the reference state `σ`. That is the
form in which the proof of Lemma B.1 (Appendix B.1) concludes: the trace
identity for `H_σ(A:C|D)` together with the duality of the Schatten-1 norm
against the operator norm of `H_σ(A:C|D)` yields exactly the marginal bound
proved here to be equivalent to Lemma 2.5.

This file establishes that equivalence and the non-negativity of the
conditional relative entropy for the concrete marginal given by the partial
trace of the source model, which is the data-processing step cited in the proof
of Lemma B.1. The operator-norm estimate for the matrix-valued MCMI itself is
not available at this interface: `McmiNorm` is an explicit datum of the source
model, so Lemma 2.5 in full remains open.

## Main statements

* `condRelEnt_le_iff_marginal_relEnt_sum_le`: the equivalence between
  Lemma 2.5 and the marginal relative-entropy bound.
* `condRelEnt_self` and `condRelEnt_le_sum_self`: at `ρ = σ` the three
  conditional relative entropies vanish, so the claim holds with `H = 0`.
* `condRelEnt_traceLeft_nonneg`: data processing under the partial trace, i.e.
  non-negativity of the conditional relative entropy over the complementary
  system.

## References

* arXiv:2412.01732v1, Lemma 2.5 (p.5, eq. (5)) and Lemma B.1 (Appendix B.1).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.GibbsSampling25.MainResults.Entropy

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

variable {I JABC JAB JBC : Type} [Fintype I] [DecidableEq I]
  [Fintype JABC] [DecidableEq JABC] [Fintype JAB] [DecidableEq JAB]
  [Fintype JBC] [DecidableEq JBC]

/-- The inequality of Lemma 2.5 of arXiv:2412.01732v1, written with an
arbitrary bound `H` in place of `‖H_σ(A:C|D)‖∞`, is equivalent to the bound

`D(mAB ρ‖mAB σ) + D(mBC ρ‖mBC σ) ≤ D(mABC ρ‖mABC σ) + D(ρ‖σ) + H`

on the relative entropies of the three marginal pairs. The equivalence is the
algebraic content of Definition 2.4, eq. (4): the three conditional relative
entropies all contain the term `D(ρ‖σ)` with coefficient one. -/
theorem condRelEnt_le_iff_marginal_relEnt_sum_le
    (mABC : Density I → Density JABC) (mAB : Density I → Density JAB)
    (mBC : Density I → Density JBC) (ρ σ : Density I) (H : ℝ) :
    condRelEnt mABC ρ σ ≤ condRelEnt mAB ρ σ + condRelEnt mBC ρ σ + H ↔
      relEnt (mAB ρ) (mAB σ) + relEnt (mBC ρ) (mBC σ) ≤
        relEnt (mABC ρ) (mABC σ) + relEnt ρ σ + H := by
  unfold condRelEnt
  constructor <;> intro h <;> linarith

/-- All three conditional relative entropies of Lemma 2.5 with their marginal
maps coincide: the unconditional term cancels the marginal's own relative
entropy of a state with itself. -/
theorem condRelEnt_self {J : Type} [Fintype J] [DecidableEq J]
    (m : Density I → Density J) (ρ : Density I) :
    condRelEnt m ρ ρ = 0 := by
  unfold condRelEnt
  rw [relEnt_self, relEnt_self]
  ring

/-- Lemma 2.5 of arXiv:2412.01732v1 at `ρ = σ`: every conditional relative
entropy of a state against itself vanishes, so the inequality holds with any
non-negative bound, in particular with `‖H_σ(A:C|D)‖∞ = 0`. -/
theorem condRelEnt_le_sum_self (mABC : Density I → Density JABC)
    (mAB : Density I → Density JAB) (mBC : Density I → Density JBC)
    (ρ : Density I) (H : ℝ) (hH : 0 ≤ H) :
    condRelEnt mABC ρ ρ ≤ condRelEnt mAB ρ ρ + condRelEnt mBC ρ ρ + H := by
  rw [condRelEnt_self, condRelEnt_self, condRelEnt_self]
  linarith

/-- Data processing under the partial trace: for states `ρ, σ` on
`(A ⊗ B) ⊗ (C ⊗ D)` with `σ` nonsingular, the conditional relative entropy of
Definition 2.4, eq. (4) with the marginal `ρ ↦ ρ_AB` (the partial trace over
`C ⊗ D`) is non-negative. This is the monotonicity of the Umegaki relative
entropy under the partial trace, quoted as the data-processing step of the
proof of Lemma 2.5 in Appendix B.1. -/
theorem condRelEnt_traceLeft_nonneg {A B C Dd : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype Dd] [DecidableEq Dd]
    (ρ σ : Density ((A × B) × (C × Dd))) (hσ : (state σ).M.NonSingular) :
    0 ≤ condRelEnt (fun τ => localState (state τ).traceLeft) ρ σ := by
  have h := (dpi_ssa_partial_trace_consumers.2.2.1 (A := A) (B := B) (C := C) (D := Dd)
    ρ σ hσ).2.2.1
  show 0 ≤ relEnt ρ σ - relEnt (localState (state ρ).traceLeft) (localState (state σ).traceLeft)
  exact h

end Qatlib.Papers.GibbsSampling25.MainResults.Entropy
