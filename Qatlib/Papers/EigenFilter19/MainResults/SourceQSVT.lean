/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.MarkovBrothers
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# EigenFilter19 — Theorem 1' (polynomial eigenvalue transformation via QSP)

Fixed source: arXiv:1910.14596 (accepted Quantum 2020-11-06), Theorem 1', printed p. 6.

Theorem 1'.: let `U` be an `(α, m, 0)`-block-encoding of a Hermitian `A`, and let
`P ∈ ℝ[x]` be a real polynomial of degree `ℓ` that is even or odd and satisfies
`|P(x)| ≤ 1` for `x ∈ [-1,1]`. Then there is a `(1, m+1, 0)`-block-encoding of
`P(A/α)` using `ℓ` queries to `U, U†` and `O((m+1)ℓ)` other primitive gates.

Formalization boundary. The paper's ancilla count `m` is encoded structurally: the
workspace is `Bool × H` (one extra qubit relative to the block-encoding workspace
`H`), and the `(1,0)` exact block-encoding is `ProjectedUnitaryEncoding` compressed
through `averageFrame F`. The query and gate ledger is the actual counted word
`hermitianResponseWord F d base zs` (both `U` and `U†` count as one query). The
polynomial target is `aeval (α⁻¹ • A) (p.map ofRealHom)`, i.e. `P(A/α)`.

The construction uses the shared same-word QSVT result
`Qatlib.Concepts.SignalPrimitive.HermitianQSVT.hermitian_same_word_actual_qsvt_frobenius_stability`;
we discharge its explicit Lipschitz hypothesis with the Markov-brothers derivative
bound (`markov_brothers_deriv_le`, constant `2 d²`), so the paper statement carries no additional Lipschitz hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.EigenFilter19.MainResults

/-- Markov-brothers Lipschitz bound for a real polynomial bounded by one on `[-1,1]`.
Degree `d`, derivative bounded by `2 d²`, hence Lipschitz constant `2 d²`. This is
the quantitative input that removes the paper's implicit "P is Lipschitz" gap. -/
theorem polynomial_lipschitz_on_unit {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ))
    (hbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |p.eval x - p.eval y| ≤ (2 * (d : ℝ) ^ 2) * |x - y| := by
  have hnat : p.natDegree ≤ d := Polynomial.natDegree_le_of_degree_le hpdeg
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ 2 * (d : ℝ) ^ 2 := by
    intro x hx
    have := Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.markov_brothers_deriv_le
      (d := d) (g := p) hnat (C := (1 : ℝ)) (by norm_num) (by simpa using hbnd) x hx
    simpa using this
  intro x hx y hy
  have hdiff : ∀ z ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ (fun t : ℝ => p.eval t) z :=
    fun z _ => p.differentiableAt
  have hbound : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ‖deriv (fun t : ℝ => p.eval t) z‖ ≤ 2 * (d : ℝ) ^ 2 := by
    intro z hz
    rw [Polynomial.deriv]
    simpa [Real.norm_eq_abs] using hderiv z hz
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun t : ℝ => p.eval t) (s := Set.Icc (-1 : ℝ) 1) (C := 2 * (d : ℝ) ^ 2)
    hdiff hbound (convex_Icc _ _) hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  rw [abs_sub_comm y x, abs_sub_comm (p.eval y) (p.eval x)] at hmv
  simpa using hmv

/-- Source Theorem 1' (arXiv:1910.14596, p. 6). From an exact `(α,0)` same-frame
block-encoding `U` of a Hermitian `A`, a degree-`d` even/odd real polynomial `p`
bounded by one on `[-1,1]` is realised as a `(1,0)` block-encoding of `p(A/α)` by an
actual counted word with `d` queries to `U,U†` and `d+1` further primitive gates. -/
theorem source_theorem1_qsvt
    {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α : ℝ) (p : Polynomial ℝ) (d : ℕ)
    (hA : A.IsHermitian) (hα : 0 < α)
    (hU : BlockEncoding A U F F α 0)
    (hpdeg : p.degree ≤ (d : WithBot ℕ))
    (hpar : HasRealParity d p)
    (hbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ cs : List (AdjointStep (Bool × H)),
      BlockEncoding (aeval (α⁻¹ • A) (p.map Complex.ofRealHom))
        (evaluate (parallelOracle U) cs) (averageFrame F) (averageFrame F) 1 0 ∧
      adjointQueryCount cs = d ∧ adjointGateCount cs = d + 1 := by
  -- The exact block encoding identifies the compressed oracle with `A / α`.
  have hcomp : compress F U F = α⁻¹ • A := by
    have hnorm : ‖A - α • compress F U F‖ = 0 := le_antisymm hU.error_le (norm_nonneg _)
    have hzero : A - α • compress F U F = 0 := norm_eq_zero.mp hnorm
    have hAeq : A = α • compress F U F := sub_eq_zero.mp hzero
    rw [hAeq, smul_smul]
    rw [inv_mul_cancel₀ (ne_of_gt hα), one_smul]
  have hEnc : ProjectedUnitaryEncoding (α⁻¹ • A) U F F :=
    ⟨hU.unitary, hU.left_isometry, hU.right_isometry, hcomp⟩
  have hαinv : IsSelfAdjoint (α⁻¹ : ℝ) := by simp [isSelfAdjoint_iff]
  have hHerm : (α⁻¹ • A).IsHermitian := hA.smul hαinv
  have hL : 0 ≤ 2 * (d : ℝ) ^ 2 := by positivity
  have hLip := polynomial_lipschitz_on_unit hpdeg hbnd
  obtain ⟨base, zs, _hbase, _hzs, _hn, _hresp, hEA, _hEB, hq, hg, _hfrob⟩ :=
    Qatlib.Concepts.SignalPrimitive.HermitianQSVT.hermitian_same_word_actual_qsvt_frobenius_stability
      H I (α⁻¹ • A) (α⁻¹ • A) U U F p d (2 * (d : ℝ) ^ 2)
      hHerm hHerm hEnc hEnc hpdeg hpar hbnd hL hLip
  refine ⟨Qatlib.Concepts.SignalPrimitive.HermitianQSVT.hermitianResponseWord F d base zs,
    ?_, hq, hg⟩
  exact Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding hEA

end Qatlib.Papers.EigenFilter19.MainResults
