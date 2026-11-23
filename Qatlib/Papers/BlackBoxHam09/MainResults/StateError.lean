/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BlackBoxHam09.MainResults.Defs
public import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel

@[expose] public section

/-!
# Euclidean state errors for black-box Hamiltonian perturbations

This module connects the Hamiltonian `L₂` operator norm used by `BlackBoxHam09` to actual
state-vector estimates in `EuclideanSpace`.  The main result is a uniform, state-level form of
the accumulated sandwich-perturbation estimate in [BerryChilds2012], Lemma 7:
the factor `C` is fixed before all index sets, Hamiltonians, states, and parameters.

The module proves two auxiliary bridges:

* two Hermitian evolutions are Lipschitz in their Hamiltonians, both as matrices and on state
  vectors;
* the real diagonal sandwich perturbation used in the paper is again Hermitian.

The uniform estimate still concerns the explicitly displayed sandwich operator.  It does not
construct the paper's state-preparation circuit or prove a trace-distance end-to-end simulation
theorem.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- The difference of two Hamiltonian evolutions is operator-norm Lipschitz in the Hamiltonian
matrices for nonnegative time. -/
theorem evolution_opNorm_sub_le (H K : Ham ι) {t : ℝ} (ht : 0 ≤ t) :
    ‖evolution H t - evolution K t‖ ≤ t * ‖H.mat - K.mat‖ := by
  have hA : ((Complex.I • H.mat) + (Complex.I • H.mat)ᴴ).PosSemidef := by
    have hz : (Complex.I • H.mat) + (Complex.I • H.mat)ᴴ = 0 := by
      rw [Matrix.conjTranspose_smul]
      ext j k
      simp [H.herm.eq, Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply,
        Complex.conj_I]
    rw [hz]
    exact Matrix.PosSemidef.zero
  have hB : ((Complex.I • K.mat) + (Complex.I • K.mat)ᴴ).PosSemidef := by
    have hz : (Complex.I • K.mat) + (Complex.I • K.mat)ᴴ = 0 := by
      rw [Matrix.conjTranspose_smul]
      ext j k
      simp [K.herm.eq, Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply,
        Complex.conj_I]
    rw [hz]
    exact Matrix.PosSemidef.zero
  have hgen := Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_sub_le
    (Complex.I • H.mat) (Complex.I • K.mat) hA hB ht
  rw [evolution_eq_dysonPropagator, evolution_eq_dysonPropagator]
  have hscale : ‖(Complex.I : ℂ) • H.mat - (Complex.I : ℂ) • K.mat‖ = ‖H.mat - K.mat‖ := by
    rw [← smul_sub, norm_smul, Complex.norm_I, one_mul]
  rw [hscale] at hgen
  exact hgen

omit [Nonempty ι] in
/-- On an amplitude vector, the difference between two Hermitian evolutions is bounded using
the Euclidean norm of the input and the `L₂` operator norm of the Hamiltonian difference. -/
theorem evolution_state_error_le (H K : Ham ι) {t : ℝ} (ht : 0 ≤ t)
    (ψ : Qatlib.Foundations.PureStateMath.QState ι) :
    ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec
      (evolution H t *ᵥ ψ - evolution K t *ᵥ ψ)‖ ≤
      t * ‖H.mat - K.mat‖ *
        ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec ψ‖ := by
  rw [← Matrix.sub_mulVec]
  exact (Matrix.l2_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (evolution_opNorm_sub_le H K ht) (norm_nonneg _))

omit [Nonempty ι] in
/-- Multiplication of a Hermitian Hamiltonian by a real diagonal matrix on the left and right,
including the first-order sandwich term, yields a Hermitian perturbation. -/
theorem sandwich_isHermitian (H : Ham ι) (x : ι → ℝ) :
    (sandwich H x).IsHermitian := by
  have hdEq : (diagMatrix x)ᴴ = diagMatrix x := by
    unfold diagMatrix
    rw [Matrix.diagonal_conjTranspose]
    simp
  have hcross : (diagMatrix x * H.mat)ᴴ = H.mat * diagMatrix x := by
    rw [Matrix.conjTranspose_mul, hdEq, H.herm.eq]
  have hsum : (diagMatrix x * H.mat + H.mat * diagMatrix x).IsHermitian := by
    rw [show diagMatrix x * H.mat + H.mat * diagMatrix x =
        diagMatrix x * H.mat + (diagMatrix x * H.mat)ᴴ by rw [hcross]]
    exact Matrix.isHermitian_add_transpose_self _
  have hmiddle : (diagMatrix x * H.mat * diagMatrix x).IsHermitian := by
    rw [show diagMatrix x * H.mat * diagMatrix x =
        diagMatrix x * H.mat * (diagMatrix x)ᴴ by rw [hdEq]]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ H.herm
  unfold sandwich
  exact hsum.add hmiddle

/-- Uniform state-level version of the sandwich error amplification in [BerryChilds2012],
Lemma 7.  For a fixed constant `C`, every Euclidean state, nonempty finite index set,
Hamiltonian, rounding profile, and admissible parameter tuple satisfies the displayed
`t * Λ₁ / ε` amplification bound. -/
theorem lemma7_uniform_state_error :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Inhabited ι]
        (H : Ham ι) (x : ι → ℝ) (ε Λ1 t : ℝ)
        (_hε : 0 < ε) (_hε1 : ε ≤ 1) (_hx : maxAbs x ≤ ε) (_hΛ1 : 0 < Λ1)
        (_ht : 0 ≤ t) (ψ : EuclideanSpace ℂ ι),
        (t * Λ1 / ε) *
          ‖(EuclideanSpace.equiv ι ℂ).symm
            (((ε / Λ1) • sandwich H x) *ᵥ ψ)‖ ≤
          C * spectralNorm H * t * ε * ‖ψ‖ := by
  refine ⟨3, by norm_num,
    fun {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Inhabited ι]
      H x ε Λ1 t hε hε1 hx hΛ1 ht ψ => ?_⟩
  calc
    (t * Λ1 / ε) *
        ‖(EuclideanSpace.equiv ι ℂ).symm
          (((ε / Λ1) • sandwich H x) *ᵥ ψ)‖
        ≤ (t * Λ1 / ε) * (‖(ε / Λ1) • sandwich H x‖ * ‖ψ‖) :=
          mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec _ _) (by positivity)
    _ = ((t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖) * ‖ψ‖ := by rw [mul_assoc]
    _ ≤ 3 * spectralNorm H * t * ε * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right
        (lemma7_error_amplification H x ε Λ1 t hε hε1 hx hΛ1 ht) (norm_nonneg _)

end Qatlib.Papers.BlackBoxHam09.MainResults
