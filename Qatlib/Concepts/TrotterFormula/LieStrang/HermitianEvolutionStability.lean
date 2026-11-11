/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.UnitaryExponentialRemainder

/-!
# Stability of Hermitian Hamiltonian evolution

This module proves Lipschitz continuity of finite-dimensional Hamiltonian evolution with respect
to the Hermitian generator, without requiring the two generators to commute. It also transfers
the operator bound to trace-norm conjugation error with a finite reference system, using matrix
and trace-norm techniques as in [Bhatia1997].

## Main statements

* `hermitian_evolution_noncommuting_stability_fintype`: the bound `|t| * ‖H - G‖` for arbitrary
  finite matrix indices.
* `hermitian_evolution_noncommuting_stability`: the operator-indexed version.
* `hermitian_evolution_reference_stability`: the reference-system trace-norm bound.

## References

* [Bhatia, 1997][Bhatia1997]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.TrotterFormula.LieStrang
open Matrix Set
open scoped Classical Matrix.Norms.L2Operator ComplexOrder
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- For Hermitian matrices on any finite index type, the evolutions at time `t` differ in
operator norm by at most `|t| * ‖H - G‖`. -/
theorem hermitian_evolution_noncommuting_stability_fintype
    {I : Type*} [Fintype I] [DecidableEq I]
    (H G : Matrix I I ℂ) (t : ℝ) (hH : H.IsHermitian) (hG : G.IsHermitian) :
    ‖HamiltonianEvolution H t - HamiltonianEvolution G t‖ ≤ |t| * ‖H-G‖ := by
  let A : Matrix I I ℂ := (-Complex.I * (t : ℂ)) • H
  let B : Matrix I I ℂ := (-Complex.I * (t : ℂ)) • G
  let U : ℝ → Matrix I I ℂ := fun s => NormedSpace.exp (s • A)
  let V : ℝ → Matrix I I ℂ := fun s => NormedSpace.exp ((1-s) • B)
  let f : ℝ → Matrix I I ℂ := fun s => U s * V s
  have hU (s : ℝ) : HasDerivAt U (U s * A) s := hasDerivAt_exp_smul_const A s
  have hV (s : ℝ) : HasDerivAt V (-(B * V s)) s := by
    have hi : HasDerivAt (fun x : ℝ => 1-x) (-1) s := by
      simpa using! (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
    convert! (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B (1-s)).scomp s hi using 1
    (try simp [V])

  have hf (s : ℝ) : HasDerivAt f (U s * (A-B) * V s) s := by
    convert! (hU s).mul (hV s) using 1
    (try dsimp [f])
    noncomm_ring
  have he (K : Matrix I I ℂ) (s : ℝ) :
      NormedSpace.exp (s • ((-Complex.I * (t : ℂ)) • K)) =
        HamiltonianEvolution K (s*t) := by
    congr 1
    ext i j
    simp [HamiltonianEvolution, Matrix.smul_apply, Complex.real_smul]
    ring
  have hnU (s : ℝ) : ‖U s‖ ≤ 1 := by
    rw [show U s = HamiltonianEvolution H (s*t) from he H s]
    exact l2_norm_unitary_le_one (hamiltonianEvolution_unitary hH _)
  have hnV (s : ℝ) : ‖V s‖ ≤ 1 := by
    rw [show V s = HamiltonianEvolution G ((1-s)*t) from he G (1-s)]
    exact l2_norm_unitary_le_one (hamiltonianEvolution_unitary hG _)
  have hd (s : ℝ) : ‖U s * (A-B) * V s‖ ≤ ‖A-B‖ := by
    calc
      _ ≤ ‖U s‖ * ‖A-B‖ * ‖V s‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖A-B‖ * 1 := by gcongr <;> first | exact hnU s | exact hnV s
      _ = _ := by ring
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_ : s ∈ Icc (0 : ℝ) 1) => (hf s).hasDerivWithinAt)
    (fun s (_ : s ∈ Ico (0 : ℝ) 1) => hd s) 1 ⟨zero_le_one, le_rfl⟩
  have hn : ‖A-B‖ = |t| * ‖H-G‖ := by
    rw [show A-B = (-Complex.I * (t : ℂ)) • (H-G) from (smul_sub _ _ _).symm]
    simp [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hn] at hb
  simpa [f, U, V, A, B, HamiltonianEvolution] using! hb

/-- For Hermitian operators `H` and `G`, their evolutions at time `t` differ by at most `|t| *
‖H - G‖` in operator norm. -/
theorem hermitian_evolution_noncommuting_stability
    (D : ℕ) (H G : Operator D) (t : ℝ) (hH : H.IsHermitian) (hG : G.IsHermitian) :
    ‖HamiltonianEvolution H t - HamiltonianEvolution G t‖ ≤ |t| * ‖H-G‖ :=
  hermitian_evolution_noncommuting_stability_fintype H G t hH hG

/-- Conjugating any matrix `X` by the two Hermitian evolutions tensored with a reference
identity gives trace-norm difference at most `2 * |t| * ‖H - G‖ * Matrix.traceNorm X`. -/
theorem hermitian_evolution_reference_stability
    (D r : ℕ) (H G : Operator D) (t : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian) :
    Matrix.traceNorm (TensorGate (HamiltonianEvolution H t) (1 : Operator r)*X*
      (TensorGate (HamiltonianEvolution H t) (1 : Operator r))ᴴ-
      TensorGate (HamiltonianEvolution G t) (1 : Operator r)*X*
      (TensorGate (HamiltonianEvolution G t) (1 : Operator r))ᴴ) ≤
        2 * |t| * ‖H-G‖*Matrix.traceNorm X := by
  exact (finite_reference_conjugation_error _ _ r X
    (hamiltonianEvolution_unitary hH t) (hamiltonianEvolution_unitary hG t)).trans
      (by have h := hermitian_evolution_noncommuting_stability D H G t hH hG
          calc
            _ ≤ (2 * (|t| * ‖H-G‖)) * Matrix.traceNorm X :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num))
                (Matrix.traceNorm_nonneg X)
            _ = _ := by ring)
end Qatlib.Concepts.TrotterFormula.LieStrang
