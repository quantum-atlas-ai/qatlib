/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphModelMath.SrgQuotient.Normalization
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false
namespace Qatlib.Foundations.GraphModelMath.SrgQuotient
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)

noncomputable def cellScales (k b : ℕ) : Fin 3 → ℂ :=
  ![1, (Real.sqrt k : ℂ), (Real.sqrt b : ℂ)]

theorem cellScales_ne_zero {k b : ℕ} (hk : 0 < k) (hb : 0 < b) (i : Fin 3) :
    cellScales k b i ≠ 0 := by
  fin_cases i
  · change (1 : ℂ) ≠ 0
    exact one_ne_zero
  · change (Real.sqrt (k : ℝ) : ℂ) ≠ 0
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < k by exact_mod_cast hk))
  · change (Real.sqrt (b : ℝ) : ℂ) ≠ 0
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < b by exact_mod_cast hb))

theorem unscale_diagonal (k b : ℕ) (z : Fin 3 → ℂ) :
    unscale k b z = Matrix.diagonal (fun i => (cellScales k b i)⁻¹) *ᵥ z := by
  funext i
  fin_cases i <;> simp [unscale, cellScales, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, div_eq_mul_inv, mul_comm]

theorem diagonal_inverse {k b : ℕ} (hk : 0 < k) (hb : 0 < b) :
    Matrix.diagonal (fun i => (cellScales k b i)⁻¹) * Matrix.diagonal (cellScales k b) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have he : (fun i => (cellScales k b i)⁻¹ * cellScales k b i) = fun _ => (1 : ℂ) := by
    funext i; exact inv_mul_cancel₀ (cellScales_ne_zero hk hb i)
  rw [he, Matrix.diagonal_one]

noncomputable def normalHamiltonian (k b l m : ℕ) (gamma : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (cellScales k b) * reduced k l m gamma *
    Matrix.diagonal (fun i => (cellScales k b i)⁻¹)

theorem normal_action {k b : ℕ} (hk : 0 < k) (hb : 0 < b)
    (l m : ℕ) (gamma : ℝ) (z : Fin 3 → ℂ) :
    unscale k b (normalHamiltonian k b l m gamma *ᵥ z) =
      reduced k l m gamma *ᵥ unscale k b z := by
  rw [unscale_diagonal, normalHamiltonian]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec, diagonal_inverse hk hb, Matrix.one_mulVec,
    unscale_diagonal]

theorem normalized_hamiltonian {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n-k-1) (gamma : ℝ) (z : Fin 3 → ℂ) :
    hamiltonian G w gamma *ᵥ (normalizedEmbed G w k (n-k-1) z).ofLp =
      (normalizedEmbed G w k (n-k-1)
        (normalHamiltonian k (n-k-1) l m gamma *ᵥ z)).ofLp := by
  change hamiltonian G w gamma *ᵥ embed G w (unscale k (n-k-1) z) = _
  rw [hamiltonian_intertwines G w h]
  change embed G w (reduced k l m gamma *ᵥ unscale k (n-k-1) z) =
    embed G w (unscale k (n-k-1) (normalHamiltonian k (n-k-1) l m gamma *ᵥ z))
  rw [normal_action hk hb]

noncomputable def uniformCoeffs (n k b : ℕ) : Fin 3 → ℂ :=
  fun i => cellScales k b i / (Real.sqrt n : ℂ)

omit [Fintype V] in

theorem actual_uniform {k b : ℕ} (hk : 0 < k) (hb : 0 < b) (n : ℕ) :
    normalizedEmbed G w k b (uniformCoeffs n k b) =
      WithLp.toLp 2 (fun _ : V => (1 : ℂ) / (Real.sqrt n : ℂ)) := by
  have he : unscale k b (uniformCoeffs n k b) = fun _ => (1 : ℂ) / (Real.sqrt n : ℂ) := by
    rw [unscale_diagonal]
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, uniformCoeffs]
    rw [← mul_div_assoc, inv_mul_cancel₀ (cellScales_ne_zero hk hb i)]
    simp
  unfold normalizedEmbed
  rw [he, uniform_embedding]

omit [Fintype V] in

theorem normalized_marked_amplitude (k b : ℕ) (z : Fin 3 → ℂ) :
    (normalizedEmbed G w k b z).ofLp w = z 0 := by
  change embed G w (unscale k b z) w = z 0
  rw [embed_at_marked]
  rfl

theorem normalized_power {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n-k-1) (gamma : ℝ) (p : ℕ) (z : Fin 3 → ℂ) :
    hamiltonian G w gamma ^ p *ᵥ (normalizedEmbed G w k (n-k-1) z).ofLp =
      (normalizedEmbed G w k (n-k-1)
        (normalHamiltonian k (n-k-1) l m gamma ^ p *ᵥ z)).ofLp := by
  induction p generalizing z with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih,
      normalized_hamiltonian G w h hk hb, pow_succ', ← Matrix.mulVec_mulVec]

omit [Fintype V] in

theorem hamiltonian_hermitian (gamma : ℝ) : (hamiltonian G w gamma).IsHermitian := by
  ext v u
  simp [hamiltonian, markProjector, Matrix.conjTranspose_apply,
    SimpleGraph.adjMatrix_apply, G.adj_comm, and_comm]
  split_ifs <;> simp
end Qatlib.Foundations.GraphModelMath.SrgQuotient
