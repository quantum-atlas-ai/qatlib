/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoGlobalSym14.NativeReduction
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

@[expose] public section

/-!
# Exact marked amplitude in the three-cell search model

The actual and reduced Hamiltonian powers give equal amplitudes at the
marked coordinate. Extending the equality through the exponential series
identifies the full and reduced continuous-time readout at every real time.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.NativeDynamics

open Qatlib.Papers.NoGlobalSym14.NativeReduction
open Qatlib.Foundations.GraphModelMath.SrgQuotient
open Qatlib.Foundations.PureStateMath
open scoped Matrix Matrix.Norms.Operator

/-- Evaluate the amplitude obtained by applying a matrix to a fixed vector. -/
private def amplitude {I : Type*} [Fintype I] (z : I → ℂ) (i : I) :
    Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun M := (M *ᵥ z) i
  map_add' A B := by simp [Matrix.add_mulVec]
  map_smul' a A := by simp [Matrix.smul_mulVec]

/-- Evaluating a marked amplitude commutes with the exponential series. -/
private theorem amplitude_exp {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z : I → ℂ) (i : I) :
    (NormedSpace.exp A *ᵥ z) i =
      ∑' p : ℕ, (((p.factorial : ℂ)⁻¹ • A ^ p) *ᵥ z) i := by
  let eval := amplitude z i
  have hsum := ((NormedSpace.expSeries_summable' (𝕂 := ℂ) A).hasSum.map
    eval.toAddMonoidHom eval.continuous_of_finiteDimensional).tsum_eq
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact hsum.symm

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)

/-- Full and reduced Hamiltonian evolution give equal marked amplitudes for any
three-cell initial vector and any real time. -/
theorem marked_evolution {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n - k - 1) (γ t : ℝ) (z : Fin 3 → ℂ) :
    (HamiltonianEvolution (hamiltonian G w γ) t *ᵥ
      (normalizedEmbed G w k (n - k - 1) z).ofLp) w =
    (HamiltonianEvolution (normalHamiltonian k (n - k - 1) l m γ) t *ᵥ z) 0 := by
  simp only [HamiltonianEvolution, amplitude_exp]
  apply tsum_congr
  intro p
  simp only [smul_pow, Matrix.smul_mulVec, Pi.smul_apply]
  rw [actual_power_marked G w h hk hb]

/-- The uniform initial state has the same marked Born weight in the full graph
and in the normalized three-cell model at any real time. -/
theorem uniform_weight {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n - k - 1) (γ t : ℝ) :
    ‖(HamiltonianEvolution (hamiltonian G w γ) t *ᵥ
        (fun _ : V => (1 : ℂ) / (Real.sqrt n : ℂ))) w‖ ^ (2 : ℕ) =
    ‖(HamiltonianEvolution (normalHamiltonian k (n - k - 1) l m γ) t *ᵥ
        uniformCoeffs n k (n - k - 1)) 0‖ ^ (2 : ℕ) := by
  have hmarked := marked_evolution G w h hk hb γ t (uniformCoeffs n k (n - k - 1))
  rw [actual_uniform G w hk hb] at hmarked
  rw [hmarked]

/-- Adding a real scalar to the diagonal of a Hamiltonian preserves each output
weight by multiplying the evolved vector by a unit-modulus phase. -/
private theorem shift_weight (H : Matrix V V ℂ) (c t : ℝ) (z : V → ℂ) (i : V) :
    ‖(HamiltonianEvolution (H + (c : ℂ) • 1) t *ᵥ z) i‖ ^ (2 : ℕ) =
    ‖(HamiltonianEvolution H t *ᵥ z) i‖ ^ (2 : ℕ) := by
  let a : ℂ := -Complex.I * (t : ℂ)
  let phase : ℂ := a * (c : ℂ)
  have hphase : ‖Complex.exp phase‖ = 1 := by
    rw [Complex.norm_exp]
    simp [phase, a, Complex.mul_re]
  have hscalar : NormedSpace.exp (phase • (1 : Matrix V V ℂ)) =
      Complex.exp phase • (1 : Matrix V V ℂ) := by
    have hd (x : ℂ) : x • (1 : Matrix V V ℂ) = Matrix.diagonal (fun _ : V => x) := by
      ext u v
      by_cases huv : u = v <;> simp [Matrix.diagonal, Matrix.smul_apply, huv]
    rw [hd phase, Matrix.exp_diagonal, hd]
    simp [Complex.exp_eq_exp_ℂ]
  have hcomm : Commute (a • H) (phase • (1 : Matrix V V ℂ)) :=
    (Commute.one_right (a • H)).smul_right phase
  change ‖(NormedSpace.exp (a • (H + (c : ℂ) • 1)) *ᵥ z) i‖ ^ (2 : ℕ) =
    ‖(NormedSpace.exp (a • H) *ᵥ z) i‖ ^ (2 : ℕ)
  rw [smul_add, smul_smul, Matrix.exp_add_of_commute _ _ hcomm, hscalar,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    norm_mul, hphase, one_mul]

/-- For the source Laplacian Hamiltonian, the full marked weight of the uniform
initial state is the corresponding three-cell weight at every real time. -/
theorem laplace_weight {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n - k - 1) (γ t : ℝ) :
    ‖(HamiltonianEvolution ((γ : ℂ) • G.lapMatrix ℂ - markProjector w) t *ᵥ
        (fun _ : V => (1 : ℂ) / (Real.sqrt n : ℂ))) w‖ ^ (2 : ℕ) =
    ‖(HamiltonianEvolution (normalHamiltonian k (n - k - 1) l m γ) t *ᵥ
        uniformCoeffs n k (n - k - 1)) 0‖ ^ (2 : ℕ) := by
  have hdegree : G.degMatrix ℂ = (k : ℂ) • (1 : Matrix V V ℂ) := by
    ext u v
    by_cases huv : u = v
    · subst v
      simp [SimpleGraph.degMatrix, Matrix.smul_apply, h.regular u]
    · simp [SimpleGraph.degMatrix, Matrix.smul_apply, huv]
  have hH : (γ : ℂ) • G.lapMatrix ℂ - markProjector w =
      hamiltonian G w γ + ((γ * (k : ℝ) : ℝ) : ℂ) • (1 : Matrix V V ℂ) := by
    rw [SimpleGraph.lapMatrix, hdegree, smul_sub, smul_smul, Complex.ofReal_mul,
      Complex.ofReal_natCast, hamiltonian, neg_smul]
    abel
  rw [hH, shift_weight]
  exact uniform_weight G w h hk hb γ t

end Qatlib.Papers.NoGlobalSym14.NativeDynamics
