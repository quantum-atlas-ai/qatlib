/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSConsumers
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InteractHybrid

open Matrix MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

def HybridObservableRepresentationV1 : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (O : Matrix I I ℂ)
    (u₀ : QState I) (t : ℝ),
    Continuous L → Continuous H → (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    let A := fun u => L u + Complex.I • H u
    let U := orderedEvolution A 0 t
    let V := fun k : ℝ => orderedEvolution (fun u => Complex.I • (H u + k • L u)) 0 t
    Qatlib.Foundations.PureStateMath.Inner (U *ᵥ u₀) (O *ᵥ (U *ᵥ u₀)) =
      ∫ k : ℝ, ∫ k' : ℝ,
        ((1/(Real.pi*(1+k^2)) * 1/(Real.pi*(1+k'^2)) : ℝ) : ℂ) •
          Qatlib.Foundations.PureStateMath.Inner (V k *ᵥ u₀) (O *ᵥ (V k' *ᵥ u₀))

private theorem cauchy_weight_integrable :
    Integrable (fun k : ℝ => 1 / (Real.pi * (1 + k ^ 2))) := by
  simpa [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm] using!
    integrable_inv_one_add_sq.const_mul Real.pi⁻¹

private theorem unitary_double_cauchy_inner_norm_le (V : ℝ → Matrix (Fin 1) (Fin 1) ℂ)
    (hV : ∀ k, V k ∈ unitaryGroup (Fin 1) ℂ) :
    ‖∫ k : ℝ, ∫ k' : ℝ,
      ((1 / (Real.pi * (1 + k ^ 2)) * 1 / (Real.pi * (1 + k' ^ 2)) : ℝ) : ℂ) •
        Qatlib.Foundations.PureStateMath.Inner (V k *ᵥ Qatlib.Foundations.PureStateMath.Ket 0) (V k' *ᵥ Qatlib.Foundations.PureStateMath.Ket 0)‖ ≤ 1 := by
  let β := fun k : ℝ => 1 / (Real.pi * (1 + k ^ 2))
  have hweight (k k' : ℝ) :
      1 / (Real.pi * (1 + k ^ 2)) * 1 / (Real.pi * (1 + k' ^ 2)) = β k * β k' := by
    dsimp [β]
    ring
  simp_rw [hweight]
  have hβ (k : ℝ) : 0 ≤ β k := by dsimp [β]; positivity
  have hn (k : ℝ) : ‖toEuclidean_fromVec (V k *ᵥ Qatlib.Foundations.PureStateMath.Ket 0)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp
      (normalized_applyGate (hV k) (normalized_ket 0))
  have hc (k k' : ℝ) : ‖Qatlib.Foundations.PureStateMath.Inner (V k *ᵥ Qatlib.Foundations.PureStateMath.Ket 0) (V k' *ᵥ Qatlib.Foundations.PureStateMath.Ket 0)‖ ≤ 1 := by
    rw [← inner_euclidean_fromVec]
    exact (norm_inner_le_norm _ _).trans_eq (by rw [hn, hn]; norm_num)
  have hi (k : ℝ) :
      ‖∫ k' : ℝ, ((β k * β k' : ℝ) : ℂ) •
        Qatlib.Foundations.PureStateMath.Inner (V k *ᵥ Qatlib.Foundations.PureStateMath.Ket 0) (V k' *ᵥ Qatlib.Foundations.PureStateMath.Ket 0)‖ ≤ β k := by
    calc
      _ ≤ ∫ k' : ℝ, β k * β k' :=
        norm_integral_le_of_norm_le (cauchy_weight_integrable.const_mul (β k))
          (Filter.Eventually.of_forall (fun k' => by
            rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hβ k) (hβ k'))]
            exact (mul_le_mul_of_nonneg_left (hc k k') (mul_nonneg (hβ k) (hβ k'))).trans_eq
              (mul_one _)))
      _ = β k := by rw [integral_const_mul, static_lchs_cauchy_density_integral, mul_one]
  calc
    _ ≤ ∫ k : ℝ, β k := norm_integral_le_of_norm_le cauchy_weight_integrable
      (Filter.Eventually.of_forall hi)
    _ = 1 := static_lchs_cauchy_density_integral

private theorem backwards_scalar_evolution :
    orderedEvolution (fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 (-1) =
      Matrix.diagonal (fun _ : Fin 1 => Complex.exp 1) := by
  have hf : (fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) =
      (fun _ : ℝ => Complex.I • (-Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ))) := by
    funext u
    simp [smul_smul, Complex.I_mul_I]
  rw [hf, orderedEvolution_constant_hamiltonian]
  unfold HamiltonianEvolution
  have he : (-Complex.I * ((-1 - 0 : ℝ) : ℂ)) •
      (-Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = Matrix.diagonal (fun _ : Fin 1 => (1 : ℂ)) := by
    simp [smul_smul, Matrix.diagonal_one, Complex.I_mul_I]
  rw [he, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

theorem hybridObservableRepresentation_counterexample : ¬ HybridObservableRepresentationV1 := by
  intro h
  let V := fun k : ℝ => orderedEvolution
    (fun _ : ℝ => Complex.I • (k • (1 : Matrix (Fin 1) (Fin 1) ℂ))) 0 (-1)
  have hV (k : ℝ) : V k ∈ unitaryGroup (Fin 1) ℂ := by
    apply ordered_evolution_hermitian_unitary (Fin 1) (fun _ : ℝ => k • (1 : Matrix (Fin 1) (Fin 1) ℂ))
      continuous_const (fun _ => ?_) 0 (-1)
    exact (Matrix.isHermitian_one).smul (R := ℝ) (IsSelfAdjoint.all k)
  have he := h (Fin 1) (fun _ => 1) (fun _ => 0) 1 (Qatlib.Foundations.PureStateMath.Ket 0) (-1)
    continuous_const continuous_const (fun _ => Matrix.PosSemidef.one) (fun _ => Matrix.isHermitian_zero)
  (try dsimp only at he)
  simp only [smul_zero, add_zero, zero_add, Matrix.one_mulVec] at he
  have hb := unitary_double_cauchy_inner_norm_le V hV
  dsimp only [V] at hb
  rw [← he, backwards_scalar_evolution] at hb
  have hs : (Matrix.diagonal (fun _ : Fin 1 => Complex.exp 1)) *ᵥ Qatlib.Foundations.PureStateMath.Ket 0 =
      (Complex.exp 1) • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1) := by
    ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  rw [hs] at hb
  have hinner : Qatlib.Foundations.PureStateMath.Inner ((Complex.exp 1) • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1)) ((Complex.exp 1) • Qatlib.Foundations.PureStateMath.Ket 0) =
      Complex.ofReal (Real.exp 2) := by
    simp only [inner_apply, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket,
      if_true, mul_one]
    have hexp : Complex.exp 1 = Complex.ofReal (Real.exp 1) :=
      (Complex.ofReal_exp 1).symm
    rw [hexp]
    simp only [Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  rw [hinner, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos 2).le] at hb
  exact (not_le_of_gt (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2))) hb

end Qatlib.Concepts.LchsSimulation.InteractHybrid
