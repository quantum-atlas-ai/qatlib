/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.LchsDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.InteractHybrid
open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeTrapezoid
open Qatlib.Concepts.LchsSimulation.TrapPrepared
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.LchsSimulation.TimeTrapezoid

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

section Clause1Loaded

theorem lchs2d_coeff_homogeneous (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (j : Fin (M + 1)) :
    lchs2dCoeff b s t K M Mt (Fin.castAdd ((M + 1) * (Mt + 1)) j) = kTrapCoeff K M j := by
  simp [lchs2dCoeff, j.isLt]

theorem lchs2d_coeff_source (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (p : Fin (M + 1) × Fin (Mt + 1)) :
    lchs2dCoeff b s t K M Mt (Fin.natAdd (M + 1) (finProdFinEquiv p)) =
      lchs2dSourceCoeff b s t K M Mt p := by
  unfold lchs2dCoeff
  rw [dif_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]

theorem lchs2d_unitary_homogeneous (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K M Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ) (j : Fin (M + 1)) :
    lchs2dUnitary L H s t K M Mt B P (Fin.castAdd ((M + 1) * (Mt + 1)) j) =
      orderedEvolution
        (fun u => Complex.I • (H u + (kTrapNode K M j) • L u)) s t := by
  simp [lchs2dUnitary, j.isLt]

theorem lchs2d_unitary_source (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K M Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (p : Fin (M + 1) × Fin (Mt + 1)) :
    lchs2dUnitary L H s t K M Mt B P (Fin.natAdd (M + 1) (finProdFinEquiv p)) =
      inh2dTrapSourceKUnitary L H s t K M Mt p.1 p.2 * (P p.2 * Bᴴ) := by
  unfold lchs2dUnitary
  rw [dif_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]

private theorem kTrapWeight_pos (K M : ℕ) (hK : 0 < K) (hM : 0 < M) (j : Fin (M + 1)) :
    0 < kTrapWeight K M j := by
  unfold kTrapWeight
  split_ifs
  · exact div_pos (by exact_mod_cast hK) (by exact_mod_cast hM)
  · exact div_pos (by exact_mod_cast (mul_pos (by norm_num) hK)) (by exact_mod_cast hM)

private theorem kTrapCoeff_real_pos (K M : ℕ) (hK : 0 < K) (hM : 0 < M)
    (j : Fin (M + 1)) :
    0 < (kTrapWeight K M j / (Real.pi * (1 + (kTrapNode K M j) ^ 2))) := by
  have hd : 0 < Real.pi * (1 + (kTrapNode K M j) ^ 2) := by positivity
  exact div_pos (kTrapWeight_pos K M hK hM j) hd

private theorem kTrapCoeff_norm_pos (K M : ℕ) (hK : 0 < K) (hM : 0 < M)
    (j : Fin (M + 1)) : 0 < ‖kTrapCoeff K M j‖ := by
  have hr := kTrapCoeff_real_pos K M hK hM j
  rw [kTrapCoeff, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
  exact hr

theorem lchs2d_coefficient_mass (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (hst : s ≤ t) :
    coefficientMass (lchs2dCoeff b s t K M Mt) =
      lchs2dKMass K M * (1 + lchs2dSourceMass b s t Mt) := by
  have hsplit :
      (∑ x : Fin (lchs2dLabelCount M Mt), ‖lchs2dCoeff b s t K M Mt x‖) =
        (∑ j : Fin (M + 1), ‖lchs2dCoeff b s t K M Mt (Fin.castAdd ((M + 1) * (Mt + 1)) j)‖) +
          (∑ y : Fin ((M + 1) * (Mt + 1)),
            ‖lchs2dCoeff b s t K M Mt (Fin.natAdd (M + 1) y)‖) := by
    simpa only [lchs2dLabelCount] using!
      (Fin.sum_univ_add (f := fun x : Fin ((M + 1) + (M + 1) * (Mt + 1)) =>
        ‖lchs2dCoeff b s t K M Mt x‖))
  unfold coefficientMass
  rw [hsplit]
  simp_rw [lchs2d_coeff_homogeneous]
  have he := (finProdFinEquiv : Fin (M + 1) × Fin (Mt + 1) ≃ Fin ((M + 1) * (Mt + 1))).sum_comp
    (fun y => ‖lchs2dCoeff b s t K M Mt (Fin.natAdd (M + 1) y)‖)
  rw [← he]
  simp_rw [lchs2d_coeff_source, lchs2dSourceCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inh_trap_weight_nonneg Mt s t hst _),
    Real.norm_of_nonneg (norm_nonneg _)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hinner : ∀ l : Fin (Mt + 1),
      (∑ j : Fin (M + 1), inhTrapWeight Mt s t l * ‖kTrapCoeff K M j‖ *
        ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖) =
      inhTrapWeight Mt s t l * ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖ *
        (∑ j : Fin (M + 1), ‖kTrapCoeff K M j‖) := by
    intro l
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  unfold lchs2dKMass lchs2dSourceMass
  ring

theorem lchs2d_mass_pos (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (hst : s ≤ t) (hK : 0 < K) (hM : 0 < M) :
    0 < coefficientMass (lchs2dCoeff b s t K M Mt) := by
  rw [lchs2d_coefficient_mass b s t K M Mt hst]
  have hkm : 0 < lchs2dKMass K M := by
    unfold lchs2dKMass
    exact Finset.sum_pos (fun i _ => kTrapCoeff_norm_pos K M hK hM i)
      (Finset.univ_nonempty)
  have hsm : 0 ≤ lchs2dSourceMass b s t Mt := by
    unfold lchs2dSourceMass
    exact Finset.sum_nonneg (fun l _ =>
      mul_nonneg (inh_trap_weight_nonneg Mt s t hst l) (norm_nonneg _))
  have hone : 1 ≤ 1 + lchs2dSourceMass b s t Mt := by linarith
  nlinarith

theorem lchs2d_unified_unitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K M Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    ∀ x, lchs2dUnitary L H s t K M Mt B P x ∈ unitaryGroup I ℂ := by
  have hV (a z : ℝ) (j : Fin (M + 1)) :
      orderedEvolution (fun u => Complex.I • (H u + (kTrapNode K M j) • L u)) a z ∈
        unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I (fun u => H u + (kTrapNode K M j) • L u)
      (by fun_prop)
      (fun u => (hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _))) a z
  have hS (j : Fin (M + 1)) (l : Fin (Mt + 1)) :
      inh2dTrapSourceKUnitary L H s t K M Mt j l ∈ unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I (fun u => H u + (kTrapNode K M j) • L u)
      (by fun_prop)
      (fun u => (hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _)))
      (inhTrapNode Mt s t l) t
  intro x
  by_cases hx : (x : ℕ) < M + 1
  · rw [lchs2dUnitary]
    simp only [dif_pos hx]
    exact hV _ _ _
  · rw [lchs2dUnitary]
    simp only [dif_neg hx]
    exact (unitaryGroup I ℂ).mul_mem (hS _ _)
      ((unitaryGroup I ℂ).mul_mem (hP _) (Unitary.star_mem hB))

theorem lchs2d_raw_vector (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ) (i₀ : I)
    (hB : B ∈ unitaryGroup I ℂ)
    (hprep : ∀ l : Fin (Mt + 1), b (inhTrapNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ = ((‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
        b (inhTrapNode Mt s t l)) :
    (∑ x, lchs2dCoeff b s t K M Mt x • lchs2dUnitary L H s t K M Mt B P x) *ᵥ
        (B *ᵥ Ket i₀) =
      (∑ j : Fin (M + 1), kTrapCoeff K M j •
        orderedEvolution (fun u => Complex.I • (H u + (kTrapNode K M j) • L u)) s t) *ᵥ
          (B *ᵥ Ket i₀) + inh2dTrapSourceSum L H b s t K M Mt := by
  have hundo : Bᴴ *ᵥ (B *ᵥ Ket i₀) = Ket i₀ := by
    have hBB : Bᴴ * B = 1 := Matrix.mem_unitaryGroup_iff'.mp hB
    rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  have hsplit :
      (∑ x : Fin (lchs2dLabelCount M Mt),
        lchs2dCoeff b s t K M Mt x • lchs2dUnitary L H s t K M Mt B P x) =
        (∑ j : Fin (M + 1),
          lchs2dCoeff b s t K M Mt (Fin.castAdd ((M + 1) * (Mt + 1)) j) •
            lchs2dUnitary L H s t K M Mt B P (Fin.castAdd ((M + 1) * (Mt + 1)) j)) +
          (∑ y : Fin ((M + 1) * (Mt + 1)),
            lchs2dCoeff b s t K M Mt (Fin.natAdd (M + 1) y) •
              lchs2dUnitary L H s t K M Mt B P (Fin.natAdd (M + 1) y)) := by
    simpa only [lchs2dLabelCount] using!
      (Fin.sum_univ_add (f := fun x : Fin ((M + 1) + (M + 1) * (Mt + 1)) =>
        lchs2dCoeff b s t K M Mt x • lchs2dUnitary L H s t K M Mt B P x))
  rw [hsplit, Matrix.add_mulVec]
  simp_rw [lchs2d_coeff_homogeneous, lchs2d_unitary_homogeneous]
  congr 1
  rw [Matrix.sum_mulVec]
  have he := (finProdFinEquiv : Fin (M + 1) × Fin (Mt + 1) ≃ Fin ((M + 1) * (Mt + 1))).sum_comp
    (fun y => (lchs2dCoeff b s t K M Mt (Fin.natAdd (M + 1) y) •
      lchs2dUnitary L H s t K M Mt B P (Fin.natAdd (M + 1) y)) *ᵥ (B *ᵥ Ket i₀))
  rw [← he]
  simp_rw [lchs2d_coeff_source, lchs2d_unitary_source, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hundo]
  have hnode (p : Fin (M + 1) × Fin (Mt + 1)) :
      (lchs2dSourceCoeff b s t K M Mt p) •
        (inh2dTrapSourceKUnitary L H s t K M Mt p.1 p.2 *ᵥ (P p.2 *ᵥ Ket i₀)) =
      (inhTrapWeight Mt s t p.2 : ℂ) • (kTrapCoeff K M p.1 •
        (inh2dTrapSourceKUnitary L H s t K M Mt p.1 p.2 *ᵥ b (inhTrapNode Mt s t p.2))) := by
    unfold lchs2dSourceCoeff
    by_cases hz : b (inhTrapNode Mt s t p.2) = 0
    · simp [hz, toEuclidean_fromVec]
    · rw [hprep p.2 hz, Matrix.mulVec_smul, smul_smul, smul_smul]
      have hn : ‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        intro h
        apply hz
        exact (WithLp.toLp_injective 2) (by simpa only [toEuclidean_fromVec,
          WithLp.toLp_zero] using! h)
      rw [Complex.ofReal_inv, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn), mul_one]
  simp_rw [hnode]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← Matrix.smul_mulVec, ← Matrix.sum_mulVec]
  rfl

theorem lchs2d_raw_vector_kTrapSum (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ) (i₀ : I)
    (hB : B ∈ unitaryGroup I ℂ)
    (hprep : ∀ l : Fin (Mt + 1), b (inhTrapNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ = ((‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
        b (inhTrapNode Mt s t l)) :
    (∑ x, lchs2dCoeff b s t K M Mt x • lchs2dUnitary L H s t K M Mt B P x) *ᵥ
        (B *ᵥ Ket i₀) =
      (kTrapSum L H s t K M) *ᵥ (B *ᵥ Ket i₀) + inh2dTrapSourceSum L H b s t K M Mt := by
  rw [kTrapSum]
  exact lchs2d_raw_vector L H b s t K M Mt B P i₀ hB hprep

theorem lchsLoadedNode_index (b : ℝ → QState I) (s t : ℝ) (Mt : ℕ) (l : Fin (Mt + 1)) :
    (lchsLoadedNode b s t Mt l).index = l.val := rfl

theorem lchsLoadedNode_position (b : ℝ → QState I) (s t : ℝ) (Mt : ℕ) (l : Fin (Mt + 1)) :
    (lchsLoadedNode b s t Mt l).position = inhTrapNode Mt s t l := rfl

theorem lchsLoadedNode_source (b : ℝ → QState I) (s t : ℝ) (Mt : ℕ) (l : Fin (Mt + 1)) :
    (lchsLoadedNode b s t Mt l).source = b (inhTrapNode Mt s t l) := rfl

theorem lchsLoadedNode_count (Mt : ℕ) :
    (Finset.univ : Finset (Fin (Mt + 1))).card = lchs2dSourceStateCount Mt := by
  simp [lchs2dSourceStateCount, Fintype.card_fin]

end Clause1Loaded

section Clause1Program

theorem lchs2d_program_expanded (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (j₀ : Fin (lchs2dLabelCount M Mt)) (i₀ : I) (k : ℕ)
    (hst : s ≤ t) (hK : 0 < K) (hM : 0 < M)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    let S := Finset.univ.filter (fun x : Fin (lchs2dLabelCount M Mt) × I => x.1 = j₀)
    IsUnitaryCircuit (staticLchsCompile (lchs2dCoeff b s t K M Mt)
      (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀ k) ∧
    Run (preparedMark S) (staticLchsCompile (lchs2dCoeff b s t K M Mt)
      (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀ k) (Ket (j₀,i₀)) =
      Run (preparedMark S) (preparedAACircuit
        (coefficientLCUUnitary (lchs2dCoeff b s t K M Mt)
          (lchs2dUnitary L H s t K M Mt B P) j₀ *
            TensorGate (1 : Matrix (Fin (lchs2dLabelCount M Mt))
              (Fin (lchs2dLabelCount M Mt)) ℂ) B) (j₀,i₀) k) (Ket (j₀,i₀)) ∧
    (staticLchsWord k).count .selectF = k + 1 ∧
    (staticLchsWord k).count .selectB = k ∧
    (staticLchsWord k).count .inputF = k + 1 ∧
    (staticLchsWord k).count .inputB = k ∧
    (staticLchsWord k).count .coefF = 2 * k + 1 ∧
    (staticLchsWord k).count .coefB = 2 * k + 1 ∧
    QueryCount (staticLchsCompile (lchs2dCoeff b s t K M Mt)
      (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀ k) = k ∧
    (staticLchsWord k).length = 10 * k + 4 := by
  have h := static_lchs_actual_expanded_prepare_select_amplification I
    (lchs2dLabelCount M Mt) (lchs2dCoeff b s t K M Mt)
    (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀ k
    (lchs2d_mass_pos b s t K M Mt hst hK hM)
    (lchs2d_unified_unitary L H s t K M Mt B P hL hH hPSD hHerm hB hP) hB
  (try dsimp only at h)
  rcases h with ⟨hcirc, hrun, hsf, hsb, hif, hib, hcf, hcb, hq, hlen⟩
  exact ⟨hcirc, hrun, hsf, hsb, hif, hib, hcf, hcb, hq, hlen⟩

theorem lchs2d_initial_data_branch (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (j₀ : Fin (lchs2dLabelCount M Mt)) (i₀ : I)
    (hst : s ≤ t) (hK : 0 < K) (hM : 0 < M)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    let S := Finset.univ.filter (fun x : Fin (lchs2dLabelCount M Mt) × I => x.1 = j₀)
    staticLchsDataBranch j₀
        (Run (preparedMark S) (staticLchsCompile (lchs2dCoeff b s t K M Mt)
          (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀ 0) (Ket (j₀,i₀))) =
      (∑ j, (lchs2dCoeff b s t K M Mt j /
        (coefficientMass (lchs2dCoeff b s t K M Mt) : ℂ)) •
          lchs2dUnitary L H s t K M Mt B P j) *ᵥ (B *ᵥ Ket i₀) := by
  have h := static_lchs_actual_initial_data_branch I (lchs2dLabelCount M Mt)
    (lchs2dCoeff b s t K M Mt) (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀
    (lchs2d_mass_pos b s t K M Mt hst hK hM)
    (lchs2d_unified_unitary L H s t K M Mt B P hL hH hPSD hHerm hB hP) hB
  (try dsimp only at h)
  exact h

theorem lchs2d_window_access_budget (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (j₀ : Fin (lchs2dLabelCount M Mt)) (i₀ : I) (m : ℕ) (j : Fin m)
    (hst : s ≤ t) (hK : 0 < K) (hM : 0 < M)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    (staticLchsWord j.val).count .inputF + (staticLchsWord j.val).count .inputB ≤ 2 * m + 1 ∧
      (staticLchsWord j.val).count .selectF + (staticLchsWord j.val).count .selectB ≤
        2 * m + 1 := by
  exact static_lchs_window_actual_access_budget I (lchs2dLabelCount M Mt)
    (lchs2dCoeff b s t K M Mt) (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀
    (lchs2d_mass_pos b s t K M Mt hst hK hM)
    (lchs2d_unified_unitary L H s t K M Mt B P hL hH hPSD hHerm hB hP) hB m j

theorem lchs2d_window_bound (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ) (τ : ℝ)
    (hst : s ≤ t) (hK : 0 < K) (hM : 0 < M) (hτ : 0 < τ) :
    0 < staticLchsWindow (coefficientMass (lchs2dCoeff b s t K M Mt)) τ ∧
      (staticLchsWindow (coefficientMass (lchs2dCoeff b s t K M Mt)) τ : ℝ) ≤
        2 * coefficientMass (lchs2dCoeff b s t K M Mt) / τ + 1 :=
  static_lchs_window_bound _ τ (lchs2d_mass_pos b s t K M Mt hst hK hM) hτ

theorem lchs2d_source_label_count (M Mt : ℕ) :
    lchs2dSelectPrepareCount M Mt =
      (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card ∧
    lchs2dSelectInputAdjointCount M Mt =
      (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card := by
  simp [lchs2dSelectPrepareCount, lchs2dSelectInputAdjointCount,
    Fintype.card_prod, Fintype.card_fin]

theorem lchs2d_source_branch_factors (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K M Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (p : Fin (M + 1) × Fin (Mt + 1)) :
    lchs2dUnitary L H s t K M Mt B P (Fin.natAdd (M + 1) (finProdFinEquiv p)) =
      inh2dTrapSourceKUnitary L H s t K M Mt p.1 p.2 * (P p.2 * Bᴴ) :=
  lchs2d_unitary_source L H s t K M Mt B P p

theorem lchs2d_window_ledger_counts (M Mt m : ℕ) :
    (lchs2dWindowLedger M Mt m).sourcePrepare =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card ∧
      (lchs2dWindowLedger M Mt m).sourceInputAdjoint =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card ∧
      (lchs2dWindowLedger M Mt m).sourceStates = Mt + 1 ∧
      (lchs2dWindowLedger M Mt m).markQueries = m ∧
      (lchs2dWindowLedger M Mt m).wordLength = 10 * m + 4 := by
  simp [lchs2dWindowLedger, lchs2dSelectPrepareCount, lchs2dSelectInputAdjointCount,
    lchs2dSourceStateCount, Fintype.card_prod, Fintype.card_fin]

end Clause1Program

section Clause4ResourceProofs

theorem lchsRegisterBits_spec (n : ℕ) : n < 2 ^ (lchsRegisterBits n) := by
  rw [lchsRegisterBits, Nat.log2_eq_log_two]
  exact Nat.lt_pow_of_log_lt (by norm_num) (Nat.lt_succ_self _)

theorem lchsClassicalBits_spec (N m Mt : ℕ) :
    N < 2 ^ (lchsRegisterBits N) ∧ m < 2 ^ (lchsRegisterBits m) ∧
      Mt + 1 < 2 ^ (lchsRegisterBits (Mt + 1)) :=
  ⟨lchsRegisterBits_spec N, lchsRegisterBits_spec m, lchsRegisterBits_spec (Mt + 1)⟩

theorem lchsFixedGateCount_eq (k : ℕ) : lchsFixedGateCount k = 9 * k + 4 := by
  simp [lchsFixedGateCount]; omega

theorem lchsQuantumSpace_spec (N : ℕ) (dataStates : ℕ) :
    lchsQuantumSpace N dataStates =
      (Finset.univ : Finset (Fin N × Fin dataStates)).card := by
  simp [lchsQuantumSpace, Fintype.card_prod, Fintype.card_fin]

theorem lchsTheoremResources_spec (N m Mt dataStates : ℕ) :
    (lchsTheoremResources N m Mt dataStates).labels = N ∧
      (lchsTheoremResources N m Mt dataStates).window = m ∧
      (lchsTheoremResources N m Mt dataStates).fixedGates = 9 * m + 4 ∧
      (lchsTheoremResources N m Mt dataStates).oracleQueries = m ∧
      (lchsTheoremResources N m Mt dataStates).classicalBits =
        lchsRegisterBits N + lchsRegisterBits m + lchsRegisterBits (Mt + 1) ∧
      (lchsTheoremResources N m Mt dataStates).quantumSpace = N * dataStates := by
  simp [lchsTheoremResources, lchsFixedGateCount_eq, lchsClassicalBits, lchsQuantumSpace]

theorem lchsTh1Resources_spec (N m dataStates : ℕ) :
    (lchsTh1Resources N m dataStates).labels = N ∧
      (lchsTh1Resources N m dataStates).window = m ∧
      (lchsTh1Resources N m dataStates).fixedGates = 9 * m + 4 ∧
      (lchsTh1Resources N m dataStates).oracleQueries = m ∧
      (lchsTh1Resources N m dataStates).classicalBits =
        lchsRegisterBits N + lchsRegisterBits m + lchsRegisterBits 1 ∧
      (lchsTh1Resources N m dataStates).quantumSpace = N * dataStates := by
  simp [lchsTh1Resources, lchsFixedGateCount_eq, lchsClassicalBits, lchsQuantumSpace]

theorem lchsTh2Resources_spec (M Mt m dataStates : ℕ) :
    (lchsTh2Resources M Mt m dataStates).labels = lchs2dLabelCount M Mt ∧
      (lchsTh2Resources M Mt m dataStates).window = m ∧
      (lchsTh2Resources M Mt m dataStates).fixedGates = 9 * m + 4 ∧
      (lchsTh2Resources M Mt m dataStates).oracleQueries = m ∧
      (lchsTh2Resources M Mt m dataStates).classicalBits =
        lchsRegisterBits (lchs2dLabelCount M Mt) + lchsRegisterBits m +
          lchsRegisterBits (Mt + 1) ∧
      (lchsTh2Resources M Mt m dataStates).quantumSpace =
        lchs2dLabelCount M Mt * dataStates := by
  simp [lchsTh2Resources, lchsTheoremResources, lchsFixedGateCount_eq,
    lchsClassicalBits, lchsQuantumSpace]

theorem lchsTh3Resources_spec (M Mt m dataStates : ℕ) :
    (lchsTh3Resources M Mt m dataStates).labels = lchs2dLabelCount M Mt ∧
      (lchsTh3Resources M Mt m dataStates).window = m ∧
      (lchsTh3Resources M Mt m dataStates).fixedGates = 9 * m + 4 + 1 ∧
      (lchsTh3Resources M Mt m dataStates).oracleQueries = m ∧
      (lchsTh3Resources M Mt m dataStates).quantumSpace =
        lchs2dLabelCount M Mt * dataStates := by
  simp [lchsTh3Resources, lchsFixedGateCount_eq, lchsQuantumSpace, capFastForwardApplications]

end Clause4ResourceProofs

section Clause3CapAndSampling

variable {I : Type} [Fintype I] [DecidableEq I]

theorem capTwoFactor_eq_propagator (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) (hL : L.IsHermitian) (hH : Continuous H)
    (hHerm : ∀ u, (H u).IsHermitian) :
    HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t =
      orderedEvolution (fun u => Complex.I • (H u + k • L)) 0 t := by
  have h := interactionPictureLchsRepresentation (I := I) L H k t hL hH hHerm
  exact h.symm

theorem capPrinted_threeFactor_extra (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) (hL : L.IsHermitian) (hH : Continuous H)
    (hHerm : ∀ u, (H u).IsHermitian) :
    capPrintedThreeFactor L H k t =
      orderedEvolution (fun u => Complex.I • (H u + k • L)) 0 t *
        HamiltonianEvolution (k • L) (-t) := by
  have h := capTwoFactor_eq_propagator L H k t hL hH hHerm
  unfold capPrintedThreeFactor
  rw [h]

private theorem unitary_mul_left_cancel {U : Matrix I I ℂ} (hU : U ∈ unitaryGroup I ℂ)
    {M N : Matrix I I ℂ} (hMN : U * M = U * N) : M = N := by
  have hUU : Matrix.conjTranspose U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hstep : Matrix.conjTranspose U * (U * M) = Matrix.conjTranspose U * (U * N) := by
    rw [hMN]
  have h1 : (Matrix.conjTranspose U * U) * M = (Matrix.conjTranspose U * U) * N := by
    simpa only [Matrix.mul_assoc] using! hstep
  rw [hUU, Matrix.one_mul, Matrix.one_mul] at h1
  exact h1

theorem capPrinted_ne_twoFactor_of_extra_ne (L : Matrix I I ℂ)
    (H : ℝ → Matrix I I ℂ) (k t : ℝ) (hL : L.IsHermitian) (hH : Continuous H)
    (hHerm : ∀ u, (H u).IsHermitian)
    (hextra : HamiltonianEvolution (k • L) (-t) ≠ 1) :
    capPrintedThreeFactor L H k t ≠
      HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t := by
  intro hcon
  have hk : Continuous (fun _ : ℝ => (k : ℝ)) := continuous_const
  have hLc : Continuous (fun _ : ℝ => L) := continuous_const
  have hU : HamiltonianEvolution (k • L) t *
      orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t ∈
      unitaryGroup I ℂ := by
    rw [capTwoFactor_eq_propagator L H k t hL hH hHerm]
    exact ordered_evolution_hermitian_unitary I (fun u => H u + k • L)
      (by fun_prop)
      (fun u => (hHerm u).add (hL.smul (R := ℝ) (IsSelfAdjoint.all k))) 0 t
  have hform : (HamiltonianEvolution (k • L) t *
      orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t) *
        HamiltonianEvolution (k • L) (-t) =
      (HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t) * 1 := by
    unfold capPrintedThreeFactor at hcon
    rw [hcon, Matrix.mul_one]
  exact hextra (unitary_mul_left_cancel hU hform)

theorem capBranch_unitary (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ) (k t : ℝ)
    (hL : L.IsHermitian) (hH : Continuous H) (hHerm : ∀ u, (H u).IsHermitian) :
    capBranchUnitary L H k t ∈ unitaryGroup I ℂ := by
  have hk : Continuous (fun _ : ℝ => (k : ℝ)) := continuous_const
  have hLc : Continuous (fun _ : ℝ => L) := continuous_const
  unfold capBranchUnitary
  rw [capTwoFactor_eq_propagator L H k t hL hH hHerm]
  exact ordered_evolution_hermitian_unitary I (fun u => H u + k • L)
    (by fun_prop)
    (fun u => (hHerm u).add (hL.smul (R := ℝ) (IsSelfAdjoint.all k))) 0 t

theorem capBranch_is_fastForward_then_interaction (L : Matrix I I ℂ)
    (H : ℝ → Matrix I I ℂ) (k t : ℝ) :
    capBranchUnitary L H k t =
      HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t := rfl

theorem capFastForward_applications (k t : ℝ) :
    capFastForwardApplications = 1 := rfl

theorem capLoaded_raw_vector (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ)
    (P : Fin (Mt + 1) → Matrix I I ℂ) (i₀ : I)
    (hB : B ∈ unitaryGroup I ℂ)
    (hprep : ∀ l : Fin (Mt + 1), b (inhTrapNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ = ((‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
        b (inhTrapNode Mt s t l)) :
    (∑ x, lchs2dCoeff b s t K M Mt x • capLoadedUnitary L H s t K M Mt B P x) *ᵥ
        (B *ᵥ Ket i₀) =
      (∑ j : Fin (M + 1), kTrapCoeff K M j • capBranchUnitary L H (kTrapNode K M j) t) *ᵥ
          (B *ᵥ Ket i₀) +
        inh2dTrapSourceSum (fun _ => L) H b s t K M Mt := by
  have hundo : Bᴴ *ᵥ (B *ᵥ Ket i₀) = Ket i₀ := by
    have hBB : Bᴴ * B = 1 := Matrix.mem_unitaryGroup_iff'.mp hB
    rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  have hsplit :
      (∑ x : Fin (lchs2dLabelCount M Mt),
        lchs2dCoeff b s t K M Mt x • capLoadedUnitary L H s t K M Mt B P x) =
        (∑ j : Fin (M + 1),
          lchs2dCoeff b s t K M Mt (Fin.castAdd ((M + 1) * (Mt + 1)) j) •
            capLoadedUnitary L H s t K M Mt B P (Fin.castAdd ((M + 1) * (Mt + 1)) j)) +
          (∑ y : Fin ((M + 1) * (Mt + 1)),
            lchs2dCoeff b s t K M Mt (Fin.natAdd (M + 1) y) •
              capLoadedUnitary L H s t K M Mt B P (Fin.natAdd (M + 1) y)) := by
    simpa only [lchs2dLabelCount] using!
      (Fin.sum_univ_add (f := fun x : Fin ((M + 1) + (M + 1) * (Mt + 1)) =>
        lchs2dCoeff b s t K M Mt x • capLoadedUnitary L H s t K M Mt B P x))
  rw [hsplit, Matrix.add_mulVec]
  simp_rw [lchs2d_coeff_homogeneous]
  have hhom (j : Fin (M + 1)) :
      capLoadedUnitary L H s t K M Mt B P (Fin.castAdd ((M + 1) * (Mt + 1)) j) =
        capBranchUnitary L H (kTrapNode K M j) t := by
    simp [capLoadedUnitary, j.isLt]
  have hsrc (p : Fin (M + 1) × Fin (Mt + 1)) :
      capLoadedUnitary L H s t K M Mt B P (Fin.natAdd (M + 1) (finProdFinEquiv p)) =
        inh2dTrapSourceKUnitary (fun _ => L) H s t K M Mt p.1 p.2 * (P p.2 * Bᴴ) := by
    unfold capLoadedUnitary
    rw [dif_neg (by simp only [Fin.val_natAdd]; omega)]
    simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]
  simp_rw [hhom]
  congr 1
  rw [Matrix.sum_mulVec]
  have he := (finProdFinEquiv : Fin (M + 1) × Fin (Mt + 1) ≃ Fin ((M + 1) * (Mt + 1))).sum_comp
    (fun y => (lchs2dCoeff b s t K M Mt (Fin.natAdd (M + 1) y) •
      capLoadedUnitary L H s t K M Mt B P (Fin.natAdd (M + 1) y)) *ᵥ (B *ᵥ Ket i₀))
  rw [← he]
  simp_rw [lchs2d_coeff_source, hsrc, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hundo]
  have hnode (p : Fin (M + 1) × Fin (Mt + 1)) :
      (lchs2dSourceCoeff b s t K M Mt p) •
        (inh2dTrapSourceKUnitary (fun _ => L) H s t K M Mt p.1 p.2 *ᵥ (P p.2 *ᵥ Ket i₀)) =
      (inhTrapWeight Mt s t p.2 : ℂ) • (kTrapCoeff K M p.1 •
        (inh2dTrapSourceKUnitary (fun _ => L) H s t K M Mt p.1 p.2 *ᵥ
          b (inhTrapNode Mt s t p.2))) := by
    unfold lchs2dSourceCoeff
    by_cases hz : b (inhTrapNode Mt s t p.2) = 0
    · simp [hz, toEuclidean_fromVec]
    · rw [hprep p.2 hz, Matrix.mulVec_smul, smul_smul, smul_smul]
      have hn : ‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        intro h
        apply hz
        exact (WithLp.toLp_injective 2) (by simpa only [toEuclidean_fromVec,
          WithLp.toLp_zero] using! h)
      rw [Complex.ofReal_inv, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn), mul_one]
  simp_rw [hnode]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← Matrix.smul_mulVec, ← Matrix.sum_mulVec]
  rfl

theorem lchsHybridSample_queries (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (j₀ : Fin (lchs2dLabelCount M Mt)) (i₀ : I) (m : ℕ)
    (hst : s ≤ t) (hK : 0 < K) (hM : 0 < M)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    QueryCount (staticLchsCompile (lchs2dCoeff b s t K M Mt)
      (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀ (m - 1)) = m - 1 ∧
      lchsHybridSampleMaxQueries m = 2 * QueryCount
        (staticLchsCompile (lchs2dCoeff b s t K M Mt)
          (lchs2dUnitary L H s t K M Mt B P) B j₀ i₀ (m - 1)) := by
  have h := lchs2d_program_expanded L H b s t K M Mt B P j₀ i₀ (m - 1)
    hst hK hM hL hH hPSD hHerm hB hP
  (try dsimp only at h)
  obtain ⟨_, _, _, _, _, _, _, _, hq, _⟩ := h
  refine ⟨hq, ?_⟩
  simpa [lchsHybridSampleMaxQueries] using! hq.symm

theorem hamiltonianEvolution_of_zero (t : ℝ) :
    HamiltonianEvolution (0 : Matrix I I ℂ) t = 1 := by
  simp [HamiltonianEvolution, NormedSpace.exp_zero]

end Clause3CapAndSampling

section Clause2HamT

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

theorem lchsHamTQueryCount_eq (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) :
    lchsHamTQueryCount (I := I) h j₀ τ K = K :=
  (taylorLCUWord_counts (I := I) h j₀ τ K).1

theorem lchsHamTGateCount_eq (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) :
    lchsHamTGateCount (I := I) h j₀ τ K = 2 * K + 3 :=
  (taylorLCUWord_counts (I := I) h j₀ τ K).2

theorem lchsHamTNativeOrder_spec (m : ℕ) :
    2^m ≤ (lchsHamTNativeOrder m + 1).factorial ∧
      (∀ j < lchsHamTNativeOrder m, (j + 1).factorial < 2^m) ∧
      lchsHamTNativeOrder m ≤ 2 * m + 1 := by
  obtain ⟨hprec, _⟩ := factorial_taylor_native_cutoff_and_rate
  obtain ⟨h1, h2, h3, _⟩ := hprec m
  exact ⟨h1, h2, h3⟩

theorem lchsHamT_tight_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      lchsHamTNativeOrder m * Nat.log 2 m ≤ C * m := by
  obtain ⟨hprec, hrate⟩ := factorial_taylor_native_cutoff_and_rate
  obtain ⟨C, m₀, hC, hm₀, h⟩ := hrate
  exact ⟨C, m₀, hC, hm₀, fun m hm => by simpa [lchsHamTNativeOrder] using! h m hm⟩

theorem lchsHamT_native_query_rate (h : J → ℝ) (j₀ : J) (τ : ℝ) :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      lchsHamTQueryCount (I := I) h j₀ τ (lchsHamTNativeOrder m) * Nat.log 2 m ≤ C * m := by
  obtain ⟨C, m₀, hC, hm₀, h⟩ := lchsHamT_tight_rate
  exact ⟨C, m₀, hC, hm₀, fun m hm => by
    rw [lchsHamTQueryCount_eq]
    exact h m hm⟩

theorem taylorWordLabelCount_eq (K : ℕ) :
    taylorWordLabelCount J K = (Finset.univ : Finset (TaylorWordLabel J K)).card := by
  have hcard : (Finset.univ : Finset (TaylorWordLabel J K)).card =
      Fintype.card (TaylorWordLabel J K) := Finset.card_univ
  rw [hcard, Fintype.card_sum, Fintype.card_sigma]
  simp [taylorWordLabelCount, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

theorem taylorAncillaBits_spec (K : ℕ) :
    (Finset.univ : Finset (TaylorWordLabel J K)).card ≤ 2 ^ (taylorAncillaBits J K) := by
  have h := lchsRegisterBits_spec (taylorWordLabelCount J K)
  rw [← taylorAncillaBits, taylorWordLabelCount_eq (J := J) K] at h
  exact le_of_lt h

theorem taylorPhaseGate_diagonal (h : J → ℝ) (τ : ℝ) (K : ℕ) :
    taylorPhaseGate h τ K =
      Matrix.diagonal (fun x => coefficientPhase (taylorCoeff h τ K x)) := rfl

theorem taylorPhaseGateCount_eq (K : ℕ) :
    taylorPhaseGateCount J K = (Finset.univ : Finset (TaylorWordLabel J K)).card := by
  rw [taylorPhaseGateCount, taylorWordLabelCount_eq]

theorem hamTAcceptProb_ge_half (m : ℕ) (accept : FairBitSample m → Bool)
    (hcard : (((Finset.univ : Finset (FairBitSample m)).filter
      (fun x => accept x = true)).card : ℝ) ≥ (2 ^ m : ℝ) / 2) :
    1 / 2 ≤ hamTAcceptProb m accept := by
  have hpos : 0 < (2 ^ m : ℝ) := by positivity
  have hle : (((Finset.univ : Finset (FairBitSample m)).filter
      (fun x => accept x = true)).card : ℝ) ≤ (2 ^ m : ℝ) := by
    have h := Finset.card_le_univ
      ((Finset.univ : Finset (FairBitSample m)).filter (fun x => accept x = true))
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  unfold hamTAcceptProb
  rw [le_div_iff₀ hpos]
  linarith

theorem hamTFailFraction_le (m r a : ℕ) (ha : (a : ℝ) ≥ (2 ^ m : ℝ) / 2)
    (ha' : a ≤ 2 ^ m) :
    (hamTFailSeqCount m r a : ℝ) / (2 ^ m : ℝ) ^ r ≤ 1 / 2 ^ r := by
  have ha'' : (a : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast ha'
  have hsub : (2 ^ m : ℝ) - a ≤ (2 ^ m : ℝ) / 2 := by linarith
  have hcast : (hamTFailSeqCount m r a : ℝ) = ((2 ^ m : ℝ) - a) ^ r := by
    simp [hamTFailSeqCount, Nat.cast_sub, Nat.cast_pow, ha']
  rw [hcast]
  have hpos1 : 0 < (2 ^ m : ℝ) ^ r := by positivity
  rw [div_le_iff₀ hpos1]
  have hnonneg : 0 ≤ (2 ^ m : ℝ) - a := by linarith
  have hnonneg2 : 0 ≤ (2 ^ m : ℝ) / 2 := by positivity
  calc
    ((2 ^ m : ℝ) - a) ^ r ≤ ((2 ^ m : ℝ) / 2) ^ r := by gcongr
    _ = (2 ^ m : ℝ) ^ r / (2 : ℝ) ^ r := div_pow ..
    _ = (1 / 2 ^ r) * (2 ^ m : ℝ) ^ r := by field_simp

theorem hamTExpectedRepetitions_le_two :
    tsum (fun r : ℕ => (1 / 2 : ℝ) ^ r) ≤ 2 := by
  have h := (hasSum_geometric_of_norm_lt_one (K := ℝ) (ξ := (1 / 2 : ℝ))
    (by norm_num)).tsum_eq
  rw [h]
  norm_num

theorem lchsWindowLabelAccesses_spec (N m : ℕ) :
    lchsWindowLabelAccesses N m = (2 * m + 1) * N ∧
      N ≤ lchsWindowLabelAccesses N m := by
  constructor
  · rfl
  · rw [lchsWindowLabelAccesses]
    calc N = N * 1 := by omega
      _ ≤ N * (2 * m + 1) := Nat.mul_le_mul_left N (by omega)
      _ = (2 * m + 1) * N := Nat.mul_comm _ _

theorem lchsWindowLabelAccesses_eq_word (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (j₀ : Fin (lchs2dLabelCount M Mt)) (i₀ : I) (m : ℕ)
    (hst : s ≤ t) (hK : 0 < K) (hM : 0 < M)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    lchsWindowLabelAccesses (lchs2dLabelCount M Mt) m =
      lchs2dLabelCount M Mt *
        ((staticLchsWord m).count .selectF + (staticLchsWord m).count .selectB) := by
  have h := lchs2d_program_expanded L H b s t K M Mt B P j₀ i₀ m
    hst hK hM hL hH hPSD hHerm hB hP
  (try dsimp only at h)
  obtain ⟨-, -, hsf, hsb, -, -, -, -, -, hlen⟩ := h
  rw [lchsWindowLabelAccesses, hsf, hsb]
  ring

end Clause2HamT

end Qatlib.Concepts.RandCompile.ChannelBudget
