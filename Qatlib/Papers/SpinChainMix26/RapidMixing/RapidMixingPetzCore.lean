/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzDefs
import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
set_option warningAsError false


open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzDefs
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzDefs.LocalTermDesc
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 2000000
namespace Qatlib.Papers.SpinChainMix26.RapidMixing
open Matrix
open scoped Classical BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ENNReal
noncomputable def twoSiteGibbs : Operator (2^2) := (1/4 : ℝ) • 1

lemma twoSite_gibbs_zero (H : Operator (2^2)) : chainGibbs (n:=2) (d:=2) H 0 = twoSiteGibbs := by
  norm_num [chainGibbs, chainGibbsPartition, chainGibbsKernel, twoSiteGibbs, Matrix.trace_one]

lemma twoSite_sqrt_gibbs : CFC.sqrt twoSiteGibbs = (1/2 : ℝ) • (1 : Operator 4) := by
  apply CFC.sqrt_unique
  · norm_num [twoSiteGibbs, smul_mul_smul, smul_smul]
  · exact smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) zero_le_one

lemma twoSite_block_reduced (s : Fin 2) :
    blockReduced (n:=2) (d:=2) twoSiteGibbs s.val 1 (by decide) (by decide) = (1/2 : ℝ) • 1 := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [blockReduced, twoSiteGibbs, Fin.sum_univ_two, mergeLabel, chainOfDigits,
      chainLabel, finPiFinEquiv, Matrix.one_apply]

lemma twoSite_sqrt_half : CFC.sqrt ((1/2 : ℝ) • (1 : Operator 2)) =
    (Real.sqrt 2 / 2) • (1 : Operator 2) := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul, one_mul]
    congr 1
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · exact smul_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 2) zero_le_one

lemma twoSite_inverse_sqrt_half :
    (CFC.sqrt ((1/2 : ℝ) • (1 : Operator 2)))⁻¹ = Real.sqrt 2 • (1 : Operator 2) := by
  rw [twoSite_sqrt_half]
  apply Matrix.inv_eq_left_inv
  simp only [smul_mul_smul, one_mul]
  have hr : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hr, one_smul]

lemma twoSite_split_label_injective (s : Fin 2) (u v : Fin 4) :
    blockLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) u =
      blockLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) v →
    compLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) u =
      compLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) v → u = v := by
  revert u v
  fin_cases s <;> decide

lemma twoSite_kraus_diagonal (s : Fin 2) (k : Fin 2) :
    petzKraus (n:=2) (d:=2) twoSiteGibbs s.val 1 (by decide) (by decide) k =
      Matrix.diagonal (fun u : Fin 4 =>
        if compLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) u = k
        then ((Real.sqrt 2 / 2 : ℝ) : ℂ) else 0) := by
  unfold petzKraus
  rw [twoSite_sqrt_gibbs, twoSite_block_reduced, twoSite_inverse_sqrt_half, smul_mul, one_mul]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hc : compLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) i = k
    · simp [blockCompEmbed, hc, Matrix.smul_apply, Complex.real_smul]
      ring
    · simp [blockCompEmbed, hc]
  · by_cases hc : compLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) i = k ∧
        compLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) j = k
    · have hb : blockLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) i ≠
          blockLabel (n:=2) (d:=2) s.val 1 (by decide) (by decide) j := by
        intro h
        exact hij (twoSite_split_label_injective s i j h (hc.1.trans hc.2.symm))
      simp [blockCompEmbed, hc, hb, hij]
    · simp [blockCompEmbed, hc, hij]

lemma ideal_channel_of_eigen {n d : ℕ} (L : Operator (d^n) →ₗ[ℂ] Operator (d^n))
    (X : Operator (d^n)) (z : ℂ) (hX : L X = z • X) (t : ℝ) :
    idealChannel L t X = Complex.exp ((t:ℂ)*z) • X := by
  let b := Matrix.stdBasis ℂ (Fin (d^n)) (Fin (d^n))
  apply b.repr.injective
  apply DFunLike.coe_injective
  change (b.repr ((Matrix.toLin b b) (NormedSpace.exp ((t:ℂ) • liouvilleMatrix L)) X) : _ → ℂ) = _
  rw [Matrix.repr_toLin]
  have he : ((t:ℂ) • liouvilleMatrix L) *ᵥ (b.repr X : _ → ℂ) =
      ((t:ℂ)*z) • (b.repr X : _ → ℂ) := by
    rw [Matrix.smul_mulVec]
    change (t:ℂ) • (LinearMap.toMatrix b b L *ᵥ (b.repr X : _ → ℂ)) = _
    rw [LinearMap.toMatrix_mulVec_repr, hX, map_smul]
    simp [smul_smul]
  rw [matrix_exp_mulVec_of_eigen _ _ _ he]
  simp

lemma twoSite_block_diagonal_action (s : Fin 2) (v : Fin 4 → ℂ) :
    petzBlockChannel (n:=2) (d:=2) twoSiteGibbs s.val 1 (by decide) (by decide) (Matrix.diagonal v) =
      (1/2 : ℂ) • Matrix.diagonal v := by
  unfold petzBlockChannel
  simp only [LinearMap.sum_apply, twoSite_kraus_diagonal, conjBranch_apply,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    have hr : (((Real.sqrt 2 / 2 : ℝ) : ℂ) * v i) *
        star (((Real.sqrt 2 / 2 : ℝ) : ℂ)) = (1/2 : ℂ) * v i := by
      simp only [RCLike.star_def, Complex.conj_ofReal]
      have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      push_cast
      linear_combination (v i / 4) * hs
    simpa [apply_ite, mul_ite, ite_mul] using hr
  · simp [Matrix.sum_apply, hij]

lemma twoSite_generator_diagonal (v : Fin 4 → ℂ) :
    petzGenerator (n:=2) (d:=2) twoSiteGibbs 1 (by decide) (by decide) (Matrix.diagonal v) =
      (-1 : ℂ) • Matrix.diagonal v := by
  simp only [petzGenerator, Nat.cast_one, inv_one, one_smul, LinearMap.sub_apply,
    Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [twoSite_block_diagonal_action (0 : Fin 2), twoSite_block_diagonal_action (1 : Fin 2)]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  norm_num
  ring

lemma twoSite_ideal_diagonal (v : Fin 4 → ℂ) (t : ℝ) :
    idealChannel (petzGenerator (n:=2) (d:=2) twoSiteGibbs 1 (by decide) (by decide)) t (Matrix.diagonal v) =
      Complex.exp (-(t:ℂ)) • Matrix.diagonal v := by
  simpa using ideal_channel_of_eigen _ _ (-1) (twoSite_generator_diagonal v) t
noncomputable def twoSiteBasisState : Operator 4 :=
    Matrix.diagonal (fun i : Fin 4 => if i=0 then 1 else 0)

lemma twoSite_basis_density : IsDensityOperator twoSiteBasisState := by
  constructor
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> positivity
  · simp [twoSiteBasisState, Matrix.trace_diagonal]

lemma twoSite_basis_traceNorm : Matrix.traceNorm twoSiteBasisState = 1 := by
  have h := twoSite_basis_density.1.traceNorm_eq_trace
  have h1 := congrArg Complex.re (h.trans twoSite_basis_density.2)
  simpa using h1

lemma twoSite_ideal_basis (t : ℝ) :
    idealChannel (petzGenerator (n:=2) (d:=2) twoSiteGibbs 1 (by decide) (by decide)) t twoSiteBasisState =
      Complex.exp (-(t:ℂ)) • twoSiteBasisState := twoSite_ideal_diagonal _ t

lemma twoSite_mixing_gap (t : ℝ) : (1/8 : ℝ) ≤
    halfTraceDist (idealChannel (petzGenerator (n:=2) (d:=2) twoSiteGibbs 1 (by decide) (by decide)) t twoSiteBasisState) twoSiteGibbs := by
  rw [twoSite_ideal_basis]
  let P : Operator 4 := Matrix.diagonal (fun i : Fin 4 => if i=1 then 1 else 0)
  have hnorm : ‖P‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    split_ifs <;> norm_num
  have htrace : Matrix.trace (P * (Complex.exp (-(t:ℂ)) • twoSiteBasisState - twoSiteGibbs)) = (-1/4 : ℂ) := by
    norm_num [P, twoSiteBasisState, twoSiteGibbs, Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
  have he := (Matrix.abs_trace_le_traceNorm (P * (Complex.exp (-(t:ℂ)) • twoSiteBasisState - twoSiteGibbs))).trans
    (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _)
  rw [htrace] at he
  have hle : ‖P‖ * Matrix.traceNorm (Complex.exp (-(t:ℂ)) • twoSiteBasisState - twoSiteGibbs) ≤
      Matrix.traceNorm (Complex.exp (-(t:ℂ)) • twoSiteBasisState - twoSiteGibbs) := by
    exact (mul_le_mul_of_nonneg_right hnorm (Matrix.traceNorm_nonneg _)).trans_eq (one_mul _)
  norm_num at he
  unfold halfTraceDist
  linarith

lemma trace_bound_of_diamond_sixteenth {D E : ℕ} (T S : Operator D →ₗ[ℂ] Operator E)
    (h : finiteDiamondDistance T S ≤ ENNReal.ofReal (1/16 : ℝ)) (X : Operator D) :
    Matrix.traceNorm (T X - S X) ≤ (1/8 : ℝ) * Matrix.traceNorm X := by
  have hN : finiteDiamondNorm (T-S) ≤ ENNReal.ofReal (1/8 : ℝ) := by
    calc
      _ = 2 * finiteDiamondDistance T S := by
        unfold finiteDiamondDistance
        rw [← mul_assoc]
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * ENNReal.ofReal (1/16 : ℝ) := mul_le_mul le_rfl h bot_le bot_le
      _ = _ := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        norm_num
  let e : Fin D ≃ Fin D × Fin 1 := (Equiv.prodUnique _ _).symm
  have hb := (finiteDiamondNorm_le_iff_uniform D E (T-S) (1/8) (by norm_num)).mp hN
    1 (Matrix.reindex e e X)
  let f : Fin E ≃ Fin E × Fin 1 := (Equiv.prodUnique _ _).symm
  have ht : tensorLeft (T-S) (Matrix.reindex e e X) =
      Matrix.reindex f f (T X - S X) := by rfl
  rw [ht, diamond_traceNorm_reindex, diamond_traceNorm_reindex] at hb
  exact hb

lemma twoSite_simulation_gap (T : Operator 4 →ₗ[ℂ] Operator 4) (hT : TracePreserving T) :
    ¬ finiteDiamondDistance T
      (idealChannel (petzGenerator (n:=2) (d:=2) twoSiteGibbs 1 (by decide) (by decide)) (Real.log 2)) ≤
        ENNReal.ofReal (1/16 : ℝ) := by
  intro h
  have he := trace_bound_of_diamond_sixteenth _ _ h twoSiteBasisState
  rw [twoSite_ideal_basis, twoSite_basis_traceNorm] at he
  have hexp : Complex.exp (-(Real.log 2 : ℂ)) = (1/2 : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [hexp] at he
  have ht : Matrix.trace (T twoSiteBasisState - (1/2 : ℂ) • twoSiteBasisState) = (1/2 : ℂ) := by
    rw [Matrix.trace_sub, Matrix.trace_smul, hT, twoSite_basis_density.2]
    norm_num
  have hl := Matrix.abs_trace_le_traceNorm (T twoSiteBasisState - (1/2 : ℂ) • twoSiteBasisState)
  rw [ht] at hl
  norm_num at hl he
  linarith

def zeroTermDescription : LocalTermDesc 4 := ⟨0, fun _ _ _ => 0, fun _ => 0⟩

lemma zeroTermDescription_admits : zeroTermDescription.Admits 0 := by
  intro p i j
  refine ⟨⟨0, by simp [zeroTermDescription]⟩, ?_⟩
  simp [zeroTermDescription]

lemma zeroTermDescription_poly : zeroTermDescription.PolyEvaluable := by
  exact ⟨1, 1, by intro p; simp [zeroTermDescription]⟩

lemma twoSite_bounded_zero : BoundedChain (n:=2) (d:=2) (fun _ => 0) := by
  intro i
  simp [OperatorSpectralNorm]

theorem not_clause4 : ¬ (
∀ (β : ℝ) (d ℓ : ℕ), 0 ≤ β → 2 ≤ d → 0 < ℓ →
    ∃ (c e : ℕ),
      ∀ (n : ℕ) (hn : ℓ < n),

        ∃ (build : (Fin n → LocalTermDesc (d * d)) → ℝ → ℝ → PetzSimArtifact n d),
          ∀ (t : ℝ) (_ht : 0 ≤ t) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1)
            (h : Fin n → Operator (d * d)) (desc : Fin n → LocalTermDesc (d * d)),
            BoundedChain h →
            (∀ i, (desc i).Admits (h i)) →
            (∀ i, (desc i).PolyEvaluable) →
            let A := build desc t ε
            let twoSiteGibbs := chainGibbs (chainHamiltonian (by omega) h) β
            let L := petzGenerator twoSiteGibbs ℓ (by omega) (by omega)

            IsDensityOperator twoSiteGibbs ∧

            A.Legal ∧
            CompletelyPositive (averageChannel A) ∧
            TracePreserving (averageChannel A) ∧

            finiteDiamondDistance (averageChannel A) (idealChannel L t)
              ≤ ENNReal.ofReal ε ∧

            (A.sampler = PetzSamplingLaw.poisson ∨ A.sampler = PetzSamplingLaw.uniform) ∧
            0 ≤ A.windowErr ∧ 0 ≤ A.samplingErr ∧ 0 ≤ A.petzLocalErr ∧
              A.windowErr + A.samplingErr + A.petzLocalErr ≤ ε ∧

            A.gates ≤ c * petzGateCore n t ε * petzLogSlack n t ε ^ e ∧
            A.depth ≤ c * petzDepthCore n t ε * petzLogSlack n t ε ^ e ∧

            A.ancillas ≤ c * n * petzLogSlack n t ε ^ e ∧

            A.classicalTime ≤ c * petzClassicalScale n (descLength desc) t ε ^ e
) := by
  intro h
  obtain ⟨_c, _e, hc⟩ := h 0 2 1 (by norm_num) (by decide) (by decide)
  obtain ⟨build, hb⟩ := hc 2 (by decide)
  have hp := hb (Real.log 2) (Real.log_nonneg (by norm_num)) (1/16) (by norm_num) (by norm_num)
    (fun _ => 0) (fun _ => zeroTermDescription) twoSite_bounded_zero (fun _ => zeroTermDescription_admits)
    (fun _ => zeroTermDescription_poly)
  dsimp only at hp
  rw [twoSite_gibbs_zero] at hp
  rcases hp with ⟨_, _, _, htp, hd, _⟩
  exact twoSite_simulation_gap _ htp hd

theorem not_clause5 : ¬ (
∀ (β : ℝ) (d ℓ : ℕ), 0 ≤ β → 2 ≤ d → 0 < ℓ →
    ∃ (c e : ℕ),
      ∀ (n : ℕ) (hn : ℓ < n),

        ∃ (build : (Fin n → LocalTermDesc (d * d)) → ℝ → PetzSimArtifact n d),
          ∀ (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1)
            (h : Fin n → Operator (d * d)) (desc : Fin n → LocalTermDesc (d * d)),
            BoundedChain h →
            (∀ i, (desc i).Admits (h i)) →
            (∀ i, (desc i).PolyEvaluable) →
            let A := build desc ε
            let twoSiteGibbs := chainGibbs (chainHamiltonian (by omega) h) β
            let L := petzGenerator twoSiteGibbs ℓ (by omega) (by omega)
            IsDensityOperator twoSiteGibbs ∧

            A.Legal ∧
            CompletelyPositive (averageChannel A) ∧
            TracePreserving (averageChannel A) ∧

            (∀ ρ0 : Operator (d ^ n), IsDensityOperator ρ0 →
              halfTraceDist (idealChannel L A.runTime ρ0) twoSiteGibbs ≤ A.mixingErr) ∧

            (finiteDiamondDistance (averageChannel A) (idealChannel L A.runTime)
              ≤ ENNReal.ofReal A.diamondErr) ∧

            0 ≤ A.mixingErr ∧ 0 ≤ A.diamondErr ∧ 0 ≤ A.prepErr ∧
              A.mixingErr + A.diamondErr + A.prepErr ≤ ε ∧

            (∀ ρ0 : Operator (d ^ n), IsDensityOperator ρ0 →
              halfTraceDist (averageChannel A ρ0) twoSiteGibbs
                ≤ A.mixingErr + A.diamondErr + A.prepErr) ∧

            A.gates ≤ c * n * petzPrepLog n ε ^ e ∧
            A.depth ≤ c * petzPrepLog n ε ^ e ∧
            A.ancillas ≤ c * n * petzPrepLog n ε ^ e
) := by
  intro h
  obtain ⟨_c, _e, hc⟩ := h 0 2 1 (by norm_num) (by decide) (by decide)
  obtain ⟨build, hb⟩ := hc 2 (by decide)
  have hp := hb (1/16) (by norm_num) (by norm_num)
    (fun _ => 0) (fun _ => zeroTermDescription) twoSite_bounded_zero (fun _ => zeroTermDescription_admits)
    (fun _ => zeroTermDescription_poly)
  dsimp only at hp
  rw [twoSite_gibbs_zero] at hp
  rcases hp with ⟨_, _, _, _, hmix, _, _, hd0, hp0, hbudget, _⟩
  have hm := hmix twoSiteBasisState twoSite_basis_density
  have hg := twoSite_mixing_gap (build (fun _ => zeroTermDescription) (1/16)).runTime
  linarith

end Qatlib.Papers.SpinChainMix26.RapidMixing
