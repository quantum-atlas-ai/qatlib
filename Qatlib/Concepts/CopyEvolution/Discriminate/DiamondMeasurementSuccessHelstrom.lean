/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondSdp
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SchattenDiamond.DiamondSdp

namespace Qatlib.Concepts.CopyEvolution.Discriminate

open Matrix Qatlib
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 2000000

private lemma density_traceNorm_one {d : ℕ} {X : Operator d} (hX : IsDensityOperator X) :
    Matrix.traceNorm X = 1 := by
  have h := hX.1.traceNorm_eq_trace
  rw [hX.2] at h
  exact Complex.ofReal_injective (by simpa using! h)

private def finProd1Equiv (D : ℕ) : (Fin D × Fin 1) ≃ Fin D :=
  ⟨Prod.fst, fun a => (a, 0),
    fun a => by ext <;> simp [Subsingleton.elim a.2 0], fun _ => rfl⟩

private lemma traceNorm_sub_output_le_diamond {D E : ℕ} (T S : Operator D →ₗ[ℂ] Operator E)
    (X : Operator D) (hX : IsDensityOperator X) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (T - S) ≤ ENNReal.ofReal δ) :
    Matrix.traceNorm (T X - S X) ≤ δ := by
  have hXn : Matrix.traceNorm X = 1 := density_traceNorm_one hX
  have hre : tensorLeft (T - S)
        (Matrix.reindex (finProd1Equiv D).symm (finProd1Equiv D).symm X)
      = Matrix.reindex (finProd1Equiv E).symm (finProd1Equiv E).symm (T X - S X) := by
    ext a b
    rfl
  have hle := Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_apply (T - S) 1
    (Matrix.reindex (finProd1Equiv D).symm (finProd1Equiv D).symm X)
  rw [hre, Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_traceNorm_reindex,
    Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_traceNorm_reindex, hXn, ENNReal.ofReal_one, mul_one] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hδ0).mp (hle.trans hδ)

private lemma exists_gamma_le_one {d : ℕ} (x : Fin d → ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ ∀ j, x j ≠ 0 → γ ≤ |x j| := by
  classical
  by_cases hne : (Finset.univ.filter (fun j => x j ≠ 0)).Nonempty
  · let S' : Finset ℝ := (Finset.univ.filter (fun j => x j ≠ 0)).image (fun j => |x j|)
    have hS' : S'.Nonempty := hne.image _
    refine ⟨min 1 (S'.min' hS'), ?_, min_le_left _ _, fun j hj => ?_⟩
    · have hpos : 0 < S'.min' hS' := by
        by_contra hle
        obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp (S'.min'_mem hS')
        rw [← hbe] at hle
        exact absurd (abs_pos.mpr (Finset.mem_filter.mp hb).2) hle
      exact lt_min_iff.mpr ⟨by norm_num, hpos⟩
    · exact min_le_iff.mpr (Or.inr (S'.min'_le _
        (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩)))
  · refine ⟨1, by norm_num, le_rfl, fun j hj => ?_⟩
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) (fun hmem => hne ⟨j, hmem⟩)

theorem frontier1 {D E : ℕ} (T S : Operator D →ₗ[ℂ] Operator E)
    (hTcp : CompletelyPositive T) (hScp : CompletelyPositive S)
    (hTtp : TracePreserving T) (hStp : TracePreserving S)
    (X : Operator D) (hX : IsDensityOperator X)
    (M : Operator E) (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef) :
    Matrix.trace (T X - S X) = 0 ∧
    measurementSuccess M (T X) (S X)
      = 1/2 + ((M - (1/2 : ℂ) • 1) * (T X - S X)).trace.re / 2 ∧
    measurementSuccess M (T X) (S X)
      ≤ 1/2 + Matrix.traceNorm (T X - S X) / 4 ∧
    (∃ Aplus : Operator E, Aplus.PosSemidef ∧ (1 - Aplus).PosSemidef ∧
      measurementSuccess Aplus (T X) (S X) = 1/2 + Matrix.traceNorm (T X - S X)/4 ∧
      (∀ A : Operator E, A.PosSemidef → (1 - A).PosSemidef →
        measurementSuccess A (T X) (S X) ≤ 1/2 + Matrix.traceNorm (T X - S X)/4)) ∧
    ∀ δ : ℝ, 0 ≤ δ → Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (T - S) ≤ ENNReal.ofReal δ →
      measurementSuccess M (T X) (S X) ≤ 1/2 + δ / 4 := by
  have hρ : IsDensityOperator (T X) := ⟨hTcp.positive hX.1, (hTtp X).trans hX.2⟩
  have hσ : IsDensityOperator (S X) := ⟨hScp.positive hX.1, (hStp X).trans hX.2⟩
  have hzero : Matrix.trace (T X - S X) = 0 := by
    rw [Matrix.trace_sub, hρ.2, hσ.2, sub_self]
  have hcenter : measurementSuccess M (T X) (S X)
      = 1/2 + ((M - (1/2 : ℂ) • 1) * (T X - S X)).trace.re / 2 := by
    exact measurementSuccess_eq_half_add_centered hσ.2 hzero
  have hquarter : measurementSuccess M (T X) (S X)
      ≤ 1/2 + Matrix.traceNorm (T X - S X) / 4 := by
    exact measurementSuccess_le_half_add_quarter hM hMc hσ.2 hzero
  have hΔher : (T X - S X).IsHermitian := by
    show (T X - S X)ᴴ = T X - S X
    rw [Matrix.conjTranspose_sub, hρ.1.1, hσ.1.1]
  obtain ⟨V, hVmem, hspec⟩ : ∃ V : Operator E, V ∈ Matrix.unitaryGroup (Fin E) ℂ ∧
      T X - S X = V * Matrix.diagonal (fun j => (hΔher.eigenvalues j : ℂ)) * Vᴴ :=
    ⟨hΔher.eigenvectorUnitary, hΔher.eigenvectorUnitary.2, by
      simpa [Function.comp_def, Matrix.star_eq_conjTranspose] using! hΔher.spectral_theorem⟩
  obtain ⟨γ, hγ0, hγ1, hγgap⟩ := exists_gamma_le_one hΔher.eigenvalues
  have hH := Qatlib.Concepts.CopyEvolution.Discriminate.finiteCopyHelstromDiscrimination
    E 2 1 γ (T X) (S X) V hΔher.eigenvalues (by norm_num) (by norm_num)
    hγ0 hγ1 hρ hσ hVmem hspec hγgap
  refine ⟨hzero, hcenter, hquarter, ⟨V * Matrix.diagonal
      (fun j => if 0 < hΔher.eigenvalues j then (1 : ℂ) else 0) * Vᴴ,
    hH.1, hH.2.1, ?_, ?_⟩, ?_⟩
  · exact hH.2.2.1
  · exact fun A hA hAc => hH.2.2.2.1 A hA hAc
  intro δ hδ0 hδ
  have hn := traceNorm_sub_output_le_diamond T S X hX hδ0 hδ
  linarith

theorem helstromInstrument_optimal {D E : ℕ} (T S : QuantumChannel D E)
    (X : Operator D) (hX : IsDensityOperator X) :
    ∃ M : Operator E, ∃ hM : M.PosSemidef, ∃ hMc : (1 - M).PosSemidef,
      Qatlib.Concepts.ProbabilityCore.Concentration.eventMass
        (discriminationLaw (Instrument.ofPOVM (binaryEffectPOVM M hM hMc))
          (T.map X) (S.map X) (T.preservesDensity hX) (S.preservesDensity hX))
        (fun z => z.1 = z.2) = 1 / 2 + Matrix.traceNorm (T.map X - S.map X) / 4 ∧
      ∀ (A : Operator E) (hA : A.PosSemidef) (hAc : (1 - A).PosSemidef),
        Qatlib.Concepts.ProbabilityCore.Concentration.eventMass
          (discriminationLaw (Instrument.ofPOVM (binaryEffectPOVM A hA hAc))
            (T.map X) (S.map X) (T.preservesDensity hX) (S.preservesDensity hX))
          (fun z => z.1 = z.2) ≤ 1 / 2 + Matrix.traceNorm (T.map X - S.map X) / 4 := by
  obtain ⟨M, hM, hMc, heq, hle⟩ :=
    (frontier1 T.map S.map T.completelyPositive S.completelyPositive
      T.tracePreserving S.tracePreserving X hX 1 Matrix.PosSemidef.one
      (by rw [sub_self]; exact Matrix.PosSemidef.zero)).2.2.2.1
  refine ⟨M, hM, hMc, ?_, ?_⟩
  · rw [discriminationLaw_success]
    exact heq
  · intro A hA hAc
    rw [discriminationLaw_success]
    exact hle A hA hAc

end Qatlib.Concepts.CopyEvolution.Discriminate
