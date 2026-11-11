/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources.ReferencePGMCollision
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

/-! A joint input-error consumer of the actual public-phase PGM.
The supplied density may depend on the public matrix. No independent-copy
or fresh-noise promise is inferred. Rejection is counted as failure, and no
postselection denominator or efficient measurement implementation is added. -/

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

open Matrix
open scoped BigOperators ComplexOrder Classical
open Qatlib.Concepts.ReferenceError.RefTraceError

/-- The trace norm of a positive semidefinite matrix is the real part of its
trace. -/
private theorem posSemidef_traceNorm_eq_re {I : Type} [Fintype I] {M : Matrix I I ℂ}
    (hM : M.PosSemidef) : Matrix.traceNorm M = (Matrix.trace M).re := by
  have hc : ((Matrix.traceNorm M : ℂ)) = Matrix.trace M := hM.traceNorm_eq_trace
  simpa using congrArg Complex.re hc

/-- The positive spectral part of a Hermitian matrix is positive semidefinite. -/
private theorem positive_split_pos {I : Type} [Fintype I] [DecidableEq I]
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (le_max_right (hX.eigenvalues i) 0)

/-- The negative spectral part of a Hermitian matrix is positive semidefinite. -/
private theorem positive_split_neg {I : Type} [Fintype I] [DecidableEq I]
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (le_max_right (-hX.eigenvalues i) 0)

/-- A positive trace-nonincreasing map spends a trace-zero perturbation budget
on the selected operator and its mass change jointly. -/
private theorem positive_tni_trace_zero_budget
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hpos : ∀ A, A.PosSemidef → (T A).PosSemidef)
    (htni : ∀ A, A.PosSemidef → (Matrix.trace (T A)).re ≤ (Matrix.trace A).re)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (hzero : (Matrix.trace X).re = 0) :
    Matrix.traceNorm (T X) + |(Matrix.trace (T X)).re| ≤ Matrix.traceNorm X := by
  let P := Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX
  let N := Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX
  have hp : P.PosSemidef := positive_split_pos hX
  have hn : N.PosSemidef := positive_split_neg hX
  have heq : P - N = X := Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.sub_posPart_negPart hX
  have hnorm : Matrix.traceNorm X = (Matrix.trace P).re + (Matrix.trace N).re := by
    rw [Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.traceNorm_sub_posPart_negPart hX]
    change Matrix.traceNorm P + Matrix.traceNorm N = _
    rw [posSemidef_traceNorm_eq_re hp, posSemidef_traceNorm_eq_re hn]
  have hequal : (Matrix.trace P).re = (Matrix.trace N).re := by
    have hh := congrArg (fun A : Matrix I I ℂ => (Matrix.trace A).re) heq
    change (Matrix.trace (P - N)).re = (Matrix.trace X).re at hh
    rw [Matrix.trace_sub, Complex.sub_re, hzero] at hh
    linarith
  have hpout := hpos P hp
  have hnout := hpos N hn
  have hdiff : T X = T P - T N := by rw [← heq, map_sub]
  have htri : Matrix.traceNorm (T X) ≤
      (Matrix.trace (T P)).re + (Matrix.trace (T N)).re := by
    rw [hdiff]
    simpa only [← sub_eq_add_neg, Matrix.traceNorm_neg,
      posSemidef_traceNorm_eq_re hpout, posSemidef_traceNorm_eq_re hnout] using
      Matrix.traceNorm_add_le (T P) (-(T N))
  have hmass : (Matrix.trace (T X)).re =
      (Matrix.trace (T P)).re - (Matrix.trace (T N)).re := by
    rw [hdiff, Matrix.trace_sub, Complex.sub_re]
  have htp := htni P hp
  have htn := htni N hn
  rw [hmass, hnorm]
  rcases le_total (Matrix.trace (T N)).re (Matrix.trace (T P)).re with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith


/-- The actual finite-label construction satisfies `reference_pgm_input_mass_error` with all displayed hypotheses. -/
private theorem reference_pgm_input_mass_error
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [Fintype J] [DecidableEq J] {D : ℕ}
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ : AddChar (J → K) ℂ) (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    |instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
        ρ (some χ) -
      instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
        (outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ)) (some χ)| ≤
      Matrix.traceNorm (ρ-outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ))/2 := by
  let τ := outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ)
  let Jpgm := Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p))
  let T := Jpgm.branch (some χ)
  have hτ : IsDensityOperator τ := (pqc_reference_pgm_born_contract M enc p χ).1
  have hzero : (Matrix.trace (ρ-τ)).re = 0 := by
    rw [Matrix.trace_sub, hρ.2, hτ.2]
    simp
  have hbudget := positive_tni_trace_zero_budget T
    (fun A hA => (Jpgm.cp (some χ)).positive hA)
    (fun A hA => Jpgm.tni (some χ) hA)
    (ρ-τ) (hρ.1.isHermitian.sub hτ.1.isHermitian) hzero
  have hmass : |(Matrix.trace (T (ρ-τ))).re| ≤ Matrix.traceNorm (T (ρ-τ)) :=
    (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  have htrace : (Matrix.trace (T (ρ-τ))).re =
      instrumentProb Jpgm ρ (some χ)-instrumentProb Jpgm τ (some χ) := by
    simp only [map_sub, Matrix.trace_sub, Complex.sub_re, instrumentProb, T]
  rw [htrace] at hbudget hmass
  change |instrumentProb Jpgm ρ (some χ)-instrumentProb Jpgm τ (some χ)| ≤ _
  change Matrix.traceNorm (T (ρ-τ)) +
      |instrumentProb Jpgm ρ (some χ)-instrumentProb Jpgm τ (some χ)| ≤
      Matrix.traceNorm (ρ-τ) at hbudget
  linarith

/-- The same actual PGM consumes an arbitrary matrix-dependent density family.
The perturbation term is the real trace distance of that supplied input;
the theorem does not assume the desired noisy success or independent errors. -/
theorem pqc_reference_pgm_perturbed_average_failure
    (K I J : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (D : ℕ) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (hinj : Function.Injective enc) (χ : AddChar (J → K) ℂ)
    (ρ : Matrix I J K → Operator D) (hρ : ∀ M, IsDensityOperator (ρ M)) :
    finiteHashAverage (fun M : Matrix I J K =>
      1-instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
        (ρ M) (some χ)) ≤
      ((Fintype.card (J → K) : ℝ)-1) * ∑ x : Fin D, p.prob x ^ 2 +
        finiteHashAverage (fun M : Matrix I J K =>
          Matrix.traceNorm (ρ M-outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ))/2) := by
  have hpoint (M : Matrix I J K) :
      1-instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p))) (ρ M) (some χ) ≤
      (1-instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
        (outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ)) (some χ)) +
          Matrix.traceNorm (ρ M-outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ))/2 := by
    have h := reference_pgm_input_mass_error M enc p χ (ρ M) (hρ M)
    have hneg := neg_le_abs (instrumentProb
      (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p))) (ρ M) (some χ) -
      instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
        (outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ)) (some χ))
    linarith
  calc
    _ ≤ finiteHashAverage (fun M : Matrix I J K =>
        (1-instrumentProb
          (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
          (outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ)) (some χ)) +
          Matrix.traceNorm (ρ M-outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ))/2) := by
      unfold finiteHashAverage
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum (fun M _ => hpoint M)
    _ = finiteHashAverage (fun M : Matrix I J K =>
        1-instrumentProb
          (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
          (outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ)) (some χ)) +
        finiteHashAverage (fun M : Matrix I J K =>
          Matrix.traceNorm (ρ M-outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ))/2) := by
      simp only [finiteHashAverage, Finset.sum_add_distrib, mul_add]
    _ ≤ _ := add_le_add (pqc_reference_pgm_average_failure K I J D enc p hinj χ) (le_refl _)

/-- A separately verified joint input-error budget is added once to the
collision failure bound. No conditional branch normalization is involved. -/
theorem pqc_reference_pgm_perturbed_budget
    (K I J : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (D : ℕ) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (hinj : Function.Injective enc) (χ : AddChar (J → K) ℂ)
    (ρ : Matrix I J K → Operator D) (hρ : ∀ M, IsDensityOperator (ρ M))
    (η : ℝ)
    (herror : finiteHashAverage (fun M : Matrix I J K =>
      Matrix.traceNorm (ρ M-outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ))/2) ≤ η) :
    finiteHashAverage (fun M : Matrix I J K =>
      1-instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
        (ρ M) (some χ)) ≤
      ((Fintype.card (J → K) : ℝ)-1) * ∑ x : Fin D, p.prob x ^ 2 + η :=
  (pqc_reference_pgm_perturbed_average_failure K I J D enc p hinj χ ρ hρ).trans
    (add_le_add (le_refl _) herror)

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
