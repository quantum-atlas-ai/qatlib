/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
/-! Adaptive input-query hybrid for the finite classical-support protocol.
The whole-run distance is derived from unconditioned instruments and a LOCAL
query-channel bound on all subnormalized PSD inputs. The actual marked-unitary
localization bound, geometric visibility, universal normal form, and output-
circuit compilation are not proved here. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder

/-- The finite protocol identity or bound `instrument_record_contraction` holds under exactly the displayed hypotheses. -/
private theorem instrument_record_contraction {A : Type} [Fintype A] {D : ℕ}
    (I : Instrument A D D) (X : Operator D) (hX : X.IsHermitian) :
    (∑ a,|(Matrix.trace (I.branch a X)).re|)≤Matrix.traceNorm X := by
  have hP : (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX).PosSemidef := by
    unfold Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart
    refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
    intro i
    exact RCLike.ofReal_nonneg.mpr (le_max_right _ _)
  have hN : (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX).PosSemidef := by
    unfold Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart
    refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
    intro i
    exact RCLike.ofReal_nonneg.mpr (le_max_right _ _)
  have hnP : Matrix.traceNorm (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX)=(Matrix.trace (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX)).re := by
    simpa using congrArg Complex.re hP.traceNorm_eq_trace
  have hnN : Matrix.traceNorm (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX)=(Matrix.trace (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX)).re := by
    simpa using congrArg Complex.re hN.traceNorm_eq_trace
  have he (a : A) : (Matrix.trace (I.branch a X)).re=
      instrumentProb I (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX) a-instrumentProb I (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX) a := by
    calc
      _ = (Matrix.trace (I.branch a (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX-Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX))).re :=
        (congrArg (fun Y => (Matrix.trace (I.branch a Y)).re) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.sub_posPart_negPart hX)).symm
      _ = _ := by rw [map_sub,Matrix.trace_sub,Complex.sub_re]; rfl
  have hs : (∑ a,|(Matrix.trace (I.branch a X)).re|)≤
      (∑ a,instrumentProb I (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX) a)+
      (∑ a,instrumentProb I (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX) a) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    rw [he]
    have hh := abs_sub_le (instrumentProb I (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX) a) 0
      (instrumentProb I (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX) a)
    simpa only [sub_zero,zero_sub,abs_neg,
      abs_of_nonneg (instrumentProb_nonneg I hP a),abs_of_nonneg (instrumentProb_nonneg I hN a)] using hh
  rw [sum_instrumentProb,sum_instrumentProb] at hs
  rw [Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.traceNorm_sub_posPart_negPart hX,hnP,hnN]
  exact hs

/-- Readout contraction on the actual full path instrument, for unnormalized
inputs. This is used at an adaptive query node before continuing the run. -/
theorem full_record_contraction {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (ρ σ : Operator D) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (∑ p,|(Matrix.trace (pathMap O S P p ρ)).re-(Matrix.trace (pathMap O S P p σ)).re|)≤
      Matrix.traceNorm (ρ-σ) := by
  have hh := instrument_record_contraction (pathInstrument O S P) (ρ-σ) (hρ.isHermitian.sub hσ.isHermitian)
  simpa only [pathInstrument,Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofBranches,map_sub,Matrix.trace_sub,Complex.sub_re] using hh


/-- Construction for record Distance in the input hybrid model. -/
def recordDistance {D R : ℕ} (O O' : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (ρ σ : Operator D) : ℝ :=
  (∑ p,|(Matrix.trace (pathMap O S P p ρ)).re-(Matrix.trace (pathMap O' S P p σ)).re|)/2

/-- Construction for query Depth in the input hybrid model. -/
def queryDepth {D R : ℕ} : Program D R → ℕ
  | .halt => 0
  | .query _ next => queryDepth next+1
  | .measure _ next => Finset.univ.sup (fun o => queryDepth (next o))
  | .support _ next => Finset.univ.sup (fun o => queryDepth (next o))

/-- The structural query depth bounds the query constructors counted along
all complete paths, including zero-probability branches. -/
theorem path_query_charge_le_depth {D R : ℕ} (P : Program D R) (p : Path P) :
    (pathCharge P p).1≤queryDepth P := by
  induction P with
  | halt => exact Nat.le_refl 0
  | query mode next ih => exact Nat.add_le_add_right (ih p) 1
  | measure I next ih =>
    exact (ih p.1 p.2).trans (Finset.le_sup (f := fun o => queryDepth (next o)) (Finset.mem_univ p.1))
  | support a next ih =>
    exact (ih p.1 p.2).trans (Finset.le_sup (f := fun o => queryDepth (next o)) (Finset.mem_univ p.1))

/-- The finite protocol identity or bound `record_triangle` holds under exactly the displayed hypotheses. -/
private theorem record_triangle {D R : ℕ} (O O' O'' : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (ρ σ τ : Operator D) :
    recordDistance O O'' S P ρ τ≤recordDistance O O' S P ρ σ+recordDistance O' O'' S P σ τ := by
  have hs : (∑ p,|(Matrix.trace (pathMap O S P p ρ)).re-(Matrix.trace (pathMap O'' S P p τ)).re|)≤
      (∑ p,|(Matrix.trace (pathMap O S P p ρ)).re-(Matrix.trace (pathMap O' S P p σ)).re|)+
      (∑ p,|(Matrix.trace (pathMap O' S P p σ)).re-(Matrix.trace (pathMap O'' S P p τ)).re|) := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun p _ => abs_sub_le _ _ _)
  unfold recordDistance
  linarith

/-- The finite protocol identity or bound `record_measure` holds under exactly the displayed hypotheses. -/
private theorem record_measure {D R n : ℕ} (O O' : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (I : Instrument (Fin n) D D) (next : Fin n → Program D R) (ρ σ : Operator D) :
    recordDistance O O' S (.measure I next) ρ σ=
      ∑ o,recordDistance O O' S (next o) (I.branch o ρ) (I.branch o σ) := by
  unfold recordDistance
  change (∑ p : (o : Fin n) × Path (next o),
    |(Matrix.trace (pathMap O S (next p.1) p.2 (I.branch p.1 ρ))).re-
      (Matrix.trace (pathMap O' S (next p.1) p.2 (I.branch p.1 σ))).re|)/2=_
  rw [Fintype.sum_sigma,Finset.sum_div]

/-- The finite protocol identity or bound `record_support` holds under exactly the displayed hypotheses. -/
private theorem record_support {D R : ℕ} (O O' : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (a : ℝ) (next : Fin R → Program D R) (ρ σ : Operator D) :
    recordDistance O O' S (.support a next) ρ σ=
      recordDistance O O' S (next (S a)) ρ σ := by
  unfold recordDistance
  change (∑ p : (o : Fin R) × Path (next o),
    |(Matrix.trace (pathMap O S (.support a next) p ρ)).re-
      (Matrix.trace (pathMap O' S (.support a next) p σ)).re|)/2=_
  rw [Fintype.sum_sigma]
  have he : (∑ o : Fin R, ∑ p : Path (next o),
      |(Matrix.trace (pathMap O S (.support a next) ⟨o,p⟩ ρ)).re-
        (Matrix.trace (pathMap O' S (.support a next) ⟨o,p⟩ σ)).re|)=
      ∑ p : Path (next (S a)),|(Matrix.trace (pathMap O S (next (S a)) p ρ)).re-
        (Matrix.trace (pathMap O' S (next (S a)) p σ)).re| := by
    rw [Finset.sum_eq_single (S a)]
    · apply Finset.sum_congr rfl
      intro p _
      rw [pathMap_support_apply,pathMap_support_apply,ite_eq_left rfl,ite_eq_left rfl]
    · intro o _ ho
      apply Finset.sum_eq_zero
      intro p _
      rw [pathMap_support_apply,pathMap_support_apply,ite_eq_right ho,ite_eq_right ho]
      simp
    · simp
  rw [he]



/-- An actual adaptive-instrument hybrid from a local query-channel bound on
arbitrary subnormalized PSD inputs. The local bound must still be proved for
the marked oracle family; this theorem does not certify it by assumption. -/
theorem adaptive_query_hybrid {H : Type} [Fintype H] {D R : ℕ}
    (μ : FinDist H) (O : H → Bool → QuantumChannel D D) (O0 : Bool → QuantumChannel D D)
    (S : ℝ → Fin R) (δ : ℝ) (hδ : 0≤δ)
    (hlocal : ∀ mode (ρ : Operator D),ρ.PosSemidef →
      (∑ h,μ.prob h*(Matrix.traceNorm ((O h mode).map ρ-(O0 mode).map ρ)/2))≤δ*(Matrix.trace ρ).re)
    (P : Program D R) (ρ : Operator D) (hρ : ρ.PosSemidef) :
    (∑ h,μ.prob h*recordDistance (O h) O0 S P ρ ρ)≤δ*(queryDepth P : ℝ)*(Matrix.trace ρ).re := by
  induction P generalizing ρ with
  | halt => simp [recordDistance,pathMap,queryDepth]
  | query mode next ih =>
    change (∑ h,μ.prob h*recordDistance (O h) O0 S next ((O h mode).map ρ) ((O0 mode).map ρ))≤_
    have hs : (∑ h,μ.prob h*recordDistance (O h) O0 S next ((O h mode).map ρ) ((O0 mode).map ρ))≤
        (∑ h,μ.prob h*(Matrix.traceNorm ((O h mode).map ρ-(O0 mode).map ρ)/2))+
        (∑ h,μ.prob h*recordDistance (O h) O0 S next ((O0 mode).map ρ) ((O0 mode).map ρ)) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro h _
      rw [←mul_add]
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg h)
      have hc : recordDistance (O h) (O h) S next ((O h mode).map ρ) ((O0 mode).map ρ)≤
          Matrix.traceNorm ((O h mode).map ρ-(O0 mode).map ρ)/2 := by
        exact div_le_div_of_nonneg_right (full_record_contraction (O h) S next _ _
          ((O h mode).completelyPositive.positive hρ) ((O0 mode).completelyPositive.positive hρ)) (by norm_num)
      exact (record_triangle (O h) (O h) O0 S next _ _ _).trans (add_le_add hc le_rfl)
    have hi := ih ((O0 mode).map ρ) ((O0 mode).completelyPositive.positive hρ)
    have ht : (Matrix.trace ((O0 mode).map ρ)).re=(Matrix.trace ρ).re :=
      congrArg Complex.re ((O0 mode).tracePreserving ρ)
    rw [ht] at hi
    calc
      _ ≤ _ := hs
      _ ≤ δ*(Matrix.trace ρ).re+δ*(queryDepth next : ℝ)*(Matrix.trace ρ).re := add_le_add (hlocal mode ρ hρ) hi
      _ = _ := by simp only [queryDepth,Nat.cast_add,Nat.cast_one]; ring
  | @measure n I next ih =>
    simp_rw [record_measure,Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : 0≤(Matrix.trace ρ).re := (RCLike.nonneg_iff.mp hρ.trace_nonneg).1
    have htotal : (∑ o : Fin n,(Matrix.trace (I.branch o ρ)).re)=(Matrix.trace ρ).re := sum_instrumentProb I ρ
    calc
      _ ≤ ∑ o : Fin n,δ*(queryDepth (next o) : ℝ)*(Matrix.trace (I.branch o ρ)).re :=
        Finset.sum_le_sum (fun o _ => ih o (I.branch o ρ) ((I.cp o).positive hρ))
      _ ≤ ∑ o : Fin n,δ*(queryDepth (.measure I next) : ℝ)*(Matrix.trace (I.branch o ρ)).re := by
        apply Finset.sum_le_sum
        intro o _
        have hcap : (queryDepth (next o) : ℝ)≤queryDepth (.measure I next) := by
          exact_mod_cast (Finset.le_sup (f := fun o => queryDepth (next o)) (Finset.mem_univ o))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap hδ) (instrumentProb_nonneg I hρ o)
      _ = _ := by rw [←Finset.mul_sum,htotal]
  | support a next ih =>
    simp_rw [record_support]
    have hm : 0≤(Matrix.trace ρ).re := (RCLike.nonneg_iff.mp hρ.trace_nonneg).1
    have hcap : (queryDepth (next (S a)) : ℝ)≤queryDepth (.support a next) := by
      exact_mod_cast (Finset.le_sup (f := fun o => queryDepth (next o)) (Finset.mem_univ (S a)))
    exact (ih (S a) ρ hρ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap hδ) hm)



/-- The joint support bound now receives a LOCAL input-query error premise;
the complete adaptive dummy/baseline distance is derived from actual execution. -/
theorem finite_protocol_query_bound {H : Type} [Fintype H] [DecidableEq H] {D R : ℕ}
    (μ : FinDist H) (O : H → Bool → QuantumChannel D D) (O0 : Bool → QuantumChannel D D)
    (S : H → ℝ → Fin R) (B : ℝ → Fin R) (P : Program D R)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (bad : H → ℝ → Prop) (hS : ∀ h a,¬bad h a → S h a=B a)
    (δ v : ℝ) (s : ℕ) (hδ : 0≤δ)
    (hlocal : ∀ mode (σ : Operator D),σ.PosSemidef →
      (∑ h,μ.prob h*(Matrix.traceNorm ((O h mode).map σ-(O0 mode).map σ)/2))≤δ*(Matrix.trace σ).re)
    (hv : ∀ a,(∑ h∈Finset.univ.filter (fun h => bad h a),μ.prob h)≤v)
    (hc : ∀ p : Path P, (pathCharge P p).2 ≤ s) :
    (∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun h => pathLaw (O h) (S h) P ρ hρ htrace)).prob hp-
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => pathLaw O0 B P ρ hρ htrace)).prob hp|)/2≤
      2*(δ*(queryDepth P : ℝ))+(s : ℝ)*v := by
  apply finite_protocol_support_bound μ O O0 S B P ρ hρ htrace bad hS
    (δ*(queryDepth P : ℝ)) v s _ hv hc
  have hh := adaptive_query_hybrid μ O O0 B δ hδ hlocal P ρ hρ
  rw [htrace,mul_one] at hh
  exact hh

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
