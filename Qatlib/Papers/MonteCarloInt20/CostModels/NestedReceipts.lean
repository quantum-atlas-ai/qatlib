/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
import Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy

/-!
# Executed nested words, access counts, and accuracy

This module connects `nestedWord` to the matrix execution of its outer amplitude-estimation
circuit. It proves the exact total source-access count `(2 * N - 1) * (2 * M - 1)` and
identifies measured outer events with the corresponding `nestedLaw` probabilities.

Under unitary preparation, the stated phase and payoff-range assumptions, and a Lipschitz
derivative for the payoff, `executed_nested_accuracy` combines the outer estimation window with
the inner error budget. This supplies an executed-circuit accuracy statement for the nested
construction studied in [KanekoEtAl2020].

## Main statements

* `nested_total_source_accesses`: Compute the sum of forward and backward source accesses.
* `nestedWord_event`: Identify output-event probabilities with the finite nested law.
* `executed_nested_accuracy`: Bound total output error with probability at least `8 / π^2`.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MonteCarloInt20.CostModels.NestedReceipts

noncomputable local instance dataDecision (n M : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq ((Reg n × Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner M I) × Bool) :=
  instDecidableEqProd

noncomputable local instance fullDecision (n M N : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq (Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner N ((Reg n × Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner M I) × Bool)) :=
  instDecidableEqProd

/-- The outer amplitude-estimation register containing the sample register, inner estimation
register, and payoff flag. -/
abbrev OuterReg (n M N : ℕ) (I : Type) := Inner N ((Reg n × Inner M I) × Bool)

/-- The matrix evaluation of `nestedWord` equals the run matrix of the stated counted outer
amplitude-estimation circuit. -/
theorem nestedWord_eval {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 0 < M) (A : Reg n → Matrix I I ℂ) (i₀ : I)
    (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    wordEval (G:=Matrix (OuterReg n M N I) (OuterReg n M N I) ℂ) (nestedWord n M N hM A i₀ S D g)=
      runMatrix (I:=OuterReg n M N I) (aeControlledGate (I:=((Reg n × Inner M I) × Bool)) N
        (preparedMark (Finset.univ.filter (fun p => p.2=true))))
        (countedAECircuit N (outerPreparation n M A i₀ S D g) ((ZeroStr n,innerSeed M hM i₀),false)) := by
  have h := expandedOuterWord_eval (I:=((Reg n × Inner M I) × Bool)) N ((ZeroStr n,innerSeed M hM i₀),false)
    (Finset.univ.filter (fun p => p.2=true)) (preparationWord n M A i₀ S D g) (aeAccessWord (I:=((Reg n × Inner M I) × Bool)) N)
  rw [preparationWord_eval] at h
  exact h

/-- For positive inner and outer sizes, the counted outer circuit has `N - 1` queries, and its
access word has `N` forward and `N - 1` backward preparation accesses. -/
theorem outer_counts {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 0 < M) (hN : 0 < N) (A : Reg n → Matrix I I ℂ) (i₀ : I)
    (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    QueryCount (countedAECircuit N (outerPreparation n M A i₀ S D g)
      ((ZeroStr n,innerSeed M hM i₀),false))=N-1 ∧
    aeForwardAccesses (aeAccessWord (I:=((Reg n × Inner M I) × Bool)) N)=N ∧
    aeBackwardAccesses (aeAccessWord (I:=((Reg n × Inner M I) × Bool)) N)=N-1 := by
  exact ⟨(prepared_ae_access_ledger N hN (outerPreparation n M A i₀ S D g)
    ((ZeroStr n,innerSeed M hM i₀),false)).1,
    (prepared_ae_separate_access_counts N hN).1,(prepared_ae_separate_access_counts N hN).2.1⟩

/-- For positive inner and outer sizes, the sum of forward and backward source accesses in the
nested word equals `(2 * N - 1) * (2 * M - 1)`. -/
theorem nested_total_source_accesses {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 0 < M) (hN : 0 < N) (A : Reg n → Matrix I I ℂ) (i₀ : I)
    (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    accessCount .inputForward (nestedWord n M N hM A i₀ S D g)+
      accessCount .inputBackward (nestedWord n M N hM A i₀ S D g)=(2*N-1)*(2*M-1) := by
  have hc := nestedWord_source_counts n M N hM hN A i₀ S D g
  rw [hc.1,hc.2]
  have hNp : N-1+1=N := Nat.sub_add_cancel hN
  have hMp : M-1+1=M := Nat.sub_add_cancel hM
  have hN2 : 2*N-1=N+(N-1) := by omega
  have hM2 : 2*M-1=M+(M-1) := by omega
  rw [hN2,hM2]
  ring

/-- With unitary preparations, payoff values in `[0, 1]`, and `M, N ≥ 2`, the executed nested
word's probability of any outer-index event equals its probability under `nestedLaw`. -/
theorem nestedWord_event {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) (P : Fin N → Prop) :
    MeasureProb (I:=OuterReg n M N I) (ApplyGate (I:=OuterReg n M N I) (wordEval (G:=Matrix (OuterReg n M N I) (OuterReg n M N I) ℂ) (nestedWord n M N (by omega) A i₀ S D g))
      (Ket (I:=OuterReg n M N I) (innerSeed N (by omega) ((ZeroStr n,innerSeed M (by omega) i₀),false))))
      (Finset.univ.filter (fun p => P p.1))=
      ∑ z ∈ Finset.univ.filter P,(nestedLaw n M N hM hN A i₀ S hA D g hg).prob z := by
  rw [nestedWord_eval,runMatrix_apply]
  have hk :=
      innerSeed_ket (I:=((Reg n × Inner M I) × Bool)) N (show 0<N by omega)
      ((ZeroStr n,innerSeed M (by omega) i₀),false)
  rw [hk]
  exact (aeLaw_event (I:=((Reg n × Inner M I) × Bool)) N hN (outerPreparation n M A i₀ S D g)
    ((ZeroStr n,innerSeed M (by omega) i₀),false) (Finset.univ.filter (fun p => p.2=true))
    (outerPreparation_unitary n M hM A i₀ S hA D g hg) P).symm

/-- Under the stated unitary, phase-matching, payoff-range, and Lipschitz-derivative hypotheses
with `M, N ≥ 2`, the executed estimate is within `outerWindow + innerBudget` of `idealMean`
with probability at least `8 / Real.pi^2`; see [KanekoEtAl2020]. -/
theorem executed_nested_accuracy {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (θ : Reg n → ℝ)
    (hθ0 : ∀ j,0 < θ j) (hθ1 : ∀ j,θ j < 1/2)
    (ha : ∀ j,MeasureProb (preparedAAState (A j) i₀) (S j)=Real.sin (θ j*Real.pi)^2)
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp)
    (hrange : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    8/Real.pi^2 ≤ MeasureProb (I:=OuterReg n M N I)
      (ApplyGate (I:=OuterReg n M N I) (wordEval (G:=Matrix (OuterReg n M N I) (OuterReg n M N I) ℂ) (nestedWord n M N (by omega) A i₀ S D g))
        (Ket (I:=OuterReg n M N I) (innerSeed N (by omega) ((ZeroStr n,innerSeed M (by omega) i₀),false))))
      (Finset.univ.filter (fun p => |aeEstimate N p.1-idealMean n θ D g| ≤
        outerWindow N (nestedMean n M hM A i₀ S hA D g)+innerBudget n M θ D gp K)) := by
  have he := nestedWord_event (I:=I) n M N hM hN A i₀ S hA D g hrange
    (fun z => |aeEstimate N z-idealMean n θ D g| ≤
      outerWindow N (nestedMean n M hM A i₀ S hA D g)+innerBudget n M θ D gp K)
  exact (nested_total_error n M N hM hN A i₀ S hA θ hθ0 hθ1 ha D g gp K hg hgp hrange).trans_eq he.symm

end Qatlib.Papers.MonteCarloInt20.CostModels.NestedReceipts
