/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidPhysicalSupply
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidFiniteOutput

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Complete two-copy record law, including measured discarded branches

Only one of the eight alternatives runs. Padded directions still supply,
fully measure and reset both actual copies; their raw measured registers
are retained until the numerical-output coarsening. Every observable then
has exactly the already proved complete-loss statistical law.
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.NativeRecords.RawCurrentRecords
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Physical records retain the otherwise discarded complete measured registers, as well as the selected current or Bell observations. -/
abbrev PhysicalPairObservation (d r : ℕ) : Type :=
  (Reg (d*r+3) × Reg (d*r+3)) ⊕
    ((CurrentObservation d r × CurrentObservation d r) ⊕ (PairGrid d r × PairGrid d r × Reg 2))

/-- Forget only the unused full measurement records after their actual cleanup has been charged. -/
def physicalPairObservationCoarsen (d r : ℕ) : PhysicalPairObservation d r → PairObservation.{0} d r
  | .inl _ => .inl PUnit.unit
  | .inr (.inl z) => .inr (.inl z)
  | .inr (.inr z) => .inr (.inr z)

/-- The finite rational result reads only the actual complete record and the already computed public coefficient. -/
def physicalPairOutputQ (d r : ℕ) (lam : ℚ) (c : InverseSquareQ)
    (z : (Bool × Fin 4) × PhysicalPairObservation d r) : ℚ :=
  paidPairOutputQ d r lam c (z.1,physicalPairObservationCoarsen d r z.2)

noncomputable section
open scoped Classical

/-- An unused copy is still actually supplied and fully measured on its original physical prefix. -/
def discardedFullCopyLaw (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) : FinDist (Reg (d*r+3)) where
  prob q := BornProb (freshPhysicalPrefix d r ψ (Ket false)) q
  nonneg q := sq_nonneg _
  sum_one := by
    rw [freshPhysicalPrefix_mass d r ψ hψ]
    simp [qubitMass,Qatlib.Foundations.PureStateMath.Ket]

/-- The unused branch retains both actual full measured copies before coarsening their numerical return to zero. -/
def physicalDiscardTaggedLaw (d r : ℕ) (p : FinDist (Reg (d*r+3) × Reg (d*r+3))) :
    FinDist (PhysicalPairObservation d r) where
  prob o := match o with | .inl z => p.prob z | .inr _ => 0
  nonneg o := by cases o with
    | inl z => exact p.nonneg z
    | inr _ => norm_num
  sum_one := by simpa only [Fintype.sum_sum_type,Finset.sum_const_zero,add_zero] using p.sum_one

/-- Every unused observation remains in the actual normalized execution law. -/
theorem physicalDiscardTaggedLaw_expect (d r : ℕ)
    (p : FinDist (Reg (d*r+3) × Reg (d*r+3))) (f : PhysicalPairObservation d r → ℝ) :
    (physicalDiscardTaggedLaw d r p).expect f=p.expect (fun z => f (.inl z)) := by
  simp [FinDist.expect,physicalDiscardTaggedLaw,Fintype.sum_sum_type]

/-- Only the selected current branch has current observations; it does not draw Bell observations. -/
def physicalCurrentTaggedLaw (d r : ℕ) (p : FinDist (CurrentObservation d r × CurrentObservation d r)) :
    FinDist (PhysicalPairObservation d r) where
  prob o := match o with | .inl _ => 0 | .inr (.inl z) => p.prob z | .inr (.inr _) => 0
  nonneg o := by
    cases o with
    | inl _ => norm_num
    | inr o => cases o with
      | inl z => exact p.nonneg z
      | inr _ => norm_num
  sum_one := by simpa only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add, add_zero] using p.sum_one

/-- Only the selected Bell branch has its two addresses and two stored-spin readouts; it does not draw current observations. -/
def physicalBellTaggedLaw (d r : ℕ) (p : FinDist (PairGrid d r × PairGrid d r × Reg 2)) :
    FinDist (PhysicalPairObservation d r) where
  prob o := match o with | .inl _ => 0 | .inr (.inl _) => 0 | .inr (.inr z) => p.prob z
  nonneg o := by
    cases o with
    | inl _ => norm_num
    | inr o => cases o with
      | inl _ => norm_num
      | inr z => exact p.nonneg z
  sum_one := by simpa only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add, add_zero] using p.sum_one

/-- Every numerical consumer of a tagged current observation has exactly its original physical two-run expectation. -/
theorem physicalCurrentTaggedLaw_expect (d r : ℕ)
    (p : FinDist (CurrentObservation d r × CurrentObservation d r)) (f : PhysicalPairObservation d r → ℝ) :
    (physicalCurrentTaggedLaw d r p).expect f = p.expect (fun z => f (.inr (.inl z))) := by
  simp [FinDist.expect,physicalCurrentTaggedLaw,Fintype.sum_sum_type]

/-- Every numerical consumer of a tagged Bell observation has exactly its original physical two-capture expectation. -/
theorem physicalBellTaggedLaw_expect (d r : ℕ)
    (p : FinDist (PairGrid d r × PairGrid d r × Reg 2)) (f : PhysicalPairObservation d r → ℝ) :
    (physicalBellTaggedLaw d r p).expect f = p.expect (fun z => f (.inr (.inr z))) := by
  simp [FinDist.expect,physicalBellTaggedLaw,Fintype.sum_sum_type]

/-- Three public fair bits choose one actual two-copy experiment; unused directions retain their measured-and-reset full records. -/
def physicalBranchLaw (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (velocity : Bool) (dir : Fin 4) :
    FinDist (PhysicalPairObservation d r) :=
  if h : dir.val<d then
    if velocity then
      let p := nativeCurrentRawLaw d r ⟨dir.val,h⟩ (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (pairFieldCoordinates d r ψ hψ)
      physicalCurrentTaggedLaw d r (independentPairLaw p p)
    else physicalBellTaggedLaw d r (pairedBellLaw ψ hψ (pairDoubleShift d r ⟨dir.val,h⟩))
  else
    let p := discardedFullCopyLaw d r ψ hψ
    physicalDiscardTaggedLaw d r (independentPairLaw p p)

/-- Coarsening is performed only after the actual unused full records have been accounted for. -/
theorem physicalBranchLaw_coarsen_expect (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (velocity : Bool) (dir : Fin 4)
    (f : PairObservation.{0} d r → ℝ) :
    (physicalBranchLaw d r ψ hψ velocity dir).expect
      (fun o => f (physicalPairObservationCoarsen d r o)) =
      (pairBranchLaw.{0} d r ψ hψ velocity dir).expect f := by
  unfold physicalBranchLaw pairBranchLaw
  by_cases h : dir.val<d
  · rw [dite_eq_left h,dite_eq_left h]
    cases velocity with
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      rw [physicalBellTaggedLaw_expect,bellPairTaggedLaw_expect]
      rfl
    | true =>
      simp only [ite_true]
      rw [physicalCurrentTaggedLaw_expect,currentPairTaggedLaw_expect]
      rfl
  · rw [dite_eq_right h,dite_eq_right h,physicalDiscardTaggedLaw_expect,discardedPairLaw_expect]
    change (independentPairLaw (discardedFullCopyLaw d r ψ hψ) (discardedFullCopyLaw d r ψ hψ)).expect
      (fun _ => f (.inl PUnit.unit))=f (.inl PUnit.unit)
    unfold FinDist.expect
    rw [← Finset.sum_mul,FinDist.sum_one,one_mul]

/-- The complete law samples one actual branch with probability 1/8 and retains its own physical observations. -/
def physicalPairLaw (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) :
    FinDist ((Bool × Fin 4) × PhysicalPairObservation d r) where
  prob z := (physicalBranchLaw d r ψ hψ z.1.1 z.1.2).prob z.2/8
  nonneg z := div_nonneg (FinDist.nonneg _ _) (by norm_num)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    have he (b : Bool) (j : Fin 4) :
        (∑ o : PhysicalPairObservation d r, (physicalBranchLaw d r ψ hψ b j).prob o/8)=(1 : ℝ)/8 := by
      rw [← Finset.sum_div,(physicalBranchLaw d r ψ hψ b j).sum_one]
    calc _ = ∑ _ : Bool, ∑ _ : Fin 4, (1 : ℝ)/8 := by
               apply Finset.sum_congr rfl
               intro b _
               apply Finset.sum_congr rfl
               intro j _
               exact he b j
         _ = 1 := by norm_num

/-- An expectation of the complete physical alternative law is the average of the eight branch expectations, rather than an experiment drawing all eight branches. -/
theorem physicalPairLaw_expect (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x, qubitMass (ψ x)=1)
    (f : ((Bool × Fin 4) × PhysicalPairObservation d r) → ℝ) :
    (physicalPairLaw d r ψ hψ).expect f =
      (∑ b : Bool, ∑ dir : Fin 4,
        (physicalBranchLaw d r ψ hψ b dir).expect (fun o => f ((b,dir),o)))/8 := by
  unfold FinDist.expect physicalPairLaw
  simp only [Fintype.sum_prod_type]
  have he (b : Bool) (dir : Fin 4) :
      (∑ o : PhysicalPairObservation d r, (physicalBranchLaw d r ψ hψ b dir).prob o/8*f ((b,dir),o)) =
        (∑ o : PhysicalPairObservation d r, (physicalBranchLaw d r ψ hψ b dir).prob o*f ((b,dir),o))/8 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro o _
    ring
  simp_rw [he,← Finset.sum_div]

/-- Actual full-record execution has the proved statistical law after discarding only classical unused details. -/
theorem physicalPairLaw_coarsen_expect (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1)
    (f : ((Bool × Fin 4) × PairObservation.{0} d r) → ℝ) :
    (physicalPairLaw d r ψ hψ).expect
      (fun z => f (z.1,physicalPairObservationCoarsen d r z.2)) =
      (paidPairLaw.{0} d r ψ hψ).expect f := by
  rw [physicalPairLaw_expect,paidPairLaw_expect]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro dir _
  exact physicalBranchLaw_coarsen_expect d r ψ hψ b dir (fun o => f ((b,dir),o))

/-- The executable return on the actual complete physical record has exactly the original statistical expectation. -/
theorem physicalPairOutputQ_expect (d r : ℕ) (lam : ℚ) (c : InverseSquareQ)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1) :
    (physicalPairLaw d r ψ hψ).expect (fun z => (physicalPairOutputQ d r lam c z : ℝ))=
      (paidPairLaw.{0} d r ψ hψ).expect (fun z => (paidPairOutputQ d r lam c z : ℝ)) :=
  physicalPairLaw_coarsen_expect d r ψ hψ (fun z => (paidPairOutputQ d r lam c z : ℝ))

/-- Variance is preserved when unused classical details are discarded after the same execution. -/
theorem physicalPairOutputQ_variance (d r : ℕ) (lam : ℚ) (c : InverseSquareQ)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1) :
    (physicalPairLaw d r ψ hψ).variance (fun z => (physicalPairOutputQ d r lam c z : ℝ))=
      (paidPairLaw.{0} d r ψ hψ).variance (fun z => (paidPairOutputQ d r lam c z : ℝ)) := by
  unfold FinDist.variance
  rw [physicalPairOutputQ_expect]
  exact physicalPairLaw_coarsen_expect d r ψ hψ
    (fun z => ((paidPairOutputQ d r lam c z : ℝ)-
      (paidPairLaw.{0} d r ψ hψ).expect (fun z => (paidPairOutputQ d r lam c z : ℝ)))^2)

/-- The actual physical finite-output execution has uniformly bounded bias for the literal whole original current-plus-spin loss. -/
theorem physicalPairOutputQ_bias (d r : ℕ) (lam beta : ℚ) (c : InverseSquareQ)
    (hc : paidPairPlanQ d r lam beta=some c)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1) :
    |(physicalPairLaw d r ψ hψ).expect (fun z => (physicalPairOutputQ d r lam c z : ℝ))-
      spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (lam : ℝ)|≤(beta : ℝ) := by
  rw [physicalPairOutputQ_expect]
  exact paidPairOutputQ_bias d r lam beta c hc ψ hψ

/-- Every actual zero-full-loss input has the exact finite-output null variance, without any added beta-squared term. -/
theorem physicalPairOutputQ_null_variance (d r : ℕ) (lam beta : ℚ) (c : InverseSquareQ)
    (hc : paidPairPlanQ d r lam beta=some c)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1)
    (hzero : spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (lam : ℝ)=0) :
    (physicalPairLaw d r ψ hψ).expect (fun z => (physicalPairOutputQ d r lam c z : ℝ))=0 ∧
    (physicalPairLaw d r ψ hψ).variance (fun z => (physicalPairOutputQ d r lam c z : ℝ))=
      8*(d : ℝ)*(paidGridSize d r : ℝ)*(c.value : ℝ)^2 ∧
    (physicalPairLaw d r ψ hψ).variance (fun z => (physicalPairOutputQ d r lam c z : ℝ))≤
      32*(d : ℝ)*(paidGridSize d r : ℝ)/(2*Real.pi/((2^r : ℕ) : ℝ))^4 := by
  rw [physicalPairOutputQ_expect,physicalPairOutputQ_variance]
  exact paidPairOutputQ_null_variance d r lam beta c hc ψ hψ hzero


/-- The ideal real-valued reference uses exactly the same actual physical record, with the known grid-spacing scale. -/
def physicalPairIdealOutput (d r : ℕ) (lam : ℝ)
    (z : (Bool × Fin 4) × PhysicalPairObservation d r) : ℝ :=
  (1/(2*Real.pi/((2^r : ℕ) : ℝ))^2)*paidPairRaw d r lam
    (z.1,physicalPairObservationCoarsen d r z.2)
/-- On the complete paid physical record the ideal reference is unbiased for the whole original loss on every normalized field. -/
theorem physicalPairIdealOutput_unbiased (d r : ℕ) (hd : d=2 ∨ d=3) (lam : ℝ)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1) :
    (physicalPairLaw d r ψ hψ).expect (physicalPairIdealOutput d r lam)=
      spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 lam := by
  unfold physicalPairIdealOutput
  rw [physicalPairLaw_coarsen_expect d r ψ hψ (fun z => (1/(2*Real.pi/((2^r : ℕ) : ℝ))^2)*paidPairRaw d r lam z),finite_expect_mul]
  rw [one_div,mul_comm,← div_eq_mul_inv]
  exact paidPairRaw_original_loss d r hd ψ hψ _ lam (by positivity)
/-- Every actual zero-full-loss input has exactly the ideal 8dM/h-fourth null variance on the same paid physical experiment. -/
theorem physicalPairIdealOutput_null_variance (d r : ℕ) (hd : d=2 ∨ d=3) (lam : ℝ)
    (hlam : 0<lam) (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1)
    (hzero : spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 lam=0) :
    (physicalPairLaw d r ψ hψ).expect (physicalPairIdealOutput d r lam)=0 ∧
    (physicalPairLaw d r ψ hψ).variance (physicalPairIdealOutput d r lam)=
      8*(d : ℝ)*(paidGridSize d r : ℝ)/(2*Real.pi/((2^r : ℕ) : ℝ))^4 := by
  have hm := physicalPairIdealOutput_unbiased d r hd lam ψ hψ
  rw [hzero] at hm
  refine ⟨hm,?_⟩
  rw [finite_variance_identity,hm,zero_pow (by decide : 2≠0),sub_zero]
  unfold physicalPairIdealOutput
  rw [physicalPairLaw_coarsen_expect d r ψ hψ (fun z => ((1/(2*Real.pi/((2^r : ℕ) : ℝ))^2)*paidPairRaw d r lam z)^2)]
  simp_rw [mul_pow]
  rw [finite_expect_mul,(paidPairRaw_null_moments.{0,0} d r hd ψ hψ _ lam (by positivity) hlam hzero).2,
    ← paidGridSize_card]
  ring

end

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
