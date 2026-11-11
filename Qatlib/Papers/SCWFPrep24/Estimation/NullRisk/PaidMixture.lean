/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidCurrent
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidBell
import Qatlib.Concepts.SpinorSampling.Retained.LowSpinLossBridge

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# One selected two-copy experiment for the complete original loss

The three public fair bits select one current or Bell experiment and one of
four padded directions. Tagged outcomes contain just the selected two-copy
branch. Complete normalized Born laws yield both raw moments and the literal
original current-plus-spin loss. Full paid execution resources are separate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.NativeRecords.RawCurrentRecords
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The original complete dyadic periodic address space. -/
abbrev PairGrid (d r : ℕ) := Fin d → Fin (2^r)
/-- The actual neighbor coin and every measured native-current register bit. -/
abbrev CurrentObservation (d r : ℕ) := Bool × Reg (registerWidth d r)
/-- One alternative observation: padded discard, two current observations, or two Bell addresses and stored-spin readouts. -/
abbrev PairObservation (d r : ℕ) := PUnit ⊕
  ((CurrentObservation d r × CurrentObservation d r) ⊕ (PairGrid d r × PairGrid d r × Reg 2))

/-- The unused direction returns one discarded-observation tag; its physical trace still requests and discards two copies. -/
def discardedPairLaw (d r : ℕ) : FinDist (PairObservation d r) where
  prob o := match o with | .inl _ => 1 | .inr _ => 0
  nonneg o := by cases o <;> norm_num
  sum_one := by simp [Fintype.sum_sum_type]

/-- Only the selected current branch has current observations; it does not draw Bell observations. -/
def currentPairTaggedLaw (d r : ℕ) (p : FinDist (CurrentObservation d r × CurrentObservation d r)) :
    FinDist (PairObservation d r) where
  prob o := match o with | .inl _ => 0 | .inr (.inl z) => p.prob z | .inr (.inr _) => 0
  nonneg o := by
    cases o with
    | inl _ => norm_num
    | inr o => cases o with
      | inl z => exact p.nonneg z
      | inr _ => norm_num
  sum_one := by simpa only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add, add_zero] using p.sum_one

/-- Only the selected Bell branch has its two addresses and two stored-spin readouts; it does not draw current observations. -/
def bellPairTaggedLaw (d r : ℕ) (p : FinDist (PairGrid d r × PairGrid d r × Reg 2)) :
    FinDist (PairObservation d r) where
  prob o := match o with | .inl _ => 0 | .inr (.inl _) => 0 | .inr (.inr z) => p.prob z
  nonneg o := by
    cases o with
    | inl _ => norm_num
    | inr o => cases o with
      | inl _ => norm_num
      | inr z => exact p.nonneg z
  sum_one := by simpa only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add, add_zero] using p.sum_one

/-- Every numerical consumer of a tagged current observation has exactly its original physical two-run expectation. -/
theorem currentPairTaggedLaw_expect (d r : ℕ)
    (p : FinDist (CurrentObservation d r × CurrentObservation d r)) (f : PairObservation d r → ℝ) :
    (currentPairTaggedLaw d r p).expect f = p.expect (fun z => f (.inr (.inl z))) := by
  simp [FinDist.expect,currentPairTaggedLaw,Fintype.sum_sum_type]

/-- Every numerical consumer of a tagged Bell observation has exactly its original physical two-capture expectation. -/
theorem bellPairTaggedLaw_expect (d r : ℕ)
    (p : FinDist (PairGrid d r × PairGrid d r × Reg 2)) (f : PairObservation d r → ℝ) :
    (bellPairTaggedLaw d r p).expect f = p.expect (fun z => f (.inr (.inr z))) := by
  simp [FinDist.expect,bellPairTaggedLaw,Fintype.sum_sum_type]

/-- The discarded tag is the only observable output after the two unused copies are discarded. -/
theorem discardedPairLaw_expect (d r : ℕ) (f : PairObservation d r → ℝ) :
    (discardedPairLaw d r).expect f = f (.inl PUnit.unit) := by
  simp [FinDist.expect,discardedPairLaw,Fintype.sum_sum_type]

/-- Literal real and imaginary parts of a normalized physical spinor meet the canonical current circuit's normalization premise. -/
theorem pairFieldCoordinates (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x, qubitMass (ψ x)=1) (x : PairGrid d r) :
    real0 ψ x^2+imag0 ψ x^2+real1 ψ x^2+imag1 ψ x^2=1 := by
  have h := hψ x
  simpa only [qubitMass,real0,imag0,real1,imag1,Complex.normSq_apply, pow_two,
    add_assoc] using h

/-- The actual physical double shift acts on the original periodic grid. -/
def pairDoubleShift (d r : ℕ) (j : Fin d) (x : PairGrid d r) : PairGrid d r :=
  periodicUnitShift d (2^r) j (periodicUnitShift d (2^r) j x)

/-- Three public fair bits choose exactly one branch and one of four padded directions. Each selected branch contains only its own two physical copies. -/
def pairBranchLaw (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1)
    (velocity : Bool) (dir : Fin 4) : FinDist (PairObservation d r) :=
  if h : dir.val<d then
    if velocity then
      let p := nativeCurrentRawLaw d r ⟨dir.val,h⟩ (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (pairFieldCoordinates d r ψ hψ)
      currentPairTaggedLaw d r (independentPairLaw p p)
    else bellPairTaggedLaw d r (pairedBellLaw ψ hψ (pairDoubleShift d r ⟨dir.val,h⟩))
  else discardedPairLaw d r

/-- The complete law samples one actual branch with probability 1/8 and retains its own physical observations. -/
def paidPairLaw (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) :
    FinDist ((Bool × Fin 4) × PairObservation d r) where
  prob z := (pairBranchLaw d r ψ hψ z.1.1 z.1.2).prob z.2/8
  nonneg z := div_nonneg (FinDist.nonneg _ _) (by norm_num)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    have he (b : Bool) (j : Fin 4) :
        (∑ o : PairObservation d r, (pairBranchLaw d r ψ hψ b j).prob o/8)=(1 : ℝ)/8 := by
      rw [← Finset.sum_div,(pairBranchLaw d r ψ hψ b j).sum_one]
    calc _ = ∑ _ : Bool, ∑ _ : Fin 4, (1 : ℝ)/8 := by
               apply Finset.sum_congr rfl
               intro b _
               apply Finset.sum_congr rfl
               intro j _
               exact he b j
         _ = 1 := by norm_num

/-- An expectation of the complete physical alternative law is the average of the eight branch expectations, rather than an experiment drawing all eight branches. -/
theorem paidPairLaw_expect (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x, qubitMass (ψ x)=1)
    (f : ((Bool × Fin 4) × PairObservation d r) → ℝ) :
    (paidPairLaw d r ψ hψ).expect f =
      (∑ b : Bool, ∑ dir : Fin 4,
        (pairBranchLaw d r ψ hψ b dir).expect (fun o => f ((b,dir),o)))/8 := by
  unfold FinDist.expect paidPairLaw
  simp only [Fintype.sum_prod_type]
  have he (b : Bool) (dir : Fin 4) :
      (∑ o : PairObservation d r, (pairBranchLaw d r ψ hψ b dir).prob o/8*f ((b,dir),o)) =
        (∑ o : PairObservation d r, (pairBranchLaw d r ψ hψ b dir).prob o*f ((b,dir),o))/8 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro o _
    ring
  simp_rw [he,← Finset.sum_div]

/-- The same finite observed branch computes its actual raw return, including zero on every padded or mismatched branch. -/
def paidPairRaw (d r : ℕ) (lam : ℝ) (z : (Bool × Fin 4) × PairObservation d r) : ℝ :=
  if h : z.1.2.val<d then
    match z.2 with
    | .inl _ => 0
    | .inr (.inl raw) => if z.1.1 then pairedCurrentPhysicalRaw d r raw else 0
    | .inr (.inr bell) => if z.1.1 then 0 else
      pairedBellScore (pairDoubleShift d r ⟨z.1.2.val,h⟩)
        (16*(Fintype.card (PairGrid d r) : ℝ)*lam^2) bell
  else 0

/-- The complete physical current mean is computed from the same original spinor coordinates. -/
def pairCurrentMean (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ) (j : Fin d) : PairGrid d r → ℝ :=
  spinorCurrentMean (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) (periodicUnitShift d (2^r)) j

/-- The actual double-shift Bell mean of the same supplied field. -/
def pairBellMean (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ) (j : Fin d) : ℝ :=
  siteMean (fun x => bellProbability (ψ x) (ψ (pairDoubleShift d r j x)))

/-- Each real selected branch has its exact mean; unused directions return zero without drawing another branch. -/
theorem pairBranchRaw_mean (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x, qubitMass (ψ x)=1) (lam : ℝ) (b : Bool) (dir : Fin 4) :
    (pairBranchLaw d r ψ hψ b dir).expect (fun o => paidPairRaw d r lam ((b,dir),o)) =
      if h : dir.val<d then
        if b then 8*siteMean (fun x => (pairCurrentMean d r ψ ⟨dir.val,h⟩ x)^2)
        else 16*lam^2*pairBellMean d r ψ ⟨dir.val,h⟩
      else 0 := by
  by_cases h : dir.val<d
  · cases b with
    | false =>
      simp only [pairBranchLaw,dite_eq_left h,Bool.false_eq_true,ite_false]
      rw [bellPairTaggedLaw_expect]
      simp only [paidPairRaw,dite_eq_left h,Bool.false_eq_true,ite_false]
      rw [pairedBellScore_mean]
      unfold pairBellMean siteMean
      have hM : (Fintype.card (PairGrid d r) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
    | true =>
      simp only [pairBranchLaw,dite_eq_left h,ite_true]
      rw [currentPairTaggedLaw_expect]
      simp only [paidPairRaw,dite_eq_left h,ite_true]
      exact pairedCurrentPhysicalRaw_mean d r ⟨dir.val,h⟩ (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (pairFieldCoordinates d r ψ hψ)
  · simp only [pairBranchLaw,dite_eq_right h]
    rw [discardedPairLaw_expect]
    simp only [paidPairRaw,dite_eq_right h]

/-- The same physical raw branch return has its exact second moment, including all collision and address misses. -/
theorem pairBranchRaw_second (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x, qubitMass (ψ x)=1) (lam : ℝ) (b : Bool) (dir : Fin 4) :
    (pairBranchLaw d r ψ hψ b dir).expect (fun o => (paidPairRaw d r lam ((b,dir),o))^2) =
      if h : dir.val<d then
        if b then 64*(Fintype.card (PairGrid d r) : ℝ)
        else 256*(Fintype.card (PairGrid d r) : ℝ)*lam^4*pairBellMean d r ψ ⟨dir.val,h⟩
      else 0 := by
  by_cases h : dir.val<d
  · cases b with
    | false =>
      simp only [pairBranchLaw,dite_eq_left h,Bool.false_eq_true,ite_false]
      rw [bellPairTaggedLaw_expect]
      simp only [paidPairRaw,dite_eq_left h,Bool.false_eq_true,ite_false]
      rw [pairedBellScore_second]
      unfold pairBellMean siteMean
      have hM : (Fintype.card (PairGrid d r) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
      ring
    | true =>
      simp only [pairBranchLaw,dite_eq_left h,ite_true]
      rw [currentPairTaggedLaw_expect]
      simp only [paidPairRaw,dite_eq_left h,ite_true]
      exact pairedCurrentPhysicalRaw_second d r ⟨dir.val,h⟩ (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (pairFieldCoordinates d r ψ hψ)
  · simp only [pairBranchLaw,dite_eq_right h]
    rw [discardedPairLaw_expect]
    simp only [paidPairRaw,dite_eq_right h,zero_pow (by norm_num : (2 : ℕ)≠0)]

/-- Four padded directions exactly cover the original two- or three-dimensional axes. -/
theorem pair_padded_direction_sum (d : ℕ) (hd : d=2 ∨ d=3) (f : Fin d → ℝ) :
    (∑ dir : Fin 4, if h : dir.val<d then f ⟨dir.val,h⟩ else 0)=∑ j : Fin d, f j := by
  rcases hd with rfl | rfl
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]

/-- The actual eight-way two-copy law has the full current-plus-Bell raw mean of the same original field. -/
theorem paidPairRaw_mean (d r : ℕ) (hd : d=2 ∨ d=3) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x, qubitMass (ψ x)=1) (lam : ℝ) :
    (paidPairLaw d r ψ hψ).expect (paidPairRaw d r lam) =
      (∑ j : Fin d, siteMean (fun x => (pairCurrentMean d r ψ j x)^2))+
        2*lam^2*(∑ j : Fin d,pairBellMean d r ψ j) := by
  rw [paidPairLaw_expect]
  simp_rw [pairBranchRaw_mean]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
  rw [pair_padded_direction_sum d hd (fun j => 16*lam^2*pairBellMean d r ψ j),
    pair_padded_direction_sum d hd (fun j => 8*siteMean (fun x => (pairCurrentMean d r ψ j x)^2))]
  simp_rw [← Finset.mul_sum]
  ring

/-- The same full raw return and normalized alternative law give the complete second moment, without drawing current and Bell copies together. -/
theorem paidPairRaw_second (d r : ℕ) (hd : d=2 ∨ d=3) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x, qubitMass (ψ x)=1) (lam : ℝ) :
    (paidPairLaw d r ψ hψ).expect (fun z => (paidPairRaw d r lam z)^2) =
      8*(d : ℝ)*(Fintype.card (PairGrid d r) : ℝ)+
        32*(Fintype.card (PairGrid d r) : ℝ)*lam^4*(∑ j : Fin d,pairBellMean d r ψ j) := by
  rw [paidPairLaw_expect]
  simp_rw [pairBranchRaw_second]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
  rw [pair_padded_direction_sum d hd
    (fun j => 256*(Fintype.card (PairGrid d r) : ℝ)*lam^4*pairBellMean d r ψ j),
    pair_padded_direction_sum d hd (fun _ : Fin d => 64*(Fintype.card (PairGrid d r) : ℝ))]
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The actual paired return in original loss units is unbiased for the literal complete current and spin loss, without a supplied loss-gap or moment certificate. -/
theorem paidPairRaw_original_loss (d r : ℕ) (hd : d=2 ∨ d=3)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1)
    (h lam : ℝ) (hh : h≠0) :
    (paidPairLaw d r ψ hψ).expect (paidPairRaw d r lam)/h^2 =
      spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (fun _ _ => 0) (periodicUnitShift d (2^r)) h 1 lam := by
  rw [paidPairRaw_mean d r hd ψ hψ lam,
    spinor_discrete_loss_eq (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (pairFieldCoordinates d r ψ hψ) (fun _ _ => 0) (periodicUnitShift d (2^r)) h 1 lam hh (by norm_num)]
  rw [implemented_loss_bell_form _ _ (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
    (pairFieldCoordinates d r ψ hψ)]
  have hb (j : Fin d) : bellMean (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      ((periodicUnitShift d (2^r) j).trans (periodicUnitShift d (2^r) j)) =
        pairBellMean d r ψ j := by
    unfold bellMean pairBellMean
    simp only [complexSpinor_parts]
    rfl
  simp_rw [hb]
  simp only [div_one,mul_zero,sub_zero,mul_pow,one_div_pow]
  simp_rw [site_mean_mul]
  rw [← Finset.mul_sum]
  unfold pairCurrentMean
  field_simp
  ring

/-- Every normalized zero-full-loss input has exactly zero paired mean and raw second moment 8dM, not merely the particular null prior. -/
theorem paidPairRaw_null_moments (d r : ℕ) (hd : d=2 ∨ d=3)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1)
    (h lam : ℝ) (hh : h≠0) (hlam : 0<lam)
    (hzero : spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (fun _ _ => 0) (periodicUnitShift d (2^r)) h 1 lam=0) :
    (paidPairLaw d r ψ hψ).expect (paidPairRaw d r lam)=0 ∧
    (paidPairLaw d r ψ hψ).expect (fun z => (paidPairRaw d r lam z)^2)=
      8*(d : ℝ)*(Fintype.card (PairGrid d r) : ℝ) := by
  have he := paidPairRaw_original_loss d r hd ψ hψ h lam hh
  rw [hzero] at he
  have hmean : (paidPairLaw d r ψ hψ).expect (paidPairRaw d r lam)=0 :=
    (div_eq_zero_iff.mp he).resolve_right (pow_ne_zero 2 hh)
  have hc : 0≤∑ j : Fin d,siteMean (fun x => (pairCurrentMean d r ψ j x)^2) := by
    apply Finset.sum_nonneg
    intro j _
    unfold siteMean
    exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hb : 0≤∑ j : Fin d,pairBellMean d r ψ j := by
    apply Finset.sum_nonneg
    intro j _
    unfold pairBellMean siteMean bellProbability
    exact div_nonneg (Finset.sum_nonneg (fun x _ => div_nonneg (Complex.normSq_nonneg _) (by norm_num)))
      (Nat.cast_nonneg _)
  have hm := paidPairRaw_mean d r hd ψ hψ lam
  rw [hmean] at hm
  have hp : 0<2*lam^2 := by positivity
  have hmul : 2*lam^2*(∑ j : Fin d,pairBellMean d r ψ j)=0 := by
    have hz := mul_nonneg hp.le hb
    linarith
  have hbzero : (∑ j : Fin d,pairBellMean d r ψ j)=0 :=
    (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
  refine ⟨hmean,?_⟩
  rw [paidPairRaw_second d r hd ψ hψ lam,hbzero]
  ring

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
