/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidMixture
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidRational

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Executable finite rational output for the original loss

Public integer dimensions, finite record bits and rational parameters determine
the coefficient and return. Exact casts connect those executable values to the
actual two-copy mixed Born law and the complete original current/spin loss.
Uniform bias and exact null variance follow without external moment witnesses.
Full physical preparation, reset and space accounting remains separate.
-/

set_option autoImplicit false
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The public grid size is computed by integer exponentiation, without enumerating its addresses. -/
def paidGridSize (d r : ℕ) : ℕ := 2^(d*r)

/-- The actual rational current score reads exactly the same two observed coins, address words and test bits. -/
def observedCurrentRawQ (d r : ℕ) (z : CurrentObservation d r × CurrentObservation d r) : ℚ :=
  let first := velocityRecord d r z.1.1 z.1.2
  let second := velocityRecord d r z.2.1 z.2.2
  if first.1=second.1 then
    8*(paidGridSize d r : ℚ)*(recordSignZ first.2 : ℚ)*(recordSignZ second.2 : ℚ) else 0

/-- An executable double shift reuses the existing native little-endian cyclic address decoder. -/
def observedDoubleShift (d r : ℕ) (j : Fin d) (x : PairGrid d r) : PairGrid d r :=
  decodedNeighbor d r j (decodedNeighbor d r j x)

/-- The finite rational score is computed from only the chosen physical observation and public parameters. -/
def paidPairRawQ (d r : ℕ) (lam : ℚ) (z : (Bool × Fin 4) × PairObservation d r) : ℚ :=
  if h : z.1.2.val<d then
    match z.2 with
    | .inl _ => 0
    | .inr (.inl raw) => if z.1.1 then observedCurrentRawQ d r raw else 0
    | .inr (.inr bell) => if z.1.1 then 0 else
      if decide (bell.2.1=observedDoubleShift d r ⟨z.1.2.val,h⟩ bell.1) then
        if isBellHit bell.2.2=true then 16*(paidGridSize d r : ℚ)*lam^2 else 0
      else 0
  else 0

/-- The same public rational envelope bounds every possible raw return. -/
def paidPairEnvelopeQ (d r : ℕ) (lam : ℚ) : ℚ :=
  8*(paidGridSize d r : ℚ)+16*(paidGridSize d r : ℚ)*lam^2

/-- Public parameters are validated before the actual finite coefficient generator is called. -/
def paidPairPlanQ (d r : ℕ) (lam beta : ℚ) : Option InverseSquareQ :=
  if (d=2 ∨ d=3) ∧ 2≤r ∧ 0<lam ∧ 0<beta then
    inverseSquareGeneratedQ (2^r) (paidPairEnvelopeQ d r lam) beta else none

/-- The final finite rational result multiplies the computed public coefficient by that same actual observed raw score. -/
def paidPairOutputQ (d r : ℕ) (lam : ℚ) (c : InverseSquareQ)
    (z : (Bool × Fin 4) × PairObservation d r) : ℚ := c.value*paidPairRawQ d r lam z


noncomputable section
open scoped Classical BigOperators

/-- The executable grid-size expression equals the original complete dyadic grid cardinality. -/
theorem paidGridSize_card (d r : ℕ) : paidGridSize d r=Fintype.card (PairGrid d r) := by
  unfold paidGridSize PairGrid
  rw [periodic_grid_card,← pow_mul,Nat.mul_comm]

/-- The integer sign already used by finite record processing is exactly the existing physical sign. -/
theorem observed_recordSignZ_cast (b : Bool) : (recordSignZ b : ℝ)=recordSign b := by
  cases b <;> norm_num [recordSignZ,recordSign]

/-- The executable double shift has precisely the original periodic double-neighbor semantics, including wraps. -/
theorem observedDoubleShift_eq (d r : ℕ) (j : Fin d) :
    observedDoubleShift d r j=pairDoubleShift d r j := by
  funext x
  simp only [observedDoubleShift,decoded_neighbor_eq_original,pairDoubleShift]

/-- Casting the executable finite rational current return gives exactly the actual physical raw current return. -/
theorem observedCurrentRawQ_cast (d r : ℕ)
    (z : CurrentObservation d r × CurrentObservation d r) :
    (observedCurrentRawQ d r z : ℝ)=pairedCurrentPhysicalRaw d r z := by
  unfold observedCurrentRawQ pairedCurrentPhysicalRaw
  rw [pairedCurrentRaw_literal]
  by_cases h : (velocityRecord d r z.1.1 z.1.2).1=(velocityRecord d r z.2.1 z.2.2).1
  · simp [h,observed_recordSignZ_cast,paidGridSize_card]
  · simp [h]

/-- The complete executable rational score is pointwise the same current/Bell return whose full Born moments were proved. -/
theorem paidPairRawQ_cast (d r : ℕ) (lam : ℚ)
    (z : (Bool × Fin 4) × PairObservation d r) :
    (paidPairRawQ d r lam z : ℝ)=paidPairRaw d r (lam : ℝ) z := by
  rcases z with ⟨⟨b,dir⟩,o⟩
  by_cases h : dir.val<d
  · cases o with
    | inl _ => simp [paidPairRawQ,paidPairRaw,h]
    | inr o => cases o with
      | inl raw =>
        cases b <;> simp [paidPairRawQ,paidPairRaw,h,observedCurrentRawQ_cast]
      | inr bell =>
        cases b with
        | true => simp [paidPairRawQ,paidPairRaw,h]
        | false =>
          by_cases hm : bell.2.1=pairDoubleShift d r ⟨dir.val,h⟩ bell.1
          <;> by_cases hh : isBellHit bell.2.2=true
          <;> simp [paidPairRawQ,paidPairRaw,h,postCaptureScore,pairedBellScore,
            observedDoubleShift_eq,paidGridSize_card,hm,hh]
  · simp [paidPairRawQ,paidPairRaw,h]

/-- Every native integer-sign current score lies within its actual finite rational envelope. -/
theorem observedCurrentRawQ_abs (d r : ℕ) (z : CurrentObservation d r × CurrentObservation d r) :
    |observedCurrentRawQ d r z|≤8*(paidGridSize d r : ℚ) := by
  have hs (b : Bool) : |(recordSignZ b : ℚ)|=1 := by
    cases b <;> norm_num [recordSignZ]
  dsimp only [observedCurrentRawQ]
  split_ifs
  · simp [abs_mul,hs]
  · simp only [abs_zero]
    positivity

/-- The public computable envelope is strictly positive for every finite dyadic grid. -/
theorem paidPairEnvelopeQ_pos (d r : ℕ) (lam : ℚ) : 0<paidPairEnvelopeQ d r lam := by
  unfold paidPairEnvelopeQ paidGridSize
  positivity

/-- Every finite executable branch return is bounded by the same computed public envelope, without looking at the unknown field. -/
theorem paidPairRawQ_abs (d r : ℕ) (lam : ℚ)
    (z : (Bool × Fin 4) × PairObservation d r) :
    |paidPairRawQ d r lam z|≤paidPairEnvelopeQ d r lam := by
  have hz : |(0 : ℚ)|≤paidPairEnvelopeQ d r lam := by
    simpa only [abs_zero] using (paidPairEnvelopeQ_pos d r lam).le
  have hc : |16*(paidGridSize d r : ℚ)*lam^2|≤paidPairEnvelopeQ d r lam := by
    rw [abs_of_nonneg (by positivity : (0 : ℚ)≤16*(paidGridSize d r : ℚ)*lam^2)]
    unfold paidPairEnvelopeQ
    have hp : (0 : ℚ)≤8*(paidGridSize d r : ℚ) := by positivity
    linarith
  rcases z with ⟨⟨b,dir⟩,o⟩
  by_cases h : dir.val<d
  · cases o with
    | inl _ => simpa only [paidPairRawQ,dite_eq_left h] using hz
    | inr o => cases o with
      | inl raw =>
        cases b with
        | false => simpa only [paidPairRawQ,dite_eq_left h,Bool.false_eq_true,ite_false] using hz
        | true =>
          simp only [paidPairRawQ,dite_eq_left h,ite_true]
          exact (observedCurrentRawQ_abs d r raw).trans (by
            unfold paidPairEnvelopeQ
            have hp : (0 : ℚ)≤16*(paidGridSize d r : ℚ)*lam^2 := by positivity
            linarith)
      | inr bell =>
        cases b with
        | true => simpa only [paidPairRawQ,dite_eq_left h,ite_true] using hz
        | false =>
          simp only [paidPairRawQ,dite_eq_left h,Bool.false_eq_true,ite_false]
          split_ifs <;> first | exact hc | exact hz
  · simpa only [paidPairRawQ,dite_eq_right h] using hz

/-- Every actual successful plan retains the checked physical parameter domain and the real finite generator result. -/
theorem paidPairPlanQ_spec (d r : ℕ) (lam beta : ℚ) (c : InverseSquareQ)
    (hc : paidPairPlanQ d r lam beta=some c) :
    ((d=2 ∨ d=3) ∧ 2≤r ∧ 0<lam ∧ 0<beta) ∧
      inverseSquareGeneratedQ (2^r) (paidPairEnvelopeQ d r lam) beta=some c := by
  dsimp only [paidPairPlanQ] at hc
  split_ifs at hc with h
  exact ⟨h,hc⟩

/-- Every valid public physical parameter tuple actually returns a computed finite rational scale before copies are requested. -/
theorem paidPairPlanQ_total (d r : ℕ) (lam beta : ℚ)
    (hd : d=2 ∨ d=3) (hr : 2≤r) (hlam : 0<lam) (hbeta : 0<beta) :
    ∃ c, paidPairPlanQ d r lam beta=some c := by
  unfold paidPairPlanQ
  rw [ite_eq_left ⟨hd,hr,hlam,hbeta⟩]
  exact inverseSquareGeneratedQ_total (2^r) (paidPairEnvelopeQ d r lam) beta
    (paidPairEnvelopeQ_pos d r lam) hbeta

/-- Casting the actual final rational return gives the same computed coefficient multiplying the original physical raw return. -/
theorem paidPairOutputQ_cast (d r : ℕ) (lam : ℚ) (c : InverseSquareQ)
    (z : (Bool × Fin 4) × PairObservation d r) :
    (paidPairOutputQ d r lam c z : ℝ)=(c.value : ℝ)*paidPairRaw d r (lam : ℝ) z := by
  rw [paidPairOutputQ,Rat.cast_mul,paidPairRawQ_cast]

/-- The same actual executable rational return differs from the ideal original-unit return by at most beta on every observation. -/
theorem paidPairOutputQ_pointwise (d r : ℕ) (lam beta : ℚ) (c : InverseSquareQ)
    (hc : paidPairPlanQ d r lam beta=some c)
    (z : (Bool × Fin 4) × PairObservation d r) :
    |(paidPairOutputQ d r lam c z : ℝ)-
      paidPairRaw d r (lam : ℝ) z/(2*Real.pi/((2^r : ℕ) : ℝ))^2|≤(beta : ℝ) := by
  have hs := paidPairPlanQ_spec d r lam beta c hc
  have hR : |paidPairRaw d r (lam : ℝ) z|≤(paidPairEnvelopeQ d r lam : ℝ) := by
    have he : |(paidPairRawQ d r lam z : ℝ)|≤(paidPairEnvelopeQ d r lam : ℝ) := by
      exact_mod_cast paidPairRawQ_abs d r lam z
    simpa only [paidPairRawQ_cast] using he
  rw [paidPairOutputQ_cast]
  exact inverseSquareGeneratedQ_pointwise (2^r) (paidPairEnvelopeQ d r lam) beta c hs.2
    (paidPairEnvelopeQ_pos d r lam) hs.1.2.2.2.le _ hR

/-- The computed finite rational output has uniform bias at most beta for the literal complete original loss on every normalized original dyadic field. -/
theorem paidPairOutputQ_bias (d r : ℕ) (lam beta : ℚ) (c : InverseSquareQ)
    (hc : paidPairPlanQ d r lam beta=some c)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) :
    |(paidPairLaw.{0} d r ψ hψ).expect (fun z => (paidPairOutputQ d r lam c z : ℝ))-
      spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (lam : ℝ)|≤(beta : ℝ) := by
  let p := paidPairLaw.{0} d r ψ hψ
  let h : ℝ := 2*Real.pi/((2^r : ℕ) : ℝ)
  have hs := paidPairPlanQ_spec d r lam beta c hc
  have hh : h≠0 := ne_of_gt (div_pos (mul_pos (by norm_num) Real.pi_pos) (by positivity))
  have hi : p.expect (fun z => paidPairRaw d r (lam : ℝ) z/h^2)=
      spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (fun _ _ => 0) (periodicUnitShift d (2^r)) h 1 (lam : ℝ) := by
    calc _ = p.expect (paidPairRaw d r (lam : ℝ))/h^2 := by
               unfold FinDist.expect
               rw [Finset.sum_div]
               apply Finset.sum_congr rfl
               intro z _
               ring
         _ = _ := paidPairRaw_original_loss d r hs.1.1 ψ hψ h (lam : ℝ) hh
  change |p.expect (fun z => (paidPairOutputQ d r lam c z : ℝ))-
    spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (fun _ _ => 0) (periodicUnitShift d (2^r)) h 1 (lam : ℝ)|≤_
  rw [← hi]
  unfold FinDist.expect
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ z, |p.prob z*(paidPairOutputQ d r lam c z : ℝ)-
          p.prob z*(paidPairRaw d r (lam : ℝ) z/h^2)| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ z, p.prob z*(beta : ℝ) := by
         apply Finset.sum_le_sum
         intro z _
         rw [← mul_sub,abs_mul,abs_of_nonneg (p.nonneg z)]
         exact mul_le_mul_of_nonneg_left (paidPairOutputQ_pointwise d r lam beta c hc z) (p.nonneg z)
       _ = _ := by rw [← Finset.sum_mul,p.sum_one,one_mul]

/-- For every actual zero-full-loss input, the same finite rational estimator has mean exactly zero and the exact null variance, with no added beta-squared term. -/
theorem paidPairOutputQ_null_variance (d r : ℕ) (lam beta : ℚ) (c : InverseSquareQ)
    (hc : paidPairPlanQ d r lam beta=some c)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1)
    (hzero : spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (lam : ℝ)=0) :
    (paidPairLaw.{0} d r ψ hψ).expect (fun z => (paidPairOutputQ d r lam c z : ℝ))=0 ∧
    (paidPairLaw.{0} d r ψ hψ).variance (fun z => (paidPairOutputQ d r lam c z : ℝ))=
      8*(d : ℝ)*(paidGridSize d r : ℝ)*(c.value : ℝ)^2 ∧
    (paidPairLaw.{0} d r ψ hψ).variance (fun z => (paidPairOutputQ d r lam c z : ℝ))≤
      32*(d : ℝ)*(paidGridSize d r : ℝ)/(2*Real.pi/((2^r : ℕ) : ℝ))^4 := by
  let p := paidPairLaw.{0} d r ψ hψ
  let h : ℝ := 2*Real.pi/((2^r : ℕ) : ℝ)
  have hs := paidPairPlanQ_spec d r lam beta c hc
  have hh : h≠0 := ne_of_gt (div_pos (mul_pos (by norm_num) Real.pi_pos) (by positivity))
  have hl : (0 : ℝ)<(lam : ℝ) := by exact_mod_cast hs.1.2.2.1
  have hm := paidPairRaw_null_moments d r hs.1.1 ψ hψ h (lam : ℝ) hh hl hzero
  have hmean : p.expect (fun z => (paidPairOutputQ d r lam c z : ℝ))=0 := by
    simp_rw [paidPairOutputQ_cast]
    rw [finite_expect_mul,hm.1,mul_zero]
  have hsecond : p.expect (fun z => (paidPairOutputQ d r lam c z : ℝ)^2)=
      8*(d : ℝ)*(paidGridSize d r : ℝ)*(c.value : ℝ)^2 := by
    simp_rw [paidPairOutputQ_cast,mul_pow]
    rw [finite_expect_mul,hm.2,← paidGridSize_card]
    ring
  have hvar : p.variance (fun z => (paidPairOutputQ d r lam c z : ℝ))=
      8*(d : ℝ)*(paidGridSize d r : ℝ)*(c.value : ℝ)^2 := by
    rw [FinDist.variance_eq_expect_sq_sub,hsecond,hmean]
    ring
  refine ⟨hmean,hvar,?_⟩
  rw [hvar]
  exact inverseSquareGeneratedQ_null_coefficient (2^r) d (paidGridSize d r)
    (paidPairEnvelopeQ d r lam) beta c hs.2

end
end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
