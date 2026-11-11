/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.EffectiveInput.EffectiveQuantizerExactScaleStat
import Qatlib.Concepts.DiamondQdrift.QuantizerCert.EffectiveCeilQuantizerLawCamp
import Qatlib.Concepts.MixtureLaw.ScheduleLaw.MixturePowerLawPerturbation

/-!
# Effective quantization with exact qDRIFT time scaling

This module implements ceiling quantization from a finite list of rational oracle reads and
proves its agreement with `effectiveCeilQuantizer`. It then proves
`effectiveQuantizerExactScaleSubgoal`, combining probability-law perturbation, sign handling,
and exact time rescaling in the qDRIFT framework of [Campbell2019].

The final result supplies a quantizer certificate, a normalized-weight error bound, a finite
diamond simulation guarantee, and per-path quantum and classical resource bounds.

## Main statements

* `effectiveCeilQuantizerReadRun_reads`: counts one oracle read per coefficient.
* `effective_budgets`: bounds analytic, quantization, and capped-sampling errors.
* `effectiveQuantizerExactScaleSubgoal`: proves the exact-scale simulation specification.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MixtureLaw.ScheduleLaw
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.DiamondQdrift.DigitEndpoint
open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.DiamondQdrift.SignedBridge
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling
open Qatlib.Concepts.RandCompile.ReferenceModel

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.RandCompile.EffectiveInput
open Matrix
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

/-- Converts a list of `L` rational digits into weights by taking the natural ceiling of each
digit scaled by `M` over the total digit mass, then adding one. -/
def effectiveCeilQuantizerRat {L : ℕ} (digits : List ℚ)
    (hlen : digits.length = L) (M : ℕ) : Fin L → ℕ :=
  let mass := digits.sum
  fun j => Nat.ceil ((M : ℚ) * digits[j.val]'(by rw [hlen]; exact j.isLt) / mass) + 1

/-- Loads each oracle value at precision `k`, computes ceiling-quantizer weights, and returns
the weights together with the number of loaded digits. -/
def effectiveCeilQuantizerReadRun {L : ℕ} (q : Fin L → ℕ → ℚ) (k M : ℕ) :
    (Fin L → ℕ) × ℕ :=
  let digits := List.ofFn (fun j => q j k)
  (effectiveCeilQuantizerRat digits List.length_ofFn M, digits.length)

/-- Taking the natural ceiling of a rational number is unchanged by casting it to the reals. -/
private theorem natCeilRatCast (x : ℚ) : Nat.ceil (x : ℝ) = Nat.ceil x := by
  rw [← Int.ceil_toNat, ← Int.ceil_toNat, Rat.ceil_cast]

/-- The finite rational read run produces exactly the weights of `effectiveCeilQuantizer`. -/
theorem effectiveCeilQuantizerReadRun_weights {L : ℕ} (q : Fin L → ℕ → ℚ) (k M : ℕ) :
    (effectiveCeilQuantizerReadRun q k M).1 = effectiveCeilQuantizer q k M := by
  funext j
  simp only [effectiveCeilQuantizerReadRun, effectiveCeilQuantizerRat,
    effectiveCeilQuantizer, ratLowerMass, List.getElem_ofFn, List.sum_ofFn]
  have hcast : (((M : ℚ) * q j k / (∑ i, q i k) : ℚ) : ℝ) =
      (M : ℝ) * (q j k : ℝ) / (∑ i, (q i k : ℝ)) := by push_cast; rfl
  rw [← natCeilRatCast, hcast]

/-- The ceiling-quantizer read run loads exactly `L` digits. -/
theorem effectiveCeilQuantizerReadRun_reads {L : ℕ} (q : Fin L → ℕ → ℚ) (k M : ℕ) :
    (effectiveCeilQuantizerReadRun q k M).2 = L := by
  simp [effectiveCeilQuantizerReadRun]

/-- Every real `x` is at most twice `2` raised to `Nat.log2 (Nat.ceil x + 1)`. -/
private theorem log2_ceil_half_bound (x : ℝ) :
    x ≤ 2*((2 ^ Nat.log2 (Nat.ceil x+1) : ℕ) : ℝ) := by
  have hl := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Nat.ceil x+1)
  rw [← Nat.log2_eq_log_two, pow_succ] at hl
  have hr : (Nat.ceil x : ℝ)+1 ≤ ((2 ^ Nat.log2 (Nat.ceil x+1) : ℕ) : ℝ)*2 := by
    exact_mod_cast hl.le
  have hc : (Nat.ceil x : ℝ) ≤ 2*((2 ^ Nat.log2 (Nat.ceil x+1) : ℕ) : ℝ) := by
    linarith only [hr]
  exact (Nat.le_ceil x).trans hc

/-- Mixing a finite probability law with a point mass with nonnegative coefficient `α` changes
its probabilities by at most `2 * α` in summed absolute difference. -/
private theorem cap_law_l1 {J : Type} [Fintype J] [DecidableEq J]
    (d e : FinDist J) (j0 : J) (α : ℝ) (hα : 0 ≤ α)
    (he : ∀ j, e.prob j = (1-α)*d.prob j+α*(if j=j0 then 1 else 0)) :
    (∑ j, |e.prob j-d.prob j|) ≤ 2*α := by
  have hpoint (j : J) : |e.prob j-d.prob j| ≤ α*((if j=j0 then 1 else 0)+d.prob j) := by
    have hid : e.prob j-d.prob j = α*((if j=j0 then 1 else 0)-d.prob j) := by
      rw [he]; ring
    rw [hid, abs_mul, abs_of_nonneg hα]
    apply mul_le_mul_of_nonneg_left _ hα
    have ht := norm_sub_le (if j=j0 then (1 : ℝ) else 0) (d.prob j)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (d.nonneg j),
      abs_of_nonneg (by split <;> norm_num : 0 ≤ (if j=j0 then (1 : ℝ) else 0))] using ht
  refine (Finset.sum_le_sum (fun j _ => hpoint j)).trans_eq ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, d.sum_one]
  simp
  ring

/-- The prescribed rejection fuel bounds `2 * n * (1/2)^R` by `(1/2)^s / 2`. -/
private theorem fair_fuel_inverse_budget (n s : ℕ) :
    2*(n : ℝ)*((2 : ℝ)⁻¹)^(fairQdriftFuel n s) ≤ ((2 : ℝ)⁻¹)^s/2 := by
  let c := Nat.clog 2 (max 1 n)
  have hp : (n : ℝ) ≤ (2 : ℝ)^c := by
    exact_mod_cast (Nat.le_max_right 1 n).trans (Nat.le_pow_clog (by decide) (max 1 n))
  change 2*(n : ℝ)*((2 : ℝ)⁻¹)^(s+c+2) ≤ _
  rw [pow_add, pow_add]
  calc
    _ ≤ 2*(2 : ℝ)^c*(((2 : ℝ)⁻¹)^s*((2 : ℝ)⁻¹)^c*((2 : ℝ)⁻¹)^2) := by gcongr
    _ = _ := by simp only [inv_pow]; field_simp

/-- For positive tolerance, the chosen step count and quantizer scale are positive, and the
analytic, accumulated quantization, and capped-sampling error expressions are bounded by `ε
/ 3`, `2 * ε / 3`, and `ε / 6`, respectively. -/
private theorem effective_budgets (L : ℕ) (lam t ε : ℝ) (hε : 0 < ε) :
    let n := realCoefQdriftSteps lam t ε
    let M : ℕ := 2^(effectiveQdriftBits L n ε)
    let s := realCoefQdriftSuccess ε
    let R := fairQdriftFuel n s
    0 < n ∧ 0 < M ∧ 4*lam^2*t^2/(n : ℝ) ≤ ε/3 ∧
      (n : ℝ)*(4*(L : ℝ)/M) ≤ 2*ε/3 ∧
      2*(n : ℝ)*((2 : ℝ)⁻¹)^R ≤ ε/6 := by
  (try dsimp only)
  let n := realCoefQdriftSteps lam t ε
  let b := effectiveQdriftBits L n ε
  let M := 2^b
  let s := realCoefQdriftSuccess ε
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hM : 0 < M := by dsimp [M]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnc : 12*lam^2*t^2/ε ≤ (n : ℝ) := (Nat.le_ceil _).trans (by
    have hc : Nat.ceil (12*lam^2*t^2/ε) ≤ n := le_max_right _ _
    exact_mod_cast hc)
  have hraw := (div_le_iff₀ hε).mp hnc
  have hanalytic : 4*lam^2*t^2/(n : ℝ) ≤ ε/3 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith only [hraw]
  have hqc : 12*(n : ℝ)*(L : ℝ)/ε ≤ 2*(M : ℝ) := log2_ceil_half_bound _
  have hqraw := (div_le_iff₀ hε).mp hqc
  have hquant : (n : ℝ)*(4*(L : ℝ)/M) ≤ 2*ε/3 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hMR).mpr
    nlinarith only [hqraw]
  have hsc : 6/ε ≤ 2*(2 : ℝ)^s := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using! log2_ceil_half_bound (6/ε)
  have hsraw := (div_le_iff₀ hε).mp hsc
  have hsbudget : ((2 : ℝ)⁻¹)^s ≤ ε/3 := by
    rw [inv_pow, inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^s)).mpr
    nlinarith only [hsraw]
  refine ⟨hn, hM, hanalytic, hquant, ?_⟩
  exact (fair_fuel_inverse_budget n s).trans (by linarith only [hsbudget])

/-- Under the sign promise, multiplying an absolute coefficient by its sign flag recovers the
original real coefficient as a complex scalar. -/
private theorem signed_flag_scalar {L : ℕ} (a : Fin L → ℝ) (sgn : Fin L → Bool)
    (hpromise : ∀ j, (if sgn j then -(a j) else a j) = |a j|) (j : Fin L) :
    (((|a j| : ℝ) : ℂ))*(if sgn j then (-1 : ℂ) else 1) = ((a j : ℝ) : ℂ) := by
  have hp := hpromise j
  by_cases hb : sgn j = true
  · rw [if_pos hb] at hp
    rw [if_pos hb, mul_neg_one, ← hp, Complex.ofReal_neg, neg_neg]
  · rw [if_neg hb] at hp
    rw [if_neg hb, mul_one, ← hp]

/-- Multiplication by the scalar sign specified by a Boolean flag preserves Hermiticity and the
contraction bound. -/
private theorem signed_flag_contract {L D : ℕ} (K : Fin L → Operator D)
    (sgn : Fin L → Bool) (Ks : Fin L → Operator D)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (hKs : ∀ j, Ks j = (if sgn j then (-1 : ℂ) else 1) • K j) (j : Fin L) :
    (Ks j).IsHermitian ∧ ‖Ks j‖ ≤ 1 := by
  rw [hKs j]
  by_cases hb : sgn j = true
  · rw [if_pos hb]
    exact ⟨by simpa using! (hK j).1.neg, by simpa using! (hK j).2⟩
  · rw [if_neg hb]
    simpa using! hK j

/-- Under positive absolute coefficient mass and the sign promise, the importance-law
Hamiltonian formed from signed terms equals the original signed coefficient sum. -/
private theorem signed_flag_hamiltonian {L D : ℕ} (a : Fin L → ℝ)
    (K : Fin L → Operator D) (sgn : Fin L → Bool) (hlam : 0 < ∑ j, |a j|)
    (Ks : Fin L → Operator D)
    (hKs : ∀ j, Ks j = (if sgn j then (-1 : ℂ) else 1) • K j)
    (hpromise : ∀ j, (if sgn j then -(a j) else a j) = |a j|) :
    qdriftHamiltonian (qdriftCoefficientLaw a hlam) Ks (∑ j, |a j|) =
      ∑ j, (a j : ℂ) • K j := by
  have hne : (∑ i, |a i| : ℝ) ≠ 0 := ne_of_gt hlam
  have hneC : ((∑ i, |a i| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  unfold qdriftHamiltonian
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hKs j]
  simp only [qdriftCoefficientLaw, smul_smul]
  congr 1
  rw [← mul_assoc, Complex.ofReal_div, mul_div_cancel₀ _ hneC]
  exact signed_flag_scalar a sgn hpromise j

/-- Valid lower oracles and sign flags satisfy the exact-scale quantizer specification for
Hermitian contraction terms and positive mass and tolerance. This includes certification,
normalized-weight accuracy, finite diamond error at most `ε`, and the stated circuit and
sampling ledgers. -/
theorem effectiveQuantizerExactScaleSubgoal : EffectiveQuantizerExactScaleSubgoal := by
  intro L D a K t ε j0 q sgn hlam hK hε horacle hpromise
  (try dsimp only)
  let lam := ∑ j, |a j|
  let n := realCoefQdriftSteps lam t ε
  let M := 2^effectiveQdriftBits L n ε
  let s := realCoefQdriftSuccess ε
  let R := fairQdriftFuel n s
  let kB := Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/lam))
  let loaded := effectiveCeilQuantizerReadRun q kB M
  let w := loaded.1
  let W := weightTotal w
  let Ks := fun j => (if sgn j then (-1 : ℂ) else 1) • K j
  have hw : effectiveCeilQuantizer q kB M = w :=
    (effectiveCeilQuantizerReadRun_weights q kB M).symm
  rw [hw]
  have hKsrepr (j : Fin L) : Ks j = (if sgn j then (-1 : ℂ) else 1) • K j := rfl
  obtain ⟨hn, hM, hanalytic, hquantBudget, hcapBudget⟩ := effective_budgets L lam t ε hε
  have hcert : ceilQuantizerCert M q kB := by
    show ceilQuantizerCert M q
      (Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/lam)))
    refine ceilQuantizerCert_of_pow_bound (h := fun j => |a j|) horacle ?_
    have h1 : (L : ℝ)*(2*(M : ℝ)+3)/lam
        ≤ ((Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/lam) : ℕ) : ℝ) :=
      by exact_mod_cast Nat.le_ceil _
    have h2 : ((Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/lam) : ℕ) : ℝ)
        ≤ ((2 : ℝ)^(Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/lam)))) :=
      by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) _
    have h := (div_le_iff₀ hlam).mp (h1.trans h2)
    exact h.trans (le_of_eq (mul_comm _ _))
  obtain ⟨hmass, hl1⟩ := effectiveCeilQuantizer_mass_and_l1 horacle hlam hM hcert
  rw [hw] at hmass hl1
  have hquantL1 : (∑ j, |(fairQdriftImportanceLaw w (lt_of_lt_of_le hM hmass.1)).prob j
      -(qdriftCoefficientLaw a hlam).prob j|) ≤ 4*(L : ℝ)/M := hl1
  have hW : 0 < W := lt_of_lt_of_le hM hmass.1
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let qd := fairQdriftImportanceLaw w hW
  let e := fairQdriftLaw w j0 R
  let p := qdriftCoefficientLaw a hlam
  let U := fun j => HamiltonianEvolution (Ks j) (t*lam/(n : ℝ))
  have hKs : ∀ j, (Ks j).IsHermitian ∧ ‖Ks j‖ ≤ 1 :=
    fun j => signed_flag_contract K sgn Ks hK hKsrepr j
  have hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    fun j => hamiltonianEvolution_unitary (hKs j).1 _
  let q0 := 1-(W : ℝ)/(2 : ℝ)^(Nat.clog 2 W)
  let α := q0^R
  have hreject := fairQdriftReject_real w hW
  have hα : 0 ≤ α := pow_nonneg hreject.2.1 R
  have hαbound : α ≤ ((2 : ℝ)⁻¹)^R :=
    pow_le_pow_left₀ hreject.2.1 (by simpa only [one_div] using! hreject.2.2) R
  have heprob (j : Fin L) : e.prob j = (1-α)*qd.prob j+α*(if j=j0 then 1 else 0) := by
    rw [fair_bit_qdrift_actual_sampler_law L R w j0 hW j]
    dsimp [e, qd, fairQdriftImportanceLaw, α, q0]
    split_ifs <;> ring
  have hcapL1 : (∑ j, |e.prob j-qd.prob j|) ≤ 2*((2 : ℝ)⁻¹)^R :=
    (cap_law_l1 qd e j0 α hα heprob).trans
      (mul_le_mul_of_nonneg_left hαbound (by norm_num))
  have hcapBudget' : (n : ℝ)*(2*((2 : ℝ)⁻¹)^R) ≤ ε/6 := by
    calc
      _ = 2*(n : ℝ)*((2 : ℝ)⁻¹)^R := by ring
      _ ≤ _ := hcapBudget
  refine ⟨hcert, ⟨hmass.1, hl1⟩, ?_, ?_⟩
  · have htime : (t*lam/(W : ℝ))*(W : ℝ)/(n : ℝ) = t*lam/(n : ℝ) := by
      field_simp
    have hbranch : (fun j => HamiltonianEvolution (Ks j)
        ((t*lam/(W : ℝ))*(weightTotal w : ℝ)/(n : ℝ))) = U :=
      funext (fun j => congrArg (HamiltonianEvolution (Ks j)) htime)
    have huniform (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
        Matrix.traceNorm (tensorLeft (fairQdriftActualMap w j0 n R Ks (t*lam/(W : ℝ))) X-
          tensorLeft (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)) X) ≤
        (2*ε)*Matrix.traceNorm X := by
      have hX := Matrix.traceNorm_nonneg X
      have hc := (referenceMixturePower_law_perturbation e qd U hU r n X).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcapL1 (Nat.cast_nonneg n)) hX)
      have hcap : Matrix.traceNorm (referenceMixturePower e U r n X
          -referenceMixturePower qd U r n X) ≤ (ε/6)*Matrix.traceNorm X :=
        hc.trans (mul_le_mul_of_nonneg_right hcapBudget' hX)
      have hq := (referenceMixturePower_law_perturbation qd p U hU r n X).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hquantL1 (Nat.cast_nonneg n)) hX)
      have hquantum : Matrix.traceNorm (referenceMixturePower qd U r n X
          -referenceMixturePower p U r n X) ≤ (2*ε/3)*Matrix.traceNorm X :=
        hq.trans (mul_le_mul_of_nonneg_right hquantBudget hX)
      have ha := qdrift_fresh_reference_global_error L D r p Ks lam t n hlam.le hn hKs X
      have hH := signed_flag_hamiltonian a K sgn hlam Ks hKsrepr hpromise
      rw [hH] at ha
      have hanal : Matrix.traceNorm (referenceMixturePower p U r n X-
          TensorGate (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t) (1 : Operator r)*X*
            (TensorGate (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)
              (1 : Operator r))ᴴ) ≤ (ε/3)*Matrix.traceNorm X :=
        ha.trans (mul_le_mul_of_nonneg_right hanalytic hX)
      have hactual : tensorLeft (fairQdriftActualMap w j0 n R Ks (t*lam/(W : ℝ))) X =
          referenceMixturePower e U r n X := by
        rw [fairQdriftActualMap_reference,
          fair_bit_qdrift_actual_fresh_channel_bridge L D n R r w j0 Ks
            (t*lam/(W : ℝ)) X hW]
        exact congrArg (fun V => referenceMixturePower e V r n X) hbranch
      rw [hactual, tensorLeft_conjBranch]
      let Y := TensorGate (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t) (1 : Operator r)*X*
        (TensorGate (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t) (1 : Operator r))ᴴ
      have hsplit : referenceMixturePower e U r n X-Y =
          (referenceMixturePower e U r n X-referenceMixturePower qd U r n X)+
          (referenceMixturePower qd U r n X-referenceMixturePower p U r n X)+
          (referenceMixturePower p U r n X-Y) := by abel
      change Matrix.traceNorm (referenceMixturePower e U r n X-Y) ≤ _
      rw [hsplit]
      calc
        _ ≤ (Matrix.traceNorm (referenceMixturePower e U r n X
            -referenceMixturePower qd U r n X)+
            Matrix.traceNorm (referenceMixturePower qd U r n X
              -referenceMixturePower p U r n X))+
            Matrix.traceNorm (referenceMixturePower p U r n X-Y) :=
          (Matrix.traceNorm_add_le _ _).trans
            (add_le_add (Matrix.traceNorm_add_le _ _) le_rfl)
        _ ≤ (ε/6)*Matrix.traceNorm X+(2*ε/3)*Matrix.traceNorm X
            +(ε/3)*Matrix.traceNorm X :=
          add_le_add (add_le_add hcap hquantum) hanal
        _ = (7*ε/6)*Matrix.traceNorm X := by ring
        _ ≤ (2*ε)*Matrix.traceNorm X :=
          mul_le_mul_of_nonneg_right (by linarith only [hε]) hX
    have hdiamond := finiteDiamondDistance_le_of_uniform
      (fairQdriftActualMap w j0 n R Ks (t*lam/(W : ℝ)))
      (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)) (2*ε)
      (by positivity) huniform
    simpa only [show (2*ε)/2 = ε by ring] using hdiamond
  · intro ω
    exact fair_bit_qdrift_actual_quantum_and_classical_path_counts L D n R w j0 Ks
      (t*lam/(W : ℝ)) ω hW (fun j => (hKs j).1)

end Qatlib.Concepts.RandCompile.EffectiveInput
