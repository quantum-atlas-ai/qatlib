/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieve
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences

/-!
# Actual and ideal dihedral sieve laws

This module connects actual dihedral-qubit extraction and readout to the ideal label sieve of
[Kuperberg2005]. The invariant `FamilyList` tracks normalized record states up to a scalar of
norm one, while `negPow` aligns actual difference labels with the ideal convention.

The probability analysis represents layers by finite binary tapes, proves size-survival bounds,
and uses signed ancestor sets to control the final top bits. `dihedralSieveIdealHit` supplies
the explicit half-period hit bound at the square-root stage count.

## Main statements

* `dihedralSieveBridge`: equality of actual and ideal output distributions for reflection-hiding
  oracles.
* `dihedralSieveWrongAnswerZero`: zero probability of an incorrect parity answer.
* `dihedralSieveIdealHit`: a quantitative lower bound on half-period hit probability.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm
open Matrix
open scoped Classical BigOperators

/-- At the half-period label modulo `2^(n+1)`, the dihedral phase is minus one for odd `s.val`
and one otherwise. -/
private theorem dihedral_half_phase_succ (n : ℕ) (s : ZMod (2^(n+1))) :
    dihedralQubitPhase (2^(n+1)) s ((2^n : ℕ) : ZMod (2^(n+1))) =
      if s.val%2=1 then -1 else 1 := by
  rw [dihedralQubitPhase_eq_stdAddChar,ZMod.stdAddChar_apply,ZMod.toCircle_apply]
  have hval : (((((2^n : ℕ) : ZMod (2^(n+1)))*s).val : ℕ))=(s.val%2)*2^n := by
    rw [ZMod.val_mul]
    have hlt : 2^n < 2^(n+1) := by
      rw [pow_succ]
      have hp : 0 < 2^n := by positivity
      omega
    have hk : (((2^n : ℕ) : ZMod (2^(n+1))).val)=2^n := ZMod.val_cast_of_lt hlt
    rw [hk]
    simpa only [pow_succ,Nat.mul_comm] using! Nat.mul_mod_mul_left (2^n) s.val 2
  rw [hval]
  have hp : ((2^n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))
  have he : 2*(Real.pi : ℂ)*Complex.I*((s.val%2*2^n : ℕ) : ℂ)/((2^(n+1) : ℕ) : ℂ) =
      (Real.pi : ℂ)*Complex.I*((s.val%2 : ℕ) : ℂ) := by
    simp only [pow_succ,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [he]
  rcases Nat.mod_two_eq_zero_or_one s.val with h | h
  · rw [h]
    norm_num
  · rw [h]
    simpa only [Nat.cast_one,mul_one,if_pos rfl] using! Complex.exp_pi_mul_I

/-- The dihedral phase at label `2^(n-1)` modulo `2^n` is determined by the parity of `s.val`. -/
private theorem dihedral_half_phase (n : ℕ) (s : ZMod (2^n)) :
    dihedralQubitPhase (2^n) s ((2^(n-1) : ℕ) : ZMod (2^n)) =
      if s.val%2=1 then -1 else 1 := by
  cases n with
  | zero =>
    change ZMod 1 at s
    letI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
    have hs : s=0 := Subsingleton.elim _ _
    subst s
    simp [dihedralQubitPhase_eq_stdAddChar]
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using! dihedral_half_phase_succ n s

/-- Parity readout of the half-period dihedral qubit returns the parity of `s.val` with
probability one, as used in the sieve algorithm of [Kuperberg2005]. -/
theorem dihedralParityReadoutPure (n : ℕ) (s : ZMod (2^n)) :
    parityReadout (dihedralQubitState (2^n) s ((2^(n-1) : ℕ) : ZMod (2^n)))
      (normalized_dihedralQubitState (2^n) s ((2^(n-1) : ℕ) : ZMod (2^n))) =
        PMF.pure (decide (s.val%2=1)) := by
  have hfamily : dihedralQubitState (2^n) s ((2^(n-1) : ℕ) : ZMod (2^n)) =
      if s.val%2=1 then Minus else Plus := by
    ext b
    simp only [dihedralQubitState]
    rw [dihedral_half_phase]
    by_cases h : s.val%2=1 <;> cases b <;>
      simp [h,Minus,Plus,Hadamard]
  have hread : ApplyGate Hadamard (dihedralQubitState (2^n) s ((2^(n-1) : ℕ) : ZMod (2^n))) =
      Ket (decide (s.val%2=1)) := by
    rw [hfamily]
    by_cases h : s.val%2=1
    · rw [if_pos h,← applyGate_hadamard_ket_true,← applyGate_mul,hadamard_mul_self,applyGate_one]
      simp [h]
    · rw [if_neg h,← applyGate_hadamard_ket_false,← applyGate_mul,hadamard_mul_self,applyGate_one]
      simp [h]
  ext b
  simp only [parityReadout,bornDistribution_apply,hread,bornProb_ket,PMF.pure_apply]
  by_cases h : b=decide (s.val%2=1)
  · simp [h]
  · simp [h]

/-- Ideal readout assigns zero probability to a Boolean answer different from the parity of
`s.val`. -/
private theorem idealReadout_wrong_zero (n : ℕ) (s : ZMod (2^n)) (L : List (ZMod (2^n)))
    (b : Bool) (hb : b ≠ decide (s.val%2=1)) : idealReadout n s L (some b)=0 := by
  unfold idealReadout
  cases h : L.find? (fun r => decide (r=((2^(n-1) : ℕ) : ZMod (2^n)))) with
  | none =>
    change PMF.pure (none : Option Bool) (some b)=0
    simp [PMF.pure_apply]
  | some r =>
    have hr : r=((2^(n-1) : ℕ) : ZMod (2^n)) := by
      simpa only [decide_eq_true_eq] using! List.find?_some h
    subst r
    (try dsimp only)
    rw [dihedralParityReadoutPure,PMF.pure_map]
    simp [PMF.pure_apply,hb]

/-- The dihedral sieve assigns zero probability to an incorrect parity answer. -/
theorem dihedralSieveWrongAnswerZero (n m : ℕ) (s : ZMod (2^n)) (b : Bool)
    (hb : b ≠ decide (s.val%2=1)) : (dihedralSieveRun n m s).1 (some b)=0 := by
  unfold dihedralSieveRun
  rw [PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.2
  intro L
  rw [idealReadout_wrong_zero n s L b hb,mul_zero]

/-- The resource triple of `dihedralSieveRun` is exactly `(24*2^(3*m), 48*2^(3*m)+1,
48*2^(3*m)+1)`. -/
theorem dihedralSieveBudget (n m : ℕ) (s : ZMod (2^n)) :
    (dihedralSieveRun n m s).2=(24*2^(3*m),48*2^(3*m)+1,48*2^(3*m)+1) := rfl

/-- For an oracle hiding the reflection indexed by `s`, the label marginal of an actual record
equals `dihedralIdealRecordLaw`. -/
theorem dihedralActualRecordLabelLaw (n : ℕ) {S : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2^n) → S) (s : ZMod (2^n))
    (hf : DihedralReflectionHides (2^n) f s) :
    (dihedralActualRecord (2^n) f).map Prod.fst=dihedralIdealRecordLaw n := by
  have hmass (k : ZMod (2^n)) :
      (∑ t : Bool, ∑ z : S, ENNReal.ofReal (BornProb (dihedralRecordJoint (2^n) f) ((k,t),z))) =
      ENNReal.ofReal (1/(2^n : ℝ)) := by
    have he (t : Bool) : (∑ z : S, ENNReal.ofReal (BornProb (dihedralRecordJoint (2^n) f) ((k,t),z))) =
        ENNReal.ofReal (1/(2*(2^n : ℝ))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => bornProb_nonneg _ _),dihedralRecordBitMarginal n f s hf k t]
    simp only [he,Fintype.sum_bool]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [dihedralActualRecord,PMF.map_comp]
  change (bornDistribution (dihedralRecordJoint (2^n) f) (normalized_dihedralRecordJoint (2^n) f)).map
    (fun q : DihedralReg (2^n)×S => q.1.1)=dihedralIdealRecordLaw n
  ext k
  rw [PMF.map_apply,tsum_fintype]
  simp only [Fintype.sum_prod_type,bornDistribution_apply]
  have he (a : ZMod (2^n)) :
      (∑ t : Bool, ∑ z : S, if k=a then ENNReal.ofReal (BornProb (dihedralRecordJoint (2^n) f) ((a,t),z)) else 0) =
        if k=a then ENNReal.ofReal (1/(2^n : ℝ)) else 0 := by
    by_cases h : k=a
    · simp only [if_pos h]
      exact hmass a
    · simp [h]
  simp only [he,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [dihedralIdealRecordLaw,PMF.uniformOfFintype'_apply]
  simp

/-- The label lists of fresh actual records have the ideal fresh-record distribution for a
reflection-hiding oracle. -/
theorem dihedralFreshRecordLabels (n : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (s : ZMod (2^n)) (hf : DihedralReflectionHides (2^n) f s) (i : ℕ) :
    (actualFreshRecords (2^n) f i).map (List.map Prod.fst)=idealFreshRecords n i := by
  induction i with
  | zero =>
    change (PMF.pure ([] : List (ZMod (2^n)×NormQ))).map (List.map Prod.fst)=PMF.pure []
    rw [PMF.pure_map]
    rfl
  | succ i ih =>
    have he (q : ZMod (2^n)×S×NormQ) :
        ((actualFreshRecords (2^n) f i).map (fun L => (q.1,q.2.2)::L)).map (List.map Prod.fst)=
          (idealFreshRecords n i).map (List.cons q.1) := by
      rw [PMF.map_comp]
      have hfun : (List.map Prod.fst ∘ (fun L => (q.1,q.2.2)::L))=
          (List.cons q.1 ∘ List.map Prod.fst) := by ext L; simp
      rw [hfun,← PMF.map_comp,ih]
    rw [actualFreshRecords,PMF.map_bind]
    simp only [he]
    change (dihedralActualRecord (2^n) f).bind
      ((fun k : ZMod (2^n) => (idealFreshRecords n i).map (List.cons k)) ∘ Prod.fst)=_
    rw [← PMF.bind_map,dihedralActualRecordLabelLaw n f s hf]
    rfl

/-- The number of records consumed by the selected pairs is at most the input list length. -/
theorem sievePairWith_length_bound (n : ℕ) {α : Type} [DecidableEq α] (label : α → ZMod (2^n)) (w t : ℕ) (L : List α) :
    2*(sievePairWith n label w t L).length ≤ L.length := by
  fun_induction sievePairWith n label w t L
  · simp
  · simp only [List.length_cons]
    omega
  · rename_i r rest r' h ih
    have hm : r' ∈ rest := List.mem_of_find?_eq_some h
    have hl := List.length_erase_add_one hm
    simp only [List.length_cons]
    omega

/-- The integer formed by the `w` label bits starting at position `t`, computed as `(label
r).val / 2^t % 2^w`. -/
private def sieveWindowKey {n : ℕ} {α : Type} (label : α → ZMod (2^n)) (w t : ℕ) (r : α) : ℕ :=
  (label r).val/2^t%2^w

/-- The number of selected pairs in a window class is the input count in that class divided by
two. -/
private theorem sievePairWith_class_count (n : ℕ) {α : Type} [DecidableEq α] (label : α → ZMod (2^n)) (w t : ℕ) (L : List α) :
    ∀ u : ℕ,
    (sievePairWith n label w t L).countP (fun p => decide (sieveWindowKey label w t p.1=u)) =
      L.countP (fun r => decide (sieveWindowKey label w t r=u))/2 := by
  fun_induction sievePairWith n label w t L
  · intro u; simp
  · rename_i r rest h ih
    intro u
    by_cases hu : sieveWindowKey label w t r=u
    · have hc : rest.countP (fun a => decide (sieveWindowKey label w t a=u))=0 := by
        apply List.countP_eq_zero.2
        intro a ha
        have hn := List.find?_eq_none.1 h a ha
        simp only [decide_eq_true_eq] at hn ⊢
        change ¬ sieveWindowKey label w t r=sieveWindowKey label w t a at hn
        exact fun he => hn (hu.trans he.symm)
      rw [List.countP_cons,ih u,hc]
      simp [hu]
    · simpa [List.countP_cons,hu] using! ih u
  · rename_i r rest r' h ih
    intro u
    have hm : r' ∈ rest := List.mem_of_find?_eq_some h
    have he : sieveWindowKey label w t r=sieveWindowKey label w t r' := by
      simpa only [decide_eq_true_eq,windowAgree,sieveWindowKey] using! List.find?_some h
    by_cases hu : sieveWindowKey label w t r=u
    · have hu' : sieveWindowKey label w t r'=u := he.symm.trans hu
      have hpos : 0 < rest.countP (fun a => decide (sieveWindowKey label w t a=u)) :=
        List.countP_pos_iff.2 ⟨r',hm,by simp [hu']⟩
      rw [List.countP_cons,List.countP_cons,ih u,List.countP_erase]
      simp only [hu,hu',decide_true,if_true,hm,and_self]
      omega
    · have hu' : sieveWindowKey label w t r' ≠ u := fun he' => hu (he.trans he')
      rw [List.countP_cons,List.countP_cons,ih u,List.countP_erase]
      simp [hu,hu',hm]

/-- Summing the counts of all possible bounded keys gives the list length. -/
private theorem sieve_class_count_sum {α : Type} (key : α → ℕ) (R : ℕ)
    (hk : ∀ a, key a < R) (L : List α) :
    (∑ u ∈ Finset.range R, L.countP (fun a => decide (key a=u)))=L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.countP_cons,decide_eq_true_eq]
    rw [Finset.sum_add_distrib,ih]
    simp [Finset.sum_ite_eq,Finset.mem_range,hk a]

/-- Pairing leaves at most `2^w` records unaccounted for by twice the number of selected pairs. -/
theorem sievePairWith_pair_coverage (n : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2^n)) (w t : ℕ) (L : List α) :
    L.length ≤ 2*(sievePairWith n label w t L).length+2^w := by
  let key := sieveWindowKey label w t
  have hk (a : α) : key a < 2^w := Nat.mod_lt _ (by positivity)
  have hL := sieve_class_count_sum key (2^w) hk L
  have hP := sieve_class_count_sum (fun p : α×α => key p.1) (2^w)
    (fun p => hk p.1) (sievePairWith n label w t L)
  dsimp only [key] at hP
  simp only [sievePairWith_class_count] at hP
  rw [← hL]
  calc
    _ ≤ ∑ u ∈ Finset.range (2^w), (2*((L.countP (fun a => decide (key a=u)))/2)+1) := by
      apply Finset.sum_le_sum
      intro u _
      omega
    _ = 2*(∑ u ∈ Finset.range (2^w), L.countP (fun a => decide (key a=u))/2)+2^w := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp
    _ = _ := by rw [hP]

section G3

/-- Iteration of negation `j` times on labels modulo `2^n`. -/
def negPow (n j : ℕ) : ZMod (2 ^ n) → ZMod (2 ^ n) :=
  (fun k : ZMod (2 ^ n) => -k)^[j]

/-- One additional iteration of negation is obtained by negating the input before applying
`negPow n j`. -/
theorem negPow_succ (n j : ℕ) (k : ZMod (2 ^ n)) : negPow n (j + 1) k = negPow n j (-k) := by
  unfold negPow
  rw [Function.iterate_succ_apply]

/-- Iterated negation commutes with negation of the label. -/
theorem negPow_neg (n j : ℕ) (k : ZMod (2 ^ n)) :
    negPow n j (-k) = -(negPow n j k) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih => rw [negPow_succ, negPow_succ, neg_neg, ih, neg_neg]

/-- Applying the same iterated negation twice returns the original label. -/
theorem negPow_invol (n j : ℕ) (k : ZMod (2 ^ n)) : negPow n j (negPow n j k) = k := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
      rw [negPow_succ, negPow_succ, negPow_neg, negPow_neg, negPow_neg, neg_neg, ih]

/-- Iterated negation is injective on labels modulo `2^n`. -/
theorem negPow_injective (n j : ℕ) : Function.Injective (negPow n j) :=
  Function.LeftInverse.injective (negPow_invol n j)

/-- The label `2^(n-1)` modulo `2^n` equals its own negative. -/
private theorem clause3_neg_half (n : ℕ) :
    (-((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))) = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) := by
  cases n with
  | zero =>
      have : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
      exact Subsingleton.elim _ _
  | succ n =>
      show (-((2 ^ n : ℕ) : ZMod (2 ^ (n + 1)))) = ((2 ^ n : ℕ) : ZMod (2 ^ (n + 1)))
      have hpos : 0 < 2 ^ n := by positivity
      have hlt : (2 ^ n : ℕ) < 2 ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.mul_two]
        omega
      have hne : ((2 ^ n : ℕ) : ZMod (2 ^ (n + 1))) ≠ 0 := by
        intro h
        have hv := ZMod.val_cast_of_lt hlt
        rw [h, ZMod.val_zero] at hv
        omega
      apply ZMod.val_injective
      rw [ZMod.neg_val, if_neg hne, ZMod.val_cast_of_lt hlt]
      omega

/-- Iterated negation fixes the half-period label. -/
theorem negPow_halfPeriod (n j : ℕ) :
    negPow n j ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [negPow_succ, clause3_neg_half, ih]

/-- Multiplication by a complex scalar of norm one preserves normalization of a quantum state. -/
private theorem clause3_unit_norm {I : Type*} [Fintype I] {u : ℂ} (hu : ‖u‖ = 1)
    {ξ : QState I} (hξ : Normalized ξ) : Normalized (u • ξ) := by
  unfold Normalized
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hu, one_mul]
  exact hξ

/-- Scaling a state by `c` multiplies every measurement-event probability by `‖c‖^2`. -/
private theorem clause3_measureProb_smul {I : Type*} [Fintype I] (c : ℂ) (ψ : QState I)
    (S : Finset I) : MeasureProb (c • ψ) S = ‖c‖ ^ 2 * MeasureProb ψ S := by
  simp only [MeasureProb, BornProb, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum]

/-- For a nonzero scalar and positive total measurement probability, post-measurement
normalization preserves the scalar's phase `c / ‖c‖`. -/
private theorem clause3_postMeasure_smul {I : Type*} [Fintype I] [DecidableEq I]
    {c : ℂ} (hc : c ≠ 0) {β : QState I} (hm : 0 < MeasureProb β Finset.univ) :
    PostMeasure (c • β) Finset.univ = (c / ‖c‖) • PostMeasure β Finset.univ := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hsqrtm : 0 < Real.sqrt (MeasureProb β Finset.univ) := Real.sqrt_pos_of_pos hm
  have hcol : ∀ i, Collapse (c • β) Finset.univ i = c * Collapse β Finset.univ i := by
    intro i
    rw [collapse_apply, collapse_apply]
    split_ifs <;> simp [Pi.smul_apply, smul_eq_mul]
  have hsqrt : Real.sqrt (‖c‖ ^ 2 * MeasureProb β Finset.univ)
      = ‖c‖ * Real.sqrt (MeasureProb β Finset.univ) := by
    rw [Real.sqrt_mul (pow_nonneg (norm_nonneg c) 2), Real.sqrt_sq (norm_nonneg c)]
  funext i
  simp only [PostMeasure, clause3_measureProb_smul, hcol, Pi.smul_apply, smul_eq_mul, hsqrt]
  field_simp
  push_cast
  ring

/-- The conditional state of a nonzero scalar multiple is the normalized original state
multiplied by `c / ‖c‖`, provided its total measurement probability is positive. -/
private theorem clause3_conditionalState_smul {I : Type*} [Fintype I] [DecidableEq I]
    {c : ℂ} (hc : c ≠ 0) {β : QState I} (hm : 0 < MeasureProb β Finset.univ) :
    ConditionalState (c • β) = some ((c / ‖c‖) • PostMeasure β Finset.univ) := by
  unfold ConditionalState
  rw [clause3_measureProb_smul, if_pos (mul_pos (pow_pos (norm_pos_iff.mpr hc) 2) hm),
    clause3_postMeasure_smul hc hm]

/-- Multiplication by a scalar of norm one transports the actual normalized record state by the
same scalar when the original total measurement probability is positive. -/
private theorem clause3_recordState_smul (c : ℂ) (hc : ‖c‖ = 1) (β : QState Bool)
    (hβ : 0 < MeasureProb β Finset.univ) (ξ : QState Bool) (hξ : Normalized ξ)
    (h : actualRecordState β = ⟨ξ, hξ⟩) :
    actualRecordState (c • β) = ⟨c • ξ, clause3_unit_norm hc hξ⟩ := by
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0] at hc; norm_num at hc
  have hpm : PostMeasure β Finset.univ = ξ := by
    have hsome : ConditionalState β = some (PostMeasure β Finset.univ) := by
      unfold ConditionalState; rw [if_pos hβ]
    have h2 := actualRecordState_eq_of_some β (PostMeasure β Finset.univ)
      (normalized_postMeasure hβ) hsome
    rw [h] at h2
    exact (Subtype.ext_iff.mp h2).symm
  have hcond' : ConditionalState (c • β) = some (c • ξ) := by
    have h3 := clause3_conditionalState_smul hcne hβ
    rw [h3, hpm, show c / ‖c‖ = c from by rw [hc]; norm_num]
  exact actualRecordState_eq_of_some _ _ (clause3_unit_norm hc hξ) hcond'

/-- The property that every record state is a scalar of norm one times the dihedral qubit state
associated with its label and hidden shift `s`. -/
def FamilyList (n : ℕ) (s : ZMod (2 ^ n)) (A : List (ZMod (2 ^ n) × NormQ)) : Prop :=
  ∀ r ∈ A, ∃ u : ℂ, ‖u‖ = 1 ∧ r.2.1 = u • dihedralQubitState (2 ^ n) s r.1

/-- Prepending a record from the same dihedral state family preserves `FamilyList`. -/
theorem FamilyList.cons {n : ℕ} {s : ZMod (2 ^ n)} {r : ZMod (2 ^ n) × NormQ}
    {A : List (ZMod (2 ^ n) × NormQ)} (hr : ∃ u : ℂ, ‖u‖ = 1 ∧ r.2.1
      = u • dihedralQubitState (2 ^ n) s r.1) (hA : FamilyList n s A) :
    FamilyList n s (r :: A) := by
  intro x hx
  rcases List.mem_cons.1 hx with h | h
  · exact h ▸ hr
  · exact hA x h

/-- A scalar of norm one leaves the extended-nonnegative Born probability of each outcome
unchanged. -/
private theorem clause3_born_smul {I : Type*} [Fintype I] {c : ℂ} (hc : ‖c‖ = 1)
    (χ : QState I) (x : I) :
    ENNReal.ofReal (BornProb (c • χ) x) = ENNReal.ofReal (BornProb χ x) := by
  simp only [BornProb, Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

/-- A scalar of norm one leaves the Born distribution unchanged. -/
private theorem clause3_bornDistribution_smul {I : Type*} [Fintype I] {c : ℂ} (hc : ‖c‖ = 1)
    {χ : QState I} (hχ : Normalized χ) :
    bornDistribution (c • χ) (clause3_unit_norm hc hχ) = bornDistribution χ hχ := by
  ext x
  rw [bornDistribution_apply, bornDistribution_apply, clause3_born_smul hc χ x]

/-- Matrix gate application commutes with complex scalar multiplication of a state. -/
private theorem clause3_applyGate_smul {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (c : ℂ) (χ : QState I) :
    ApplyGate U (c • χ) = c • ApplyGate U χ := by
  funext i
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [eq_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The product of two complex scalars of norm one has norm one. -/
private theorem clause3_norm_mul {u u' : ℂ} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) : ‖u * u'‖ = 1 := by
  rw [norm_mul, hu, hu']; norm_num

/-- The extraction bit has the distribution of the second computational-basis outcome after
applying CNOT to the tensor product of the input states. -/
private theorem clause3_extraction_fst_eq (ψ φ : QState Bool) (hψ : Normalized ψ)
    (hφ : Normalized φ) :
    (dihedralExtraction ψ φ hψ hφ).map Prod.fst
      = (bornDistribution (ApplyGate CNOT (TensorState ψ φ))
          (normalized_applyGate cnot_unitary (normalized_tensorState hψ hφ))).map Prod.snd := by
  simp only [dihedralExtraction, PMF.map_comp]
  rfl

/-- Extraction from two dihedral qubits, including arbitrary scalar phases of norm one, yields a
uniform Boolean outcome. -/
theorem dihedralExtraction_fair (N : ℕ) [NeZero N] (s k ℓ : ZMod N) (u u' : ℂ)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) :
    (dihedralExtraction (u • dihedralQubitState N s k) (u' • dihedralQubitState N s ℓ)
        (clause3_unit_norm hu (normalized_dihedralQubitState N s k))
        (clause3_unit_norm hu' (normalized_dihedralQubitState N s ℓ))).map Prod.fst
      = PMF.uniformOfFintype' Bool := by
  have hc : ‖u * u'‖ = 1 := clause3_norm_mul hu hu'
  have hgate : ApplyGate CNOT (TensorState (u • dihedralQubitState N s k)
        (u' • dihedralQubitState N s ℓ))
      = (u * u') • ApplyGate CNOT (TensorState (dihedralQubitState N s k)
          (dihedralQubitState N s ℓ)) := by
    have htens : TensorState (u • dihedralQubitState N s k)
        (u' • dihedralQubitState N s ℓ)
        = (u * u') • TensorState (dihedralQubitState N s k)
          (dihedralQubitState N s ℓ) := by
      funext p; simp only [TensorState, Pi.smul_apply, smul_eq_mul]; ring
    rw [htens, clause3_applyGate_smul]
  have hP : bornDistribution
        (ApplyGate CNOT (TensorState (u • dihedralQubitState N s k)
          (u' • dihedralQubitState N s ℓ)))
        (normalized_applyGate cnot_unitary (normalized_tensorState
          (clause3_unit_norm hu (normalized_dihedralQubitState N s k))
          (clause3_unit_norm hu' (normalized_dihedralQubitState N s ℓ))))
      = bornDistribution
        (ApplyGate CNOT (TensorState (dihedralQubitState N s k)
          (dihedralQubitState N s ℓ)))
        (normalized_applyGate cnot_unitary (normalized_tensorState
          (normalized_dihedralQubitState N s k)
          (normalized_dihedralQubitState N s ℓ))) := by
    ext x
    rw [bornDistribution_apply, bornDistribution_apply, hgate, clause3_born_smul hc _ x]
  rw [clause3_extraction_fst_eq, hP, ← clause3_extraction_fst_eq (dihedralQubitState N s k)
      (dihedralQubitState N s ℓ) (normalized_dihedralQubitState N s k)
      (normalized_dihedralQubitState N s ℓ)]
  obtain ⟨xiPlus, xiMinus, hPlus, hMinus, _uPlus, _uMinus, _hup, _hum, _hxip, _hxim, hlaw⟩ :=
    dihedralExtractionLaw N s k ℓ
  have hEr (b' : Bool) (r : NormQ) :
      (dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
        (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s ℓ)) (b', r)
        = if (b' = false ∧ r.1 = xiPlus) ∨ (b' = true ∧ r.1 = xiMinus)
          then 1 / 2 else 0 := by
    obtain ⟨ξ, hξ⟩ := r
    simpa using! hlaw b' ξ hξ
  ext b
  have hR : (PMF.uniformOfFintype' Bool) b = 1 / 2 := by
    rw [PMF.uniformOfFintype'_apply]; norm_num
  rw [PMF.map_apply, hR]
  set E : PMF (Bool × NormQ) :=
    dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
      (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s ℓ) with hEdef
  cases b with
  | false =>
      have hmain : @ite ENNReal (false = ((false, ⟨xiPlus, hPlus⟩) : Bool × NormQ).1)
          (Classical.propDecidable _) (E (false, ⟨xiPlus, hPlus⟩)) 0 = 1 / 2 := by
        rw [if_pos rfl, hEr false ⟨xiPlus, hPlus⟩, if_pos (Or.inl ⟨rfl, rfl⟩)]
      have hrest : ∀ q : Bool × NormQ, q ≠ ((false, ⟨xiPlus, hPlus⟩) : Bool × NormQ) →
          @ite ENNReal (false = q.1) (Classical.propDecidable (false = q.1)) (E q) 0 = 0 := by
        intro q hq
        have hqe : q = (q.1, q.2) := (Prod.eta q).symm
        by_cases hb : q.1 = false
        · rw [hqe, hb, if_pos rfl, hEr false q.2, if_neg]
          intro hcond
          rcases hcond with ⟨_, he⟩ | ⟨hf, _⟩
          · exact hq (Prod.ext hb (Subtype.ext he))
          · exact Bool.noConfusion hf
        · rw [if_neg (fun h => hb h.symm)]
      exact (tsum_eq_single ((false, ⟨xiPlus, hPlus⟩) : Bool × NormQ) hrest).trans hmain
  | true =>
      have hmain : @ite ENNReal (true = ((true, ⟨xiMinus, hMinus⟩) : Bool × NormQ).1)
          (Classical.propDecidable _) (E (true, ⟨xiMinus, hMinus⟩)) 0 = 1 / 2 := by
        rw [if_pos rfl, hEr true ⟨xiMinus, hMinus⟩, if_pos (Or.inr ⟨rfl, rfl⟩)]
      have hrest : ∀ q : Bool × NormQ, q ≠ ((true, ⟨xiMinus, hMinus⟩) : Bool × NormQ) →
          @ite ENNReal (true = q.1) (Classical.propDecidable (true = q.1)) (E q) 0 = 0 := by
        intro q hq
        have hqe : q = (q.1, q.2) := (Prod.eta q).symm
        by_cases hb : q.1 = true
        · rw [hqe, hb, if_pos rfl, hEr true q.2, if_neg]
          intro hcond
          rcases hcond with ⟨hf, _⟩ | ⟨_, he⟩
          · exact Bool.noConfusion hf
          · exact hq (Prod.ext hb (Subtype.ext he))
        · rw [if_neg (fun h => hb h.symm)]
      exact (tsum_eq_single ((true, ⟨xiMinus, hMinus⟩) : Bool × NormQ) hrest).trans hmain

/-- The mass of an input point is bounded by the mass of its image under a mapped probability
mass function. -/
private theorem clause3_map_single_le {α β : Type} (p : PMF α) (f : α → β) (x : α) :
    p x ≤ (p.map f) (f x) := by
  classical
  calc p x = (if f x = f x then p x else 0) := (if_pos rfl).symm
    _ = (fun a => if f x = f a then p a else 0) x := rfl
    _ ≤ ∑' a, (fun a => if f x = f a then p a else 0) a := ENNReal.le_tsum (f := fun a => if f x = f a then p a else 0) x
    _ = (p.map f) (f x) := (PMF.map_apply f p (f x)).symm

/-- A point of positive mapped probability has a preimage of positive probability. -/
private theorem clause3_map_pos_witness {α β : Type} (p : PMF α) (f : α → β) (y : β)
    (hy : 0 < (p.map f) y) : ∃ x : α, f x = y ∧ 0 < p x := by
  classical
  by_contra hcon
  push Not at hcon
  have hterm : ∀ x : α, (if y = f x then p x else 0) = 0 := by
    intro x
    by_cases h : y = f x
    · rw [if_pos h]
      exact le_antisymm (hcon x (by rw [h])) (by simp)
    · rw [if_neg h]
  rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 hterm] at hy
  simp at hy

/-- A positive outcome of binding a distribution to a mapped independent distribution has a pair
of positive-probability input witnesses. -/
private theorem clause3_bind_map_pos_witness {α β γ : Type} (p : PMF α) (q : PMF β)
    (g : α → β → γ) (z : γ) (hz : 0 < (p.bind fun a => q.map (g a)) z) :
    ∃ a b, g a b = z ∧ 0 < p a ∧ 0 < q b := by
  classical
  by_contra hcon
  push Not at hcon
  have hterm : ∀ a : α, (p a * (q.map (g a)) z) = 0 := by
    intro a
    by_cases hpa : 0 < p a
    · have hinner : (q.map (g a)) z = 0 := by
        rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 (fun b => by
          by_cases h : z = g a b
          · rw [if_pos h]
            refine le_antisymm (hcon a b (by rw [h]) hpa) (by simp)
          · rw [if_neg h])]
      rw [hinner, mul_zero]
    · have hpz : p a = 0 := le_antisymm (not_lt.1 hpa) (by simp)
      rw [hpz, zero_mul]
  rw [PMF.bind_apply, ENNReal.tsum_eq_zero.2 hterm] at hz
  simp at hz

/-- Post-measurement normalization over the whole basis fixes an already normalized state. -/
private theorem clause3_postMeasure_self {I : Type*} [Fintype I] [DecidableEq I] {ψ : QState I}
    (hψ : Normalized ψ) : PostMeasure ψ Finset.univ = ψ := by
  have hm : MeasureProb ψ Finset.univ = 1 := by
    unfold MeasureProb BornProb
    simpa using! hψ
  funext i
  simp only [PostMeasure, collapse_apply, if_pos (Finset.mem_univ i), hm]
  simp

/-- Every positive-probability extraction record is, up to a scalar of norm one, the dihedral
qubit with label `k - ℓ` for a true outcome and `k + ℓ` otherwise. -/
theorem dihedralExtraction_family (N : ℕ) [NeZero N] (s k ℓ : ZMod N) (u u' : ℂ)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (q : Bool × NormQ)
    (hq : 0 < (dihedralExtraction (u • dihedralQubitState N s k)
        (u' • dihedralQubitState N s ℓ)
        (clause3_unit_norm hu (normalized_dihedralQubitState N s k))
        (clause3_unit_norm hu' (normalized_dihedralQubitState N s ℓ))) q) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      q.2.1 = w • dihedralQubitState N s (if q.1 then k - ℓ else k + ℓ) := by
  classical
  have hc : ‖u * u'‖ = 1 := clause3_norm_mul hu hu'
  have hcne : u * u' ≠ 0 := by
    intro h0
    rw [h0] at hc
    exact absurd hc (by simp)
  obtain ⟨xiPlus, xiMinus, hPlus, hMinus, uPlus, uMinus, hup, hum, hxip, hxim, hlaw⟩ :=
    dihedralExtractionLaw N s k ℓ
  set χ : QState (Bool × Bool) := ApplyGate CNOT
      (TensorState (dihedralQubitState N s k) (dihedralQubitState N s ℓ)) with hχdef
  have hnormχ : Normalized χ := normalized_applyGate cnot_unitary
    (normalized_tensorState (normalized_dihedralQubitState N s k)
      (normalized_dihedralQubitState N s ℓ))
  have hgate : ApplyGate CNOT (TensorState (u • dihedralQubitState N s k)
        (u' • dihedralQubitState N s ℓ)) = (u * u') • χ := by
    have htens : TensorState (u • dihedralQubitState N s k)
        (u' • dihedralQubitState N s ℓ)
        = (u * u') • TensorState (dihedralQubitState N s k)
          (dihedralQubitState N s ℓ) := by
      funext p; simp only [TensorState, Pi.smul_apply, smul_eq_mul]; ring
    rw [htens, clause3_applyGate_smul]
  have hunfold : (dihedralExtraction (u • dihedralQubitState N s k)
      (u' • dihedralQubitState N s ℓ)
      (clause3_unit_norm hu (normalized_dihedralQubitState N s k))
      (clause3_unit_norm hu' (normalized_dihedralQubitState N s ℓ)))
      = (bornDistribution (ApplyGate CNOT (TensorState (u • dihedralQubitState N s k)
          (u' • dihedralQubitState N s ℓ)))
        (normalized_applyGate cnot_unitary (normalized_tensorState
          (clause3_unit_norm hu (normalized_dihedralQubitState N s k))
          (clause3_unit_norm hu' (normalized_dihedralQubitState N s ℓ))))).map
        (fun w : Bool × Bool => (w.2, actualRecordState
          (fun a => ApplyGate CNOT (TensorState (u • dihedralQubitState N s k)
            (u' • dihedralQubitState N s ℓ)) (a, w.2)))) := rfl
  rw [hunfold] at hq
  obtain ⟨q₀, hq₀eq, hq₀mass⟩ := clause3_map_pos_witness _ _ q hq
  have hq₀eq' : q = (q₀.2, actualRecordState
      (fun a => ApplyGate CNOT (TensorState (u • dihedralQubitState N s k)
        (u' • dihedralQubitState N s ℓ)) (a, q₀.2))) := hq₀eq.symm

  have hbaseMass : 0 < (bornDistribution χ hnormχ) q₀ := by
    have h := hq₀mass
    rw [bornDistribution_apply, hgate, clause3_born_smul hc χ q₀] at h
    rw [bornDistribution_apply]
    exact h

  have hbranchmass : 0 < MeasureProb (fun a => χ (a, q₀.2)) Finset.univ := by
    have hle := Finset.single_le_sum (fun (i : Bool) (_ : i ∈ Finset.univ) =>
        bornProb_nonneg (fun a => χ (a, q₀.2)) i) (Finset.mem_univ q₀.1)
    have hbornbase : 0 < BornProb χ q₀ := by
      have hn : χ q₀ ≠ 0 := by
        intro h0
        rw [bornDistribution_apply] at hbaseMass
        unfold BornProb at hbaseMass
        rw [h0] at hbaseMass
        simp at hbaseMass
      unfold BornProb
      exact pow_pos (norm_pos_iff.mpr hn) 2
    exact lt_of_lt_of_le hbornbase hle

  have hcond : ConditionalState (fun a => χ (a, q₀.2))
      = some (PostMeasure (fun a => χ (a, q₀.2)) Finset.univ) := by
    unfold ConditionalState
    rw [if_pos hbranchmass]
  have harss : actualRecordState (fun a => χ (a, q₀.2))
      = ⟨PostMeasure (fun a => χ (a, q₀.2)) Finset.univ,
        normalized_postMeasure hbranchmass⟩ :=
    actualRecordState_eq_of_some _ _ (normalized_postMeasure hbranchmass) hcond

  have hβsmul : (fun a => ApplyGate CNOT (TensorState (u • dihedralQubitState N s k)
        (u' • dihedralQubitState N s ℓ)) (a, q₀.2))
      = (u * u') • (fun a => χ (a, q₀.2)) := by
    funext a
    rw [hgate]
    simp
  have hcond' : ConditionalState ((u * u') • (fun a => χ (a, q₀.2)))
      = some ((u * u') • PostMeasure (fun a => χ (a, q₀.2)) Finset.univ) := by
    rw [clause3_conditionalState_smul hcne hbranchmass, show u * u' / ‖u * u'‖ = u * u' from by
      rw [hc]; norm_num]
  have harss' : actualRecordState (fun a => ApplyGate CNOT
        (TensorState (u • dihedralQubitState N s k)
          (u' • dihedralQubitState N s ℓ)) (a, q₀.2))
      = ⟨(u * u') • PostMeasure (fun a => χ (a, q₀.2)) Finset.univ,
        clause3_unit_norm hc (normalized_postMeasure hbranchmass)⟩ := by
    rw [hβsmul]
    exact actualRecordState_eq_of_some _ _ (clause3_unit_norm hc
      (normalized_postMeasure hbranchmass)) hcond'
  rw [harss'] at hq₀eq'
  have hq1 : q.1 = q₀.2 := congrArg Prod.fst hq₀eq'
  have hq2 : q.2 = ⟨(u * u') • PostMeasure (fun a => χ (a, q₀.2)) Finset.univ,
      clause3_unit_norm hc (normalized_postMeasure hbranchmass)⟩ := congrArg Prod.snd hq₀eq'
  have hq21 : q.2.1
      = (u * u') • PostMeasure (fun a => χ (a, q₀.2)) Finset.univ := by
    rw [hq2]

  have hbasepos : 0 < (dihedralExtraction (dihedralQubitState N s k)
      (dihedralQubitState N s ℓ) (normalized_dihedralQubitState N s k)
      (normalized_dihedralQubitState N s ℓ)) (q₀.2,
        ⟨PostMeasure (fun a => χ (a, q₀.2)) Finset.univ,
          normalized_postMeasure hbranchmass⟩) := by
    have hunfold' : (dihedralExtraction (dihedralQubitState N s k)
        (dihedralQubitState N s ℓ) (normalized_dihedralQubitState N s k)
        (normalized_dihedralQubitState N s ℓ))
        = (bornDistribution χ hnormχ).map
          (fun w : Bool × Bool => (w.2, actualRecordState (fun a => χ (a, w.2)))) := rfl
    rw [hunfold']
    have hle := clause3_map_single_le (bornDistribution χ hnormχ)
      (fun w : Bool × Bool => (w.2, actualRecordState (fun a => χ (a, w.2)))) q₀
    have hle' : (bornDistribution χ hnormχ) q₀
        ≤ ((bornDistribution χ hnormχ).map
            (fun w : Bool × Bool => (w.2, actualRecordState (fun a => χ (a, w.2)))))
            (q₀.2, actualRecordState (fun a => χ (a, q₀.2))) := hle
    rw [harss] at hle'
    exact lt_of_lt_of_le hbaseMass hle'
  rw [hlaw q₀.2 (PostMeasure (fun a => χ (a, q₀.2)) Finset.univ)
    (normalized_postMeasure hbranchmass)] at hbasepos
  by_cases hsel : (q₀.2 = false ∧
      PostMeasure (fun a => χ (a, q₀.2)) Finset.univ = xiPlus) ∨
    (q₀.2 = true ∧ PostMeasure (fun a => χ (a, q₀.2)) Finset.univ = xiMinus)
  · rw [if_pos hsel] at hbasepos
    rcases hsel with ⟨hq₂f, heq⟩ | ⟨hq₂t, heq⟩
    · refine ⟨(u * u') * uPlus, by
        rw [norm_mul, clause3_norm_mul hu hu', hup]; norm_num, ?_⟩
      rw [hq1, hq₂f, if_neg (by decide)]
      rw [hq21, heq, hxip, smul_smul]
    · refine ⟨(u * u') * uMinus, by
        rw [norm_mul, clause3_norm_mul hu hu', hum]; norm_num, ?_⟩
      rw [hq1, hq₂t, if_pos rfl]
      rw [hq21, heq, hxim, smul_smul]
  · rw [if_neg hsel] at hbasepos
    simp at hbasepos

/-- Every positive-probability actual record of a reflection-hiding oracle has its label's
dihedral qubit state up to a scalar of norm one. -/
theorem dihedralActualRecord_family (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s)
    (r : ZMod (2 ^ n) × S × NormQ)
    (hr : 0 < (dihedralActualRecord (2 ^ n) f) r) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ r.2.2.1 = u • dihedralQubitState (2 ^ n) s r.1 := by
  classical
  have hunfold : (dihedralActualRecord (2 ^ n) f)
      = (bornDistribution (dihedralRecordJoint (2 ^ n) f)
          (normalized_dihedralRecordJoint (2 ^ n) f)).map
        (fun w : DihedralReg (2 ^ n) × S => (w.1.1, w.2, actualRecordState
          (fun t => dihedralRecordJoint (2 ^ n) f ((w.1.1, t), w.2)))) := rfl
  rw [hunfold] at hr
  obtain ⟨q₀, hq₀eq, hq₀mass⟩ := clause3_map_pos_witness _ _ r hr
  have hq₀eq' : r = (q₀.1.1, q₀.2, actualRecordState
      (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2))) := hq₀eq.symm
  rw [bornDistribution_apply] at hq₀mass
  have hborn : 0 < BornProb (dihedralRecordJoint (2 ^ n) f) q₀ :=
    ENNReal.ofReal_pos.1 hq₀mass

  obtain ⟨γ, _hγ, hγ⟩ := (dihedralRecordLaw n f s hf).2.2 q₀.1.1
  have hbranch : (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2))
      = γ q₀.2 • dihedralQubitState (2 ^ n) s q₀.1.1 := by
    funext t
    rw [Pi.smul_apply, smul_eq_mul]
    exact hγ t q₀.2
  have hvalq : dihedralRecordJoint (2 ^ n) f q₀
      = γ q₀.2 * dihedralQubitState (2 ^ n) s q₀.1.1 q₀.1.2 := hγ q₀.1.2 q₀.2
  have hγne : γ q₀.2 ≠ 0 := by
    intro h0
    unfold BornProb at hborn
    rw [hvalq, h0] at hborn
    simp at hborn
  have hnormunit : ‖γ q₀.2 / ‖γ q₀.2‖‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hγne)]
  have hbranchmass : 0 < MeasureProb
      (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2)) Finset.univ := by
    have hle := Finset.single_le_sum (fun (i : Bool) (_ : i ∈ Finset.univ) =>
        bornProb_nonneg (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2)) i)
      (Finset.mem_univ q₀.1.2)
    have hval : BornProb (dihedralRecordJoint (2 ^ n) f) q₀
        = ‖γ q₀.2‖ ^ 2 * (1 / 2 : ℝ) := by
      unfold BornProb
      rw [hvalq, norm_mul, mul_pow,
        show ‖dihedralQubitState (2 ^ n) s q₀.1.1 q₀.1.2‖ ^ 2 = 1 / 2 from
          dihedralQubitState_born (2 ^ n) s q₀.1.1 q₀.1.2]
    have hposhalf : 0 < ‖γ q₀.2‖ ^ 2 * (1 / 2 : ℝ) := by
      refine mul_pos (pow_pos (norm_pos_iff.mpr hγne) 2) (by norm_num)
    have hgoal : 0 < BornProb (dihedralRecordJoint (2 ^ n) f) q₀ := by
      rw [hval]
      exact hposhalf
    exact lt_of_lt_of_le hgoal hle

  have hcond : ConditionalState
      (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2))
      = some (PostMeasure
          (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2)) Finset.univ) := by
    unfold ConditionalState
    rw [if_pos hbranchmass]
  have hψmass : 0 < MeasureProb (dihedralQubitState (2 ^ n) s q₀.1.1) Finset.univ := by
    have hm : MeasureProb (dihedralQubitState (2 ^ n) s q₀.1.1) Finset.univ = 1 := by
      have hψ := normalized_dihedralQubitState (2 ^ n) s q₀.1.1
      unfold Normalized at hψ
      unfold MeasureProb BornProb
      simpa using! hψ
    rw [hm]
    norm_num
  have hpm : PostMeasure
      (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2)) Finset.univ
      = (γ q₀.2 / ‖γ q₀.2‖) • dihedralQubitState (2 ^ n) s q₀.1.1 := by
    rw [hbranch, clause3_postMeasure_smul hγne hψmass,
      clause3_postMeasure_self (normalized_dihedralQubitState (2 ^ n) s q₀.1.1)]
  have harss : actualRecordState
      (fun t => dihedralRecordJoint (2 ^ n) f ((q₀.1.1, t), q₀.2))
      = ⟨(γ q₀.2 / ‖γ q₀.2‖) • dihedralQubitState (2 ^ n) s q₀.1.1,
        clause3_unit_norm hnormunit (normalized_dihedralQubitState (2 ^ n) s q₀.1.1)⟩ := by
    refine actualRecordState_eq_of_some _ _ (clause3_unit_norm hnormunit
      (normalized_dihedralQubitState (2 ^ n) s q₀.1.1)) ?_
    rw [hcond, hpm]
  rw [harss] at hq₀eq'
  refine ⟨γ q₀.2 / ‖γ q₀.2‖, hnormunit, ?_⟩
  have h1 : r.1 = q₀.1.1 := congrArg Prod.fst hq₀eq'
  have h2 : r.2.2 = ⟨(γ q₀.2 / ‖γ q₀.2‖) • dihedralQubitState (2 ^ n) s q₀.1.1, _⟩ :=
    congrArg (fun x => x.2.2) hq₀eq'
  rw [h1]
  rw [show r.2.2.1 = (γ q₀.2 / ‖γ q₀.2‖) • dihedralQubitState (2 ^ n) s q₀.1.1 from by
    rw [h2]]

/-- Every positive-probability list of fresh records from a reflection-hiding oracle satisfies
`FamilyList`. -/
theorem actualFreshRecords_family (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) (i : ℕ)
    (L : List (ZMod (2 ^ n) × NormQ))
    (hL : 0 < (actualFreshRecords (2 ^ n) f i) L) : FamilyList n s L := by
  classical
  induction i generalizing L with
  | zero =>
      change 0 < (PMF.pure ([] : List (ZMod (2 ^ n) × NormQ))) L at hL
      rw [PMF.pure_apply] at hL
      by_cases hEq : L = []
      · subst hEq
        intro r hr
        exact absurd hr (by simp)
      · rw [if_neg hEq] at hL
        simp at hL
  | succ i ih =>
      rw [actualFreshRecords] at hL
      obtain ⟨q, L', _hmap, hq, hL'⟩ := clause3_bind_map_pos_witness
        (dihedralActualRecord (2 ^ n) f) (actualFreshRecords (2 ^ n) f i)
        (fun q L' => (q.1, q.2.2) :: L') L hL
      have hLcons : L = (q.1, q.2.2) :: L' := _hmap.symm
      subst hLcons
      obtain ⟨u, hu, hufam⟩ := dihedralActualRecord_family n f s hf q hq
      exact FamilyList.cons ⟨u, hu, hufam⟩ (ih L' hL')

/-- Iterated negation of `k - ℓ` at step `j+1` equals the difference of the step-`j` images in
reversed order. -/
theorem negPow_sub_succ (n j : ℕ) (k ℓ : ZMod (2 ^ n)) :
    negPow n (j + 1) (k - ℓ) = negPow n j ℓ - negPow n j k := by
  induction j generalizing k ℓ with
  | zero =>
      show -(k - ℓ) = ℓ - k
      rw [neg_sub]
  | succ j ih =>
      rw [negPow_succ, neg_sub, ih, negPow_succ, negPow_succ, negPow_neg, negPow_neg,
        neg_sub_neg]

/-- If `m` is positive and divides `M`, subtraction from `M` preserves and reflects equality of
residues modulo `m` for numbers at most `M`. -/
private theorem clause3_mod_sub_iff (M m a b : ℕ) (hm : 0 < m) (hdvd : m ∣ M)
    (ha : a ≤ M) (hb : b ≤ M) :
    (M - a) % m = (M - b) % m ↔ a % m = b % m := by
  have hMm : M % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hshape : ∀ x : ℕ, x ≤ M →
      (x % m = 0 ∧ (M - x) % m = 0) ∨ x % m + (M - x) % m = m := by
    intro x hx
    have hsum : (x % m + (M - x) % m) % m = 0 := by
      have h1 : (x % m + (M - x) % m) % m = ((x + (M - x)) % m) % m := by
        conv_rhs => rw [Nat.add_mod x (M - x) m, Nat.mod_mod_of_dvd _ (Nat.dvd_refl m)]
      rw [h1, show x + (M - x) = M from by omega, hMm, Nat.zero_mod]
    obtain ⟨q, hq⟩ : ∃ q, x % m + (M - x) % m = m * q := by
      refine ⟨(x % m + (M - x) % m) / m, ?_⟩
      exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hsum)).symm
    have hAm : x % m < m := Nat.mod_lt x hm
    have hXm : (M - x) % m < m := Nat.mod_lt _ hm
    have hq2 : q < 2 := by
      have hlt : m * q < m * 2 := by
        calc m * q = x % m + (M - x) % m := hq.symm
          _ < m + m := by omega
          _ = m * 2 := (Nat.mul_two m).symm
      exact Nat.lt_of_mul_lt_mul_left hlt
    rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
    · left
      omega
    · right
      omega
  set A := a % m with hA
  set B := b % m with hB
  set X := (M - a) % m with hX
  set Y := (M - b) % m with hY
  have hsa := hshape a ha
  have hsb := hshape b hb
  have hAm : A < m := Nat.mod_lt a hm
  have hBm : B < m := Nat.mod_lt b hm
  have hXm : X < m := Nat.mod_lt _ hm
  have hYm : Y < m := Nat.mod_lt _ hm
  constructor
  · intro h
    rcases hsa with ⟨ha0, hX0⟩ | haS <;>
      rcases hsb with ⟨hb0, hY0⟩ | hbS <;> omega
  · intro h
    rcases hsa with ⟨ha0, hX0⟩ | haS <;>
      rcases hsb with ⟨hb0, hY0⟩ | hbS <;> omega

/-- Negating a label preserves vanishing of its lowest `t` bits when `t ≤ n`. -/
private theorem clause3_neg_zeroBits (n t : ℕ) (ht : t ≤ n) (k : ZMod (2 ^ n))
    (hk : k.val % 2 ^ t = 0) : (-k).val % 2 ^ t = 0 := by
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · rw [ZMod.neg_val, if_neg hk0, Nat.mod_eq_zero_of_dvd]
    exact Nat.dvd_sub (Nat.pow_dvd_pow _ ht) (Nat.dvd_of_mod_eq_zero hk)

/-- For a label with `t` zero low bits, the quotient of its negative by `2^t` is the modular
negative of the original quotient modulo `2^(n-t)`. -/
private theorem clause3_neg_div (n t : ℕ) (ht : t ≤ n) (k : ZMod (2 ^ n))
    (hk : k.val % 2 ^ t = 0) :
    (-k).val / 2 ^ t = (2 ^ (n - t) - k.val / 2 ^ t) % 2 ^ (n - t) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have hp : (0:ℕ) < 2 ^ t := by positivity
    have hκ : k.val = (k.val / 2 ^ t) * 2 ^ t := by
      have h := Nat.div_add_mod k.val (2 ^ t)
      rw [hk, add_zero] at h
      rw [Nat.mul_comm]
      exact h.symm
    have hκlt : k.val / 2 ^ t < 2 ^ (n - t) := by
      rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, Nat.sub_add_cancel ht]
      exact ZMod.val_lt k
    have hκpos : 0 < k.val / 2 ^ t := by
      by_contra hc0
      have hz : k.val / 2 ^ t = 0 :=
        le_antisymm (not_lt.1 hc0) (Nat.zero_le _)
      apply hk0
      apply ZMod.val_injective
      rw [hκ, hz, Nat.zero_mul, ZMod.val_zero]
    set v := k.val with hv
    have hsub : 2 ^ n - v = (2 ^ (n - t) - v / 2 ^ t) * 2 ^ t := by
      rw [hκ, Nat.mul_div_cancel _ hp,
        show (2 ^ n : ℕ) = 2 ^ (n - t) * 2 ^ t from by
          rw [← pow_add, Nat.sub_add_cancel ht]]
      exact (Nat.sub_mul (2 ^ (n - t)) (v / 2 ^ t) (2 ^ t)).symm
    rw [ZMod.neg_val, if_neg hk0, hsub, Nat.mul_div_cancel _ hp,
      Nat.mod_eq_of_lt (by omega)]

/-- Simultaneously negating two labels preserves and reflects window agreement when their lowest
`t` bits vanish and `w+t ≤ n`. -/
theorem windowAgree_neg (n w t : ℕ) (k ℓ : ZMod (2 ^ n))
    (hk : k.val % 2 ^ t = 0) (hℓ : ℓ.val % 2 ^ t = 0) (hw : w + t ≤ n) :
    windowAgree n w t k ℓ ↔ windowAgree n w t (-k) (-ℓ) := by
  have ht : t ≤ n := by omega
  have hκle : k.val / 2 ^ t ≤ 2 ^ (n - t) := by
    have h1 : k.val / 2 ^ t < 2 ^ (n - t) := by
      rw [Nat.div_lt_iff_lt_mul (show 0 < 2 ^ t by positivity),
        ← pow_add, Nat.sub_add_cancel ht]
      exact ZMod.val_lt k
    omega
  have hℓle : ℓ.val / 2 ^ t ≤ 2 ^ (n - t) := by
    have h1 : ℓ.val / 2 ^ t < 2 ^ (n - t) := by
      rw [Nat.div_lt_iff_lt_mul (show 0 < 2 ^ t by positivity),
        ← pow_add, Nat.sub_add_cancel ht]
      exact ZMod.val_lt ℓ
    omega
  have hdvd : 2 ^ w ∣ 2 ^ (n - t) :=
    Nat.pow_dvd_pow (a := 2) (m := w) (n := n - t) (by omega)
  unfold windowAgree
  rw [clause3_neg_div n t ht k hk, clause3_neg_div n t ht ℓ hℓ,
    Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd]
  exact (clause3_mod_sub_iff _ _ _ _ (show 0 < 2 ^ w by positivity) hdvd hκle hℓle).symm

/-- Iterated negation preserves and reflects window agreement under the zero-low-bit and
window-size hypotheses. -/
theorem windowAgree_negPow (n w t j : ℕ) (k ℓ : ZMod (2 ^ n))
    (hk : k.val % 2 ^ t = 0) (hℓ : ℓ.val % 2 ^ t = 0) (hw : w + t ≤ n) :
    windowAgree n w t k ℓ ↔ windowAgree n w t (negPow n j k) (negPow n j ℓ) := by
  induction j generalizing k ℓ with
  | zero => rfl
  | succ j ih =>
      have ht : t ≤ n := by omega
      rw [negPow_succ, negPow_succ]
      exact (windowAgree_neg n w t k ℓ hk hℓ hw).trans (ih (-k) (-ℓ)
        (clause3_neg_zeroBits n t ht k hk) (clause3_neg_zeroBits n t ht ℓ hℓ))

/-- The canonical residue of a label difference is computed by adding the complement of the
subtrahend modulo `2^n`. -/
private theorem clause3_val_sub_mod (n : ℕ) (k ℓ : ZMod (2 ^ n)) :
    (k - ℓ).val % 2 ^ n = (k.val + (2 ^ n - ℓ.val)) % 2 ^ n := by
  rw [sub_eq_add_neg, ZMod.val_add, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), ZMod.neg_val]
  by_cases hℓ : ℓ = 0
  · subst hℓ
    simp
  · rw [if_neg hℓ]

/-- Subtracting labels whose lowest `c` bits vanish preserves that property when `c ≤ n`. -/
private theorem clause3_zmod_sub_zeroBits (n c : ℕ) (hc : c ≤ n) (k ℓ : ZMod (2 ^ n))
    (hk : k.val % 2 ^ c = 0) (hℓ : ℓ.val % 2 ^ c = 0) :
    (k - ℓ).val % 2 ^ c = 0 := by
  have hℓlt : ℓ.val < 2 ^ n := ZMod.val_lt ℓ
  have hkd : 2 ^ c ∣ k.val := Nat.dvd_of_mod_eq_zero hk
  have hℓd : 2 ^ c ∣ ℓ.val := Nat.dvd_of_mod_eq_zero hℓ
  have hnd : 2 ^ c ∣ 2 ^ n := Nat.pow_dvd_pow _ hc
  have hEq : k.val + (2 ^ n - ℓ.val) = k.val + 2 ^ n - ℓ.val := by omega
  rw [show (k - ℓ).val % 2 ^ c = ((k - ℓ).val % 2 ^ n) % 2 ^ c from by
      rw [Nat.mod_eq_of_lt (ZMod.val_lt (k - ℓ))],
    clause3_val_sub_mod n k ℓ, Nat.mod_mod_of_dvd _ hnd, hEq]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub (Nat.dvd_add hkd hnd) hℓd)

/-- For labels with `t` zero low bits, window agreement is equivalent to congruence modulo
`2^(t+w)`. -/
theorem windowAgree_iff_modEq (n w t : ℕ) (k ℓ : ZMod (2 ^ n))
    (hk : k.val % 2 ^ t = 0) (hℓ : ℓ.val % 2 ^ t = 0) :
    windowAgree n w t k ℓ ↔ k.val ≡ ℓ.val [MOD 2 ^ (t + w)] := by
  have hkval : k.val = (k.val / 2 ^ t) * 2 ^ t := by
    have h := Nat.div_add_mod k.val (2 ^ t)
    rw [hk, add_zero, Nat.mul_comm] at h
    exact h.symm
  have hℓval : ℓ.val = (ℓ.val / 2 ^ t) * 2 ^ t := by
    have h := Nat.div_add_mod ℓ.val (2 ^ t)
    rw [hℓ, add_zero, Nat.mul_comm] at h
    exact h.symm
  have hmod : 2 ^ w * 2 ^ t = 2 ^ (t + w) := by
    rw [Nat.mul_comm, ← pow_add]
  unfold windowAgree
  constructor
  · intro h
    have h1 : (k.val / 2 ^ t) ≡ (ℓ.val / 2 ^ t) [MOD 2 ^ w] := h
    have h2 := Nat.ModEq.mul_right' (2 ^ t) h1
    rw [hmod] at h2
    rw [hkval, hℓval]
    exact h2
  · intro h
    rw [hkval, hℓval, ← hmod] at h
    exact h.mul_right_cancel' (show (2 ^ t : ℕ) ≠ 0 by positivity)

/-- The difference of window-agreeing labels with `t` zero low bits has `t+w` zero low bits when
the window fits within `n` bits. -/
theorem windowAgree_sub_zeroBits (n w t : ℕ) (k ℓ : ZMod (2 ^ n))
    (hk : k.val % 2 ^ t = 0) (hℓ : ℓ.val % 2 ^ t = 0)
    (hag : windowAgree n w t k ℓ) (htw : t + w ≤ n) :
    (k - ℓ : ZMod (2 ^ n)).val % 2 ^ (t + w) = 0 := by
  have hmod := (windowAgree_iff_modEq n w t k ℓ hk hℓ).1 hag
  have hℓlt : ℓ.val < 2 ^ n := ZMod.val_lt ℓ
  have hPd : 2 ^ (t + w) ∣ 2 ^ n := Nat.pow_dvd_pow _ htw
  have hEq : k.val + (2 ^ n - ℓ.val) = k.val + 2 ^ n - ℓ.val := by omega
  have h1 : k.val + 2 ^ n ≡ ℓ.val + 0 [MOD 2 ^ (t + w)] :=
    hmod.add ((Nat.modEq_zero_iff_dvd (a := 2 ^ n) (n := 2 ^ (t + w))).2 hPd)
  have hb1 : ℓ.val ≤ k.val + 2 ^ n := by omega
  have hb2 : ℓ.val ≤ ℓ.val + 0 := by omega
  have h2 := Nat.ModEq.sub_right hb1 hb2 h1
  rw [Nat.add_zero, Nat.sub_self] at h2
  rw [show (k - ℓ).val % 2 ^ (t + w) = ((k - ℓ).val % 2 ^ n) % 2 ^ (t + w) from by
      rw [Nat.mod_eq_of_lt (ZMod.val_lt (k - ℓ))],
    clause3_val_sub_mod n k ℓ, Nat.mod_mod_of_dvd _ hPd, hEq]
  exact Nat.mod_eq_zero_of_dvd ((Nat.modEq_zero_iff_dvd (a := k.val + 2 ^ n - ℓ.val)
    (n := 2 ^ (t + w))).1 h2)

/-- Erasing the image of a record commutes with mapping when that record is the first element
found with the specified image. -/
private theorem clause3_erase_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (r' : α) :
    ∀ (l : List α), l.find? (fun a => decide (f a = f r')) = some r' →
    (l.map f).erase (f r') = (l.erase r').map f := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro h
    by_cases ha : f a = f r'
    · have har : a = r' := by
        have h2 : (a :: l).find? (fun x => decide (f x = f r')) = some a := by
          simp [ha]
        rw [h2] at h
        exact Option.some.inj h
      subst har
      simp
    · have h2 : l.find? (fun x => decide (f x = f r')) = some r' := by
        have h3 : (a :: l).find? (fun x => decide (f x = f r'))
            = l.find? (fun x => decide (f x = f r')) := by simp [ha]
        rw [h3] at h
        exact h
      have hne : a ≠ r' := fun heq => ha (by rw [heq])
      have hL : ((a :: l).map f).erase (f r') = f a :: (l.map f).erase (f r') := by
        simp [ha]
      have hR : ((a :: l).erase r').map f = f a :: (l.erase r').map f := by
        simp [hne]
      rw [hL, hR, ih h2]

/-- Predicates that agree on every list element produce the same first matching element. -/
private theorem clause3_find?_congr {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
      intro h
      have hqa : p a = q a := h a (by simp)
      cases hq : q a with
      | true =>
          rw [List.find?_cons, List.find?_cons, hqa, hq]
      | false =>
          rw [List.find?_cons, List.find?_cons, hqa, hq]
          exact ih (fun x hx => h x (by simp [hx]))

/-- If `q` implies `p` on a list, and the first `p` match also satisfies `q`, it is the first
`q` match. -/
private theorem clause3_find?_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α) (r' : α), (∀ a ∈ l, q a = true → p a = true) →
    l.find? p = some r' → q r' = true → l.find? q = some r' := by
  intro l
  induction l with
  | nil => intro r' _ hfind _; simp at hfind
  | cons a l ih =>
    intro r' h hfind hq
    rw [List.find?_cons] at hfind ⊢
    cases hp : p a with
    | true =>
        rw [hp] at hfind
        have har : a = r' := Option.some.inj hfind
        rw [← har] at hq
        rw [hq, har]
    | false =>
        rw [hp] at hfind
        have hqa : q a = false := by
          cases hq' : q a with
          | true =>
              have hpt : p a = true := h a (by simp) hq'
              rw [hpt] at hp
              exact Bool.noConfusion hp
          | false => rfl
        rw [hqa]
        exact ih r' (fun a' ha' => h a' (by simp [ha'])) hfind hq

/-- Pair selection commutes with an injective label transformation that preserves window
agreement on labels with the specified zero low bits. -/
theorem sievePairWith_transport (n w t e : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (σ : ZMod (2 ^ n) → ZMod (2 ^ n))
    (hσ : Function.Injective σ)
    (hagree : ∀ (x y : α), (label x).val % 2 ^ e = 0 → (label y).val % 2 ^ e = 0 →
      (windowAgree n w t (label x) (label y) ↔
        windowAgree n w t (σ (label x)) (σ (label y)))) :
    ∀ (L : List α), (∀ x ∈ L, (label x).val % 2 ^ e = 0) →
    sievePair n w t ((L.map label).map σ)
    = (sievePairWith n label w t L).map
        (fun p : α × α => (σ (label p.1), σ (label p.2))) := by
  have main : ∀ (N : ℕ) (L : List α), L.length ≤ N →
      (∀ x ∈ L, (label x).val % 2 ^ e = 0) →
      sievePair n w t ((L.map label).map σ)
      = (sievePairWith n label w t L).map
        (fun p : α × α => (σ (label p.1), σ (label p.2))) := by
    intro N
    induction N with
    | zero =>
        intro L hL _
        cases L with
        | nil =>
            show sievePairWith n id w t ([] : List (ZMod (2 ^ n)))
              = (sievePairWith n label w t []).map
                  (fun p : α × α => (σ (label p.1), σ (label p.2)))
            rw [sievePairWith, sievePairWith]
            rfl
        | cons r rest => simp at hL
    | succ N ih =>
        intro L hL htail
        cases L with
        | nil =>
            show sievePairWith n id w t ([] : List (ZMod (2 ^ n)))
              = (sievePairWith n label w t []).map
                  (fun p : α × α => (σ (label p.1), σ (label p.2)))
            rw [sievePairWith, sievePairWith]
            rfl
        | cons r rest =>
          have hrestlen : rest.length ≤ N := by
            have hc : (r :: rest).length = rest.length + 1 :=
              List.length_cons (a := r) (as := rest)
            omega
          have hmapcons : ((r :: rest).map label).map σ
              = σ (label r) :: (rest.map label).map σ := by
            simp only [List.map_cons]
          have hfind : (((rest.map label).map σ).find?
              (fun x => @decide (windowAgree n w t (σ (label r)) x)
                (instDecidableWindowAgree n w t (id (σ (label r))) (id x))))
              = Option.map (fun a => σ (label a))
                  (rest.find? (fun r' => decide (windowAgree n w t (label r) (label r')))) := by
            have hlist : (rest.map label).map σ = rest.map (fun a => σ (label a)) := by
              rw [List.map_map]
              rfl
            have hpred : ∀ a ∈ rest,
                (((fun x => @decide (windowAgree n w t (σ (label r)) x)
                      (instDecidableWindowAgree n w t (id (σ (label r))) (id x)))
                  ∘ (fun a => σ (label a))) a)
                  = (fun a => decide (windowAgree n w t (label r) (label a))) a := by
              intro a ha
              show @decide (windowAgree n w t (σ (label r)) (σ (label a)))
                  (instDecidableWindowAgree n w t (id (σ (label r))) (id (σ (label a))))
                = decide (windowAgree n w t (label r) (label a))
              by_cases hag : windowAgree n w t (label r) (label a)
              · rw [decide_eq_true hag]
                have hr0 : (label r).val % 2 ^ e = 0 := htail r (by simp)
                have ha0 : (label a).val % 2 ^ e = 0 := htail a (by simp [ha])
                exact decide_eq_true ((hagree r a hr0 ha0).mp hag)
              · rw [decide_eq_false hag]
                have hr0 : (label r).val % 2 ^ e = 0 := htail r (by simp)
                have ha0 : (label a).val % 2 ^ e = 0 := htail a (by simp [ha])
                exact decide_eq_false ((hagree r a hr0 ha0).not.mp hag)
            rw [hlist, List.find?_map]
            exact congrArg _ (clause3_find?_congr _ _ rest hpred)
          cases hF : rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) with
          | none =>
              rw [sievePair, hmapcons, sievePairWith, sievePairWith]
              simp only [id]
              rw [hfind, hF]
              exact ih rest hrestlen (fun x hx => htail x (by simp [hx]))
          | some r' =>
              have hr' : r' ∈ rest := List.mem_of_find?_eq_some hF
              have hlen2 : (rest.erase r').length ≤ N := by
                rw [List.length_erase_of_mem hr']
                have hc : (r :: rest).length = rest.length + 1 :=
                  List.length_cons (a := r) (as := rest)
                omega
              have hfirstσ : rest.find? (fun a => decide (σ (label a) = σ (label r')))
                  = some r' := by
                refine clause3_find?_of_imp
                  (fun x => decide (windowAgree n w t (label r) (label x)))
                  (fun a => decide (σ (label a) = σ (label r'))) rest r' ?_ hF ?_
                · intro a _ hqa
                  have hal : label a = label r' := hσ (of_decide_eq_true hqa)
                  show decide (windowAgree n w t (label r) (label a)) = true
                  rw [hal]
                  exact List.find?_some (p := fun x =>
                    decide (windowAgree n w t (label r) (label x))) hF
                · simp
              have herase : (((rest.map label).map σ)).erase (σ (label r'))
                  = (rest.erase r').map (fun a => σ (label a)) := by
                rw [show (rest.map label).map σ = rest.map (fun a => σ (label a)) from by
                  rw [List.map_map]
                  rfl]
                exact clause3_erase_map (fun a => σ (label a)) r' rest hfirstσ
              rw [sievePair, hmapcons, sievePairWith, sievePairWith]
              simp only [id]
              rw [hfind, hF]
              simp only [Option.map_some]
              rw [herase, List.map_cons]
              have ih2 := ih (rest.erase r') hlen2
                (fun x hx => htail x (by simp [List.mem_of_mem_erase hx]))
              rw [List.map_map] at ih2
              exact congrArg _ ih2
  intro L htailL
  exact main L.length L (Nat.le_refl _) htailL

/-- Mapping a uniform element of `Fin 2` to the test for equality to one gives a uniform
Boolean. -/
private theorem clause3_fin2_bool :
    (PMF.uniformOfFintype' (Fin 2)).map (fun b : Fin 2 => decide (b = 1))
      = PMF.uniformOfFintype' Bool := by
  refine PMF.ext fun c => ?_
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype'_apply]
  cases c <;> simp [Fin.sum_univ_two, Fintype.card_bool]

/-- A computation depending only on a fair extraction bit can be expressed using a uniform
element of `Fin 2`. -/
private theorem clause3_coin_split {γ : Type} (P : PMF (Bool × NormQ))
    (hfair : P.map Prod.fst = PMF.uniformOfFintype' Bool) (F : Bool → PMF γ) :
    P.bind (fun q => F q.1)
      = (PMF.uniformOfFintype' (Fin 2)).bind (fun b => F (b = 1)) := by
  have h1 : P.bind (fun q => F q.1) = (P.map Prod.fst).bind F :=
    (PMF.bind_map P Prod.fst F).symm
  rw [h1, hfair, ← clause3_fin2_bool, PMF.bind_map]
  rfl

/-- Two probability kernels have equal binds if they agree at every positive-probability input. -/
private theorem clause3_bind_congr {α β : Type} {p : PMF α} {f g : α → PMF β}
    (h : ∀ a, 0 < p a → f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases hpos : 0 < p a
  · rw [h a hpos]
  · have hz : p a = 0 := le_antisymm (not_lt.mp hpos) zero_le
    rw [hz, zero_mul, zero_mul]

/-- Every pair of labels agrees on a window of width zero. -/
private theorem clause3_windowAgree_zero (n t : ℕ) (k ℓ : ZMod (2 ^ n)) :
    windowAgree n 0 t k ℓ := by
  unfold windowAgree
  rw [Nat.pow_zero, Nat.mod_one, Nat.mod_one]

/-- Both components of every selected pair belong to the input list, under the stated length
bound. -/
private theorem clause3_pairWith_mem (n : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) :
    ∀ (N : ℕ) (L : List α), L.length ≤ N →
      ∀ p ∈ sievePairWith n label w t L, p.1 ∈ L ∧ p.2 ∈ L := by
  intro N
  induction N with
  | zero =>
      intro L hL
      cases L with
      | nil =>
          intro p hp
          rw [sievePairWith] at hp
          simp at hp
      | cons r rest => simp at hL
  | succ N ih =>
      intro L hL
      cases L with
      | nil =>
          intro p hp
          rw [sievePairWith] at hp
          simp at hp
      | cons r rest =>
          have hc : (r :: rest).length = rest.length + 1 :=
            List.length_cons (a := r) (as := rest)
          have hrestlen : rest.length ≤ N := by omega
          intro p hp
          rw [sievePairWith] at hp
          split at hp
          · have hm := ih rest hrestlen p hp
            exact ⟨by simp [hm.1], by simp [hm.2]⟩
          · next r' heq =>
              have hr'mem : r' ∈ rest := List.mem_of_find?_eq_some heq
              have herase : (rest.erase r').length ≤ N := by
                rw [List.length_erase_of_mem hr'mem]
                omega
              rcases List.mem_cons.1 hp with hpeq | hrest
              · subst hpeq
                exact ⟨by simp, by simp [hr'mem]⟩
              · have hm := ih (rest.erase r') herase p hrest
                have h1 : p.1 ∈ rest := List.mem_of_mem_erase hm.1
                have h2 : p.2 ∈ rest := List.mem_of_mem_erase hm.2
                exact ⟨by simp [h1], by simp [h2]⟩

/-- The two Boolean coercion forms of the keep-or-discard test define the same mapped list
distribution. -/
private theorem clause3_layer_coin_head {γ : Type} (Q : PMF (List γ)) (x : γ) :
    ∀ b : Fin 2,
      Q.map (fun T => if decide (b = 1) then x :: T else T)
        = Q.map (fun T => if b = 1 then x :: T else T) := by
  intro b
  ext T
  by_cases hb : b = 1 <;> simp [hb]

/-- For pairs of dihedral-family records, mapping output labels by `negPow n (j+1)` turns actual
auxiliary extraction into ideal extraction on labels transformed by `negPow n j`. -/
private theorem clause3_layerAux_transport (n j : ℕ) (s : ZMod (2 ^ n))
    (ps : List ((ZMod (2 ^ n) × NormQ) × (ZMod (2 ^ n) × NormQ)))
    (hfam : ∀ p ∈ ps, ∃ u u' : ℂ, ‖u‖ = 1 ∧ ‖u'‖ = 1 ∧
      p.1.2.1 = u • dihedralQubitState (2 ^ n) s p.1.1 ∧
      p.2.2.1 = u' • dihedralQubitState (2 ^ n) s p.2.1) :
    (actualLayerAux n ps).map (fun B => B.map (fun r => negPow n (j + 1) r.1))
      = idealLayerAux n (ps.map (fun p => (negPow n j p.1.1, negPow n j p.2.1))) := by
  classical
  induction ps with
  | nil =>
      show (PMF.pure ([] : List (ZMod (2 ^ n) × NormQ))).map
          (fun B => B.map (fun r => negPow n (j + 1) r.1))
        = PMF.pure ([] : List (ZMod (2 ^ n)))
      rw [PMF.pure_map]
      rfl
  | cons p ps ih =>
      obtain ⟨⟨k, χ⟩, ℓ, χ'⟩ := p
      obtain ⟨u, u', hu, hu', hχ, hχ'⟩ := hfam (⟨k, χ⟩, ℓ, χ') (by simp)
      have hfair : (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2).map Prod.fst
          = PMF.uniformOfFintype' Bool := by
        have hf := dihedralExtraction_fair (2 ^ n) s k ℓ u u' hu hu'
        have hχe : (χ : NormQ) = ⟨u • dihedralQubitState (2 ^ n) s k,
            clause3_unit_norm hu (normalized_dihedralQubitState (2 ^ n) s k)⟩ := Subtype.ext hχ
        have hχ'e : (χ' : NormQ) = ⟨u' • dihedralQubitState (2 ^ n) s ℓ,
            clause3_unit_norm hu' (normalized_dihedralQubitState (2 ^ n) s ℓ)⟩ := Subtype.ext hχ'
        rw [hχe, hχ'e]
        exact hf
      have hAL : (actualLayerAux n (((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) :: ps)).map
            (fun B => B.map (fun r => negPow n (j + 1) r.1))
          = (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2).bind (fun q =>
              ((actualLayerAux n ps).map
                (fun tail => if q.1 then (k - ℓ, q.2) :: tail else tail)).map
                (fun B => B.map (fun r => negPow n (j + 1) r.1))) := by
        rw [actualLayerAux, PMF.map_bind]
      have hIL : idealLayerAux n ((negPow n j k, negPow n j ℓ) ::
            (ps.map (fun p => (negPow n j p.1.1, negPow n j p.2.1))))
          = (PMF.uniformOfFintype' (Fin 2)).bind (fun b =>
              (idealLayerAux n (ps.map
                (fun p => (negPow n j p.1.1, negPow n j p.2.1)))).map
                (fun tail => if b = 1 then (negPow n j ℓ - negPow n j k) :: tail else tail)) := by
        rw [idealLayerAux]
      rw [hAL]
      simp only [List.map_cons]
      rw [hIL]
      have hco : ∀ q : Bool × NormQ,
          (fun B => B.map (fun r => negPow n (j + 1) r.1)) ∘
              (fun tail => if q.1 then (k - ℓ, q.2) :: tail else tail)
            = (fun T => if q.1 then (negPow n j ℓ - negPow n j k) :: T else T) ∘
              (fun B => B.map (fun r => negPow n (j + 1) r.1)) := by
        intro q
        funext T
        by_cases hq : q.1 = true
        · show List.map (fun r => negPow n (j + 1) r.1)
                ((if q.1 = true then (k - ℓ, q.2) :: T else T))
            = (if q.1 = true then (negPow n j ℓ - negPow n j k)
                :: List.map (fun r => negPow n (j + 1) r.1) T
              else List.map (fun r => negPow n (j + 1) r.1) T)
          rw [if_pos hq, if_pos hq, List.map_cons, negPow_sub_succ n j k ℓ]
        · show List.map (fun r => negPow n (j + 1) r.1)
                ((if q.1 = true then (k - ℓ, q.2) :: T else T))
            = (if q.1 = true then (negPow n j ℓ - negPow n j k)
                :: List.map (fun r => negPow n (j + 1) r.1) T
              else List.map (fun r => negPow n (j + 1) r.1) T)
          rw [if_neg hq, if_neg hq]
      have hcs := clause3_coin_split (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2) hfair
          (fun c : Bool => (idealLayerAux n (ps.map
            (fun p => (negPow n j p.1.1, negPow n j p.2.1)))).map
            (fun T => if c then (negPow n j ℓ - negPow n j k) :: T else T))
      refine Eq.trans ?_ (Eq.trans hcs
        (clause3_bind_congr (p := PMF.uniformOfFintype' (Fin 2)) (fun b _ =>
          clause3_layer_coin_head (idealLayerAux n (ps.map
            (fun p => (negPow n j p.1.1, negPow n j p.2.1))))
            (negPow n j ℓ - negPow n j k) b)))
      exact clause3_bind_congr (p := dihedralExtraction χ.1 χ'.1 χ.2 χ'.2)
        (fun q _ => by
          rw [PMF.map_comp, hco q, ← PMF.map_comp,
            ih (fun p hp => hfam p (by simp [hp]))])

/-- Adding the current window width to `m*j`, capped at `n-1`, gives the next capped bit
threshold. -/
private theorem clause3_child_window (n m j : ℕ) :
    min (m * j + sieveWindowWidth n m j) (n - 1) = min (m * (j + 1)) (n - 1) := by
  unfold sieveWindowWidth
  simp only [Nat.mul_succ]
  by_cases h : n - 1 - m * j ≤ m
  · rw [Nat.min_eq_right h]
    omega
  · rw [Nat.min_eq_left (by omega : m ≤ n - 1 - m * j)]

/-- Actual layer labels follow the ideal layer after iterated negation when the stated
window-agreement, zero-low-bit, and paired-state family hypotheses hold. -/
private theorem clause3_layer_step_of (n m j e : ℕ) (s : ZMod (2 ^ n))
    (A : List (ZMod (2 ^ n) × NormQ))
    (hagree : ∀ (x y : ZMod (2 ^ n) × NormQ),
      (Prod.fst x).val % 2 ^ e = 0 → (Prod.fst y).val % 2 ^ e = 0 →
      (windowAgree n (sieveWindowWidth n m j) (m * j) (Prod.fst x) (Prod.fst y) ↔
        windowAgree n (sieveWindowWidth n m j) (m * j)
          (negPow n j (Prod.fst x)) (negPow n j (Prod.fst y))))
    (htl : ∀ x ∈ A, (Prod.fst x).val % 2 ^ e = 0)
    (hfamA : ∀ p ∈ sievePairWith n (α := ZMod (2 ^ n) × NormQ) Prod.fst
        (sieveWindowWidth n m j) (m * j) A, ∃ u u' : ℂ, ‖u‖ = 1 ∧ ‖u'‖ = 1 ∧
      p.1.2.1 = u • dihedralQubitState (2 ^ n) s p.1.1 ∧
      p.2.2.1 = u' • dihedralQubitState (2 ^ n) s p.2.1) :
    (actualLayer n (sieveWindowWidth n m j) (m * j) A).map
        (fun B => B.map (fun r => negPow n (j + 1) r.1))
      = idealLayer n m j (A.map (fun r => negPow n j r.1)) := by
  have htp := sievePairWith_transport n (sieveWindowWidth n m j) (m * j) e
    (α := ZMod (2 ^ n) × NormQ) Prod.fst (negPow n j) (negPow_injective n j) hagree A htl
  have hmap : A.map (fun r => negPow n j r.1) = (A.map Prod.fst).map (negPow n j) := by
    rw [List.map_map]
    rfl
  rw [actualLayer, idealLayer, hmap, htp]
  exact clause3_layerAux_transport n j s _ hfamA

/-- On a family list satisfying the stage's zero-low-bit invariant, the actual layer's
transformed label law equals the corresponding ideal layer law. -/
private theorem clause3_layer_step (n m j : ℕ) (s : ZMod (2 ^ n))
    (A : List (ZMod (2 ^ n) × NormQ)) (hfam : FamilyList n s A)
    (htail : ∀ r ∈ A, r.1.val % 2 ^ (min (m * j) (n - 1)) = 0) :
    (actualLayer n (sieveWindowWidth n m j) (m * j) A).map
        (fun B => B.map (fun r => negPow n (j + 1) r.1))
      = idealLayer n m j (A.map (fun r => negPow n j r.1)) := by
  classical
  have hfamA : ∀ p ∈ sievePairWith n (α := ZMod (2 ^ n) × NormQ) Prod.fst
      (sieveWindowWidth n m j) (m * j) A, ∃ u u' : ℂ, ‖u‖ = 1 ∧ ‖u'‖ = 1 ∧
      p.1.2.1 = u • dihedralQubitState (2 ^ n) s p.1.1 ∧
      p.2.2.1 = u' • dihedralQubitState (2 ^ n) s p.2.1 := by
    intro p hp
    have hmem := clause3_pairWith_mem n Prod.fst (sieveWindowWidth n m j) (m * j)
      A.length A (Nat.le_refl _) p hp
    obtain ⟨u, hu, hu1⟩ := hfam p.1 hmem.1
    obtain ⟨u', hu', hu2⟩ := hfam p.2 hmem.2
    exact ⟨u, u', hu, hu', hu1, hu2⟩
  by_cases hw : sieveWindowWidth n m j = 0
  · have hagree : ∀ (x y : ZMod (2 ^ n) × NormQ),
        (Prod.fst x).val % 2 ^ 0 = 0 → (Prod.fst y).val % 2 ^ 0 = 0 →
        (windowAgree n (sieveWindowWidth n m j) (m * j) (Prod.fst x) (Prod.fst y) ↔
          windowAgree n (sieveWindowWidth n m j) (m * j)
            (negPow n j (Prod.fst x)) (negPow n j (Prod.fst y))) := by
      intro x y _ _
      rw [hw]
      constructor <;> intro _ <;> exact clause3_windowAgree_zero n _ _ _
    refine clause3_layer_step_of n m j 0 s A hagree ?_ hfamA
    intro x _
    exact Nat.mod_one _
  · have hwle : sieveWindowWidth n m j ≤ n - 1 - m * j := Nat.min_le_right _ _
    have htw : m * j + sieveWindowWidth n m j ≤ n := by omega
    have hmin : min (m * j) (n - 1) = m * j := by omega
    refine clause3_layer_step_of n m j (m * j) s A
      (fun x y hx hy => windowAgree_negPow n _ _ j _ _ hx hy
        (by omega : sieveWindowWidth n m j + m * j ≤ n)) ?_ hfamA
    intro x hx
    have h := htail x hx
    rwa [hmin] at h

/-- Auxiliary extraction from pairs in the dihedral state family produces only lists in the same
family at positive probability. -/
private theorem clause3_layerAux_fam (n : ℕ) (s : ZMod (2 ^ n))
    (ps : List ((ZMod (2 ^ n) × NormQ) × (ZMod (2 ^ n) × NormQ)))
    (hfam : ∀ p ∈ ps, ∃ u u' : ℂ, ‖u‖ = 1 ∧ ‖u'‖ = 1 ∧
      p.1.2.1 = u • dihedralQubitState (2 ^ n) s p.1.1 ∧
      p.2.2.1 = u' • dihedralQubitState (2 ^ n) s p.2.1) :
    ∀ B, 0 < actualLayerAux n ps B → FamilyList n s B := by
  induction ps with
  | nil =>
      intro B hB
      change 0 < (PMF.pure ([] : List (ZMod (2 ^ n) × NormQ))) B at hB
      rw [PMF.pure_apply] at hB
      by_cases hEq : B = []
      · subst hEq
        intro r hr
        exact absurd hr (by simp)
      · rw [if_neg hEq] at hB
        simp at hB
  | cons p ps ih =>
      obtain ⟨⟨k, χ⟩, ℓ, χ'⟩ := p
      obtain ⟨u, u', hu, hu', hχ, hχ'⟩ := hfam (⟨k, χ⟩, ℓ, χ') List.mem_cons_self
      have hih := ih (fun p hp => hfam p (by simp [hp]))
      intro B hB
      change 0 < (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2).bind
        (fun q => (actualLayerAux n ps).map
          (fun tail => if q.1 then (k - ℓ, q.2) :: tail else tail)) B at hB
      obtain ⟨q, T, hTB, hqe, hT⟩ := clause3_bind_map_pos_witness
        (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2) (actualLayerAux n ps)
        (fun q tail => if q.1 then (k - ℓ, q.2) :: tail else tail) B hB
      cases hq1 : q.1 with
      | true =>
          have hBdef : (if q.1 = true then (k - ℓ, q.2) :: T else T) = B := hTB
          rw [hq1, if_pos (rfl : (true : Bool) = true)] at hBdef
          subst hBdef
          have hχe : (χ : NormQ) = ⟨u • dihedralQubitState (2 ^ n) s k,
              clause3_unit_norm hu (normalized_dihedralQubitState (2 ^ n) s k)⟩ := Subtype.ext hχ
          have hχ'e : (χ' : NormQ) = ⟨u' • dihedralQubitState (2 ^ n) s ℓ,
              clause3_unit_norm hu' (normalized_dihedralQubitState (2 ^ n) s ℓ)⟩ :=
            Subtype.ext hχ'
          rw [hχe, hχ'e] at hqe
          obtain ⟨w, hw, hwfam⟩ := dihedralExtraction_family (2 ^ n) s k ℓ u u' hu hu' q hqe
          rw [hq1, if_pos (rfl : (true : Bool) = true)] at hwfam
          exact FamilyList.cons ⟨w, hw, hwfam⟩ (hih T hT)
      | false =>
          have hBdef : (if q.1 = true then (k - ℓ, q.2) :: T else T) = B := hTB
          rw [hq1, if_neg (by simp : ¬(false : Bool) = true)] at hBdef
          subst hBdef
          exact hih T hT

/-- Every pair selected by `sievePairWith` has window-agreeing labels, under the stated input
length bound. -/
private theorem clause3_pairWith_agree (n : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) :
    ∀ (N : ℕ) (L : List α), L.length ≤ N →
      ∀ p ∈ sievePairWith n label w t L, windowAgree n w t (label p.1) (label p.2) := by
  intro N
  induction N with
  | zero =>
      intro L hL
      cases L with
      | nil =>
          intro p hp
          rw [sievePairWith] at hp
          simp at hp
      | cons r rest => simp at hL
  | succ N ih =>
      intro L hL
      cases L with
      | nil =>
          intro p hp
          rw [sievePairWith] at hp
          simp at hp
      | cons r rest =>
          have hc : (r :: rest).length = rest.length + 1 :=
            List.length_cons (a := r) (as := rest)
          have hrestlen : rest.length ≤ N := by omega
          intro p hp
          rw [sievePairWith] at hp
          split at hp
          · exact ih rest hrestlen p hp
          · next r' heq =>
              have hr'mem : r' ∈ rest := List.mem_of_find?_eq_some heq
              have herase : (rest.erase r').length ≤ N := by
                rw [List.length_erase_of_mem hr'mem]
                omega
              rcases List.mem_cons.1 hp with hpeq | hrest
              · subst hpeq
                exact of_decide_eq_true (List.find?_some (p := fun x =>
                  decide (windowAgree n w t (label r) (label x))) heq)
              · exact ih (rest.erase r') herase p hrest

/-- Auxiliary extraction from window-agreeing pairs with `t` zero low bits produces only labels
with `t+w` zero low bits when `t+w ≤ n`. -/
private theorem clause3_layerAux_tail_wpos (n w t : ℕ) (htw : t + w ≤ n)
    (ps : List ((ZMod (2 ^ n) × NormQ) × (ZMod (2 ^ n) × NormQ)))
    (hagree : ∀ (k : ZMod (2 ^ n)) (χ : NormQ) (ℓ : ZMod (2 ^ n)) (χ' : NormQ),
      ((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) ∈ ps → windowAgree n w t k ℓ)
    (htail : ∀ (k : ZMod (2 ^ n)) (χ : NormQ) (ℓ : ZMod (2 ^ n)) (χ' : NormQ),
      ((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) ∈ ps →
      k.val % 2 ^ t = 0 ∧ ℓ.val % 2 ^ t = 0) :
    ∀ B, 0 < actualLayerAux n ps B → ∀ r ∈ B, r.1.val % 2 ^ (t + w) = 0 := by
  induction ps with
  | nil =>
      intro B hB
      change 0 < (PMF.pure ([] : List (ZMod (2 ^ n) × NormQ))) B at hB
      rw [PMF.pure_apply] at hB
      by_cases hEq : B = []
      · subst hEq
        intro r hr
        exact absurd hr (by simp)
      · rw [if_neg hEq] at hB
        simp at hB
  | cons p ps ih =>
      obtain ⟨⟨k, χ⟩, ℓ, χ'⟩ := p
      have hmem : ((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) ∈
          ((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) :: ps := List.mem_cons_self
      have hagP : windowAgree n w t k ℓ := hagree k χ ℓ χ' hmem
      obtain ⟨htl1, htl2⟩ := htail k χ ℓ χ' hmem
      have hih := ih (fun k χ ℓ χ' hp => hagree k χ ℓ χ' (by simp [hp]))
        (fun k χ ℓ χ' hp => htail k χ ℓ χ' (by simp [hp]))
      intro B hB
      change 0 < (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2).bind
        (fun q => (actualLayerAux n ps).map
          (fun tail => if q.1 then (k - ℓ, q.2) :: tail else tail)) B at hB
      obtain ⟨q, T, hTB, _hqe, hT⟩ := clause3_bind_map_pos_witness
        (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2) (actualLayerAux n ps)
        (fun q tail => if q.1 then (k - ℓ, q.2) :: tail else tail) B hB
      cases hq1 : q.1 with
      | true =>
          have hBdef : (if q.1 = true then (k - ℓ, q.2) :: T else T) = B := hTB
          rw [hq1, if_pos (rfl : (true : Bool) = true)] at hBdef
          subst hBdef
          intro r hr
          rcases List.mem_cons.1 hr with he | he
          · subst he
            exact windowAgree_sub_zeroBits n w t k ℓ htl1 htl2 hagP htw
          · exact hih T hT r he
      | false =>
          have hBdef : (if q.1 = true then (k - ℓ, q.2) :: T else T) = B := hTB
          rw [hq1, if_neg (by simp : ¬(false : Bool) = true)] at hBdef
          subst hBdef
          exact hih T hT

/-- Auxiliary extraction preserves `c` zero low bits when both labels of every input pair
satisfy that property and `c ≤ n`. -/
private theorem clause3_layerAux_tail_w0 (n c : ℕ) (hc : c ≤ n)
    (ps : List ((ZMod (2 ^ n) × NormQ) × (ZMod (2 ^ n) × NormQ)))
    (htail : ∀ (k : ZMod (2 ^ n)) (χ : NormQ) (ℓ : ZMod (2 ^ n)) (χ' : NormQ),
      ((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) ∈ ps →
      k.val % 2 ^ c = 0 ∧ ℓ.val % 2 ^ c = 0) :
    ∀ B, 0 < actualLayerAux n ps B → ∀ r ∈ B, r.1.val % 2 ^ c = 0 := by
  induction ps with
  | nil =>
      intro B hB
      change 0 < (PMF.pure ([] : List (ZMod (2 ^ n) × NormQ))) B at hB
      rw [PMF.pure_apply] at hB
      by_cases hEq : B = []
      · subst hEq
        intro r hr
        exact absurd hr (by simp)
      · rw [if_neg hEq] at hB
        simp at hB
  | cons p ps ih =>
      obtain ⟨⟨k, χ⟩, ℓ, χ'⟩ := p
      have hmem : ((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) ∈
          ((⟨k, χ⟩ : ZMod (2 ^ n) × NormQ), (ℓ, χ')) :: ps := List.mem_cons_self
      obtain ⟨htl1, htl2⟩ := htail k χ ℓ χ' hmem
      have hih := ih (fun k χ ℓ χ' hp => htail k χ ℓ χ' (by simp [hp]))
      intro B hB
      change 0 < (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2).bind
        (fun q => (actualLayerAux n ps).map
          (fun tail => if q.1 then (k - ℓ, q.2) :: tail else tail)) B at hB
      obtain ⟨q, T, hTB, _hqe, hT⟩ := clause3_bind_map_pos_witness
        (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2) (actualLayerAux n ps)
        (fun q tail => if q.1 then (k - ℓ, q.2) :: tail else tail) B hB
      cases hq1 : q.1 with
      | true =>
          have hBdef : (if q.1 = true then (k - ℓ, q.2) :: T else T) = B := hTB
          rw [hq1, if_pos (rfl : (true : Bool) = true)] at hBdef
          subst hBdef
          intro r hr
          rcases List.mem_cons.1 hr with he | he
          · subst he
            exact clause3_zmod_sub_zeroBits n c hc k ℓ htl1 htl2
          · exact hih T hT r he
      | false =>
          have hBdef : (if q.1 = true then (k - ℓ, q.2) :: T else T) = B := hTB
          rw [hq1, if_neg (by simp : ¬(false : Bool) = true)] at hBdef
          subst hBdef
          exact hih T hT

/-- A positive-probability outcome of a bind has an intermediate value with positive outer and
conditional probability. -/
private theorem clause3_bind_pos_witness {α β : Type} (p : PMF α) (q : α → PMF β) (z : β)
    (hz : 0 < p.bind q z) : ∃ a, 0 < p a ∧ 0 < q a z := by
  classical
  by_contra hcon
  push Not at hcon
  have hterm : ∀ a, p a * q a z = 0 := by
    intro a
    by_cases hpa : 0 < p a
    · have hqz : q a z = 0 := le_antisymm (hcon a hpa) (by simp)
      rw [hqz, mul_zero]
    · have hpa0 : p a = 0 := le_antisymm (not_lt.mp hpa) (by simp)
      rw [hpa0, zero_mul]
  rw [PMF.bind_apply, ENNReal.tsum_eq_zero.2 hterm] at hz
  simp at hz

/-- Every positive-probability actual layer output preserves the input's dihedral family
property. -/
private theorem clause3_layer_fam (n m j : ℕ) (s : ZMod (2 ^ n))
    (A : List (ZMod (2 ^ n) × NormQ)) (hfam : FamilyList n s A) (B)
    (hB : 0 < actualLayer n (sieveWindowWidth n m j) (m * j) A B) :
    FamilyList n s B := by
  rw [actualLayer] at hB
  refine clause3_layerAux_fam n s _ ?_ B hB
  intro p hp
  have hmem := clause3_pairWith_mem n Prod.fst (sieveWindowWidth n m j) (m * j)
    A.length A (Nat.le_refl _) p hp
  obtain ⟨u, hu, hu1⟩ := hfam p.1 hmem.1
  obtain ⟨u', hu', hu2⟩ := hfam p.2 hmem.2
  exact ⟨u, u', hu, hu', hu1, hu2⟩

/-- Every positive-probability actual layer output satisfies the next stage's capped
zero-low-bit invariant. -/
private theorem clause3_layer_tail (n m j : ℕ)
    (A : List (ZMod (2 ^ n) × NormQ))
    (htail : ∀ r ∈ A, r.1.val % 2 ^ (min (m * j) (n - 1)) = 0) (B)
    (hB : 0 < actualLayer n (sieveWindowWidth n m j) (m * j) A B) :
    ∀ r ∈ B, r.1.val % 2 ^ (min (m * (j + 1)) (n - 1)) = 0 := by
  classical
  rw [actualLayer] at hB
  have hmem := clause3_pairWith_mem n Prod.fst (sieveWindowWidth n m j) (m * j)
    A.length A (Nat.le_refl _)
  have hagreeL := clause3_pairWith_agree n Prod.fst (sieveWindowWidth n m j) (m * j)
    A.length A (Nat.le_refl _)
  by_cases hw : sieveWindowWidth n m j = 0
  · rw [← clause3_child_window n m j, hw, Nat.add_zero]
    refine clause3_layerAux_tail_w0 n (min (m * j) (n - 1))
      (Nat.le_trans (Nat.min_le_right _ _) (by omega)) _ ?_ B hB
    intro k χ ℓ χ' hp
    obtain ⟨h1, h2⟩ := hmem _ hp
    exact ⟨htail (k, χ) h1, htail (ℓ, χ') h2⟩
  · have hwle : sieveWindowWidth n m j ≤ n - 1 - m * j := Nat.min_le_right _ _
    have htw : sieveWindowWidth n m j + m * j ≤ n := by omega
    have hmin : min (m * j) (n - 1) = m * j := by omega
    have hc2 : min (m * j + sieveWindowWidth n m j) (n - 1)
        = m * j + sieveWindowWidth n m j := Nat.min_eq_left (by omega)
    rw [← clause3_child_window n m j, hc2]
    refine clause3_layerAux_tail_wpos n (sieveWindowWidth n m j) (m * j)
      (by omega : m * j + sieveWindowWidth n m j ≤ n) _ ?_ ?_ B hB
    · intro _k _χ _ℓ _χ' hp
      exact hagreeL _ hp
    · intro k χ ℓ χ' hp
      obtain ⟨h1, h2⟩ := hmem _ hp
      rw [hmin] at htail
      exact ⟨htail (k, χ) h1, htail (ℓ, χ') h2⟩

/-- Recursive actual sieving from a family list preserves the family property and enforces the
stage's capped zero-low-bit invariant on every positive-probability output. -/
private theorem clause3_sieve_rec_support (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)) :
    ∀ (j : ℕ) (A : List (ZMod (2 ^ n) × NormQ)), FamilyList n s A →
      ∀ B, 0 < actualSieveRec n m f j A B →
        FamilyList n s B ∧ (∀ r ∈ B, r.1.val % 2 ^ (min (m * j) (n - 1)) = 0) := by
  intro j
  induction j with
  | zero =>
      intro A hfam B hB
      change 0 < (PMF.pure A) B at hB
      have hBA : B = A := by
        by_contra hne
        rw [PMF.pure_apply, if_neg hne] at hB
        simp at hB
      subst hBA
      refine ⟨hfam, fun r _ => Nat.mod_one _⟩
  | succ j ih =>
      intro A hfam B hB
      rw [actualSieveRec] at hB
      obtain ⟨A', hA'pos, hB'pos⟩ := clause3_bind_pos_witness
        (actualSieveRec n m f j A)
        (actualLayer n (sieveWindowWidth n m j) (m * j)) B hB
      obtain ⟨hfamA', htailA'⟩ := ih A hfam A' hA'pos
      exact ⟨clause3_layer_fam n m j s A' hfamA' B hB'pos,
        clause3_layer_tail n m j A' htailA' B hB'pos⟩

/-- Mapping recursive actual output labels by the stage's iterated negation gives the ideal
recursive label distribution for a family-list input. -/
private theorem clause3_sieve_rec_transport (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)) :
    ∀ (j : ℕ) (A : List (ZMod (2 ^ n) × NormQ)), FamilyList n s A →
      (actualSieveRec n m f j A).map (fun B => B.map (fun r => negPow n j r.1))
        = idealSieveRec n m j (A.map Prod.fst) := by
  intro j
  induction j with
  | zero =>
      intro A hfam
      have hfun : (fun r : ZMod (2 ^ n) × NormQ => negPow n 0 r.1) = Prod.fst := by
        funext r
        rfl
      show (PMF.pure A).map (fun B => B.map (fun r => negPow n 0 r.1))
          = PMF.pure (A.map Prod.fst)
      rw [PMF.pure_map, hfun]
  | succ j ih =>
      intro A hfam
      rw [actualSieveRec, idealSieveRec, PMF.map_bind, ← ih A hfam, PMF.bind_map]
      refine clause3_bind_congr (p := actualSieveRec n m f j A) ?_
      intro A' hpos
      obtain ⟨hfamA', htailA'⟩ := clause3_sieve_rec_support n m f s j A hfam A' hpos
      exact clause3_layer_step n m j s A' hfamA' htailA'

/-- Equal normalized state vectors determine equal Born distributions. -/
private theorem clause3_bornDistribution_congr {I : Type*} [Fintype I] {ψ φ : QState I}
    (hψ : Normalized ψ) (hφ : Normalized φ) (h : ψ = φ) :
    bornDistribution ψ hψ = bornDistribution φ hφ := by
  subst h
  rfl

/-- Equal normalized qubit state vectors determine equal parity-readout distributions. -/
private theorem clause3_parityReadout_congr {ψ φ : QState Bool} (hψ : Normalized ψ)
    (hφ : Normalized φ) (h : ψ = φ) : parityReadout ψ hψ = parityReadout φ hφ := by
  subst h
  rfl

/-- A scalar of norm one leaves parity readout unchanged. -/
private theorem clause3_parityReadout_smul {u : ℂ} (hu : ‖u‖ = 1) (χ : QState Bool)
    (hχ : Normalized χ) :
    parityReadout (u • χ) (clause3_unit_norm hu hχ) = parityReadout χ hχ := by
  have hstep := clause3_bornDistribution_congr
    (normalized_applyGate hadamard_unitary (clause3_unit_norm hu hχ))
    (clause3_unit_norm hu (normalized_applyGate hadamard_unitary hχ))
    (clause3_applyGate_smul Hadamard u χ)
  have hsmul := clause3_bornDistribution_smul hu
    (normalized_applyGate hadamard_unitary hχ)
  unfold parityReadout
  exact hstep.trans hsmul

/-- Actual readout of a family list equals ideal readout on labels transformed by `negPow n m`. -/
private theorem clause3_readout_transport (n m : ℕ) (s : ZMod (2 ^ n))
    (A : List (ZMod (2 ^ n) × NormQ)) (hfam : FamilyList n s A) :
    actualReadout n A
      = idealReadout n s (A.map (fun r => negPow n m r.1)) := by
  classical
  have hfind : (A.map (fun r => negPow n m r.1)).find?
      (fun r => decide (r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))))
      = Option.map (fun r => negPow n m r.1)
          (A.find? (fun r : ZMod (2 ^ n) × NormQ =>
            decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))))) := by
    rw [List.find?_map]
    refine congrArg _ (clause3_find?_congr _ _ A ?_)
    intro r _hr
    show decide (negPow n m r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))
        = decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))
    by_cases h : r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))
    · rw [h, negPow_halfPeriod]
    · rw [decide_eq_false h, decide_eq_false (fun hpos =>
        h (by rw [← negPow_invol n m r.1, hpos, negPow_halfPeriod]))]
  rw [actualReadout, idealReadout, hfind]
  cases hF : A.find? (fun r => decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none =>
      rfl
  | some r =>
      have hrhalf : r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) :=
        of_decide_eq_true
          (List.find?_some (p := fun x : ZMod (2 ^ n) × NormQ =>
            decide (x.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) hF)
      have hrmem : r ∈ A := List.mem_of_find?_eq_some hF
      obtain ⟨u, hu, hr2⟩ := hfam r hrmem
      show (parityReadout r.2.1 r.2.2).map some
          = (parityReadout (dihedralQubitState (2 ^ n) s (negPow n m r.1))
              (normalized_dihedralQubitState (2 ^ n) s (negPow n m r.1))).map some
      rw [hrhalf] at hr2
      rw [hrhalf, negPow_halfPeriod, clause3_parityReadout_congr r.2.property
        (clause3_unit_norm hu (normalized_dihedralQubitState (2 ^ n) s
          ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) hr2, clause3_parityReadout_smul hu
        (dihedralQubitState (2 ^ n) s ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))
        (normalized_dihedralQubitState (2 ^ n) s
          ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))]

/-- For a reflection-hiding oracle, the actual dihedral sieve output distribution equals the
idealized sieve distribution indexed by the hidden shift [Kuperberg2005]. -/
theorem dihedralSieveBridge (n m : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    dihedralSieveActual n m f = (dihedralSieveRun n m s).1 := by
  classical
  have hstep1 : ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
      (actualSieveRec n m f m)).map (fun B => B.map (fun r => negPow n m r.1))
      = (idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m) := by
    rw [PMF.map_bind]
    rw [← dihedralFreshRecordLabels n f s hf (24 * 2 ^ (3 * m)), PMF.bind_map]
    refine clause3_bind_congr (p := actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))) ?_
    intro A hpos
    exact clause3_sieve_rec_transport n m f s m A
      (actualFreshRecords_family n f s hf (24 * 2 ^ (3 * m)) A hpos)
  have hA : dihedralSieveActual n m f
      = ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
          (actualSieveRec n m f m)).bind (actualReadout n) := rfl
  have hB : ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
      (actualSieveRec n m f m)).bind (actualReadout n)
      = ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
          (actualSieveRec n m f m)).bind
          (fun A => idealReadout n s (A.map (fun r => negPow n m r.1))) := by
    refine clause3_bind_congr
      (p := (actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
        (actualSieveRec n m f m)) ?_
    intro A hpos
    obtain ⟨A₀, h0, hrecpos⟩ := clause3_bind_pos_witness
      (actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))) (actualSieveRec n m f m) A hpos
    exact clause3_readout_transport n m s A
      (clause3_sieve_rec_support n m f s m A₀
        (actualFreshRecords_family n f s hf (24 * 2 ^ (3 * m)) A₀ h0) A hrecpos).1
  have hC : ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
      (actualSieveRec n m f m)).bind
      (fun A => idealReadout n s (A.map (fun r => negPow n m r.1)))
      = (dihedralSieveRun n m s).1 := by
    show ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
        (actualSieveRec n m f m)).bind
        ((idealReadout n s) ∘ (fun B => B.map (fun r => negPow n m r.1)))
      = (dihedralSieveRun n m s).1
    rw [← PMF.bind_map, hstep1]
    rfl
  rw [hA, hB, hC]

end G3

noncomputable section

/-- The real power of two with exponent two equals four. -/
private theorem num_checkpt_two_pow_two : (2:ℝ) ^ ((2:ℝ)) = 4 := by
  have h := Real.rpow_natCast (2:ℝ) 2
  simp only [Nat.cast_ofNat] at h
  rw [h, pow_two]
  norm_num

/-- The real power of two with exponent minus two equals one quarter. -/
private theorem num_checkpt_two_pow_neg_two : (2:ℝ) ^ (-(2:ℝ)) = 1 / 4 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), num_checkpt_two_pow_two, inv_eq_one_div]

/-- Every natural power of a real number in `[0,1]` is at most one. -/
private theorem num_checkpt_pow_le_one {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : ∀ n : ℕ, a ^ n ≤ 1 := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
    calc a ^ (k + 1) = a ^ k * a := pow_succ a k
      _ ≤ 1 * a := mul_le_mul_of_nonneg_right ih h0
      _ = a := by ring
      _ ≤ 1 := h1

/-- Every positive natural power of a real number in `[0,1]` is at most that number. -/
private theorem num_checkpt_pow_le_self {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    a ^ n ≤ a := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  calc a ^ (k + 1) = a ^ k * a := pow_succ a k
    _ ≤ 1 * a := mul_le_mul_of_nonneg_right (num_checkpt_pow_le_one h0 h1 k) h0
    _ = a := by ring

/-- If `0 < E ≤ 1` and `p*(2-E) ≤ E`, then `(1-E/2)^m*(1-p)` is at least `(1-E)^m` for `m ≥ 1`. -/
private theorem num_checkpt_merge_aux {E p : ℝ} (hE0 : 0 < E) (hE1 : E ≤ 1)
    (hkey : p * (2 - E) ≤ E) (m : ℕ) (hm : 1 ≤ m) :
    (1 - E / 2) ^ m * (1 - p) ≥ (1 - E) ^ m := by
  have h2E : 0 < 2 - E := by linarith
  have hd : p ≤ E / (2 - E) := by rwa [le_div_iff₀ h2E]
  have hsplit : (1 - E) = (1 - E / 2) * (1 - E / (2 - E)) := by
    field_simp
    ring
  have hnn : 0 ≤ E / (2 - E) := div_nonneg hE0.le h2E.le
  have hd1 : E / (2 - E) ≤ 1 := by
    rw [div_le_one h2E]
    linarith
  have hmono : (1 - E / (2 - E)) ^ m ≤ 1 - E / (2 - E) :=
    num_checkpt_pow_le_self (by linarith) (by linarith) hm
  have h12 : 0 ≤ 1 - E / 2 := by linarith
  have hfinal : (1 - E / 2) ^ m * (1 - E / (2 - E)) ^ m ≤ (1 - E / 2) ^ m * (1 - p) :=
    mul_le_mul_of_nonneg_left (le_trans hmono (by linarith)) (pow_nonneg h12 m)
  rw [hsplit, mul_pow]
  exact hfinal

/-- For `m ≥ 1`, the doubly exponential top-bit failure term satisfies the comparison needed to
merge it with the exponential layer error. -/
private theorem num_checkpt_epsTail (m : ℕ) (hm : 1 ≤ m) :
    (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) * (2 - Real.exp (-(2:ℝ) ^ ((m:ℝ) / 3 - 2)))
      ≤ Real.exp (-(2:ℝ) ^ ((m:ℝ) / 3 - 2)) := by
  have hp' : (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) = ((2:ℝ) ^ ((2 ^ m : ℕ)))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  have hlog : Real.log (2 * (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)))
      = Real.log 2 - ((2 ^ m : ℕ) : ℝ) * Real.log 2 := by
    rw [hp', Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt (by positivity)),
      Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hlog2half : (1/2:ℝ) < Real.log 2 := by
    have h1 : (1/2:ℝ) < 0.6931471803 := by norm_num
    linarith [h1, Real.log_two_gt_d9]
  have hN2 : (2:ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    have h : (2:ℕ) ^ 1 ≤ (2:ℕ) ^ m := pow_le_pow_right' (by norm_num) hm
    exact_mod_cast h
  have hm3 : 3 * ((m:ℝ) / 3) = (m:ℝ) := by ring
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have htm : (2:ℝ) ^ ((m:ℝ) / 3 - 2) ≤ (((2 ^ m : ℕ) : ℝ) - 1) * Real.log 2 := by
    have h1 : (2:ℝ) ^ ((m:ℝ) / 3 - 2) ≤ (2:ℝ) ^ ((m:ℝ) - 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith [hm3, hm0])
    have h2 : (2:ℝ) ^ ((m:ℝ) - 2) = (2:ℝ) ^ ((m:ℝ)) / 4 := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), num_checkpt_two_pow_two]
    have h3 : (2:ℝ) ^ ((m:ℝ)) = ((2 ^ m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    rw [h2, h3] at h1
    calc (2:ℝ) ^ ((m:ℝ) / 3 - 2) ≤ ((2 ^ m : ℕ) : ℝ) / 4 := h1
      _ ≤ (((2 ^ m : ℕ) : ℝ) - 1) * (1/2) := by linarith [hN2]
      _ ≤ (((2 ^ m : ℕ) : ℝ) - 1) * Real.log 2 :=
            mul_le_mul_of_nonneg_left hlog2half.le (by linarith [hN2])
  have hmain : 2 * (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ))
      ≤ Real.exp (-((2:ℝ) ^ ((m:ℝ) / 3 - 2))) := by
    have hp0 : 0 < (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
    have h2p : 0 < 2 * (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) :=
      mul_pos (by norm_num : (0:ℝ) < 2) hp0
    refine (Real.log_le_log_iff h2p (Real.exp_pos _)).mp ?_
    rw [Real.log_exp, hlog]
    have hexpnd : (((2 ^ m : ℕ) : ℝ) - 1) * Real.log 2
        = ((2 ^ m : ℕ) : ℝ) * Real.log 2 - Real.log 2 := by ring
    linarith [htm, hexpnd]
  have hfin : (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) * (2 - Real.exp (-((2:ℝ) ^ ((m:ℝ) / 3 - 2))))
      = 2 * (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ))
        - (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) * Real.exp (-((2:ℝ) ^ ((m:ℝ) / 3 - 2))) := by
    ring
  have hpE : 0 ≤ (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) * Real.exp (-((2:ℝ) ^ ((m:ℝ) / 3 - 2))) :=
    mul_nonneg (by positivity) (Real.exp_pos _).le
  linarith [hfin, hmain, hpE]

/-- For `m ≥ 1`, multiplying the layer-survival bound by the top-bit success factor is bounded
below by `(1-exp(-2^(m/3-2)))^m`. -/
private theorem num_checkpt_merge (m : ℕ) (hm : 1 ≤ m) :
    (1 - Real.exp (-(2:ℝ) ^ ((m:ℝ) / 3 - 2)) / 2) ^ m
      * (1 - (2:ℝ) ^ (-((2 ^ m : ℕ) : ℝ)))
      ≥ (1 - Real.exp (-(2:ℝ) ^ ((m:ℝ) / 3 - 2))) ^ m :=
  num_checkpt_merge_aux (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
    (num_checkpt_epsTail m hm) m hm

/-- For `m ≥ 1` and `j ≤ m-1`, the sum of `2^(i-4*m/3)` over `i < j` is at most `2^(-m/3-1)`. -/
private theorem num_checkpt_sumB (m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ m - 1) :
    (∑ i ∈ Finset.range j, (2:ℝ) ^ ((i:ℝ) - 4 * (m:ℝ) / 3))
      ≤ (2:ℝ) ^ (-(m:ℝ) / 3 - 1) := by
  have hp2 : (0:ℝ) < 2 := by norm_num
  have hterm : ∀ i : ℕ, (2:ℝ) ^ ((i:ℝ) - 4 * (m:ℝ) / 3)
      = (2:ℝ) ^ (-(4 * (m:ℝ) / 3)) * (2:ℝ) ^ (i:ℕ) := by
    intro i
    rw [show ((i:ℝ) - 4 * (m:ℝ) / 3) = (-(4 * (m:ℝ) / 3)) + (i:ℝ) from by ring,
      Real.rpow_add hp2, Real.rpow_natCast]
  simp only [hterm, ← Finset.mul_sum]
  have hsumj : ∀ k : ℕ, ∑ i ∈ Finset.range k, (2:ℝ) ^ (i:ℕ) ≤ (2:ℝ) ^ (k:ℕ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)) k]
  have hcast : (j:ℝ) ≤ (m:ℝ) - 1 := by
    have h1 : (((m:ℕ) - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    have h2 : (j:ℝ) ≤ (((m:ℕ) - 1 : ℕ) : ℝ) := by exact_mod_cast hj
    rw [h1] at h2
    exact h2
  have hm3 : 3 * ((m:ℝ) / 3) = (m:ℝ) := by ring
  calc (2:ℝ) ^ (-(4 * (m:ℝ) / 3)) * ∑ i ∈ Finset.range j, (2:ℝ) ^ (i:ℕ)
      ≤ (2:ℝ) ^ (-(4 * (m:ℝ) / 3)) * (2:ℝ) ^ (j:ℕ) :=
        mul_le_mul_of_nonneg_left (hsumj j) (by positivity)
    _ = (2:ℝ) ^ ((j:ℝ) - 4 * (m:ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hp2]
        congr 1
        ring
    _ ≤ (2:ℝ) ^ (-(m:ℝ) / 3 - 1) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ?_
        linarith [hcast, hm3]

/-- For `m ≥ 1` and `j ≤ m-1`, the stated concentration exponent is at least `2^(m/3-2) + log
2`. -/
private theorem num_checkpt_hoeffding (m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ m - 1) :
    (6 * (2:ℝ) ^ (3 * (m:ℝ) - 2 * (j:ℝ)) - (2:ℝ) ^ ((m:ℝ) - 1))
      * (2:ℝ) ^ (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1)
      ≥ (2:ℝ) ^ ((m:ℝ) / 3 - 2) + Real.log 2 := by
  have hp2 : (0:ℝ) < 2 := by norm_num
  have hp1 : (1:ℝ) ≤ 2 := by norm_num
  have keyA : (2:ℝ) ^ (3 * (m:ℝ) - 2 * (j:ℝ)) * (2:ℝ) ^ (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1)
      = (2:ℝ) ^ ((m:ℝ) / 3 - 2) * 2 := by
    have hE1 : (3 * (m:ℝ) - 2 * (j:ℝ)) + (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1)
        = ((m:ℝ) / 3 - 2) + 1 := by ring
    rw [← Real.rpow_add hp2, hE1, Real.rpow_add hp2, Real.rpow_one]
  have keyB : (2:ℝ) ^ ((m:ℝ) - 1) * (2:ℝ) ^ (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1)
      = (2:ℝ) ^ ((m:ℝ) / 3 - 2) * (2:ℝ) ^ (2 * (j:ℝ) - 2 * (m:ℝ)) := by
    have hE2 : ((m:ℝ) - 1) + (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1)
        = ((m:ℝ) / 3 - 2) + (2 * (j:ℝ) - 2 * (m:ℝ)) := by ring
    rw [← Real.rpow_add hp2, hE2, Real.rpow_add hp2]
  rw [show (6 * (2:ℝ) ^ (3 * (m:ℝ) - 2 * (j:ℝ)) - (2:ℝ) ^ ((m:ℝ) - 1))
        * (2:ℝ) ^ (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1)
      = 6 * ((2:ℝ) ^ (3 * (m:ℝ) - 2 * (j:ℝ)) * (2:ℝ) ^ (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1))
        - (2:ℝ) ^ ((m:ℝ) - 1) * (2:ℝ) ^ (2 * (j:ℝ) - 8 * (m:ℝ) / 3 - 1) from by ring,
    keyA, keyB]
  have hcast : (j:ℝ) ≤ (m:ℝ) - 1 := by
    have h1 : (((m:ℕ) - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    have h2 : (j:ℝ) ≤ (((m:ℕ) - 1 : ℕ) : ℝ) := by exact_mod_cast hj
    rw [h1] at h2
    exact h2
  have hq : (2:ℝ) ^ (2 * (j:ℝ) - 2 * (m:ℝ)) ≤ 1/4 := by
    have hexpl : 2 * (j:ℝ) - 2 * (m:ℝ) ≤ -(2:ℝ) := by linarith
    have hle := Real.rpow_le_rpow_of_exponent_le hp1 hexpl
    rwa [num_checkpt_two_pow_neg_two] at hle
  have hw : (1/4) ≤ (2:ℝ) ^ ((m:ℝ) / 3 - 2) := by
    have hm3 : 3 * ((m:ℝ) / 3) = (m:ℝ) := by ring
    have hnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have hexpw : (-(2:ℝ)) ≤ (m:ℝ) / 3 - 2 := by
      have h3 : (0:ℝ) ≤ (m:ℝ) / 3 := div_nonneg hnn (by norm_num)
      linarith
    calc (1/4) = (2:ℝ) ^ (-(2:ℝ)) := (num_checkpt_two_pow_neg_two).symm
      _ ≤ (2:ℝ) ^ ((m:ℝ) / 3 - 2) := Real.rpow_le_rpow_of_exponent_le hp1 hexpw
  have hprod : (2:ℝ) ^ ((m:ℝ) / 3 - 2) * (2:ℝ) ^ (2 * (j:ℝ) - 2 * (m:ℝ))
      ≤ (2:ℝ) ^ ((m:ℝ) / 3 - 2) * (1/4) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  linarith [hprod, hw, Real.log_two_lt_d9]

/-- A nonzero mass in a bind has an intermediate value with nonzero outer and conditional
masses. -/
private theorem exists_of_bind_ne_zero {α β : Type} {p : PMF α} {f : α → PMF β} {b : β}
    (h : p.bind f b ≠ 0) : ∃ a, p a ≠ 0 ∧ f a b ≠ 0 := by
  rw [PMF.bind_apply] at h
  by_contra hcon
  apply h
  apply ENNReal.tsum_eq_zero.2
  intro a
  by_cases ha : p a = 0
  · rw [ha, zero_mul]
  · have h2 : f a b = 0 := by
      by_contra h2
      exact hcon ⟨a, ha, h2⟩
    rw [h2, mul_zero]

/-- A point with nonzero mapped mass has a preimage of nonzero mass. -/
private theorem exists_of_map_ne_zero {α β : Type} {p : PMF α} {f : α → β} {b : β}
    (h : p.map f b ≠ 0) : ∃ a, p a ≠ 0 ∧ f a = b := by
  rw [PMF.map_apply] at h
  by_contra hcon
  apply h
  apply ENNReal.tsum_eq_zero.2
  intro a
  by_cases hb : b = f a
  · rw [if_pos hb]
    by_contra ha0
    exact hcon ⟨a, ha0, hb.symm⟩
  · rw [if_neg hb]

/-- A point with nonzero mass in a pure distribution equals its distinguished value. -/
private theorem eq_of_pure_ne_zero {α : Type} {a b : α} (h : PMF.pure a b ≠ 0) : b = a := by
  by_contra hab
  rw [PMF.pure_apply, if_neg hab] at h
  exact h rfl

/-- Subtracting window-agreeing labels with `t` zero low bits gives `t+w` zero low bits when the
window fits in the label. -/
private theorem zeroBitsGE_sub_of_windowAgree {n t w : ℕ} {r r' : ZMod (2 ^ n)}
    (hr : zeroBitsGE n t r) (hr' : zeroBitsGE n t r') (hw : windowAgree n w t r r')
    (htw : t + w ≤ n) : zeroBitsGE n (t + w) (r' - r) := by
  have hmodeq : r.val ≡ r'.val [MOD 2 ^ (t + w)] := by
    have hdiv : r.val = 2 ^ t * (r.val / 2 ^ t) :=
      (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hr)).symm
    have hdiv' : r'.val = 2 ^ t * (r'.val / 2 ^ t) :=
      (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hr')).symm
    have hwin : r.val / 2 ^ t ≡ r'.val / 2 ^ t [MOD 2 ^ w] := hw
    have h := hwin.mul_left' (2 ^ t)
    rw [← pow_add] at h
    rwa [← hdiv, ← hdiv'] at h
  show (r' - r).val % 2 ^ (t + w) = 0
  rcases le_total r.val r'.val with hle | hle
  · obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hle).mp hmodeq
    rw [ZMod.val_sub hle, hd]
    exact Nat.mul_mod_right _ _
  · rcases eq_or_lt_of_le hle with heq | hlt
    · have hrr : r' = r := ZMod.val_injective _ heq
      subst hrr
      rw [sub_self, ZMod.val_zero]
      exact Nat.zero_mod _
    · obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).mp hmodeq.symm
      have hne : r - r' ≠ 0 := by
        intro h0
        have h1 : r = r' := sub_eq_zero.mp h0
        subst h1
        exact absurd hlt (lt_irrefl _)
      haveI : NeZero (r - r') := ⟨hne⟩
      have hval : (r' - r).val = 2 ^ n - (r.val - r'.val) := by
        rw [show r' - r = -(r - r') from (neg_sub r r').symm,
          ZMod.val_neg_of_ne_zero (r - r'), ZMod.val_sub (Nat.le_of_lt hlt)]
      have hd_bound : d < 2 ^ (n - t - w) := by
        have h2 : r.val - r'.val < 2 ^ n := by
          have := ZMod.val_lt r
          omega
        have h3 : 2 ^ n = 2 ^ (t + w) * 2 ^ (n - t - w) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hd, h3] at h2
        exact Nat.lt_of_mul_lt_mul_left h2
      have hfact : 2 ^ n - (r.val - r'.val) = 2 ^ (t + w) * (2 ^ (n - t - w) - d) := by
        rw [Nat.mul_sub_left_distrib, ← pow_add, show t + w + (n - t - w) = n from by omega,
          ← hd]
      rw [hval, hfact]
      exact Nat.mul_mod_right _ _

/-- Each selected pair consists of input elements whose labels agree in the selected window. -/
private theorem sievePairWith_mem_window {n : ℕ} {α : Type} [DecidableEq α]
    {label : α → ZMod (2^n)} {w t : ℕ} {L : List α} :
    ∀ p : α × α, p ∈ sievePairWith n label w t L →
      p.1 ∈ L ∧ p.2 ∈ L ∧ windowAgree n w t (label p.1) (label p.2) := by
  fun_induction sievePairWith n label w t L
  · intro p hp
    simp at hp
  · rename_i r rest hfind ih
    intro p hp
    obtain ⟨h1, h2, h3⟩ := ih p hp
    exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3⟩
  · rename_i r rest r' hfind ih
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with hp | hp
    · subst hp
      have hm : r' ∈ rest := List.mem_of_find?_eq_some hfind
      have hwin : windowAgree n w t (label r) (label r') := by
        simpa only [decide_eq_true_eq] using! List.find?_some hfind
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hm, hwin⟩
    · obtain ⟨h1, h2, h3⟩ := ih p hp
      exact ⟨List.mem_cons_of_mem _ (List.mem_of_mem_erase h1),
        List.mem_cons_of_mem _ (List.mem_of_mem_erase h2), h3⟩

/-- Every label in a nonzero-probability ideal auxiliary output is the second label minus the
first label of some input pair. -/
private theorem idealLayerAux_mem {n : ℕ} :
    ∀ (ps : List (ZMod (2^n) × ZMod (2^n))) {L : List (ZMod (2^n))},
      (idealLayerAux n ps) L ≠ 0 → ∀ k ∈ L, ∃ p ∈ ps, k = p.2 - p.1 := by
  intro ps
  induction ps with
  | nil =>
    intro L h
    have hL : L = [] := by
      change (PMF.pure ([] : List (ZMod (2^n)))) L ≠ 0 at h
      exact eq_of_pure_ne_zero h
    subst hL
    intro k hk
    simp at hk
  | cons p ps ih =>
    obtain ⟨r, r'⟩ := p
    intro L h k hk
    change ((PMF.uniformOfFintype' (Fin 2)).bind fun b =>
      (idealLayerAux n ps).map fun tail => if b = 1 then (r' - r) :: tail else tail) L ≠ 0 at h
    obtain ⟨b, _hb1, hb2⟩ := exists_of_bind_ne_zero h
    obtain ⟨tail, htail, hL⟩ := exists_of_map_ne_zero hb2
    subst hL
    have hrec : ∀ k ∈ tail, ∃ p ∈ ps, k = p.2 - p.1 := ih htail
    by_cases hb : b = 1
    · rw [if_pos hb] at hk
      rw [List.mem_cons] at hk
      rcases hk with hk | hk
      · exact ⟨(r, r'), List.mem_cons_self, by rw [hk]⟩
      · obtain ⟨p', hp', hk'⟩ := hrec k hk
        exact ⟨p', List.mem_cons_of_mem _ hp', hk'⟩
    · rw [if_neg hb] at hk
      obtain ⟨p', hp', hk'⟩ := hrec k hk
      exact ⟨p', List.mem_cons_of_mem _ hp', hk'⟩

/-- Every nonzero-probability ideal auxiliary output has length at most the number of input
pairs. -/
private theorem idealLayerAux_len_le {n : ℕ} :
    ∀ (ps : List (ZMod (2^n) × ZMod (2^n))) {L : List (ZMod (2^n))},
      (idealLayerAux n ps) L ≠ 0 → L.length ≤ ps.length := by
  intro ps
  induction ps with
  | nil =>
    intro L h
    have hL : L = [] := by
      change (PMF.pure ([] : List (ZMod (2^n)))) L ≠ 0 at h
      exact eq_of_pure_ne_zero h
    subst hL
    simp
  | cons p ps ih =>
    obtain ⟨r, r'⟩ := p
    intro L h
    change ((PMF.uniformOfFintype' (Fin 2)).bind fun b =>
      (idealLayerAux n ps).map fun tail => if b = 1 then (r' - r) :: tail else tail) L ≠ 0 at h
    obtain ⟨b, _hb1, hb2⟩ := exists_of_bind_ne_zero h
    obtain ⟨tail, htail, hL⟩ := exists_of_map_ne_zero hb2
    subst hL
    have hrec : tail.length ≤ ps.length := ih htail
    by_cases hb : b = 1
    · rw [if_pos hb, List.length_cons, List.length_cons]
      omega
    · rw [if_neg hb, List.length_cons]
      omega

/-- Every label in a nonzero-probability ideal recursive output has at least the stage's capped
number of zero low bits. -/
private theorem idealSieveRec_zeroBits {n m : ℕ} :
    ∀ (j : ℕ) {L L' : List (ZMod (2^n))},
      (idealSieveRec n m j L) L' ≠ 0 → ∀ k ∈ L', zeroBitsGE n (min (m * j) (n - 1)) k := by
  intro j
  induction j with
  | zero =>
    intro L L' h k hk
    have hL : L' = L := by
      change (PMF.pure L) L' ≠ 0 at h
      exact eq_of_pure_ne_zero h
    subst hL
    show k.val % 2 ^ min (m * 0) (n - 1) = 0
    rw [Nat.mul_zero, min_eq_left (Nat.zero_le _), pow_zero]
    exact Nat.mod_one _
  | succ j ih =>
    intro L L' h k hk
    change ((idealSieveRec n m j L).bind (idealLayer n m j)) L' ≠ 0 at h
    obtain ⟨L'', h1, h2⟩ := exists_of_bind_ne_zero h
    have hk' : ∃ p ∈ sievePair n (sieveWindowWidth n m j) (m * j) L'', k = p.2 - p.1 :=
      idealLayerAux_mem _ h2 k hk
    obtain ⟨p, hp, hpk⟩ := hk'
    obtain ⟨hpm1, hpm2, hwin⟩ := sievePairWith_mem_window (label := id) p hp
    have hz1 : zeroBitsGE n (min (m * j) (n - 1)) p.1 := ih h1 p.1 hpm1
    have hz2 : zeroBitsGE n (min (m * j) (n - 1)) p.2 := ih h1 p.2 hpm2
    subst hpk
    by_cases hcase : m * j ≤ n - 1
    · have htw : m * j + sieveWindowWidth n m j = min (m * (j + 1)) (n - 1) := by
        unfold sieveWindowWidth
        rw [Nat.mul_succ]
        omega
      rw [← htw]
      apply zeroBitsGE_sub_of_windowAgree
      · rwa [min_eq_left hcase] at hz1
      · rwa [min_eq_left hcase] at hz2
      · exact hwin
      · rw [htw]
        exact le_trans (min_le_right _ _) (Nat.sub_le n 1)
    · have hlt : n - 1 < m * j := lt_of_not_ge hcase
      have hle : n - 1 ≤ m * j := Nat.le_of_lt hlt
      have hmin1 : min (m * j) (n - 1) = n - 1 := min_eq_right hle
      have hmin2 : min (m * (j + 1)) (n - 1) = n - 1 :=
        min_eq_right (le_trans hle (Nat.mul_le_mul_left m (Nat.le_succ j)))
      rw [hmin2]
      have hwin' : windowAgree n 0 (n - 1) p.1 p.2 := by
        show (p.1.val / 2 ^ (n - 1)) % 2 ^ 0 = (p.2.val / 2 ^ (n - 1)) % 2 ^ 0
        rw [pow_zero, Nat.mod_one, Nat.mod_one]
      rw [hmin1] at hz1 hz2
      have hz := zeroBitsGE_sub_of_windowAgree hz1 hz2 hwin' (by
        rw [Nat.add_zero]
        exact Nat.sub_le n 1)
      rwa [Nat.add_zero] at hz

/-- If `n ≥ 1` and `n-1 ≤ m*m`, every label remaining after `m` ideal sieve stages is zero or
the half-period label. -/
private theorem idealSieveRec_zero_or_half {n m : ℕ} (hn : 1 ≤ n) (hmm : n - 1 ≤ m * m)
    {L L' : List (ZMod (2^n))} (h : (idealSieveRec n m m L) L' ≠ 0) :
    ∀ k ∈ L', k = 0 ∨ k = ((2 ^ (n - 1) : ℕ) : ZMod (2^n)) := by
  intro k hk
  have hz : zeroBitsGE n (min (m * m) (n - 1)) k := idealSieveRec_zeroBits m h k hk
  rw [min_eq_right hmm] at hz
  have hlt : k.val < 2 ^ n := ZMod.val_lt k
  have h2n : 2 ^ n = 2 ^ (n - 1) * 2 := by
    calc 2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
      _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
  have hdecomp : k.val = 2 ^ (n - 1) * (k.val / 2 ^ (n - 1)) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hz)).symm
  have hq2 : k.val / 2 ^ (n - 1) < 2 := by
    have h1 : 2 ^ (n - 1) * (k.val / 2 ^ (n - 1)) < 2 ^ (n - 1) * 2 := by
      calc 2 ^ (n - 1) * (k.val / 2 ^ (n - 1)) = k.val := hdecomp.symm
        _ < 2 ^ n := hlt
        _ = 2 ^ (n - 1) * 2 := h2n
    exact Nat.lt_of_mul_lt_mul_left h1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq2) with hq0 | hq1
  · left
    apply ZMod.val_injective _
    rw [hdecomp, hq0, mul_zero]
    exact (ZMod.val_zero).symm
  · right
    apply ZMod.val_injective _
    rw [hdecomp, hq1, mul_one]
    exact (ZMod.val_cast_of_lt (by rw [h2n]; omega : 2 ^ (n - 1) < 2 ^ n)).symm

/-- The deterministic list of child records obtained by retaining a pair's child exactly when
its corresponding tape entry equals one. -/
private def layerRunGen {α : Type} (child : α × α → α) :
    List (α × α) → (ℕ → Fin 2) → List α
  | [], _ => []
  | p :: ps, c => (if c 0 = 1 then [child p] else []) ++ layerRunGen child ps (fun i => c (i + 1))

/-- Deterministic layer execution depends only on tape entries indexed below the number of input
pairs. -/
private theorem layerRunGen_congr {α : Type} (child : α × α → α) :
    ∀ (ps : List (α × α)) (c₁ c₂ : ℕ → Fin 2),
      (∀ i, i < ps.length → c₁ i = c₂ i) → layerRunGen child ps c₁ = layerRunGen child ps c₂ := by
  intro ps
  induction ps with
  | nil => intro c₁ c₂ _; rfl
  | cons p ps ih =>
    intro c₁ c₂ h
    have h0 : c₁ 0 = c₂ 0 := h 0 (Nat.succ_pos _)
    have hrest : ∀ i, i < ps.length → (fun j => c₁ (j + 1)) i = (fun j => c₂ (j + 1)) i := by
      intro i hi
      exact h (i + 1) (by rw [List.length_cons]; omega)
    show (if c₁ 0 = 1 then [child p] else []) ++ layerRunGen child ps (fun i => c₁ (i + 1)) =
      (if c₂ 0 = 1 then [child p] else []) ++ layerRunGen child ps (fun i => c₂ (i + 1))
    rw [h0, ih _ _ hrest]

/-- Extension of a finite binary tape to natural indices by setting every entry beyond its
length to zero. -/
private def coinLift {k : ℕ} (c : Fin k → Fin 2) : ℕ → Fin 2 :=
  fun i => if h : i < k then c ⟨i, h⟩ else 0

/-- The extended tape agrees with the original finite tape at every in-range index. -/
private theorem coinLift_lt {k : ℕ} (c : Fin k → Fin 2) {i : ℕ} (hi : i < k) :
    coinLift c i = c ⟨i, hi⟩ := dif_pos hi

/-- The two successor-index representations give the same sum of binary keep indicators. -/
private theorem sum_succ_shift_eq {P : ℕ} (c : ℕ → Fin 2) :
    (∑ i : Fin P, (if c ((i : ℕ) + 1) = 1 then (1 : ℕ) else 0)) =
      ∑ i : Fin P, (if c ((i.succ : ℕ)) = 1 then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.val_succ]

/-- The deterministic layer output length equals the sum of its binary keep indicators. -/
private theorem layerRunGen_length {α : Type} (child : α × α → α) :
    ∀ (ps : List (α × α)) (c : ℕ → Fin 2),
      (layerRunGen child ps c).length = ∑ i : Fin ps.length, (if c i = 1 then 1 else 0) := by
  intro ps
  induction ps with
  | nil =>
    intro c
    show ([] : List α).length = _
    simp
  | cons p ps ih =>
    intro c
    show ((if c 0 = 1 then [child p] else []) ++ layerRunGen child ps (fun i => c (i + 1))).length =
      ∑ i : Fin (ps.length + 1), (if c i = 1 then 1 else 0)
    rw [List.length_append, ih, Fin.sum_univ_succ]
    show (if c 0 = 1 then [child p] else []).length +
        (∑ i : Fin ps.length, if c ((i : ℕ) + 1) = 1 then 1 else 0) =
      (if c ((0 : Fin (ps.length + 1)) : ℕ) = 1 then 1 else 0) +
        ∑ i : Fin ps.length, if c ((i.succ : ℕ)) = 1 then 1 else 0
    rw [sum_succ_shift_eq c]
    by_cases h1 : c 0 = 1
    · have h1' : c ((0 : Fin (ps.length + 1)) : ℕ) = 1 := h1
      rw [if_pos h1, if_pos h1', List.length_singleton]
    · have h1' : ¬c ((0 : Fin (ps.length + 1)) : ℕ) = 1 := h1
      rw [if_neg h1, if_neg h1', List.length_nil]

/-- The real-valued deterministic layer output length equals the sum of its real-valued keep
indicators. -/
private theorem layerRunGen_length_real {α : Type} (child : α × α → α)
    (ps : List (α × α)) (c : ℕ → Fin 2) :
    ((layerRunGen child ps c).length : ℝ) =
      ∑ i : Fin ps.length, (if c i = 1 then (1 : ℝ) else 0) := by
  rw [layerRunGen_length]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = 1 <;> simp [h]

/-- The finite probability distribution assigning probability one half to each element of `Fin
2`. -/
private def uniformFin2 : FinDist (Fin 2) where
  prob := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by rw [Fin.sum_univ_two]; norm_num

/-- Each outcome of `uniformFin2` has probability one half. -/
private theorem uniformFin2_prob (x : Fin 2) : uniformFin2.prob x = 1 / 2 := rfl

/-- The keep indicator has expectation one half under `uniformFin2`. -/
private theorem uniformFin2_expect_keep :
    uniformFin2.expect (fun x => if x = 1 then (1 : ℝ) else 0) = 1 / 2 := by
  rw [FinDist.expect, Fin.sum_univ_two]
  norm_num [uniformFin2]

/-- Prepending a value to a function indexed by `Fin k`, producing a function indexed by `Fin
(k+1)`. -/
private def consFn {X : Type} {k : ℕ} (x : X) (ω : Fin k → X) : Fin (k + 1) → X :=
  Fin.cons x ω

/-- The value at zero of `consFn x ω` is `x`. -/
private theorem consFn_zero {X : Type} {k : ℕ} (x : X) (ω : Fin k → X) :
    consFn x ω 0 = x := rfl

/-- The successor entries of `consFn x ω` are the entries of `ω`. -/
private theorem consFn_succ {X : Type} {k : ℕ} (x : X) (ω : Fin k → X) (i : Fin k) :
    consFn x ω i.succ = ω i := rfl

/-- Prepending a finite function's first value to its tail reconstructs the function. -/
private theorem consFn_self_tail {X : Type} {k : ℕ} (ω : Fin (k + 1) → X) :
    consFn (ω 0) (Fin.tail ω) = ω := Fin.cons_self_tail ω

/-- A uniform finite function can be sampled by independently sampling its first entry and its
remaining entries. -/
private theorem uniform_fin_succ_split (X : Type) [Fintype X] [Nonempty X] (k : ℕ) :
    PMF.uniformOfFintype' (Fin (k + 1) → X) =
      (PMF.uniformOfFintype' X).bind fun x =>
        (PMF.uniformOfFintype' (Fin k → X)).map (consFn x) := by
  have ha0 : (Fintype.card X : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have haT : (Fintype.card X : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext ω
  rw [PMF.bind_apply, tsum_eq_single (ω 0) (fun x hx => by
    have hm : ((PMF.uniformOfFintype' (Fin k → X)).map (consFn x)) ω = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.2
      intro ω'
      have hne2 : ¬ ω = consFn x ω' := by
        intro hcon
        apply hx
        have h1 : ω 0 = x := congrFun hcon 0
        exact h1.symm
      simp only [hne2, if_false]
    rw [hm, mul_zero])]
  rw [PMF.map_apply, tsum_eq_single (Fin.tail ω) (fun ω' hne => by
    have hne2 : ¬ ω = consFn (ω 0) ω' := by
      intro hcon
      apply hne
      funext i
      have h1 : ω i.succ = ω' i := congrFun hcon i.succ
      exact h1.symm
    rw [if_neg hne2])]
  · rw [if_pos (consFn_self_tail ω).symm, PMF.uniformOfFintype'_apply, PMF.uniformOfFintype'_apply,
      PMF.uniformOfFintype'_apply]
    have hcard : Fintype.card (Fin (k + 1) → X) = Fintype.card X * Fintype.card (Fin k → X) := by
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_succ,
        Nat.mul_comm]
    rw [hcard, Nat.cast_mul]
    exact ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)

/-- The ideal auxiliary layer law is the image of a uniform finite binary tape under
deterministic keep-or-discard execution. -/
private theorem idealLayerAux_eq_map_run {n : ℕ} :
    ∀ (ps : List (ZMod (2^n) × ZMod (2^n))),
      idealLayerAux n ps = (PMF.uniformOfFintype' (Fin ps.length → Fin 2)).map
        (fun c => layerRunGen (fun p => p.2 - p.1) ps (coinLift c)) := by
  intro ps
  induction ps with
  | nil =>
    ext L
    change (PMF.pure ([] : List (ZMod (2^n)))) L = _
    rw [List.length_nil, PMF.map_apply]
    have hrun : ∀ ω : Fin 0 → Fin 2,
        layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
          ([] : List (ZMod (2^n) × ZMod (2^n))) (coinLift ω) = [] := fun _ => rfl
    simp_rw [hrun]
    by_cases h : L = []
    · subst h
      rw [PMF.pure_apply_self]
      rw [show (∑' ω : Fin 0 → Fin 2,
          if ([] : List (ZMod (2^n))) = [] then (PMF.uniformOfFintype' (Fin 0 → Fin 2)) ω
            else 0)
          = ∑' ω : Fin 0 → Fin 2, (PMF.uniformOfFintype' (Fin 0 → Fin 2)) ω
        from tsum_congr fun ω => if_pos rfl]
      rw [PMF.tsum_coe]
    · rw [PMF.pure_apply, if_neg h]
      rw [show (∑' ω : Fin 0 → Fin 2,
          if L = [] then (PMF.uniformOfFintype' (Fin 0 → Fin 2)) ω else 0) = 0
        from ENNReal.tsum_eq_zero.2 fun ω => if_neg h]
  | cons p ps ih =>
    obtain ⟨r, r'⟩ := p
    change (PMF.uniformOfFintype' (Fin 2)).bind (fun b =>
      (idealLayerAux n ps).map fun tail => if b = 1 then (r' - r) :: tail else tail) = _
    rw [List.length_cons, uniform_fin_succ_split (Fin 2) ps.length, PMF.map_bind]
    ext L
    simp only [PMF.bind_apply]
    apply tsum_congr
    intro b
    congr 1
    congr 1
    rw [PMF.map_comp]
    have hfun : (fun c => layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
            ((r, r') :: ps) (coinLift c)) ∘ consFn b
        = (fun tail => if b = 1 then (r' - r) :: tail else tail) ∘
          (fun c : Fin ps.length → Fin 2 => layerRunGen
            (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ps (coinLift c)) := by
      funext ω
      show layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ((r, r') :: ps)
          (coinLift (consFn b ω)) = _
      show (if coinLift (consFn b ω) 0 = 1 then [(r' - r)] else []) ++
          layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ps
            (fun i => coinLift (consFn b ω) (i + 1)) = _
      have h0 : coinLift (consFn b ω) 0 = b := by
        rw [coinLift_lt _ (Nat.succ_pos _)]
        exact consFn_zero b ω
      have hrest : (fun i => coinLift (consFn b ω) (i + 1)) = coinLift ω := by
        funext i
        show coinLift (consFn b ω) (i + 1) = coinLift ω i
        by_cases hi : i < ps.length
        · rw [coinLift_lt _ (by omega : i + 1 < ps.length + 1), coinLift_lt _ hi]
          exact consFn_succ b ω ⟨i, hi⟩
        · have e1 : coinLift (consFn b ω) (i + 1) = 0 :=
            dif_neg (by omega : ¬ i + 1 < ps.length + 1)
          have e2 : coinLift ω i = 0 := dif_neg hi
          rw [e1, e2]
      rw [h0, hrest]
      show (if b = 1 then [r' - r] else []) ++
          layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ps (coinLift ω) =
        if b = 1 then (r' - r) :: layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ps
            (coinLift ω)
          else layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ps (coinLift ω)
      by_cases hb : b = 1
      · simp [hb]
      · simp [hb]
    rw [hfun, ← PMF.map_comp, ← ih]

/-- The probability of an event under a mapped probability mass function equals the probability
of its preimage. -/
private theorem pmf_map_event {α β : Type} (μ : PMF α) (f : α → β) (Q : β → Prop) [DecidablePred Q] :
    (∑' b, if Q b then μ.map f b else 0) = ∑' a, if Q (f a) then μ a else 0 := by
  have step : ∀ b, (if Q b then μ.map f b else 0) =
      ∑' a, if Q b then (if b = f a then μ a else 0) else 0 := by
    intro b
    by_cases hQ : Q b
    · rw [if_pos hQ, PMF.map_apply]
      apply tsum_congr
      intro a
      by_cases hb : b = f a
      · rw [if_pos hb, if_pos hQ]
      · rw [if_neg hb, if_pos hQ]
    · rw [if_neg hQ]
      exact (ENNReal.tsum_eq_zero.2 fun a => if_neg hQ).symm
  rw [tsum_congr step, ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  by_cases ha : Q (f a)
  · rw [if_pos ha]
    rw [tsum_eq_single (f a) (fun b hb => by
      by_cases hQ : Q b
      · rw [if_pos hQ, if_neg hb]
      · rw [if_neg hQ])]
    rw [if_pos ha, if_pos rfl]
  · rw [if_neg ha]
    apply ENNReal.tsum_eq_zero.2
    intro b
    by_cases hb : b = f a
    · have h1 : ¬ Q b := fun h => ha (hb ▸ h)
      rw [if_neg h1]
    · by_cases hQb : Q b
      · rw [if_pos hQb, if_neg hb]
      · rw [if_neg hQb]

/-- For `b > 0`, the probability that an ideal auxiliary layer keeps at most `(1-b)` times half
the input pairs is at most `exp(-b^2*ps.length/2)`. -/
private theorem layer_len_tail {n : ℕ} (ps : List (ZMod (2^n) × ZMod (2^n))) (b : ℝ) (hb : 0 < b) :
    (∑' L : List (ZMod (2^n)),
      if ((L.length : ℝ) ≤ (1 - b) * ((ps.length : ℝ) / 2)) then (idealLayerAux n ps) L else 0)
      ≤ ENNReal.ofReal (Real.exp (-(b ^ 2 * (ps.length : ℝ) / 2))) := by
  by_cases hP : ps.length = 0
  · rw [List.length_eq_zero_iff] at hP
    subst hP
    simp only [List.length_nil, Nat.cast_zero, zero_div, mul_zero]
    rw [show (fun L : List (ZMod (2^n)) =>
          if (L.length : ℝ) ≤ 0 then (idealLayerAux n []) L else 0)
        = fun L => if L = [] then (PMF.pure ([] : List (ZMod (2^n)))) L else 0 from by
      funext L
      by_cases hL : L = []
      · subst hL
        rw [if_pos (by simp), if_pos rfl]
        rfl
      · rw [if_neg hL, if_neg (show ¬ (L.length : ℝ) ≤ 0 from fun hle =>
          hL (List.length_eq_zero_iff.mp (Nat.cast_nonpos.mp hle)))]]
    rw [tsum_eq_single ([] : List (ZMod (2^n))) (fun L hL => by rw [if_neg hL]), if_pos rfl,
      PMF.pure_apply_self]
    rw [neg_zero, Real.exp_zero, ENNReal.ofReal_one]
  · have hP1 : 1 ≤ ps.length := Nat.one_le_iff_ne_zero.mpr hP
    rw [idealLayerAux_eq_map_run ps, pmf_map_event]

    set P := ps.length with hPdef
    set run := fun c : Fin P → Fin 2 =>
      layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ps (coinLift c) with hrundef
    set Q' : (Fin P → Fin 2) → Prop := fun ω => ((run ω).length : ℝ) ≤ (1 - b) * (P / 2 : ℝ)
      with hQ'def

    have hmass : (∑' ω : Fin P → Fin 2, if Q' ω then (PMF.uniformOfFintype' (Fin P → Fin 2)) ω
        else 0)
        = ((Finset.univ.filter Q').card : ENNReal) * ((2 ^ P : ℕ) : ENNReal)⁻¹ := by
      rw [tsum_fintype]
      rw [show (∑ ω : Fin P → Fin 2, if Q' ω then (PMF.uniformOfFintype' (Fin P → Fin 2)) ω else 0)
          = ∑ ω ∈ Finset.univ.filter Q', (PMF.uniformOfFintype' (Fin P → Fin 2)) ω from
        (Finset.sum_filter _ _).symm]
      simp_rw [PMF.uniformOfFintype'_apply]
      rw [Finset.sum_const]
      rw [show (Fintype.card (Fin P → Fin 2)) = 2 ^ P from by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]]
      rw [nsmul_eq_mul]
    rw [hmass]

    set plaw : Fin P → FinDist (Fin 2) := fun _ => uniformFin2 with hplawdef
    have hprob : ∀ ω : Fin P → Fin 2, (independentSampleLaw plaw).prob ω = (1 / 2) ^ P := by
      intro ω
      show ∏ i : Fin P, (plaw i).prob (ω i) = _
      rw [show (∏ i : Fin P, (plaw i).prob (ω i)) = ∏ i : Fin P, (1 / 2 : ℝ) from
        Finset.prod_congr rfl (fun i _ => rfl)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

    set cnt : (Fin P → Fin 2) → ℝ := fun ω => ((run ω).length : ℝ) with hcntdef
    have hcnt_eq : ∀ ω : Fin P → Fin 2, cnt ω = ∑ i : Fin P, (if ω i = 1 then (1 : ℝ) else 0) := by
      intro ω
      show ((run ω).length : ℝ) = _
      show ((layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1) ps
          (coinLift ω)).length : ℝ) = _
      rw [layerRunGen_length_real]
      apply Finset.sum_congr rfl
      intro i _
      have hc : coinLift ω (i : ℕ) = ω i := coinLift_lt ω i.isLt
      rw [hc]
    have hexp : (independentSampleLaw plaw).expect cnt = P / 2 := by
      have hsum_eq : cnt = weightedSampleSum (fun _ : Fin P => (1 : ℝ))
          (fun _ x => if x = 1 then (1 : ℝ) else 0) := by
        funext ω
        rw [hcnt_eq ω]
        show (∑ i : Fin P, (if ω i = 1 then (1 : ℝ) else 0)) =
            ∑ i : Fin P, (1 : ℝ) * (if ω i = 1 then (1 : ℝ) else 0)
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : ω i = 1 <;> simp [hi]
      rw [hsum_eq, independent_weighted_expectation]
      show (∑ i : Fin P, (1 : ℝ) * (plaw i).expect (fun x => if x = 1 then (1 : ℝ) else 0))
          = (P : ℝ) / 2
      rw [show (∑ i : Fin P, (1 : ℝ) * (plaw i).expect (fun x => if x = 1 then (1 : ℝ) else 0))
          = ∑ i : Fin P, (1 / 2 : ℝ) from by
        apply Finset.sum_congr rfl
        intro i _
        rw [one_mul]
        exact uniformFin2_expect_keep]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hS : (0 : ℝ) < ∑ i : Fin P, (1 : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one]
      exact Nat.cast_pos.mpr (by omega)

    have hdiff : ∀ (i : Fin P) (ω τ : Fin P → Fin 2), (∀ j, j ≠ i → ω j = τ j) →
        |(fun ω => -cnt ω) ω - (fun ω => -cnt ω) τ| ≤ 1 := by
      intro i ω τ hωτ
      simp only
      rw [hcnt_eq ω, hcnt_eq τ]
      have hsum : (∑ j : Fin P, (if ω j = 1 then (1 : ℝ) else 0)) -
          (∑ j : Fin P, (if τ j = 1 then (1 : ℝ) else 0)) =
          (if ω i = 1 then (1 : ℝ) else 0) - (if τ i = 1 then (1 : ℝ) else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_eq_single i
        · intro j _ hj
          rw [hωτ j hj]
          simp
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [neg_sub_neg, abs_sub_comm, hsum]
      by_cases h1 : ω i = 1 <;> by_cases h2 : τ i = 1 <;> simp [h1, h2]
    have htail := (finite_product_bounded_differences_tail (Fin 2) P plaw (fun ω => -cnt ω)
      (fun _ => 1) (b * (P / 2)) (fun _ => zero_le_one) hS (by positivity) hdiff).1

    have hmean : (independentSampleLaw plaw).expect (fun ω => -cnt ω) = -P / 2 := by
      have : (independentSampleLaw plaw).expect (fun ω => -cnt ω) =
          -(independentSampleLaw plaw).expect cnt := by
        rw [FinDist.expect, FinDist.expect, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      rw [this, hexp]
      ring
    rw [hmean] at htail

    have hfilter : Finset.univ.filter (fun ω => -P / 2 + b * (P / 2) ≤ -cnt ω) =
        Finset.univ.filter Q' := by
      apply Finset.filter_congr
      intro ω _
      rw [hQ'def, hcntdef]
      constructor
      · intro h
        have : ((run ω).length : ℝ) ≤ (1 - b) * (P / 2 : ℝ) := by linarith
        exact this
      · intro h
        linarith
    rw [hfilter] at htail

    have hsum : ∑ ω ∈ Finset.univ.filter Q', (independentSampleLaw plaw).prob ω =
        (Finset.univ.filter Q').card * (1 / 2) ^ P := by
      rw [Finset.sum_congr rfl (fun ω _ => hprob ω), Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at htail

    have hexp_arg : -2 * (b * (P / 2)) ^ 2 / ∑ i : Fin P, (1 : ℝ) ^ 2 = -(b ^ 2 * P / 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one]
      have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast (by omega : P ≠ 0)
      field_simp
    rw [hexp_arg] at htail

    have hcard : ((Finset.univ.filter Q').card : ENNReal) * ((2 ^ P : ℕ) : ENNReal)⁻¹ =
        ENNReal.ofReal ((Finset.univ.filter Q').card * (1 / 2) ^ P) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      · exact (ENNReal.ofReal_natCast _).symm
      · rw [one_div, inv_pow, ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ P),
          show ((2 : ℝ) ^ P) = ((2 ^ P : ℕ) : ℝ) from by norm_cast, ENNReal.ofReal_natCast]
    rw [hcard]
    exact ENNReal.ofReal_le_ofReal htail

/-- Every nonzero-probability list of `i` ideal fresh records has length exactly `i`. -/
private theorem idealFreshRecords_length {n : ℕ} :
    ∀ (i : ℕ) {L : List (ZMod (2^n))}, (idealFreshRecords n i) L ≠ 0 → L.length = i := by
  intro i
  induction i with
  | zero =>
    intro L h
    change (PMF.pure ([] : List (ZMod (2^n)))) L ≠ 0 at h
    have hL : L = [] := eq_of_pure_ne_zero h
    rw [hL, List.length_nil]
  | succ i ih =>
    intro L h
    change ((dihedralIdealRecordLaw n).bind fun r =>
      (idealFreshRecords n i).map fun L => r :: L) L ≠ 0 at h
    obtain ⟨r, _, h2⟩ := exists_of_bind_ne_zero h
    obtain ⟨L', hL', h3⟩ := exists_of_map_ne_zero h2
    have h3' : r :: L' = L := h3
    rw [← h3', List.length_cons, ih hL']

/-- The recursive real retention threshold starting at one and incorporating each stage's
multiplicative loss and window-class correction. -/
private noncomputable def ρChain (n m : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => (1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) *
      (ρChain n m j - (2:ℝ)^(sieveWindowWidth n m j) / (24 * (2:ℝ)^(3*m - 2*j)))

/-- The real cube root of two is at least `18/17`. -/
private theorem two_rpow_third_ge : (18:ℝ)/17 ≤ (2:ℝ)^((1:ℝ)/3) := by
  have hx3 : ((2:ℝ)^((1:ℝ)/3)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hxpos : (0:ℝ) < (2:ℝ)^((1:ℝ)/3) := by positivity
  by_contra h
  push Not at h
  have h2 : ((2:ℝ)^((1:ℝ)/3))^3 < (18/17:ℝ)^3 := by
    exact pow_lt_pow_left₀ h hxpos.le (by norm_num)
  rw [hx3] at h2
  norm_num at h2

/-- The reciprocal real cube root of two is at most `17/18`. -/
private theorem two_rpow_neg_third_le : (2:ℝ)^(-(1:ℝ)/3) ≤ 17/18 := by
  have h := two_rpow_third_ge
  have hxpos : (0:ℝ) < (2:ℝ)^((1:ℝ)/3) := by positivity
  rw [show (2:ℝ)^(-(1:ℝ)/3) = ((2:ℝ)^((1:ℝ)/3))⁻¹ from by
    rw [neg_div, Real.rpow_neg (by norm_num)]]
  rw [inv_le_comm₀ hxpos (by norm_num : (0:ℝ) < 17/18)]
  have h17 : ((17/18 : ℝ))⁻¹ = 18/17 := by norm_num
  rwa [h17]

/-- The real power `2^(-4/3)` is at most `35/72`. -/
private theorem two_rpow_neg43_le : (2:ℝ)^(-(4:ℝ)/3) ≤ 35/72 := by
  have h1 : (2:ℝ)^(-(4:ℝ)/3) = (2:ℝ)^(-(1:ℝ)/3) / 2 := by
    rw [show (-(4:ℝ)/3) = (-(1:ℝ)/3) - 1 from by ring, Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
    rw [Real.rpow_one]
  rw [h1]
  have h := two_rpow_neg_third_le
  linarith

/-- For `m ≥ 1`, the real power `2^(-m/3)` is at most `17/18`. -/
private theorem two_rpow_m3_le (m : ℕ) (hm1 : 1 ≤ m) : (2:ℝ)^(-(m:ℝ)/3) ≤ 17/18 := by
  have h1 : (2:ℝ)^(-(m:ℝ)/3) ≤ (2:ℝ)^(-(1:ℝ)/3) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    have h1m : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    linarith
  exact le_trans h1 two_rpow_neg_third_le

/-- For `m ≥ 1` and `j ≤ m`, the cumulative window-class correction through stage `j` is at most
`1/72`. -/
private theorem dStep_sum_le (n m : ℕ) (hm1 : 1 ≤ m) :
    ∀ j : ℕ, j ≤ m →
      (∑ i ∈ Finset.range j, ((2:ℝ)^(sieveWindowWidth n m i) / (24 * (2:ℝ)^(3*m - 2*i))))
        ≤ 1/72 := by
  intro j hjm
  have hterm : ∀ i ∈ Finset.range j,
      (2:ℝ)^(sieveWindowWidth n m i) / (24 * (2:ℝ)^(3*m - 2*i)) ≤ (4:ℝ)^i / (24 * (4:ℝ)^m) := by
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    have him : i ≤ m := by omega
    have hwle : sieveWindowWidth n m i ≤ m := Nat.min_le_left _ _
    have hnum : (2:ℝ)^(sieveWindowWidth n m i) ≤ (2:ℝ)^m := by
      have h : (2:ℕ)^(sieveWindowWidth n m i) ≤ (2:ℕ)^m := pow_le_pow_right₀ (by norm_num) hwle
      exact_mod_cast h
    have hden : (24:ℝ) * (2:ℝ)^(3*m - 2*i) = (24 * (2:ℝ)^m) * (4:ℝ)^(m - i) := by
      have h1 : (3*m - 2*i) = m + 2*(m - i) := by omega
      rw [h1, pow_add]
      have h2 : (2:ℝ)^(2*(m-i)) = (4:ℝ)^(m-i) := by
        rw [show (4:ℝ) = 2^2 from by norm_num, ← pow_mul]
      rw [h2]
      ring
    rw [hden]
    have hpos : (0:ℝ) < (24 * (2:ℝ)^m) * (4:ℝ)^(m - i) := by positivity
    have hle1 : (2:ℝ)^(sieveWindowWidth n m i) / ((24 * (2:ℝ)^m) * (4:ℝ)^(m - i))
        ≤ (2:ℝ)^m / ((24 * (2:ℝ)^m) * (4:ℝ)^(m - i)) :=
      (div_le_div_iff_of_pos_right hpos).mpr hnum
    refine le_trans hle1 ?_
    have he1 : (2:ℝ)^m / ((24 * (2:ℝ)^m) * (4:ℝ)^(m - i)) = 1 / (24 * (4:ℝ)^(m-i)) := by
      field_simp
    have he2 : (1:ℝ) / (24 * (4:ℝ)^(m-i)) = (4:ℝ)^i / (24 * (4:ℝ)^m) := by
      have h3 : (4:ℝ)^(m - i) * (4:ℝ)^i = (4:ℝ)^m := by
        rw [← pow_add, Nat.sub_add_cancel him]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (-24 : ℝ) * h3
    rw [he1, he2]
  calc (∑ i ∈ Finset.range j, ((2:ℝ)^(sieveWindowWidth n m i) / (24 * (2:ℝ)^(3*m - 2*i))))
      ≤ ∑ i ∈ Finset.range j, (4:ℝ)^i / (24 * (4:ℝ)^m) := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range j, (4:ℝ)^i) / (24 * (4:ℝ)^m) := by rw [Finset.sum_div]
    _ = ((4:ℝ)^j - 1) / 3 / (24 * (4:ℝ)^m) := by
        rw [geom_sum_eq (by norm_num : (4:ℝ) ≠ 1) j]
        norm_num
    _ ≤ (1:ℝ)/72 := by
        have h4j : (4:ℝ)^j ≤ (4:ℝ)^m := pow_le_pow_right₀ (by norm_num) hjm
        rw [div_div, show (3:ℝ) * (24 * (4:ℝ)^m) = 72 * (4:ℝ)^m from by ring,
          div_le_iff₀ (by positivity : (0:ℝ) < 72 * (4:ℝ)^m),
          show (1:ℝ)/72 * (72 * (4:ℝ)^m) = (4:ℝ)^m from by ring]
        linarith [h4j]

/-- For `m ≥ 1`, the sum of `2^(i-4*m/3)` over `i < m` is at most `2^(-m/3)`. -/
private theorem bStep_sum_le_m (m : ℕ) (hm1 : 1 ≤ m) :
    (∑ i ∈ Finset.range m, (2:ℝ)^((i:ℝ) - 4*(m:ℝ)/3)) ≤ (2:ℝ)^(-(m:ℝ)/3) := by
  cases m with
  | zero => simp at hm1
  | succ m =>
    rw [Finset.sum_range_succ]
    have hsum := num_checkpt_sumB (m+1) m (by omega) (by omega)
    have hterm : (2:ℝ)^((m:ℝ) - 4*((m+1:ℕ):ℝ)/3) = (2:ℝ)^(-((m+1:ℕ):ℝ)/3 - 1) := by
      congr 1
      push_cast
      ring
    rw [hterm]
    have h2 : (2:ℝ)^(-((m+1:ℕ):ℝ)/3 - 1) = (2:ℝ)^(-((m+1:ℕ):ℝ)/3) / 2 := by
      rw [show -((m+1:ℕ):ℝ)/3 - 1 = (-((m+1:ℕ):ℝ)/3) - 1 from by ring,
        Real.rpow_sub (by norm_num), Real.rpow_one]
    rw [h2] at hsum ⊢
    linarith [hsum]

/-- Through stage `m`, the retention threshold is at least one minus the cumulative
multiplicative-loss and window-class corrections, for `m ≥ 1`. -/
private theorem ρChain_lower (n m : ℕ) (hm1 : 1 ≤ m) :
    ∀ j : ℕ, j ≤ m →
      1 - (∑ i ∈ Finset.range j, ((2:ℝ)^((i:ℝ) - 4*(m:ℝ)/3)
        + (2:ℝ)^(sieveWindowWidth n m i) / (24 * (2:ℝ)^(3*m - 2*i)))) ≤ ρChain n m j := by
  intro j
  induction j with
  | zero => intro _; simp [ρChain]
  | succ j ih =>
    intro hjm
    have hj1 : j ≤ m - 1 := by omega
    have IH := ih (by omega)
    have hjm2 : (j:ℝ) ≤ (m:ℝ) - 1 := by
      have h1 : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
      have h2 : (j:ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hj1
      rw [h1] at h2
      exact h2
    have hb1 : (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3) ≤ 1 := by
      have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (show (j:ℝ) - 4*(m:ℝ)/3 ≤ 0 from by linarith [hjm2, hm1'])
      rwa [Real.rpow_zero] at h
    have hb0 : (0:ℝ) ≤ (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3) := by positivity
    have hδ0 : (0:ℝ) ≤ (2:ℝ)^(sieveWindowWidth n m j) / (24 * (2:ℝ)^(3*m - 2*j)) := by positivity
    have hS0 : (0:ℝ) ≤ ∑ i ∈ Finset.range j, ((2:ℝ)^((i:ℝ) - 4*(m:ℝ)/3)
        + (2:ℝ)^(sieveWindowWidth n m i) / (24 * (2:ℝ)^(3*m - 2*i))) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hrec : ρChain n m (j+1) = (1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) *
        (ρChain n m j - (2:ℝ)^(sieveWindowWidth n m j) / (24 * (2:ℝ)^(3*m - 2*j))) := rfl
    rw [Finset.sum_range_succ, hrec]
    have h1 : (1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) * (1 - (∑ i ∈ Finset.range j,
          ((2:ℝ)^((i:ℝ) - 4*(m:ℝ)/3)
            + (2:ℝ)^(sieveWindowWidth n m i) / (24 * (2:ℝ)^(3*m - 2*i))))
        - (2:ℝ)^(sieveWindowWidth n m j) / (24 * (2:ℝ)^(3*m - 2*j)))
        ≤ (1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) * (ρChain n m j
            - (2:ℝ)^(sieveWindowWidth n m j) / (24 * (2:ℝ)^(3*m - 2*j))) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith [hb1])
      linarith [IH]
    refine le_trans ?_ h1
    nlinarith [mul_nonneg hb0 (add_nonneg hS0 hδ0)]

/-- Under the stated stage, input-size, retention, and target-threshold hypotheses, an ideal
layer reaches the target length with probability at least `1-exp(-2^(m/3-2))/2`. -/
private theorem idealLayer_survival (n m j : ℕ) (hm1 : 1 ≤ m) (hj : j ≤ m - 1)
    (ρ : ℝ) (hρ2 : 1 / 2 ≤ ρ)
    (L : List (ZMod (2^n))) (hL : (24 * (2:ℝ)^(3*m - 2*j)) * ρ ≤ L.length)
    (Tg : ℝ) (hTg : Tg ≤ (1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) *
      ((24 * (2:ℝ)^(3*m - 2*j)) * ρ - (2:ℝ)^(sieveWindowWidth n m j)) / 4) :
    ENNReal.ofReal (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ≤
      ∑' L' : List (ZMod (2^n)),
        if (Tg ≤ (L'.length : ℝ)) then (idealLayer n m j L) L' else 0 := by
  set w : ℕ := sieveWindowWidth n m j with hwdef
  set b : ℝ := (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3) with hbdef
  have hbpos : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hjm2 : (j:ℝ) ≤ (m:ℝ) - 1 := by
    have h1 : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
      rw [Nat.cast_sub hm1, Nat.cast_one]
    have h2 : (j:ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hj
    rw [h1] at h2
    exact h2
  have hb1 : b ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (j:ℝ) - 4*(m:ℝ)/3 ≤ 0 from by
        have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
        linarith)
    rwa [Real.rpow_zero] at h
  set ps : List (ZMod (2^n) × ZMod (2^n)) := sievePair n w (m * j) L with hpsdef
  have hlayer : idealLayer n m j L = idealLayerAux n ps := rfl
  rw [hlayer]
  have hwle : w ≤ m := by
    rw [hwdef]
    exact Nat.min_le_left _ _
  have hcov : L.length ≤ 2 * ps.length + 2 ^ w :=
    sievePairWith_pair_coverage n id w (m * j) L
  have h2w : ((2:ℝ) ^ w : ℝ) ≤ (2:ℝ) ^ m := by
    have h : (2:ℕ)^w ≤ (2:ℕ)^m := pow_le_pow_right₀ (by norm_num) hwle
    exact_mod_cast h
  have hPl : (24 * (2:ℝ)^(3*m - 2*j)) * ρ - (2:ℝ)^m ≤ 2 * (ps.length : ℝ) := by
    have hcov' : (L.length : ℝ) ≤ 2 * (ps.length : ℝ) + (2:ℝ)^w := by exact_mod_cast hcov
    linarith [hL, hcov', h2w]
  have hPl2 : 6 * (2:ℝ)^(3*(m:ℝ) - 2*(j:ℝ)) - (2:ℝ)^((m:ℝ) - 1) ≤ (ps.length : ℝ) := by
    have h1 : (24 * (2:ℝ)^(3*m - 2*j)) * (1/2) - (2:ℝ)^m ≤ 2 * (ps.length : ℝ) := by
      have hρρ : (24 * (2:ℝ)^(3*m - 2*j)) * (1/2) ≤ (24 * (2:ℝ)^(3*m - 2*j)) * ρ :=
        mul_le_mul_of_nonneg_left hρ2 (by positivity)
      linarith [hPl, hρρ]
    have hB : (2:ℝ)^(3*m - 2*j) = (2:ℝ)^(3*(m:ℝ) - 2*(j:ℝ)) := by
      have h2j : 2*j ≤ 3*m := by omega
      rw [← Real.rpow_natCast 2 (3*m - 2*j)]
      congr 1
      rw [Nat.cast_sub h2j]
      push_cast
      ring
    rw [hB] at h1
    have hm2 : (2:ℝ)^m = 2 * (2:ℝ)^((m:ℝ) - 1) := by
      rw [← Real.rpow_natCast 2 m,
        show (2:ℝ)^((m:ℝ)) = (2:ℝ)^(((m:ℝ) - 1) + 1) from by congr 1; ring]
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
      ring
    rw [hm2] at h1
    linarith [h1]
  have hb2 : b ^ 2 = (2:ℝ)^(2*(j:ℝ) - 8*(m:ℝ)/3) := by
    rw [hbdef, ← Real.rpow_natCast ((2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have hchk := num_checkpt_hoeffding m j hm1 hj
  have hexp_lb : (2:ℝ)^((m:ℝ)/3 - 2) + Real.log 2 ≤ b ^ 2 * (ps.length : ℝ) / 2 := by
    have h1 : (6 * (2:ℝ)^(3*(m:ℝ) - 2*(j:ℝ)) - (2:ℝ)^((m:ℝ) - 1))
        * (2:ℝ)^(2*(j:ℝ) - 8*(m:ℝ)/3 - 1) ≤ b^2 * (ps.length : ℝ) / 2 := by
      rw [show b ^ 2 * (ps.length : ℝ) / 2
          = (ps.length : ℝ) * ((2:ℝ)^(2*(j:ℝ) - 8*(m:ℝ)/3 - 1)) from by
        rw [hb2,
          show (2:ℝ)^(2*(j:ℝ) - 8*(m:ℝ)/3)
            = (2:ℝ)^((2*(j:ℝ) - 8*(m:ℝ)/3 - 1) + 1) from by congr 1; ring,
          Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
        ring]
      exact mul_le_mul_of_nonneg_right hPl2 (by positivity)
    exact le_trans hchk h1
  have hexp_ub : Real.exp (-(b ^ 2 * (ps.length : ℝ) / 2))
      ≤ Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2 := by
    have hle : -(b ^ 2 * (ps.length : ℝ) / 2) ≤ -((2:ℝ)^((m:ℝ)/3 - 2) + Real.log 2) := by
      linarith [hexp_lb]
    have h1 : Real.exp (-(b ^ 2 * (ps.length : ℝ) / 2))
        ≤ Real.exp (-((2:ℝ)^((m:ℝ)/3 - 2) + Real.log 2)) :=
      Real.exp_le_exp.mpr hle
    have h2 : Real.exp (-((2:ℝ)^((m:ℝ)/3 - 2) + Real.log 2))
        = Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2 := by
      rw [show -((2:ℝ)^((m:ℝ)/3 - 2) + Real.log 2)
          = -(2:ℝ)^((m:ℝ)/3 - 2) + -(Real.log 2) from by ring,
        Real.exp_add, Real.exp_neg (Real.log 2), Real.exp_log (by norm_num : (0:ℝ) < 2)]
      ring
    exact h1.trans (le_of_eq h2)
  have hbad := layer_len_tail ps b hbpos
  have hbad2 : (∑' L', if ↑L'.length ≤ (1 - b) * (↑ps.length / 2)
        then idealLayerAux n ps L' else 0)
      ≤ ENNReal.ofReal (Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) :=
    le_trans hbad (ENNReal.ofReal_le_ofReal hexp_ub)
  have hcover : ∀ L' : List (ZMod (2^n)),
      (idealLayerAux n ps) L' ≤
        (if Tg ≤ (L'.length : ℝ) then idealLayerAux n ps L' else 0) +
        (if (L'.length : ℝ) ≤ (1 - b) * ((ps.length : ℝ) / 2)
          then idealLayerAux n ps L' else 0) := by
    intro L'
    by_cases hg : Tg ≤ (L'.length : ℝ)
    · rw [if_pos hg]
      exact le_self_add
    · rw [if_neg hg]
      push Not at hg
      have hbadL : (L'.length : ℝ) ≤ (1 - b) * ((ps.length : ℝ) / 2) := by
        have hb0 : (0:ℝ) ≤ 1 - b := by linarith [hb1]
        have hinner : ((24 * (2:ℝ)^(3*m - 2*j)) * ρ - (2:ℝ)^w) / 4 ≤ (ps.length : ℝ) / 2 := by
          have hcov' : (L.length : ℝ) ≤ 2 * (ps.length : ℝ) + (2:ℝ)^w := by exact_mod_cast hcov
          linarith [hL, hcov']
        have h1 : (1 - b) * ((24 * (2:ℝ)^(3*m - 2*j)) * ρ - (2:ℝ)^w) / 4
            ≤ (1 - b) * ((ps.length : ℝ) / 2) := by
          calc (1 - b) * ((24 * (2:ℝ)^(3*m - 2*j)) * ρ - (2:ℝ)^w) / 4
              = (1 - b) * (((24 * (2:ℝ)^(3*m - 2*j)) * ρ - (2:ℝ)^w) / 4) := by ring
            _ ≤ (1 - b) * ((ps.length : ℝ) / 2) := mul_le_mul_of_nonneg_left hinner hb0
        linarith [hg, hTg, h1]
      rw [if_pos hbadL]
      simp
  have htot : (∑' L' : List (ZMod (2^n)), idealLayerAux n ps L') = 1 := PMF.tsum_coe _
  have hsum_le : (1 : ENNReal) ≤
      (∑' L', (if Tg ≤ (L'.length : ℝ) then idealLayerAux n ps L' else 0)) +
      (∑' L', (if ↑L'.length ≤ (1 - b) * (↑ps.length / 2)
        then idealLayerAux n ps L' else 0)) := by
    rw [← htot, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hcover
  have hfinal : ENNReal.ofReal (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2)
      = 1 - ENNReal.ofReal (Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) := by
    rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one]
  rw [hfinal, tsub_le_iff_right]
  refine le_trans hsum_le ?_
  exact add_le_add (le_refl _) hbad2

/-- The event probability after binding is the outer-probability-weighted sum of conditional
event probabilities. -/
private theorem pmf_bind_event {α β : Type} (μ : PMF α) (F : α → PMF β) (Q : β → Prop)
    [DecidablePred Q] :
    (∑' b, if Q b then (μ.bind F) b else 0) = ∑' a, μ a * (∑' b, if Q b then F a b else 0) := by
  have step1 : (fun b => if Q b then (μ.bind F) b else 0)
      = fun b => ∑' a, μ a * (if Q b then F a b else 0) := by
    funext b
    rw [PMF.bind_apply]
    by_cases hQ : Q b
    · rw [if_pos hQ]
      apply tsum_congr
      intro a
      rw [if_pos hQ]
    · rw [if_neg hQ]
      rw [show (∑' a, μ a * (if Q b then F a b else 0)) = ∑' a, (0 : ENNReal) from by
        apply tsum_congr
        intro a
        rw [if_neg hQ, mul_zero]]
      rw [tsum_zero]
  rw [step1, ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [← ENNReal.tsum_mul_left]

/-- The layer-survival factor `1-exp(-2^(m/3-2))/2` is nonnegative. -/
private theorem one_sub_eps_half_nonneg (m : ℕ) :
    (0:ℝ) ≤ 1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2 := by
  have h0 : (0:ℝ) ≤ (2:ℝ)^((m:ℝ)/3 - 2) := by positivity
  have heps1 : Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) ≤ 1 := by
    calc Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hpos := Real.exp_pos (-(2:ℝ)^((m:ℝ)/3 - 2))
  linarith [heps1, hpos]

/-- For `m ≥ 1` and `j ≤ m`, the probability of meeting the stage-`j` retention threshold is at
least the `j`th power of the layer-survival factor. -/
private theorem idealSieve_size_chain (n m : ℕ) (hm1 : 1 ≤ m) :
    ∀ j : ℕ, j ≤ m →
      ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ j) ≤
        ∑' L : List (ZMod (2^n)),
          if ((24 * (2:ℝ)^(3*m - 2*j)) * ρChain n m j ≤ (L.length : ℝ))
            then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m j)) L else 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [pow_zero, ENNReal.ofReal_one]
    have hlen : ∀ L : List (ZMod (2^n)),
        ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m 0)) L ≠ 0 →
          (24 * (2:ℝ)^(3*m - 2*0)) * ρChain n m 0 ≤ (L.length : ℝ) := by
      intro L hL
      have h1 : ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m 0)) L =
          (idealFreshRecords n (24 * 2^(3*m))) L := by
        rw [show idealSieveRec n m 0 = fun L => PMF.pure L from funext fun L => rfl]
        rw [PMF.bind_pure]
      rw [h1] at hL
      have h2 := idealFreshRecords_length (24 * 2^(3*m)) hL
      have h3 : (24 * (2:ℝ)^(3*m - 2*0)) * ρChain n m 0 = ((24 * 2^(3*m) : ℕ) : ℝ) := by
        rw [show 3*m - 2*0 = 3*m from by omega, show ρChain n m 0 = 1 from rfl, mul_one]
        norm_cast
      rw [h3, h2]
    have hsum : (∑' L : List (ZMod (2^n)),
        if ((24 * (2:ℝ)^(3*m - 2*0)) * ρChain n m 0 ≤ (L.length : ℝ))
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m 0)) L else 0) = 1 := by
      rw [show (fun L : List (ZMod (2^n)) =>
          if ((24 * (2:ℝ)^(3*m - 2*0)) * ρChain n m 0 ≤ (L.length : ℝ))
            then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m 0)) L else 0)
          = fun L => (idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m 0) L from by
        funext L
        by_cases hE : (24 * (2:ℝ)^(3*m - 2*0)) * ρChain n m 0 ≤ (L.length : ℝ)
        · rw [if_pos hE]
        · rw [if_neg hE]
          have h0 : ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m 0)) L = 0 := by
            by_contra hne
            exact hE (hlen L hne)
          rw [h0]]
      exact PMF.tsum_coe _
    rw [hsum]
  | succ j ih =>
    intro hjm
    have IH := ih (by omega : j ≤ m)
    have hj1 : j ≤ m - 1 := by omega
    have hρ2 : 1 / 2 ≤ ρChain n m j := by
      have hlow := ρChain_lower n m hm1 j (by omega)
      have hsum_b := num_checkpt_sumB m j hm1 hj1
      have hsum_d := dStep_sum_le n m hm1 j (by omega)
      have hnum : (2:ℝ)^(-(m:ℝ)/3 - 1) + 1/72 ≤ 1/2 := by
        have h1 : (2:ℝ)^(-(m:ℝ)/3 - 1) ≤ (2:ℝ)^(-(4:ℝ)/3) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          have h1m : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
          linarith
        have h2 := two_rpow_neg43_le
        linarith
      rw [Finset.sum_add_distrib] at hlow
      linarith [hlow, hsum_b, hsum_d, hnum]
    have hstep : ∀ L : List (ZMod (2^n)),
        (24 * (2:ℝ)^(3*m - 2*j)) * ρChain n m j ≤ (L.length : ℝ) →
        ENNReal.ofReal (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ≤
          ∑' L' : List (ZMod (2^n)),
            if ((24 * (2:ℝ)^(3*m - 2*(j+1))) * ρChain n m (j+1) ≤ (L'.length : ℝ))
              then (idealLayer n m j L) L' else 0 := by
      intro L hL
      apply idealLayer_survival n m j hm1 hj1 _ hρ2 L hL
      have hB4 : (2:ℝ)^(3*m - 2*j) = 4 * (2:ℝ)^(3*m - 2*(j+1)) := by
        have h2le : 2 ≤ 3*m - 2*j := by omega
        rw [show 3*m - 2*j = (3*m - 2*(j+1)) + 2 from by omega, pow_add]
        ring
      have hδ : (2:ℝ)^(sieveWindowWidth n m j) / (24 * (4 * (2:ℝ)^(3*m - 2*(j+1))))
          * (24 * (4 * (2:ℝ)^(3*m - 2*(j+1)))) = (2:ℝ)^(sieveWindowWidth n m j) :=
        div_mul_cancel₀ _ (by positivity)
      have hrec : ρChain n m (j+1) = (1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) *
          (ρChain n m j - (2:ℝ)^(sieveWindowWidth n m j) / (24 * (2:ℝ)^(3*m - 2*j))) := rfl
      rw [hrec]
      have key : (24 * (2:ℝ)^(3*m - 2*(j+1))) * ((1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) *
            (ρChain n m j - (2:ℝ)^(sieveWindowWidth n m j) / (24 * (2:ℝ)^(3*m - 2*j))))
          = (1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) * ((24 * (2:ℝ)^(3*m - 2*j)) * ρChain n m j
              - (2:ℝ)^(sieveWindowWidth n m j)) / 4 := by
        rw [hB4]
        linear_combination (-(1 - (2:ℝ)^((j:ℝ) - 4*(m:ℝ)/3)) / 4) * hδ
      exact le_of_eq key
    have hbind : ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m (j+1)))
        = (((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m j)).bind
            (idealLayer n m j)) := by
      rw [show idealSieveRec n m (j+1)
          = fun L => (idealSieveRec n m j L).bind (idealLayer n m j) from funext fun L => rfl]
      rw [PMF.bind_bind]
    rw [hbind, pmf_bind_event]
    have he2 := one_sub_eps_half_nonneg m
    calc ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ (j+1))
        = ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2)
            * (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ j) := by
          rw [pow_succ']
      _ = ENNReal.ofReal (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2)
          * ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ j) := by
          rw [ENNReal.ofReal_mul he2]
      _ ≤ ENNReal.ofReal (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2)
          * ∑' L : List (ZMod (2^n)),
            (if ((24 * (2:ℝ)^(3*m - 2*j)) * ρChain n m j ≤ (L.length : ℝ))
              then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m j)) L
              else 0) :=
          mul_le_mul_right IH _
      _ ≤ ∑' L : List (ZMod (2^n)),
            ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m j)) L *
            (∑' L' : List (ZMod (2^n)),
              if ((24 * (2:ℝ)^(3*m - 2*(j+1))) * ρChain n m (j+1) ≤ (L'.length : ℝ))
                then (idealLayer n m j L) L' else 0) := by
          rw [← ENNReal.tsum_mul_left]
          apply ENNReal.tsum_le_tsum
          intro L
          by_cases hE : (24 * (2:ℝ)^(3*m - 2*j)) * ρChain n m j ≤ (L.length : ℝ)
          · rw [if_pos hE]
            exact (mul_le_mul' (hstep L hE) (le_refl _)).trans_eq (mul_comm _ _)
          · rw [if_neg hE]
            simp

/-- For `m ≥ 1`, the final retention threshold `ρChain n m m` is at least `1/24`. -/
private theorem ρChain_m_ge (n m : ℕ) (hm1 : 1 ≤ m) :
    (1:ℝ)/24 ≤ ρChain n m m := by
  have hlow := ρChain_lower n m hm1 m (le_refl m)
  have hsum_b := bStep_sum_le_m m hm1
  have hsum_d := dStep_sum_le n m hm1 m (le_refl m)
  have hnum : (2:ℝ)^(-(m:ℝ)/3) + 1/72 ≤ 23/24 := by
    have h := two_rpow_m3_le m hm1
    linarith
  rw [Finset.sum_add_distrib] at hlow
  linarith [hlow, hsum_b, hsum_d, hnum]

/-- Starting with `24*2^(3*m)` fresh ideal records, the probability of retaining at least `2^m`
records after `m` stages is bounded below by the stated product of layer-survival factors
for `m ≥ 1`. -/
private theorem idealSieve_size_final (n m : ℕ) (hm1 : 1 ≤ m) :
    ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ m) ≤
      ∑' L : List (ZMod (2^n)),
        if ((2^m : ℕ) ≤ L.length)
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0 := by
  refine le_trans (idealSieve_size_chain n m hm1 m (le_refl m)) ?_
  apply ENNReal.tsum_le_tsum
  intro L
  by_cases hc : (24 * (2:ℝ)^(3*m - 2*m)) * ρChain n m m ≤ (L.length : ℝ)
  · have hB : ((2^m : ℕ) : ℝ) ≤ (24 * (2:ℝ)^(3*m - 2*m)) * ρChain n m m := by
      have h3 : 3*m - 2*m = m := by omega
      rw [h3]
      have hρ := ρChain_m_ge n m hm1
      have h1 : (24 * (2:ℝ)^m) * (1/24) ≤ (24 * (2:ℝ)^m) * ρChain n m m :=
        mul_le_mul_of_nonneg_left hρ (by positivity)
      have h2 : (24 * (2:ℝ)^m) * (1/24) = (2:ℝ)^m := by ring
      rw [h2] at h1
      exact_mod_cast h1
    have h2m : (2^m : ℕ) ≤ L.length := by
      have hc' : ((2^m : ℕ) : ℝ) ≤ (L.length : ℝ) := le_trans hB hc
      exact_mod_cast hc'
    rw [if_pos hc, if_pos h2m]
  · rw [if_neg hc]
    simp

/-- For `m ≥ 1`, the assumed top-bit success estimate and the final size bound imply half-period
hit probability at least `(1-exp(-2^(m/3-2)))^m`. -/
private theorem idealHit_of_topbit (n m : ℕ) (hm1 : 1 ≤ m)
    (htop : (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
        * ENNReal.ofReal (1 - (2:ℝ)^(-((2^m : ℕ) : ℝ)))
      ≤ ∑' L : List (ZMod (2^n)),
        if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0) :
    ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m) ≤
      ∑' L : List (ZMod (2^n)),
        if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0 := by
  have hmerge := num_checkpt_merge m hm1
  have hsize := idealSieve_size_final n m hm1
  have h2m : (0:ℝ) ≤ (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ m :=
    pow_nonneg (one_sub_eps_half_nonneg m) m
  calc ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m)
      ≤ ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ m
          * (1 - (2:ℝ)^(-((2^m : ℕ) : ℝ)))) :=
        ENNReal.ofReal_le_ofReal hmerge
    _ = ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) / 2) ^ m)
        * ENNReal.ofReal (1 - (2:ℝ)^(-((2^m : ℕ) : ℝ))) :=
        ENNReal.ofReal_mul h2m
    _ ≤ (∑' L : List (ZMod (2^n)),
          if (2^m : ℕ) ≤ L.length
            then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
        * ENNReal.ofReal (1 - (2:ℝ)^(-((2^m : ℕ) : ℝ))) :=
        mul_le_mul' hsize (le_refl _)
    _ ≤ _ := htop

/-- The extension of a finite binary tape is zero outside its original range. -/
private theorem coinLift_ge {k : ℕ} (c : Fin k → Fin 2) {i : ℕ} (hi : ¬ i < k) :
    coinLift c i = 0 := dif_neg hi

/-- A bijection between nonempty finite types maps the uniform distribution to the uniform
distribution. -/
private theorem uni_bij {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → β) (hf : Function.Bijective f) :
    (PMF.uniformOfFintype' α).map f = PMF.uniformOfFintype' β := by
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_of_bijective hf
  ext b
  rw [PMF.map_apply]
  obtain ⟨a, ha⟩ := hf.2 b
  rw [tsum_eq_single a (fun a' ha' => by
    refine if_neg ?_
    intro hcon
    rw [hcon] at ha
    exact ha' (hf.1 ha.symm))]
  rw [if_pos ha.symm, PMF.uniformOfFintype'_apply, PMF.uniformOfFintype'_apply, hcard]

/-- Independent uniform samples from two nonempty finite types give the uniform distribution on
their product. -/
private theorem uni_bind_prod {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype' A).bind (fun a => (PMF.uniformOfFintype' B).map (fun b => (a, b)))
      = PMF.uniformOfFintype' (A × B) := by
  have hA : ((Fintype.card A : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : ((Fintype.card B : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hAT : ((Fintype.card A : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext ⟨a, b⟩
  rw [PMF.bind_apply]
  rw [tsum_eq_single (a) (fun a' ha' => by
    have hmap : ((PMF.uniformOfFintype' B).map (fun b => (a', b))) (a, b) = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.2
      intro b'
      refine if_neg ?_
      intro hcon
      simp only [Prod.mk.injEq] at hcon
      exact ha' hcon.1.symm
    rw [hmap, mul_zero])]
  rw [PMF.map_apply, tsum_eq_single b (fun b' hb' => by
    refine if_neg ?_
    intro hcon
    simp only [Prod.mk.injEq] at hcon
    exact hb' hcon.2.symm)]
  rw [if_pos rfl, PMF.uniformOfFintype'_apply, PMF.uniformOfFintype'_apply,
    PMF.uniformOfFintype'_apply, Fintype.card_prod, Nat.cast_mul]
  exact (ENNReal.mul_inv (Or.inl hA) (Or.inl hAT)).symm

/-- Applying a binary function to two independent uniform samples equals mapping that function
over a uniform product sample. -/
private theorem uni_bind_map_prod {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    {γ : Type} (F : A → B → γ) :
    (PMF.uniformOfFintype' A).bind (fun a => (PMF.uniformOfFintype' B).map (F a))
      = (PMF.uniformOfFintype' (A × B)).map (fun p => F p.1 p.2) := by
  rw [← uni_bind_prod (A := A) (B := B), PMF.map_bind]
  refine congrArg (PMF.bind (PMF.uniformOfFintype' A)) (funext fun a => ?_)
  rw [PMF.map_comp]
  rfl

/-- The initial `N` entries of a binary tape of length `N+K`. -/
private def takeTape {N K : ℕ} (d : Fin (N + K) → Fin 2) : Fin N → Fin 2 :=
  fun i => d (Fin.castLE (Nat.le_add_right N K) i)

/-- The final `K` entries of a binary tape of length `N+K`. -/
private def dropTape {N K : ℕ} (d : Fin (N + K) → Fin 2) : Fin K → Fin 2 :=
  fun i => d (Fin.natAdd N i)

/-- Concatenation of two finite binary tapes of lengths `N` and `K`. -/
private def glueTape {N K : ℕ} (c : Fin N → Fin 2) (c' : Fin K → Fin 2) : Fin (N + K) → Fin 2 :=
  fun j => if h : (j : ℕ) < N then c ⟨(j : ℕ), h⟩ else c' ⟨(j : ℕ) - N, by omega⟩

/-- A concatenated tape reads from its first component at indices below `N`. -/
private theorem glue_apply_lt {N K : ℕ} (c : Fin N → Fin 2) (c' : Fin K → Fin 2) {j : Fin (N + K)}
    (hj : (j : ℕ) < N) : glueTape c c' j = c ⟨(j : ℕ), hj⟩ := dif_pos hj

/-- A concatenated tape reads from its second component, with index shifted by `N`, at indices
at least `N`. -/
private theorem glue_apply_ge {N K : ℕ} (c : Fin N → Fin 2) (c' : Fin K → Fin 2) {j : Fin (N + K)}
    (hj : ¬ (j : ℕ) < N) : glueTape c c' j = c' ⟨(j : ℕ) - N, by omega⟩ := dif_neg hj

/-- Taking the prefix of a concatenated tape recovers the first tape. -/
private theorem take_glue {N K : ℕ} (c : Fin N → Fin 2) (c' : Fin K → Fin 2) :
    takeTape (glueTape c c') = c := by
  funext i
  show glueTape c c' (Fin.castLE (Nat.le_add_right N K) i) = c i
  have hi : ((Fin.castLE (Nat.le_add_right N K) i : Fin (N + K)) : ℕ) < N := i.2
  rw [glue_apply_lt c c' hi]
  exact congrArg c (Fin.ext rfl)

/-- Dropping the prefix of a concatenated tape recovers the second tape. -/
private theorem drop_glue {N K : ℕ} (c : Fin N → Fin 2) (c' : Fin K → Fin 2) :
    dropTape (glueTape c c') = c' := by
  funext i
  show glueTape c c' (Fin.natAdd N i) = c' i
  have hi : ¬ ((Fin.natAdd N i : Fin (N + K)) : ℕ) < N := by
    show ¬ (N + (i : ℕ) < N)
    omega
  rw [glue_apply_ge c c' hi]
  exact congrArg c' (Fin.ext (by
    show ((Fin.natAdd N i : Fin (N + K)) : ℕ) - N = (i : ℕ)
    simp))

/-- Concatenating a tape's prefix and suffix reconstructs the tape. -/
private theorem glue_take_drop {N K : ℕ} (d : Fin (N + K) → Fin 2) :
    glueTape (takeTape d) (dropTape d) = d := by
  funext j
  by_cases hj : (j : ℕ) < N
  · show glueTape (takeTape d) (dropTape d) j = d j
    rw [glue_apply_lt _ _ hj]
    show d (Fin.castLE (Nat.le_add_right N K) ⟨(j : ℕ), hj⟩) = d j
    exact congrArg d (Fin.ext rfl)
  · show glueTape (takeTape d) (dropTape d) j = d j
    rw [glue_apply_ge _ _ hj]
    show d (Fin.natAdd N ⟨(j : ℕ) - N, by omega⟩) = d j
    have h1 : (Fin.natAdd N ⟨(j : ℕ) - N, by omega⟩ : Fin (N + K))
        = ⟨N + ((j : ℕ) - N), by omega⟩ := rfl
    rw [h1]
    have h2 : (⟨N + ((j : ℕ) - N), by omega⟩ : Fin (N + K)) = j :=
      Fin.ext (by show N + ((j : ℕ) - N) = (j : ℕ); omega)
    rw [h2]

/-- Concatenation is a bijection from pairs of binary tapes to tapes of the combined length. -/
private theorem glue_bij {N K : ℕ} :
    Function.Bijective (fun p : (Fin N → Fin 2) × (Fin K → Fin 2) => glueTape p.1 p.2) := by
  constructor
  · intro p p' h
    have h' : glueTape p.1 p.2 = glueTape p'.1 p'.2 := h
    have h1 : p.1 = p'.1 := by
      rw [← take_glue p.1 p.2, ← take_glue p'.1 p'.2, ← h']
    have h2 : p.2 = p'.2 := by
      rw [← drop_glue p.1 p.2, ← drop_glue p'.1 p'.2, ← h']
    exact Prod.ext_iff.2 ⟨h1, h2⟩
  · intro d
    exact ⟨(takeTape d, dropTape d), glue_take_drop d⟩

/-- The prefix and suffix of a uniform binary tape can be sampled as independent uniform tapes. -/
private theorem uni_glue {N K : ℕ} {γ : Type} (G : (Fin N → Fin 2) → (Fin K → Fin 2) → γ) :
    (PMF.uniformOfFintype' (Fin (N + K) → Fin 2)).map (fun d => G (takeTape d) (dropTape d))
      = (PMF.uniformOfFintype' (Fin N → Fin 2)).bind
          (fun c => (PMF.uniformOfFintype' (Fin K → Fin 2)).map (G c)) := by
  rw [← uni_bij _ (glue_bij (N := N) (K := K)), PMF.map_comp, uni_bind_map_prod]
  congr 1
  funext p
  simp only [Function.comp]
  rw [take_glue p.1 p.2, drop_glue p.1 p.2]

/-- The prefix of a uniform binary tape is uniformly distributed. -/
private theorem uni_restrict_add (N K : ℕ) :
    (PMF.uniformOfFintype' (Fin (N + K) → Fin 2)).map takeTape
      = PMF.uniformOfFintype' (Fin N → Fin 2) := by
  have h := uni_glue (N := N) (K := K) (G := fun c _ => c)
  have hbeta : (fun d : Fin (N + K) → Fin 2 => (fun c _ => c) (takeTape d) (dropTape d))
      = takeTape := rfl
  rw [hbeta] at h
  refine h.trans ?_
  have hfam : (fun c : Fin N → Fin 2 => (PMF.uniformOfFintype' (Fin K → Fin 2)).map (fun _ => c))
      = PMF.pure := by
    funext c
    have hc : (fun _ => c) = Function.const (Fin K → Fin 2) c := rfl
    rw [hc]
    exact PMF.map_const _ c
  rw [hfam, PMF.bind_pure]

/-- Restricting a uniform binary tape to its first `k` entries gives a uniform tape of length
`k` when `k ≤ R`. -/
private theorem uni_marginal {k R : ℕ} (h : k ≤ R) :
    (PMF.uniformOfFintype' (Fin R → Fin 2)).map (fun d i => d (Fin.castLE h i))
      = PMF.uniformOfFintype' (Fin k → Fin 2) := by
  obtain ⟨s, hs⟩ := Nat.le.dest h
  subst hs
  have hfun : (fun d : Fin (k + s) → Fin 2 => fun i => d (Fin.castLE (Nat.le_add_right k s) i))
      = takeTape := by
    funext d i
    show d (Fin.castLE (Nat.le_add_right k s) i) = d (Fin.castLE (Nat.le_add_right k s) i)
    rfl
  rw [hfun, uni_restrict_add]

/-- A function of the first `k` entries of a longer uniform tape has the same law as on a
uniform tape of length `k`. -/
private theorem uni_lift {k R : ℕ} (h : k ≤ R) {γ : Type} (F : (Fin k → Fin 2) → γ) :
    (PMF.uniformOfFintype' (Fin R → Fin 2)).map (fun d => F (fun i => d (Fin.castLE h i)))
      = (PMF.uniformOfFintype' (Fin k → Fin 2)).map F := by
  rw [show (fun d : Fin R → Fin 2 => F (fun i => d (Fin.castLE h i)))
        = (F ∘ (fun d : Fin R → Fin 2 => fun i => d (Fin.castLE h i))) from rfl,
    ← PMF.map_comp, uni_marginal h]

/-- Converting a prepended finite function to a list gives the prepended value followed by the
original function's list. -/
private theorem ofFn_consFn {X : Type} {k : ℕ} (x : X) (ω : Fin k → X) :
    List.ofFn (consFn x ω) = x :: List.ofFn ω := by
  rw [List.ofFn_succ]
  have htail : List.ofFn (fun i => consFn x ω i.succ) = List.ofFn ω := by
    have hfun : (fun i => consFn x ω i.succ) = ω := by
      funext i
      exact consFn_succ x ω i
    rw [hfun]
  rw [htail, consFn_zero x ω]

/-- Pointwise equal finite functions give equal lists under `List.ofFn`. -/
private theorem ofFn_congr {X : Type} {k : ℕ} {f g : Fin k → X} (h : ∀ i, f i = g i) :
    List.ofFn f = List.ofFn g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ, h 0, ih fun i => h i.succ]

/-- Ideal fresh records have the law of the list obtained from a uniformly sampled finite label
table. -/
private theorem fresh_table (n : ℕ) : ∀ i : ℕ,
    idealFreshRecords n i
      = (PMF.uniformOfFintype' (Fin i → ZMod (2^n))).map (fun a => List.ofFn a) := by
  intro i
  induction i with
  | zero =>
    show (PMF.pure ([] : List (ZMod (2^n)))) = _
    have hconst : (fun a : Fin 0 → ZMod (2^n) => List.ofFn a)
        = Function.const (Fin 0 → ZMod (2^n)) ([] : List (ZMod (2^n))) := by
      funext a
      exact List.ofFn_zero
    rw [hconst, PMF.map_const]
  | succ i ih =>
    change (dihedralIdealRecordLaw n).bind (fun r =>
      (idealFreshRecords n i).map (fun L => r :: L)) = _
    have hfam : (fun r : ZMod (2^n) => (idealFreshRecords n i).map (fun L => r :: L))
        = (fun r : ZMod (2^n) => (PMF.uniformOfFintype' (Fin i → ZMod (2^n))).map
            (fun a => r :: List.ofFn a)) := by
      funext r
      rw [ih, PMF.map_comp]
      rfl
    have hR : (PMF.uniformOfFintype' (Fin (i+1) → ZMod (2^n))).map (fun a => List.ofFn a)
        = (PMF.uniformOfFintype' (ZMod (2^n))).bind (fun z =>
            (PMF.uniformOfFintype' (Fin i → ZMod (2^n))).map
              (fun a => z :: List.ofFn a)) := by
      rw [show PMF.uniformOfFintype' (Fin (i+1) → ZMod (2^n))
          = (PMF.uniformOfFintype' (ZMod (2^n))).bind
              (fun z => (PMF.uniformOfFintype' (Fin i → ZMod (2^n))).map (consFn z)) from
        uniform_fin_succ_split (ZMod (2^n)) i, PMF.map_bind]
      refine congrArg (PMF.bind (PMF.uniformOfFintype' (ZMod (2^n)))) (funext fun z => ?_)
      have hfun : ((fun a : Fin (i + 1) → ZMod (2^n) => List.ofFn a) ∘ consFn z)
          = (fun a : Fin i → ZMod (2^n) => z :: List.ofFn a) := by
        funext a; exact ofFn_consFn z a
      rw [PMF.map_comp, hfun]
    rw [dihedralIdealRecordLaw, hfam, hR]

/-- Deterministic recursive sieving using pair differences and a binary tape divided into stage
blocks of length `R`. -/
private def detSieveRun (n m R : ℕ) :
    ℕ → List (ZMod (2 ^ n)) → (ℕ → Fin 2) → List (ZMod (2 ^ n))
  | 0, L, _ => L
  | j + 1, L, C =>
    layerRunGen (fun p : ZMod (2 ^ n) × ZMod (2 ^ n) => p.2 - p.1)
      (sievePair n (sieveWindowWidth n m j) (m * j) (detSieveRun n m R j L C))
      (fun i => C (j * R + i))

/-- Deterministic layer execution produces at most one child per input pair. -/
private theorem layerRunGen_length_le {α : Type} (child : α × α → α) :
    ∀ (ps : List (α × α)) (c : ℕ → Fin 2), (layerRunGen child ps c).length ≤ ps.length := by
  intro ps
  induction ps with
  | nil => intro c; simp [layerRunGen]
  | cons p ps ih =>
    intro c
    have hrec := ih (fun i => c (i + 1))
    have hlen1 : (if c 0 = 1 then [child p] else []).length ≤ 1 := by
      by_cases h : c 0 = 1
      · rw [if_pos h]; simp
      · rw [if_neg h]; simp
    show ((if c 0 = 1 then [child p] else []) ++
      layerRunGen child ps (fun i => c (i + 1))).length ≤ ps.length + 1
    rw [List.length_append]
    omega

/-- Deterministic recursive sieving never increases the input list length. -/
private theorem detSieveRun_length_le (n m R : ℕ) :
    ∀ (j : ℕ) (L : List (ZMod (2^n))) (C : ℕ → Fin 2),
      (detSieveRun n m R j L C).length ≤ L.length := by
  intro j
  induction j with
  | zero => intro L C; exact Nat.le_refl _
  | succ j ih =>
    intro L C
    have h1 := layerRunGen_length_le (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
      (sievePair n (sieveWindowWidth n m j) (m * j) (detSieveRun n m R j L C))
      (fun i => C (j * R + i))
    have h2 : 2 * (sievePair n (sieveWindowWidth n m j) (m * j)
        (detSieveRun n m R j L C)).length
        ≤ (detSieveRun n m R j L C).length :=
      sievePairWith_length_bound n id (sieveWindowWidth n m j) (m * j)
        (detSieveRun n m R j L C)
    have h3 := ih L C
    show (layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
      (sievePair n (sieveWindowWidth n m j) (m * j) (detSieveRun n m R j L C))
      (fun i => C (j * R + i))).length ≤ L.length
    omega

/-- For an input list of length at most `R`, the first `j*R` tape entries determine execution of
`j` deterministic sieve stages. -/
private theorem detSieveRun_congr (n m R : ℕ) (L : List (ZMod (2^n))) (hL : L.length ≤ R) :
    ∀ (j : ℕ) (C₁ C₂ : ℕ → Fin 2), (∀ i, i < j * R → C₁ i = C₂ i) →
      detSieveRun n m R j L C₁ = detSieveRun n m R j L C₂ := by
  intro j
  induction j with
  | zero => intro C₁ C₂ _; rfl
  | succ j ih =>
    intro C₁ C₂ hC
    have hstep : (j + 1) * R = j * R + R := by ring
    have hrest : detSieveRun n m R j L C₁ = detSieveRun n m R j L C₂ :=
      ih C₁ C₂ (fun i hi => hC i (by omega))
    show layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
        (sievePair n (sieveWindowWidth n m j) (m * j) (detSieveRun n m R j L C₁))
        (fun i => C₁ (j * R + i))
      = layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
        (sievePair n (sieveWindowWidth n m j) (m * j) (detSieveRun n m R j L C₂))
        (fun i => C₂ (j * R + i))
    rw [hrest]
    refine layerRunGen_congr _ _ _ _ ?_
    intro i hi
    have hps : 2 * (sievePair n (sieveWindowWidth n m j) (m * j)
        (detSieveRun n m R j L C₁)).length
        ≤ (detSieveRun n m R j L C₁).length :=
      sievePairWith_length_bound n id (sieveWindowWidth n m j) (m * j)
        (detSieveRun n m R j L C₁)
    rw [hrest] at hps
    have hLj := detSieveRun_length_le n m R j L C₂
    have hlt : j * R + i < (j + 1) * R := by omega
    exact hC _ hlt

/-- For input length at most `R`, the ideal recursive sieve law is deterministic sieve execution
driven by a uniform tape of length `j*R`. -/
private theorem idealSieveRec_eq_map_det (n m R : ℕ) :
    ∀ (j : ℕ) (L : List (ZMod (2^n))) (_hL : L.length ≤ R),
      idealSieveRec n m j L = (PMF.uniformOfFintype' (Fin (j * R) → Fin 2)).map
        (fun c => detSieveRun n m R j L (coinLift c)) := by
  intro j
  induction j with
  | zero =>
    intro L hL
    have hconst : (fun c : Fin (0 * R) → Fin 2 => detSieveRun n m R 0 L (coinLift c))
        = Function.const (Fin (0 * R) → Fin 2) L := by
      funext c; rfl
    show (PMF.pure L) = _
    rw [hconst, PMF.map_const]
  | succ j ih =>
    intro L hL
    rw [show idealSieveRec n m (j+1) L
        = (idealSieveRec n m j L).bind (fun L' => idealLayerAux n
            (sievePair n (sieveWindowWidth n m j) (m * j) L')) from rfl,
      ih L hL, PMF.bind_map]
    show (PMF.uniformOfFintype' (Fin (j * R) → Fin 2)).bind
        (fun c => idealLayerAux n (sievePair n (sieveWindowWidth n m j) (m * j)
          (detSieveRun n m R j L (coinLift c)))) = _
    have hps_le : ∀ c : Fin (j * R) → Fin 2,
        (sievePair n (sieveWindowWidth n m j) (m * j)
            (detSieveRun n m R j L (coinLift c))).length ≤ R := by
      intro c
      have h1 : 2 * (sievePair n (sieveWindowWidth n m j) (m * j)
          (detSieveRun n m R j L (coinLift c))).length
          ≤ (detSieveRun n m R j L (coinLift c)).length :=
        sievePairWith_length_bound n id (sieveWindowWidth n m j) (m * j)
          (detSieveRun n m R j L (coinLift c))
      have h2 := detSieveRun_length_le n m R j L (coinLift c)
      omega
    have hinner : ∀ c : Fin (j * R) → Fin 2,
        idealLayerAux n (sievePair n (sieveWindowWidth n m j) (m * j)
            (detSieveRun n m R j L (coinLift c)))
        = (PMF.uniformOfFintype' (Fin R → Fin 2)).map
          (fun d => layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
            (sievePair n (sieveWindowWidth n m j) (m * j)
              (detSieveRun n m R j L (coinLift c))) (coinLift d)) := by
      intro c
      have hcR := hps_le c
      rw [idealLayerAux_eq_map_run, ← uni_lift hcR
        (F := fun c' => layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
          (sievePair n (sieveWindowWidth n m j) (m * j)
            (detSieveRun n m R j L (coinLift c))) (coinLift c'))]
      congr 1
      funext d
      refine layerRunGen_congr _ _ _ _ ?_
      intro i hi
      show coinLift (fun i => d (Fin.castLE hcR i)) i = coinLift d i
      rw [coinLift_lt _ hi, coinLift_lt _ (by omega : i < R)]
      rfl
    refine (congrArg (PMF.bind (PMF.uniformOfFintype' (Fin (j * R) → Fin 2)))
      (funext hinner)).trans ?_
    rw [← uni_glue (N := j * R) (K := R)
      (G := fun c d => layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
        (sievePair n (sieveWindowWidth n m j) (m * j)
          (detSieveRun n m R j L (coinLift c))) (coinLift d))]
    rw [show (j + 1) * R = j * R + R from by ring]
    congr 1
    funext d
    have hrest : detSieveRun n m R j L (coinLift (takeTape d))
        = detSieveRun n m R j L (coinLift d) := by
      refine detSieveRun_congr n m R L hL j _ _ ?_
      intro i hi
      show coinLift (takeTape d) i = coinLift d i
      rw [coinLift_lt _ hi, coinLift_lt _ (by omega : i < j * R + R)]
      rfl
    have hcoins : coinLift (dropTape d) = (fun i => coinLift d (j * R + i)) := by
      funext i
      by_cases hi : i < R
      · rw [coinLift_lt _ hi, coinLift_lt _ (by omega : j * R + i < j * R + R)]
        rfl
      · rw [coinLift_ge _ hi, coinLift_ge _ (by omega)]
    show layerRunGen (fun p : ZMod (2^n) × ZMod (2^n) => p.2 - p.1)
        (sievePair n (sieveWindowWidth n m j) (m * j)
          (detSieveRun n m R j L (coinLift (takeTape d)))) (coinLift (dropTape d))
      = detSieveRun n m R (j + 1) L (coinLift d)
    rw [hrest, hcoins]
    rfl

/-- For `R > 0`, fresh-label sampling followed by `m` ideal stages equals deterministic
execution on a uniformly sampled label table and binary tape. -/
private theorem mu_factorized (n m R : ℕ) (_hR : 0 < R) :
    (idealFreshRecords n R).bind (idealSieveRec n m m) =
    (PMF.uniformOfFintype' ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2))).map
      (fun p => detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)) := by
  rw [fresh_table n R, PMF.bind_map]
  show (PMF.uniformOfFintype' (Fin R → ZMod (2^n))).bind
      (fun a => idealSieveRec n m m (List.ofFn a)) = _
  rw [← uni_bind_map_prod (fun (a : Fin R → ZMod (2^n)) (c : Fin (m * R) → Fin 2) =>
    detSieveRun n m R m (List.ofFn a) (coinLift c))]
  refine congrArg (PMF.bind (PMF.uniformOfFintype' (Fin R → ZMod (2^n)))) (funext fun a => ?_)
  rw [idealSieveRec_eq_map_det n m R m (List.ofFn a)
    (by rw [List.length_ofFn])]

/-- Reduction of a label modulo `2^n` to its residue modulo `2^(n-1)`. -/
private def lowb {n : ℕ} (x : ZMod (2 ^ n)) : ZMod (2 ^ (n - 1)) :=
  ((x.val % 2 ^ (n - 1) : ℕ) : ZMod (2 ^ (n - 1)))

/-- The canonical value of `lowb x` is `x.val % 2^(n-1)`. -/
private theorem lowb_val {n : ℕ} (x : ZMod (2 ^ n)) :
    (lowb x).val = x.val % 2 ^ (n - 1) := by
  rw [lowb, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ (by positivity))]

/-- The natural power `2^(n-1)` divides `2^n`. -/
private theorem pow_sub_dvd {n : ℕ} : (2 : ℕ) ^ (n - 1) ∣ 2 ^ n :=
  pow_dvd_pow 2 (Nat.sub_le n 1)

/-- Reduction by `lowb` preserves addition. -/
private theorem lowb_add {n : ℕ} (x y : ZMod (2 ^ n)) :
    lowb (x + y) = lowb x + lowb y := by
  apply ZMod.val_injective
  rw [lowb_val, ZMod.val_add, Nat.mod_mod_of_dvd _ pow_sub_dvd, ZMod.val_add, lowb_val,
    lowb_val, Nat.add_mod]

/-- Reduction by `lowb` preserves subtraction. -/
private theorem lowb_sub {n : ℕ} (x y : ZMod (2 ^ n)) :
    lowb (x - y) = lowb x - lowb y := by
  refine eq_sub_of_add_eq ?_
  rw [← lowb_add, sub_add_cancel]

/-- Dividing the residue modulo `2^(t+w)` by `2^t` gives the quotient modulo `2^w`. -/
private theorem mod_div_split (a t w : ℕ) :
    (a % 2 ^ (t + w)) / 2 ^ t = (a / 2 ^ t) % 2 ^ w := by
  have h1 : 2 ^ t * (a / 2 ^ t) + a % 2 ^ t = a := Nat.div_add_mod a (2 ^ t)
  have h2 : 2 ^ w * ((a / 2 ^ t) / 2 ^ w) + (a / 2 ^ t) % 2 ^ w = a / 2 ^ t :=
    Nat.div_add_mod _ (2 ^ w)
  have hvt : a % 2 ^ t < 2 ^ t := Nat.mod_lt _ (by omega)
  have h4 : a / 2 ^ (t + w) = (a / 2 ^ t) / 2 ^ w := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h3 : 2 ^ (t + w) * (a / 2 ^ (t + w)) + a % 2 ^ (t + w) = a :=
    Nat.div_add_mod a (2 ^ (t + w))
  rw [h4] at h3
  have e2 : 2 ^ t * (2 ^ w * ((a / 2 ^ t) / 2 ^ w) + (a / 2 ^ t) % 2 ^ w)
      = 2 ^ (t + w) * ((a / 2 ^ t) / 2 ^ w) + 2 ^ t * ((a / 2 ^ t) % 2 ^ w) := by
    rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
  have e3 : 2 ^ t * (a / 2 ^ t)
      = 2 ^ t * (2 ^ w * ((a / 2 ^ t) / 2 ^ w) + (a / 2 ^ t) % 2 ^ w) := by
    rw [h2]
  have e4 : 2 ^ (t + w) * ((a / 2 ^ t) / 2 ^ w) + 2 ^ t * ((a / 2 ^ t) % 2 ^ w) + a % 2 ^ t = a := by
    rw [← e2, ← e3, h1]
  have h6 : a % 2 ^ (t + w) = 2 ^ t * ((a / 2 ^ t) % 2 ^ w) + a % 2 ^ t := by
    have hc : 2 ^ (t + w) * (a / 2 ^ t / 2 ^ w) + a % 2 ^ (t + w)
        = 2 ^ (t + w) * (a / 2 ^ t / 2 ^ w) + 2 ^ t * (a / 2 ^ t % 2 ^ w) + a % 2 ^ t :=
      h3.trans e4.symm
    omega
  rw [h6, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : (0:ℕ) < 2 ^ t),
    Nat.div_eq_of_lt hvt]
  simp

/-- A window contained in the lowest `n-1` bits has the same agreement test before and after
applying `lowb`. -/
private theorem windowAgree_low {n w t : ℕ} (htw : t + w ≤ n - 1)
    (x y : ZMod (2 ^ n)) :
    windowAgree n w t x y ↔ windowAgree (n - 1) w t (lowb x) (lowb y) := by
  have key : ∀ z : ZMod (2 ^ n),
      (z.val / 2 ^ t) % 2 ^ w = ((z.val % 2 ^ (n - 1)) / 2 ^ t) % 2 ^ w := by
    intro z
    rw [← mod_div_split z.val t w, ← mod_div_split (z.val % 2 ^ (n - 1)) t w,
      Nat.mod_mod_of_dvd z.val (pow_dvd_pow 2 htw)]
  constructor
  · intro h
    have h' : (x.val / 2 ^ t) % 2 ^ w = (y.val / 2 ^ t) % 2 ^ w := h
    show ((lowb x).val / 2 ^ t) % 2 ^ w = ((lowb y).val / 2 ^ t) % 2 ^ w
    rw [lowb_val, lowb_val, ← key x, ← key y]
    exact h'
  · intro h
    have h' : ((lowb x).val / 2 ^ t) % 2 ^ w = ((lowb y).val / 2 ^ t) % 2 ^ w := h
    show (x.val / 2 ^ t) % 2 ^ w = (y.val / 2 ^ t) % 2 ^ w
    rw [lowb_val, lowb_val] at h'
    rw [key x, key y]
    exact h'

/-- Reconstruction of an `n`-bit label table from a table of its lowest `n-1` bits and a binary
top-bit table. -/
private def tabCombine {n R : ℕ} (ℓ : Fin R → ZMod (2 ^ (n - 1))) (t : Fin R → Fin 2) :
    Fin R → ZMod (2 ^ n) :=
  fun i => ((ℓ i).val + 2 ^ (n - 1) * (t i).val : ℕ)

/-- For `n ≥ 1`, two copies of `2^(n-1)` sum to `2^n`. -/
private theorem h2pow {n : ℕ} (hn : 1 ≤ n) : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  subst hk
  rw [Nat.add_comm 1 k]
  show (2:ℕ) ^ k + 2 ^ k = 2 ^ (k + 1)
  rw [Nat.pow_succ]
  ring

/-- For `n ≥ 1`, each integer reconstructed from a low residue and a top bit is less than `2^n`. -/
private theorem tabCombine_val_lt {n R : ℕ} (hn : 1 ≤ n) (ℓ : Fin R → ZMod (2 ^ (n - 1)))
    (t : Fin R → Fin 2) (i : Fin R) :
    (ℓ i).val + 2 ^ (n - 1) * (t i).val < 2 ^ n := by
  have h2 : (ℓ i).val < 2 ^ (n - 1) := ZMod.val_lt _
  have h3 : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← h2pow hn]; omega
  rcases (by omega : (t i).val = 0 ∨ (t i).val = 1) with h0 | h1
  · rw [h0, Nat.mul_zero, Nat.add_zero]; omega
  · rw [h1, Nat.mul_one]; omega

/-- For `n ≥ 1`, the canonical value of a reconstructed table entry is its low value plus
`2^(n-1)` times its top bit. -/
private theorem tabCombine_val {n R : ℕ} (hn : 1 ≤ n) (ℓ : Fin R → ZMod (2 ^ (n - 1)))
    (t : Fin R → Fin 2) (i : Fin R) :
    (tabCombine ℓ t i).val = (ℓ i).val + 2 ^ (n - 1) * (t i).val :=
  ZMod.val_cast_of_lt (tabCombine_val_lt hn ℓ t i)

/-- For `n ≥ 1`, reducing a reconstructed table entry recovers its low residue. -/
private theorem lowb_tabCombine {n R : ℕ} (hn : 1 ≤ n) (ℓ : Fin R → ZMod (2 ^ (n - 1)))
    (t : Fin R → Fin 2) (i : Fin R) :
    lowb (tabCombine ℓ t i) = ℓ i := by
  apply ZMod.val_injective
  rw [lowb_val, tabCombine_val hn, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-- The binary top-bit table of labels modulo `2^n`, defined when `n ≥ 1`. -/
private def tabTop {n R : ℕ} (hn : 1 ≤ n) (a : Fin R → ZMod (2 ^ n)) : Fin R → Fin 2 :=
  fun i => ⟨(a i).val / 2 ^ (n - 1), by
    have h := ZMod.val_lt (a i)
    have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by rw [← h2pow hn]; omega
    exact Nat.div_lt_of_lt_mul (by omega : (a i).val < 2 ^ (n - 1) * 2)⟩

/-- The table obtained by reducing each label with `lowb`. -/
private def tabLow {n R : ℕ} (a : Fin R → ZMod (2 ^ n)) : Fin R → ZMod (2 ^ (n - 1)) :=
  fun i => lowb (a i)

/-- For `n ≥ 1`, combining a label table's low and top-bit tables reconstructs the original
table. -/
private theorem tabCombine_tabLow {n R : ℕ} (hn : 1 ≤ n) (a : Fin R → ZMod (2 ^ n)) :
    tabCombine (tabLow a) (tabTop hn a) = a := by
  funext i
  apply ZMod.val_injective
  rw [tabCombine_val hn, show tabLow a i = lowb (a i) from rfl, lowb_val,
    show ((tabTop hn a i) : ℕ) = (a i).val / 2 ^ (n - 1) from rfl, Nat.mod_add_div]

/-- For `n ≥ 1`, combining low residues and top bits is a bijection onto full label tables. -/
private theorem tabCombine_bij {n R : ℕ} (hn : 1 ≤ n) :
    Function.Bijective
      (fun p : (Fin R → ZMod (2 ^ (n - 1))) × (Fin R → Fin 2) => tabCombine p.1 p.2) := by
  constructor
  · rintro ⟨ℓ, t⟩ ⟨ℓ', t'⟩ h
    have hfun : tabCombine ℓ t = tabCombine ℓ' t' := h
    have key : ∀ i : Fin R,
        (ℓ i).val + 2 ^ (n - 1) * (t i).val
          = (ℓ' i).val + 2 ^ (n - 1) * (t' i).val := by
      intro i
      have h1 := tabCombine_val hn ℓ t i
      have h2 := tabCombine_val hn ℓ' t' i
      rw [← h1, ← h2, congrFun hfun i]
    have hℓ : ℓ = ℓ' := by
      funext i
      have hm : ((ℓ i).val) % 2 ^ (n - 1) = ((ℓ' i).val) % 2 ^ (n - 1) := by
        have hvv := key i
        have hmod : (((ℓ i).val + 2 ^ (n - 1) * (t i).val) % 2 ^ (n - 1))
            = (((ℓ' i).val + 2 ^ (n - 1) * (t' i).val) % 2 ^ (n - 1)) := by rw [hvv]
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at hmod
        exact hmod
      apply ZMod.val_injective
      rw [Nat.mod_eq_of_lt (ZMod.val_lt (ℓ i)), Nat.mod_eq_of_lt (ZMod.val_lt (ℓ' i))] at hm
      exact hm
    have ht : t = t' := by
      funext i
      have hv := key i
      have hvℓ : (ℓ i).val = (ℓ' i).val := congrArg ZMod.val (congrFun hℓ i)
      have hteq : 2 ^ (n - 1) * (t i).val = 2 ^ (n - 1) * (t' i).val := by omega
      have hc : (0:ℕ) < 2 ^ (n - 1) := by positivity
      have htv : (t i).val = (t' i).val := by
        rcases (by omega : (t i).val = 0 ∨ (t i).val = 1) with h1 | h1 <;>
          rcases (by omega : (t' i).val = 0 ∨ (t' i).val = 1) with h2 | h2 <;>
          rw [h1, h2] at hteq ⊢
        all_goals simp at hteq
        all_goals omega
      exact Fin.ext htv
    exact Prod.ext_iff.2 ⟨hℓ, ht⟩
  · intro a
    exact ⟨(tabLow a, tabTop hn a), tabCombine_tabLow hn a⟩

/-- For `n ≥ 1`, combining uniformly sampled low residues and top bits gives a uniform full
label table. -/
private theorem table_split {n R : ℕ} (hn : 1 ≤ n) :
    (PMF.uniformOfFintype' ((Fin R → ZMod (2 ^ (n - 1))) × (Fin R → Fin 2))).map
        (fun p => tabCombine p.1 p.2)
      = PMF.uniformOfFintype' (Fin R → ZMod (2 ^ n)) :=
  uni_bij _ (tabCombine_bij hn)

/-- A full-label record paired with finite sets of positive and negative ancestor indices. -/
private abbrev ERec (n R : ℕ) : Type := ZMod (2 ^ n) × Finset (Fin R) × Finset (Fin R)

/-- A reduced-label record paired with finite sets of positive and negative ancestor indices. -/
private abbrev SRec (n R : ℕ) : Type := ZMod (2 ^ (n - 1)) × Finset (Fin R) × Finset (Fin R)

/-- The full-label difference record whose positive ancestors are the second positive and first
negative ancestors, and whose negative ancestors are the second negative and first positive
ancestors. -/
private def eChild {n R : ℕ} (p : ERec n R × ERec n R) : ERec n R :=
  (p.2.1 - p.1.1, p.2.2.1 ∪ p.1.2.2, p.2.2.2 ∪ p.1.2.1)

/-- The reduced-label difference record with the corresponding unions of positive and negative
ancestor indices. -/
private def sChild {n R : ℕ} (p : SRec n R × SRec n R) : SRec n R :=
  (p.2.1 - p.1.1, p.2.2.1 ∪ p.1.2.2, p.2.2.2 ∪ p.1.2.1)

/-- Deterministic full-label sieving that carries signed ancestor sets through every retained
pair difference. -/
private def eRun (n m R : ℕ) :
    ℕ → List (ERec n R) → (ℕ → Fin 2) → List (ERec n R)
  | 0, E, _ => E
  | j + 1, E, C =>
    layerRunGen eChild
      (sievePairWith n (fun e : ERec n R => e.1) (sieveWindowWidth n m j) (m * j)
        (eRun n m R j E C))
      (fun i => C (j * R + i))

/-- Deterministic reduced-label sieving that carries signed ancestor sets and uses the full
sieve's stage windows. -/
private def sRun (n m R : ℕ) :
    ℕ → List (SRec n R) → (ℕ → Fin 2) → List (SRec n R)
  | 0, S, _ => S
  | j + 1, S, C =>
    layerRunGen sChild
      (sievePairWith (n - 1) (fun s : SRec n R => s.1) (sieveWindowWidth n m j) (m * j)
        (sRun n m R j S C))
      (fun i => C (j * R + i))

/-- The initial full-label record list, assigning each table entry its own positive singleton
ancestor and no negative ancestors. -/
private def eInit {n R : ℕ} (a : Fin R → ZMod (2 ^ n)) : List (ERec n R) :=
  List.ofFn (fun i : Fin R => (a i, {i}, (∅ : Finset (Fin R))))

/-- The initial reduced-label record list, assigning each table entry its own positive singleton
ancestor and no negative ancestors. -/
private def sInit {n R : ℕ} (ℓ : Fin R → ZMod (2 ^ (n - 1))) : List (SRec n R) :=
  List.ofFn (fun i : Fin R => (ℓ i, {i}, (∅ : Finset (Fin R))))

/-- An element occurring in a list without duplicates has count one. -/
private theorem count_eq_one_fix {α : Type} [DecidableEq α] {L : List α} {x : α}
    (hx : x ∈ L) (hnodup : L.Nodup) : L.count x = 1 :=
  List.count_eq_one_of_mem hnodup hx

/-- Erasing a present element from a list without duplicates leaves exactly the other original
elements. -/
private theorem mem_erase_nodup {α : Type} [DecidableEq α] {L : List α} (hL : L.Nodup)
    {b : α} (hb : b ∈ L) : ∀ x : α, x ∈ L.erase b ↔ (x ∈ L ∧ x ≠ b) := by
  intro x
  constructor
  · intro hx
    refine ⟨List.mem_of_mem_erase hx, ?_⟩
    intro hxb
    subst hxb
    have hcount : (L.erase x).count x = 0 := by
      rw [List.count_erase, count_eq_one_fix hb hL]
      simp
    have hc1 : (L.erase x).count x = 1 :=
      count_eq_one_fix hx (hL.erase x)
    omega
  · rintro ⟨hxL, hxb⟩
    exact (List.mem_erase_of_ne hxb).2 hxL

/-- Predicates agreeing on all elements of a list have the same first matching element. -/
private theorem find?_congr' {α : Type} (p q : α → Bool) :
    ∀ (L : List α), (∀ x ∈ L, p x = q x) → L.find? p = L.find? q := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons x L ih =>
    intro h
    have hpx : p x = q x := h x List.mem_cons_self
    by_cases hp : p x = true
    · have hq : q x = true := by rw [← hpx]; exact hp
      rw [List.find?_cons, List.find?_cons, hp, hq]
    · have hp' : p x = false := by
        rcases Bool.eq_false_or_eq_true (p x) with hpc | hpc
        · exact absurd hpc hp
        · exact hpc
      have hq' : q x = false := by rw [← hpx]; exact hp'
      rw [List.find?_cons, List.find?_cons, hp', hq']
      exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- Erasing a mapped first match commutes with mapping the list after erasing that match. -/
private theorem pair_erase_map {α β : Type} [DecidableEq α] [DecidableEq β] (Q : α → Bool)
    (f : β → α) : ∀ (L : List β) (r' : β), L.find? (fun x => Q (f x)) = some r' →
      (L.map f).erase (f r') = (L.erase r').map f := by
  intro L
  induction L with
  | nil => intro r' h; simp at h
  | cons x L ih =>
    intro r' h
    by_cases hx : Q (f x) = true
    · have heq : (x :: L).find? (fun x => Q (f x)) = some x := by
        simp [hx]
      rw [heq] at h
      have h' := Option.some.inj h
      subst h'
      rw [List.map_cons, List.erase_cons_head, List.erase_cons_head]
    · have heq : (x :: L).find? (fun x => Q (f x)) = L.find? (fun x => Q (f x)) := by
        simp [hx]
      rw [heq] at h
      have hmem : r' ∈ L := List.mem_of_find?_eq_some h
      have ihL := ih r' h
      have hqr : Q (f r') = true := List.find?_some (p := fun x => Q (f x)) h
      have hne : f x ≠ f r' := by
        intro hcon
        rw [hcon] at hx
        exact hx hqr
      have hxe : r' ≠ x := by
        intro hcon
        exact hne (hcon ▸ rfl)
      rw [List.map_cons, List.erase_cons_tail (by simpa using! hne),
        List.erase_cons_tail (by simpa using! hxe.symm), ihL]
      rfl

/-- Pair selection skips the head when no remaining label agrees with its window. -/
private theorem pairWith_cons_none {n w t : ℕ} {α : Type} [DecidableEq α]
    (lab : α → ZMod (2 ^ n)) (r : α) {rest : List α}
    (h : rest.find? (fun x => decide (windowAgree n w t (lab r) (lab x))) = none) :
    sievePairWith n lab w t (r :: rest) = sievePairWith n lab w t rest := by
  simp only [sievePairWith]
  split
  · rfl
  · rename_i a hsome
    have hc := h.symm.trans hsome
    simp at hc

/-- Pair selection pairs the head with the first window-agreeing record, then recurses after
erasing that record. -/
private theorem pairWith_cons_some {n w t : ℕ} {α : Type} [DecidableEq α]
    (lab : α → ZMod (2 ^ n)) (r : α) {rest : List α} {r' : α}
    (h : rest.find? (fun x => decide (windowAgree n w t (lab r) (lab x))) = some r') :
    sievePairWith n lab w t (r :: rest)
      = (r, r') :: sievePairWith n lab w t (rest.erase r') := by
  simp only [sievePairWith]
  split
  · rename_i hnone
    have h2 : List.find? (fun r' => decide (windowAgree n w t (lab r) (lab r'))) rest
        = some r' := h
    have hc := h2.symm.trans hnone
    simp at hc
  · rename_i a hsome
    have h2 : List.find? (fun r' => decide (windowAgree n w t (lab r) (lab r'))) rest
        = some r' := h
    have ha : a = r' := (Option.some.inj (h2.symm.trans hsome)).symm
    rw [ha]

/-- Pair selection commutes with mapping records when the labeling function is composed with
that map. -/
private theorem pair_map {n w t : ℕ} {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : β → α) (lab : α → ZMod (2 ^ n)) :
    ∀ (L : List β), sievePairWith n lab w t (L.map f)
      = (sievePairWith n (fun x => lab (f x)) w t L).map (fun p => (f p.1, f p.2)) := by
  intro L
  fun_induction sievePairWith n (fun x => lab (f x)) w t L
  · simp [sievePairWith]
  · rename_i r rest hfind ih
    have hnone : (rest.map f).find?
        (fun v => decide (windowAgree n w t (lab (f r)) (lab v))) = none := by
      rw [List.find?_eq_none]
      intro v hv
      obtain ⟨x, hx, hvx⟩ := List.mem_map.1 hv
      have hthis := (List.find?_eq_none.1 hfind) x hx
      rw [hvx] at hthis
      exact hthis
    rw [List.map_cons, pairWith_cons_none lab (f r) hnone]
    exact ih
  · rename_i r rest r' hfind ih
    have hsome : (rest.map f).find?
        (fun v => decide (windowAgree n w t (lab (f r)) (lab v))) = some (f r') := by
      rw [List.find?_map]
      have hbeta : ((fun v => decide (windowAgree n w t (lab (f r)) (lab v))) ∘ f)
          = (fun x => decide (windowAgree n w t (lab (f r)) (lab (f x)))) := rfl
      rw [hbeta, hfind]
      rfl
    have hemap : (List.map f rest).erase (f r') = List.map f (rest.erase r') :=
      pair_erase_map (fun v => decide (windowAgree n w t (lab (f r)) (lab v))) f rest r' hfind
    rw [List.map_cons, pairWith_cons_some lab (f r) hsome, List.map_cons, hemap]
    exact congr (congrArg List.cons rfl) ih

/-- Labelings with equivalent window-agreement tests produce identical selected pairs. -/
private theorem pair_label_congr {n n' w t : ℕ} {α : Type} [DecidableEq α]
    (lab : α → ZMod (2 ^ n)) (lab' : α → ZMod (2 ^ n'))
    (h : ∀ x y : α, windowAgree n w t (lab x) (lab y) ↔ windowAgree n' w t (lab' x) (lab' y)) :
    ∀ (L : List α), sievePairWith n lab w t L = sievePairWith n' lab' w t L := by
  intro L
  fun_induction sievePairWith n lab w t L
  · simp [sievePairWith]
  · rename_i r rest hfind ih
    have hc : rest.find? (fun x => decide (windowAgree n w t (lab r) (lab x)))
        = rest.find? (fun x => decide (windowAgree n' w t (lab' r) (lab' x))) := by
      refine find?_congr' _ _ rest ?_
      intro x hx
      rw [decide_eq_decide]
      exact h r x
    have hfx : List.find? (fun x => decide (windowAgree n w t (lab r) (lab x))) rest = none :=
      hfind
    rw [pairWith_cons_none lab' r (hc.symm.trans hfx)]
    exact ih
  · rename_i r rest r' hfind ih
    have hc : rest.find? (fun x => decide (windowAgree n w t (lab r) (lab x)))
        = rest.find? (fun x => decide (windowAgree n' w t (lab' r) (lab' x))) := by
      refine find?_congr' _ _ rest ?_
      intro x hx
      rw [decide_eq_decide]
      exact h r x
    have hfx : List.find? (fun x => decide (windowAgree n w t (lab r) (lab x))) rest = some r' :=
      hfind
    rw [pairWith_cons_some lab' r (hc.symm.trans hfx)]
    exact congr (congrArg List.cons rfl) ih

/-- Mapping deterministic layer outputs commutes with layer execution when the map intertwines
the two child functions. -/
private theorem layerRunGen_map {α β : Type} (child : α × α → α) (child₂ : β × β → β)
    (g : α → β) (hg : ∀ p : α × α, g (child p) = child₂ (g p.1, g p.2)) :
    ∀ (ps : List (α × α)) (C : ℕ → Fin 2),
      (layerRunGen child ps C).map g
        = layerRunGen child₂ (ps.map (fun p => (g p.1, g p.2))) C := by
  intro ps
  induction ps with
  | nil => intro C; rfl
  | cons p ps ih =>
    intro C
    show ((if C 0 = 1 then [child p] else []) ++
      layerRunGen child ps (fun i => C (i + 1))).map g = _
    rw [List.map_append]
    by_cases h : C 0 = 1
    · simp only [h, if_true, hg p, ih (fun i => C (i + 1)),
      List.map_cons, layerRunGen]
      rfl
    · simp only [h, if_false, List.map_nil, ih (fun i => C (i + 1)),
      List.map_cons, layerRunGen, List.nil_append]

/-- Every deterministic layer output is the child of some input pair. -/
private theorem layerRunGen_mem {α : Type} (child : α × α → α) :
    ∀ (ps : List (α × α)) (C : ℕ → Fin 2) (x : α), x ∈ layerRunGen child ps C →
      ∃ p ∈ ps, x = child p := by
  intro ps
  induction ps with
  | nil => intro C x hx; simp [layerRunGen] at hx
  | cons p ps ih =>
    intro C x hx
    simp only [layerRunGen] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases h : C 0 = 1
      · rw [if_pos h] at hx
        rw [List.mem_singleton] at hx
        exact ⟨p, List.mem_cons_self, hx⟩
      · rw [if_neg h] at hx; simp at hx
    · obtain ⟨p', hp', hx'⟩ := ih _ x hx
      exact ⟨p', List.mem_cons_of_mem _ hp', hx'⟩

/-- A deterministic layer output has no duplicates if the input pairs have no duplicates and the
child function is injective on those pairs. -/
private theorem layerRunGen_nodup {α : Type} (child : α × α → α) :
    ∀ (ps : List (α × α)) (C : ℕ → Fin 2),
      ps.Nodup → (∀ p ∈ ps, ∀ p' ∈ ps, child p = child p' → p = p') →
        (layerRunGen child ps C).Nodup := by
  intro ps
  induction ps with
  | nil => intro C _ _; exact List.nodup_nil
  | cons p ps ih =>
    intro C hnodup hinj
    have hnodup_ps : ps.Nodup := (List.nodup_cons.1 hnodup).2
    have hrec := ih (fun i => C (i + 1)) hnodup_ps (fun q hq q' hq' h =>
      hinj _ (List.mem_cons_of_mem _ hq) _ (List.mem_cons_of_mem _ hq') h)
    show ((if C 0 = 1 then [child p] else []) ++
      layerRunGen child ps (fun i => C (i + 1))).Nodup
    by_cases h : C 0 = 1
    · rw [if_pos h]
      refine List.Nodup.append (by simp) hrec ?_
      intro x hx hy
      rw [List.mem_singleton] at hx
      subst hx
      obtain ⟨q, hq, hxy'⟩ := layerRunGen_mem child ps (fun i => C (i + 1)) (child p) hy
      have hpq : p = q := hinj p List.mem_cons_self q (List.mem_cons_of_mem _ hq) hxy'
      exact (List.nodup_cons.1 hnodup).1 (hpq ▸ hq)
    · rw [if_neg h]
      exact hrec

/-- Distinct pairs selected from a list without duplicates share no component. -/
private theorem pair_sep {n w t : ℕ} {α : Type} [DecidableEq α] (lab : α → ZMod (2 ^ n)) :
    ∀ (L : List α), L.Nodup → ∀ p p' : α × α,
      p ∈ sievePairWith n lab w t L → p' ∈ sievePairWith n lab w t L → p ≠ p' →
      p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2 := by
  intro L
  fun_induction sievePairWith n lab w t L
  · intro _ p p' hp _; simp at hp
  · rename_i r rest hfind ih
    intro hL p p' hp hp' hne
    exact ih (List.nodup_cons.1 hL).2 p p' hp hp' hne
  · rename_i r rest r' hfind ih
    intro hL p p' hp hp' hne
    have hnodup_rest : rest.Nodup := (List.nodup_cons.1 hL).2
    have hrnot : r ∉ rest := (List.nodup_cons.1 hL).1
    have hr'mem : r' ∈ rest := List.mem_of_find?_eq_some hfind
    have hnodup_er : (rest.erase r').Nodup := hnodup_rest.erase r'
    have hrec_mem : ∀ q ∈ sievePairWith n lab w t (rest.erase r'),
        q.1 ∈ rest.erase r' ∧ q.2 ∈ rest.erase r' := by
      intro q hq
      have := sievePairWith_mem_window q hq
      exact ⟨this.1, this.2.1⟩
    rw [List.mem_cons] at hp hp'
    rcases hp with hp | hp
    · rcases hp' with hp' | hp'
      · subst hp; subst hp'; exact absurd rfl hne
      · subst hp
        obtain ⟨hz1, hz2⟩ := hrec_mem p' hp'
        rw [mem_erase_nodup hnodup_rest hr'mem] at hz1 hz2
        show r ≠ p'.1 ∧ r ≠ p'.2 ∧ r' ≠ p'.1 ∧ r' ≠ p'.2
        exact ⟨fun hcon => hrnot (hcon ▸ hz1.1),
          fun hcon => hrnot (hcon ▸ hz2.1),
          fun hcon => hz1.2 hcon.symm,
          fun hcon => hz2.2 hcon.symm⟩
    · rcases hp' with hp' | hp'
      · subst hp'
        obtain ⟨hz1, hz2⟩ := hrec_mem p hp
        rw [mem_erase_nodup hnodup_rest hr'mem] at hz1 hz2
        show p.1 ≠ r ∧ p.1 ≠ r' ∧ p.2 ≠ r ∧ p.2 ≠ r'
        exact ⟨fun hcon => hrnot (hcon ▸ hz1.1),
          fun hcon => hz1.2 hcon,
          fun hcon => hrnot (hcon ▸ hz2.1),
          fun hcon => hz2.2 hcon⟩
      · exact ih hnodup_er p p' hp hp' hne

/-- Pair selection from a list without duplicates produces a list without duplicate pairs. -/
private theorem pair_nodup {n w t : ℕ} {α : Type} [DecidableEq α] (lab : α → ZMod (2 ^ n)) :
    ∀ (L : List α), L.Nodup → (sievePairWith n lab w t L).Nodup := by
  intro L
  fun_induction sievePairWith n lab w t L
  · intro _; simp
  · rename_i r rest hfind ih
    intro hL
    exact ih (List.nodup_cons.1 hL).2
  · rename_i r rest r' hfind ih
    intro hL
    have hnodup_rest : rest.Nodup := (List.nodup_cons.1 hL).2
    have hrnot : r ∉ rest := (List.nodup_cons.1 hL).1
    have hr'mem : r' ∈ rest := List.mem_of_find?_eq_some hfind
    refine List.nodup_cons.2 ⟨?_, ih (hnodup_rest.erase r')⟩
    intro hcon
    have h1 := sievePairWith_mem_window (r, r') hcon
    exact hrnot (List.mem_of_mem_erase h1.1)

/-- The two components of each pair selected from a list without duplicates are distinct. -/
private theorem pair_ne {n w t : ℕ} {α : Type} [DecidableEq α] (lab : α → ZMod (2 ^ n)) :
    ∀ (L : List α), L.Nodup → ∀ p : α × α,
      p ∈ sievePairWith n lab w t L → p.1 ≠ p.2 := by
  intro L
  fun_induction sievePairWith n lab w t L
  · intro _ p hp; simp at hp
  · rename_i r rest hfind ih
    intro hL p hp
    exact ih (List.nodup_cons.1 hL).2 p hp
  · rename_i r rest r' hfind ih
    intro hL p hp
    have hnodup_rest : rest.Nodup := (List.nodup_cons.1 hL).2
    have hrnot : r ∉ rest := (List.nodup_cons.1 hL).1
    have hr'mem : r' ∈ rest := List.mem_of_find?_eq_some hfind
    have hnodup_er : (rest.erase r').Nodup := hnodup_rest.erase r'
    rw [List.mem_cons] at hp
    rcases hp with hp | hp
    · subst hp
      show r ≠ r'
      intro hcon
      exact hrnot (by rw [hcon]; exact hr'mem)
    · exact ih hnodup_er p hp

/-- The signed sum of table entries over positive and negative ancestor sets. -/
private def valOf {n R : ℕ} (a : Fin R → ZMod (2 ^ n)) (P N : Finset (Fin R)) : ZMod (2 ^ n) :=
  (∑ i ∈ P, a i) - (∑ i ∈ N, a i)

/-- A singleton positive ancestor and an empty negative ancestor set evaluate to the
corresponding table entry. -/
private theorem valOf_eInit {n R : ℕ} (a : Fin R → ZMod (2 ^ n)) (i : Fin R) :
    valOf a {i} (∅ : Finset (Fin R)) = a i := by
  rw [valOf, Finset.sum_empty, sub_zero, Finset.sum_singleton]

/-- For disjoint ancestor supports, the child ancestor sets evaluate to the second signed sum
minus the first. -/
private theorem valOf_child {n R : ℕ} (a : Fin R → ZMod (2 ^ n)) {P1 P2 N1 N2 : Finset (Fin R)}
    (hd : Disjoint (P1 ∪ N1) (P2 ∪ N2)) :
    valOf a (P2 ∪ N1) (N2 ∪ P1) = valOf a P2 N2 - valOf a P1 N1 := by
  have hd1 : Disjoint P2 N1 :=
    Disjoint.mono (Finset.subset_union_left) (Finset.subset_union_right) hd.symm
  have hd2 : Disjoint N2 P1 :=
    Disjoint.mono (Finset.subset_union_right) (Finset.subset_union_left) hd.symm
  unfold valOf
  rw [Finset.sum_union hd1, Finset.sum_union hd2]
  ring

/-- The ancestor support of a child is the union of its two parent supports. -/
private theorem eChild_supp {n R : ℕ} (p : ERec n R × ERec n R) :
    (eChild p).2.1 ∪ (eChild p).2.2
      = (p.1.2.1 ∪ p.1.2.2) ∪ (p.2.2.1 ∪ p.2.2.2) := by
  ext i
  simp only [eChild, Finset.mem_union]
  tauto

/-- A full-label child preserves representation by the signed ancestor sum when the parent
representations hold and their supports are disjoint. -/
private theorem eChild_val {n R : ℕ} (a : Fin R → ZMod (2 ^ n)) (p : ERec n R × ERec n R)
    (h1 : p.1.1 = valOf a p.1.2.1 p.1.2.2) (h2 : p.2.1 = valOf a p.2.2.1 p.2.2.2)
    (hd : Disjoint (p.1.2.1 ∪ p.1.2.2) (p.2.2.1 ∪ p.2.2.2)) :
    (eChild p).1 = valOf a (eChild p).2.1 (eChild p).2.2 := by
  show p.2.1 - p.1.1 = _
  rw [h1, h2]
  exact (valOf_child a hd).symm

/-- Every stage of initialized full-label sieving preserves signed-sum labels, nonempty
supports, disjoint positive and negative ancestors, absence of duplicate records, and
disjoint supports for distinct records. -/
private theorem eRun_inv {n R : ℕ} (a : Fin R → ZMod (2 ^ n)) (m : ℕ) (C : ℕ → Fin 2) :
    ∀ j : ℕ, (∀ e ∈ eRun n m R j (eInit a) C,
        e.1 = valOf a e.2.1 e.2.2 ∧ (e.2.1 ∪ e.2.2).Nonempty ∧ Disjoint e.2.1 e.2.2)
      ∧ (eRun n m R j (eInit a) C).Nodup
      ∧ (∀ e ∈ eRun n m R j (eInit a) C, ∀ e' ∈ eRun n m R j (eInit a) C, e ≠ e' →
          Disjoint (e.2.1 ∪ e.2.2) (e'.2.1 ∪ e'.2.2)) := by
  intro j
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨i, hi⟩ := List.mem_ofFn.1 he
      subst hi
      exact ⟨(valOf_eInit a i).symm, ⟨i, by simp⟩, by simp⟩
    · show (List.ofFn (fun i : Fin R => ((a i, {i}, (∅ : Finset (Fin R))) : ERec n R))).Nodup
      rw [List.nodup_ofFn]
      intro x y h
      have hxy : ({x} : Finset (Fin R)) = {y} := congrArg (fun q : ERec n R => q.2.1) h
      have hmem : x ∈ ({y} : Finset (Fin R)) := by
        have h1 : x ∈ ({x} : Finset (Fin R)) := by simp
        exact ((Finset.ext_iff.1 hxy) x).mp h1
      exact (Finset.mem_singleton.1 hmem)
    · intro e he e' he' hne
      obtain ⟨i, hi⟩ := List.mem_ofFn.1 he
      obtain ⟨i', hi'⟩ := List.mem_ofFn.1 he'
      subst hi; subst hi'
      have hii : i ≠ i' := by
        intro hcon; subst hcon; exact hne rfl
      rw [Finset.union_empty, Finset.union_empty]
      exact Finset.disjoint_singleton.2 hii
  | succ j ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hpairmem : ∀ q ∈ sievePairWith n (fun e : ERec n R => e.1)
        (sieveWindowWidth n m j) (m * j) (eRun n m R j (eInit a) C),
        q.1 ∈ eRun n m R j (eInit a) C ∧ q.2 ∈ eRun n m R j (eInit a) C := by
      intro q hq
      have h := sievePairWith_mem_window q hq
      exact ⟨h.1, h.2.1⟩
    have hd : ∀ q ∈ sievePairWith n (fun e : ERec n R => e.1)
        (sieveWindowWidth n m j) (m * j) (eRun n m R j (eInit a) C), q.1 ≠ q.2 :=
      fun q hq => pair_ne (fun e : ERec n R => e.1) _ ih2 q hq

    have hinj : ∀ q ∈ sievePairWith n (fun e : ERec n R => e.1)
        (sieveWindowWidth n m j) (m * j) (eRun n m R j (eInit a) C),
        ∀ q' ∈ sievePairWith n (fun e : ERec n R => e.1)
        (sieveWindowWidth n m j) (m * j) (eRun n m R j (eInit a) C),
        eChild q = eChild q' → q = q' := by
      intro q hq q' hq' hcc
      by_cases hne : q = q'
      · exact hne
      · exfalso
        obtain ⟨t1, t2, t3, t4⟩ := pair_sep (fun e : ERec n R => e.1) _ ih2 q q' hq hq' hne
        obtain ⟨hq1, hq2⟩ := hpairmem q hq
        obtain ⟨hq1', hq2'⟩ := hpairmem q' hq'
        have hdisj : Disjoint ((q.1.2.1 ∪ q.1.2.2) ∪ (q.2.2.1 ∪ q.2.2.2))
            ((q'.1.2.1 ∪ q'.1.2.2) ∪ (q'.2.2.1 ∪ q'.2.2.2)) := by
          apply Finset.disjoint_union_left.2
          constructor
          · exact Finset.disjoint_union_right.2
              ⟨ih3 _ hq1 _ hq1' t1, ih3 _ hq1 _ hq2' t2⟩
          · exact Finset.disjoint_union_right.2
              ⟨ih3 _ hq2 _ hq1' t3, ih3 _ hq2 _ hq2' t4⟩
        have hUU : ((q.1.2.1 ∪ q.1.2.2) ∪ (q.2.2.1 ∪ q.2.2.2))
            = ((q'.1.2.1 ∪ q'.1.2.2) ∪ (q'.2.2.1 ∪ q'.2.2.2)) := by
          rw [← eChild_supp q, ← eChild_supp q', hcc]
        have hdisj' : Disjoint ((q.1.2.1 ∪ q.1.2.2) ∪ (q.2.2.1 ∪ q.2.2.2))
            ((q.1.2.1 ∪ q.1.2.2) ∪ (q.2.2.1 ∪ q.2.2.2)) := hUU ▸ hdisj
        have hemp : ((q.1.2.1 ∪ q.1.2.2) ∪ (q.2.2.1 ∪ q.2.2.2)) = ∅ :=
          (Finset.disjoint_self_iff_empty _).1 hdisj'
        obtain ⟨i, hi⟩ := (ih1 q.1 hq1).2.1
        have him : i ∈ (∅ : Finset (Fin R)) := by
          rw [← hemp]
          exact Finset.mem_union_left _ hi
        simp at him
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨q, hq, rfl⟩ := layerRunGen_mem eChild _ _ e he
      obtain ⟨hq1, hq2⟩ := hpairmem q hq
      refine ⟨eChild_val a q (ih1 q.1 hq1).1 (ih1 q.2 hq2).1 (ih3 q.1 hq1 q.2 hq2 (hd q hq)),
        ?_, ?_⟩
      · obtain ⟨i, hi⟩ := (ih1 q.1 hq1).2.1
        refine ⟨i, ?_⟩
        rw [eChild_supp]
        exact Finset.mem_union_left _ hi
      · show Disjoint (q.2.2.1 ∪ q.1.2.2) (q.2.2.2 ∪ q.1.2.1)
        apply Finset.disjoint_union_left.2
        constructor
        · exact Finset.disjoint_union_right.2
            ⟨(ih1 q.2 hq2).2.2, Disjoint.mono Finset.subset_union_left Finset.subset_union_left
              (ih3 q.2 hq2 q.1 hq1 (hd q hq).symm)⟩
        · exact Finset.disjoint_union_right.2
            ⟨Disjoint.mono Finset.subset_union_right Finset.subset_union_right
              (ih3 q.1 hq1 q.2 hq2 (hd q hq)), (ih1 q.1 hq1).2.2.symm⟩
    · exact layerRunGen_nodup eChild _ _
        (pair_nodup (fun e : ERec n R => e.1) _ ih2) hinj
    · intro e he e' he' hne
      obtain ⟨q, hq, rfl⟩ := layerRunGen_mem eChild _ _ e he
      obtain ⟨q', hq', rfl⟩ := layerRunGen_mem eChild _ _ e' he'
      have hqq : q ≠ q' := by
        intro hcon
        exact hne (hcon ▸ rfl)
      obtain ⟨t1, t2, t3, t4⟩ := pair_sep (fun e : ERec n R => e.1) _ ih2 q q' hq hq' hqq
      obtain ⟨hq1, hq2⟩ := hpairmem q hq
      obtain ⟨hq1', hq2'⟩ := hpairmem q' hq'
      rw [eChild_supp, eChild_supp]
      apply Finset.disjoint_union_left.2
      constructor
      · exact Finset.disjoint_union_right.2
          ⟨ih3 _ hq1 _ hq1' t1, ih3 _ hq1 _ hq2' t2⟩
      · exact Finset.disjoint_union_right.2
          ⟨ih3 _ hq2 _ hq1' t3, ih3 _ hq2 _ hq2' t4⟩

/-- Forgetting ancestor sets from full-label sieving gives the deterministic label-only sieve
run. -/
private theorem eRun_map (n m R : ℕ) :
    ∀ (j : ℕ) (E : List (ERec n R)) (C : ℕ → Fin 2),
      (eRun n m R j E C).map (fun e => e.1) = detSieveRun n m R j (E.map (fun e => e.1)) C := by
  intro j
  induction j with
  | zero => intro E C; rfl
  | succ j ih =>
    intro E C
    show (layerRunGen eChild
      (sievePairWith n (fun e : ERec n R => e.1) (sieveWindowWidth n m j) (m * j)
        (eRun n m R j E C)) (fun i => C (j * R + i))).map (fun e => e.1) = _
    rw [layerRunGen_map eChild (fun p : ZMod (2 ^ n) × ZMod (2 ^ n) => p.2 - p.1)
      (fun e : ERec n R => e.1) (fun p => rfl)]
    have hpair : (sievePairWith n (fun e : ERec n R => e.1)
        (sieveWindowWidth n m j) (m * j) (eRun n m R j E C)).map
        (fun p => (p.1.1, p.2.1))
      = sievePairWith n id (sieveWindowWidth n m j) (m * j)
          ((eRun n m R j E C).map (fun e => e.1)) := by
      rw [pair_map (fun e : ERec n R => e.1) id (eRun n m R j E C)]
      rfl
    show layerRunGen (fun p : ZMod (2 ^ n) × ZMod (2 ^ n) => p.2 - p.1)
      ((sievePairWith n (fun e : ERec n R => e.1) (sieveWindowWidth n m j) (m * j)
        (eRun n m R j E C)).map (fun p => (p.1.1, p.2.1))) (fun i => C (j * R + i)) = _
    rw [hpair, ih E C]
    rfl

/-- Window agreement for the width capped at `n-1-t` is unchanged by reducing labels with
`lowb`. -/
private theorem windowAgree_low_any {n w t : ℕ} (x y : ZMod (2 ^ n)) :
    windowAgree n (min w (n - 1 - t)) t x y
      ↔ windowAgree (n - 1) (min w (n - 1 - t)) t (lowb x) (lowb y) := by
  by_cases hcase : t + min w (n - 1 - t) ≤ n - 1
  · exact windowAgree_low hcase x y
  · have h0 : min w (n - 1 - t) = 0 := by
      by_contra hne
      apply hcase
      have h1 : 0 < min w (n - 1 - t) := Nat.pos_of_ne_zero hne
      have h2 := min_le_right w (n - 1 - t)
      omega
    rw [h0]
    constructor
    · intro _
      show ((lowb x).val / 2 ^ t) % 2 ^ 0 = ((lowb y).val / 2 ^ t) % 2 ^ 0
      rw [pow_zero, Nat.mod_one, Nat.mod_one]
    · intro _
      show (x.val / 2 ^ t) % 2 ^ 0 = (y.val / 2 ^ t) % 2 ^ 0
      rw [pow_zero, Nat.mod_one, Nat.mod_one]

/-- For `n ≥ 1`, reducing full-label sieve records and retaining their ancestor sets gives the
reduced-label sieve run. -/
private theorem eRun_skel {n : ℕ} (_hn : 1 ≤ n) (m R : ℕ) (a : Fin R → ZMod (2 ^ n))
    (C : ℕ → Fin 2) :
    ∀ j : ℕ, (eRun n m R j (eInit a) C).map (fun e => (lowb e.1, e.2.1, e.2.2))
      = sRun n m R j (sInit (fun i => lowb (a i))) C := by
  intro j
  induction j with
  | zero =>
    show List.map _ (eInit a) = sInit (fun i => lowb (a i))
    show List.map _ (List.ofFn _) = List.ofFn _
    rw [List.map_ofFn]
    refine ofFn_congr ?_
    intro i
    rfl
  | succ j ih =>
    have hchild : ∀ p : ERec n R × ERec n R,
        (fun e : ERec n R => (lowb e.1, e.2.1, e.2.2)) (eChild p)
          = sChild ((fun e : ERec n R => (lowb e.1, e.2.1, e.2.2)) p.1,
              (fun e : ERec n R => (lowb e.1, e.2.1, e.2.2)) p.2) := by
      intro p
      show (lowb (p.2.1 - p.1.1), p.2.2.1 ∪ p.1.2.2, p.2.2.2 ∪ p.1.2.1)
        = (lowb p.2.1 - lowb p.1.1, p.2.2.1 ∪ p.1.2.2, p.2.2.2 ∪ p.1.2.1)
      rw [lowb_sub]
    show (layerRunGen eChild
      (sievePairWith n (fun e : ERec n R => e.1) (sieveWindowWidth n m j) (m * j)
        (eRun n m R j (eInit a) C)) (fun i => C (j * R + i))).map
        (fun e => (lowb e.1, e.2.1, e.2.2)) = _
    rw [layerRunGen_map eChild sChild (fun e : ERec n R => (lowb e.1, e.2.1, e.2.2)) hchild]
    have hpair : (sievePairWith n (fun e : ERec n R => e.1) (sieveWindowWidth n m j) (m * j)
        (eRun n m R j (eInit a) C)).map
        (fun p => ((lowb p.1.1, p.1.2.1, p.1.2.2), (lowb p.2.1, p.2.2.1, p.2.2.2)))
      = sievePairWith (n - 1) (fun s : SRec n R => s.1) (sieveWindowWidth n m j) (m * j)
          ((eRun n m R j (eInit a) C).map (fun e => (lowb e.1, e.2.1, e.2.2))) := by
      rw [pair_map (fun e : ERec n R => (lowb e.1, e.2.1, e.2.2)) (fun s : SRec n R => s.1)
        (eRun n m R j (eInit a) C)]
      show _ = (sievePairWith (n - 1) (fun e : ERec n R => lowb e.1) (sieveWindowWidth n m j)
        (m * j) (eRun n m R j (eInit a) C)).map _
      congr 1
      exact pair_label_congr _ _ (fun x y => windowAgree_low_any x.1 y.1) _
    show layerRunGen sChild ((sievePairWith n (fun e : ERec n R => e.1) (sieveWindowWidth n m j)
        (m * j) (eRun n m R j (eInit a) C)).map
        (fun p => ((lowb p.1.1, p.1.2.1, p.1.2.2), (lowb p.2.1, p.2.2.1, p.2.2.2))))
        (fun i => C (j * R + i)) = _
    rw [hpair, ih]
    rfl

/-- The highest binary digit of a label modulo `2^n`, defined for `n ≥ 1`. -/
private def topBit {n : ℕ} (hn : 1 ≤ n) (x : ZMod (2 ^ n)) : Fin 2 :=
  ⟨(x.val / 2 ^ (n - 1)), by
    have h := ZMod.val_lt x
    have h2 : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← h2pow hn]; omega
    exact Nat.div_lt_of_lt_mul (by omega : x.val < 2 ^ (n - 1) * 2)⟩

/-- The natural value of a label's top bit is its canonical value divided by `2^(n-1)`. -/
private theorem topBit_val {n : ℕ} (hn : 1 ≤ n) (x : ZMod (2 ^ n)) :
    (topBit hn x).val = x.val / 2 ^ (n - 1) := rfl

/-- The top bit of the zero label is zero. -/
private theorem topBit_zero {n : ℕ} (hn : 1 ≤ n) : topBit hn (0 : ZMod (2 ^ n)) = 0 := by
  apply Fin.ext
  show (0 : ZMod (2 ^ n)).val / 2 ^ (n - 1) = (0 : Fin 2).val
  rw [ZMod.val_zero, Nat.zero_div]
  decide

/-- For `n ≥ 1`, a label is reconstructed from its low residue and its top bit. -/
private theorem zmod_eq_low_add_top {n : ℕ} (hn : 1 ≤ n) (x : ZMod (2 ^ n)) :
    x = (((lowb x).val + 2 ^ (n - 1) * (topBit hn x).val : ℕ) : ZMod (2 ^ n)) := by
  apply ZMod.val_injective
  have hblt : (lowb x).val + 2 ^ (n - 1) * (topBit hn x).val < 2 ^ n := by
    have h1 : (lowb x).val < 2 ^ (n - 1) := ZMod.val_lt _
    have h2 : (topBit hn x).val ≤ 1 := by have := (topBit hn x).isLt; omega
    have h3 : 2 ^ (n - 1) * (topBit hn x).val ≤ 2 ^ (n - 1) * 1 := Nat.mul_le_mul_left _ h2
    have h4 : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← h2pow hn]; omega
    have hp : 0 < 2 ^ (n - 1) := by positivity
    omega
  rw [ZMod.val_cast_of_lt hblt, lowb_val, topBit_val, Nat.mod_add_div]

/-- Adding a binary multiple of the half-period label adds that bit to the top bit modulo two. -/
private theorem topBit_add {n : ℕ} (hn : 1 ≤ n) (x : ZMod (2 ^ n)) (d : Fin 2) :
    topBit hn (x + ((2 ^ (n - 1) * (d.val : ℕ) : ℕ) : ZMod (2 ^ n))) = topBit hn x + d := by
  have hv := ZMod.val_lt x
  have h2 : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← h2pow hn]; omega
  have hd2 : d.val ≤ 1 := by have := d.isLt; omega
  have hcast : (((2 ^ (n - 1) * d.val : ℕ)) : ZMod (2 ^ n)).val = 2 ^ (n - 1) * d.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have h5 : 2 ^ (n - 1) * d.val ≤ 2 ^ (n - 1) * 1 := Nat.mul_le_mul_left _ hd2
      have hp : 0 < 2 ^ (n - 1) := by positivity
      omega)]
  have hval : (x + ((2 ^ (n - 1) * d.val : ℕ) : ZMod (2 ^ n))).val
      = (x.val + 2 ^ (n - 1) * d.val) % 2 ^ n := by
    rw [ZMod.val_add, hcast]
  apply Fin.ext
  show (x + ((2 ^ (n - 1) * d.val : ℕ) : ZMod (2 ^ n))).val / 2 ^ (n - 1)
    = (topBit hn x + d).val
  rw [hval]
  have hfin : (topBit hn x + d).val = (x.val / 2 ^ (n - 1) + d.val) % 2 := rfl
  rw [hfin]
  have hp : 0 < 2 ^ (n - 1) := by positivity
  obtain ⟨q, r, hvr, hq1, hr⟩ :
      ∃ q r, x.val = 2 ^ (n - 1) * q + r ∧ q ≤ 1 ∧ r < 2 ^ (n - 1) :=
    ⟨x.val / 2 ^ (n - 1), x.val % 2 ^ (n - 1), (Nat.div_add_mod _ _).symm,
      by
        have h := Nat.div_lt_of_lt_mul (by omega : x.val < 2 ^ (n - 1) * 2)
        omega,
      Nat.mod_lt _ hp⟩
  have hdiv : (2 ^ (n - 1) * q + r) / 2 ^ (n - 1) = q := by
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.add_zero]
  rw [hvr]
  have hsum : 2 ^ (n - 1) * q + r + 2 ^ (n - 1) * d.val
      = 2 ^ (n - 1) * (q + d.val) + r := by ring
  rw [hsum, hdiv]
  by_cases hqd : q + d.val ≤ 1
  · have hlt : 2 ^ (n - 1) * (q + d.val) + r < 2 ^ n := by
      have h5 : 2 ^ (n - 1) * (q + d.val) ≤ 2 ^ (n - 1) * 1 := Nat.mul_le_mul_left _ hqd
      omega
    rw [Nat.mod_eq_of_lt hlt, Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : q + d.val < 2)]
  · have hqd2 : q + d.val = 2 := by omega
    rw [hqd2, ← h2, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : r < 2 ^ (n - 1) * 2),
      Nat.mod_eq_of_lt (by omega : r < 2 ^ (n - 1) * 2),
      Nat.div_eq_of_lt hr, Nat.mod_self]

/-- The natural value of a sum in `Fin 2` is the sum of natural values modulo two. -/
private theorem fin2_sum_val {α : Type} (s : Finset α) (f : α → Fin 2) :
    (∑ i ∈ s, f i).val = (∑ i ∈ s, (f i).val) % 2 := by
  induction s using Finset.induction with
  | empty =>
    show (0 : Fin 2).val = 0 % 2
    decide
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Fin.val_add, ih]
    omega

/-- Every element of `Fin 2` added to itself is zero. -/
private theorem fin2_self_add (x : Fin 2) : x + x = 0 := by
  apply Fin.ext
  show (x.val + x.val) % 2 = 0
  have h : x.val ≤ 1 := by have := x.isLt; omega
  omega

/-- For `n ≥ 1`, a multiple of the half-period label depends only on the multiplier's parity. -/
private theorem half_pow_mul_cast {n : ℕ} (hn : 1 ≤ n) (S : ℕ) :
    ((2 ^ (n - 1) * S : ℕ) : ZMod (2 ^ n)) = ((2 ^ (n - 1) * (S % 2) : ℕ) : ZMod (2 ^ n)) := by
  conv_lhs => rw [show S = S % 2 + 2 * (S / 2) from (Nat.mod_add_div S 2).symm]
  rw [Nat.mul_add, Nat.cast_add]
  show (_ : ZMod (2 ^ n)) + ((2 ^ (n - 1) * (2 * (S / 2)) : ℕ) : ZMod (2 ^ n)) = _
  rw [show 2 ^ (n - 1) * (2 * (S / 2)) = 2 ^ n * (S / 2) from by
    rw [← h2pow hn]; ring]
  have hkill : ((2 ^ n * (S / 2) : ℕ) : ZMod (2 ^ n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
  rw [hkill, add_zero]

/-- For `n ≥ 1`, separating low residues and top-bit contributions in a signed ancestor sum
gives the stated equality of labels. -/
private theorem valOf_tab_split {n R : ℕ} (hn : 1 ≤ n) (a : Fin R → ZMod (2 ^ n))
    (P N : Finset (Fin R)) :
    valOf a P N + ((2 ^ (n - 1) * (∑ i ∈ N, (topBit hn (a i)).val) : ℕ) : ZMod (2 ^ n))
      = valOf (fun i => ((lowb (a i)).val : ZMod (2 ^ n))) P N
        + ((2 ^ (n - 1) * (∑ i ∈ P, (topBit hn (a i)).val) : ℕ) : ZMod (2 ^ n)) := by
  have hsplit : ∀ i : Fin R,
      a i = ((lowb (a i)).val : ZMod (2 ^ n))
        + ((2 ^ (n - 1) * (topBit hn (a i)).val : ℕ) : ZMod (2 ^ n)) := by
    intro i
    conv_lhs => rw [zmod_eq_low_add_top hn (a i)]
    rw [Nat.cast_add]
  have hsum : ∀ s : Finset (Fin R), (∑ i ∈ s, a i)
      = (∑ i ∈ s, ((lowb (a i)).val : ZMod (2 ^ n)))
        + ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) * (∑ i ∈ s, ((topBit hn (a i)).val : ZMod (2 ^ n))) := by
    intro s
    rw [show (∑ i ∈ s, a i) = ∑ i ∈ s, (((lowb (a i)).val : ZMod (2 ^ n))
        + ((2 ^ (n - 1) * (topBit hn (a i)).val : ℕ) : ZMod (2 ^ n))) from
      Finset.sum_congr rfl fun i _ => hsplit i]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_mul]
  have e1 : ((2 ^ (n - 1) * (∑ i ∈ N, (topBit hn (a i)).val) : ℕ) : ZMod (2 ^ n))
      = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))
        * (∑ i ∈ N, ((topBit hn (a i)).val : ZMod (2 ^ n))) := by
    rw [Nat.cast_mul, Nat.cast_sum]
  have e2 : ((2 ^ (n - 1) * (∑ i ∈ P, (topBit hn (a i)).val) : ℕ) : ZMod (2 ^ n))
      = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))
        * (∑ i ∈ P, ((topBit hn (a i)).val : ZMod (2 ^ n))) := by
    rw [Nat.cast_mul, Nat.cast_sum]
  rw [valOf, valOf, hsum P, hsum N, e1, e2]
  ring

/-- The top bit of a signed ancestor sum is the top bit of its low-residue sum plus all positive
and negative ancestor top bits modulo two. -/
private theorem topBit_valOf {n R : ℕ} (hn : 1 ≤ n) (a : Fin R → ZMod (2 ^ n))
    (P N : Finset (Fin R)) :
    topBit hn (valOf a P N)
      = topBit hn (valOf (fun i => ((lowb (a i)).val : ZMod (2 ^ n))) P N)
        + ((∑ i ∈ P, topBit hn (a i)) + (∑ i ∈ N, topBit hn (a i))) := by
  have key := valOf_tab_split hn a P N
  have e1 := topBit_add hn (valOf a P N) (∑ i ∈ N, topBit hn (a i))
  have e2 := topBit_add hn (valOf (fun i => ((lowb (a i)).val : ZMod (2 ^ n))) P N)
    (∑ i ∈ P, topBit hn (a i))
  have hNv : (∑ i ∈ N, topBit hn (a i)).val = (∑ i ∈ N, (topBit hn (a i)).val) % 2 :=
    fin2_sum_val N (fun i => topBit hn (a i))
  have hPv : (∑ i ∈ P, topBit hn (a i)).val = (∑ i ∈ P, (topBit hn (a i)).val) % 2 :=
    fin2_sum_val P (fun i => topBit hn (a i))
  rw [hNv] at e1
  rw [hPv] at e2
  rw [← half_pow_mul_cast hn (∑ i ∈ N, (topBit hn (a i)).val)] at e1
  rw [← half_pow_mul_cast hn (∑ i ∈ P, (topBit hn (a i)).val)] at e2
  rw [key] at e1
  rw [e2] at e1
  calc topBit hn (valOf a P N)
      = topBit hn (valOf a P N)
          + ((∑ i ∈ N, topBit hn (a i)) + (∑ i ∈ N, topBit hn (a i))) := by
        rw [fin2_self_add, add_zero]
    _ = (topBit hn (valOf a P N) + (∑ i ∈ N, topBit hn (a i)))
          + (∑ i ∈ N, topBit hn (a i)) := by
        rw [add_assoc]
    _ = (topBit hn (valOf (fun i => ((lowb (a i)).val : ZMod (2 ^ n))) P N)
          + (∑ i ∈ P, topBit hn (a i))) + (∑ i ∈ N, topBit hn (a i)) := by
        rw [← e1]
    _ = topBit hn (valOf (fun i => ((lowb (a i)).val : ZMod (2 ^ n))) P N)
          + ((∑ i ∈ P, topBit hn (a i)) + (∑ i ∈ N, topBit hn (a i))) := by
        rw [add_assoc]

/-- The initialized deterministic sieve equals initialized full-label sieving with ancestor sets
forgotten. -/
private theorem detSieveRun_eq_eRun_map {n m R : ℕ}
    (a : Fin R → ZMod (2 ^ n)) (c : Fin (m * R) → Fin 2) :
    detSieveRun n m R m (List.ofFn a) (coinLift c)
      = (eRun n m R m (eInit a) (coinLift c)).map (fun e => e.1) := by
  rw [eRun_map n m R m (eInit a) (coinLift c)]
  show detSieveRun n m R m (List.ofFn a) (coinLift c)
    = detSieveRun n m R m ((eInit a).map (fun e => e.1)) (coinLift c)
  rw [show (eInit a).map (fun e : ERec n R => e.1) = List.ofFn a from by
    rw [eInit, List.map_ofFn]
    rfl]

/-- The union of positive and negative ancestors of the specified final reduced-label record,
using empty sets for a missing record. -/
private def ancIdx {n m R : ℕ} (a : Fin R → ZMod (2 ^ n)) (c : Fin (m * R) → Fin 2)
    (j : Fin (2 ^ m)) : Finset (Fin R) :=
  (((sRun n m R m (sInit (fun i' => lowb (a i'))) (coinLift c)).getD ↑j
      ((0, ∅, ∅) : SRec n R)).2.1
    ∪ ((sRun n m R m (sInit (fun i' => lowb (a i'))) (coinLift c)).getD ↑j
      ((0, ∅, ∅) : SRec n R)).2.2)

/-- The binary indicator for the least ancestor of a final reduced record selected by the target
bit table `u`. -/
private def flipTop {n m R : ℕ} (a : Fin R → ZMod (2 ^ n)) (c : Fin (m * R) → Fin 2)
    (u : Fin (2 ^ m) → Fin 2) (i : Fin R) : Fin 2 :=
  if (∃ j : Fin (2 ^ m), u j = 1 ∧ i ∈ ancIdx a c j ∧ ∀ i' ∈ ancIdx a c j, i ≤ i')
  then 1 else 0

/-- The label table obtained by adding the half-period label at positions marked by `flipTop`. -/
private def flipTable {n m R : ℕ} (_hn : 1 ≤ n) (a : Fin R → ZMod (2 ^ n))
    (c : Fin (m * R) → Fin 2) (u : Fin (2 ^ m) → Fin 2) : Fin R → ZMod (2 ^ n) :=
  fun i => a i + ((2 ^ (n - 1) * ((flipTop a c u i).val : ℕ) : ℕ) : ZMod (2 ^ n))

/-- For `n ≥ 1`, reducing a binary multiple of the half-period label with `lowb` gives zero. -/
private theorem lowb_shift {n : ℕ} (hn : 1 ≤ n) (v : ℕ) (hv : v ≤ 1) :
    lowb (((2 ^ (n - 1) * v : ℕ)) : ZMod (2 ^ n)) = 0 := by
  apply ZMod.val_injective
  have hcast : (((2 ^ (n - 1) * v : ℕ)) : ZMod (2 ^ n)).val = 2 ^ (n - 1) * v := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have h5 : 2 ^ (n - 1) * v ≤ 2 ^ (n - 1) * 1 := Nat.mul_le_mul_left _ hv
      have h2 : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← h2pow hn]; omega
      have hp : 0 < 2 ^ (n - 1) := by positivity
      omega)]
  rw [lowb_val, hcast, Nat.mul_mod_right, ZMod.val_zero]

/-- For `n ≥ 1`, twice any multiple of the half-period label is zero modulo `2^n`. -/
private theorem shift_self_add {n : ℕ} (hn : 1 ≤ n) (v : ℕ) :
    ((2 ^ (n - 1) * v : ℕ) : ZMod (2 ^ n)) + ((2 ^ (n - 1) * v : ℕ) : ZMod (2 ^ n)) = 0 := by
  rw [← Nat.cast_add]
  show ((2 ^ (n - 1) * v + 2 ^ (n - 1) * v : ℕ) : ZMod (2 ^ n)) = 0
  rw [show 2 ^ (n - 1) * v + 2 ^ (n - 1) * v = 2 ^ n * v from by rw [← h2pow hn]; ring]
  rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- Four binary summands can be regrouped by exchanging the two middle summands. -/
private theorem fin2_rearr (x y z w : Fin 2) : (x + y) + (z + w) = x + z + (y + w) := by
  apply Fin.ext
  simp only [Fin.val_add]
  have hx : x.val ≤ 1 := by have := x.isLt; omega
  have hy : y.val ≤ 1 := by have := y.isLt; omega
  have hz : z.val ≤ 1 := by have := z.isLt; omega
  have hw : w.val ≤ 1 := by have := w.isLt; omega
  omega

/-- If a deterministic run retains at least `2^m` labels and all are zero, the prescribed table
flips preserve low residues and that length bound while setting the first `2^m` output top
bits to `u`. -/
private theorem flip_bundle {n m R : ℕ} (hn : 1 ≤ n) (_hR : 0 < R)
    (a : Fin R → ZMod (2 ^ n)) (c : Fin (m * R) → Fin 2)
    (hlen : (2 ^ m : ℕ) ≤ (detSieveRun n m R m (List.ofFn a) (coinLift c)).length)
    (hzero : ∀ k ∈ detSieveRun n m R m (List.ofFn a) (coinLift c), k = 0)
    (u : Fin (2 ^ m) → Fin 2) :
    (∀ i, lowb (flipTable hn a c u i) = lowb (a i))
    ∧ (2 ^ m : ℕ) ≤ (detSieveRun n m R m (List.ofFn (flipTable hn a c u)) (coinLift c)).length
    ∧ (∀ j : Fin (2 ^ m),
        topBit hn (((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).map (fun e => e.1)).getD
          ↑j (0 : ZMod (2 ^ n))) = u j) := by
  set E := eRun n m R m (eInit a) (coinLift c) with hEdef
  have hrun : detSieveRun n m R m (List.ofFn a) (coinLift c) = E.map (fun e => e.1) :=
    detSieveRun_eq_eRun_map a c
  obtain ⟨hInv1, hInv2, hInv3⟩ := eRun_inv a m (coinLift c) m
  have hEl : E.length = (detSieveRun n m R m (List.ofFn a) (coinLift c)).length := by
    rw [hrun, List.length_map]
  have hj : ∀ j : Fin (2 ^ m), (j : ℕ) < E.length := fun j => by
    have h1 : (j : ℕ) < 2 ^ m := j.2
    have h2 : (2 ^ m : ℕ) ≤ E.length := by rw [hEl]; exact hlen
    omega
  have hskel : E.map (fun e => (lowb e.1, e.2.1, e.2.2))
      = sRun n m R m (sInit (fun i => lowb (a i))) (coinLift c) :=
    eRun_skel hn m R a (coinLift c) m
  have hElS : E.length = (sRun n m R m (sInit (fun i => lowb (a i))) (coinLift c)).length := by
    rw [← hskel, List.length_map]
  have hanc : ∀ j : Fin (2 ^ m),
      ancIdx a c j = (E[↑j]'(hj j)).2.1 ∪ (E[↑j]'(hj j)).2.2 := by
    intro j
    show (((sRun n m R m (sInit (fun i' => lowb (a i'))) (coinLift c)).getD ↑j
        ((0, ∅, ∅) : SRec n R)).2.1
      ∪ ((sRun n m R m (sInit (fun i' => lowb (a i'))) (coinLift c)).getD ↑j
        ((0, ∅, ∅) : SRec n R)).2.2) = _
    rw [← hskel, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj j),
      List.getElem_map]
    rfl
  have hne_rec : ∀ {j j' : Fin (2 ^ m)}, j' ≠ j →
      E[↑j']'(hj j') ≠ E[↑j]'(hj j) := by
    intro j j' hne hcon
    have hv := congrArg Fin.val ((hInv2.get_inj_iff).1 hcon)
    exact hne (Fin.ext (show (j' : ℕ) = (j : ℕ) from hv))
  have hlow1 : ∀ i, lowb (flipTable hn a c u i) = lowb (a i) := by
    intro i
    show lowb (a i + ((2 ^ (n - 1) * ((flipTop a c u i).val : ℕ) : ℕ) : ZMod (2 ^ n))) = _
    rw [lowb_add, lowb_shift hn _ (by have := (flipTop a c u i).isLt; omega), add_zero]
  refine ⟨hlow1, ?_, ?_⟩
  · have hrun' : detSieveRun n m R m (List.ofFn (flipTable hn a c u)) (coinLift c)
        = (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).map (fun e => e.1) :=
      detSieveRun_eq_eRun_map (flipTable hn a c u) c
    have hskel' : (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).map
        (fun e => (lowb e.1, e.2.1, e.2.2))
        = sRun n m R m (sInit (fun i => lowb (flipTable hn a c u i))) (coinLift c) :=
      eRun_skel hn m R (flipTable hn a c u) (coinLift c) m
    have hlow : (fun i => lowb (flipTable hn a c u i)) = (fun i => lowb (a i)) :=
      funext hlow1
    have hE'l : (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).length = E.length := by
      have h1 : (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).length
          = (sRun n m R m (sInit (fun i => lowb (flipTable hn a c u i))) (coinLift c)).length := by
        rw [← hskel', List.length_map]
      rw [h1, hlow, ← hElS]
    rw [hrun', List.length_map, hE'l, hEl]
    exact hlen
  · intro j
    obtain ⟨hInv1', hInv2', hInv3'⟩ := eRun_inv (flipTable hn a c u) m (coinLift c) m
    have hskel' : (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).map
        (fun e => (lowb e.1, e.2.1, e.2.2))
        = sRun n m R m (sInit (fun i => lowb (flipTable hn a c u i))) (coinLift c) :=
      eRun_skel hn m R (flipTable hn a c u) (coinLift c) m
    have hlow : (fun i => lowb (flipTable hn a c u i)) = (fun i => lowb (a i)) :=
      funext hlow1
    have hE'l : (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).length = E.length := by
      have h1 : (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).length
          = (sRun n m R m (sInit (fun i => lowb (flipTable hn a c u i))) (coinLift c)).length := by
        rw [← hskel', List.length_map]
      rw [h1, hlow, ← hElS]
    have hj' : (j : ℕ) < (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).length := by
      rw [hE'l]; exact hj j
    have hsupp : ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).2
        = (E[↑j]'(hj j)).2 := by
      have e1 : (((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).map
          (fun e => (lowb e.1, e.2.1, e.2.2))).getD ↑j ((0, ∅, ∅) : SRec n R))
          = (lowb ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).1,
            ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).2.1,
            ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).2.2) := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map]
        rfl
      have e2 : ((E.map (fun e => (lowb e.1, e.2.1, e.2.2))).getD ↑j ((0, ∅, ∅) : SRec n R))
          = (lowb (E[↑j]'(hj j)).1, (E[↑j]'(hj j)).2.1, (E[↑j]'(hj j)).2.2) := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj j), List.getElem_map]
        rfl
      have e3 : (((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).map
          (fun e => (lowb e.1, e.2.1, e.2.2))).getD ↑j ((0, ∅, ∅) : SRec n R))
          = ((E.map (fun e => (lowb e.1, e.2.1, e.2.2))).getD ↑j ((0, ∅, ∅) : SRec n R)) := by
        rw [hskel', hlow, ← hskel]
      rw [e1, e2] at e3
      have h4 := congrArg Prod.snd e3
      exact h4
    have hlabel : (((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c)).map (fun e => e.1)).getD
        ↑j (0 : ZMod (2 ^ n)))
        = ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).1 := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map]
      rfl
    rw [hlabel]
    have hmem' : (eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')
        ∈ eRun n m R m (eInit (flipTable hn a c u)) (coinLift c) := List.getElem_mem hj'
    obtain ⟨hv', hne', hd'⟩ := hInv1' _ hmem'
    have hmem : E[↑j]'(hj j) ∈ E := List.getElem_mem (hj j)
    obtain ⟨hv, hne, hd⟩ := hInv1 _ hmem
    rw [hv']
    have htb : ∀ i, topBit hn (flipTable hn a c u i) = topBit hn (a i) + flipTop a c u i :=
      fun i => topBit_add hn (a i) (flipTop a c u i)
    have hcount : (∑ i ∈ (E[↑j]'(hj j)).2.1, flipTop a c u i)
        + (∑ i ∈ (E[↑j]'(hj j)).2.2, flipTop a c u i) = u j := by
      have hne₀ : ((E[↑j]'(hj j)).2.1 ∪ (E[↑j]'(hj j)).2.2).Nonempty := hne
      have hfilt : ((E[↑j]'(hj j)).2.1 ∪ (E[↑j]'(hj j)).2.2).filter (fun i =>
          ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j' ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')
          = if u j = 1 then {((E[↑j]'(hj j)).2.1 ∪ (E[↑j]'(hj j)).2.2).min' hne₀} else ∅ := by
        by_cases hu : u j = 1
        · rw [if_pos hu]
          ext i
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hiS, j', huj', hiA, hleast⟩
            have hij : i ∈ (E[↑j']'(hj j')).2.1 ∪ (E[↑j']'(hj j')).2.2 := (hanc j') ▸ hiA
            have hjj : j' = j := by
              by_contra hnec
              have hdij := hInv3 _ (List.getElem_mem (hj j')) _ (List.getElem_mem (hj j))
                (hne_rec hnec)
              exact (Finset.disjoint_left.1 hdij) hij hiS
            rw [hjj] at hleast
            apply le_antisymm
            · exact hleast _ ((hanc j).symm ▸ Finset.min'_mem _ _)
            · exact Finset.min'_le _ _ hiS
          · intro hi
            subst hi
            exact ⟨Finset.min'_mem _ _, ⟨j, hu, (hanc j).symm ▸ Finset.min'_mem _ _,
              fun i' hi' => Finset.min'_le _ _ ((hanc j) ▸ hi')⟩⟩
        · rw [if_neg hu, Finset.filter_eq_empty_iff]
          intro i hiS hD
          obtain ⟨j', huj', hiA, hleast⟩ := hD
          have hij : i ∈ (E[↑j']'(hj j')).2.1 ∪ (E[↑j']'(hj j')).2.2 := (hanc j') ▸ hiA
          have hjj : j' = j := by
            by_contra hnec
            have hdij := hInv3 _ (List.getElem_mem (hj j')) _ (List.getElem_mem (hj j))
              (hne_rec hnec)
            exact (Finset.disjoint_left.1 hdij) hij hiS
          rw [hjj] at huj'
          exact hu huj'
      have hcard : (((E[↑j]'(hj j)).2.1 ∪ (E[↑j]'(hj j)).2.2).filter (fun i =>
          ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j' ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')
          ).card = (u j).val := by
        rw [hfilt]
        by_cases hu : u j = 1
        · rw [if_pos hu, Finset.card_singleton, hu]
          decide
        · rw [if_neg hu, Finset.card_empty]
          have h0 : u j = 0 := by
            rcases (by omega : u j = 0 ∨ u j = 1) with h | h
            · exact h
            · exact absurd h hu
          rw [h0]
          decide
      have hval : ∀ i, (flipTop a c u i).val
          = (if (∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j'
              ∧ ∀ i' ∈ ancIdx a c j', i ≤ i') then 1 else 0 : ℕ) := by
        intro i
        show (if (∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j'
            ∧ ∀ i' ∈ ancIdx a c j', i ≤ i') then (1 : Fin 2) else (0 : Fin 2)).val = _
        by_cases h : (∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j'
            ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')
        · rw [if_pos h, if_pos h]
          decide
        · rw [if_neg h, if_neg h]
          decide
      have hsumv : ∀ s : Finset (Fin R), (∑ i ∈ s, (flipTop a c u i).val)
          = (s.filter (fun i => ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j'
              ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')).card := by
        intro s
        rw [Finset.sum_congr rfl fun i _ => hval i, Finset.sum_boole, Nat.cast_id]
      have hdisj : Disjoint (((E[↑j]'(hj j)).2.1).filter (fun i =>
          ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j' ∧ ∀ i' ∈ ancIdx a c j', i ≤ i'))
          (((E[↑j]'(hj j)).2.2).filter (fun i =>
          ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j' ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')) :=
        Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd
      have hcardunion : (((E[↑j]'(hj j)).2.1 ∪ (E[↑j]'(hj j)).2.2).filter (fun i =>
          ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j' ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')
          ).card
          = (((E[↑j]'(hj j)).2.1).filter (fun i => ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j'
              ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')).card
            + (((E[↑j]'(hj j)).2.2).filter (fun i => ∃ j' : Fin (2 ^ m), u j' = 1 ∧ i ∈ ancIdx a c j'
              ∧ ∀ i' ∈ ancIdx a c j', i ≤ i')).card := by
        rw [Finset.filter_union, Finset.card_union_of_disjoint hdisj]
      apply Fin.ext
      show ((∑ i ∈ (E[↑j]'(hj j)).2.1, flipTop a c u i)
          + (∑ i ∈ (E[↑j]'(hj j)).2.2, flipTop a c u i)).val = (u j).val
      rw [Fin.val_add, fin2_sum_val, fin2_sum_val, hsumv, hsumv]
      have huj := hcard
      rw [hcardunion] at huj
      have hle : (u j).val ≤ 1 := by have := (u j).isLt; omega
      omega
    have hcarry : topBit hn (valOf (flipTable hn a c u)
        ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).2.1
        ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).2.2)
        = topBit hn (valOf a (E[↑j]'(hj j)).2.1 (E[↑j]'(hj j)).2.2) + u j := by
      have h1 := topBit_valOf hn (flipTable hn a c u)
        ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).2.1
        ((eRun n m R m (eInit (flipTable hn a c u)) (coinLift c))[↑j]'(hj')).2.2
      rw [h1]
      rw [hsupp]
      rw [show (fun i => ((lowb (flipTable hn a c u i)).val : ZMod (2 ^ n)))
          = (fun i => ((lowb (a i)).val : ZMod (2 ^ n))) from funext fun i => by
        rw [hlow1 i]]
      simp only [htb]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, fin2_rearr, hcount]
      have h2 := topBit_valOf hn a ((E[↑j]'(hj j)).2.1) ((E[↑j]'(hj j)).2.2)
      rw [h2]
      exact (add_assoc _ _ _).symm
    rw [hcarry]
    have hzeroj : (E[↑j]'(hj j)).1 = 0 := by
      have hmemrun : (E[↑j]'(hj j)).1 ∈ detSieveRun n m R m (List.ofFn a) (coinLift c) := by
        rw [hrun]
        exact List.mem_map.2 ⟨_, List.getElem_mem _, rfl⟩
      exact hzero _ hmemrun
    rw [← hv, hzeroj, topBit_zero, zero_add]

/-- Tables with identical low residues produce identical flip indicators for the same tape and
target bits. -/
private theorem flipTop_congr {n m R : ℕ} (a1 a2 : Fin R → ZMod (2 ^ n))
    (c : Fin (m * R) → Fin 2) (u : Fin (2 ^ m) → Fin 2)
    (h : ∀ i, lowb (a1 i) = lowb (a2 i)) (i : Fin R) :
    flipTop a1 c u i = flipTop a2 c u i := by
  have hfun : (fun i' => lowb (a1 i')) = (fun i' => lowb (a2 i')) := funext h
  unfold flipTop ancIdx
  rw [hfun]

/-- The table flips preserve every entry's low residue. -/
private theorem lowb_flipTable {n m R : ℕ} (hn : 1 ≤ n) (a : Fin R → ZMod (2 ^ n))
    (c : Fin (m * R) → Fin 2) (u : Fin (2 ^ m) → Fin 2) (i : Fin R) :
    lowb (flipTable hn a c u i) = lowb (a i) := by
  rw [flipTable, lowb_add, lowb_shift hn _ (by
    have := (flipTop a c u i).isLt
    omega), add_zero]

/-- Applying the same table flip twice restores the original label table. -/
private theorem flipTable_invol {n m R : ℕ} (hn : 1 ≤ n) (a : Fin R → ZMod (2 ^ n))
    (c : Fin (m * R) → Fin 2) (u : Fin (2 ^ m) → Fin 2) :
    flipTable hn (flipTable hn a c u) c u = a := by
  funext i
  have hcon : flipTop (flipTable hn a c u) c u i = flipTop a c u i :=
    flipTop_congr _ _ _ _ (fun i' => lowb_flipTable hn a c u i') i
  rw [flipTable, flipTable, hcon, add_assoc, shift_self_add hn _, add_zero]

/-- The probability of an event under a uniform finite distribution is its cardinality divided
by the type's cardinality. -/
private theorem htop_uniform_event {D : Type} [Fintype D] [Nonempty D] (Q : D → Prop)
    [DecidablePred Q] :
    (∑' x : D, if Q x then (PMF.uniformOfFintype' D) x else 0)
      = ((Finset.univ.filter Q).card : ENNReal) * (Fintype.card D : ENNReal)⁻¹ := by
  classical
  simp only [PMF.uniformOfFintype'_apply, tsum_fintype]
  rw [← Finset.sum_filter]
  simp [Finset.sum_const]

/-- For `n ≥ 1` and `R > 0`, the number of inputs with at least `2^m` all-zero outputs,
multiplied by `2^(2^m)`, is at most the number with at least `2^m` outputs. -/
private theorem htop_card_bound {n m R : ℕ} (hn : 1 ≤ n) (hR : 0 < R) :
    (Finset.univ.filter (fun p : (Fin R → ZMod (2 ^ n)) × (Fin (m * R) → Fin 2) =>
        (2 ^ m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length ∧
        ∀ k ∈ detSieveRun n m R m (List.ofFn p.1) (coinLift p.2), k = 0)).card *
      (2 ^ (2 ^ m : ℕ) : ℕ) ≤
    (Finset.univ.filter (fun p : (Fin R → ZMod (2 ^ n)) × (Fin (m * R) → Fin 2) =>
        (2 ^ m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length)).card := by
  classical
  set Qz : ((Fin R → ZMod (2 ^ n)) × (Fin (m * R) → Fin 2)) → Prop := fun p =>
    (2 ^ m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length ∧
    ∀ k ∈ detSieveRun n m R m (List.ofFn p.1) (coinLift p.2), k = 0 with hQzdef
  set Qg : ((Fin R → ZMod (2 ^ n)) × (Fin (m * R) → Fin 2)) → Prop := fun p =>
    (2 ^ m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length with hQgdef
  have hcardU : Fintype.card (Fin (2 ^ m) → Fin 2) = (2 ^ (2 ^ m : ℕ) : ℕ) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hZc : Fintype.card {p // Qz p} = (Finset.univ.filter Qz).card :=
    Fintype.subtype_card (Finset.univ.filter Qz) (fun x => by simp [Finset.mem_filter])
  have hGc : Fintype.card {p // Qg p} = (Finset.univ.filter Qg).card :=
    Fintype.subtype_card (Finset.univ.filter Qg) (fun x => by simp [Finset.mem_filter])
  have hle : Fintype.card ({p // Qz p} × (Fin (2 ^ m) → Fin 2)) ≤ Fintype.card {p // Qg p} :=
    Fintype.card_le_of_injective
      (fun xz : {p // Qz p} × (Fin (2 ^ m) → Fin 2) =>
        ⟨(flipTable hn xz.1.1.1 xz.1.1.2 xz.2, xz.1.1.2),
          (flip_bundle hn hR xz.1.1.1 xz.1.1.2 xz.1.2.1 xz.1.2.2 xz.2).2.1⟩) (by
      intro xz yz hxy
      have hval : (flipTable hn xz.1.1.1 xz.1.1.2 xz.2, xz.1.1.2)
          = (flipTable hn yz.1.1.1 yz.1.1.2 yz.2, yz.1.1.2) :=
        congrArg Subtype.val hxy
      injection hval with htab hc
      have hbx := flip_bundle hn hR xz.1.1.1 xz.1.1.2 xz.1.2.1 xz.1.2.2 xz.2
      have hby := flip_bundle hn hR yz.1.1.1 yz.1.1.2 yz.1.2.1 yz.1.2.2 yz.2
      have hu : xz.2 = yz.2 := by
        funext j
        have h1 := hbx.2.2 j
        have h2 := hby.2.2 j
        rw [htab, hc] at h1
        exact h1.symm.trans h2
      have ha : xz.1.1.1 = yz.1.1.1 := by
        have h1 := flipTable_invol hn xz.1.1.1 xz.1.1.2 xz.2
        have h2 := flipTable_invol hn yz.1.1.1 yz.1.1.2 yz.2
        rw [htab, hc, hu] at h1
        exact h1.symm.trans h2
      exact Prod.ext (Subtype.ext (Prod.ext ha hc)) hu)
  calc (Finset.univ.filter Qz).card * (2 ^ (2 ^ m : ℕ) : ℕ)
      = Fintype.card ({p // Qz p} × (Fin (2 ^ m) → Fin 2)) := by
        rw [Fintype.card_prod, hZc, hcardU]
    _ ≤ Fintype.card {p // Qg p} := hle
    _ = (Finset.univ.filter Qg).card := hGc

/-- For `n ≥ 1` and `R > 0`, the probability of retaining at least `2^m` all-zero labels is at
most `2^(-2^m)` times the probability of retaining at least `2^m` labels. -/
private theorem htop_cond {n m R : ℕ} (hn : 1 ≤ n) (hR : 0 < R) :
    (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
          then ((idealFreshRecords n R).bind (idealSieveRec n m m)) L else 0)
      ≤ (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length
          then ((idealFreshRecords n R).bind (idealSieveRec n m m)) L else 0)
        * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := by
  classical
  have hKne : ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal) ≠ 0 := by positivity
  have hKtop : ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have key : ∀ cz cg : ℕ, cz * (2 ^ (2 ^ m : ℕ) : ℕ) ≤ cg →
      (cz : ENNReal) * (Fintype.card ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)) : ENNReal)⁻¹
        ≤ (cg : ENNReal)
          * (Fintype.card ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)) : ENNReal)⁻¹
          * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := by
    intro cz cg hle
    have h1 : ((cz * (2 ^ (2 ^ m : ℕ) : ℕ) : ℕ) : ENNReal) ≤ (cg : ENNReal) := by
      exact_mod_cast hle
    rw [Nat.cast_mul] at h1
    have h2 : (cz : ENNReal) ≤ (cg : ENNReal) * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := by
      calc (cz : ENNReal) = (cz : ENNReal) * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)
            * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := by
              rw [mul_assoc, ENNReal.mul_inv_cancel hKne hKtop, mul_one]
        _ ≤ (cg : ENNReal) * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := mul_le_mul_left h1 _
    calc (cz : ENNReal)
        * (Fintype.card ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)) : ENNReal)⁻¹
        ≤ ((cg : ENNReal) * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹)
          * (Fintype.card ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)) : ENNReal)⁻¹ :=
          mul_le_mul_left h2 _
      _ = (cg : ENNReal)
          * (Fintype.card ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)) : ENNReal)⁻¹
          * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := by ring
  have hZu := htop_uniform_event (fun p : (Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2) =>
    (2^m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length ∧
    ∀ k ∈ detSieveRun n m R m (List.ofFn p.1) (coinLift p.2), k = 0)
  have hEu := htop_uniform_event (fun p : (Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2) =>
    (2^m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length)
  have hZev := pmf_map_event (PMF.uniformOfFintype' ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)))
    (fun p => detSieveRun n m R m (List.ofFn p.1) (coinLift p.2))
    (fun L => (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0)
  have hEev := pmf_map_event (PMF.uniformOfFintype' ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)))
    (fun p => detSieveRun n m R m (List.ofFn p.1) (coinLift p.2))
    (fun L => (2^m : ℕ) ≤ L.length)
  calc (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
          then ((idealFreshRecords n R).bind (idealSieveRec n m m)) L else 0)
      = (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
          then ((PMF.uniformOfFintype' ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2))).map
            (fun p => detSieveRun n m R m (List.ofFn p.1) (coinLift p.2))) L else 0) := by
        rw [← mu_factorized n m R hR]
    _ = (∑' p : (Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2),
        if (2^m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length ∧
            ∀ k ∈ detSieveRun n m R m (List.ofFn p.1) (coinLift p.2), k = 0
          then (PMF.uniformOfFintype' ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2))) p else 0) :=
        hZev
    _ = ((Finset.univ.filter (fun p : (Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2) =>
          (2^m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length ∧
          ∀ k ∈ detSieveRun n m R m (List.ofFn p.1) (coinLift p.2), k = 0)).card : ENNReal)
        * (Fintype.card ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)) : ENNReal)⁻¹ := hZu
    _ ≤ ((Finset.univ.filter (fun p : (Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2) =>
          (2^m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length)).card : ENNReal)
        * (Fintype.card ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2)) : ENNReal)⁻¹
        * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := key _ _ (htop_card_bound hn hR)
    _ = (∑' p : (Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2),
        if (2^m : ℕ) ≤ (detSieveRun n m R m (List.ofFn p.1) (coinLift p.2)).length
          then (PMF.uniformOfFintype' ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2))) p else 0)
        * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ :=
        congrArg (fun x => x * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹) hEu.symm
    _ = (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length
          then ((PMF.uniformOfFintype' ((Fin R → ZMod (2^n)) × (Fin (m * R) → Fin 2))).map
            (fun p => detSieveRun n m R m (List.ofFn p.1) (coinLift p.2))) L else 0)
        * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ :=
        congrArg (fun x => x * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹) hEev.symm
    _ = (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length
          then ((idealFreshRecords n R).bind (idealSieveRec n m m)) L else 0)
        * ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹ := by rw [mu_factorized n m R hR]

/-- The probability of any event in a probability mass function is at most one. -/
private theorem pmf_event_le_one {α : Type} (μ : PMF α) (Q : α → Prop) [DecidablePred Q] :
    (∑' a, if Q a then μ a else 0) ≤ 1 := by
  calc (∑' a, if Q a then μ a else 0) ≤ ∑' a, μ a :=
        ENNReal.tsum_le_tsum fun a => by
          by_cases h : Q a <;> simp [h]
    _ = 1 := PMF.tsum_coe μ

/-- For finite event masses with `a ≤ b+c` and `c ≤ a*e`, where `e ∈ [0,1]`, the mass `b` is at
least `a*(1-e)`. -/
private theorem htop_finish {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {a b c : ENNReal}
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hE : a ≤ b + c) (hZ : c ≤ a * ENNReal.ofReal e) :
    a * ENNReal.ofReal (1 - e) ≤ b := by
  have haT : a ≠ ⊤ := (lt_of_le_of_lt ha ENNReal.one_lt_top).ne
  have hbT : b ≠ ⊤ := (lt_of_le_of_lt hb ENNReal.one_lt_top).ne
  have hcT : c ≠ ⊤ := (lt_of_le_of_lt hc ENNReal.one_lt_top).ne
  have hoe : ENNReal.ofReal e ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1e : ENNReal.ofReal (1 - e) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hE' : a.toReal ≤ b.toReal + c.toReal := by
    have h1 := (ENNReal.toReal_le_toReal haT (ENNReal.add_ne_top.2 ⟨hbT, hcT⟩)).mpr hE
    rwa [ENNReal.toReal_add hbT hcT] at h1
  have hZ' : c.toReal ≤ a.toReal * e := by
    have h1 := (ENNReal.toReal_le_toReal hcT
      (ENNReal.mul_ne_top haT ENNReal.ofReal_ne_top)).mpr hZ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal he0] at h1
  refine (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top haT h1e) hbT).mp ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  have hEq : a.toReal * (1 - e) = a.toReal - a.toReal * e := by ring
  rw [hEq]
  linarith

/-- For `n ≥ 2` and `m = ceil(sqrt(n-1))`, the half-period hit probability is at least the final
size-event probability times `1-2^(-2^m)`. -/
private theorem htop_main (n m : ℕ) (hn : 2 ≤ n) (hm : m = Nat.ceil (Real.sqrt (n - 1))) :
    (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
        * ENNReal.ofReal (1 - (2:ℝ)^(-((2^m : ℕ) : ℝ)))
      ≤ ∑' L : List (ZMod (2^n)),
        if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0 := by
  classical
  have hnn : 1 ≤ n := by omega
  have hR : 0 < 24 * 2^(3*m) := by positivity
  have hmm : n - 1 ≤ m * m := by
    have hn1 : (0:ℝ) ≤ (n:ℝ) - 1 := by
      have h2n : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have hceil : (Real.sqrt ((n:ℝ) - 1)) ≤ ((m : ℕ) : ℝ) := by
      rw [hm]
      exact_mod_cast Nat.le_ceil _
    have h2 : (Real.sqrt ((n:ℝ) - 1))^2 ≤ ((m:ℕ):ℝ) * ((m:ℕ):ℝ) := by
      rw [pow_two]
      exact mul_le_mul hceil hceil (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hceil)
    rw [Real.sq_sqrt hn1] at h2
    have h3 : ((n - 1 : ℕ) : ℝ) ≤ ((m * m : ℕ) : ℝ) := by
      rw [Nat.cast_sub hnn, Nat.cast_mul, Nat.cast_one]
      exact h2
    exact_mod_cast h3
  have hε1 : (2:ℝ)^(-((2^m : ℕ) : ℝ)) ≤ 1 := by
    calc (2:ℝ)^(-((2^m : ℕ) : ℝ)) ≤ (2:ℝ)^(0:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simp)
      _ = 1 := by simp
  have hnum : ((2 ^ (2 ^ m : ℕ) : ℕ) : ENNReal)⁻¹
      = ENNReal.ofReal ((2:ℝ)^(-((2^m : ℕ) : ℝ))) := by
    rw [Real.rpow_neg (by norm_num), ENNReal.ofReal_inv_of_pos (by positivity),
      Real.rpow_natCast, ENNReal.ofReal_pow (by norm_num)]
    simp [Nat.cast_pow]
  have hE1 := pmf_event_le_one ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m))
    (fun L : List (ZMod (2^n)) => (2^m : ℕ) ≤ L.length)
  have hh1 := pmf_event_le_one ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m))
    (fun L : List (ZMod (2^n)) => ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L)
  have hz1 := pmf_event_le_one ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m))
    (fun L : List (ZMod (2^n)) => (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0)
  have hpt : ∀ L : List (ZMod (2^n)),
      (if (2^m : ℕ) ≤ L.length
        then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
      ≤ (if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
        + (if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0) := by
    intro L
    by_cases hEL : (2^m : ℕ) ≤ L.length
    · by_cases hν : ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L = 0
      · rw [if_pos hEL, hν]
        exact zero_le
      · obtain ⟨fr, _, hfr⟩ := exists_of_bind_ne_zero hν
        have hzh := idealSieveRec_zero_or_half hnn hmm hfr
        by_cases hZ : ∀ k ∈ L, k = 0
        · have hQz : (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0 := ⟨hEL, hZ⟩
          rw [if_pos hEL, if_pos hQz]
          calc ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L
              = 0 + ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L :=
                (zero_add _).symm
            _ ≤ (if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
                then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
                + ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L :=
                add_le_add (zero_le : (0:ENNReal) ≤ _) (le_refl _)
        · have hex : ∃ k, k ∈ L ∧ k ≠ 0 := by
            by_contra hcon
            refine hZ fun k hkL => ?_
            by_contra hk0
            exact hcon ⟨k, hkL, hk0⟩
          obtain ⟨k, hkL, hk0⟩ := hex
          have hhalf : k = ((2^(n-1):ℕ) : ZMod (2^n)) := (hzh k hkL).resolve_left hk0
          have hmem : ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L := by
            rw [← hhalf]
            exact hkL
          rw [if_pos hEL, if_pos hmem]
          calc ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L
              = ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L + 0 :=
                (add_zero _).symm
            _ ≤ ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L
                + (if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
                  then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0) :=
                add_le_add (le_refl _) (zero_le : (0:ENNReal) ≤ _)
    · rw [if_neg hEL]
      exact zero_le
  have hE : (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
      ≤ (∑' L : List (ZMod (2^n)),
          if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
            then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
        + (∑' L : List (ZMod (2^n)),
          if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
            then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0) := by
    calc (∑' L : List (ZMod (2^n)),
        if (2^m : ℕ) ≤ L.length
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
        ≤ (∑' L : List (ZMod (2^n)),
            ((if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
              then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
              + (if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
                then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0))) :=
          ENNReal.tsum_le_tsum hpt
      _ = (∑' L : List (ZMod (2^n)),
          if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
            then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0)
          + (∑' L : List (ZMod (2^n)),
          if (2^m : ℕ) ≤ L.length ∧ ∀ k ∈ L, k = 0
            then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0) :=
          ENNReal.tsum_add
  have hZcond := htop_cond (m := m) hnn hR
  rw [hnum] at hZcond
  exact htop_finish (Real.rpow_pos_of_pos (by norm_num) _).le hε1 hE1 hh1 hz1 hE hZcond

/-- For `n ≥ 2` and `m = ceil(sqrt(n-1))`, the ideal sieve hits the half-period label with
probability at least `(1-exp(-2^(m/3-2)))^m` [Kuperberg2005]. -/
theorem dihedralSieveIdealHit (n m : ℕ) (hn : 2 ≤ n) (hm : m = Nat.ceil (Real.sqrt (n - 1))) :
    ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m) ≤
      ∑' L : List (ZMod (2^n)),
        if ((2^(n-1):ℕ) : ZMod (2^n)) ∈ L
          then ((idealFreshRecords n (24 * 2^(3*m))).bind (idealSieveRec n m m)) L else 0 := by
  have hm1 : 1 ≤ m := by
    rw [hm]
    have hsqrt : (0:ℝ) < Real.sqrt ((n:ℝ) - 1) := by
      apply Real.sqrt_pos.mpr
      have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr hsqrt)
  apply idealHit_of_topbit n m hm1
  exact htop_main n m hn hm
end

end Qatlib.Concepts.HspRecovery.SieveAlgorithm
