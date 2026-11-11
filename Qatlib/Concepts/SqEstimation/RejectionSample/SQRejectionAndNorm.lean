/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SqEstimation.RejectionSample.SQRejectionModels

/-!
# Capped rejection laws and norm estimation

`sqCappedRecords` supplies independent proposal-and-coin records for `sqRejectRun`. The module
derives the exact capped output law and expected cost from the envelope-to-target energy ratio,
then uses acceptance-bit block medians to estimate the target squared norm and control the
induced norm error. For background, see [ChiaEtAl2022].

## Main statements

* `sq_rejection_actual_capped_law_and_cost`: proves normalization, geometric timeout, output
  probabilities, and cost bounds.
* `sq_rejection_acceptance_norm_estimation`: bounds relative squared-norm estimation error and
  transfers it through the square root.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.SqEstimation.RejectionSample
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The finite distribution of `B` independent proposal-and-acceptance pairs. -/
noncomputable def sqCappedRecords {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) : FinDist (Fin B→I×Bool) :=
  independentSampleLaw (fun _ => sqTrialLaw p coin)

/-- The product masses of all length-`B` proposal-and-coin records sum to one. -/
theorem sqTrialProduct_sum_one {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) :
    (∑ omega : Fin B→I×Bool,sqTrialProduct p coin omega)=1 :=
  (sqCappedRecords p coin B).sum_one

/-- On a nonempty record, rejection sampling stops at an accepted first proposal with cost four,
or runs the tail and adds four to its cost. -/
theorem sqRejectRun_cons {I : Type} {B : ℕ} (z : I×Bool) (omega : Fin B→I×Bool) :
    sqRejectRun (Fin.cons z omega) = if z.2 then (some z.1,4) else
      ((sqRejectRun omega).1,(sqRejectRun omega).2+4) := by
  simp [sqRejectRun,List.ofFn_succ,sqRejectList]

/-- A weighted sum over length-`B + 1` trial records decomposes into a sum over the first trial
and the independent tail record. -/
theorem sq_record_sum_cons {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) (f : (Fin (B+1)→I×Bool)→ℝ) :
    (∑ omega : Fin (B+1)→I×Bool,sqTrialProduct p coin omega*f omega) =
      ∑ z : I×Bool,sqTrialMass p coin z*(∑ omega : Fin B→I×Bool,
        sqTrialProduct p coin omega*f (Fin.cons z omega)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (B+1) => I×Bool)).sum_comp,Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply,sqTrialProduct,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  change (sqTrialMass p coin z*(∏ b,sqTrialMass p coin (omega b)))*f (Fin.cons z omega) = _
  ring

/-- The total trial-record probability that capped rejection sampling returns a specified
optional output. -/
noncomputable def sqRejectMass {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) (o : Option I) : ℝ :=
  ∑ omega : Fin B→I×Bool,sqTrialProduct p coin omega*(if (sqRejectRun omega).1=o then 1 else 0)

/-- The output mass equals the sum of product trial masses over records whose run returns that
output. -/
theorem sqRejectMass_eq_filter {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) (o : Option I) :
    sqRejectMass p coin B o = ∑ omega ∈ Finset.univ.filter
      (fun omega : Fin B→I×Bool => (sqRejectRun omega).1=o),sqTrialProduct p coin omega := by
  rw [sqRejectMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro omega _
  split_ifs <;> simp

/-- The output mass with one additional trial is the immediate accepted-output mass plus the
rejection probability times the remaining-run mass. -/
theorem sqRejectMass_succ {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) (o : Option I) :
    sqRejectMass p coin (B+1) o =
      (∑ i,sqTrialMass p coin (i,true)*(if some i=o then 1 else 0)) +
      (∑ i,sqTrialMass p coin (i,false))*sqRejectMass p coin B o := by
  rw [sqRejectMass,sq_record_sum_cons,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,sqRejectRun_cons,if_true,Bool.false_eq_true,if_false]
  have hsum : ∀ i : I,
      (∑ omega : Fin B→I×Bool,sqTrialProduct p coin omega*(if some i=o then 1 else 0)) =
        if some i=o then 1 else 0 := by
    intro i
    rw [← Finset.sum_mul,sqTrialProduct_sum_one,one_mul]
  simp only [hsum]
  rw [Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [sqRejectMass]

/-- With zero trials, capped rejection sampling assigns all output mass to `none`. -/
theorem sqRejectMass_zero {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (o : Option I) :
    sqRejectMass p coin 0 o = if none=o then 1 else 0 := by
  simp [sqRejectMass,sqTrialProduct,sqRejectRun,sqRejectList]

/-- The total rejection probability is one minus the total acceptance probability. -/
theorem sqTrial_false_sum {I : Type} [Fintype I] (p : FinDist I) (coin : I→FinDist Bool) :
    (∑ i,sqTrialMass p coin (i,false))=1-(∑ i,sqTrialMass p coin (i,true)) := by
  have h := (sqTrialLaw p coin).sum_one
  simp only [sqTrialLaw,Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib] at h
  linarith

/-- With exact envelope proposals and ratio coins, timeout after `B` trials has probability `(1
- 1/phi)^B`, where `phi` is the envelope-to-target energy ratio. Each successful output has
the complementary success probability times its normalized target squared norm. -/
theorem sqRejectMass_closed {I : Type} [Fintype I] [DecidableEq I]
    (u uh : I→ℂ) (p : FinDist I) (coin : I→FinDist Bool)
    (hen : SQEnvelope u uh)
    (hp : ∀ i,p.prob i=Complex.normSq (uh i)/(∑ i,Complex.normSq (uh i)))
    (hc : ∀ i,(coin i).prob true=sqRatio u uh i) (B : ℕ) :
    let phi := (∑ i,Complex.normSq (uh i))/(∑ i,Complex.normSq (u i));
    sqRejectMass p coin B none=(1-1/phi)^B ∧
    ∀ i,sqRejectMass p coin B (some i)=
      (1-(1-1/phi)^B)*Complex.normSq (u i)/(∑ i,Complex.normSq (u i)) := by
  (try dsimp only)
  let phi := (∑ i,Complex.normSq (uh i))/(∑ i,Complex.normSq (u i))
  have hs := sq_rejection_envelope_single_trial I u uh p coin hen hp hc
  have hfalse : (∑ i,sqTrialMass p coin (i,false))=1-1/phi := by rw [sqTrial_false_sum,hs.2.2.1]
  have hm (i : I) : sqTrialMass p coin (i,true)=
      (1/phi)*(Complex.normSq (u i)/(∑ i,Complex.normSq (u i))) := by
    rw [sqTrial_true_mass u uh p coin hen hp hc]
    dsimp [phi]
    field_simp [ne_of_gt hen.1,ne_of_gt (sqEnvelope_energy u uh hen).1]
  induction B with
  | zero => simp [sqRejectMass_zero]
  | succ B ih =>
    constructor
    · rw [sqRejectMass_succ,hfalse,ih.1]
      simp [pow_succ,mul_comm,phi]
    · intro i
      rw [sqRejectMass_succ,hfalse,ih.2 i]
      simp only [Option.some.injEq,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      rw [hm i,pow_succ]
      ring

/-- The cost of a capped rejection run on any length-`B` record is at most `4 * B`. -/
theorem sqRejectRun_cost_le {I : Type} {B : ℕ} (omega : Fin B→I×Bool) : (sqRejectRun omega).2 ≤ 4*B := by
  have h (l : List (I×Bool)) : (sqRejectList l).2 ≤ 4*l.length := by
    induction l with
    | nil => simp [sqRejectList]
    | cons z l ih =>
      simp only [sqRejectList]
      split_ifs <;> simp only
      all_goals simp only [List.length_cons] at ⊢
      all_goals omega
  simpa [sqRejectRun] using h (List.ofFn omega)

/-- The expected recorded cost of capped rejection sampling under the product trial law. -/
noncomputable def sqRejectExpectedCost {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) : ℝ :=
  ∑ omega : Fin B→I×Bool,sqTrialProduct p coin omega*((sqRejectRun omega).2 : ℝ)

/-- Adding one trial incurs cost four plus the total rejection probability times the expected
cost of the remaining capped run. -/
theorem sqRejectExpectedCost_succ {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) :
    sqRejectExpectedCost p coin (B+1)=4+
      (∑ i,sqTrialMass p coin (i,false))*sqRejectExpectedCost p coin B := by
  rw [sqRejectExpectedCost,sq_record_sum_cons,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,sqRejectRun_cons,Bool.false_eq_true,if_false,if_true,Nat.cast_add,Nat.cast_ofNat]
  have hsum : (∑ omega : Fin B→I×Bool,sqTrialProduct p coin omega*(4 : ℝ))=4 := by
    rw [← Finset.sum_mul,sqTrialProduct_sum_one,one_mul]
  simp_rw [mul_add,Finset.sum_add_distrib,hsum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul]
  have htot : (∑ i,sqTrialMass p coin (i,true))+(∑ i,sqTrialMass p coin (i,false))=1 := by
    rw [sqTrial_false_sum];ring
  dsimp only [sqRejectExpectedCost]
  nlinarith [htot]

/-- With exact envelope proposals and ratio coins, expected capped rejection cost is at most
four times the envelope-to-target energy ratio. -/
theorem sqRejectExpectedCost_le {I : Type} [Fintype I] [DecidableEq I]
    (u uh : I→ℂ) (p : FinDist I) (coin : I→FinDist Bool)
    (hen : SQEnvelope u uh)
    (hp : ∀ i,p.prob i=Complex.normSq (uh i)/(∑ i,Complex.normSq (uh i)))
    (hc : ∀ i,(coin i).prob true=sqRatio u uh i) (B : ℕ) :
    sqRejectExpectedCost p coin B ≤ 4*((∑ i,Complex.normSq (uh i))/(∑ i,Complex.normSq (u i))) := by
  let phi := (∑ i,Complex.normSq (uh i))/(∑ i,Complex.normSq (u i))
  have hs := sq_rejection_envelope_single_trial I u uh p coin hen hp hc
  have hphi : 0 < phi := lt_of_lt_of_le (by norm_num) hs.1
  have hfalse : (∑ i,sqTrialMass p coin (i,false))=1-1/phi := by rw [sqTrial_false_sum,hs.2.2.1]
  have hf0 : 0 ≤ ∑ i,sqTrialMass p coin (i,false) :=
    Finset.sum_nonneg (fun i _ => (sqTrialLaw p coin).nonneg (i,false))
  induction B with
  | zero =>
    simpa [sqRejectExpectedCost,sqTrialProduct,sqRejectRun,sqRejectList,phi] using
      (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hphi.le)
  | succ B ih =>
    rw [sqRejectExpectedCost_succ]
    calc
      _ ≤ 4+(∑ i,sqTrialMass p coin (i,false))*(4*phi) := add_le_add (le_refl 4) (mul_le_mul_of_nonneg_left ih hf0)
      _ = 4*phi := by rw [hfalse];field_simp;ring

/-- The total probability of a nonempty rejection-sampling output is one minus the timeout mass. -/
theorem sqReject_success_complement {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ) :
    (∑ omega ∈ Finset.univ.filter (fun omega : Fin B→I×Bool => (sqRejectRun omega).1≠none),
      sqTrialProduct p coin omega)=1-sqRejectMass p coin B none := by
  have hsplit : (∑ omega ∈ Finset.univ.filter (fun omega : Fin B→I×Bool => (sqRejectRun omega).1≠none),
      sqTrialProduct p coin omega)+sqRejectMass p coin B none=1 := by
    rw [sqRejectMass_eq_filter,Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
    convert sqTrialProduct_sum_one p coin B using 1
    apply Finset.sum_congr rfl
    intro omega _
    by_cases h : (sqRejectRun omega).1=none <;> simp [h]
  linarith

/-- For a positive-energy target with a dominating envelope and exact proposal and coin laws,
the capped record law is normalized and has geometric timeout and target-proportional
successful output masses. Pathwise cost is at most `4*B`, expected cost is at most `4*phi`,
and any timeout bound gives the complementary success guarantee, as in [Chia et al., Lemma
3.5][ChiaEtAl2022]. -/
theorem sq_rejection_actual_capped_law_and_cost : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (u uh : I→ℂ) (p : FinDist I) (coin : I→FinDist Bool) (B : ℕ),
    SQEnvelope u uh → (∀ i,p.prob i=Complex.normSq (uh i)/(∑ i,Complex.normSq (uh i))) →
    (∀ i,(coin i).prob true=sqRatio u uh i) →
    let phi := (∑ i,Complex.normSq (uh i))/(∑ i,Complex.normSq (u i));
    (∑ omega : Fin B→I×Bool,sqTrialProduct p coin omega)=1 ∧
    (∑ omega ∈ Finset.univ.filter (fun omega : Fin B→I×Bool => (sqRejectRun omega).1=none),
      sqTrialProduct p coin omega)=(1-1/phi)^B ∧
    (∀ i,(∑ omega ∈ Finset.univ.filter (fun omega : Fin B→I×Bool => (sqRejectRun omega).1=some i),
      sqTrialProduct p coin omega)=(1-(1-1/phi)^B)*Complex.normSq (u i)/(∑ i,Complex.normSq (u i))) ∧
    (∀ omega : Fin B→I×Bool,(sqRejectRun omega).2 ≤ 4*B) ∧
    (∑ omega : Fin B→I×Bool,sqTrialProduct p coin omega*((sqRejectRun omega).2 : ℝ)) ≤ 4*phi ∧
    (∀ delta : ℝ,0 < delta → (1-1/phi)^B ≤ delta →
      1-delta ≤ ∑ omega ∈ Finset.univ.filter (fun omega : Fin B→I×Bool => (sqRejectRun omega).1≠none),
        sqTrialProduct p coin omega) := by
  intro I _ _ u uh p coin B hen hp hc
  (try dsimp only)
  have hmass := sqRejectMass_closed u uh p coin hen hp hc B
  refine ⟨sqTrialProduct_sum_one p coin B,?_,?_,sqRejectRun_cost_le,
    sqRejectExpectedCost_le u uh p coin hen hp hc B,?_⟩
  · rw [← sqRejectMass_eq_filter];exact hmass.1
  · intro i
    rw [← sqRejectMass_eq_filter];exact hmass.2 i
  · intro delta _ hdelta
    rw [sqReject_success_complement,hmass.1]
    linarith

/-- The real-valued indicator that a proposal-and-coin pair is accepted. -/
def sqAcceptBit {I : Type} (z : I×Bool) : ℝ := if z.2 then 1 else 0

/-- If `a` is the total acceptance probability, the acceptance bit has expectation `a` and
centered second moment `a * (1 - a)`. -/
theorem sqAcceptBit_moments {I : Type} [Fintype I] (p : FinDist I) (coin : I→FinDist Bool) :
    let a := ∑ i,sqTrialMass p coin (i,true);
    (sqTrialLaw p coin).expect sqAcceptBit=a ∧
    (sqTrialLaw p coin).expect (fun z => (sqAcceptBit z-a)^2)=a*(1-a) := by
  (try dsimp only)
  constructor
  · simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,sqTrialLaw,sqAcceptBit,Fintype.sum_prod_type,Fintype.sum_bool]
  · change (∑ z : I×Bool,sqTrialMass p coin z*(sqAcceptBit z-(∑ i,sqTrialMass p coin (i,true)))^2)=_
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,sqAcceptBit,if_true,Bool.false_eq_true,if_false,zero_sub,neg_sq,
      Finset.sum_add_distrib,← Finset.sum_mul]
    rw [sqTrial_false_sum]
    ring

/-- For positive `a` and nonnegative relative tolerance, a relative error bound around `a`
implies the same relative bound for the real square roots. -/
theorem sq_relative_sqrt (x a nu : ℝ) (ha : 0 < a) (hnu : 0 ≤ nu)
    (hclose : |x-a| ≤ nu*a) : |Real.sqrt x-Real.sqrt a| ≤ nu*Real.sqrt a := by
  by_cases hx : 0 ≤ x
  · have hs := Real.sq_sqrt hx
    have ha2 := Real.sq_sqrt ha.le
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    have hid : (Real.sqrt x-Real.sqrt a)*(Real.sqrt x+Real.sqrt a)=x-a := by nlinarith
    have hab : |Real.sqrt x-Real.sqrt a| * Real.sqrt a ≤ |x-a| := by
      rw [← hid,abs_mul,abs_of_nonneg (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg a))]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg x]) (abs_nonneg _)
    have h := hab.trans hclose
    rw [show nu*a=(nu*Real.sqrt a)*Real.sqrt a by nlinarith] at h
    exact (mul_le_mul_iff_left₀ hsa).mp (by simpa [mul_comm] using h)
  · have hneg : x < 0 := lt_of_not_ge hx
    have hn : 1 ≤ nu := by rw [abs_of_neg (by linarith)] at hclose; nlinarith
    rw [Real.sqrt_eq_zero_of_nonpos hneg.le,zero_sub,abs_neg,abs_of_nonneg (Real.sqrt_nonneg a)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg a)

/-- Under exact envelope sampling and acceptance coins, block size at least `16*phi/nu²` bounds
the relative squared-norm failure probability by `2^(2*r+1)*(1/16)^(r+1)` for `0 < nu ≤ 1`.
Every record satisfying that squared-norm bound also satisfies the corresponding relative
norm bound, giving the acceptance-based estimate of [Chia et al., Lemma 3.5][ChiaEtAl2022]. -/
theorem sq_rejection_acceptance_norm_estimation : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (u uh : I→ℂ) (p : FinDist I) (coin : I→FinDist Bool) (r B : ℕ) (nu : ℝ),
    SQEnvelope u uh → (∀ i,p.prob i=Complex.normSq (uh i)/(∑ i,Complex.normSq (uh i))) →
    (∀ i,(coin i).prob true=sqRatio u uh i) → 0 < B → 0 < nu → nu ≤ 1 →
    16*((∑ i,Complex.normSq (uh i))/(∑ i,Complex.normSq (u i)))/nu^2 ≤ (B : ℝ) →
    (∑ omega ∈ Finset.univ.filter (fun omega : Fin (2*r+1)→Fin B→I×Bool =>
      nu*(∑ i,Complex.normSq (u i)) < |sqNormSquaredEstimate (∑ i,Complex.normSq (uh i)) r B omega-
        (∑ i,Complex.normSq (u i))|), ∏ j,sqTrialProduct p coin (omega j)) ≤
      (2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1) ∧
    (∀ omega : Fin (2*r+1)→Fin B→I×Bool,
      |sqNormSquaredEstimate (∑ i,Complex.normSq (uh i)) r B omega-(∑ i,Complex.normSq (u i))| ≤
        nu*(∑ i,Complex.normSq (u i)) →
      |Real.sqrt (sqNormSquaredEstimate (∑ i,Complex.normSq (uh i)) r B omega)-
        Real.sqrt (∑ i,Complex.normSq (u i))| ≤ nu*Real.sqrt (∑ i,Complex.normSq (u i))) := by
  intro I _ _ u uh p coin r B nu hen hp hc hB hnu _ hbudget
  let eu := ∑ i,Complex.normSq (u i)
  let d := ∑ i,Complex.normSq (uh i)
  let a := eu/d
  have heu : 0 < eu := hen.1
  have hd : 0 < d := (sqEnvelope_energy u uh hen).1
  have ha : 0 < a := div_pos heu hd
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have htrue : (∑ i,sqTrialMass p coin (i,true))=a := by
    simp_rw [sqTrial_true_mass u uh p coin hen hp hc]
    rw [← Finset.sum_div]
  have hmean : (sqTrialLaw p coin).expect sqAcceptBit=a := by
    rw [(sqAcceptBit_moments p coin).1,htrue]
  have hvar : (sqTrialLaw p coin).expect (fun z => (sqAcceptBit z-a)^2) ≤ a := by
    rw [← htrue,(sqAcceptBit_moments p coin).2,htrue]
    nlinarith
  have hprecision : a/(B : ℝ) ≤ (nu*a)^2/16 := by
    have hh := (div_le_iff₀ (pow_pos hnu 2)).mp hbudget
    change 16*(d/eu) ≤ (B : ℝ)*nu^2 at hh
    have hid : (d/eu)*a=1 := by dsimp [a];field_simp
    have hh' := mul_le_mul_of_nonneg_right hh ha.le
    rw [mul_assoc, hid] at hh'
    apply (div_le_iff₀ hBr).mpr
    nlinarith [sq_nonneg nu]
  let laws : Fin (2*r+1)→Fin B→FinDist (I×Bool) := fun _ _ => sqTrialLaw p coin
  let weights : Fin (2*r+1)→Fin B→ℝ := fun _ _ => 1/(B : ℝ)
  let stats : Fin (2*r+1)→Fin B→(I×Bool)→ℝ := fun _ _ => sqAcceptBit
  have hmeans : ∀ j, (∑ b,weights j b*(laws j b).expect (stats j b))=a := by
    intro j
    simp only [weights,laws,stats,hmean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hvars : ∀ j, (∑ b,(weights j b)^2*(laws j b).expect
      (fun z => (stats j b z-(laws j b).expect (stats j b))^2)) ≤ (nu*a)^2/16 := by
    intro j
    simp only [weights,laws,stats,hmean]
    calc
      _ ≤ ∑ _ : Fin B,(1/(B : ℝ))^2*a := Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left hvar (sq_nonneg _))
      _ = a/(B : ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp
      _ ≤ _ := hprecision
  have hcon := heterogeneous_weighted_median_concentration r B laws weights stats a (nu*a)
    (mul_pos hnu ha) hmeans hvars
  have hblocks (omega : Fin (2*r+1)→Fin B→I×Bool) :
      weightedBlock r B weights stats omega =
        (fun j => (∑ b,if (omega j b).2 then (1 : ℝ) else 0)/(B : ℝ)) := by
    ext j
    simp only [weightedBlock,weights,stats,sqAcceptBit,← Finset.mul_sum]
    ring
  have hevent (omega : Fin (2*r+1)→Fin B→I×Bool) :
      nu*eu < |sqNormSquaredEstimate d r B omega-eu| ↔
        nu*a < |sortedBlockMedian r (weightedBlock r B weights stats omega)-a| := by
    rw [hblocks]
    have hea : eu=d*a := by dsimp [a];field_simp
    rw [sqNormSquaredEstimate,hea,← mul_sub,abs_mul,abs_of_pos hd]
    constructor <;> intro h <;> nlinarith [hd]
  refine ⟨?_,fun omega hclose => sq_relative_sqrt _ eu nu heu hnu.le hclose⟩
  rw [Finset.filter_congr (fun omega _ => hevent omega)]
  exact hcon

end Qatlib.Concepts.SqEstimation.RejectionSample
