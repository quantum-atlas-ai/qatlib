/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanRecoveryProbability
import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardPhase
import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder

/-!
# Boolean Fourier sampling for near periods

Defines `NearPeriodPromise`, which bounds the number of inputs where translation by a Boolean
vector changes the function value. Decomposes oracle label branches into periodic and
exceptional parts, then uses Fourier orthogonality and Parseval's identity to bound the
probability of a nonorthogonal sample.

If at most `q` of the `2 ^ n` inputs violate periodicity, one sample is nonorthogonal with
probability at most `q / 2 ^ n`, and all `m` fresh samples are orthogonal with probability at
least `(1 - q / 2 ^ n) ^ m` when `q ≤ 2 ^ n`. This extends the orthogonality mechanism of Simon
sampling [Simon1997].

## Main statements

* `booleanSample_dot_ne_zero_event_le`: bounds one-sample nonorthogonality.
* `hiddenSubgroupFreshSamples_allDot_ge_of_nearPeriod`: bounds the probability that all fresh
  samples are orthogonal.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.WalshMoment.Forrelation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open scoped Classical ComplexConjugate ENNReal

/-- The promise that at most `q` inputs have different function values before and after
translation by `s`. -/
def NearPeriodPromise {n : ℕ} {R : Type} (f : BooleanVec n → R)
    (s : BooleanVec n) (q : ℕ) : Prop :=
  Nat.card {x : BooleanVec n | f x ≠ f (x + s)} ≤ q

variable {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- Every Boolean vector added to itself is zero. -/
private lemma booleanVec_add_self (s : BooleanVec n) : s + s = 0 := by
  funext i
  exact zmod2_add_self (s i)

/-- The sum of Born probabilities is preserved by the finite additive Fourier transform. -/
private lemma born_parseval {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ψ : QState G) : ∑ χ, BornProb (Qatlib.Concepts.WalshMoment.Forrelation.fourier ψ) χ = ∑ x, BornProb ψ x := by
  have h := inner_fourier ψ ψ
  simp only [inner_self, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- If a state is invariant under translation by `s`, its Fourier amplitude vanishes at every
character taking value `-1` on `s`. -/
private lemma fourier_periodic_zero (ψ : QState (BooleanVec n)) (s : BooleanVec n)
    (hp : ∀ x, ψ (x + s) = ψ x) (χ : AddChar (BooleanVec n) ℂ) (hχ : χ s = -1) :
    Qatlib.Concepts.WalshMoment.Forrelation.fourier ψ χ = 0 := by
  let a : ℂ := ∑ x, conj (χ x) * ψ x
  have hsum := Equiv.sum_comp (Equiv.addRight s) (fun x => conj (χ x) * ψ x)
  have he : -a = a := by
    calc
      -a = ∑ x, conj (χ (x + s)) * ψ (x + s) := by
        simp only [AddChar.map_add_eq_mul, hp, hχ, map_neg,
          mul_neg_one, neg_mul, Finset.sum_neg_distrib, a]
      _ = a := hsum
  have ha : a = 0 := by linear_combination (-(1 / 2 : ℂ)) * he
  rw [fourier_apply]
  change fourierScale (BooleanVec n) * a = 0
  rw [ha, mul_zero]

/-- The oracle label branch restricted to inputs where translation by `s` changes the function
value. -/
private def badLabelBranch (f : BooleanVec n → R) (s : BooleanVec n) (z : R) :
    QState (BooleanVec n) := fun x =>
  if f x = f (x + s) then 0 else addOracleLabelBranch f (Uniform (BooleanVec n)) z x

/-- The oracle label branch restricted to inputs where translation by `s` preserves the function
value. -/
private def goodLabelBranch (f : BooleanVec n → R) (s : BooleanVec n) (z : R) :
    QState (BooleanVec n) := fun x =>
  if f x = f (x + s) then addOracleLabelBranch f (Uniform (BooleanVec n)) z x else 0

/-- The good oracle label branch is invariant under translation by `s`. -/
private lemma goodLabelBranch_periodic (f : BooleanVec n → R) (s : BooleanVec n) (z : R) :
    ∀ x, goodLabelBranch f s z (x + s) = goodLabelBranch f s z x := by
  intro x
  have hss : x + s + s = x := by rw [add_assoc, booleanVec_add_self, add_zero]
  unfold goodLabelBranch
  rw [hss]
  by_cases hf : f x = f (x + s)
  · simp [hf, addOracleLabelBranch_apply, Uniform]
  · simp [hf, Ne.symm hf]

/-- Every element of `ZMod 2` equals zero or one. -/
private lemma zmod_two_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hz : z.val ≤ 1 := Nat.le_of_lt_succ (by simpa using z.val_lt)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hz with hz | hz
  · exact Or.inl ((ZMod.val_eq_zero z).1 hz)
  · exact Or.inr ((ZMod.val_eq_one (by norm_num) z).1 hz)

/-- A Boolean character whose decoded vector has nonzero dot product with `s` takes the value
`-1` on `s`. -/
private lemma character_neg_of_dot_ne (s : BooleanVec n) (χ : AddChar (BooleanVec n) ℂ)
    (h : booleanDot s ((booleanCharacterEquiv n).symm χ) ≠ 0) : χ s = -1 := by
  have hd : booleanDot ((booleanCharacterEquiv n).symm χ) s = 1 := by
    apply (zmod_two_eq_zero_or_one _).resolve_left
    simpa only [booleanDot_comm'] using h
  conv_lhs => rw [← (booleanCharacterEquiv n).apply_symm_apply χ]
  rw [booleanCharacterEquiv_apply, booleanCharacter_apply, hd, zmod2_stdAddChar_one]

/-- At a character nonorthogonal to `s`, the Fourier amplitude of the full oracle label branch
equals that of its bad part. -/
private lemma fourier_bad_branch (f : BooleanVec n → R) (s : BooleanVec n) (z : R)
    (χ : AddChar (BooleanVec n) ℂ)
    (hχ : booleanDot s ((booleanCharacterEquiv n).symm χ) ≠ 0) :
    Qatlib.Concepts.WalshMoment.Forrelation.fourier (addOracleLabelBranch f (Uniform (BooleanVec n)) z) χ =
      Qatlib.Concepts.WalshMoment.Forrelation.fourier (badLabelBranch f s z) χ := by
  have hsplit : addOracleLabelBranch f (Uniform (BooleanVec n)) z =
      goodLabelBranch f s z + badLabelBranch f s z := by
    funext x
    by_cases hx : f x = f (x + s) <;> simp [goodLabelBranch, badLabelBranch, hx]
  have hadd : Qatlib.Concepts.WalshMoment.Forrelation.fourier (goodLabelBranch f s z + badLabelBranch f s z) =
      Qatlib.Concepts.WalshMoment.Forrelation.fourier (goodLabelBranch f s z) +
        Qatlib.Concepts.WalshMoment.Forrelation.fourier (badLabelBranch f s z) :=
    (fourierEquiv (G := BooleanVec n)).map_add _ _
  rw [hsplit, hadd]
  have hz := fourier_periodic_zero (goodLabelBranch f s z) s
    (goodLabelBranch_periodic f s z) χ (character_neg_of_dot_ne s χ hχ)
  simp [hz]

/-- The total Born mass of all bad label branches is the proportion of inputs where translation
by `s` changes `f`. -/
private lemma bad_branch_energy (f : BooleanVec n → R) (s : BooleanVec n) :
    (∑ z : R, ∑ x : BooleanVec n, BornProb (badLabelBranch f s z) x) =
      (Nat.card {x : BooleanVec n | f x ≠ f (x + s)} : ℝ) /
        (Fintype.card (BooleanVec n) : ℝ) := by
  have hu : ∀ x : BooleanVec n, ‖Uniform (BooleanVec n) x‖ ^ 2 =
      (Fintype.card (BooleanVec n) : ℝ)⁻¹ := by
    intro x
    simp [Uniform, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  have hrow : ∀ x : BooleanVec n, (∑ z : R, BornProb (badLabelBranch f s z) x) =
      if f x ≠ f (x + s) then (Fintype.card (BooleanVec n) : ℝ)⁻¹ else 0 := by
    intro x
    by_cases hx : f x = f (x + s)
    · simp [badLabelBranch, BornProb, hx]
    · rw [if_pos hx, Finset.sum_eq_single (f x)]
      · simpa [badLabelBranch, BornProb, addOracleLabelBranch_apply, hx] using hu x
      · intro z _ hz
        simp [badLabelBranch, BornProb, addOracleLabelBranch_apply, hx, hz]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
  have hc : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} =
      (Finset.univ.filter (fun x : BooleanVec n => f x ≠ f (x + s))).card := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun x _ => hrow x), ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, ← hc, div_eq_mul_inv]

/-- The probability of a Fourier character whose decoded vector is nonorthogonal to `s` is at
most the proportion of inputs violating translation invariance. -/
private lemma sampleDist_nonorthogonal_le (f : BooleanVec n → R) (s : BooleanVec n) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar (BooleanVec n) ℂ =>
      booleanDot s ((booleanCharacterEquiv n).symm χ) ≠ 0),
      (hiddenSubgroupSampleDist f (booleanCharacterEquiv n).toEquiv).prob χ) ≤
      (Nat.card {x : BooleanVec n | f x ≠ f (x + s)} : ℝ) /
        (Fintype.card (BooleanVec n) : ℝ) := by
  have hprob : ∀ χ : AddChar (BooleanVec n) ℂ,
      (hiddenSubgroupSampleDist f (booleanCharacterEquiv n).toEquiv).prob χ =
        ∑ z : R, BornProb (Qatlib.Concepts.WalshMoment.Forrelation.fourier
          (addOracleLabelBranch f (Uniform (BooleanVec n)) z)) χ := by
    intro χ
    simp only [hiddenSubgroupSampleDist, MarginalProbLeft, MeasureProb,
      Finset.sum_product, Finset.sum_singleton]
    simp_rw [bornProb_run_hiddenSubgroupSamplingCircuit]
  calc
    _ = ∑ χ ∈ Finset.univ.filter (fun χ : AddChar (BooleanVec n) ℂ =>
        booleanDot s ((booleanCharacterEquiv n).symm χ) ≠ 0),
        ∑ z : R, BornProb (Qatlib.Concepts.WalshMoment.Forrelation.fourier (badLabelBranch f s z)) χ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hprob]
      apply Finset.sum_congr rfl
      intro z _
      unfold BornProb
      rw [fourier_bad_branch f s z χ (Finset.mem_filter.mp hχ).2]
    _ ≤ ∑ χ : AddChar (BooleanVec n) ℂ,
        ∑ z : R, BornProb (Qatlib.Concepts.WalshMoment.Forrelation.fourier (badLabelBranch f s z)) χ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun χ _ _ => Finset.sum_nonneg fun z _ => bornProb_nonneg _ _)
    _ = ∑ z : R, ∑ x : BooleanVec n, BornProb (badLabelBranch f s z) x := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => born_parseval (badLabelBranch f s z)
    _ = _ := bad_branch_energy f s

/-- For a finite probability mass function, an event probability is the sum of the masses of its
satisfying elements. -/
private theorem finite_pmf_event_sum {A : Type*} [Fintype A] (p : PMF A)
    (P : A → Prop) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p P = ∑ a ∈ Finset.univ.filter P, p a := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]

/-- The Boolean hidden subgroup sample law assigns an event the `ENNReal.ofReal` conversion of
the corresponding sum of finite-distribution probabilities. -/
private lemma sample_event_ofReal (f : BooleanVec n → R)
    (P : AddChar (BooleanVec n) ℂ → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (hiddenSubgroupSampleLaw f (booleanCharacterEquiv n).toEquiv) P =
      ENNReal.ofReal (∑ χ ∈ Finset.univ.filter P,
        (hiddenSubgroupSampleDist f (booleanCharacterEquiv n).toEquiv).prob χ) := by
  rw [finite_pmf_event_sum]
  simp only [hiddenSubgroupSampleLaw_apply]
  exact (ENNReal.ofReal_sum_of_nonneg (fun χ _ =>
    (hiddenSubgroupSampleDist f (booleanCharacterEquiv n).toEquiv).nonneg χ)).symm

/-- Under `NearPeriodPromise f s q`, the probability that one decoded Fourier sample has nonzero
dot product with `s` is at most `q / 2 ^ n`. -/
theorem booleanSample_dot_ne_zero_event_le (f : BooleanVec n → R)
    (s : BooleanVec n) (q : ℕ) (hq : NearPeriodPromise f s q) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (hiddenSubgroupSampleLaw f (booleanCharacterEquiv n).toEquiv)
      (fun χ => booleanDot s ((booleanCharacterEquiv n).symm χ) ≠ 0) ≤
        ENNReal.ofReal ((q : ℝ) / 2 ^ n) := by
  rw [sample_event_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hc : Fintype.card (BooleanVec n) = 2 ^ n := by simp [BooleanVec, Fintype.card_pi]
  have hmass := sampleDist_nonorthogonal_le f s
  have hcount : (Nat.card {x : BooleanVec n | f x ≠ f (x + s)} : ℝ) /
      (Fintype.card (BooleanVec n) : ℝ) ≤ (q : ℝ) / (Fintype.card (BooleanVec n) : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hq) (Nat.cast_nonneg _)
  have hfin := hmass.trans hcount
  rw [hc, Nat.cast_pow, Nat.cast_ofNat] at hfin
  refine le_trans ?_ hfin
  apply le_of_eq
  apply Finset.sum_congr
  · ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro χ _
    rfl

/-- If at most `q ≤ 2 ^ n` inputs violate periodicity by `s`, the probability that all `m` fresh
decoded samples are orthogonal to `s` is at least `(1 - q / 2 ^ n) ^ m`. -/
theorem hiddenSubgroupFreshSamples_allDot_ge_of_nearPeriod (f : BooleanVec n → R)
    (s : BooleanVec n) (q : ℕ) (hqn : q ≤ 2 ^ n) (hq : NearPeriodPromise f s q) (m : ℕ) :
    ENNReal.ofReal ((1 - (q : ℝ) / 2 ^ n) ^ m) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv m)
        (fun xs => ∀ i, booleanDot s (booleanDecodedSamples xs i) = 0) := by
  let p := hiddenSubgroupSampleDist f (booleanCharacterEquiv n).toEquiv
  let P := fun χ : AddChar (BooleanVec n) ℂ =>
    booleanDot s ((booleanCharacterEquiv n).symm χ) = 0
  have hevent : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv m)
        (fun xs => ∀ i, booleanDot s (booleanDecodedSamples xs i) = 0) =
      ENNReal.ofReal ((∑ χ ∈ Finset.univ.filter P, p.prob χ) ^ m) := by
    rw [finite_pmf_event_sum, hiddenSubgroupFreshSamples_event]
    congr 1
    unfold FinDist.probEvent
    refine Eq.trans ?_ (FinDist.sum_probOf_forall_eq_pow p P m)
    apply Finset.sum_congr
    · ext xs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, booleanDecodedSamples]
    · intro xs _
      rfl
  rw [hevent]
  apply ENNReal.ofReal_le_ofReal
  have hbad := booleanSample_dot_ne_zero_event_le f s q hq
  rw [sample_event_ofReal] at hbad
  have hbadR := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ (q : ℝ) / 2 ^ n)).mp hbad
  have hpart : (∑ χ ∈ Finset.univ.filter P, p.prob χ) +
      (∑ χ ∈ Finset.univ.filter (fun χ => ¬ P χ), p.prob χ) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, p.sum_one]
  have hg : 1 - (q : ℝ) / 2 ^ n ≤ ∑ χ ∈ Finset.univ.filter P, p.prob χ := by
    have hbadR' : (∑ χ ∈ Finset.univ.filter (fun χ => ¬ P χ), p.prob χ) ≤
        (q : ℝ) / 2 ^ n := by
      refine le_trans ?_ hbadR
      apply le_of_eq
      apply Finset.sum_congr
      · ext χ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
      · intro χ _
        rfl
    linarith
  have hbase : 0 ≤ 1 - (q : ℝ) / 2 ^ n := by
    have hr : (q : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hqn
    have hdiv : (q : ℝ) / 2 ^ n ≤ 1 := (div_le_one (by positivity)).mpr hr
    linarith
  exact pow_le_pow_left₀ hbase hg m

end Qatlib.Concepts.HspRecovery.Distinguisher
