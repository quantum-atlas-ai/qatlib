/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic

/-!
# Envelope rejection and linear-combination access models

`SQEnvelope` expresses positive target energy and pointwise squared-norm domination. The
proposal-and-coin model defines rejection records, a counted stopping rule, and acceptance-based
norm estimates; the linear-combination model constructs a square-root envelope and a joint
mixture proposal whose coordinate marginal samples that envelope. For background, see
[ChiaEtAl2022].

## Main statements

* `sq_rejection_envelope_single_trial`: computes the acceptance rate and accepted-coordinate
  mass.
* `sq_rejection_linear_combination_access`: establishes the combined envelope, its energy, the
  normalized mixture, and exact point-query count.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.SqEstimation.RejectionSample
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The target has positive squared norm and is pointwise dominated in squared complex norm by
the envelope. -/
def SQEnvelope {I : Type} [Fintype I] (u uh : I→ℂ) : Prop :=
  0< (∑ i, Complex.normSq (u i)) ∧ ∀ i, Complex.normSq (u i)≤ Complex.normSq (uh i)
/-- The coordinatewise ratio of target squared norm to envelope squared norm, using real
division. -/
noncomputable def sqRatio {I : Type} (u uh : I→ℂ) (i : I) : ℝ :=
  Complex.normSq (u i)/Complex.normSq (uh i)
/-- The joint probability of a proposal index and its conditional acceptance-coin outcome. -/
noncomputable def sqTrialMass {I : Type} [Fintype I]
    (p : FinDist I) (coin : I→FinDist Bool) (z : I×Bool) : ℝ :=
  p.prob z.1*(coin z.1).prob z.2
/-- The product of the single-trial masses along a finite proposal-and-coin record. -/
noncomputable def sqTrialProduct {I : Type} [Fintype I] {B : ℕ}
    (p : FinDist I) (coin : I→FinDist Bool) (ω : Fin B→I×Bool) : ℝ :=
  ∏ b, sqTrialMass p coin (ω b)
/-- Return the index of the first accepted pair in a list, or `none` if all are rejected,
charging four operations per inspected pair. -/
def sqRejectList {I : Type} : List (I×Bool)→Option I×ℕ
  | [] => (none,0)
  | z::zs => if z.2 then (some z.1,4) else
      let q:= sqRejectList zs; (q.1,q.2+4)
/-- Apply the counted first-acceptance rule to the list associated with a finite trial record. -/
def sqRejectRun {I : Type} {B : ℕ} (ω : Fin B→I×Bool) : Option I×ℕ :=
  sqRejectList (List.ofFn ω)
/-- Estimate squared norm by multiplying an envelope-energy scale by the median of `2 * r + 1`
block acceptance frequencies. -/
noncomputable def sqNormSquaredEstimate {I : Type} (d : ℝ) (r B : ℕ)
    (ω : Fin (2*r+1)→Fin B→I×Bool) : ℝ :=
  d*sortedBlockMedian r (fun j=> (∑ b, if (ω j b).2 then (1:ℝ) else 0)/(B:ℝ))
/-- The coordinate value of a finite complex linear combination of input vectors. -/
noncomputable def sqLinearValue {J I : Type} [Fintype J] (c : J→ℂ)
    (u : J→I→ℂ) (i : I) : ℂ := ∑ j, c j*u j i
/-- The real square-root envelope whose squared magnitude is the number of summands times the
sum of squared weighted envelope entries. -/
noncomputable def sqLinearEnvelope {J I : Type} [Fintype J] (c : J→ℂ)
    (uh : J→I→ℂ) (i : I) : ℂ :=
  (Real.sqrt ((Fintype.card J:ℝ)*∑ j,Complex.normSq (c j*uh j i)):ℂ)
/-- The joint component-and-coordinate proposal mass, proportional to the squared weighted
envelope entry and normalized by the total weighted envelope energy. -/
noncomputable def sqMixtureMass {J I : Type} [Fintype J] [Fintype I]
    (c : J→ℂ) (uh : J→I→ℂ) (z : J×I) : ℝ :=
  Complex.normSq (c z.1*uh z.1 z.2)/(∑ j,Complex.normSq (c j)*(∑ i, Complex.normSq ((uh j) i)))
/-- Evaluate a linear-combination coordinate by a finite summation fold, recording one query per
summand. -/
noncomputable def sqLinearQuery {J I : Type} [Fintype J] (c : J→ℂ)
    (u : J→I→ℂ) (i : I) : ℂ×ℕ :=
  (List.ofFn (fun j : Fin (Fintype.card J)=> (Fintype.equivFin J).symm j)).foldl
    (fun a j => (a.1+c j*u j i,a.2+1)) (0,0)

/-- A valid envelope has positive energy, and the target energy is bounded by the envelope
energy. -/
theorem sqEnvelope_energy {I : Type} [Fintype I] (u uh : I→ℂ) (h : SQEnvelope u uh) :
    0 < (∑ i,Complex.normSq (uh i)) ∧
    (∑ i,Complex.normSq (u i)) ≤ ∑ i,Complex.normSq (uh i) := by
  have he := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h.2 i)
  exact ⟨h.1.trans_le he,he⟩

/-- Under `SQEnvelope`, each target-to-envelope squared-norm ratio lies in the unit interval. -/
theorem sqRatio_range {I : Type} [Fintype I] (u uh : I→ℂ) (h : SQEnvelope u uh) (i : I) :
    0 ≤ sqRatio u uh i ∧ sqRatio u uh i ≤ 1 := by
  refine ⟨div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),?_⟩
  by_cases hz : Complex.normSq (uh i)=0
  · simp [sqRatio,hz]
  · exact (div_le_one (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hz))).mpr (h.2 i)

/-- Exact squared-envelope proposals and ratio acceptance coins yield accepted-coordinate mass
equal to target squared magnitude divided by total envelope energy. -/
theorem sqTrial_true_mass {I : Type} [Fintype I] (u uh : I→ℂ)
    (p : FinDist I) (coin : I→FinDist Bool) (h : SQEnvelope u uh)
    (hp : ∀ i,p.prob i=Complex.normSq (uh i)/(∑ i,Complex.normSq (uh i)))
    (hc : ∀ i,(coin i).prob true=sqRatio u uh i) (i : I) :
    sqTrialMass p coin (i,true)=Complex.normSq (u i)/(∑ i,Complex.normSq (uh i)) := by
  rw [sqTrialMass,hp,hc,sqRatio]
  by_cases hz : Complex.normSq (uh i)=0
  · have hu : Complex.normSq (u i)=0 := le_antisymm (by simpa [hz] using h.2 i) (Complex.normSq_nonneg _)
    simp [hz,hu]
  · field_simp

/-- For an exact envelope proposal and ratio coin, the envelope-to-target energy ratio is at
least one, each acceptance parameter lies in the unit interval, and the acceptance rate is
the reciprocal energy ratio. Accepted-coordinate masses are target squared magnitudes
divided by envelope energy, as in [Chia et al., Lemma 3.5][ChiaEtAl2022]. -/
theorem sq_rejection_envelope_single_trial : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (u uh : I→ℂ) (p : FinDist I) (coin : I→FinDist Bool),
    SQEnvelope u uh → (∀ i,p.prob i=Complex.normSq (uh i)/(∑ i,Complex.normSq (uh i))) →
    (∀ i,(coin i).prob true=sqRatio u uh i) →
    let φ := (∑ i,Complex.normSq (uh i))/(∑ i,Complex.normSq (u i));
    1≤φ ∧ (∀ i,0≤ sqRatio u uh i ∧ sqRatio u uh i≤1) ∧
    (∑ i,sqTrialMass p coin (i,true))=1/φ ∧
    (∀ i,sqTrialMass p coin (i,true)=Complex.normSq (u i)/(∑ i,Complex.normSq (uh i))) := by
  intro I _ _ u uh p coin h hp hc
  (try dsimp only)
  have he := sqEnvelope_energy u uh h
  refine ⟨(one_le_div h.1).mpr he.2,sqRatio_range u uh h,?_,sqTrial_true_mass u uh p coin h hp hc⟩
  simp_rw [sqTrial_true_mass u uh p coin h hp hc]
  rw [← Finset.sum_div]
  field_simp

/-- The finite joint distribution of a proposal index and its conditional Boolean coin outcome. -/
noncomputable def sqTrialLaw {I : Type} [Fintype I] (p : FinDist I) (coin : I→FinDist Bool) : FinDist (I×Bool) where
  prob := sqTrialMass p coin
  nonneg z := mul_nonneg (p.nonneg z.1) ((coin z.1).nonneg z.2)
  sum_one := by
    simp only [sqTrialMass,Fintype.sum_prod_type,← Finset.mul_sum,(coin _).sum_one,mul_one]
    exact p.sum_one

/-- The squared magnitude of the combined envelope is the number of components times the sum of
squared weighted envelope entries. -/
theorem sqLinearEnvelope_normSq {J I : Type} [Fintype J] (c : J→ℂ) (uh : J→I→ℂ) (i : I) :
    Complex.normSq (sqLinearEnvelope c uh i) =
      (Fintype.card J : ℝ)*∑ j,Complex.normSq (c j*uh j i) := by
  unfold sqLinearEnvelope
  rw [Complex.normSq_ofReal]
  simpa only [pow_two] using Real.sq_sqrt (show 0 ≤
    (Fintype.card J : ℝ)*∑ j,Complex.normSq (c j*uh j i) by
      exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)))

/-- If each input has a valid envelope, the combined square-root envelope pointwise dominates
the squared magnitude of their linear combination. -/
theorem sqLinearEnvelope_dominates {J I : Type} [Fintype J] [Fintype I]
    (c : J→ℂ) (u uh : J→I→ℂ) (h : ∀ j,SQEnvelope (u j) (uh j)) (i : I) :
    Complex.normSq (sqLinearValue c u i) ≤ Complex.normSq (sqLinearEnvelope c uh i) := by
  rw [sqLinearEnvelope_normSq,Complex.normSq_eq_norm_sq,sqLinearValue]
  have hn := norm_sum_le Finset.univ (fun j => c j*u j i)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖c j*u j i‖) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hc
  calc
    _ ≤ (∑ j,‖c j*u j i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (∑ j,‖c j*u j i‖^2)*(Fintype.card J : ℝ) := hc
    _ = (Fintype.card J : ℝ)*∑ j,Complex.normSq (c j)*Complex.normSq (u j i) := by
      simp_rw [← Complex.normSq_eq_norm_sq,Complex.normSq_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      rw [Complex.normSq_mul]
      exact mul_le_mul_of_nonneg_left ((h j).2 i) (Complex.normSq_nonneg _)

/-- A fold that adds one complex contribution and one count per entry returns the initial sum
plus all contributions and the initial count plus the list length. -/
theorem sq_linear_fold {J : Type} (f : J→ℂ) (l : List J) (a : ℂ×ℕ) :
    l.foldl (fun a j => (a.1+f j,a.2+1)) a = (a.1+(l.map f).sum,a.2+l.length) := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih => simp [ih,add_assoc,Nat.add_comm]

/-- The counted coordinate query equals the linear-combination value and uses exactly one query
per component. -/
theorem sqLinearQuery_value_count {J I : Type} [Fintype J] (c : J→ℂ) (u : J→I→ℂ) (i : I) :
    (sqLinearQuery c u i).1 = sqLinearValue c u i ∧ (sqLinearQuery c u i).2=Fintype.card J := by
  unfold sqLinearQuery
  rw [sq_linear_fold]
  simp only [zero_add,List.length_ofFn,List.map_ofFn,List.sum_ofFn]
  constructor
  · exact (Fintype.equivFin J).symm.sum_comp (fun j => c j*u j i)
  · trivial

/-- A nonzero linear combination of enveloped inputs has the specified dominating envelope and
weighted energy formula. The joint mixture is normalized, its coordinate marginal is the
squared-envelope law, and each point query uses exactly the number of components, giving the
closure interface of [Chia et al., Lemma 3.6][ChiaEtAl2022]. -/
theorem sq_rejection_linear_combination_access : ∀ (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (c : J→ℂ) (u uh : J→I→ℂ),
    (∀ j,SQEnvelope (u j) (uh j)) → 0 < (∑ i,Complex.normSq (sqLinearValue c u i)) →
    SQEnvelope (sqLinearValue c u) (sqLinearEnvelope c uh) ∧
    (∑ i,Complex.normSq (sqLinearEnvelope c uh i)) =
      (Fintype.card J : ℝ)*∑ j,Complex.normSq (c j)*(∑ i,Complex.normSq (uh j i)) ∧
    (∑ z : J×I,sqMixtureMass c uh z)=1 ∧
    (∀ i,(∑ j,sqMixtureMass c uh (j,i)) =
      Complex.normSq (sqLinearEnvelope c uh i)/(∑ i,Complex.normSq (sqLinearEnvelope c uh i))) ∧
    (∀ i,(sqLinearQuery c u i).1=sqLinearValue c u i ∧ (sqLinearQuery c u i).2=Fintype.card J) := by
  intro J I _ _ _ _ c u uh h hpos
  have hen : SQEnvelope (sqLinearValue c u) (sqLinearEnvelope c uh) :=
    ⟨hpos,sqLinearEnvelope_dominates c u uh h⟩
  have hm : (∑ i,Complex.normSq (sqLinearEnvelope c uh i)) =
      (Fintype.card J : ℝ)*∑ j,Complex.normSq (c j)*(∑ i,Complex.normSq (uh j i)) := by
    simp_rw [sqLinearEnvelope_normSq,Complex.normSq_mul]
    rw [← Finset.mul_sum,Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have hD : 0 < ∑ j,Complex.normSq (c j)*(∑ i,Complex.normSq (uh j i)) := by
    have hp := (sqEnvelope_energy _ _ hen).1
    rw [hm] at hp
    have hz : 0 ≤ ∑ j,Complex.normSq (c j)*(∑ i,Complex.normSq (uh j i)) := by
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (Complex.normSq_nonneg _)
        (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)))
    by_contra hh
    have hd : (∑ j,Complex.normSq (c j)*(∑ i,Complex.normSq (uh j i)))=0 := by linarith
    simp [hd] at hp
  have hcard : (Fintype.card J : ℝ) ≠ 0 := by
    have hp := (sqEnvelope_energy _ _ hen).1
    rw [hm] at hp
    intro hz
    simp [hz] at hp
  refine ⟨hen,hm,?_,?_,sqLinearQuery_value_count c u⟩
  · simp only [sqMixtureMass,Fintype.sum_prod_type,Complex.normSq_mul,← Finset.sum_div,← Finset.mul_sum]
    exact div_self (ne_of_gt hD)
  · intro i
    rw [hm,sqLinearEnvelope_normSq]
    simp only [sqMixtureMass,← Finset.sum_div]
    field_simp

end Qatlib.Concepts.SqEstimation.RejectionSample
