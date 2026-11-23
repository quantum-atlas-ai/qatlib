/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RectangularPureDistance

/-!
# Overlap bound for binary measurements on pure states

The necessity direction of [HoyerLeeSpalek2007], Theorem 3, follows by lifting
a binary POVM to basis readout. The two correct-outcome probability bounds
give a lower bound on total variation, which is bounded above by the pure-state
distance in the finite-dimensional Hilbert space. The measurement construction
for the reverse implication is outside this module.

See the [fixed preprint](https://arxiv.org/abs/quant-ph/0611054v2), §2.
-/

@[expose] public section

open scoped BigOperators Matrix
open Qatlib.Concepts.AdversaryBounds.AdvDuality (IsPovm povmProb povmLiftMatrix povmLift_gram povmLift_born outcomeEvent)
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.NegWeights06.MainResults

/-- The outcome probabilities of a binary POVM on a normalized pure state sum to one. -/
private theorem binary_povm_total {H : Type} [Fintype H] [DecidableEq H]
    (out : Bool → Matrix H H ℂ) (ho : IsPovm out) (w : QState H) (hw : Normalized w) :
    povmProb out false w + povmProb out true w = 1 := by
  have hsum : out false + out true = 1 := by
    ext i j
    have h := congrArg (fun M : Matrix H H ℂ => M i j) ho.2
    by_cases hij : i = j <;> simpa [Fintype.sum_bool, Matrix.one_apply, hij, add_comm] using h
  have hadd : (Inner w ((out false + out true) *ᵥ w)).re =
      povmProb out false w + povmProb out true w := by
    rw [Matrix.add_mulVec]
    simp only [povmProb, inner_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
  rw [hsum, Matrix.one_mulVec, (normalized_iff_inner_self w).mp hw, Complex.one_re] at hadd
  exact hadd.symm

/-- If one binary POVM distinguishes two unit pure states with error at most `ε` on each input,
their overlap magnitude is at most `2 * √(ε * (1 - ε))`, as in Theorem 3. -/
theorem pure_overlap_le_of_binary_povm_success {H : Type} [Fintype H] [DecidableEq H]
    (u v : QState H) (hu : Normalized u) (hv : Normalized v)
    (out : Bool → Matrix H H ℂ) (hout : IsPovm out) (ε : ℝ) (he₀ : 0 ≤ ε) (he₁ : ε ≤ 1 / 2)
    (huok : 1 - ε ≤ povmProb out true u) (hvok : 1 - ε ≤ povmProb out false v) :
    ‖Inner u v‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  let V := povmLiftMatrix out
  let p (b : Bool) (i : H) := BornProb (V *ᵥ u) (b, i)
  let q (b : Bool) (i : H) := BornProb (V *ᵥ v) (b, i)
  have hborn (w : QState H) (b : Bool) :
      ∑ i : H, BornProb (V *ᵥ w) (b, i) = povmProb out b w := by
    cases b with
    | false =>
      simpa [V, MeasureProb, outcomeEvent, Finset.sum_filter, Fintype.sum_prod_type] using
        povmLift_born out hout w false
    | true =>
      simpa [V, MeasureProb, outcomeEvent, Finset.sum_filter, Fintype.sum_prod_type] using
        povmLift_born out hout w true
  have htrue : 1 - 2 * ε ≤ ∑ i, |p true i - q true i| := by
    calc
      1 - 2 * ε ≤ povmProb out true u - povmProb out true v := by
        linarith [binary_povm_total out hout v hv]
      _ = ∑ i, (p true i - q true i) := by
        rw [Finset.sum_sub_distrib, hborn u true, hborn v true]
      _ ≤ _ := le_trans (le_abs_self _) (Finset.abs_sum_le_sum_abs _ _)
  have hfalse : 1 - 2 * ε ≤ ∑ i, |p false i - q false i| := by
    calc
      1 - 2 * ε ≤ povmProb out false v - povmProb out false u := by
        linarith [binary_povm_total out hout u hu]
      _ = ∑ i, (q false i - p false i) := by
        rw [Finset.sum_sub_distrib, hborn v false, hborn u false]
      _ ≤ ∑ i, |q false i - p false i| := le_trans (le_abs_self _) (Finset.abs_sum_le_sum_abs _ _)
      _ = _ := Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  have hnu := (normalized_iff_norm_toEuclidean_fromVec u).mp hu
  have hnv := (normalized_iff_norm_toEuclidean_fromVec v).mp hv
  have htv :=
    Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.rectangular_born_tv_le_sqrt_fidelity
      V (povmLift_gram out hout) (toEuclidean_fromVec u) (toEuclidean_fromVec v) hnu hnv
  rw [inner_euclidean_fromVec, Fintype.sum_prod_type, Fintype.sum_bool] at htv
  change (1 / 2 : ℝ) * ((∑ i, |p _ i - q _ i|) + (∑ i, |p _ i - q _ i|)) ≤ _ at htv
  have hdist : 1 - 2 * ε ≤ Real.sqrt (1 - ‖Inner u v‖ ^ 2) := by linarith
  have hoverlap : ‖Inner u v‖ ≤ 1 := by
    calc
      ‖Inner u v‖ = ‖inner ℂ (toEuclidean_fromVec u) (toEuclidean_fromVec v)‖ := by
        rw [inner_euclidean_fromVec]
      _ ≤ ‖toEuclidean_fromVec u‖ * ‖toEuclidean_fromVec v‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hnu, hnv, one_mul]
  have hdom : 0 ≤ 1 - ‖Inner u v‖ ^ 2 := by nlinarith [norm_nonneg (Inner u v)]
  have hs : (1 - 2 * ε) ^ 2 ≤ (Real.sqrt (1 - ‖Inner u v‖ ^ 2)) ^ 2 :=
    (sq_le_sq₀ (by linarith) (Real.sqrt_nonneg _)).mpr hdist
  rw [Real.sq_sqrt hdom] at hs
  have he : 0 ≤ ε * (1 - ε) := mul_nonneg he₀ (by linarith)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt he]
  nlinarith

end Qatlib.Papers.NegWeights06.MainResults
