/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Qatlib.Concepts.MonteCarloMean.LayeredMean.LayeredQuantumMean
import Qatlib.Concepts.SketchArith.TransposeAccess.FinDistTransport
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian

/-!
# Signed and relative quantum mean estimation

`signedMeanLaw` samples a center and estimates the positive and negative centered payoffs with
layer circuits. The module proves additive error and fresh median guarantees under a variance
bound, a relative error guarantee using a sampled scale, and explicit preparation, measurement,
query, and gate ledgers for these programs. See [Montanaro2015] for background.

## Main statements

* `signed_centered_same_program_mean_guarantee`: For `k ≥ 4`, positive `σ`, and variance at most
  `σ^2`, the signed estimator has error at most `8 * σ * (1 / 2)^k` with probability at least `2
  / 3`. See [Montanaro2015].
* `relative_variance_actual_conditional_estimator`: For nonnegative payoff, positive mean, and
  variance at most `B` times the squared mean, the conditional estimator attains the stated
  relative error with probability at least `2 / 3` when `B ≥ 1` and `k ≥ 4`. See
  [Montanaro2015].
* `signed_centered_full_resources`: The signed estimator uses one source preparation and `2 * q`
  layer copies, with all measurement, forward, inverse, query, and gate counts given by the
  displayed resource record.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Matrix
open scoped Classical BigOperators
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- The record of repeated amplitude estimation outcomes for the `k + 2` payoff layers at the
grid and repetition counts specified by `k`. -/
abbrev LayerRecord (k : ℕ) := Fin (k+2) → Fin (2*layerRepetitions k+1) → Fin (layerGrid k)

/-- The positive part of the centered payoff `(f i - f x) / (4 * σ)`. -/
noncomputable def centerPositive {I : Type} (f : I → ℝ) (σ : ℝ) (x i : I) : ℝ :=
  max ((f i-f x)/(4*σ)) 0

/-- The positive part of the oppositely centered payoff `(f x - f i) / (4 * σ)`. -/
noncomputable def centerNegative {I : Type} (f : I → ℝ) (σ : ℝ) (x i : I) : ℝ :=
  max ((f x-f i)/(4*σ)) 0

/-- The finite Born distribution obtained by preparing `A *ᵥ Ket j` with unitary `A`. -/
noncomputable def signedMeanSource {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) : FinDist I where
  prob i := BornProb (ApplyGate A (Ket j)) i
  nonneg _ := bornProb_nonneg _ _
  sum_one := bornProb_sum_eq_one (normalized_applyGate hA (normalized_ket j))

/-- The joint law of a Born sampled center and two conditionally independent layer records for
its positive and negative centered payoffs. -/
noncomputable def signedMeanLaw {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (σ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : FinDist (I × (LayerRecord k × LayerRecord k)) where
  prob ω := (signedMeanSource A j hA).prob ω.1 *
    (layerLaw k A j (centerPositive f σ ω.1) hA (fun _ => le_max_right _ _)).prob ω.2.1 *
    (layerLaw k A j (centerNegative f σ ω.1) hA (fun _ => le_max_right _ _)).prob ω.2.2
  nonneg ω := mul_nonneg
    (mul_nonneg ((signedMeanSource A j hA).nonneg _)
      ((layerLaw k A j (centerPositive f σ ω.1) hA (fun _ => le_max_right _ _)).nonneg _))
    ((layerLaw k A j (centerNegative f σ ω.1) hA (fun _ => le_max_right _ _)).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ x, (signedMeanSource A j hA).prob x := by
        apply Finset.sum_congr rfl
        intro x _
        let P := layerLaw k A j (centerPositive f σ x) hA (fun _ => le_max_right _ _)
        let N := layerLaw k A j (centerNegative f σ x) hA (fun _ => le_max_right _ _)
        change (∑ u, ∑ v, (signedMeanSource A j hA).prob x * P.prob u * N.prob v) = _
        calc
          _ = (signedMeanSource A j hA).prob x * ((∑ u, P.prob u)*(∑ v, N.prob v)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
          _ = _ := by rw [P.sum_one, N.sum_one]; ring
      _ = 1 := (signedMeanSource A j hA).sum_one

/-- The signed mean estimate obtained by adding `4 * σ` times the difference of the two layer
estimates to the sampled center value. -/
noncomputable def signedMeanEstimate {I : Type} (k : ℕ) (f : I → ℝ) (σ : ℝ)
    (ω : I × (LayerRecord k × LayerRecord k)) : ℝ :=
  f ω.1 + 4*σ*(layerEstimate k ω.2.1-layerEstimate k ω.2.2)

/-- The sorted median of `2 * r + 1` signed mean estimates. -/
noncomputable def signedMeanMedian {I : Type} (k r : ℕ) (f : I → ℝ) (σ : ℝ)
    (ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k)) : ℝ :=
  sortedBlockMedian r (fun i => signedMeanEstimate k f σ (ω i))

/-- The joint signed estimator probability factors into the Born probability of the center and
the two conditional layer record probabilities. See [Montanaro2015]. -/
theorem signed_centered_actual_joint_law (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (σ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (x : I) (u v : LayerRecord k) :
    (signedMeanLaw k A j f σ hA).prob (x,(u,v)) = BornProb (ApplyGate A (Ket j)) x *
      (layerLaw k A j (centerPositive f σ x) hA (fun _ => le_max_right _ _)).prob u *
      (layerLaw k A j (centerNegative f σ x) hA (fun _ => le_max_right _ _)).prob v := rfl

/-- The sample average of `f` over the `32 * B` seed observations. -/
noncomputable def relativeMeanCenter {I : Type} (B : ℕ) (f : I → ℝ)
    (ω : Fin (32*B) → I) : ℝ := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f ω

/-- The relative estimator scale `2 * sqrt (B + 1)` times the seed sample average. -/
noncomputable def relativeMeanScale {I : Type} (B : ℕ) (f : I → ℝ)
    (ω : Fin (32*B) → I) : ℝ := 2*Real.sqrt (B+1 : ℝ)*relativeMeanCenter B f ω

/-- The payoff normalized by the scale computed from the seed record. -/
noncomputable def relativeMeanPayoff {I : Type} (B : ℕ) (f : I → ℝ)
    (ω : Fin (32*B) → I) (i : I) : ℝ := f i/relativeMeanScale B f ω

/-- A pointwise nonnegative payoff remains nonnegative after division by the seed based relative
mean scale. -/
theorem relativeMeanPayoff_nonneg {I : Type} (B : ℕ) (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (ω : Fin (32*B) → I) : ∀ i, 0 ≤ relativeMeanPayoff B f ω i := by
  have hc : 0 ≤ relativeMeanCenter B f ω := by
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => hf _)) (Nat.cast_nonneg _)
  intro i
  exact div_nonneg (hf i) (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hc)

/-- The joint law of `32 * B` independent source samples and a conditional layer record for the
payoff normalized by their computed scale. -/
noncomputable def relativeMeanLaw {I : Type} [Fintype I] [DecidableEq I]
    (B k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) :
    FinDist ((Fin (32*B) → I) × LayerRecord k) where
  prob ω := (signedMeanSource A j hA).probOf ω.1 *
    (layerLaw k A j (relativeMeanPayoff B f ω.1) hA (relativeMeanPayoff_nonneg B f hf ω.1)).prob ω.2
  nonneg ω := mul_nonneg (Finset.prod_nonneg (fun _ _ => (signedMeanSource A j hA).nonneg _))
    ((layerLaw k A j (relativeMeanPayoff B f ω.1) hA
      (relativeMeanPayoff_nonneg B f hf ω.1)).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ ω, (signedMeanSource A j hA).probOf ω := by
        apply Finset.sum_congr rfl
        intro ω _
        let P := layerLaw k A j (relativeMeanPayoff B f ω) hA (relativeMeanPayoff_nonneg B f hf ω)
        change (∑ u, (signedMeanSource A j hA).probOf ω * P.prob u) = _
        rw [← Finset.mul_sum, P.sum_one, mul_one]
      _ = 1 := (signedMeanSource A j hA).sum_probOf (32*B)

/-- The relative mean estimate obtained by multiplying the conditional layer estimate by the
seed based scale. -/
noncomputable def relativeMeanEstimate {I : Type} (B k : ℕ) (f : I → ℝ)
    (ω : (Fin (32*B) → I) × LayerRecord k) : ℝ :=
  relativeMeanScale B f ω.1 * layerEstimate k ω.2

namespace SignedMean
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The total probability mass of a predicate under a finite distribution. -/
noncomputable def mass (p : FinDist I) (E : I → Prop) : ℝ := ∑ x with E x, p.prob x

/-- The masses of a predicate and its complement sum to one. -/
theorem mass_complement (p : FinDist I) (E : I → Prop) :
    mass p E + mass p (fun x => ¬E x)=1 := by
  unfold mass
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  calc
    _ = ∑ x, p.prob x := Finset.sum_congr rfl (fun x _ => by by_cases hx : E x <;> simp [hx])
    _ = 1 := p.sum_one

/-- Probability mass is monotone under inclusion of predicates. -/
theorem mass_mono (p : FinDist I) {E F : I → Prop} (h : ∀ x, E x → F x) :
    mass p E ≤ mass p F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩
  · intro x _ _
    exact p.nonneg x

/-- The second moment about `c` is the variance plus the squared difference between the mean and
`c`. -/
theorem shifted_second_moment (p : FinDist I) (f : I → ℝ) (c : ℝ) :
    (∑ i, p.prob i*(f i-c)^2) = p.variance f + (p.expect f-c)^2 := by
  have he (i : I) : p.prob i*(f i-c)^2 =
      p.prob i*(f i-p.expect f)^2 +
        2*(p.expect f-c)*(p.prob i*(f i-p.expect f)) + (p.expect f-c)^2*p.prob i := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_sub_mean, p.sum_one]
  simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance,
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect]

/-- For positive `ε`, the mass where `f` differs from its mean by more than `ε` is at most its
variance divided by `ε^2`. -/
theorem chebyshev (p : FinDist I) (f : I → ℝ) (ε : ℝ) (hε : 0 < ε) :
    mass p (fun x => ε < |f x-p.expect f|) ≤ p.variance f/ε^2 :=
  ProbabilityInterfaces.chebyshev_strict p f ε hε

/-- For two conditionally independent records, the mass of the three specified events factors
into a sum of the center weight times the two conditional event masses. -/
theorem conditional_two_event {J K : Type} [Fintype J] [Fintype K]
    (p : FinDist I) (q : I → FinDist J) (z : I → FinDist K)
    (E : I → Prop) (F : I → J → Prop) (G : I → K → Prop) :
    (∑ ω : I × (J × K) with E ω.1 ∧ F ω.1 ω.2.1 ∧ G ω.1 ω.2.2,
      p.prob ω.1*(q ω.1).prob ω.2.1*(z ω.1).prob ω.2.2) =
      ∑ x with E x, p.prob x * (mass (q x) (F x)*mass (z x) (G x)) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x
  · rw [if_pos hx]
    unfold mass
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hu : F x u <;> by_cases hv : G x v <;> simp [hx, hu, hv, mul_assoc]
  · simp [hx]

/-- A nonnegative function bounded below by nonnegative `t` on an event of mass at least `s` has
expectation at least `s * t`. -/
theorem conditional_lower (p : FinDist I) (E : I → Prop) (v : I → ℝ)
    (s t : ℝ) (ht : 0 ≤ t) (hv : ∀ x, 0 ≤ v x)
    (hE : s ≤ mass p E) (hgood : ∀ x, E x → t ≤ v x) :
    s*t ≤ ∑ x, p.prob x*v x := by
  calc
    _ ≤ mass p E*t := mul_le_mul_of_nonneg_right hE ht
    _ = ∑ x with E x, p.prob x*t := Finset.sum_mul _ _ _
    _ ≤ ∑ x with E x, p.prob x*v x := Finset.sum_le_sum
      (fun x hx => mul_le_mul_of_nonneg_left (hgood x (Finset.mem_filter.mp hx).2) (p.nonneg x))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => mul_nonneg (p.nonneg x) (hv x))

/-- The mass of every predicate under a finite distribution is nonnegative. -/
theorem mass_nonneg (p : FinDist I) (E : I → Prop) : 0 ≤ mass p E :=
  Finset.sum_nonneg (fun x _ => p.nonneg x)

/-- The weighted sum of a function over an event of mass at least `s` is at least `s * t` when
the function is at least nonnegative `t` on that event. -/
theorem conditional_good_lower (p : FinDist I) (E : I → Prop) (v : I → ℝ)
    (s t : ℝ) (ht : 0 ≤ t)
    (hE : s ≤ mass p E) (hgood : ∀ x, E x → t ≤ v x) :
    s*t ≤ ∑ x with E x, p.prob x*v x := by
  calc
    _ ≤ mass p E*t := mul_le_mul_of_nonneg_right hE ht
    _ = ∑ x with E x, p.prob x*t := Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum
      (fun x hx => mul_le_mul_of_nonneg_left (hgood x (Finset.mem_filter.mp hx).2) (p.nonneg x))

/-- If an estimate has failure mass at most `1 / 3`, the sorted median of `2 * r + 1`
independent estimates has failure probability at most `(8 / 9)^r`. See
[BrassardHoyerTapp1998Counting]. -/
theorem sorted_median_failure (p : FinDist I) (v : I → ℝ) (r : ℕ) (μ ε : ℝ)
    (hε : 0 ≤ ε) (hb : mass p (fun x => ε < |v x-μ|) ≤ 1/3) :
    p.probEvent (fun ω : Fin (2*r+1) → I =>
      ε < |sortedBlockMedian r (fun k => v (ω k))-μ|) ≤ (8/9 : ℝ)^r := by
  let B := fun x => ε < |v x-μ|
  let w := fun x => if B x then (2 : ℝ) else 1
  have hw : (∑ x, p.prob x*w x)=1+mass p B := by
    have he (x : I) : p.prob x*w x=p.prob x+(if B x then p.prob x else 0) := by
      dsimp [w]
      by_cases hx : B x <;> simp [hx, mul_two]
    simp_rw [he]
    rw [Finset.sum_add_distrib, p.sum_one, ← Finset.sum_filter]
    rfl
  have hmoment : (∑ ω : Fin (2*r+1) → I, p.probOf ω*∏ k, w (ω k)) ≤ (4/3 : ℝ)^(2*r+1) := by
    rw [p.expect_prod (fun _ x => w x)]
    simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    apply pow_le_pow_left₀
    · exact add_nonneg (by norm_num) (mass_nonneg p B)
    · linarith
  have hbound : (2 : ℝ)^(r+1)*p.probEvent (fun ω : Fin (2*r+1) → I =>
      ε < |sortedBlockMedian r (fun k => v (ω k))-μ|) ≤
      ∑ ω : Fin (2*r+1) → I, p.probOf ω*∏ k, w (ω k) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ ω with ε < |sortedBlockMedian r (fun k => v (ω k))-μ|,
          p.probOf ω*∏ k, w (ω k) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hh := heterogeneous_sorted_median_majority_witness r (fun k => v (ω k)) μ ε hε
          (Finset.mem_filter.mp hω).2
        have he : (∏ k, w (ω k)) = (2 : ℝ)^(Finset.univ.filter (fun k => B (ω k))).card := by
          simp [w, Finset.prod_ite]
        have hp : 0 ≤ p.probOf ω := Finset.prod_nonneg (fun _ _ => p.nonneg _)
        rw [he, mul_comm ((2 : ℝ)^(r+1))]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hh) hp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω _ _ => mul_nonneg (Finset.prod_nonneg (fun _ _ => p.nonneg _))
          (Finset.prod_nonneg (fun _ _ => by dsimp [w]; split_ifs <;> norm_num)))
  have he : (4/3 : ℝ)^(2*r+1)/(2 : ℝ)^(r+1)=(2/3 : ℝ)*(8/9 : ℝ)^r := by
    rw [pow_succ, pow_succ, pow_mul]
    rw [show (4/3 : ℝ)^2=(8/9 : ℝ)*2 from by norm_num, mul_pow]
    field_simp
    ring
  calc
    _ ≤ (4/3 : ℝ)^(2*r+1)/(2 : ℝ)^(r+1) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using! hbound.trans hmoment)
    _ = _ := he
    _ ≤ (8/9 : ℝ)^r := by
      have hp : 0 ≤ (8/9 : ℝ)^r := by positivity
      nlinarith

/-- The mass of a source event and a conditional record event is the source weighted sum of the
conditional event masses. -/
theorem conditional_one_event {J : Type} [Fintype J]
    (p : FinDist I) (q : I → FinDist J) (E : I → Prop) (F : I → J → Prop) :
    (∑ ω : I × J with E ω.1 ∧ F ω.1 ω.2, p.prob ω.1*(q ω.1).prob ω.2) =
      ∑ x with E x, p.prob x*mass (q x) (F x) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x
  · rw [if_pos hx]
    unfold mass
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : F x u <;> simp [hx, hu]
  · simp [hx]
end SignedMean

/-- Under variance at most positive `σ^2`, a sampled center lies within `3 * σ` of the mean with
mass at least `8 / 9`, and each normalized centered payoff then has second moment at most
one. See [Montanaro2015]. -/
theorem signed_center_good_mass_and_second_moments (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (σ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hσ : 0 < σ) :
    let p := fun i => BornProb (ApplyGate A (Ket j)) i
    let μ := ∑ i, p i*f i
    (∑ i, p i*(f i-μ)^2) ≤ σ^2 →
      (∑ x with |f x-μ| ≤ 3*σ, p x) ≥ 8/9 ∧
      ∀ x, |f x-μ| ≤ 3*σ →
        (∑ i, p i*(centerPositive f σ x i)^2) ≤ 1 ∧
        (∑ i, p i*(centerNegative f σ x i)^2) ≤ 1 := by
  (try dsimp only)
  let p := signedMeanSource A j hA
  change p.variance f ≤ σ^2 →
    SignedMean.mass p (fun x => |f x-p.expect f| ≤ 3*σ) ≥ 8/9 ∧
    ∀ x, |f x-p.expect f| ≤ 3*σ →
      (∑ i, p.prob i*(centerPositive f σ x i)^2) ≤ 1 ∧
      (∑ i, p.prob i*(centerNegative f σ x i)^2) ≤ 1
  intro hv
  have hσ2 : 0 < σ^2 := by positivity
  constructor
  · have hb := SignedMean.chebyshev p f (3*σ) (by positivity)
    have hb' : SignedMean.mass p (fun x => 3*σ < |f x-p.expect f|) ≤ 1/9 := by
      calc
        _ ≤ p.variance f/(3*σ)^2 := hb
        _ ≤ σ^2/(3*σ)^2 := div_le_div_of_nonneg_right hv (by positivity)
        _ = 1/9 := by field_simp; ring
    have hc := SignedMean.mass_complement p (fun x => |f x-p.expect f| ≤ 3*σ)
    simp only [not_le] at hc
    linarith
  · intro x hx
    have hs : (∑ i, p.prob i*(f i-f x)^2) ≤ 10*σ^2 := by
      rw [SignedMean.shifted_second_moment]
      have hx2 : (p.expect f-f x)^2 ≤ 9*σ^2 := by
        have hh := mul_self_le_mul_self (abs_nonneg _) hx
        nlinarith [sq_abs (f x-p.expect f)]
      linarith
    have hscale : (∑ i, p.prob i*((f i-f x)/(4*σ))^2) ≤ 1 := by
      have he : (∑ i, p.prob i*((f i-f x)/(4*σ))^2) =
          (∑ i, p.prob i*(f i-f x)^2)/(4*σ)^2 := by
        simp only [div_pow, mul_div_assoc, Finset.sum_div]
      rw [he]
      apply (div_le_one (by positivity : (0 : ℝ) < (4*σ)^2)).mpr
      nlinarith
    constructor
    · refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hscale
      apply mul_le_mul_of_nonneg_left _ (p.nonneg i)
      unfold centerPositive
      by_cases hi : 0 ≤ (f i-f x)/(4*σ)
      · rw [max_eq_left hi]
      · rw [max_eq_right (le_of_not_ge hi)]
        simpa only [zero_pow (by decide : 2 ≠ 0)] using! sq_nonneg ((f i-f x)/(4*σ))
    · refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hscale
      apply mul_le_mul_of_nonneg_left _ (p.nonneg i)
      unfold centerNegative
      have he : (f x-f i)/(4*σ) = -((f i-f x)/(4*σ)) := by ring
      rw [he]
      by_cases hi : 0 ≤ -((f i-f x)/(4*σ))
      · rw [max_eq_left hi, neg_sq]
      · rw [max_eq_right (le_of_not_ge hi)]
        simpa only [zero_pow (by decide : 2 ≠ 0)] using! sq_nonneg ((f i-f x)/(4*σ))

/-- The positive and negative layer circuit families together use exactly `2 * q * (layerGrid k
- 1)` queries, where `q = (k + 2) * (2 * layerRepetitions k + 1)`. See [Montanaro2015]. -/
theorem signed_centered_actual_access_ledger (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j x : I) (f : I → ℝ) (σ : ℝ) :
    let q := (k+2)*(2*layerRepetitions k+1)
    (∑ b : Bool, ∑ l : Fin (k+2), ∑ _ : Fin (2*layerRepetitions k+1),
      QueryCount (countedAECircuit (layerGrid k)
        (payoffPreparation A (layerPayoff (if b then centerPositive f σ x else centerNegative f σ x) l.val))
        (j,false))) = 2*q*(layerGrid k-1) := by
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [layered_quantum_mean_actual_query_ledger, layered_quantum_mean_actual_query_ledger]
  ring

/-- The difference of the positive and negative centered payoffs equals `(f i - f x) / (4 * σ)`. -/
theorem signed_center_difference {I : Type} (f : I → ℝ) (σ : ℝ) (x i : I) :
    centerPositive f σ x i-centerNegative f σ x i=(f i-f x)/(4*σ) := by
  unfold centerPositive centerNegative
  have he : (f x-f i)/(4*σ) = -((f i-f x)/(4*σ)) := by ring
  rw [he]
  by_cases hh : 0 ≤ (f i-f x)/(4*σ)
  · rw [max_eq_left hh, max_eq_right (neg_nonpos.mpr hh), sub_zero]
  · have hn := le_of_not_ge hh
    rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
    ring

/-- For positive `σ`, recombining the exact centered payoff expectations recovers the original
mean. -/
theorem signed_center_expectation {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℝ) (σ : ℝ) (x : I) (hσ : 0 < σ) :
    f x+4*σ*(p.expect (centerPositive f σ x)-p.expect (centerNegative f σ x))=p.expect f := by
  have he : p.expect (centerPositive f σ x)-p.expect (centerNegative f σ x) =
      (p.expect f-f x)/(4*σ) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, signed_center_difference, ← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, p.sum_one, one_mul]
  rw [he]
  field_simp
  ring

/-- If both centered layer estimates have error at most `ε`, the reconstructed signed mean has
error at most `8 * σ * ε`. -/
theorem signed_center_record_error {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (k : ℕ) (f : I → ℝ) (σ ε : ℝ) (x : I) (u v : LayerRecord k)
    (hσ : 0 < σ)
    (hu : |layerEstimate k u-p.expect (centerPositive f σ x)| ≤ ε)
    (hv : |layerEstimate k v-p.expect (centerNegative f σ x)| ≤ ε) :
    |signedMeanEstimate k f σ (x,(u,v))-p.expect f| ≤ 8*σ*ε := by
  have he : signedMeanEstimate k f σ (x,(u,v))-p.expect f =
      4*σ*((layerEstimate k u-p.expect (centerPositive f σ x))-
        (layerEstimate k v-p.expect (centerNegative f σ x))) := by
    rw [← signed_center_expectation p f σ x hσ]
    unfold signedMeanEstimate
    ring
  rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4*σ)]
  have hh : |(layerEstimate k u-p.expect (centerPositive f σ x))-
      (layerEstimate k v-p.expect (centerNegative f σ x))| ≤ 2*ε := by
    have ht := abs_sub_le (layerEstimate k u-p.expect (centerPositive f σ x)) 0
      (layerEstimate k v-p.expect (centerNegative f σ x))
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

/-- For `k ≥ 4`, positive `σ`, and variance at most `σ^2`, the signed estimator has error at
most `8 * σ * (1 / 2)^k` with probability at least `2 / 3`. See [Montanaro2015]. -/
theorem signed_centered_same_program_mean_guarantee (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (σ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hk : 4 ≤ k) (hσ : 0 < σ) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i*f i
    (∑ i, BornProb (ApplyGate A (Ket j)) i*(f i-μ)^2) ≤ σ^2 →
    (∑ ω with |signedMeanEstimate k f σ ω-μ| ≤ 8*σ*(1/2 : ℝ)^k,
      (signedMeanLaw k A j f σ hA).prob ω) ≥ 2/3 := by
  let p := signedMeanSource A j hA
  let ε := (1/2 : ℝ)^k
  let E := fun x => |f x-p.expect f| ≤ 3*σ
  let P := fun x => layerLaw k A j (centerPositive f σ x) hA (fun _ => le_max_right _ _)
  let N := fun x => layerLaw k A j (centerNegative f σ x) hA (fun _ => le_max_right _ _)
  let F := fun x u => |layerEstimate k u-p.expect (centerPositive f σ x)| ≤ ε
  let G := fun x v => |layerEstimate k v-p.expect (centerNegative f σ x)| ≤ ε
  change p.variance f ≤ σ^2 →
    (∑ ω with |signedMeanEstimate k f σ ω-p.expect f| ≤ 8*σ*ε,
      (signedMeanLaw k A j f σ hA).prob ω) ≥ 2/3
  intro hv
  have hc := signed_center_good_mass_and_second_moments I A j f σ hA hσ hv
  have hε : ε ≤ 1/16 := by
    calc
      _ ≤ (1/2 : ℝ)^4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = _ := by norm_num
  have hP (x : I) (hx : E x) : 15/16 ≤ SignedMean.mass (P x) (F x) := by
    have hh := layered_quantum_mean_actual_guarantee k (by omega) A j (centerPositive f σ x)
      hA (fun _ => le_max_right _ _) (hc.2 x hx).1
    have hh' : 1-ε ≤ SignedMean.mass (P x) (F x) := by
      simpa only [SignedMean.mass, neg_pow_half_eq] using! hh
    linarith
  have hN (x : I) (hx : E x) : 15/16 ≤ SignedMean.mass (N x) (G x) := by
    have hh := layered_quantum_mean_actual_guarantee k (by omega) A j (centerNegative f σ x)
      hA (fun _ => le_max_right _ _) (hc.2 x hx).2
    have hh' : 1-ε ≤ SignedMean.mass (N x) (G x) := by
      simpa only [SignedMean.mass, neg_pow_half_eq] using! hh
    linarith
  have hl : (8/9 : ℝ)*(15/16)^2 ≤
      ∑ x with E x, p.prob x*(SignedMean.mass (P x) (F x)*SignedMean.mass (N x) (G x)) := by
    apply SignedMean.conditional_good_lower p E _ (8/9) ((15/16)^2) (by norm_num) hc.1
    intro x hx
    have hp := SignedMean.mass_nonneg (P x) (F x)
    have hn := SignedMean.mass_nonneg (N x) (G x)
    nlinarith [hP x hx, hN x hx,
      mul_nonneg (sub_nonneg.mpr (hP x hx)) (sub_nonneg.mpr (hN x hx))]
  have hm := SignedMean.conditional_two_event p P N E F G
  have hi : (∑ ω : I × (LayerRecord k × LayerRecord k) with E ω.1 ∧ F ω.1 ω.2.1 ∧ G ω.1 ω.2.2,
      (signedMeanLaw k A j f σ hA).prob ω) ≤
      ∑ ω with |signedMeanEstimate k f σ ω-p.expect f| ≤ 8*σ*ε,
        (signedMeanLaw k A j f σ hA).prob ω := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      obtain ⟨_, _, hu, hw⟩ := Finset.mem_filter.mp hω
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        signed_center_record_error p k f σ ε ω.1 ω.2.1 ω.2.2 hσ hu hw⟩
    · intro ω _ _
      exact (signedMeanLaw k A j f σ hA).nonneg ω
  have hl' : (8/9 : ℝ)*(15/16)^2 ≤
      ∑ ω with E ω.1 ∧ F ω.1 ω.2.1 ∧ G ω.1 ω.2.2,
        (signedMeanLaw k A j f σ hA).prob ω := by
    exact hm.symm ▸ hl
  exact (by norm_num : (2/3 : ℝ) ≤ (8/9)*(15/16)^2).trans (hl'.trans hi)

/-- Under the signed estimator variance and parameter hypotheses, the median of `2 * r + 1`
fresh estimates exceeds error `8 * σ * (1 / 2)^k` with probability at most `(8 / 9)^r`. -/
theorem signed_centered_fresh_median_failure (I : Type) [Fintype I] [DecidableEq I]
    (k r : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (σ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hk : 4 ≤ k) (hσ : 0 < σ) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i*f i
    (∑ i, BornProb (ApplyGate A (Ket j)) i*(f i-μ)^2) ≤ σ^2 →
    (signedMeanLaw k A j f σ hA).probEvent
      (fun ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
        8*σ*(1/2 : ℝ)^k < |signedMeanMedian k r f σ ω-μ|) ≤ (8/9 : ℝ)^r := by
  (try dsimp only)
  intro hv
  have hg := signed_centered_same_program_mean_guarantee I k A j f σ hA hk hσ hv
  have hc := SignedMean.mass_complement (signedMeanLaw k A j f σ hA)
    (fun ω => |signedMeanEstimate k f σ ω-(∑ i, BornProb (ApplyGate A (Ket j)) i*f i)| ≤
      8*σ*(1/2 : ℝ)^k)
  simp only [not_le] at hc
  apply SignedMean.sorted_median_failure _ (signedMeanEstimate k f σ) r _ _ (by positivity)
  change SignedMean.mass _ _ ≤ 1/3
  change 2/3 ≤ SignedMean.mass _ _ at hg
  linarith

/-- The independent source sampling law for the `32 * B` observations used to choose the
relative mean scale. -/
noncomputable def relativeMeanSeedLaw {I : Type} [Fintype I] [DecidableEq I]
    (B : ℕ) (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    FinDist (Fin (32*B) → I) :=
  independentSampleLaw (fun _ => signedMeanSource A j hA)

/-- For positive mean and variance at most `B` times its square, the seed average is within half
the mean with probability at least `7 / 8` when `B ≥ 1`. -/
theorem relativeMean_seed_good {I : Type} [Fintype I] [DecidableEq I]
    (B : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hB : 1 ≤ B) (hμ : 0 < (signedMeanSource A j hA).expect f)
    (hv : (signedMeanSource A j hA).variance f ≤ (B : ℝ)*((signedMeanSource A j hA).expect f)^2) :
    SignedMean.mass (relativeMeanSeedLaw B A j hA)
      (fun ω => |relativeMeanCenter B f ω-(signedMeanSource A j hA).expect f| ≤
        (signedMeanSource A j hA).expect f/2) ≥ 7/8 := by
  let p := signedMeanSource A j hA
  have hBR : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hb := p.chebyshev_avg (L := 32*B) f (by omega) (p.expect f/2) (by positivity)
  have hb' : SignedMean.mass (relativeMeanSeedLaw B A j hA)
      (fun ω => p.expect f/2 < |relativeMeanCenter B f ω-p.expect f|) ≤ 1/8 := by
    calc
      _ ≤ p.variance f/((32*B : ℕ)*(p.expect f/2)^2) := hb
      _ ≤ (B : ℝ)*(p.expect f)^2/((32*B : ℕ)*(p.expect f/2)^2) :=
        div_le_div_of_nonneg_right hv (by positivity)
      _ = 1/8 := by
        have hm0 : p.expect f ≠ 0 := ne_of_gt hμ
        push_cast
        field_simp [hm0, ne_of_gt hBR]
        norm_num
  have hc := SignedMean.mass_complement (relativeMeanSeedLaw B A j hA)
    (fun ω => |relativeMeanCenter B f ω-p.expect f| ≤ p.expect f/2)
  simp only [not_le] at hc
  linarith

/-- A seed average within half a positive mean gives a positive scale at most `3 * sqrt (B + 1)`
times the mean and a normalized payoff second moment at most one. -/
theorem relativeMean_good_seed_second_moment {I : Type} [Fintype I] [DecidableEq I]
    (B : ℕ) (p : FinDist I) (f : I → ℝ) (ω : Fin (32*B) → I)
    (hμ : 0 < p.expect f) (hv : p.variance f ≤ (B : ℝ)*(p.expect f)^2)
    (hseed : |relativeMeanCenter B f ω-p.expect f| ≤ p.expect f/2) :
    0 < relativeMeanScale B f ω ∧
      relativeMeanScale B f ω ≤ 3*Real.sqrt (B+1 : ℝ)*p.expect f ∧
      (∑ i, p.prob i*(relativeMeanPayoff B f ω i)^2) ≤ 1 := by
  let c := relativeMeanCenter B f ω
  let μ := p.expect f
  have hc : μ/2 ≤ c := by have hh := (abs_le.mp hseed).1; dsimp [c, μ]; linarith
  have hc' : c ≤ 3*μ/2 := by have hh := (abs_le.mp hseed).2; dsimp [c, μ]; linarith
  have hcpos : 0 < c := by linarith
  have hspos : 0 < Real.sqrt (B+1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hs : (Real.sqrt (B+1 : ℝ))^2=(B+1 : ℝ) := Real.sq_sqrt (by positivity)
  have hscale : 0 < relativeMeanScale B f ω := by
    exact mul_pos (mul_pos (by norm_num) hspos) hcpos
  refine ⟨hscale, ?_, ?_⟩
  · change 2*Real.sqrt (B+1 : ℝ)*c ≤ 3*Real.sqrt (B+1 : ℝ)*μ
    nlinarith [mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ 2*Real.sqrt (B+1 : ℝ))]
  · have hraw : (∑ i, p.prob i*(f i)^2) ≤ (B+1 : ℝ)*μ^2 := by
      have he := SignedMean.shifted_second_moment p f 0
      simp only [sub_zero] at he
      rw [he]
      dsimp [μ]
      nlinarith
    have he : (∑ i, p.prob i*(relativeMeanPayoff B f ω i)^2) =
        (∑ i, p.prob i*(f i)^2)/(relativeMeanScale B f ω)^2 := by
      simp only [relativeMeanPayoff, div_pow, mul_div_assoc, Finset.sum_div]
    rw [he]
    apply (div_le_one (by positivity : 0 < (relativeMeanScale B f ω)^2)).mpr
    have hcsq : μ^2 ≤ 4*c^2 := by
      have hh := mul_self_le_mul_self (by linarith : 0 ≤ μ/2) hc
      nlinarith
    have hssq : (relativeMeanScale B f ω)^2=4*(B+1 : ℝ)*c^2 := by
      change (2*Real.sqrt (B+1 : ℝ)*c)^2=_
      rw [mul_pow, mul_pow, hs]
      ring
    rw [hssq]
    exact hraw.trans (by nlinarith [mul_le_mul_of_nonneg_left hcsq (by positivity : 0 ≤ (B+1 : ℝ))])

/-- A layer estimate accurate to `(1 / 2)^k` under the stated scale bounds yields relative mean
error at most `3 * sqrt (B + 1) * (1 / 2)^k` times the mean. -/
theorem relativeMean_good_record_error {I : Type} [Fintype I] [DecidableEq I]
    (B k : ℕ) (p : FinDist I) (f : I → ℝ) (ω : Fin (32*B) → I) (u : LayerRecord k)
    (hscale : 0 < relativeMeanScale B f ω)
    (hscale' : relativeMeanScale B f ω ≤ 3*Real.sqrt (B+1 : ℝ)*p.expect f)
    (hu : |layerEstimate k u-p.expect (relativeMeanPayoff B f ω)| ≤ (1/2 : ℝ)^k) :
    |relativeMeanEstimate B k f (ω,u)-p.expect f| ≤
      3*Real.sqrt (B+1 : ℝ)*(1/2 : ℝ)^k*p.expect f := by
  have hmean : p.expect (relativeMeanPayoff B f ω)=p.expect f/relativeMeanScale B f ω := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect relativeMeanPayoff
    simp only [← mul_div_assoc, Finset.sum_div]
  have he : relativeMeanEstimate B k f (ω,u)-p.expect f =
      relativeMeanScale B f ω*(layerEstimate k u-p.expect (relativeMeanPayoff B f ω)) := by
    rw [hmean]
    unfold relativeMeanEstimate
    field_simp
  rw [he, abs_mul, abs_of_pos hscale]
  calc
    _ ≤ relativeMeanScale B f ω*(1/2 : ℝ)^k := mul_le_mul_of_nonneg_left hu hscale.le
    _ ≤ (3*Real.sqrt (B+1 : ℝ)*p.expect f)*(1/2 : ℝ)^k :=
      mul_le_mul_of_nonneg_right hscale' (by positivity)
    _ = _ := by ring

/-- For nonnegative payoff, positive mean, and variance at most `B` times the squared mean, the
conditional estimator attains the stated relative error with probability at least `2 / 3`
when `B ≥ 1` and `k ≥ 4`. See [Montanaro2015]. -/
theorem relative_variance_actual_conditional_estimator (I : Type) [Fintype I] [DecidableEq I]
    (B k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i)
    (hB : 1 ≤ B) (hk : 4 ≤ k) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i*f i
    0 < μ → (∑ i, BornProb (ApplyGate A (Ket j)) i*(f i-μ)^2) ≤ (B : ℝ)*μ^2 →
    (∑ ω with |relativeMeanEstimate B k f ω-μ| ≤ 3*Real.sqrt (B+1 : ℝ)*(1/2 : ℝ)^k*μ,
      (relativeMeanLaw B k A j f hA hf).prob ω) ≥ 2/3 := by
  let p := signedMeanSource A j hA
  let seed := relativeMeanSeedLaw B A j hA
  let E := fun ω => |relativeMeanCenter B f ω-p.expect f| ≤ p.expect f/2
  let Q :=
      fun ω => layerLaw k A j (relativeMeanPayoff B f ω) hA (relativeMeanPayoff_nonneg B f hf ω)
  let F := fun ω u => |layerEstimate k u-p.expect (relativeMeanPayoff B f ω)| ≤ (1/2 : ℝ)^k
  change 0 < p.expect f → p.variance f ≤ (B : ℝ)*(p.expect f)^2 → _
  intro hμ hv
  have hseed : 7/8 ≤ SignedMean.mass seed E := relativeMean_seed_good B A j f hA hB hμ hv
  have hF (ω : Fin (32*B) → I) (hω : E ω) : 15/16 ≤ SignedMean.mass (Q ω) (F ω) := by
    have hs := relativeMean_good_seed_second_moment B p f ω hμ hv hω
    have hg := layered_quantum_mean_actual_guarantee k (by omega) A j (relativeMeanPayoff B f ω)
      hA (relativeMeanPayoff_nonneg B f hf ω) hs.2.2
    have hg' : 1-(1/2 : ℝ)^k ≤ SignedMean.mass (Q ω) (F ω) := by
      simpa only [SignedMean.mass, neg_pow_half_eq] using! hg
    have he : (1/2 : ℝ)^k ≤ 1/16 := by
      calc
        _ ≤ (1/2 : ℝ)^4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
        _ = _ := by norm_num
    linarith
  have hl := SignedMean.conditional_good_lower seed E (fun ω => SignedMean.mass (Q ω) (F ω))
    (7/8) (15/16) (by norm_num) hseed hF
  have hm := SignedMean.conditional_one_event seed Q E F
  have hl' : (7/8 : ℝ)*(15/16) ≤
      ∑ ω with E ω.1 ∧ F ω.1 ω.2, (relativeMeanLaw B k A j f hA hf).prob ω := by
    exact hm.symm ▸ hl
  apply (by norm_num : (2/3 : ℝ) ≤ (7/8)*(15/16)).trans
  apply hl'.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    obtain ⟨_, he, hu⟩ := Finset.mem_filter.mp hω
    have hs := relativeMean_good_seed_second_moment B p f ω.1 hμ hv he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      relativeMean_good_record_error B k p f ω.1 ω.2 hs.1 hs.2.1 hu⟩
  · intro ω _ _
    exact (relativeMeanLaw B k A j f hA hf).nonneg ω

/-- The list of counted amplitude estimation circuits for all payoff layers, each repeated
according to `layerRepetitions`. -/
noncomputable def meanAEPrograms {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) :
    List (Circuit (Fin (layerGrid k) × (Bool × (I × Bool)))) :=
  (List.ofFn (fun l : Fin (k+2) => List.replicate (2*layerRepetitions k+1)
    (countedAECircuit (layerGrid k) (payoffPreparation A (layerPayoff f l.val)) (j,false)))).flatten

/-- The layer program list has `q` circuits, `q * (layerGrid k - 1)` queries, and `q * (5 *
(layerGrid k - 1) + 3)` gates, where `q = (k + 2) * (2 * layerRepetitions k + 1)`. -/
theorem meanAEPrograms_counts {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) :
    let q := (k+2)*(2*layerRepetitions k+1)
    (meanAEPrograms k A j f).length=q ∧
      ((meanAEPrograms k A j f).map QueryCount).sum=q*(layerGrid k-1) ∧
      ((meanAEPrograms k A j f).map GateCount).sum=q*(5*(layerGrid k-1)+3) := by
  have hquery (l : Fin (k+2)) := (prepared_ae_access_ledger (layerGrid k) (layerGrid_pos k)
    (payoffPreparation A (layerPayoff f l.val)) (j,false)).1
  have hgate (l : Fin (k+2)) := (prepared_ae_access_ledger (layerGrid k) (layerGrid_pos k)
    (payoffPreparation A (layerPayoff f l.val)) (j,false)).2.1
  constructor
  · simp [meanAEPrograms, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    ring
  · constructor <;>
      simp only [meanAEPrograms, List.map_flatten, List.sum_flatten,
        Function.comp_def, List.map_ofFn, List.sum_ofFn, List.map_replicate, List.sum_replicate,
        hquery, hgate, nsmul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    all_goals push_cast; ring

/-- Resource counts for source preparations, layer copies, measurements, forward and inverse
layer accesses, queries, and gates. -/
@[ext] structure QuantumMeanResources where
  sourcePreparations : ℕ
  layerCopies : ℕ
  measurements : ℕ
  layerForward : ℕ
  layerInverse : ℕ
  queries : ℕ
  gates : ℕ
  deriving DecidableEq

/-- Collects source preparation and layer circuit counts into a `QuantumMeanResources` record. -/
noncomputable def meanProgramResources {I : Type} [Fintype I] [DecidableEq I]
    (k m : ℕ) (A : Matrix I I ℂ)
    (C : List (Circuit (Fin (layerGrid k) × (Bool × (I × Bool))))) : QuantumMeanResources where
  sourcePreparations := GateCount (List.replicate m (Step.gate A))
  layerCopies := C.length
  measurements := m+C.length
  layerForward := (C.map (fun _ => aeForwardAccesses (aeAccessWord (I := I × Bool) (layerGrid k)))).sum
  layerInverse := (C.map (fun _ => aeBackwardAccesses (aeAccessWord (I := I × Bool) (layerGrid k)))).sum
  queries := (C.map QueryCount).sum
  gates := GateCount (List.replicate m (Step.gate A))+(C.map GateCount).sum

/-- The resource ledger for one source preparation and the positive and negative centered layer
program families. -/
noncomputable def signedMeanResources {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j x : I) (f : I → ℝ) (σ : ℝ) : QuantumMeanResources :=
  meanProgramResources k 1 A
    (meanAEPrograms k A j (centerPositive f σ x) ++ meanAEPrograms k A j (centerNegative f σ x))

/-- The resource ledger for `32 * B` source preparations and the conditional normalized payoff
layer programs. -/
noncomputable def relativeMeanResources {I : Type} [Fintype I] [DecidableEq I]
    (B k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (ω : Fin (32*B) → I) : QuantumMeanResources :=
  meanProgramResources k (32*B) A (meanAEPrograms k A j (relativeMeanPayoff B f ω))

/-- The collected ledger has `m` source preparations, `C.length * layerGrid k` forward layer
accesses, and `C.length * (layerGrid k - 1)` inverse layer accesses. -/
theorem meanProgramResources_labels {I : Type} [Fintype I] [DecidableEq I]
    (k m : ℕ) (A : Matrix I I ℂ)
    (C : List (Circuit (Fin (layerGrid k) × (Bool × (I × Bool))))) :
    (meanProgramResources k m A C).sourcePreparations=m ∧
      (meanProgramResources k m A C).layerForward=C.length*layerGrid k ∧
      (meanProgramResources k m A C).layerInverse=C.length*(layerGrid k-1) := by
  have hs := prepared_ae_separate_access_counts (I := I × Bool) (layerGrid k) (layerGrid_pos k)
  have hsource : GateCount (List.replicate m (Step.gate A))=m := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, ih]
  simp [meanProgramResources, hs.1, hs.2.1, hsource]

/-- Given the stated length, query, and gate totals for `C`, the full ledger equals the explicit
seven-field resource record. -/
theorem meanProgramResources_eq {I : Type} [Fintype I] [DecidableEq I]
    (k m : ℕ) (A : Matrix I I ℂ)
    (C : List (Circuit (Fin (layerGrid k) × (Bool × (I × Bool))))) (q : ℕ)
    (hlen : C.length=q) (hquery : (C.map QueryCount).sum=q*(layerGrid k-1))
    (hgate : (C.map GateCount).sum=q*(5*(layerGrid k-1)+3)) :
    meanProgramResources k m A C =
      ⟨m,q,m+q,q*layerGrid k,q*(layerGrid k-1),q*(layerGrid k-1),m+q*(5*(layerGrid k-1)+3)⟩ := by
  have hl := meanProgramResources_labels k m A C
  apply QuantumMeanResources.ext
  · exact hl.1
  · exact hlen
  · change m+C.length=m+q
    rw [hlen]
  · exact hl.2.1.trans (congrArg (fun n => n*layerGrid k) hlen)
  · exact hl.2.2.trans (congrArg (fun n => n*(layerGrid k-1)) hlen)
  · exact hquery
  · change (meanProgramResources k m A C).sourcePreparations+(C.map GateCount).sum=_
    rw [hl.1, hgate]

/-- The signed estimator uses one source preparation and `2 * q` layer copies, with all
measurement, forward, inverse, query, and gate counts given by the displayed resource
record. -/
theorem signed_centered_full_resources {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j x : I) (f : I → ℝ) (σ : ℝ) :
    let q := (k+2)*(2*layerRepetitions k+1)
    signedMeanResources k A j x f σ =
      ⟨1, 2*q, 1+2*q, 2*q*layerGrid k, 2*q*(layerGrid k-1),
        2*q*(layerGrid k-1), 1+2*q*(5*(layerGrid k-1)+3)⟩ := by
  have hp := meanAEPrograms_counts k A j (centerPositive f σ x)
  have hn := meanAEPrograms_counts k A j (centerNegative f σ x)
  apply meanProgramResources_eq
  · rw [List.length_append, hp.1, hn.1]
    ring
  · rw [List.map_append, List.sum_append, hp.2.1, hn.2.1]
    ring
  · rw [List.map_append, List.sum_append, hp.2.2, hn.2.2]
    ring

/-- The relative estimator uses `32 * B` source preparations and `q` layer copies, with all
remaining counts given by the displayed resource record. -/
theorem relative_variance_full_resources {I : Type} [Fintype I] [DecidableEq I]
    (B k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (ω : Fin (32*B) → I) :
    let q := (k+2)*(2*layerRepetitions k+1)
    relativeMeanResources B k A j f ω =
      ⟨32*B, q, 32*B+q, q*layerGrid k, q*(layerGrid k-1), q*(layerGrid k-1),
        32*B+q*(5*(layerGrid k-1)+3)⟩ := by
  have hc := meanAEPrograms_counts k A j (relativeMeanPayoff B f ω)
  exact meanProgramResources_eq k (32*B) A _ _ hc.1 hc.2.1 hc.2.2

/-- The aggregate resource ledger for the `2 * r + 1` signed estimator runs used by the median. -/
noncomputable def signedMeanMedianResources {I : Type} [Fintype I] [DecidableEq I]
    (k r : ℕ) (A : Matrix I I ℂ) (j : I) (x : Fin (2*r+1) → I) (f : I → ℝ) (σ : ℝ) :
    QuantumMeanResources := meanProgramResources k (2*r+1) A
      (List.ofFn (fun a : Fin (2*r+1) => meanAEPrograms k A j (centerPositive f σ (x a)) ++
        meanAEPrograms k A j (centerNegative f σ (x a)))).flatten

/-- The fresh median ledger multiplies every signed estimator resource count by `2 * r + 1`,
with `q = (k + 2) * (2 * layerRepetitions k + 1)`. -/
theorem signed_centered_fresh_full_resources {I : Type} [Fintype I] [DecidableEq I]
    (k r : ℕ) (A : Matrix I I ℂ) (j : I) (x : Fin (2*r+1) → I) (f : I → ℝ) (σ : ℝ) :
    let q := (k+2)*(2*layerRepetitions k+1)
    let m := 2*r+1
    signedMeanMedianResources k r A j x f σ =
      ⟨m,m*(2*q),m*(1+2*q),m*(2*q*layerGrid k),m*(2*q*(layerGrid k-1)),
        m*(2*q*(layerGrid k-1)),m*(1+2*q*(5*(layerGrid k-1)+3))⟩ := by
  let q := (k+2)*(2*layerRepetitions k+1)
  let m := 2*r+1
  let C := fun a : Fin m => meanAEPrograms k A j (centerPositive f σ (x a)) ++
    meanAEPrograms k A j (centerNegative f σ (x a))
  have hlen (a : Fin m) : (C a).length=2*q := by
    dsimp [C]
    rw [List.length_append, (meanAEPrograms_counts k A j (centerPositive f σ (x a))).1,
      (meanAEPrograms_counts k A j (centerNegative f σ (x a))).1]
    dsimp [q]
    ring
  have hquery (a : Fin m) : ((C a).map QueryCount).sum=2*q*(layerGrid k-1) := by
    dsimp [C]
    rw [List.map_append, List.sum_append,
      (meanAEPrograms_counts k A j (centerPositive f σ (x a))).2.1,
      (meanAEPrograms_counts k A j (centerNegative f σ (x a))).2.1]
    dsimp [q]
    ring
  have hgate (a : Fin m) : ((C a).map GateCount).sum=2*q*(5*(layerGrid k-1)+3) := by
    dsimp [C]
    rw [List.map_append, List.sum_append,
      (meanAEPrograms_counts k A j (centerPositive f σ (x a))).2.2,
      (meanAEPrograms_counts k A j (centerNegative f σ (x a))).2.2]
    dsimp [q]
    ring
  have hh : (List.ofFn C).flatten.length=m*(2*q) := by
    simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def, hlen,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rfl
  have hq : (((List.ofFn C).flatten).map QueryCount).sum=m*(2*q)*(layerGrid k-1) := by
    simp only [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def, hquery,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hg : (((List.ofFn C).flatten).map GateCount).sum=m*(2*q)*(5*(layerGrid k-1)+3) := by
    simp only [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def, hgate,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have he := meanProgramResources_eq k m A (List.ofFn C).flatten (m*(2*q)) hh hq hg
  change meanProgramResources k m A (List.ofFn C).flatten = _
  rw [he]
  congr 1 <;> ring
end Qatlib.Concepts.AmplitudeCore.PayoffMedian
