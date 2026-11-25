/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.Sampling
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteDistributionVariation

@[expose] public section

/-!
# Stability of the signed tomography transcript

In the two batches of [KerenidisLandmanPrakash2020], Appendix G, the law
of the second shot depends on the first record through its empirical
reference. Uniform bounds for each conditional shot therefore control
the full transcript. The bounds allow arbitrary finite shot laws.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript (jointLaw)
open scoped BigOperators Classical

/-- The sum of absolute mass differences of two joint laws is bounded by the
first-record difference plus a uniform bound for their conditional laws. -/
private theorem joint_mass_difference_le {H T : Type} [Fintype H] [Fintype T]
    (p q : FinDist H) (P Q : H → FinDist T) (δ : ℝ)
    (hδ : ∀ h, (∑ t, |(P h).prob t - (Q h).prob t|) ≤ δ) :
    (∑ z, |(jointLaw p P).prob z - (jointLaw q Q).prob z|) ≤
      (∑ h, |p.prob h - q.prob h|) + δ := by
  have hPoint (h : H) (t : T) :
      |p.prob h * (P h).prob t - q.prob h * (Q h).prob t| ≤
        p.prob h * |(P h).prob t - (Q h).prob t| +
          |p.prob h - q.prob h| * (Q h).prob t := by
    calc
      _ = |p.prob h * ((P h).prob t - (Q h).prob t) +
            (p.prob h - q.prob h) * (Q h).prob t| := by congr 1; ring
      _ ≤ _ := by
        simpa only [abs_mul, abs_of_nonneg (p.nonneg h), abs_of_nonneg ((Q h).nonneg t)]
          using abs_add_le (p.prob h * ((P h).prob t - (Q h).prob t))
            ((p.prob h - q.prob h) * (Q h).prob t)
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ h, ∑ t, (p.prob h * |(P h).prob t - (Q h).prob t| +
          |p.prob h - q.prob h| * (Q h).prob t) :=
      Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun t _ => hPoint h t
    _ ≤ ∑ h, (p.prob h * δ + |p.prob h - q.prob h|) := by
      apply Finset.sum_le_sum
      intro h _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (Q h).sum_one, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_left (hδ h) (p.nonneg h)) le_rfl
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_one, one_mul, add_comm]

/-- Prepending a shot multiplies the probability of the tail by the first-shot mass. -/
private theorem repeated_sample_prob_cons {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) {n : ℕ} (x : X) (tail : Fin n → X) :
    (independentSampleLaw (fun _ : Fin (n + 1) => p)).prob (Fin.cons x tail) =
      p.prob x * (independentSampleLaw (fun _ : Fin n => p)).prob tail := by
  change (∏ i : Fin (n + 1), p.prob ((Fin.cons x tail : Fin (n + 1) → X) i)) =
    p.prob x * ∏ i : Fin n, p.prob (tail i)
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Repeating an independent shot grows its total variation bound at most linearly
in the number of shots. -/
theorem repeated_sample_tv_le {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (n : ℕ) :
    tvDist (independentSampleLaw fun _ : Fin n => p)
      (independentSampleLaw fun _ : Fin n => q) ≤ n * tvDist p q := by
  have hMass (m : ℕ) :
      (∑ w, |(independentSampleLaw fun _ : Fin m => p).prob w -
        (independentSampleLaw fun _ : Fin m => q).prob w|) ≤
        m * ∑ x, |p.prob x - q.prob x| := by
    induction m with
    | zero => simp [independentSampleLaw]
    | succ m ih =>
        let P (_ : X) := independentSampleLaw fun _ : Fin m => p
        let Q (_ : X) := independentSampleLaw fun _ : Fin m => q
        have hReindex :
            (∑ w, |(independentSampleLaw fun _ : Fin (m + 1) => p).prob w -
              (independentSampleLaw fun _ : Fin (m + 1) => q).prob w|) =
              ∑ z, |(jointLaw p P).prob z - (jointLaw q Q).prob z| := by
          let e := Fin.consEquiv (fun _ : Fin (m + 1) => X)
          rw [← e.sum_comp (fun w =>
            |(independentSampleLaw fun _ : Fin (m + 1) => p).prob w -
              (independentSampleLaw fun _ : Fin (m + 1) => q).prob w|)]
          refine Finset.sum_congr rfl fun ⟨x, tail⟩ _ => ?_
          change |(independentSampleLaw fun _ : Fin (m + 1) => p).prob (Fin.cons x tail) -
            (independentSampleLaw fun _ : Fin (m + 1) => q).prob (Fin.cons x tail)| = _
          simp only [jointLaw, P, Q, repeated_sample_prob_cons]
        rw [hReindex]
        exact (joint_mass_difference_le p q P Q _ (fun _ => ih)).trans_eq (by push_cast; ring)
  unfold tvDist
  calc
    _ ≤ (1 / 2 : ℝ) * (n * ∑ x, |p.prob x - q.prob x|) :=
      mul_le_mul_of_nonneg_left (hMass n) (by norm_num)
    _ = _ := by ring

/-- An event's probability can increase by at most the total variation distance. -/
theorem event_mass_le_add_tv {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (event : X → Prop) [DecidablePred event] :
    eventMass p event ≤ eventMass q event + tvDist p q := by
  have hEvent : |eventMass p event - eventMass q event| ≤ FiniteInformationDivergence.tv p q :=
    FiniteDistributionVariation.event_distance p q (Finset.univ.filter event)
  have hTV : FiniteInformationDivergence.tv p q = tvDist p q := by
    unfold FiniteInformationDivergence.tv tvDist
    ring
  exact sub_le_iff_le_add'.mp ((le_abs_self _).trans (hEvent.trans_eq hTV))

variable {depth basisShots interferenceShots : ℕ}

/-- The total variation of the two signed tomography records is bounded by the
number of shots of each kind times its respective per-shot error. The second
bound must hold for the reference constructed from each first record. -/
theorem signed_tomography_transcript_tv_le (direction : Address depth → ℝ)
    (hDirection : ∑ i, direction i ^ 2 = 1) (hBasis : 0 < basisShots)
    (basisLaw : FinDist (Address depth))
    (interferenceLaw : (Fin basisShots → Address depth) → FinDist (Bool × Address depth))
    (basisError interferenceError : ℝ)
    (hBasisError : tvDist basisLaw (basisSampleLaw direction hDirection) ≤ basisError)
    (hInterferenceError : ∀ b (hne : List.ofFn b ≠ []),
      tvDist (interferenceLaw b)
        (interferenceSampleLaw direction hDirection (List.ofFn b) hne) ≤ interferenceError) :
    tvDist (jointLaw (independentSampleLaw fun _ : Fin basisShots => basisLaw)
      (fun b => independentSampleLaw fun _ : Fin interferenceShots => interferenceLaw b))
      (signedTomographyLaw direction hDirection basisShots interferenceShots hBasis) ≤
      basisShots * basisError + interferenceShots * interferenceError := by
  let p := independentSampleLaw fun _ : Fin basisShots => basisLaw
  let q := independentSampleLaw fun _ : Fin basisShots => basisSampleLaw direction hDirection
  let P (b : Fin basisShots → Address depth) :=
    independentSampleLaw fun _ : Fin interferenceShots => interferenceLaw b
  have hne (b : Fin basisShots → Address depth) : List.ofFn b ≠ [] := by
    intro hEmpty
    have hLength := congrArg List.length hEmpty
    simp only [List.length_ofFn, List.length_nil] at hLength
    exact hBasis.ne' hLength
  let Q (b : Fin basisShots → Address depth) := independentSampleLaw
    fun _ : Fin interferenceShots => interferenceSampleLaw direction hDirection (List.ofFn b) (hne b)
  have hp : tvDist p q ≤ (basisShots : ℝ) * basisError :=
    (repeated_sample_tv_le _ _ _).trans
      (mul_le_mul_of_nonneg_left hBasisError (Nat.cast_nonneg _))
  have hq (b : Fin basisShots → Address depth) :
      tvDist (P b) (Q b) ≤ (interferenceShots : ℝ) * interferenceError :=
    (repeated_sample_tv_le _ _ _).trans
      (mul_le_mul_of_nonneg_left (hInterferenceError b (hne b)) (Nat.cast_nonneg _))
  change tvDist (jointLaw p P) (jointLaw q Q) ≤ _
  have hh := joint_mass_difference_le p q P Q (2 * (interferenceShots * interferenceError))
    (fun b => by have h := hq b; unfold tvDist at h; linarith)
  unfold tvDist at hp ⊢
  linarith

end Qatlib.Concepts.QRAM.SignedReadout
