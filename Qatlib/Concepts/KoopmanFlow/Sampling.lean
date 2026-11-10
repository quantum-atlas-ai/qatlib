/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.KrausCompile.BornMoments.IndependentShots
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Lattice
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.KoopmanFlow.Sampling
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.KrausCompile.BornMoments
open Qatlib.Concepts.ProbabilityCore.Concentration
open scoped BigOperators

def recordsLaw {h N : ℕ} (p : Fin h → FinDist (Fin N)) (M : ℕ) :
    FinDist (Fin h → Fin M → Fin N) := independentSampleLaw (fun j => iidLaw (p j) M)

theorem recordsLaw_mass {h N M : ℕ} (p : Fin h → FinDist (Fin N))
    (r : Fin h → Fin M → Fin N) :
    (recordsLaw p M).prob r = ∏ j, ∏ m, (p j).prob (r j m) := rfl

def recordsPMF {h N : ℕ} (p : Fin h → FinDist (Fin N)) (M : ℕ) :
    PMF (Fin h → Fin M → Fin N) := toPMF (recordsLaw p M)

theorem recordsPMF_mass {h N M : ℕ} (p : Fin h → FinDist (Fin N))
    (r : Fin h → Fin M → Fin N) :
    (recordsPMF p M r).toReal = ∏ j, ∏ m, (p j).prob (r j m) := by
  exact ENNReal.toReal_ofReal ((recordsLaw p M).nonneg r)

def indicator {N : ℕ} (i a : Fin N) : ℝ := if a = i then 1 else 0

def empirical {N M : ℕ} (i : Fin N) (r : Fin M → Fin N) : ℝ := FinDist.avg (indicator i) r

def mixture {h N : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ) (i : Fin N) : ℝ :=
  ∑ j, w j * (p j).prob i

def empiricalMixture {h N M : ℕ} (w : Fin h → ℝ) (i : Fin N)
    (r : Fin h → Fin M → Fin N) : ℝ := ∑ j, w j * empirical i (r j)

theorem indicator_mean {N : ℕ} (p : FinDist (Fin N)) (i : Fin N) :
    p.expect (indicator i) = p.prob i := by
  simp [FinDist.expect, indicator, mul_ite]

theorem indicator_variance {N : ℕ} (p : FinDist (Fin N)) (i : Fin N) :
    p.variance (indicator i) = p.prob i - p.prob i ^ 2 := by
  rw [FinDist.variance_eq_expect_sq_sub, indicator_mean]
  have hs : (fun a => indicator i a ^ 2) = indicator i := by
    ext a
    by_cases h : a = i <;> simp [indicator, h]
  rw [hs, indicator_mean]

theorem mixture_mean {h N M : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ)
    (hM : 0 < M) (i : Fin N) :
    (recordsLaw p M).expect (empiricalMixture w i) = mixture p w i := by
  change (independentSampleLaw (fun j => iidLaw (p j) M)).expect
    (weightedSampleSum w (fun _ => FinDist.avg (indicator i))) = _
  rw [independent_weighted_expectation]
  simp_rw [iid_average_mean _ M _ hM, indicator_mean]
  rfl

theorem mixture_coordinate_variance {h N M : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ)
    (hM : 0 < M) (i : Fin N) :
    (recordsLaw p M).variance (empiricalMixture w i) =
      (∑ j, w j ^ 2 * ((p j).prob i - (p j).prob i ^ 2)) / M := by
  change (independentSampleLaw (fun j => iidLaw (p j) M)).variance
    (weightedSampleSum w (fun _ => FinDist.avg (indicator i))) = _
  rw [independent_weighted_variance]
  simp_rw [iid_average_variance _ M _ hM, indicator_variance]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

def squaredError {h N M : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ)
    (r : Fin h → Fin M → Fin N) : ℝ :=
  ∑ i, (empiricalMixture w i r - mixture p w i) ^ 2

def errorVector {h N M : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ)
    (r : Fin h → Fin M → Fin N) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => empiricalMixture w i r - mixture p w i)

def l2Error {h N M : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ)
    (r : Fin h → Fin M → Fin N) : ℝ := ‖errorVector p w r‖

theorem l2Error_sq {h N M : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ)
    (r : Fin h → Fin M → Fin N) : l2Error p w r ^ 2 = squaredError p w r := by
  exact EuclideanSpace.real_norm_sq_eq (errorVector p w r)

theorem expect_sum {X I : Type} [Fintype X] [DecidableEq X] [Fintype I]
    (q : FinDist X) (f : I → X → ℝ) :
    q.expect (fun r => ∑ i, f i r) = ∑ i, q.expect (f i) := by
  unfold FinDist.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mixture_exact_second_moment {h N M : ℕ} (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ)
    (hM : 0 < M) :
    (recordsLaw p M).expect (squaredError p w) =
      (∑ j, w j ^ 2 * (1 - ∑ i, (p j).prob i ^ 2)) / M := by
  unfold squaredError
  rw [expect_sum]
  have hv (i : Fin N) : (recordsLaw p M).expect
      (fun r => (empiricalMixture w i r - mixture p w i) ^ 2) =
      (recordsLaw p M).variance (empiricalMixture w i) := by
    unfold FinDist.variance
    rw [mixture_mean p w hM i]
  simp_rw [hv, mixture_coordinate_variance p w hM]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, (p j).sum_one]

theorem mixture_second_moment_le_sum_weights {h N M : ℕ}
    (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ) (hM : 0 < M) :
    (recordsLaw p M).expect (squaredError p w) ≤ (∑ j, w j ^ 2) / M := by
  rw [mixture_exact_second_moment p w hM]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ (M : ℝ))
  apply Finset.sum_le_sum
  intro j _
  have hp : 0 ≤ ∑ i, (p j).prob i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [sq_nonneg (w j)]

theorem sum_weights_sq_le {h : ℕ} (w : Fin h → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j, w j = 1) (W : ℝ) (hW : ∀ j, w j ≤ W) : ∑ j, w j ^ 2 ≤ W := by
  calc
    ∑ j, w j ^ 2 ≤ ∑ j, W * w j := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [mul_nonneg (hw j) (sub_nonneg.mpr (hW j))]
    _ = W := by rw [← Finset.mul_sum, hsum, mul_one]

theorem mixture_second_moment_le_bound {h N M : ℕ}
    (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ) (hM : 0 < M)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (W : ℝ) (hW : ∀ j, w j ≤ W) :
    (recordsLaw p M).expect (squaredError p w) ≤ W / M := by
  exact (mixture_second_moment_le_sum_weights p w hM).trans
    (div_le_div_of_nonneg_right (sum_weights_sq_le w hw hsum W hW) (by positivity))

theorem expect_sq_le_second {X : Type} [Fintype X] [DecidableEq X]
    (q : FinDist X) (f : X → ℝ) : q.expect f ^ 2 ≤ q.expect (fun x => f x ^ 2) := by
  have hvar : 0 ≤ q.variance f :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (q.nonneg x) (sq_nonneg _))
  rw [FinDist.variance_eq_expect_sq_sub] at hvar
  linarith

theorem mixture_expected_l2_le_bound {h N M : ℕ}
    (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ) (hM : 0 < M)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (W : ℝ) (hW : ∀ j, w j ≤ W) :
    (recordsLaw p M).expect (l2Error p w) ≤ Real.sqrt (W / M) := by
  apply Real.le_sqrt_of_sq_le
  have hv := expect_sq_le_second (recordsLaw p M) (l2Error p w)
  have he : (recordsLaw p M).expect (fun r => l2Error p w r ^ 2) =
      (recordsLaw p M).expect (squaredError p w) := by
    congr 1
    ext r
    exact l2Error_sq p w r
  rw [he] at hv
  exact hv.trans (mixture_second_moment_le_bound p w hM hw hsum W hW)

def maxWeight {h : ℕ} (hh : 0 < h) (w : Fin h → ℝ) : ℝ :=
  Finset.univ.sup' (by exact ⟨⟨0, hh⟩, Finset.mem_univ _⟩) w

theorem weight_le_max {h : ℕ} (hh : 0 < h) (w : Fin h → ℝ) (j : Fin h) :
    w j ≤ maxWeight hh w := Finset.le_sup' w (Finset.mem_univ j)

theorem mixture_expected_l2_le_max {h N M : ℕ}
    (p : Fin h → FinDist (Fin N)) (w : Fin h → ℝ) (hM : 0 < M) (hh : 0 < h)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    (recordsLaw p M).expect (l2Error p w) ≤ Real.sqrt (maxWeight hh w / M) :=
  mixture_expected_l2_le_bound p w hM hw hsum _ (weight_le_max hh w)

def rawWeight {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (j : Fin h) : ℝ :=
  (2 * K / (h : ℝ)) / (Real.pi * (1 + nodes j ^ 2))

def quadratureMass {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) : ℝ := ∑ j, rawWeight K nodes j

def normalizedWeight {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (j : Fin h) : ℝ :=
  rawWeight K nodes j / quadratureMass K nodes

theorem rawWeight_pos {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h)
    (j : Fin h) : 0 < rawWeight K nodes j := by
  unfold rawWeight
  positivity

theorem quadratureMass_pos {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h) :
    0 < quadratureMass K nodes := by
  unfold quadratureMass
  exact Finset.sum_pos (fun j _ => rawWeight_pos K nodes hK hh j)
    ⟨⟨0, hh⟩, Finset.mem_univ _⟩

theorem normalizedWeight_pos {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h)
    (j : Fin h) : 0 < normalizedWeight K nodes j :=
  div_pos (rawWeight_pos K nodes hK hh j) (quadratureMass_pos K nodes hK hh)

theorem normalizedWeight_sum {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h) :
    ∑ j, normalizedWeight K nodes j = 1 := by
  unfold normalizedWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (quadratureMass_pos K nodes hK hh))

theorem rawWeight_le {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h)
    (j : Fin h) : rawWeight K nodes j ≤ 2 * K / (Real.pi * (h : ℝ)) := by
  have ha : 0 ≤ 2 * K / (h : ℝ) := by positivity
  have hden : Real.pi ≤ Real.pi * (1 + nodes j ^ 2) := by
    nlinarith [Real.pi_pos, sq_nonneg (nodes j)]
  unfold rawWeight
  calc
    _ ≤ (2 * K / (h : ℝ)) / Real.pi := div_le_div_of_nonneg_left ha Real.pi_pos hden
    _ = _ := by rw [div_div, mul_comm (h : ℝ) Real.pi]

theorem normalizedWeight_le {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h)
    (j : Fin h) :
    normalizedWeight K nodes j ≤ 2 * K / (Real.pi * (h : ℝ) * quadratureMass K nodes) := by
  unfold normalizedWeight
  calc
    _ ≤ (2 * K / (Real.pi * (h : ℝ))) / quadratureMass K nodes :=
      div_le_div_of_nonneg_right (rawWeight_le K nodes hK hh j)
        (le_of_lt (quadratureMass_pos K nodes hK hh))
    _ = _ := by rw [div_div]

theorem normalized_maxWeight_le {h : ℕ} (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h) :
    maxWeight hh (normalizedWeight K nodes) ≤
      2 * K / (Real.pi * (h : ℝ) * quadratureMass K nodes) := by
  unfold maxWeight
  exact Finset.sup'_le _ _ (fun j _ => normalizedWeight_le K nodes hK hh j)

theorem normalized_mixture_eq_raw_div {h N : ℕ} (p : Fin h → FinDist (Fin N))
    (K : ℝ) (nodes : Fin h → ℝ) (i : Fin N) :
    mixture p (normalizedWeight K nodes) i =
      (∑ j, rawWeight K nodes j * (p j).prob i) / quadratureMass K nodes := by
  unfold mixture normalizedWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadrature_expected_l2_bound {h N M : ℕ} (p : Fin h → FinDist (Fin N))
    (K : ℝ) (nodes : Fin h → ℝ) (hK : 0 < K) (hh : 0 < h) (hM : 0 < M) :
    (recordsLaw p M).expect (l2Error p (normalizedWeight K nodes)) ≤
      Real.sqrt (2 * K / (Real.pi * (h : ℝ) * (M : ℝ) * quadratureMass K nodes)) := by
  have h := mixture_expected_l2_le_bound p (normalizedWeight K nodes) hM
    (fun j => le_of_lt (normalizedWeight_pos K nodes hK hh j))
    (normalizedWeight_sum K nodes hK hh)
    (2 * K / (Real.pi * (h : ℝ) * quadratureMass K nodes))
    (normalizedWeight_le K nodes hK hh)
  convert h using 1
  congr 1
  rw [div_div]
  congr 1
  ring

def uniformRightNodes (K : ℝ) (h : ℕ) (j : Fin h) : ℝ :=
  -K + ((j : ℝ) + 1) * (2 * K / (h : ℝ))

def cubicCutoff (κ : ℝ) (h : ℕ) : ℝ := κ * (h : ℝ) ^ (1 / 3 : ℝ)

def UniformMassConvergence (κ : ℝ) : Prop :=
  Filter.Tendsto (fun h : ℕ => quadratureMass (cubicCutoff κ h)
    (uniformRightNodes (cubicCutoff κ h) h)) Filter.atTop (nhds 1)

def SourceSamplingScaling {N : ℕ} (κ : ℝ)
    (p : (h : ℕ) → Fin h → FinDist (Fin N)) : Prop :=
  Asymptotics.IsBigO (Filter.atTop : Filter (ℕ × ℕ))
    (fun b : ℕ × ℕ => (recordsLaw (p b.1) b.2).expect
      (l2Error (p b.1) (normalizedWeight (cubicCutoff κ b.1)
        (uniformRightNodes (cubicCutoff κ b.1) b.1))))
    (fun b : ℕ × ℕ => (b.2 : ℝ) ^ (-(1 / 2 : ℝ)) * (b.1 : ℝ) ^ (-(1 / 3 : ℝ)))

end Qatlib.Concepts.KoopmanFlow.Sampling
