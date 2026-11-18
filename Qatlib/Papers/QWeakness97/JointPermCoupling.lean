/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWeakness97.RandomPermOracle
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Theorem 3.6: joint oracle/fresh-string coupling

This module joins the two finite randomness sources used by the permutation-oracle hybrid
argument. `jointPermFreshDraw` is the product of the uniform permutation-oracle draw and the
uniform draw of the fresh-string tuple. Its point masses factor, its marginals are the two
original laws, and expectations of separated products factor; the sources are therefore
independent by construction, rather than identified with one another.

On the dynamical side, `mixRunDist_telescope` instantiates `Qatlib.Papers.QWeakness97.MainResults.PermCoupling.hybDist` for the
transposition chain, `chainStep_telescope_atom` records the one-step action decomposition and
its exact two-point disagreement scope, and `avgDistMix` converts `Qatlib.Papers.QWeakness97.MainResults.PermCoupling.avgCharge`
into a finite Cauchy--Schwarz distance estimate. The main theorem
`jointMixRun_expectedDist_le` normalizes that estimate under the joint product law, giving an
expected Euclidean-distance bound for a uniformly drawn seed oracle and an independent
`T`-step fresh-string chain.

These are finite probability and finite hybrid estimates only. They do not prove Theorem 3.6,
any probability-one transport, a countable-QTM or all-lengths uniform statement, an
`OReg`-truth-table representation bridge, an NP∩coNP/BQTime separation, or any asymptotic
claim. The permutation action remains the restricted in-place model documented by
`Qatlib.Papers.QWeakness97.MainResults.PermCoupling`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.QWeakness97.MainResults.PermCoupling
open Qatlib.Papers.QWeakness97.RandomPermOracle
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QWeakness97.JointPermCoupling

variable {I : Type} [Fintype I] [DecidableEq I]

/-! ## The independent joint law -/

/-- The uniform law on the fresh-string tuple used by a `T`-step transposition chain. The
tuple has coordinates `0, ..., T`, exactly as required by `extSeq T` and `mixRun T`. -/
noncomputable def freshStringDraw (T : ℕ) [Nonempty I] : FinDist (Fin (T + 1) → I) :=
  unifDist _

omit [DecidableEq I] in
/-- Every fresh-string tuple has the inverse-cardinality mass under the uniform fresh-string
law. -/
theorem freshStringDraw_prob [Nonempty I] (T : ℕ) (r : Fin (T + 1) → I) :
    (freshStringDraw (I := I) T).prob r
      = ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹ := rfl

/-- The joint law of an independently drawn uniform permutation oracle and uniform fresh-string
tuple. This is a product distribution on the product sample space, not a conditioning or a
single-source reindexing. -/
noncomputable def jointPermFreshDraw (T : ℕ) [Nonempty I] :
    FinDist (Equiv.Perm I × (Fin (T + 1) → I)) :=
  FinDist.independentPair (permOracleDraw (I := I)) (freshStringDraw (I := I) T)

/-- The joint mass of an oracle/fresh-string pair is the product of its two marginal masses. -/
theorem jointPermFreshDraw_prob [Nonempty I] (T : ℕ) (σ : Equiv.Perm I)
    (r : Fin (T + 1) → I) :
    (jointPermFreshDraw (I := I) T).prob (σ, r)
      = (permOracleDraw (I := I)).prob σ * (freshStringDraw (I := I) T).prob r := rfl

/-- Expectations of products of separate oracle and fresh-string payoffs factor under the joint
law. This is the expectation form of independence of the two randomness sources. -/
theorem jointPermFreshDraw_expect_mul [Nonempty I] (T : ℕ) (F : Equiv.Perm I → ℝ)
    (G : (Fin (T + 1) → I) → ℝ) :
    (jointPermFreshDraw (I := I) T).expect (fun z => F z.1 * G z.2)
      = (permOracleDraw (I := I)).expect F * (freshStringDraw (I := I) T).expect G := by
  classical
  change (∑ z : Equiv.Perm I × (Fin (T + 1) → I),
      ((permOracleDraw (I := I)).prob z.1 * (freshStringDraw (I := I) T).prob z.2)
        * (F z.1 * G z.2))
    = (∑ σ, (permOracleDraw (I := I)).prob σ * F σ)
        * (∑ r, (freshStringDraw (I := I) T).prob r * G r)
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ σ r,
      ((permOracleDraw (I := I)).prob σ * (freshStringDraw (I := I) T).prob r)
          * (F σ * G r)
        = ((permOracleDraw (I := I)).prob σ * F σ)
          * ((freshStringDraw (I := I) T).prob r * G r) by
    intros; ring]
  rw [Finset.sum_mul_sum]

/-- The oracle marginal of the joint law is exactly the uniform permutation-oracle
 draw. -/
theorem jointPermFreshDraw_expect_oracle [Nonempty I] (T : ℕ) (F : Equiv.Perm I → ℝ) :
    (jointPermFreshDraw (I := I) T).expect (fun z => F z.1)
      = (permOracleDraw (I := I)).expect F := by
  classical
  have h := jointPermFreshDraw_expect_mul (I := I) T F (fun _ => (1 : ℝ))
  simpa only [mul_one, FinDist.expect_const] using h

/-- The fresh-string marginal of the joint law is exactly the uniform fresh-string draw. -/
theorem jointPermFreshDraw_expect_fresh [Nonempty I] (T : ℕ)
    (G : (Fin (T + 1) → I) → ℝ) :
    (jointPermFreshDraw (I := I) T).expect (fun z => G z.2)
      = (freshStringDraw (I := I) T).expect G := by
  classical
  have h := jointPermFreshDraw_expect_mul (I := I) T (fun _ => (1 : ℝ)) G
  simpa only [one_mul, FinDist.expect_const] using h

omit [DecidableEq I] in
/-- The number of fresh-string tuples of length `T + 1` is `|I| ^ (T + 1)`. -/
theorem card_freshString (T : ℕ) :
    Fintype.card (Fin (T + 1) → I) = (Fintype.card I) ^ (T + 1) := by
  rw [Fintype.card_pi]
  simp

/-! ## The transposition-chain telescope -/

/-- The one-step oracle deviation along the mixed transposition-chain trajectory at step `k`,
compared with the final oracle at stage `T`. -/
noncomputable def mixStepDist (T : ℕ) (π0 : Equiv.Perm I) (r : Fin (T + 1) → I)
    (U : ℕ → Matrix I I ℂ) (init : QState I) (k : ℕ) : ℝ :=
  ‖toEuclidean_fromVec
    (permAct (chainPerm π0 (extSeq T r) k) (mixRun T π0 r U init k)
      - permAct (chainPerm π0 (extSeq T r) T) (mixRun T π0 r U init k))‖

/-- The Euclidean distance between the `T`-step mixed-chain run and the run using its final
oracle at every step. -/
noncomputable def mixRunDist (T : ℕ) (π0 : Equiv.Perm I) (r : Fin (T + 1) → I)
    (U : ℕ → Matrix I I ℂ) (init : QState I) : ℝ :=
  ‖toEuclidean_fromVec (mixRun T π0 r U init T
    - oracleRun (fun _ => chainPerm π0 (extSeq T r) T) U init T)‖

/-- The mixed-chain telescope: the final run distance is at most the sum of the oracle
deviations along the mixed trajectory. This is `Qatlib.Papers.QWeakness97.MainResults.PermCoupling.hybDist` specialized to
`chainPerm π0 (extSeq T r)`. -/
theorem mixRunDist_telescope (T : ℕ) (π0 : Equiv.Perm I) (r : Fin (T + 1) → I)
    (U : ℕ → Matrix I I ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (init : QState I) :
    mixRunDist T π0 r U init ≤ ∑ k ∈ Finset.range T, mixStepDist T π0 r U init k := by
  exact hybDist (fun t => chainPerm π0 (extSeq T r) t)
    (chainPerm π0 (extSeq T r) T) U hU init T

/-- The atomic transposition-chain step combines the action decomposition with the exact
 disagreement scope: the new action is the transposition action followed by the old action,
 and the squared oracle perturbation is bounded by four times the mass on the two swapped
 inputs. -/
theorem chainStep_telescope_atom (π0 : Equiv.Perm I) (xs : ℕ → I) (k : ℕ) (ψ : QState I)
    (hxs : xs k ≠ xs (k + 1)) :
    permAct (chainPerm π0 xs (k + 1)) ψ
        = permAct (chainPerm π0 xs k) (permAct (Equiv.swap (xs k) (xs (k + 1))) ψ)
      ∧ ‖toEuclidean_fromVec
          (permAct (chainPerm π0 xs (k + 1)) ψ - permAct (chainPerm π0 xs k) ψ)‖ ^ 2
        ≤ 4 * ∑ y ∈ ({xs k, xs (k + 1)} : Finset I), ‖ψ y‖ ^ 2 := by
  refine ⟨permAct_chainPerm_succ π0 xs k ψ, ?_⟩
  rw [norm_toEuclidean_fromVec_sq]
  have hset : differSet (chainPerm π0 xs (k + 1)) (chainPerm π0 xs k)
      = {xs k, xs (k + 1)} := by
    rw [chainPerm_succ]
    exact differSet_updateSwap _ hxs
  rw [← hset]
  exact permDiff_le _ _ _

/-- The squared one-step distance against the final oracle is bounded by four times the mixed
state's mass on the corresponding chain disagreement set. -/
theorem mixStepDist_sq_le (T : ℕ) (π0 : Equiv.Perm I) (r : Fin (T + 1) → I)
    (U : ℕ → Matrix I I ℂ) (init : QState I) (k : ℕ) :
    (mixStepDist T π0 r U init k) ^ 2
      ≤ 4 * ∑ y ∈ differSet (chainPerm π0 (extSeq T r) k)
          (chainPerm π0 (extSeq T r) T), ‖mixRun T π0 r U init k y‖ ^ 2 := by
  unfold mixStepDist
  rw [norm_toEuclidean_fromVec_sq]
  exact permDiff_le _ _ _

/-- Cauchy--Schwarz over the fresh-string tuples, followed by `Qatlib.Papers.QWeakness97.MainResults.PermCoupling.avgCharge`, bounds
the squared summed distance at each reached step by the explicit finite charge expression. -/
theorem sum_mixStepDist_sq_le [Nonempty I] {T k : ℕ} (hk : k < T)
    (π0 : Equiv.Perm I) (U : ℕ → Matrix I I ℂ)
    (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ) (init : QState I)
    (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1) :
    (∑ r : Fin (T + 1) → I, mixStepDist T π0 r U init k) ^ 2
      ≤ (2 * ((Fintype.card I : ℝ) ^ T)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2 := by
  classical
  have hcardpos : (0 : ℝ) < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcs : (∑ r : Fin (T + 1) → I, mixStepDist T π0 r U init k) ^ 2
      ≤ (Fintype.card (Fin (T + 1) → I) : ℝ)
        * ∑ r : Fin (T + 1) → I, (mixStepDist T π0 r U init k) ^ 2 := by
    exact_mod_cast (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin (T + 1) → I)))
      (f := fun r => mixStepDist T π0 r U init k))
  have hchg := avgCharge (I := I) T T k hk (Nat.le_of_lt hk) (le_refl T)
    π0 U hU init hinit
  have hsumSq : (∑ r : Fin (T + 1) → I, (mixStepDist T π0 r U init k) ^ 2)
      ≤ 4 * (((T + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ T)) := by
    calc (∑ r : Fin (T + 1) → I, (mixStepDist T π0 r U init k) ^ 2)
        ≤ ∑ r : Fin (T + 1) → I, 4 * ∑ y ∈ differSet
            (chainPerm π0 (extSeq T r) k) (chainPerm π0 (extSeq T r) T),
            ‖mixRun T π0 r U init k y‖ ^ 2 :=
          Finset.sum_le_sum fun r _ => mixStepDist_sq_le T π0 r U init k
      _ = 4 * ∑ r : Fin (T + 1) → I, ∑ y ∈ differSet
            (chainPerm π0 (extSeq T r) k) (chainPerm π0 (extSeq T r) T),
            ‖mixRun T π0 r U init k y‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * (((T + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ T)) :=
          mul_le_mul_of_nonneg_left hchg (by norm_num)
  have hpow : (2 * ((Fintype.card I : ℝ) ^ T)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2
      = ((Fintype.card I : ℝ) ^ (T + 1))
        * (4 * (((T + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ T))) := by
    have hK : (0 : ℝ) ≤ ((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ) := by
      positivity
    have e1 : (2 * ((Fintype.card I : ℝ) ^ T)
          * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2
        = (2 : ℝ) ^ 2 * (((Fintype.card I : ℝ) ^ T) ^ 2)
          * (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hK]
    have e1' : (2 : ℝ) ^ 2 * (((Fintype.card I : ℝ) ^ T) ^ 2)
          * (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))
        = 4 * ((Fintype.card I : ℝ) ^ (T + T))
          * (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
      rw [show (2 : ℝ) ^ 2 = 4 by norm_num, sq, ← pow_add]
    have e2 : 4 * ((Fintype.card I : ℝ) ^ (T + T))
          * (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))
        = ((Fintype.card I : ℝ) ^ (T + 1))
          * (4 * (((T + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ T))) := by
      rw [pow_succ, pow_add]
      ring
    rw [e1, e1', e2]
  calc (∑ r : Fin (T + 1) → I, mixStepDist T π0 r U init k) ^ 2
      ≤ (Fintype.card (Fin (T + 1) → I) : ℝ)
        * ∑ r : Fin (T + 1) → I, (mixStepDist T π0 r U init k) ^ 2 := hcs
    _ = ((Fintype.card I : ℝ) ^ (T + 1))
        * ∑ r : Fin (T + 1) → I, (mixStepDist T π0 r U init k) ^ 2 := by
        rw [card_freshString]
        push_cast
        ring
    _ ≤ ((Fintype.card I : ℝ) ^ (T + 1))
        * (4 * (((T + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ T))) :=
        mul_le_mul_of_nonneg_left hsumSq (by positivity)
    _ = (2 * ((Fintype.card I : ℝ) ^ T)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2 := hpow.symm

/-- Taking nonnegative square roots in the summed squared-distance estimate gives the explicit
per-step distance contribution of the fresh-string average. -/
theorem sum_mixStepDist_le [Nonempty I] {T k : ℕ} (hk : k < T)
    (π0 : Equiv.Perm I) (U : ℕ → Matrix I I ℂ)
    (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ) (init : QState I)
    (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1) :
    (∑ r : Fin (T + 1) → I, mixStepDist T π0 r U init k)
      ≤ 2 * ((Fintype.card I : ℝ) ^ T)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
  have hsquare := sum_mixStepDist_sq_le (I := I) hk π0 U hU init hinit
  have e1 : (∑ r : Fin (T + 1) → I, mixStepDist T π0 r U init k)
      = Real.sqrt ((∑ r : Fin (T + 1) → I, mixStepDist T π0 r U init k) ^ 2) :=
    (Real.sqrt_sq (Finset.sum_nonneg fun r _ => by
      unfold mixStepDist
      exact norm_nonneg _)).symm
  have e2 : 2 * ((Fintype.card I : ℝ) ^ T)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))
      = Real.sqrt ((2 * ((Fintype.card I : ℝ) ^ T)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [e1, e2]
  exact Real.sqrt_le_sqrt hsquare

/-- The unnormalized fresh-string average of the full `T`-step hybrid distance is bounded by
the finite square-root sum obtained from `avgCharge` at every step. -/
theorem avgDistMix [Nonempty I] (T : ℕ) (π0 : Equiv.Perm I)
    (U : ℕ → Matrix I I ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (init : QState I) (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1) :
    (∑ r : Fin (T + 1) → I, mixRunDist T π0 r U init)
      ≤ ∑ k ∈ Finset.range T, 2 * ((Fintype.card I : ℝ) ^ T)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
  classical
  calc (∑ r : Fin (T + 1) → I, mixRunDist T π0 r U init)
      ≤ ∑ r : Fin (T + 1) → I, ∑ k ∈ Finset.range T, mixStepDist T π0 r U init k :=
        Finset.sum_le_sum fun r _ => mixRunDist_telescope T π0 r U hU init
    _ = ∑ k ∈ Finset.range T, ∑ r : Fin (T + 1) → I, mixStepDist T π0 r U init k :=
        Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range T, 2 * ((Fintype.card I : ℝ) ^ T)
          * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) :=
        Finset.sum_le_sum fun k hk =>
          sum_mixStepDist_le (I := I) (Finset.mem_range.mp hk) π0 U hU init hinit

/-! ## Expected distance under the joint draw -/

/-- **Joint-draw hybrid distance bound.** For a uniformly drawn seed permutation and an
independently drawn fresh-string tuple, the expected distance between the `T`-step mixed-chain
run and the run under its final oracle is at most
`Σ_{k<T} (2 / |I|) √((T + 1 - k) |I|)`. The proof telescopes with `hybDist`, prices each step
with `avgCharge`, and uses the product masses to normalize both independent randomness sources.
This is a finite expectation bound, not an asymptotic or separation statement. -/
theorem jointMixRun_expectedDist_le [Nonempty I] (T : ℕ)
    (U : ℕ → Matrix I I ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (init : QState I) (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1) :
    (jointPermFreshDraw (I := I) T).expect (fun z => mixRunDist T z.1 z.2 U init)
      ≤ ∑ k ∈ Finset.range T, 2 / (Fintype.card I : ℝ)
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
  classical
  have hcardpos : (0 : ℝ) < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have havg : ∀ π0 : Equiv.Perm I,
      (∑ r : Fin (T + 1) → I, mixRunDist T π0 r U init)
        ≤ ∑ k ∈ Finset.range T, 2 * ((Fintype.card I : ℝ) ^ T)
          * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) :=
    fun π0 => avgDistMix T π0 U hU init hinit
  change (∑ z : Equiv.Perm I × (Fin (T + 1) → I),
      ((permOracleDraw (I := I)).prob z.1 * (freshStringDraw (I := I) T).prob z.2)
        * mixRunDist T z.1 z.2 U init) ≤ _
  rw [Fintype.sum_prod_type]
  simp_rw [freshStringDraw_prob]
  calc (∑ π0 : Equiv.Perm I, ∑ r : Fin (T + 1) → I,
        ((permOracleDraw (I := I)).prob π0
          * ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹) * mixRunDist T π0 r U init)
      = ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹
          * ∑ π0 : Equiv.Perm I, (permOracleDraw (I := I)).prob π0
            * (∑ r : Fin (T + 1) → I, mixRunDist T π0 r U init) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun π0 _ => ?_
        calc (∑ r : Fin (T + 1) → I,
              ((permOracleDraw (I := I)).prob π0
                * ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹) * mixRunDist T π0 r U init)
            = ((permOracleDraw (I := I)).prob π0
                * ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹)
              * (∑ r : Fin (T + 1) → I, mixRunDist T π0 r U init) :=
              (Finset.mul_sum _ _ _).symm
          _ = ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹
              * ((permOracleDraw (I := I)).prob π0
                * (∑ r : Fin (T + 1) → I, mixRunDist T π0 r U init)) := by ring
    _ ≤ ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹
          * ∑ π0 : Equiv.Perm I, (permOracleDraw (I := I)).prob π0
            * (∑ k ∈ Finset.range T, 2 * ((Fintype.card I : ℝ) ^ T)
              * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π0 _ =>
          mul_le_mul_of_nonneg_left (havg π0) ((permOracleDraw (I := I)).nonneg π0)) ?_
        positivity
    _ = ((Fintype.card (Fin (T + 1) → I) : ℕ) : ℝ)⁻¹
          * (∑ k ∈ Finset.range T, 2 * ((Fintype.card I : ℝ) ^ T)
            * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) := by
        rw [← Finset.sum_mul, (permOracleDraw (I := I)).sum_one, one_mul]
    _ = ∑ k ∈ Finset.range T, 2 / (Fintype.card I : ℝ)
          * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [card_freshString]
        push_cast
        rw [pow_succ]
        field_simp [ne_of_gt hcardpos]

end Qatlib.Papers.QWeakness97.JointPermCoupling
