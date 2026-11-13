/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalStat
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Iteration choice for known-count Grover search

`groverIterations` rounds π/(4θ) down to a natural number, and `knownCountAngle` represents a
marked fraction by arcsin(√p). The phase and success estimates establish
`knownCount_searchClaim`, with a common circuit for all marked sets of the specified size.

For the mathematical background, see [Grover1997].

## Main statements

* `knownCount_searchClaim`: For a positive marked count at most half the search-space size,
  `KnownCountSearchClaim` holds. See [Ambainis2005].

## References

* [Grover, 1997][Grover1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The natural floor of π/(4θ), used as the known-count Grover iteration count. -/
noncomputable def groverIterations (θ : ℝ) : ℕ := ⌊Real.pi / (4 * θ)⌋₊

/-- For θ > 0, the final angle after `groverIterations θ` iterations differs from π/2 by at most
θ. -/
theorem groverIterations_phase_error {θ : ℝ} (hθ : 0 < θ) :
    |(2 * (groverIterations θ : ℝ) + 1) * θ - Real.pi / 2| ≤ θ := by
  have hd : 0 < 4 * θ := by positivity
  have hlo := Nat.floor_le (show 0 ≤ Real.pi / (4 * θ) by positivity)
  have hhi := Nat.lt_floor_add_one (Real.pi / (4 * θ))
  have hlo' : (groverIterations θ : ℝ) * (4 * θ) ≤ Real.pi :=
    (le_div_iff₀ hd).mp hlo
  have hhi' : Real.pi < ((groverIterations θ : ℝ) + 1) * (4 * θ) :=
    (div_lt_iff₀ hd).mp hhi
  apply abs_le.mpr
  constructor <;> nlinarith

/-- For 0 < θ ≤ π/2, the prescribed iteration count yields sine-square success at least 1 −
sin²(θ). -/
theorem groverIterations_success {θ : ℝ} (hθ : 0 < θ) (hθπ : θ ≤ Real.pi / 2) :
    1 - (Real.sin θ) ^ 2 ≤
      (Real.sin ((2 * (groverIterations θ : ℝ) + 1) * θ)) ^ 2 := by
  let δ := (2 * (groverIterations θ : ℝ) + 1) * θ - Real.pi / 2
  have hδ : |δ| ≤ θ := groverIterations_phase_error hθ
  have habs : Real.cos |δ| = Real.cos δ := by
    rcases le_total 0 δ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.cos_neg]
  have hcos : Real.cos θ ≤ Real.cos δ := by
    rw [← habs]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ)
      (by linarith [Real.pi_pos]) hδ
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθπ⟩
  have hsq : (Real.cos θ) ^ 2 ≤ (Real.cos δ) ^ 2 := by nlinarith
  have hid : Real.cos δ = Real.sin ((2 * (groverIterations θ : ℝ) + 1) * θ) :=
    Real.cos_sub_pi_div_two _
  rw [hid] at hsq
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- For θ > 0 and sin(θ) > 0, the iteration count is at most π/(4 sin(θ)). -/
theorem groverIterations_le {θ : ℝ} (hθ : 0 < θ) (hs : 0 < Real.sin θ) :
    (groverIterations θ : ℝ) ≤ Real.pi / (4 * Real.sin θ) := by
  calc
    (groverIterations θ : ℝ) ≤ Real.pi / (4 * θ) :=
      Nat.floor_le (by positivity)
    _ ≤ Real.pi / (4 * Real.sin θ) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
        (by nlinarith [Real.sin_le hθ.le])

/-- The Grover angle arcsin(√p) associated with marked fraction p. -/
noncomputable def knownCountAngle (p : ℝ) : ℝ := Real.arcsin (Real.sqrt p)

/-- For 0 < p < 1, `knownCountAngle p` lies strictly between zero and π/2, has sine √p and sine
square p, and has nonzero cosine. -/
theorem knownCountAngle_spec {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < knownCountAngle p ∧ knownCountAngle p < Real.pi / 2 ∧
      Real.sin (knownCountAngle p) = Real.sqrt p ∧
      (Real.sin (knownCountAngle p)) ^ 2 = p ∧
      Real.cos (knownCountAngle p) ≠ 0 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos_of_pos hp
  have hs1 : Real.sqrt p < 1 := by nlinarith [Real.sq_sqrt hp.le]
  have hpos : 0 < knownCountAngle p := Real.arcsin_pos.mpr hs
  have hlt : knownCountAngle p < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hsin : Real.sin (knownCountAngle p) = Real.sqrt p :=
    Real.sin_arcsin (by linarith) hs1.le
  refine ⟨hpos, hlt, hsin, ?_, ?_⟩
  · rw [hsin, Real.sq_sqrt hp.le]
  · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩).ne'

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- For marked count 0 < m < N, Grover search at the prescribed angle and iteration count
succeeds with probability at least 1 − m/N. -/
theorem knownCount_success (hN : 0 < Fintype.card I) (A : Finset I)
    {m : ℕ} (hA : A.card = m) (hm : 0 < m) (hmN : m < Fintype.card I) :
    1 - (m : ℝ) / Fintype.card I ≤
      MeasureProb (GroverState A
        (groverIterations (knownCountAngle ((m : ℝ) / Fintype.card I)))) A := by
  have hNr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 < (m : ℝ) / Fintype.card I := div_pos hmr hNr
  have hp1 : (m : ℝ) / Fintype.card I < 1 :=
    (div_lt_one hNr).mpr (by exact_mod_cast hmN)
  obtain ⟨hpos, hlt, hsin, hsq, hcos⟩ := knownCountAngle_spec hp hp1
  have hs : Real.sin (knownCountAngle ((m : ℝ) / Fintype.card I)) ≠ 0 := by
    rw [hsin]
    exact (Real.sqrt_pos_of_pos hp).ne'
  rw [measureProb_groverState hN A _ (by simpa [hA] using hsq) hs hcos]
  simpa only [hsq] using groverIterations_success hpos hlt.le

set_option maxHeartbeats 800000 in

/-- For 0 < m and 2m ≤ N, the prescribed iteration count gives a fixed-space query upper bound
for all m-element marked sets with success at least 1/2. See [BihamEtAl1999]. -/
theorem knownCount_query_upper {m : ℕ} (hm : 0 < m) (hmN : 2 * m ≤ Fintype.card I) :
    FixedSpaceQueryUpperBound
      (fun A : KnownMarkedSets I m => SetOracle A.val) (fun A => A.val) (1 / 2)
      (groverIterations (knownCountAngle ((m : ℝ) / Fintype.card I))) := by
  have hN : 0 < Fintype.card I := by omega
  have hmN' : m < Fintype.card I := by omega
  have hNr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hmNr : (2 : ℝ) * m ≤ Fintype.card I := by exact_mod_cast hmN
  have hpHalf : (m : ℝ) / Fintype.card I ≤ 1 / 2 :=
    (div_le_iff₀ hNr).mpr (by nlinarith)
  let k := groverIterations (knownCountAngle ((m : ℝ) / Fintype.card I))
  let algorithm : QueryAlgorithm I :=
    ⟨GroverCircuit I k, Uniform I,
      isUnitaryCircuit_groverCircuit hN k, normalized_uniform hN⟩
  have hcount : QueryCount algorithm.circuit ≤ k :=
    (queryCount_groverCircuit (I := I) k).le
  have hsolve : SolvesWithError
      (fun A : KnownMarkedSets I m => SetOracle A.val) (fun A => A.val)
      algorithm.circuit algorithm.start (1 / 2) := by
    intro A
    change 1 - (1 / 2 : ℝ) ≤ MeasureProb (GroverState A.val k) A.val
    have hsuccess := knownCount_success hN A.val A.property hm hmN'
    change 1 - (m : ℝ) / Fintype.card I ≤ MeasureProb (GroverState A.val k) A.val
      at hsuccess
    linarith
  exact algorithm.queryUpperBound (by norm_num)
    (fun A : KnownMarkedSets I m => setOracle_unitary A.val) hcount hsolve

omit [DecidableEq I] in

/-- For 0 < m < N, the prescribed known-count iteration count is at most π/(4√(m/N)). -/
theorem knownCount_query_budget {m : ℕ} (hm : 0 < m) (hmN : m < Fintype.card I) :
    (groverIterations (knownCountAngle ((m : ℝ) / Fintype.card I)) : ℝ) ≤
      Real.pi / (4 * Real.sqrt ((m : ℝ) / Fintype.card I)) := by
  have hN : 0 < Fintype.card I := lt_trans hm hmN
  have hp : 0 < (m : ℝ) / Fintype.card I := div_pos
    (by exact_mod_cast hm) (by exact_mod_cast hN)
  have hp1 : (m : ℝ) / Fintype.card I < 1 :=
    (div_lt_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hmN)
  obtain ⟨hpos, _, hsin, _, _⟩ := knownCountAngle_spec hp hp1
  simpa only [hsin] using groverIterations_le hpos
    (show 0 < Real.sin (knownCountAngle ((m : ℝ) / Fintype.card I)) by
      rw [hsin]; exact Real.sqrt_pos_of_pos hp)

/-- For a positive marked count at most half the search-space size, `KnownCountSearchClaim`
holds. See [Ambainis2005]. -/
theorem knownCount_searchClaim {m : ℕ} (hm : 0 < m) (hmN : 2 * m ≤ Fintype.card I) :
    KnownCountSearchClaim I m := by
  refine ⟨groverIterations (knownCountAngle ((m : ℝ) / Fintype.card I)),
    knownCount_query_upper hm hmN, knownCount_query_budget hm ?_⟩
  omega

/-- Establishes the universal known-count search upper-bound proposition
`Section3KnownCountSubgoal`. -/
theorem section3KnownCountSubgoal : Section3KnownCountSubgoal := by
  intro I _ _ m hm hmN
  exact knownCount_searchClaim hm hmN

end Qatlib.Concepts.SearchStopping.KnownCount
