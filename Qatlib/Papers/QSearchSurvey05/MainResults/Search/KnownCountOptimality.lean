/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountDefs
import Qatlib.Concepts.SearchStopping.PaidRestart.Section31ExactSuccessTigh
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Known count Grover budgets

This module defines the Grover angle and integer query count used in the known marked count
discussion of [Ambainis2005]. The theorems `fact2_known_count_upper` and
`fact2_quarter_density_exact` give a general ceiling budget upper bound and establish that one
query is the least exact budget at marked density one quarter.

## Main statements

* `fact2_known_count_upper`: Exhibits a known count search upper bound with error one half.
* `fact2_quarter_density_exact`: Proves exact one query optimality at quarter density.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- The Grover angle arcsin(√(k/N)) for k marked items among N addresses. -/
noncomputable def groverAngle (N k : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt ((k : ℝ) / (N : ℝ)))

/-- The integer candidate query count ⌈π/(4θ) − 1/2⌉ determined by `groverAngle`. -/
noncomputable def exactOptimalQueryCount (N k : ℕ) : ℕ :=
  Nat.ceil (Real.pi / (4 * groverAngle N k) - 1 / 2)

/-- The real Grover budget π/(4√(k/N)). -/
noncomputable def groverOptimalBudget (N k : ℕ) : ℝ :=
  Real.pi / (4 * Real.sqrt ((k : ℝ) / (N : ℝ)))

/-- For 0 < k ≤ N, the integer candidate count is at most the ceiling of the real Grover budget.
See [Ambainis2005]. -/
theorem fact2_ceiling_budget_witness {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (hkN : k ≤ N) :
    exactOptimalQueryCount N k ≤ Nat.ceil (groverOptimalBudget N k) := by
  unfold exactOptimalQueryCount groverOptimalBudget groverAngle
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hypos : 0 < Real.sqrt ((k : ℝ) / (N : ℝ)) :=
    Real.sqrt_pos.mpr (div_pos hkpos hNpos)
  have hy1 : Real.sqrt ((k : ℝ) / (N : ℝ)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact (div_le_one hNpos).mpr (by exact_mod_cast hkN)
  have hsiny : Real.sin (Real.sqrt ((k : ℝ) / (N : ℝ))) ≤
      Real.sqrt ((k : ℝ) / (N : ℝ)) :=
    le_of_lt (Real.sin_lt hypos)
  have hy_pi : Real.sqrt ((k : ℝ) / (N : ℝ)) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have harcsin : Real.sqrt ((k : ℝ) / (N : ℝ)) ≤
      Real.arcsin (Real.sqrt ((k : ℝ) / (N : ℝ))) := by
    have := Real.arcsin_le_arcsin hsiny
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) hy_pi] at this
  have hanglepos : 0 < Real.arcsin (Real.sqrt ((k : ℝ) / (N : ℝ))) :=
    lt_of_lt_of_le hypos harcsin
  apply Nat.ceil_mono
  have hfrac : Real.pi / (4 * Real.arcsin (Real.sqrt ((k : ℝ) / (N : ℝ)))) ≤
      Real.pi / (4 * Real.sqrt ((k : ℝ) / (N : ℝ))) := by
    exact div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ Real.pi)
      (by positivity : (0 : ℝ) < 4 * Real.sqrt ((k : ℝ) / (N : ℝ)))
      (by linarith)
  linarith

/-- For 0 < k and 2k ≤ N, known count search has a fixed space upper bound with error one half
and query count at most the ceiling of the Grover budget. See [Ambainis2005]. -/
theorem fact2_known_count_upper {N k : ℕ} (hk : 0 < k) (hkN : 2 * k ≤ N) :
    ∃ t : ℕ,
      FixedSpaceQueryUpperBound
        (fun A : KnownMarkedSets (Fin N) k => SetOracle A.val) (fun A => A.val) (1 / 2) t ∧
      (t : ℝ) ≤ Nat.ceil (groverOptimalBudget N k) := by
  have hcard : Fintype.card (Fin N) = N := Fintype.card_fin N
  have hkN' : 2 * k ≤ Fintype.card (Fin N) := by rw [hcard]; exact hkN
  obtain ⟨t, hupper, hbudget⟩ := knownCount_searchClaim (I := Fin N) (m := k) hk hkN'
  refine ⟨t, hupper, ?_⟩
  have hbud : (t : ℝ) ≤ groverOptimalBudget N k := by
    simpa only [groverOptimalBudget, Fintype.card_fin] using hbudget
  exact hbud.trans (Nat.le_ceil _)

/-- For positive m, the candidate exact query count for m marked items among 4m addresses is
one. See [Ambainis2005]. -/
theorem exactOptimalQueryCount_quarter (m : ℕ) (hm : 0 < m) :
    exactOptimalQueryCount (4 * m) m = 1 := by
  unfold exactOptimalQueryCount groverAngle
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv : ((m : ℝ) / (((4 * m : ℕ) : ℝ))) = 1 / 4 := by
    push_cast
    field_simp
  rw [hdiv]
  have hsqrt : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  have harc : Real.arcsin ((1 : ℝ) / 2) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [harc]
  have hval : Real.pi / (4 * (Real.pi / 6)) - 1 / 2 = 1 := by
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring
  rw [hval]
  exact Nat.ceil_one

/-- For positive m, no zero query fixed space algorithm finds a marked item with zero error for
every m element subset of 4m addresses. -/
theorem quarterDensity_no_zero_query (m : ℕ) (hm : 0 < m) :
    ¬ FixedSpaceQueryUpperBound
      (fun A : KnownMarkedSets (Fin (4 * m)) m => SetOracle A.val)
      (fun A => A.val) 0 0 := by
  rintro ⟨hε, hO, C, ψ₀, hC, hψ₀, hcount, hsolve⟩
  have hq0 : QueryCount C = 0 := Nat.le_zero.mp hcount
  set ψ : QState (Fin (4 * m)) := Run (1 : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ) C ψ₀
    with hψdef
  have hrun : ∀ A : KnownMarkedSets (Fin (4 * m)) m,
      Run (SetOracle A.val) C ψ₀ = ψ := by
    intro A
    exact run_eq_of_queryCount_eq_zero _ _ C hq0 ψ₀
  have hnorm : Normalized ψ :=
    normalized_run _ (Submonoid.one_mem _) C hC hψ₀

  have hcarduniv : (Finset.univ : Finset (Fin (4 * m))).card = 4 * m := by
    rw [Finset.card_univ, Fintype.card_fin]
  obtain ⟨A, -, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (4 * m)))) (n := m)
      (by rw [hcarduniv]; omega)
  have hcompl : m ≤ (Aᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, hAcard]; omega
  obtain ⟨B, hBsub, hBcard⟩ :=
    Finset.exists_subset_card_eq (s := Aᶜ) (n := m) hcompl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_compl.mp (hBsub hxB)) hxA
  have hA1 : (1 : ℝ) ≤ MeasureProb ψ A := by
    have h := hsolve ⟨A, hAcard⟩
    rw [hrun ⟨A, hAcard⟩] at h
    simpa using h
  have hB1 : (1 : ℝ) ≤ MeasureProb ψ B := by
    have h := hsolve ⟨B, hBcard⟩
    rw [hrun ⟨B, hBcard⟩] at h
    simpa using h
  have hunion : MeasureProb ψ (A ∪ B) = MeasureProb ψ A + MeasureProb ψ B := by
    rw [MeasureProb, MeasureProb, MeasureProb, Finset.sum_union hdisj]
  have hle : MeasureProb ψ (A ∪ B) ≤ 1 := by
    rw [← measureProb_univ hnorm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => bornProb_nonneg ψ i)
  linarith

/-- At marked density one quarter, `exactOptimalQueryCount` is the least query budget for a zero
error fixed space search upper bound. See [Ambainis2005]. -/
theorem fact2_quarter_density_exact (m : ℕ) (hm : 0 < m) :
    IsLeast
      { t : ℕ |
        FixedSpaceQueryUpperBound
          (fun A : KnownMarkedSets (Fin (4 * m)) m => SetOracle A.val)
          (fun A => A.val) 0 t }
      (exactOptimalQueryCount (4 * m) m) := by
  rw [exactOptimalQueryCount_quarter m hm]
  refine ⟨?_, ?_⟩
  · exact section3_1ExactSuccess (Fin (4 * m)) m hm (by simp)
  · intro t ht
    by_contra hlt
    have ht0 : t = 0 := by omega
    subst ht0
    exact quarterDensity_no_zero_query m hm ht

end Qatlib.Papers.QSearchSurvey05.MainResults
