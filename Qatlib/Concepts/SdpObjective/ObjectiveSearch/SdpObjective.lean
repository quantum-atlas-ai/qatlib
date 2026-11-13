/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.SdpObjective.ObjectiveSearch.SdpObjectiveSearchDefs

/-!
# Objective bisection for the diamond norm SDP

`searchLoop_spec` proves an invariant, interval contraction, and oracle-call bound for rational
objective bisection. `g1` uses a Gaussian-rational Choi matrix to produce a true dual feasible
point whose score is within ε of the common primal and dual optimum, which also represents
`finiteDiamondNorm`.

For the mathematical background, see [Watrous2018].

## Main statements

* `g1`: For a positive input dimension and a Gaussian-rational Choi matrix, `solve` returns a
  dual feasible point within ε above the common primal and dual optimum representing
  `finiteDiamondNorm`, with the stated trace length and separation-call bound.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.DyadicFloor.FloorRounding.Program
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.SdpObjective.ObjectiveSearch

set_option autoImplicit false

namespace Qatlib.Concepts.SdpObjective.ObjectiveSearch
open Qatlib.Concepts.DyadicFloor.FloorRounding Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.SdpObjective.ObjectiveSearch
open scoped BigOperators ComplexOrder

/-- The per-call rational ellipsoid search budget determined by the diamond SDP coordinate
dimension and its outer and inner radii. -/
def searchBudget {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (η : ℚ) : ℕ :=
  rationalEllipsoidSearchBudget (diamondDyadicWordCount D E)
    (diamondCoordinateOuterRadius J η) (diamondCoordinateInnerRadius J η)

/-- Appending one objective-search result increases `calls` by the length of that result's
ellipsoid trace. -/
lemma calls_append {D E : ℕ} (s : SearchState D E) (mid : ℚ)
    (out : RationalEllipsoidRunResult (diamondDyadicWordCount D E))
    (lower upper : ℚ) (best : DiamondRationalCoordinates D E) :
    calls ⟨lower, upper, best, s.trace ++ [(mid, out)]⟩ = calls s + out.trace.length := by
  simp [calls, List.map_append, List.sum_append]

/-- A feasible midpoint update halves the real width of the rational search interval. -/
lemma width_feasible (lower upper : ℚ) :
    ((((lower + upper) / 2 - lower : ℚ) : ℝ)) = ((upper : ℝ) - lower) / 2 := by
  push_cast
  ring

/-- An exhausted midpoint update gives half the previous interval width plus η. -/
lemma width_exhausted (lower upper η : ℚ) :
    (((upper - ((lower + upper) / 2 - η) : ℚ) : ℝ)) = ((upper : ℝ) - lower) / 2 + (η : ℝ) := by
  push_cast
  ring

/-- The objective-search invariant requiring feasibility of the stored dual point, a lower
endpoint below α, and its score below the upper endpoint. -/
structure LoopInv {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (α : ℝ) (s : SearchState D E) : Prop where
  feasible : (diamondProgram T).DualFeasible (diamondRationalDecode s.best)
  lower_le : (s.lower : ℝ) ≤ α
  score_le : (diamondProgram T).dualScore (diamondRationalDecode s.best) ≤ (s.upper : ℝ)

/-- Given the stated solver-outcome guarantees, `searchLoop` preserves `LoopInv`, bounds the
interval width after n steps, appends exactly n trace entries, and uses at most n additional
per-call budgets. -/
lemma searchLoop_spec {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (hJ : gaussianRationalMatrix J = MatrixMap.choi_matrix T) {η : ℚ} (hη : 0 < η)
    (α : ℝ)
    (houtcome : ∀ γ : ℚ,
      ((diamondEllipsoidSolve J γ η).outcome = .feasible ∧
        (diamondProgram T).DualFeasible
          (diamondRationalDecode (diamondEllipsoidSolve J γ η).state.center) ∧
        (diamondProgram T).dualScore
          (diamondRationalDecode (diamondEllipsoidSolve J γ η).state.center) ≤ (γ : ℝ)) ∨
      ((diamondEllipsoidSolve J γ η).outcome = .exhausted ∧ (γ : ℝ) < α + (η : ℝ)))
    (n : ℕ) (s : SearchState D E) (hinv : LoopInv T α s) :
    LoopInv T α (searchLoop J η n s) ∧
      (((searchLoop J η n s).upper - (searchLoop J η n s).lower : ℚ) : ℝ) ≤
        ((s.upper - s.lower : ℚ) : ℝ) / (2 : ℝ) ^ n + (η : ℝ) * (2 - 2 / (2 : ℝ) ^ n) ∧
      (searchLoop J η n s).trace.length = s.trace.length + n ∧
      calls (searchLoop J η n s) ≤ calls s + n * searchBudget J η := by
  induction n generalizing s with
  | zero =>
    refine ⟨hinv, ?_, ?_, ?_⟩
    · simp [searchLoop]
    · simp [searchLoop]
    · simp [searchLoop]
  | succ n ih =>
    let mid : ℚ := (s.lower + s.upper) / 2
    let out := diamondEllipsoidSolve J mid η
    have hnot : out.outcome ≠ .invalid := diamondEllipsoidSolve_not_invalid T J hJ mid η
    have hcall : out.trace.length ≤ searchBudget J η := diamondEllipsoidSolve_calls_le J mid η
    cases ho : out.outcome with
    | invalid =>
      exact absurd ho hnot
    | feasible =>
      have hfeas : (diamondProgram T).DualFeasible (diamondRationalDecode out.state.center) ∧
          (diamondProgram T).dualScore (diamondRationalDecode out.state.center) ≤ (mid : ℝ) :=
        diamondEllipsoidSolve_feasible T J hJ mid η ho
      let s1 : SearchState D E := ⟨s.lower, mid, out.state.center, s.trace ++ [(mid, out)]⟩
      have hinv1 : LoopInv T α s1 := by
        refine ⟨hfeas.1, ?_, ?_⟩
        · simpa [s1] using! hinv.lower_le
        · simpa [s1] using! hfeas.2
      have hwidth1 : ((s1.upper - s1.lower : ℚ) : ℝ) ≤
          ((s.upper - s.lower : ℚ) : ℝ) / 2 + η := by
        have heq := width_feasible s.lower s.upper
        have hη0 : (0 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη.le
        simpa [s1, mid] using! le_add_of_le_of_nonneg heq.le hη0
      have hlen1 : s1.trace.length = s.trace.length + 1 := by
        simp [s1, List.length_append]
      have hcalls1 : calls s1 ≤ calls s + searchBudget J η := by
        rw [calls_append]
        exact Nat.add_le_add_left hcall _
      have ih1 := ih s1 hinv1
      have hrec : searchLoop J η (n + 1) s = searchLoop J η n s1 := by
        simp only [searchLoop]
        rw [ho]
      refine ⟨hrec ▸ ih1.1, ?_, ?_, ?_⟩
      · calc
          (((searchLoop J η (n + 1) s).upper - (searchLoop J η (n + 1) s).lower : ℚ) : ℝ) ≤
              ((s1.upper - s1.lower : ℚ) : ℝ) / (2 : ℝ) ^ n +
                (η : ℝ) * (2 - 2 / (2 : ℝ) ^ n) := by
            simpa [hrec] using! ih1.2.1
          _ ≤ (((s.upper - s.lower : ℚ) : ℝ) / 2 + (η : ℝ)) / (2 : ℝ) ^ n +
                (η : ℝ) * (2 - 2 / (2 : ℝ) ^ n) := by
            gcongr
          _ = ((s.upper - s.lower : ℚ) : ℝ) / (2 : ℝ) ^ (n + 1) +
                (η : ℝ) * (2 - 2 / (2 : ℝ) ^ (n + 1)) := by
            have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by ring
            rw [hpow]
            ring
      · rw [hrec, ih1.2.2.1, hlen1]
        ring
      · calc
          calls (searchLoop J η (n + 1) s) ≤ calls s1 + n * searchBudget J η := by
            simpa [hrec] using! ih1.2.2.2
          _ ≤ calls s + searchBudget J η + n * searchBudget J η := by
            gcongr
          _ = calls s + (n + 1) * searchBudget J η := by ring
    | exhausted =>
      have hlt : (mid : ℝ) < α + (η : ℝ) := by
        rcases houtcome mid with ⟨hfe, _, _⟩ | ⟨_, hlt⟩
        · rw [ho] at hfe
          exact nomatch hfe
        · exact hlt
      let s1 : SearchState D E := ⟨mid - η, s.upper, s.best, s.trace ++ [(mid, out)]⟩
      have hinv1 : LoopInv T α s1 := by
        refine ⟨?_, ?_, ?_⟩
        · simpa [s1] using! hinv.feasible
        · have : (mid - η : ℝ) ≤ α := by linarith
          simpa [s1] using! this
        · simpa [s1] using! hinv.score_le
      have hwidth1 : ((s1.upper - s1.lower : ℚ) : ℝ) ≤
          ((s.upper - s.lower : ℚ) : ℝ) / 2 + η := by
        have heq := width_exhausted s.lower s.upper η
        simpa [s1, mid] using! heq.le
      have hlen1 : s1.trace.length = s.trace.length + 1 := by
        simp [s1, List.length_append]
      have hcalls1 : calls s1 ≤ calls s + searchBudget J η := by
        rw [calls_append]
        exact Nat.add_le_add_left hcall _
      have ih1 := ih s1 hinv1
      have hrec : searchLoop J η (n + 1) s = searchLoop J η n s1 := by
        simp only [searchLoop]
        rw [ho]
      refine ⟨hrec ▸ ih1.1, ?_, ?_, ?_⟩
      · calc
          (((searchLoop J η (n + 1) s).upper - (searchLoop J η (n + 1) s).lower : ℚ) : ℝ) ≤
              ((s1.upper - s1.lower : ℚ) : ℝ) / (2 : ℝ) ^ n +
                (η : ℝ) * (2 - 2 / (2 : ℝ) ^ n) := by
            simpa [hrec] using! ih1.2.1
          _ ≤ (((s.upper - s.lower : ℚ) : ℝ) / 2 + (η : ℝ)) / (2 : ℝ) ^ n +
                (η : ℝ) * (2 - 2 / (2 : ℝ) ^ n) := by
            gcongr
          _ = ((s.upper - s.lower : ℚ) : ℝ) / (2 : ℝ) ^ (n + 1) +
                (η : ℝ) * (2 - 2 / (2 : ℝ) ^ (n + 1)) := by
            have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by ring
            rw [hpow]
            ring
      · rw [hrec, ih1.2.2.1, hlen1]
        ring
      · calc
          calls (searchLoop J η (n + 1) s) ≤ calls s1 + n * searchBudget J η := by
            simpa [hrec] using! ih1.2.2.2
          _ ≤ calls s + searchBudget J η + n * searchBudget J η := by
            gcongr
          _ = calls s + (n + 1) * searchBudget J η := by ring

/-- For a positive input dimension and a Gaussian-rational Choi matrix, `solve` returns a dual
feasible point within ε above the common primal and dual optimum representing
`finiteDiamondNorm`, with the stated trace length and separation-call bound. -/
theorem g1 :
    ∀ (D E : ℕ), 0 < D →
      ∀ (T : Operator D →ₗ[ℂ] Operator E)
        (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational),
        gaussianRationalMatrix J = MatrixMap.choi_matrix T →
        ∀ ε : ℚ, 0 < ε →
          ∃ α : ℝ, finiteDiamondNorm T = ENNReal.ofReal α ∧
            IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α ∧
            (diamondProgram T).DualFeasible (diamondRationalDecode (solve J ε).best) ∧
            α ≤ (diamondProgram T).dualScore (diamondRationalDecode (solve J ε).best) ∧
            (diamondProgram T).dualScore (diamondRationalDecode (solve J ε).best) ≤ α + (ε : ℝ) ∧
            (solve J ε).trace.length = dyadicPrecision ⌈4 * ((initial J).upper + 1) / ε⌉₊ ∧
            calls (solve J ε) ≤ (solve J ε).trace.length *
              rationalEllipsoidSearchBudget (diamondDyadicWordCount D E)
                (diamondCoordinateOuterRadius J (ε / 8)) (diamondCoordinateInnerRadius J (ε / 8)) := by
  intro D E hD T J hJ ε hε
  have hη : 0 < ε / 8 := div_pos hε (by norm_num)
  obtain ⟨α, hnorm, hlub, hglb, houtcome⟩ := diamondEllipsoidSolve_outcome hD T J hJ hη
  obtain ⟨β, -, -, -, -, -, -, hglbβ, -, -, hβ0, -⟩ := diamondProgram_bounded_optimizers hD T
  have hαβ : α = β := IsGLB.unique hglb hglbβ
  have hα0 : 0 ≤ α := by simpa [hαβ] using! hβ0
  have hcenter := diamondRationalCenterCoordinates_decode J
  have hfeas0 : (diamondProgram T).DualFeasible
      (diamondRationalDecode (initial J).best) := by
    change (diamondProgram T).DualFeasible
      (diamondRationalDecode (diamondRationalCenterCoordinates J))
    rw [hcenter]
    have hone : (0 : HermitianMat (DiamondRegister D E) ℂ) ≤ 1 :=
      HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one
    exact le_trans hone (diamondRationalCenter_margin T J hJ)
  have hscore0 : (diamondProgram T).dualScore (diamondRationalDecode (initial J).best) =
      ((initial J).upper : ℝ) := by
    change (diamondProgram T).dualScore
      (diamondRationalDecode (diamondRationalCenterCoordinates J)) = _
    rw [← diamondRationalScore_cast T (diamondRationalCenterCoordinates J)]
    rfl
  have hinv0 : LoopInv T α (initial J) := by
    refine ⟨hfeas0, ?_, ?_⟩
    · simpa [initial] using! hα0
    · exact hscore0.le
  let q : ℕ := ⌈4 * ((initial J).upper + 1) / ε⌉₊
  let steps : ℕ := dyadicPrecision q
  have hspec := searchLoop_spec T J hJ hη α houtcome steps (initial J) hinv0
  have hsolve : solve J ε = searchLoop J (ε / 8) steps (initial J) := by
    simp [solve, steps, q, initial]
  have hshrink : ((initial J).upper : ℝ) / (2 : ℝ) ^ steps ≤ (ε : ℝ) / 4 := by
    have hq : 4 * (((initial J).upper + 1 : ℚ) : ℝ) / (ε : ℝ) ≤ (q : ℝ) := by
      have hle : ((4 * ((initial J).upper + 1) / ε : ℚ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.le_ceil (4 * ((initial J).upper + 1) / ε))
      convert! hle using 1
      push_cast
      ring
    have hprec := dyadicPrecision_sufficient (c := 4 * (((initial J).upper + 1 : ℚ) : ℝ))
      (r := (ε : ℝ)) (by exact_mod_cast hε) q hq
    have hpos4 : (0 : ℝ) < 4 := by norm_num
    have hone : (((initial J).upper + 1 : ℚ) : ℝ) / (2 : ℝ) ^ steps ≤ (ε : ℝ) / 4 := by
      have hmul : 4 * (((initial J).upper + 1 : ℚ) : ℝ) / (2 : ℝ) ^ steps ≤ (ε : ℝ) := hprec
      apply (le_div_iff₀ hpos4).mpr
      calc
        (((initial J).upper + 1 : ℚ) : ℝ) / (2 : ℝ) ^ steps * 4
            = 4 * (((initial J).upper + 1 : ℚ) : ℝ) / (2 : ℝ) ^ steps := by ring
        _ ≤ (ε : ℝ) := hmul
    have hupper : ((initial J).upper : ℝ) ≤ (((initial J).upper + 1 : ℚ) : ℝ) := by
      push_cast
      linarith
    exact (div_le_div_of_nonneg_right hupper
      (le_of_lt (by positivity : (0 : ℝ) < (2 : ℝ) ^ steps))).trans hone
  have hdiff : (((solve J ε).upper - (solve J ε).lower : ℚ) : ℝ) ≤ (ε : ℝ) := by
    have hrec := hspec.2.1
    have hw0 : ((initial J).upper - (initial J).lower : ℚ) = (initial J).upper := by
      simp [initial]
    have htail : ((ε / 8 : ℚ) : ℝ) * (2 - 2 / (2 : ℝ) ^ steps) ≤ ((ε / 8 : ℚ) : ℝ) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hη.le)
      have : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ steps := by positivity
      linarith
    have hsum : ((initial J).upper : ℝ) / (2 : ℝ) ^ steps + ((ε / 8 : ℚ) : ℝ) * 2 ≤ (ε : ℝ) := by
      have hε4 : ((ε / 8 : ℚ) : ℝ) * 2 = (ε : ℝ) / 4 := by
        push_cast
        ring
      calc
        ((initial J).upper : ℝ) / (2 : ℝ) ^ steps + ((ε / 8 : ℚ) : ℝ) * 2
            ≤ (ε : ℝ) / 4 + (ε : ℝ) / 4 := by
          rw [hε4]
          gcongr
        _ = (ε : ℝ) / 2 := by ring
        _ ≤ (ε : ℝ) := by
          have : (0 : ℝ) ≤ ε := by exact_mod_cast hε.le
          linarith
    calc
      (((solve J ε).upper - (solve J ε).lower : ℚ) : ℝ) ≤
          ((initial J).upper : ℝ) / (2 : ℝ) ^ steps +
            ((ε / 8 : ℚ) : ℝ) * (2 - 2 / (2 : ℝ) ^ steps) := by
        rw [hsolve]
        simpa [hw0] using! hrec
      _ ≤ ((initial J).upper : ℝ) / (2 : ℝ) ^ steps + ((ε / 8 : ℚ) : ℝ) * 2 := by
        gcongr
      _ ≤ (ε : ℝ) := hsum
  have hupper : ((solve J ε).upper : ℝ) ≤ α + (ε : ℝ) := by
    have hlow : ((solve J ε).lower : ℝ) ≤ α := by
      rw [hsolve]
      exact hspec.1.lower_le
    have hsplit : ((solve J ε).upper : ℝ) =
        ((solve J ε).lower : ℝ) + (((solve J ε).upper - (solve J ε).lower : ℚ) : ℝ) := by
      push_cast
      ring
    linarith
  have hfeas : (diamondProgram T).DualFeasible (diamondRationalDecode (solve J ε).best) := by
    rw [hsolve]
    exact hspec.1.feasible
  have hscore : (diamondProgram T).dualScore (diamondRationalDecode (solve J ε).best) ≤ α + (ε : ℝ) := by
    have hs : (diamondProgram T).dualScore (diamondRationalDecode (solve J ε).best) ≤
        ((solve J ε).upper : ℝ) := by
      rw [hsolve]
      exact hspec.1.score_le
    exact hs.trans hupper
  have hbest : α ≤ (diamondProgram T).dualScore (diamondRationalDecode (solve J ε).best) :=
    hglb.1 ⟨diamondRationalDecode (solve J ε).best, hfeas, rfl⟩
  have hlen : (solve J ε).trace.length = steps := by
    rw [hsolve]
    simpa [initial] using! hspec.2.2.1
  have hcalls : calls (solve J ε) ≤ steps * searchBudget J (ε / 8) := by
    rw [hsolve]
    simpa [initial, calls] using! hspec.2.2.2
  refine ⟨α, hnorm, hlub, hglb, hfeas, hbest, hscore, ?_, ?_⟩
  · simpa [steps, q] using! hlen
  · have hbudget : searchBudget J (ε / 8) =
        rationalEllipsoidSearchBudget (diamondDyadicWordCount D E)
          (diamondCoordinateOuterRadius J (ε / 8)) (diamondCoordinateInnerRadius J (ε / 8)) := rfl
    rw [hlen]
    simpa [← hbudget] using! hcalls

end Qatlib.Concepts.SdpObjective.ObjectiveSearch
