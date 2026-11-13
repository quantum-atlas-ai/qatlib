/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section6LowerBoundSubgoalStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryBlockTransport
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Singleton phase-query search lower bound

`section6LowerBoundSubgoal` establishes the fixed-space singleton search lower bound at success
threshold 1/2. The supporting lemmas relate singleton phase oracles and direct label decoding to
the underlying query model.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `section6LowerBoundSubgoal`: Singleton phase-oracle search has fixed-space query lower bound
  ⌊sin(π/8)√N⌋ at success threshold 1/2.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SearchStopping.QueryLowerBound
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Matrix
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The singleton phase oracle for w fixes a basis vector at any distinct index c. -/
private theorem mark_fixes_single (w c : I) (hc : c ≠ w) :
    MarkOracle w *ᵥ (EuclideanSpace.single c (1 : ℂ)).ofLp =
      (EuclideanSpace.single c (1 : ℂ)).ofLp := by
  ext j
  by_cases hj : j = c
  · subst j
    simp [MarkOracle, PhaseOracle, Matrix.mulVec_diagonal, hc]
  · simp [MarkOracle, PhaseOracle, Matrix.mulVec_diagonal, hj]

/-- Identity decoding succeeds at target w with probability equal to the Born mass of the
singleton {w}. -/
private theorem identity_label_success (ψ : QState I) (w : I) :
    QuerySuccess (fun c : I => some c) (toEuclidean_fromVec ψ) w = MeasureProb ψ {w} := by
  simp [QuerySuccess, QueryProjection, EuclideanSpace.norm_sq_eq,
    toEuclidean_fromVec, MeasureProb, BornProb]
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _hb hbw
    simp [hbw]
  · simp

/-- Singleton phase-oracle search has fixed-space query lower bound ⌊sin(π/8)√N⌋ at success
threshold 1/2. -/
theorem section6LowerBoundSubgoal : Section6LowerBoundSubgoal := by
  intro I _ _
  refine ⟨⟨by norm_num, by norm_num⟩, markOracle_unitary, ?_⟩
  intro C ψ hC hψ hsolve
  rcases isEmpty_or_nonempty I with hempty | hnonempty
  · letI := hempty
    simp
  · letI := hnonempty
    let gs := (splitQueries C).2
    let P := (splitQueries C).1
    obtain ⟨hP, hgs⟩ := splitQueries_unitary C hC
    let init := toEuclidean_fromVec (P *ᵥ ψ)
    let U : ℕ → EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I :=
      fun n => unitaryEuclidean (gs.getD n 1) (block_get_unitary gs hgs n)
    let V : I → ℕ → EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I :=
      fun w => blockEvolution gs hgs (MarkOracle w) (markOracle_unitary w)
    let labels : ℕ → I → Option I := fun _ c => some c
    have hinit : ‖init‖ = 1 := by
      have h := (unitaryEuclidean P hP).norm_map (toEuclidean_fromVec ψ)
      rw [unitaryEuclidean_apply] at h
      simpa [init, toEuclidean_fromVec] using
          h.trans ((normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ)
    have hrun (w : I) :
        toEuclidean_fromVec (Run (MarkOracle w) C ψ) = UnitaryEvolution (V w) init (QueryCount C) := by
      rw [splitQueries_semantics]
      have h := blocks_evolution gs hgs (MarkOracle w) (markOracle_unitary w) (P *ᵥ ψ)
      simpa only [gs, splitQueries_count] using h.symm
    have hagree : ∀ w n, n < QueryCount C → ∀ c, labels n c ≠ some w →
        V w n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1) := by
      intro w n _hn c hc
      have hcw : c ≠ w := by intro he; subst c; exact hc rfl
      dsimp only [V, U, blockEvolution]
      rw [unitaryEuclidean_apply, unitaryEuclidean_apply,
        ← Matrix.mulVec_mulVec, mark_fixes_single w c hcw]
    have hsuccess (w : I) :
        1 / 2 ≤ QuerySuccess (labels (QueryCount C)) (UnitaryEvolution (V w) init (QueryCount C)) w := by
      rw [← hrun w, identity_label_success]
      have hs : 1 - (1 / 2 : ℝ) ≤ MeasureProb (Run (MarkOracle w) C ψ) {w} := hsolve w
      norm_num at hs
      exact hs
    have havg : (Fintype.card I : ℝ) / 2 ≤
        ∑ w : I, QuerySuccess (labels (QueryCount C)) (UnitaryEvolution (V w) init (QueryCount C)) w := by
      calc
        _ = ∑ _w : I, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
        _ ≤ _ := Finset.sum_le_sum (fun w _hw => hsuccess w)
    have hInt := theorem7Corrected U V labels init hinit (QueryCount C) hagree havg
    simpa only [Int.floor_toNat] using Int.toNat_le.mpr hInt

end Qatlib.Concepts.SearchStopping.KnownCount
