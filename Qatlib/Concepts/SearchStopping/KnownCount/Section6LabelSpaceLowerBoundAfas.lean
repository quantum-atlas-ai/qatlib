/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section6LabelSpaceLowerBoundStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryBlockTransport

/-!
# Search lower bound for labeled configuration spaces

`section6LabelSpaceLowerBound` proves the phase-query lower bound when configurations carry
labels through a surjective map. The supporting identities show that the oracle fixes
configurations outside the target fiber and that label decoding measures that fiber.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `section6LabelSpaceLowerBound`: For a surjective labeling of a finite configuration space,
  phase-oracle search of target fibers has fixed-space query lower bound ⌊sin(π/8)√N⌋ at success
  threshold 1/2, where N is the label cardinality.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SearchStopping.QueryLowerBound
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.SearchStopping.KnownCount
open Matrix
open scoped Classical BigOperators

/-- A target-fiber phase oracle fixes a basis vector whose configuration label differs from the
target. -/
private theorem labelOracle_fixes_single
    {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
    (lbl : C → I) (w : I) (c : C) (hc : lbl c ≠ w) :
    SetOracle (Finset.univ.filter fun c => lbl c = w) *ᵥ (EuclideanSpace.single c (1 : ℂ)).ofLp =
      (EuclideanSpace.single c (1 : ℂ)).ofLp := by
  ext j
  by_cases hj : j = c
  · subst j
    simp [SetOracle, PhaseOracle, Matrix.mulVec_diagonal, hc]
  · simp [SetOracle, PhaseOracle, Matrix.mulVec_diagonal, hj]

/-- Decoding a configuration by `lbl` succeeds on target w with probability equal to the Born
mass of the fiber of w. -/
private theorem label_space_success
    {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
    (lbl : C → I) (ψ : QState C) (w : I) :
    QuerySuccess (fun c => some (lbl c)) (toEuclidean_fromVec ψ) w =
      MeasureProb ψ (Finset.univ.filter fun c => lbl c = w) := by
  simp [QuerySuccess, QueryProjection, EuclideanSpace.norm_sq_eq,
    toEuclidean_fromVec, MeasureProb, BornProb, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

/-- For a surjective labeling of a finite configuration space, phase-oracle search of target
fibers has fixed-space query lower bound ⌊sin(π/8)√N⌋ at success threshold 1/2, where N is
the label cardinality. -/
theorem section6LabelSpaceLowerBound : Section6LabelSpaceLowerBound := by
  intro I Cfg _ _ _ _ lbl _hsurj
  refine ⟨⟨by norm_num, by norm_num⟩, (fun w => setOracle_unitary _), ?_⟩
  intro C ψ hC hψ hsolve
  rcases isEmpty_or_nonempty I with hempty | hnonempty
  · letI := hempty
    simp
  · letI := hnonempty
    let gs := (splitQueries C).2
    let P := (splitQueries C).1
    obtain ⟨hP, hgs⟩ := splitQueries_unitary C hC
    let init := toEuclidean_fromVec (P *ᵥ ψ)
    let U : ℕ → EuclideanSpace ℂ Cfg ≃ₗᵢ[ℂ] EuclideanSpace ℂ Cfg :=
      fun n => unitaryEuclidean (gs.getD n 1) (block_get_unitary gs hgs n)
    let V : I → ℕ → EuclideanSpace ℂ Cfg ≃ₗᵢ[ℂ] EuclideanSpace ℂ Cfg :=
      fun w => blockEvolution gs hgs (SetOracle (Finset.univ.filter fun c => lbl c = w)) (setOracle_unitary _)
    let labels : ℕ → Cfg → Option I := fun _ c => some (lbl c)
    have hinit : ‖init‖ = 1 := by
      have h := (unitaryEuclidean P hP).norm_map (toEuclidean_fromVec ψ)
      rw [unitaryEuclidean_apply] at h
      simpa [init, toEuclidean_fromVec] using
          h.trans ((normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ)
    have hrun (w : I) :
        toEuclidean_fromVec (Run (SetOracle (Finset.univ.filter fun c => lbl c = w)) C ψ) = UnitaryEvolution (V w) init (QueryCount C) := by
      rw [splitQueries_semantics]
      have h :=
          blocks_evolution gs hgs (SetOracle (Finset.univ.filter fun c => lbl c = w))
          (setOracle_unitary _) (P *ᵥ ψ)
      simpa only [gs, splitQueries_count] using h.symm
    have hagree : ∀ w n, n < QueryCount C → ∀ c, labels n c ≠ some w →
        V w n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1) := by
      intro w n _hn c hc
      have hcw : lbl c ≠ w := by intro he; exact hc (congrArg some he)
      dsimp only [V, U, blockEvolution]
      rw [unitaryEuclidean_apply, unitaryEuclidean_apply,
        ← Matrix.mulVec_mulVec, labelOracle_fixes_single lbl w c hcw]
    have hsuccess (w : I) :
        1 / 2 ≤ QuerySuccess (labels (QueryCount C)) (UnitaryEvolution (V w) init (QueryCount C)) w := by
      rw [← hrun w, label_space_success]
      have hs :
          1 - (1 / 2 : ℝ) ≤ MeasureProb
          (Run (SetOracle (Finset.univ.filter fun c => lbl c = w)) C ψ)
          (Finset.univ.filter fun c => lbl c = w) := hsolve w
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
