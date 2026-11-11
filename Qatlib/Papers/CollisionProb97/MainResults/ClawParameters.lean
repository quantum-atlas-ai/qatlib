/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.SampledClaw
import Qatlib.Papers.CollisionProb97.MainResults.BijectiveClaw
import Qatlib.Papers.CollisionProb97.MainResults.IntegerParameters
import Qatlib.Papers.CollisionProb97.MainResults.InputSelection

/-!
# Cube-root parameters for claw finding

This module chooses integer cube-root table sizes for the bijective and regular sampled claw
algorithms of [BrassardHoyerTapp1998Collision]. The results `bijective_cube_root` and
`sampled_cube_root` bound the expected numbers of evaluations of the two functions separately.

The singleton codomain case is handled by `singletonRun`, which compares one value from each
function without constructing a table.

## Main statements

* `bijective_cube_root`: For injective `F` and bijective `G` on equally sized domains, choose a
  table of integer cube-root size with the stated separate cube-root bounds on expected `F` and
  `G` evaluations, as in Theorem 4 of [BrassardHoyerTapp1998Collision].
* `sampled_cube_root`: For regular surjections to a codomain of size at least two, choose an
  admissible integer cube-root table size with the stated separate bounds on expected `F` and
  `G` evaluations, supporting Theorem 5 of [BrassardHoyerTapp1998Collision].
* `singletonRun_correct`: For a singleton codomain, the chosen inputs form a claw and
  `singletonRun` returns it with cost pair `(1, 1)`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.QueryWordCore.Circuit
namespace Qatlib.Papers.CollisionProb97.MainResults.ClawParameters
variable {S X R : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

omit [Nonempty S] in

/-- For injective `F` and bijective `G` on equally sized domains, choose a table of integer
cube-root size with the stated separate cube-root bounds on expected `F` and `G`
evaluations, as in Theorem 4 of [BrassardHoyerTapp1998Collision]. -/
theorem bijective_cube_root (F : S → R) (hF : Function.Injective F)
    (G : X → R) (hG : Function.Bijective G) (hSX : Fintype.card S = Fintype.card X)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    ∃ (K : Finset S) (hK : K.Nonempty),
      K.card = Nat.nthRoot 3 (Fintype.card X) ∧
      expectation (BijectiveClaw.run F hF G hG K hK l hl hl4) (fun z => (z.2.1:ℝ≥0∞)) ≤
        ENNReal.ofReal ((Fintype.card X:ℝ)^(1/3:ℝ)) ∧
      expectation (BijectiveClaw.run F hF G hG K hK l hl hl4) (fun z => (z.2.2:ℝ≥0∞)) ≤
        ENNReal.ofReal (3*(1+4*SourcePhaseConstant l)*(Fintype.card X:ℝ)^(1/3:ℝ)) := by
  let n := Fintype.card X
  let k := Nat.nthRoot 3 n
  have hn : 1 ≤ n := Fintype.card_pos
  obtain ⟨hk,hpow,_⟩ := IntegerParameters.cube_root_bounds n hn
  change 1 ≤ k at hk
  change k^3 ≤ n at hpow
  have hkn : k ≤ n := by nlinarith [Nat.mul_self_le_mul_self hk]
  have hkS : k ≤ Fintype.card S := by rw [hSX]; exact hkn
  let K := InputSelection.select (X := S) k
  have hcard : K.card = k := InputSelection.select_card k hkS
  have hK : K.Nonempty := InputSelection.select_nonempty k hk hkS
  have hroot := (IntegerParameters.cube_root_real_window n).1
  change (k:ℝ) ≤ (n:ℝ)^(1/3:ℝ) at hroot
  have hs := IntegerParameters.cube_root_search_bound n hn
  change Real.sqrt ((n:ℝ)/k) ≤ 3*(k:ℝ) at hs
  have hg : 0 ≤ 1+4*SourcePhaseConstant l := by
    have := search_source_constant_nonneg l hl hl4
    linarith
  refine ⟨K,hK,hcard,?_,?_⟩
  · rw [BijectiveClaw.run_Fmean,hcard]
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hroot
  · apply (BijectiveClaw.run_Gbound F hF G hG K hK l hl hl4).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hcard]
    have h1 := mul_le_mul_of_nonneg_left hs hg
    have h2 := mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hg)
    nlinarith

/-- For regular surjections to a codomain of size at least two, choose an admissible integer
cube-root table size with the stated separate bounds on expected `F` and `G` evaluations,
supporting Theorem 5 of [BrassardHoyerTapp1998Collision]. -/
theorem sampled_cube_root (F : S → R) (rF : ℕ) (hrF : 0 < rF) (hF : RToOne F rF)
    (hontoF : Finset.univ.image F = Finset.univ)
    (G : X → R) (rG : ℕ) (hrG : 0 < rG) (hG : RToOne G rG)
    (hontoG : Finset.univ.image G = Finset.univ) (hm : 2 ≤ Fintype.card R)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    ∃ (k : ℕ) (hk : 0 < k) (hhalf : 2*k ≤ (Finset.univ.image F).card),
      k = Nat.nthRoot 3 (Fintype.card R) ∧
      expectation (SampledClaw.run F rF hrF hF G rG hrG hG hontoG k hk hhalf l hl hl4)
        (fun z => (z.2.1 : ℝ≥0∞)) ≤ ENNReal.ofReal (2*(Fintype.card R:ℝ)^(1/3:ℝ)) ∧
      expectation (SampledClaw.run F rF hrF hF G rG hrG hG hontoG k hk hhalf l hl hl4)
        (fun z => (z.2.2 : ℝ≥0∞)) ≤
        ENNReal.ofReal (3*(1+4*SourcePhaseConstant l)*(Fintype.card R:ℝ)^(1/3:ℝ)) := by
  let m := Fintype.card R
  let k := Nat.nthRoot 3 m
  have hk : 0 < k := (IntegerParameters.cube_root_bounds m (by omega)).1
  have hhalf : 2*k ≤ (Finset.univ.image F).card := by
    rw [hontoF, Finset.card_univ]
    have hc := IntegerParameters.cube_root_claw_admissible m hm
    change k ≤ m/2 at hc
    omega
  have hN : (Fintype.card X:ℝ) = (m:ℝ)*(rG:ℝ) := by
    have hn := card_eq_image_card_mul G rG hG
    rw [hontoG, Finset.card_univ] at hn
    exact_mod_cast hn
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrR : (rG:ℝ) ≠ 0 := by exact_mod_cast hrG.ne'
  have he : (Fintype.card X:ℝ)/((k*rG:ℕ):ℝ) = (m:ℝ)/k := by
    rw [hN, Nat.cast_mul]
    field_simp
  have hkroot := (IntegerParameters.cube_root_real_window m).1
  change (k:ℝ) ≤ (m:ℝ)^(1/3:ℝ) at hkroot
  have hs := IntegerParameters.cube_root_search_bound m (by omega)
  change Real.sqrt ((m:ℝ)/k) ≤ 3*(k:ℝ) at hs
  have hg : 0 ≤ 1+4*SourcePhaseConstant l := by
    have := search_source_constant_nonneg l hl hl4
    linarith
  refine ⟨k,hk,hhalf,rfl,?_,?_⟩
  · apply (SampledClaw.run_Fbounds F rF hrF hF G rG hrG hG hontoG k hk hhalf l hl hl4).2.trans
    have hb := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hkroot (by norm_num : (0:ℝ) ≤ 2))
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast] using hb
  · apply (SampledClaw.run_Gbound F rF hrF hF G rG hrG hG hontoG k hk hhalf l hl hl4).trans
    apply ENNReal.ofReal_le_ofReal
    rw [he]
    have h1 := mul_le_mul_of_nonneg_left hs hg
    have h2 := mul_le_mul_of_nonneg_left hkroot (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hg)
    nlinarith

omit [AddCommGroup R] [DecidableEq R] in

/-- A codomain of cardinality one cannot satisfy the half-image table constraint for a positive
table size. -/
theorem singleton_no_table (hm : Fintype.card R = 1) (k : ℕ) (hk : 0 < k) :
    ¬ 2*k ≤ Fintype.card R := by omega

/-- The deterministic law comparing `F s` and `G x`, returning the pair exactly when the values
agree and recording one evaluation of each function. -/
def singletonRun (F : S → R) (G : X → R) (s : S) (x : X) : PMF (Option (S × X) × (ℕ × ℕ)) :=
  PMF.pure ((if F s = G x then some (s,x) else none),(1,1))

omit [Nonempty S] [Nonempty X] in

/-- With empty table memory, the single-query circuits for `F` and `G` each use one query and
produce the corresponding evaluated basis states [BrassardHoyerTapp1998Collision]. -/
theorem singleton_fetch_words (F : S → R) (G : X → R) (s : S) (x : X) :
    QueryCount ([Step.query] : Circuit ((S × R) × ReadOnlyTable.Memory (X := S) (R := R) 0)) = 1 ∧
    QueryCount ([Step.query] : Circuit ((X × R) × ReadOnlyTable.Memory (X := X) (R := R) 0)) = 1 ∧
    ReadOnlySearch.verificationState F (fun i : Fin 0 => Fin.elim0 i : ReadOnlyTable.Memory (X := S) (R := R) 0) s =
      Qatlib.Foundations.PureStateMath.Ket ((s,F s),fun i : Fin 0 => Fin.elim0 i) ∧
    ReadOnlySearch.verificationState G (fun i : Fin 0 => Fin.elim0 i : ReadOnlyTable.Memory (X := X) (R := R) 0) x =
      Qatlib.Foundations.PureStateMath.Ket ((x,G x),fun i : Fin 0 => Fin.elim0 i) :=
  ⟨rfl,rfl,ReadOnlySearch.verificationState_eq F _ s,ReadOnlySearch.verificationState_eq G _ x⟩

omit [Fintype S] [DecidableEq S] [Nonempty S] [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup R] in

/-- For a singleton codomain, the chosen inputs form a claw and `singletonRun` returns it with
cost pair `(1, 1)`. -/
theorem singletonRun_correct (F : S → R) (G : X → R) (s : S) (x : X)
    (hm : Fintype.card R = 1) :
    singletonRun F G s x = PMF.pure (some (s,x),(1,1)) ∧ F s = G x := by
  haveI : Subsingleton R := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have he : F s = G x := Subsingleton.elim _ _
  exact ⟨by simp only [singletonRun, if_pos he],he⟩

end Qatlib.Papers.CollisionProb97.MainResults.ClawParameters
