/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.LocalMeasurementLowerBoundSubgoalStat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Qatlib.Papers.ClassShadows20.LowerBound.LocalShotPauliMomentSubgoalHuan
import Qatlib.Papers.ClassShadows20.LowerBound.LocalProductRecordInformation
import Qatlib.Papers.ClassShadows20.LowerBound.LocalMeasurementDecoder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.ClassShadows20.LowerBound.HuangKuengPreskill2020
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option maxHeartbeats 3000000
namespace Qatlib.Papers.ClassShadows20.LowerBound
open Matrix
open scoped Classical BigOperators ComplexOrder

theorem localMeasurementLowerBoundSubgoal : LocalMeasurementLowerBoundSubgoal := by
  classical
  intro n k N M O _ _ J _ _ κ Uf hκU hκ1 hκ2 hk ε δ hε hε1 w hw ψ hψ hwSum Pw hScard _hPinj g hg
  have hv : 0 ≤ 9 * ε^2 / (3 ^ k : ℝ) := by positivity
  by_cases hM : M ≤ 1
  · have hm : M = 0 ∨ M = 1 := by omega
    rcases hm with rfl | rfl <;> simp only [Nat.cast_zero, Nat.cast_one,
      Real.log_zero, Real.log_one, mul_zero, zero_sub]
    all_goals have hn : 0 ≤ 9 * (N:ℝ)*ε^2/(3^k:ℝ) := by positivity
    all_goals linarith
  have hMpos : 0 < M := by omega
  have hwNorm : ∀ j, ∑ o, w j o = 1 := by
    intro j
    have ht : ∀ o, Matrix.trace (tensorPauliProduct n (ψ j o)) = 1 := by
      intro o
      rw [tensorPauliProduct_trace]
      simp only [fun q => (hψ j o q).1.2, Finset.prod_const_one]
    have h := congrArg Matrix.trace (hwSum j)
    have hr := congrArg Complex.re h
    simp only [Matrix.trace_sum, Matrix.trace_smul, ht, Complex.re_sum,
      Complex.smul_re, smul_eq_mul, Complex.one_re, mul_one,
      Matrix.trace_one, Fintype.card_fin, Complex.natCast_re] at hr
    rw [← Finset.sum_mul] at hr
    have hd : (0:ℝ) < 2^n := by positivity
    exact (mul_left_inj' hd.ne').mp (by simpa only [one_mul, Nat.cast_pow, Nat.cast_ofNat] using hr)
  let W : Fin N → FinDist O := fun j => ⟨w j, hw j, hwNorm j⟩
  let μ : FinDist (Fin n → J) := ⟨κ.probOf,
    fun uw => Finset.prod_nonneg (fun i _ => κ.nonneg _), κ.sum_probOf n⟩
  have hUuw : ∀ uw, 0 < μ.prob uw → ∀ i, Uf (uw i) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    intro uw hp i
    apply hκU
    have hi : κ.prob (uw i) ≠ 0 := by
      intro hz
      have hzero : μ.prob uw = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      exact hp.ne' hzero
    exact lt_of_le_of_ne (κ.nonneg _) (Ne.symm hi)
  let q : Fin M → (Fin n → J) → Fin N → FinDist O := fun x uw j =>
    if hu : ∀ i, Uf (uw i) ∈ Matrix.unitaryGroup (Fin 2) ℂ then
      { prob := fun o => localShotValue Uf (w j o) (ψ j o) uw (theorem6CodeState n ε (Pw x))
        nonneg := fun o => local_shot_nonneg Uf (w j o) (hw j o) (ψ j o) (hψ j o) uw hu (Pw x) ε hε hε1
        sum_one := local_shot_sum Uf uw hu (w j) (ψ j) (hwSum j) _ (local_code_trace ε (Pw x) hk (hScard x)) }
    else W j
  have hq : ∀ x uw j o, 0 < μ.prob uw → (q x uw j).prob o =
      localShotValue Uf (w j o) (ψ j o) uw (theorem6CodeState n ε (Pw x)) := by
    intro x uw j o hp
    simp only [q, dif_pos (hUuw uw hp)]
  have hqweighted : ∀ x uw j o, μ.prob uw * (q x uw j).prob o = μ.prob uw *
      localShotValue Uf (w j o) (ψ j o) uw (theorem6CodeState n ε (Pw x)) := by
    intro x uw j o
    by_cases hz : μ.prob uw = 0
    · simp [hz]
    · rw [hq x uw j o (lt_of_le_of_ne (μ.nonneg uw) (Ne.symm hz))]
  have hqweighted2 : ∀ x uw j o, μ.prob uw * ((q x uw j).prob o)^2 = μ.prob uw *
      (localShotValue Uf (w j o) (ψ j o) uw (theorem6CodeState n ε (Pw x)))^2 := by
    intro x uw j o
    by_cases hz : μ.prob uw = 0
    · simp [hz]
    · rw [hq x uw j o (lt_of_le_of_ne (μ.nonneg uw) (Ne.symm hz))]
  have hshot := fun x j o => localShotPauliMomentSubgoal n k J κ Uf hκU hκ1 hκ2
    (w j o) (hw j o) (ψ j o) (hψ j o) (Pw x) hk (hScard x) ε hε hε1
  have hmean : ∀ j o, (1/(M:ℝ)) * ∑ x, ∑ uw, μ.prob uw * (q x uw j).prob o = (W j).prob o := by
    intro j o
    simp_rw [hqweighted]
    change (1/(M:ℝ)) * ∑ x, ∑ uw, (∏ i, κ.prob (uw i)) *
      localShotValue Uf (w j o) (ψ j o) uw (theorem6CodeState n ε (Pw x)) = w j o
    simp_rw [fun x => (hshot x j o).1]
    simp [Nat.ne_of_gt hMpos]
  have hsecond : ∀ j o, (1/(M:ℝ)) * ∑ x, ∑ uw, μ.prob uw * ((q x uw j).prob o)^2 ≤
      ((W j).prob o)^2 * (1 + 9 * ε^2 / (3^k:ℝ)) := by
    intro j o
    simp_rw [hqweighted2]
    have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => (hshot x j o).2)
    have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 1/(M:ℝ) by positivity)
    simpa [W, μ, FinDist.probOf, Nat.ne_of_gt hMpos] using h'
  have hmax : ∀ uw ω, ∃ d : Fin M, ∀ i, g uw ω i ≤ g uw ω d := by
    intro uw ω
    have hn : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0,hMpos⟩, Finset.mem_univ _⟩
    obtain ⟨d, _, hd⟩ := Finset.exists_max_image Finset.univ (g uw ω) hn
    exact ⟨d, fun i => hd i (Finset.mem_univ _)⟩
  let dec : (Fin n → J) → (Fin N → O) → Fin M := fun uw ω => Classical.choose (hmax uw ω)
  have hdec : ∀ uw ω i, g uw ω i ≤ g uw ω (dec uw ω) :=
      fun uw ω => Classical.choose_spec (hmax uw ω)
  have hgood : ∀ x uw, 0 < μ.prob uw →
      1-δ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => dec uw ω = x), ∏ j, (q x uw j).prob (ω j) := by
    intro x uw hp
    have he : ∀ ω, (∀ i, |g uw ω i - 3*ε*(if i=x then (1:ℝ) else 0)| ≤ ε) → dec uw ω = x := by
      intro ω hω
      exact local_good_prediction_decodes ε hε (g uw ω) x (dec uw ω) (hdec uw ω) hω
    have hi := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun ω : Fin N → O => ∏ j : Fin N, (q x uw j).prob (ω j))
      (show Finset.univ.filter (fun ω : Fin N → O => ∀ i, |g uw ω i - 3*ε*(if i=x then (1:ℝ) else 0)| ≤ ε) ⊆
          Finset.univ.filter (fun ω => dec uw ω = x) from fun ω hω =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ω (Finset.mem_filter.mp hω).2⟩)
      (fun ω _ _ => Finset.prod_nonneg (fun j _ => (q x uw j).nonneg _))
    have hg' := hg x uw
    simp_rw [hq x uw _ _ hp] at hi ⊢
    exact hg'.trans hi
  have h := local_product_record_moment_fano_supported M N (Fin n → J) O μ W q
    (9*ε^2/(3^k:ℝ)) δ hv hmean hsecond dec hgood
  convert h using 1
  ring

theorem localMeasurementLowerBound_finite_backend :
    ∃ (κ : FinDist (Fin 24)) (Uf : Fin 24 → Operator 2),
    (∀ j, 0 < κ.prob j → Uf j ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
    (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re =
        (Matrix.trace A).re / 2) ∧
    (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      A.IsHermitian → B.IsHermitian →
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
          (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re =
        ((Matrix.trace A).re * (Matrix.trace B).re +
          (Matrix.trace (A * B)).re) / 6) ∧
    (∀ (n k N M : ℕ) (O : Type) [Fintype O] [DecidableEq O]
(_hk1pos : 1 ≤ k)
    (ε δ : ℝ) (_hε : 0 < ε) (_hε1 : 3 * ε ≤ 1)
    (w : Fin N → O → ℝ) (_hw : ∀ j o, 0 ≤ w j o)
    (ψ : Fin N → O → Fin n → Operator 2)
    (_hψ : ∀ j o q, IsPureDensityOperator (ψ j o q))
    (_hwSum : ∀ j, (∑ o, (w j o * (2 ^ n : ℝ)) • tensorPauliProduct n (ψ j o)) = 1)
    (Pw : Fin M → Fin n → Option (Fin 3))
    (_hScard : ∀ m, tensorPauliWeight (Pw m) = k)
    (_hPinj : Function.Injective Pw)
    (g : (Fin n → Fin 24) → (Fin N → O) → Fin M → ℝ)
    (_hg : ∀ (x : Fin M) (uw : Fin n → Fin 24),
      1 - δ ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin N → O =>
            ∀ i, |g uw ω i - 3 * ε * (if i = x then (1 : ℝ) else 0)| ≤ ε),
        ∏ j, localShotValue Uf (w j (ω j)) (ψ j (ω j)) uw
          (theorem6CodeState n ε (Pw x))),
    9 * (N : ℝ) * ε ^ 2 / (3 ^ k : ℝ) ≥ (1 - δ) * Real.log (M : ℝ) - 1) := by
  obtain ⟨Uf, hU, h1, h2⟩ := qubit_conjugation_two_design_exists
  let κ : FinDist (Fin 24) :=
      {prob := fun _ => 1/24, nonneg := by intro i; norm_num, sum_one := by norm_num}
  have hκ1 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re =
        (Matrix.trace A).re / 2 := by
    intro P hP A
    have h := h1 P hP A
    change (∑ i, (1/24 : ℝ) * (Matrix.trace (A * (Uf i)ᴴ * P * Uf i)).re) = _
    rw [← Finset.mul_sum]
    simpa only [div_eq_mul_inv, one_mul, mul_comm, Matrix.mul_assoc] using h
  have hκ2 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      A.IsHermitian → B.IsHermitian →
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
          (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re =
        ((Matrix.trace A).re * (Matrix.trace B).re +
          (Matrix.trace (A * B)).re) / 6 := by
    intro P hP A B hA hB
    have h := h2 P hP A B hA hB
    change (∑ i, (1/24 : ℝ) * (Matrix.trace (A * (Uf i)ᴴ * P * Uf i)).re *
      (Matrix.trace (B * (Uf i)ᴴ * P * Uf i)).re) = _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    simpa only [div_eq_mul_inv, one_mul, mul_comm, Matrix.mul_assoc] using h
  refine ⟨κ, Uf, (fun i _ => hU i), hκ1, hκ2, ?_⟩
  intro n k N M O _ _ hk ε δ hε hε1 w hw ψ hψ hwSum Pw hScard hPinj g hg
  exact localMeasurementLowerBoundSubgoal n k N M O (Fin 24) κ Uf (fun i _ => hU i)
    hκ1 hκ2 hk ε δ hε hε1 w hw ψ hψ hwSum Pw hScard hPinj g hg
end Qatlib.Papers.ClassShadows20.LowerBound
