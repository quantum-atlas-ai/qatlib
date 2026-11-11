/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.InitializedRun
import Qatlib.Papers.QAOAScaling23.FreshRepeat.Run

/-!
# Fresh amplification with native candidate outputs

`freshNative` repeats controller trials and retains an actual candidate of lowest cost in
`NativeBatch`. When rank order matches cost order, failure probabilities multiply, and
logarithmically many repetitions achieve a prescribed error with a pathwise total-charge cap.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `native_failure_moment`: For ranks ordered by cost, the mean failure indicator of `k` fresh
  native trials is the `k`th power of the single-trial mean failure indicator.
* `native_amplified_run`: For ranks ordered by cost, trials with mean failure at most `1/2` and
  pathwise charge at most `B` yield failure probability at most positive `δ` after
  `outerIterations δ` repetitions, with total charge at most `outerIterations δ * B`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.FreshRepeat
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open CausalSearch
variable {I : Type}

/-- A batch of controller results with an optional best candidate, accumulated paid charge, and
list of runs. -/
structure NativeBatch (I : Type) where
  best : Option I
  totalPaid : ℕ
  runs : List (Result I I)

/-- Adds a controller result to a batch, accumulating its charge and selecting a lower-cost
candidate from the two saved candidates. -/
def combineNative (cost : I → ℝ) (out : Result I I) (b : NativeBatch I) : NativeBatch I :=
  ⟨match b.best with
    | none => some out.best
    | some previous => some (selectLower cost out.best previous),
    out.paid+b.totalPaid,out::b.runs⟩

/-- Runs `k` fresh controller trials and combines their saved candidates, paid charges, and
results. -/
def freshNative (cost : I → ℝ)
    (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (Result I I)) :
    ℕ → Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (NativeBatch I)
  | 0 => .pure ⟨none,0,[]⟩
  | k+1 => trial.bind (fun out => (freshNative cost trial k).map (combineNative cost out))

/-- The indicator that the batch does not contain a saved candidate of rank zero. -/
def nativeBatchFailure (rank : I → ℕ) (b : NativeBatch I) : ℝ :=
  if b.best.map rank=some 0 then 0 else 1

/-- If rank order agrees with cost order, selecting the lower-cost candidate gives the minimum
of the two ranks. -/
theorem selectLower_rank (cost : I → ℝ) (rank : I → ℕ)
    (horder : ∀ i j,rank i<rank j ↔ cost i<cost j) (old candidate : I) :
    rank (selectLower cost old candidate)=min (rank old) (rank candidate) := by
  unfold selectLower
  by_cases hc : cost candidate<cost old
  · rw [if_pos hc,min_eq_right ((horder _ _).mpr hc).le]
  · rw [if_neg hc,min_eq_left]
    exact Nat.le_of_not_gt (fun h => hc ((horder _ _).mp h))

/-- If rank order agrees with cost order, the failure indicator of a combined batch is the
product of the result and batch failure indicators. -/
theorem combineNative_failure (cost : I → ℝ) (rank : I → ℕ)
    (horder : ∀ i j,rank i<rank j ↔ cost i<cost j) (out : Result I I) (b : NativeBatch I) :
    nativeBatchFailure rank (combineNative cost out b)=physicalFailure rank out*nativeBatchFailure rank b := by
  cases hb : b.best with
  | none => simp [nativeBatchFailure,physicalFailure,combineNative,hb]
  | some j =>
    simp only [nativeBatchFailure,combineNative,hb,Option.map_some,selectLower_rank cost rank horder]
    by_cases ho : rank out.best=0 <;> by_cases hj : rank j=0 <;>
      simp [physicalFailure,ho,hj]

/-- For ranks ordered by cost, the mean failure indicator of `k` fresh native trials is the
`k`th power of the single-trial mean failure indicator. -/
theorem native_failure_moment (cost : I → ℝ) (rank : I → ℕ)
    (horder : ∀ i j,rank i<rank j ↔ cost i<cost j)
    (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (Result I I)) (k : ℕ) :
    (freshNative cost trial k).mean (nativeBatchFailure rank)=
      (trial.mean (physicalFailure rank))^k := by
  induction k with
  | zero => simp [freshNative,Tree.mean,nativeBatchFailure]
  | succ k ih =>
    rw [freshNative,Tree.mean_bind]
    simp_rw [Tree.mean_map,combineNative_failure cost rank horder,Tree.mean_mul,ih]
    have he : (fun out => physicalFailure rank out*(trial.mean (physicalFailure rank))^k)=
        fun out => (trial.mean (physicalFailure rank))^k*physicalFailure rank out := by funext out; ring
    rw [he,Tree.mean_mul]
    exact (pow_succ _ k).symm

/-- If every trial pays at most `B`, every batch of `k` fresh trials pays at most `k * B`. -/
theorem freshNative_cap (cost : I → ℝ)
    (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (Result I I))
    (B : ℕ) (hcap : trial.All (fun out => out.paid≤B)) (k : ℕ) :
    (freshNative cost trial k).All (fun b => b.totalPaid≤k*B) := by
  induction k with
  | zero => simp [freshNative,Tree.All]
  | succ k ih =>
    rw [freshNative,Tree.all_bind]
    apply Tree.all_mono _ hcap
    intro out hout
    rw [Tree.all_map]
    apply Tree.all_mono _ ih
    intro b hb
    change out.paid+b.totalPaid≤(k+1)*B
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- For ranks ordered by cost, trials with mean failure at most `1/2` and pathwise charge at
most `B` yield failure probability at most positive `δ` after `outerIterations δ`
repetitions, with total charge at most `outerIterations δ * B`. See [ShaydulinEtAl2024]. -/
theorem native_amplified_run (cost : I → ℝ) (rank : I → ℕ)
    (horder : ∀ i j,rank i<rank j ↔ cost i<cost j)
    (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (Result I I))
    (htrial : trial.mean (physicalFailure rank)≤1/2)
    (B : ℕ) (hcap : trial.All (fun out => out.paid≤B)) (δ : ℝ) (hδ : 0<δ) :
    (freshNative cost trial (outerIterations δ)).probability
        (fun b => b.best.map rank≠some 0)≤δ ∧
      (freshNative cost trial (outerIterations δ)).All
        (fun b => b.totalPaid≤outerIterations δ*B) := by
  have he : (freshNative cost trial (outerIterations δ)).probability
      (fun b => b.best.map rank≠some 0)=
      (freshNative cost trial (outerIterations δ)).mean (nativeBatchFailure rank) := by
    apply Tree.mean_congr
    apply Tree.all_of_forall
    intro b
    by_cases hb : b.best.map rank=some 0 <;> simp [nativeBatchFailure,hb]
  rw [he,native_failure_moment cost rank horder]
  refine ⟨(pow_le_pow_left₀ ?_ htrial _).trans (dyadic_error_bound δ hδ),
    freshNative_cap cost trial B hcap _⟩
  apply Tree.mean_nonneg
  apply Tree.all_of_forall
  intro out
  unfold physicalFailure
  split_ifs <;> norm_num
end Qatlib.Papers.QAOAScaling23.FreshRepeat
