/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic
import Qatlib.Concepts.MonteCarloMean.LayeredMean.NativeComposedMean
import Qatlib.Concepts.ShadowModels.SampleBudget.RationalLinearSelection
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian
open scoped BigOperators Classical
set_option warningAsError false

variable {X : Type} [Fintype X] [DecidableEq X]

def evaluate (h : X → X → ℚ) {n : ℕ} (w : Fin n → X) : ℚ × ℕ :=
  let a := (Qatlib.Concepts.ShadowModels.UStatBackend.pairIndexList n).foldl
    (fun (a : ℚ × ℕ) z => (a.1+h (w z.1) (w z.2),a.2+1)) (0,0)
  (a.1/(n.choose 2 : ℚ),a.2)

private theorem fold_value {P : Type} (f : P → ℚ) (xs : List P) (a : ℚ × ℕ) :
    xs.foldl (fun a z => (a.1+f z,a.2+1)) a =
      (a.1+(xs.map f).sum,a.2+xs.length) := by
  induction xs generalizing a with
  | nil => simp
  | cons z xs ih => simp [ih,add_assoc,Nat.add_comm]

omit [Fintype X] [DecidableEq X] in

theorem evaluate_spec (h : X → X → ℚ) {n : ℕ} (w : Fin n → X) :
    Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h w = (((Qatlib.Concepts.ShadowModels.UStatBackend.pairIndexList n).map (fun z => h (w z.1) (w z.2))).sum /
      (n.choose 2 : ℚ), n.choose 2) := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate,fold_value,Qatlib.Concepts.ShadowModels.UStatBackend.pairIndexList_length]

omit [Fintype X] [DecidableEq X] in

theorem cast_evaluate (h : X → X → ℚ) {n : ℕ} (w : Fin n → X) :
    ((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h w).1 : ℝ) = Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic (fun x y => (h x y : ℝ)) w := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate_spec]
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic,Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelSum,Function.comp_def]

def run (h : X → X → ℚ) (n r : ℕ) (w : Fin (2*r+1) → Fin n → X) : ℚ × ℕ :=
  (Qatlib.Concepts.MonteCarloMean.LayeredMean.nativeRationalMedian r (fun i => (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h (w i)).1),
    ∑ i, (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h (w i)).2)

omit [Fintype X] [DecidableEq X] in

theorem run_pair_count (h : X → X → ℚ) (n r : ℕ) (w : Fin (2*r+1) → Fin n → X) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run h n r w).2 = (2*r+1)*n.choose 2 := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run,Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate_spec]

omit [Fintype X] [DecidableEq X] in

theorem run_cast (h : X → X → ℚ) (n r : ℕ) (w : Fin (2*r+1) → Fin n → X) :
    ((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run h n r w).1 : ℝ) =
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.sortedBlockMedian r (fun i => Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic (fun x y => (h x y : ℝ)) (w i)) := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run,Qatlib.Concepts.MonteCarloMean.LayeredMean.nativeRationalMedian_cast]
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.cast_evaluate]

noncomputable def blockLaw (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin n → X) :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw (fun _ => p)

noncomputable def varianceBudget (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (h : X → X → ℚ) (n : ℕ) : ℝ :=
  (4*(n-2 : ℕ) : ℝ)/((n : ℝ)*(n-1 : ℕ))*
    Qatlib.Concepts.ShadowModels.UStatBackend.pairConditionalVariance p (fun x y => (h x y : ℝ)) +
  2/((n : ℝ)*(n-1 : ℕ))*Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelVariance p (fun x y => (h x y : ℝ))

theorem actual_mean (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (h : X → X → ℚ) (n : ℕ) (hn : 2≤n) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).expect (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h w).1 : ℝ)) =
      Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean p (fun x y => (h x y : ℝ)) := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.cast_evaluate]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.finite_pair_u_statistic_unbiased X p n _ hn

theorem actual_variance (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (h : X → X → ℚ) (n : ℕ) (hn : 2≤n)
    (hsym : ∀ x y, h x y=h y x) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).variance (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h w).1 : ℝ)) = Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.varianceBudget p h n := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.actual_mean p h n hn]
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.cast_evaluate]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.finite_pair_u_statistic_exact_variance X p n _ hn
      (fun x y => by rw [hsym x y])

theorem failure_bound (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (h : X → X → ℚ) (n r : ℕ) (hn : 2≤n)
    (hsym : ∀ x y, h x y=h y x) (eps : ℝ) (heps : 0<eps)
    (hbudget : Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.varianceBudget p h n ≤ eps^2/3) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).probEvent (fun w : Fin (2*r+1) → Fin n → X =>
      eps < |((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run h n r w).1 : ℝ)-Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean p (fun x y => (h x y : ℝ))|) ≤
        (8/9 : ℝ)^r := by
  have ht := Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.chebyshev (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n)
    (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h w).1 : ℝ)) eps heps
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.actual_mean p h n hn,Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.actual_variance p h n hn hsym] at ht
  have hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n) (fun w =>
      eps < |((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h w).1 : ℝ)-Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean p (fun x y => (h x y : ℝ))|) ≤ 1/3 := by
    apply ht.trans
    apply (div_le_iff₀ (sq_pos_of_pos heps)).mpr
    linarith
  have hm := Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n)
    (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h w).1 : ℝ)) r _ eps heps.le hb
  simpa only [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run_cast,Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.cast_evaluate] using! hm

def countedRun (h : X → X → ℚ) (n r : ℕ) (w : Fin (2*r+1) → Fin n → X) : ℚ × ℕ × ℕ :=
  let v :=
      Qatlib.Concepts.ShadowModels.SampleBudget.qSelect
      (List.ofFn (fun i => (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h (w i)).1)) r
  (v.1, ∑ i, (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h (w i)).2, v.2)

omit [Fintype X] [DecidableEq X] in

theorem countedRun_spec (h : X → X → ℚ) (n r : ℕ) (w : Fin (2*r+1) → Fin n → X) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun h n r w).1=(Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run h n r w).1 ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun h n r w).2.1=(2*r+1)*n.choose 2 ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun h n r w).2.2≤10000*(2*r+1) := by
  have hc :=
      Qatlib.Concepts.ShadowModels.SampleBudget.rational_selection_median_exact_real_sorted_semantics r (fun i => (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h (w i)).1)
  refine ⟨?_,Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run_pair_count h n r w,hc.2⟩
  apply Rat.cast_injective (α:=ℝ)
  change ((Qatlib.Concepts.ShadowModels.SampleBudget.qSelect (List.ofFn (fun i => (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate h (w i)).1)) r).1 : ℝ)=_
  rw [hc.1,Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run_cast]
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.cast_evaluate]

theorem counted_failure_bound (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (h : X → X → ℚ) (n r : ℕ) (hn : 2≤n)
    (hsym : ∀ x y, h x y=h y x) (eps : ℝ) (heps : 0<eps)
    (hbudget : Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.varianceBudget p h n ≤ eps^2/3) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).probEvent (fun w : Fin (2*r+1) → Fin n → X =>
      eps < |((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun h n r w).1 : ℝ)-Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean p (fun x y => (h x y : ℝ))|) ≤
        (8/9 : ℝ)^r := by
  have he (w : Fin (2*r+1) → Fin n → X) :=
      (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun_spec h n r w).1
  simp only [he]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.failure_bound p h n r hn hsym eps heps hbudget

end Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian
