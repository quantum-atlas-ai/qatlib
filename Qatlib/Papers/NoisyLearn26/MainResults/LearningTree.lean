/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.LearningTree

open Qatlib.Papers.NoisyLearn26.MainResults

theorem tvDist_nonneg {X : Type*} [Fintype X] (p q : X → ℝ) : 0 ≤ tvDist p q := by
  unfold tvDist
  positivity

theorem tvDist_comm {X : Type*} [Fintype X] (p q : X → ℝ) :
    tvDist p q = tvDist q p := by
  unfold tvDist
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [abs_sub_comm]

def layerTreeTail {A : Type*} [Fintype A] {N : ℕ} (T : LayerTree A (N + 1))
    (a : A) : LayerTree A N where
  kernel i u b := T.kernel i.succ (Fin.cons a u) b
  kernel_nonneg i u b := T.kernel_nonneg i.succ (Fin.cons a u) b
  kernel_sum_one i u := T.kernel_sum_one i.succ (Fin.cons a u)

theorem pathPrefix_cons_succ {A : Type*} [Fintype A] {N : ℕ} (a : A)
    (xs : Fin N → A) (i : Fin N) :
    LayerTree.pathPrefix (A := A) (Fin.cons a xs) i.succ =
      Fin.cons a (LayerTree.pathPrefix xs i) := by
  funext j
  cases j using Fin.cases <;> rfl

theorem pathProb_nonneg {A : Type*} [Fintype A] {N : ℕ} (T : LayerTree A N)
    (x : Fin N → A) : 0 ≤ T.pathProb x := by
  unfold LayerTree.pathProb
  exact Finset.prod_nonneg (fun i _ => T.kernel_nonneg i _ _)

theorem pathProb_cons {A : Type*} [Fintype A] {N : ℕ} (T : LayerTree A (N + 1))
    (a : A) (xs : Fin N → A) :
    T.pathProb (Fin.cons a xs) =
      T.kernel 0 (fun j => Fin.elim0 j) a * (layerTreeTail T a).pathProb xs := by
  unfold LayerTree.pathProb
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.cons_zero]
    have hpre : LayerTree.pathPrefix (A := A) (Fin.cons a xs) (0 : Fin (N + 1)) =
        fun j => Fin.elim0 j := by
      funext j
      exact Fin.elim0 j
    rw [hpre]
    rfl
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.cons_succ, pathPrefix_cons_succ]
    rfl

theorem pathProb_sum_one {A : Type*} [Fintype A] {N : ℕ} (T : LayerTree A N) :
    (∑ x : Fin N → A, T.pathProb x) = 1 := by
  revert T
  induction N with
  | zero =>
      intro T
      have huniq : ∀ x : Fin 0 → A, T.pathProb x = 1 := by
        intro x
        simp [LayerTree.pathProb]
      rw [Finset.sum_congr rfl (fun x _ => huniq x)]
      simp
  | succ N ih =>
      intro T
      calc (∑ x : Fin (N + 1) → A, T.pathProb x)
          = ∑ p : A × (Fin N → A), T.pathProb (Fin.cons p.1 p.2) := by
            rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => A))
              (fun x => T.pathProb x)]
            rfl
        _ = ∑ a, ∑ xs : Fin N → A, T.pathProb (Fin.cons a xs) :=
            Fintype.sum_prod_type _
        _ = ∑ a, ∑ xs : Fin N → A,
              T.kernel 0 (fun j => Fin.elim0 j) a * (layerTreeTail T a).pathProb xs := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro xs _
            rw [pathProb_cons]
        _ = ∑ a, (T.kernel 0 (fun j => Fin.elim0 j) a *
              ∑ xs : Fin N → A, (layerTreeTail T a).pathProb xs) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
        _ = ∑ a, (T.kernel 0 (fun j => Fin.elim0 j) a * 1) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [ih (layerTreeTail T a)]
        _ = 1 := by
            rw [← Finset.sum_mul]
            rw [T.kernel_sum_one 0 (fun j => Fin.elim0 j)]
            ring

theorem distinguishability_propagation
    {A : Type*} [Fintype A] [DecidableEq A] {N : ℕ}
    (T T' : LayerTree A N) (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ (i : Fin N) (u : Fin i.val → A),
      tvDist (T.kernel i u) (T'.kernel i u) ≤ ε) :
    leafTV T T' ≤ ε * N := by
  induction N with
  | zero =>
      have hzero : ∀ x : Fin 0 → A, T.pathProb x = T'.pathProb x := by
        intro x
        simp [LayerTree.pathProb]
      unfold leafTV
      simp only [hzero, sub_self, abs_zero]
      simp
  | succ N ih =>

      have hstep0 : tvDist (T.kernel 0 (fun j => Fin.elim0 j))
          (T'.kernel 0 (fun j => Fin.elim0 j)) ≤ ε :=
        hstep 0 (fun j => Fin.elim0 j)

      have hterm : ∀ (a : A) (xs : Fin N → A),
          |T.pathProb (Fin.cons a xs) - T'.pathProb (Fin.cons a xs)| ≤
            T.kernel 0 (fun j => Fin.elim0 j) a *
                |(layerTreeTail T a).pathProb xs - (layerTreeTail T' a).pathProb xs| +
              |T.kernel 0 (fun j => Fin.elim0 j) a -
                T'.kernel 0 (fun j => Fin.elim0 j) a| *
                (layerTreeTail T' a).pathProb xs := by
        intro a xs
        rw [pathProb_cons, pathProb_cons]
        have hq : 0 ≤ (layerTreeTail T' a).pathProb xs := pathProb_nonneg _ _
        have hf : 0 ≤ T.kernel 0 (fun j => Fin.elim0 j) a :=
          T.kernel_nonneg 0 _ a
        calc |T.kernel 0 (fun j => Fin.elim0 j) a * (layerTreeTail T a).pathProb xs -
                T'.kernel 0 (fun j => Fin.elim0 j) a * (layerTreeTail T' a).pathProb xs|
            = |T.kernel 0 (fun j => Fin.elim0 j) a *
                  ((layerTreeTail T a).pathProb xs - (layerTreeTail T' a).pathProb xs) +
                (T.kernel 0 (fun j => Fin.elim0 j) a -
                  T'.kernel 0 (fun j => Fin.elim0 j) a) *
                  (layerTreeTail T' a).pathProb xs| := by
                congr 1
                ring
          _ ≤ |T.kernel 0 (fun j => Fin.elim0 j) a *
                  ((layerTreeTail T a).pathProb xs - (layerTreeTail T' a).pathProb xs)| +
                |(T.kernel 0 (fun j => Fin.elim0 j) a -
                  T'.kernel 0 (fun j => Fin.elim0 j) a) *
                  (layerTreeTail T' a).pathProb xs| := abs_add_le _ _
          _ = T.kernel 0 (fun j => Fin.elim0 j) a *
                  |(layerTreeTail T a).pathProb xs - (layerTreeTail T' a).pathProb xs| +
                |T.kernel 0 (fun j => Fin.elim0 j) a -
                  T'.kernel 0 (fun j => Fin.elim0 j) a| *
                  (layerTreeTail T' a).pathProb xs := by
                rw [abs_mul, abs_mul, abs_of_nonneg hf, abs_of_nonneg hq]

      have hsum_bound :
          (∑ a, ∑ xs : Fin N → A,
              |T.pathProb (Fin.cons a xs) - T'.pathProb (Fin.cons a xs)|) ≤
            ∑ a, (T.kernel 0 (fun j => Fin.elim0 j) a *
                (2 * leafTV (layerTreeTail T a) (layerTreeTail T' a)) +
              |T.kernel 0 (fun j => Fin.elim0 j) a -
                T'.kernel 0 (fun j => Fin.elim0 j) a|) := by
        apply Finset.sum_le_sum
        intro a _
        calc (∑ xs : Fin N → A,
                |T.pathProb (Fin.cons a xs) - T'.pathProb (Fin.cons a xs)|)
            ≤ ∑ xs : Fin N → A,
                (T.kernel 0 (fun j => Fin.elim0 j) a *
                    |(layerTreeTail T a).pathProb xs - (layerTreeTail T' a).pathProb xs| +
                  |T.kernel 0 (fun j => Fin.elim0 j) a -
                    T'.kernel 0 (fun j => Fin.elim0 j) a| *
                    (layerTreeTail T' a).pathProb xs) :=
              Finset.sum_le_sum (fun xs _ => hterm a xs)
          _ = T.kernel 0 (fun j => Fin.elim0 j) a *
                  (∑ xs : Fin N → A,
                    |(layerTreeTail T a).pathProb xs - (layerTreeTail T' a).pathProb xs|) +
                |T.kernel 0 (fun j => Fin.elim0 j) a -
                  T'.kernel 0 (fun j => Fin.elim0 j) a| *
                  (∑ xs : Fin N → A, (layerTreeTail T' a).pathProb xs) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = T.kernel 0 (fun j => Fin.elim0 j) a *
                  (2 * leafTV (layerTreeTail T a) (layerTreeTail T' a)) +
                |T.kernel 0 (fun j => Fin.elim0 j) a -
                  T'.kernel 0 (fun j => Fin.elim0 j) a| := by
              rw [pathProb_sum_one (layerTreeTail T' a), mul_one]
              congr 2
              unfold leafTV
              ring

      have hfirst :
          (∑ a, T.kernel 0 (fun j => Fin.elim0 j) a *
              (2 * leafTV (layerTreeTail T a) (layerTreeTail T' a))) ≤ 2 * ε * N := by
        calc (∑ a, T.kernel 0 (fun j => Fin.elim0 j) a *
                (2 * leafTV (layerTreeTail T a) (layerTreeTail T' a)))
            ≤ ∑ a, T.kernel 0 (fun j => Fin.elim0 j) a * (2 * (ε * N)) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul_of_nonneg_left _ (T.kernel_nonneg 0 _ a)
              have hih := ih (layerTreeTail T a) (layerTreeTail T' a)
                (fun i u => hstep i.succ (Fin.cons a u))
              linarith
          _ = 2 * ε * N := by
              rw [← Finset.sum_mul, T.kernel_sum_one 0 (fun j => Fin.elim0 j)]
              ring
      have hsecond :
          (∑ a, |T.kernel 0 (fun j => Fin.elim0 j) a -
                T'.kernel 0 (fun j => Fin.elim0 j) a|) ≤ 2 * ε := by
        have htv : (∑ a, |T.kernel 0 (fun j => Fin.elim0 j) a -
              T'.kernel 0 (fun j => Fin.elim0 j) a|) =
            2 * tvDist (T.kernel 0 (fun j => Fin.elim0 j))
              (T'.kernel 0 (fun j => Fin.elim0 j)) := by
          unfold tvDist
          ring
        rw [htv]
        linarith
      have hkey :
          (∑ a, ∑ xs : Fin N → A,
              |T.pathProb (Fin.cons a xs) - T'.pathProb (Fin.cons a xs)|) ≤
            2 * ε * N + 2 * ε := by
        calc (∑ a, ∑ xs : Fin N → A,
                |T.pathProb (Fin.cons a xs) - T'.pathProb (Fin.cons a xs)|)
            ≤ ∑ a, (T.kernel 0 (fun j => Fin.elim0 j) a *
                (2 * leafTV (layerTreeTail T a) (layerTreeTail T' a)) +
              |T.kernel 0 (fun j => Fin.elim0 j) a -
                T'.kernel 0 (fun j => Fin.elim0 j) a|) := hsum_bound
          _ = (∑ a, T.kernel 0 (fun j => Fin.elim0 j) a *
                (2 * leafTV (layerTreeTail T a) (layerTreeTail T' a))) +
              (∑ a, |T.kernel 0 (fun j => Fin.elim0 j) a -
                T'.kernel 0 (fun j => Fin.elim0 j) a|) := by
              rw [Finset.sum_add_distrib]
          _ ≤ 2 * ε * N + 2 * ε := add_le_add hfirst hsecond
      unfold leafTV
      have htot : (∑ x : Fin (N + 1) → A,
            |T.pathProb x - T'.pathProb x|) =
          ∑ a, ∑ xs : Fin N → A,
            |T.pathProb (Fin.cons a xs) - T'.pathProb (Fin.cons a xs)| := by
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => A))
          (fun x => |T.pathProb x - T'.pathProb x|)]
        rw [Fintype.sum_prod_type]
        rfl
      rw [htot]
      push_cast
      linarith [hkey]

end Qatlib.Papers.NoisyLearn26.MainResults.LearningTree
