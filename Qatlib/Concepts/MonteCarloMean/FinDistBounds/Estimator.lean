/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

structure FinDist (X : Type*) [Fintype X] where

  prob : X → ℝ

  nonneg : ∀ x, 0 ≤ prob x

  sum_one : ∑ x, prob x = 1

namespace FinDist

variable {X : Type*} [Fintype X] [DecidableEq X]

def expect (p : FinDist X) (f : X → ℝ) : ℝ := ∑ x, p.prob x * f x

def probOf {L : ℕ} (p : FinDist X) (ω : Fin L → X) : ℝ := ∏ i, p.prob (ω i)

def probEvent {L : ℕ} (p : FinDist X) (E : (Fin L → X) → Prop) [DecidablePred E] : ℝ :=
  ∑ ω ∈ Finset.univ.filter E, p.probOf ω

theorem sum_sub_mean (p : FinDist X) (f : X → ℝ) :
    ∑ x, p.prob x * (f x - expect p f) = 0 := by
  have h1 : ∀ x : X, p.prob x * (f x - expect p f)
      = p.prob x * f x - expect p f * p.prob x := fun x => by ring
  have h2 : ∑ x, p.prob x * (f x - expect p f)
      = (∑ x, p.prob x * f x) - (∑ x, expect p f * p.prob x) := by
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib]
  have h3 : (∑ x, expect p f * p.prob x) = expect p f * (∑ x, p.prob x) :=
    (Finset.mul_sum Finset.univ (fun x => p.prob x) (expect p f)).symm
  rw [h2, h3, p.sum_one, mul_one]
  exact sub_self (∑ x, p.prob x * f x)

theorem sum_probOf (p : FinDist X) (L : ℕ) : ∑ ω : Fin L → X, p.probOf ω = 1 := by
  have hswap : ∑ ω : Fin L → X, ∏ i, p.prob (ω i)
      = ∑ ω ∈ Fintype.piFinset (fun _ : Fin L => (Finset.univ : Finset X)),
          ∏ i, p.prob (ω i) :=
    Finset.sum_congr rfl (fun ω _ => rfl)
  unfold probOf
  rw [hswap, ← Finset.prod_univ_sum, Finset.prod_congr rfl (fun i _ => p.sum_one)]
  simp

theorem expect_prod {L : ℕ} (p : FinDist X) (g : Fin L → X → ℝ) :
    ∑ ω : Fin L → X, p.probOf ω * ∏ k, g k (ω k)
      = ∏ k, (∑ x, p.prob x * g k x) := by
  have habs : ∀ ω : Fin L → X,
      p.probOf ω * ∏ k, g k (ω k) = ∏ k, (p.prob (ω k) * g k (ω k)) := by
    intro ω
    unfold probOf
    rw [← Finset.prod_mul_distrib]
  calc ∑ ω : Fin L → X, p.probOf ω * ∏ k, g k (ω k)
      = ∑ ω : Fin L → X, ∏ k, (p.prob (ω k) * g k (ω k)) :=
        Finset.sum_congr rfl (fun ω _ => habs ω)
    _ = ∑ ω ∈ Fintype.piFinset (fun _ : Fin L => (Finset.univ : Finset X)),
          ∏ k, (p.prob (ω k) * g k (ω k)) :=
        Finset.sum_congr rfl (fun ω _ => rfl)
    _ = ∏ k, (∑ x, p.prob x * g k x) := by
        exact (Finset.prod_univ_sum
          (t := fun _ : Fin L => (Finset.univ : Finset X))
          (f := fun k x => p.prob x * g k x)).symm

theorem expect_coord {L : ℕ} (p : FinDist X) (k : Fin L) (h : X → ℝ) :
    ∑ ω : Fin L → X, p.probOf ω * h (ω k) = ∑ x, p.prob x * h x := by
  have hsplit : ∀ ω : Fin L → X,
      h (ω k) = ∏ j, (if j = k then h (ω j) else 1) := by
    intro ω
    rw [Finset.prod_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hjk
      simp [hjk]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  have hex := expect_prod p (fun j x => if j = k then h x else 1)
  calc ∑ ω : Fin L → X, p.probOf ω * h (ω k)
      = ∑ ω : Fin L → X, p.probOf ω * ∏ j, (if j = k then h (ω j) else 1) :=
        Finset.sum_congr rfl (fun ω _ => by rw [hsplit ω])
    _ = ∏ j, (∑ x, p.prob x * (if j = k then h x else 1)) := hex
    _ = ∑ x, p.prob x * h x := by
        rw [Finset.prod_eq_single k]
        · simp
        · intro j _ hjk
          simp only [hjk, if_false, mul_one]
          exact p.sum_one
        · intro hcon
          exact absurd (Finset.mem_univ k) hcon

noncomputable def avg {L : ℕ} (f : X → ℝ) (ω : Fin L → X) : ℝ := (∑ k, f (ω k)) / L

theorem expect_avg {L : ℕ} (p : FinDist X) (f : X → ℝ) (hL : 0 < L) :
    ∑ ω : Fin L → X, p.probOf ω * avg f ω = expect p f := by
  calc ∑ ω : Fin L → X, p.probOf ω * avg f ω
      = ∑ ω : Fin L → X, (p.probOf ω * ∑ k : Fin L, f (ω k)) / L := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        show p.probOf ω * ((∑ k : Fin L, f (ω k)) / L) = _
        rw [mul_div_assoc]
    _ = (∑ ω : Fin L → X, p.probOf ω * ∑ k : Fin L, f (ω k)) / L := by
        exact (Finset.sum_div (Finset.univ : Finset (Fin L → X))
          (fun ω : Fin L → X => p.probOf ω * ∑ k : Fin L, f (ω k)) L).symm
    _ = (∑ k : Fin L, ∑ ω : Fin L → X, p.probOf ω * f (ω k)) / L := by
        refine congrArg (fun t : ℝ => t / (L : ℝ)) ?_
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = (∑ k : Fin L, ∑ x, p.prob x * f x) / L := by
        refine congrArg (fun t : ℝ => t / (L : ℝ)) ?_
        exact Finset.sum_congr rfl fun k _ => expect_coord p k f
    _ = expect p f := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        exact mul_div_cancel_left₀ _ (by exact_mod_cast hL.ne')

def variance (p : FinDist X) (f : X → ℝ) : ℝ := expect p (fun x => (f x - expect p f) ^ 2)

theorem expect_avg_sub_sq {L : ℕ} (p : FinDist X) (f : X → ℝ) (hL : 0 < L) :
    ∑ ω : Fin L → X, p.probOf ω * (avg f ω - expect p f) ^ 2
      = variance p f / L := by
  set μ := expect p f with hμ
  have hcenter : ∀ ω : Fin L → X,
      avg f ω - μ = (∑ k : Fin L, (f (ω k) - μ)) / L := by
    intro ω
    have hμL : μ = (μ * L) / L := by field_simp
    show (∑ k : Fin L, f (ω k)) / L - μ = (∑ k : Fin L, (f (ω k) - μ)) / L
    have hsum : ∑ k : Fin L, f (ω k) - μ * L = ∑ k : Fin L, (f (ω k) - μ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring
    conv_lhs => rw [hμL]
    rw [div_sub_div_same, hsum]
  have hsq : ∀ ω : Fin L → X,
      (avg f ω - μ) ^ 2
        = (∑ k : Fin L, ∑ j : Fin L, (f (ω k) - μ) * (f (ω j) - μ)) / L ^ 2 := by
    intro ω
    rw [hcenter ω, div_pow, sq, Finset.sum_mul_sum]
  have hmean : ∑ x, p.prob x * (f x - μ) = 0 := sum_sub_mean p f

  have hterm : ∀ k j : Fin L,
      ∑ ω : Fin L → X, p.probOf ω * ((f (ω k) - μ) * (f (ω j) - μ))
        = (if k = j then variance p f else 0) := by
    intro k j
    by_cases hkj : k = j
    · subst hkj
      have hprod : ∀ ω : Fin L → X,
          ∏ m, (if m = k then (f (ω m) - μ) * (f (ω m) - μ) else 1)
            = (f (ω k) - μ) * (f (ω k) - μ) := by
        intro ω
        rw [Finset.prod_eq_single k]
        · simp only [eq_self, if_true]
        · intro m _ hmk
          simp only [hmk, if_false]
        · intro hcon
          exact absurd (Finset.mem_univ k) hcon
      have hrhs : ∏ m, (∑ x, p.prob x * (if m = k then (f x - μ) * (f x - μ) else 1))
          = variance p f := by
        rw [Finset.prod_eq_single k]
        · simp only [eq_self, if_true]
          exact Finset.sum_congr rfl fun x _ => by
            show p.prob x * ((f x - μ) * (f x - μ))
              = p.prob x * ((f x - expect p f) ^ 2)
            rw [hμ]
            ring
        · intro m _ hmk
          rw [show (∑ x, p.prob x * (if m = k then (f x - μ) * (f x - μ) else 1))
              = ∑ x, p.prob x from
            Finset.sum_congr rfl (fun x _ => by simp only [hmk, if_false, mul_one])]
          exact p.sum_one
        · intro hcon
          exact absurd (Finset.mem_univ k) hcon
      rw [if_pos rfl]
      calc ∑ ω : Fin L → X, p.probOf ω * ((f (ω k) - μ) * (f (ω k) - μ))
          = ∑ ω : Fin L → X, p.probOf ω
              * ∏ m, (if m = k then (f (ω m) - μ) * (f (ω m) - μ) else 1) :=
            Finset.sum_congr rfl fun ω _ => by rw [hprod ω]
        _ = ∏ m, (∑ x, p.prob x * (if m = k then (f x - μ) * (f x - μ) else 1)) :=
            expect_prod p (fun m x => if m = k then (f x - μ) * (f x - μ) else 1)
        _ = variance p f := hrhs
    · have hprod : ∀ ω : Fin L → X,
          ∏ m, (if m = k ∨ m = j then f (ω m) - μ else 1)
            = (f (ω k) - μ) * (f (ω j) - μ) := by
        intro ω
        rw [← Finset.prod_subset (Finset.subset_univ (insert k {j}))
          (fun m _ hm => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rw [if_neg (fun hor => by tauto)]),
          Finset.prod_insert (Finset.notMem_singleton.mpr hkj), Finset.prod_singleton]
        simp only [true_or, or_true, if_true]
      have hrhs : ∏ m, (∑ x, p.prob x * (if m = k ∨ m = j then f x - μ else 1))
          = 0 := by
        have hz : (∑ x, p.prob x * (if k = k ∨ k = j then f x - μ else 1)) = 0 := by
          simp only [eq_self, true_or, if_true]
          exact hmean
        exact Finset.prod_eq_zero (Finset.mem_univ k) hz
      rw [if_neg hkj]
      calc ∑ ω : Fin L → X, p.probOf ω * ((f (ω k) - μ) * (f (ω j) - μ))
          = ∑ ω : Fin L → X, p.probOf ω * ∏ m, (if m = k ∨ m = j then f (ω m) - μ else 1) :=
            Finset.sum_congr rfl fun ω _ => by rw [hprod ω]
        _ = ∏ m, (∑ x, p.prob x * (if m = k ∨ m = j then f x - μ else 1)) :=
            expect_prod p (fun m x => if m = k ∨ m = j then f x - μ else 1)
        _ = 0 := hrhs

  have hdiag : ∑ k : Fin L, (∑ j : Fin L, (if k = j then variance p f else 0))
      = L * variance p f := by
    have hinner : ∀ k : Fin L,
        (∑ j : Fin L, (if k = j then variance p f else 0)) = variance p f := by
      intro k
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ k)]
    rw [Finset.sum_congr rfl (fun k _ => hinner k), Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin]
  calc ∑ ω : Fin L → X, p.probOf ω * (avg f ω - μ) ^ 2
      = ∑ ω : Fin L → X, p.probOf ω
          * ((∑ k : Fin L, ∑ j : Fin L, (f (ω k) - μ) * (f (ω j) - μ)) / L ^ 2) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hsq ω]
    _ = ∑ ω : Fin L → X, (p.probOf ω
          * ∑ k : Fin L, ∑ j : Fin L, (f (ω k) - μ) * (f (ω j) - μ)) / L ^ 2 := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [mul_div_assoc]
    _ = (∑ ω : Fin L → X, p.probOf ω
          * ∑ k : Fin L, ∑ j : Fin L, (f (ω k) - μ) * (f (ω j) - μ)) / L ^ 2 := by
        exact (Finset.sum_div (Finset.univ : Finset (Fin L → X))
          (fun ω : Fin L → X => p.probOf ω
            * ∑ k : Fin L, ∑ j : Fin L, (f (ω k) - μ) * (f (ω j) - μ))
          ((L : ℝ) ^ 2)).symm
    _ = (∑ k : Fin L, ∑ j : Fin L, ∑ ω : Fin L → X,
          p.probOf ω * ((f (ω k) - μ) * (f (ω j) - μ))) / L ^ 2 := by
        have h1 : (∑ ω : Fin L → X, p.probOf ω
              * ∑ k : Fin L, ∑ j : Fin L, (f (ω k) - μ) * (f (ω j) - μ))
            = ∑ ω : Fin L → X, ∑ k : Fin L, ∑ j : Fin L,
                p.probOf ω * ((f (ω k) - μ) * (f (ω j) - μ)) := by
          simp only [Finset.mul_sum]
        have h2 : (∑ ω : Fin L → X, ∑ k : Fin L, ∑ j : Fin L,
                p.probOf ω * ((f (ω k) - μ) * (f (ω j) - μ)))
            = ∑ k : Fin L, ∑ j : Fin L, ∑ ω : Fin L → X,
                p.probOf ω * ((f (ω k) - μ) * (f (ω j) - μ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
        rw [h1, h2]
    _ = (∑ k : Fin L, ∑ j : Fin L, (if k = j then variance p f else 0)) / L ^ 2 := by
        refine congrArg (fun t => t / (L : ℝ) ^ 2) ?_
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hterm k j
    _ = variance p f / L := by
        rw [hdiag, sq, mul_div_mul_left _ _ (by exact_mod_cast hL.ne')]

theorem chebyshev_avg {L : ℕ} (p : FinDist X) (f : X → ℝ) (hL : 0 < L) (ε : ℝ)
    (hε : 0 < ε) :
    probEvent (L := L) p (fun ω : Fin L → X => ε < |avg f ω - expect p f|)
      ≤ variance p f / (L * ε ^ 2) := by
  have hnn : ∀ ω : Fin L → X, 0 ≤ p.probOf ω :=
    fun ω => Finset.prod_nonneg fun i _ => p.nonneg _
  have hstep1 : ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
        p.probOf ω
      ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
          p.probOf ω * (avg f ω - expect p f) ^ 2 / ε ^ 2 := by
    refine Finset.sum_le_sum fun ω hω => ?_
    have hlt : ε < |avg f ω - expect p f| := (Finset.mem_filter.mp hω).2
    have habsnn : 0 ≤ |avg f ω - expect p f| := abs_nonneg _
    have hd : ε ^ 2 ≤ (avg f ω - expect p f) ^ 2 := by
      nlinarith [hlt, habsnn, sq_abs (avg f ω - expect p f)]
    calc p.probOf ω = p.probOf ω * 1 := by ring
      _ ≤ p.probOf ω * ((avg f ω - expect p f) ^ 2 / ε ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (hnn ω)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2), one_mul]
          exact hd
      _ = p.probOf ω * (avg f ω - expect p f) ^ 2 / ε ^ 2 := by ring
  have hstep2 : ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
        p.probOf ω * (avg f ω - expect p f) ^ 2 / ε ^ 2
      = (∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
          p.probOf ω * (avg f ω - expect p f) ^ 2) / ε ^ 2 := by
        exact (Finset.sum_div (Finset.univ.filter
          (fun ω => ε < |avg f ω - expect p f|))
          (fun ω => p.probOf ω * (avg f ω - expect p f) ^ 2) _).symm
  have hstep3 : (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
        p.probOf ω * (avg f ω - expect p f) ^ 2)
      ≤ ∑ ω : Fin L → X, p.probOf ω * (avg f ω - expect p f) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => mul_nonneg (Finset.prod_nonneg fun i _ => p.nonneg _)
        (sq_nonneg _))
  have hstep4 : ∑ ω : Fin L → X, p.probOf ω * (avg f ω - expect p f) ^ 2
      = variance p f / L := expect_avg_sub_sq p f hL
  show (∑ ω ∈ Finset.univ.filter
      (fun ω : Fin L → X => ε < |avg f ω - expect p f|), p.probOf ω)
    ≤ variance p f / (L * ε ^ 2)
  calc (∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => ε < |avg f ω - expect p f|), p.probOf ω)
      ≤ (∑ ω : Fin L → X, p.probOf ω * (avg f ω - expect p f) ^ 2) / ε ^ 2 := by
        calc (∑ ω ∈ Finset.univ.filter
                (fun ω : Fin L → X => ε < |avg f ω - expect p f|), p.probOf ω)
            ≤ (∑ ω ∈ Finset.univ.filter
                (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
                p.probOf ω * (avg f ω - expect p f) ^ 2 / ε ^ 2) := hstep1
          _ = (∑ ω ∈ Finset.univ.filter
                (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
                p.probOf ω * (avg f ω - expect p f) ^ 2) / ε ^ 2 := hstep2
          _ ≤ ((∑ ω : Fin L → X, p.probOf ω * (avg f ω - expect p f) ^ 2)) / ε ^ 2 := by
              have hmono : (∑ ω ∈ Finset.univ.filter
                  (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
                  p.probOf ω * (avg f ω - expect p f) ^ 2)
                  ≤ (∑ ω : Fin L → X, p.probOf ω * (avg f ω - expect p f) ^ 2) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun ω _ _ => mul_nonneg (Finset.prod_nonneg fun i _ => p.nonneg _)
                    (sq_nonneg _))
              calc (∑ ω ∈ Finset.univ.filter
                    (fun ω : Fin L → X => ε < |avg f ω - expect p f|),
                    p.probOf ω * (avg f ω - expect p f) ^ 2) / ε ^ 2
                  ≤ ((∑ ω : Fin L → X,
                      p.probOf ω * (avg f ω - expect p f) ^ 2)) / ε ^ 2 := by
                      rw [le_div_iff₀ (pow_pos hε 2)]
                      field_simp
                      exact hmono
          _ = ((∑ ω : Fin L → X, p.probOf ω * (avg f ω - expect p f) ^ 2)) / ε ^ 2 := rfl
    _ = variance p f / L / ε ^ 2 := by rw [hstep4]
    _ = variance p f / (L * ε ^ 2) := by
        rw [show (variance p f / L / ε ^ 2) = variance p f / (L * ε ^ 2) from by
          field_simp]

theorem union_bound {L : ℕ} (p : FinDist X) {M : ℕ} (E : Fin M → (Fin L → X) → Prop)
    [∀ m, DecidablePred (E m)]
    [DecidablePred (fun ω : Fin L → X => ∃ m, E m ω)] :
    probEvent p (fun ω : Fin L → X => ∃ m, E m ω)
      ≤ ∑ m : Fin M, probEvent p (E m) := by
  classical
  have hsplit : ∀ ω : Fin L → X,
      p.probOf ω * ∑ m : Fin M, (if E m ω then (1 : ℝ) else 0)
        = ∑ m : Fin M, p.probOf ω * (if E m ω then (1 : ℝ) else 0) :=
        fun ω => Finset.mul_sum (Finset.univ : Finset (Fin M))
          (fun m => if E m ω then (1 : ℝ) else 0) (p.probOf ω)
  calc probEvent (L := L) p (fun ω : Fin L → X => ∃ m, E m ω)
      = ∑ ω ∈ Finset.univ.filter (fun ω : Fin L → X => ∃ m, E m ω), p.probOf ω := rfl
    _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin L → X => ∃ m, E m ω),
          ∑ m : Fin M, p.probOf ω * (if E m ω then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun ω hω => ?_
        rw [← hsplit ω]
        obtain ⟨m₀, hm₀⟩ := (Finset.mem_filter.mp hω).2
        have h1 : (1 : ℝ) ≤ ∑ m : Fin M, if E m ω then (1 : ℝ) else 0 := by
          have hm₀' : (1 : ℝ) ≤ (if E m₀ ω then (1 : ℝ) else 0) := by
            rw [if_pos hm₀]
          exact hm₀'.trans (Finset.single_le_sum
            (f := fun m => if E m ω then (1 : ℝ) else 0)
            (fun m _ => by positivity) (Finset.mem_univ m₀))
        calc p.probOf ω = p.probOf ω * 1 := by ring
          _ ≤ p.probOf ω * ∑ m : Fin M, if E m ω then (1 : ℝ) else 0 :=
              mul_le_mul_of_nonneg_left h1 (Finset.prod_nonneg fun i _ => p.nonneg _)
    _ ≤ ∑ ω : Fin L → X, ∑ m : Fin M, p.probOf ω * (if E m ω then (1 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => Finset.sum_nonneg fun m _ => mul_nonneg
            (Finset.prod_nonneg fun i _ => p.nonneg _) (by positivity))
    _ = ∑ m : Fin M, ∑ ω : Fin L → X, p.probOf ω * (if E m ω then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ m : Fin M, probEvent p (E m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [probEvent]
        rw [show (∑ ω : Fin L → X, p.probOf ω * (if E m ω then 1 else 0))
            = ∑ ω ∈ Finset.univ.filter (E m), p.probOf ω from by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun ω _ => by
            rw [mul_ite, mul_one, mul_zero]]

set_option linter.unusedVariables false in

noncomputable def medianOfMeans {L M : ℕ} (p : FinDist X) (f : X → ℝ)
    (ω : Fin M → Fin L → X) : ℝ :=
  ((List.ofFn fun m => avg f (ω m)).mergeSort (· ≤ ·)).getD (M / 2) 0

theorem countP_ofFn_eq_card_filter {M : ℕ} (ys : Fin M → ℝ) (Q : ℝ → Prop)
    [DecidablePred Q] :
    (List.ofFn ys).countP (fun x => decide (Q x))
      = (Finset.univ.filter fun m => Q (ys m)).card := by
  rw [List.ofFn_eq_map, List.countP_map]
  have hcard : (Finset.univ.filter fun m => Q (ys m)).card
      = Multiset.countP (fun m => Q (ys m)) (Finset.univ : Finset (Fin M)).val := by
    show Multiset.card (Finset.univ.filter fun m => Q (ys m)).val = _
    rw [Finset.filter_val, ← Multiset.countP_eq_card_filter]
  rw [hcard]
  rw [show (Finset.univ : Finset (Fin M)).val = (List.finRange M : Multiset (Fin M)) from rfl]
  rw [Multiset.coe_countP]
  rfl

theorem sorted_countP_ge_of_median_dev {M : ℕ} {s : List ℝ} (hs : s.SortedLE)
    (hslen : s.length = M) (hM : 0 < M) {μ ε : ℝ}
    (hmed : ε < |s.getD (M / 2) 0 - μ|) :
    M - M / 2 ≤ s.countP fun x => decide (ε < |x - μ|) := by
  have hk : M / 2 < s.length := by rw [hslen]; omega
  rw [List.getD_eq_getElem s 0 hk] at hmed
  rcases lt_or_ge ε 0 with hεneg | hεnn
  · calc M - M / 2 ≤ s.length := by rw [hslen]; omega
      _ = s.countP (fun x => decide (ε < |x - μ|)) :=
          ((List.countP_eq_length).mpr fun x _ => decide_eq_true_eq.mpr
            (lt_of_lt_of_le hεneg (abs_nonneg _))).symm
  · rcases le_or_gt 0 (s[M / 2] - μ) with hnn | hneg
    · rw [abs_of_nonneg hnn] at hmed
      have hdrop : ∀ x ∈ s.drop (M / 2), ε < |x - μ| := by
        intro x hx
        rw [List.mem_iff_get] at hx
        obtain ⟨i, hi⟩ := hx
        have h2 : i.val < s.length - M / 2 := by simpa using i.isLt
        have hil : M / 2 + i.val < s.length := by omega
        have hx' : x = s[M / 2 + i.val] := by
          rw [← hi, List.get_eq_getElem, List.getElem_drop]
        have hle : s[M / 2] ≤ s[M / 2 + i.val] :=
          hs.getElem_le_getElem_of_le (Nat.le_add_right _ _)
        rw [hx']
        have h1 : ε < s[M / 2 + i.val] - μ := lt_of_lt_of_le hmed (sub_le_sub_right hle μ)
        rw [abs_of_pos (by linarith)]
        exact h1
      calc M - M / 2 = (s.drop (M / 2)).length := by rw [List.length_drop, hslen]
        _ = (s.drop (M / 2)).countP (fun x => decide (ε < |x - μ|)) :=
            ((List.countP_eq_length).mpr
              (fun x hx => decide_eq_true_eq.mpr (hdrop x hx))).symm
        _ ≤ s.countP _ := List.Sublist.countP_le (List.drop_sublist _ s)
    · rw [abs_of_neg hneg] at hmed
      have htake : ∀ x ∈ s.take (M / 2 + 1), ε < |x - μ| := by
        intro x hx
        rw [List.mem_iff_get] at hx
        obtain ⟨i, hi⟩ := hx
        have h2 : i.val < min (M / 2 + 1) s.length := by simpa using i.isLt
        have hil : i.val < s.length := by omega
        have hx' : x = s[i.val] := by
          rw [← hi, List.get_eq_getElem, List.getElem_take]
        have hle : s[i.val] ≤ s[M / 2] :=
          hs.getElem_le_getElem_of_le (by omega : i.val ≤ M / 2)
        rw [hx']
        have h1 : s[i.val] - μ < -ε := by
          have h3 := sub_le_sub_right hle μ
          linarith
        rw [abs_of_neg (by linarith)]
        linarith
      calc M - M / 2 ≤ (s.take (M / 2 + 1)).length := by
            rw [List.length_take, hslen]; omega
        _ = (s.take (M / 2 + 1)).countP (fun x => decide (ε < |x - μ|)) :=
            ((List.countP_eq_length).mpr
              (fun x hx => decide_eq_true_eq.mpr (htake x hx))).symm
        _ ≤ s.countP _ := List.Sublist.countP_le (List.take_sublist _ s)

theorem medianOfMeans_bad_imp_many_bad {L M : ℕ} (p : FinDist X) (f : X → ℝ)
    (hM : 0 < M) (μ ε : ℝ) (ω : Fin M → Fin L → X)
    (hmed : ε < |medianOfMeans p f ω - μ|) :
    M - M / 2 ≤ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card := by
  set s := (List.ofFn fun m => avg f (ω m)).mergeSort (· ≤ ·) with hsdef
  have hperm : List.Perm s (List.ofFn fun m => avg f (ω m)) := List.mergeSort_perm _ _
  have hsorted : s.SortedLE := List.sortedLE_mergeSort
  have hlen : s.length = M := by
    rw [hsdef, (List.mergeSort_perm _ _).length_eq, List.length_ofFn]
  have h := sorted_countP_ge_of_median_dev hsorted hlen hM hmed
  rw [hsdef,
    List.Perm.countP_eq (fun x => decide (ε < |x - μ|)) hperm,
    countP_ofFn_eq_card_filter] at h
  exact h

theorem median_of_means_concentration {L M : ℕ} (p : FinDist X) (f : X → ℝ)
    (hL : 0 < L) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (hvar : 4 * p.variance f ≤ (L : ℝ) * ε ^ 2) :
    ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin M → Fin L → X => ε < |p.medianOfMeans f ω - p.expect f|),
      ∏ m, p.probOf (ω m) ≤ 3 ^ (M / 2) / 2 ^ M := by
  set μ := p.expect f with hμ

  set q : FinDist (Fin L → X) :=
    ⟨p.probOf, fun ω => Finset.prod_nonneg fun i _ => p.nonneg _, p.sum_probOf L⟩ with hq

  have hrnn : 0 ≤ p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|) :=
    Finset.sum_nonneg fun ω₀ _ => Finset.prod_nonneg fun i _ => p.nonneg _
  have hrq : p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|) ≤ 1 / 4 := by
    have hcheb := p.chebyshev_avg f hL ε hε
    have hLε : (0 : ℝ) < (L : ℝ) * ε ^ 2 :=
      mul_pos (by exact_mod_cast hL) (pow_pos hε 2)
    have h2 : p.variance f / ((L : ℝ) * ε ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hLε (by norm_num)]
      linarith
    exact hcheb.trans h2

  have hsub : (Finset.univ.filter
        (fun ω : Fin M → Fin L → X => ε < |p.medianOfMeans f ω - μ|))
      ⊆ (Finset.univ.filter
        (fun ω : Fin M → Fin L → X => M - M / 2 ≤
          (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨Finset.mem_univ ω, medianOfMeans_bad_imp_many_bad p f hM μ ε ω hω.2⟩

  have hprob : ∀ ω : Fin M → Fin L → X,
      (if M - M / 2 ≤ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
          then (1 : ℝ) else 0)
        ≤ 3 ^ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
          / 3 ^ (M - M / 2) := by
    intro ω
    by_cases h : M - M / 2 ≤ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
    · rw [if_pos h, le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) _), one_mul]
      exact pow_le_pow_right₀ (by norm_num) h
    · rw [if_neg h]
      positivity

  have hpow : ∀ ω : Fin M → Fin L → X,
      (3 : ℝ) ^ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
        = ∏ m : Fin M, if ε < |avg f (ω m) - μ| then (3 : ℝ) else 1 := by
    intro ω
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

  have hfactor : ∀ m : Fin M,
      (∑ ω₀ : Fin L → X, q.prob ω₀ * (if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1))
        = 1 + 2 * p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|) := by
    intro m
    have h2 : ∀ ω₀ : Fin L → X,
        p.probOf ω₀ * (if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1)
          = (if ε < |avg f ω₀ - μ| then 3 * p.probOf ω₀ else p.probOf ω₀) := by
      intro ω₀
      by_cases h : ε < |avg f ω₀ - μ| <;> simp only [h, if_true, if_false] <;> ring
    have htot : (∑ ω₀ ∈ Finset.univ.filter
          (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|), p.probOf ω₀)
        + (∑ ω₀ ∈ Finset.univ.filter
          (fun ω₀ : Fin L → X => ¬ ε < |avg f ω₀ - μ|), p.probOf ω₀) = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact p.sum_probOf L
    calc ∑ ω₀ : Fin L → X, q.prob ω₀ * (if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1)
        = ∑ ω₀ : Fin L → X, p.probOf ω₀ * (if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1) :=
          Finset.sum_congr rfl fun ω₀ _ => rfl
      _ = ∑ ω₀ : Fin L → X,
            (if ε < |avg f ω₀ - μ| then 3 * p.probOf ω₀ else p.probOf ω₀) :=
          Finset.sum_congr rfl fun ω₀ _ => h2 ω₀
      _ = (∑ ω₀ ∈ Finset.univ.filter (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|),
              3 * p.probOf ω₀)
            + (∑ ω₀ ∈ Finset.univ.filter (fun ω₀ : Fin L → X => ¬ ε < |avg f ω₀ - μ|),
              p.probOf ω₀) := Finset.sum_ite ..
      _ = 3 * (∑ ω₀ ∈ Finset.univ.filter (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|),
              p.probOf ω₀)
            + (∑ ω₀ ∈ Finset.univ.filter (fun ω₀ : Fin L → X => ¬ ε < |avg f ω₀ - μ|),
              p.probOf ω₀) := by rw [Finset.mul_sum]
      _ = 3 * p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|)
            + (1 - p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|)) := by
          have hpos : (∑ ω₀ ∈ Finset.univ.filter
                (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|), p.probOf ω₀)
              = p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|) := rfl
          have hnot : (∑ ω₀ ∈ Finset.univ.filter
                (fun ω₀ : Fin L → X => ¬ ε < |avg f ω₀ - μ|), p.probOf ω₀)
              = 1 - p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|) := by
            show (∑ ω₀ ∈ Finset.univ.filter
                (fun ω₀ : Fin L → X => ¬ ε < |avg f ω₀ - μ|), p.probOf ω₀)
              = 1 - (∑ ω₀ ∈ Finset.univ.filter
                (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|), p.probOf ω₀)
            linarith
          rw [hpos, hnot]
      _ = 1 + 2 * p.probEvent (fun ω₀ : Fin L → X => ε < |avg f ω₀ - μ|) := by ring

  have hprod : ∏ m : Fin M,
        (∑ ω₀ : Fin L → X, q.prob ω₀ * (if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1))
      ≤ ((3 : ℝ) / 2) ^ M := by
    calc ∏ m : Fin M,
          (∑ ω₀ : Fin L → X, q.prob ω₀ * (if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1))
        ≤ ∏ _m : Fin M, (3 : ℝ) / 2 := by
          refine Finset.prod_le_prod₀ (fun m _ => ?_) (fun m _ => ?_)
          · rw [hfactor m]; linarith
          · rw [hfactor m]; linarith
      _ = ((3 : ℝ) / 2) ^ M := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

  calc ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin M → Fin L → X => ε < |p.medianOfMeans f ω - μ|),
        ∏ m, p.probOf (ω m)
      = ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin M → Fin L → X => ε < |p.medianOfMeans f ω - μ|),
        q.probOf ω := Finset.sum_congr rfl fun ω _ => rfl
    _ ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin M → Fin L → X => M - M / 2 ≤
            (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card),
        q.probOf ω :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ω _ _ => Finset.prod_nonneg fun i _ => q.nonneg _)
    _ = ∑ ω : Fin M → Fin L → X, q.probOf ω *
          (if M - M / 2 ≤ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
              then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun ω _ => by rw [mul_ite, mul_one, mul_zero]
    _ ≤ ∑ ω : Fin M → Fin L → X, q.probOf ω *
          (3 ^ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
            / 3 ^ (M - M / 2)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hprob ω)
          (Finset.prod_nonneg fun i _ => q.nonneg _)
    _ = (∑ ω : Fin M → Fin L → X, q.probOf ω *
          3 ^ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card)
          / 3 ^ (M - M / 2) := by
        have step : ∀ ω : Fin M → Fin L → X,
            q.probOf ω *
                (3 ^ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
                  / 3 ^ (M - M / 2))
              = (q.probOf ω *
                  3 ^ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card)
                / 3 ^ (M - M / 2) :=
          fun ω => (mul_div_assoc _ _ _).symm
        rw [Finset.sum_congr rfl fun ω _ => step ω, Finset.sum_div]
    _ = (∏ m : Fin M, ∑ ω₀ : Fin L → X,
            q.prob ω₀ * (if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1))
          / 3 ^ (M - M / 2) := by
        congr 1
        have step : ∀ ω : Fin M → Fin L → X,
            q.probOf ω * 3 ^ (Finset.univ.filter fun m => ε < |avg f (ω m) - μ|).card
              = q.probOf ω *
                ∏ m : Fin M, if ε < |avg f (ω m) - μ| then (3 : ℝ) else 1 :=
          fun ω => by rw [hpow ω]
        rw [Finset.sum_congr rfl fun ω _ => step ω]
        exact q.expect_prod (fun _ ω₀ => if ε < |avg f ω₀ - μ| then (3 : ℝ) else 1)
    _ ≤ ((3 : ℝ) / 2) ^ M / 3 ^ (M - M / 2) :=
        div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) _)
    _ = 3 ^ (M / 2) / 2 ^ M := by
        have h3K : (3 : ℝ) ^ (M - M / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
        have h2M : (2 : ℝ) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
        have h3M : (3 : ℝ) ^ M = 3 ^ (M / 2) * 3 ^ (M - M / 2) := by
          rw [← pow_add]; congr 1; omega
        rw [div_pow, div_div, h3M]
        field_simp

end FinDist

end Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Matrix
open scoped ComplexOrder

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

noncomputable def FinDist.independentPair {J K : Type*} [Fintype J] [Fintype K]
    (d : FinDist J) (e : FinDist K) : FinDist (J × K) where
  prob jk := d.prob jk.1 * e.prob jk.2
  nonneg jk := mul_nonneg (d.nonneg jk.1) (e.nonneg jk.2)
  sum_one := by
    have h : (∑ x : J × K, d.prob x.1 * e.prob x.2) = ∑ j, ∑ k, d.prob j * e.prob k :=
      Fintype.sum_prod_type' (fun j k => d.prob j * e.prob k)
    rw [h]
    calc (∑ j, ∑ k, d.prob j * e.prob k) = ∑ j, d.prob j * ∑ k, e.prob k := by
          refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ j, d.prob j * 1 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [e.sum_one]
      _ = 1 := by rw [(Finset.sum_mul _ _ _).symm, d.sum_one, one_mul]

theorem FinDist.independentPair_prob {J K : Type*} [Fintype J] [Fintype K] (d : FinDist J)
    (e : FinDist K) (j : J) (k : K) :
    (FinDist.independentPair d e).prob (j, k) = d.prob j * e.prob k := rfl

theorem FinDist.independentPair_sum_left {J K : Type*} [Fintype J] [Fintype K] (d : FinDist J)
    (e : FinDist K) (j : J) : ∑ k, (FinDist.independentPair d e).prob (j, k) = d.prob j := by
  calc ∑ k, (FinDist.independentPair d e).prob (j, k) = ∑ k, d.prob j * e.prob k :=
        Finset.sum_congr rfl fun k _ => FinDist.independentPair_prob d e j k
    _ = d.prob j * ∑ k, e.prob k := (Finset.mul_sum _ _ _).symm
    _ = d.prob j * 1 := by rw [e.sum_one]
    _ = d.prob j := by ring

theorem FinDist.independentPair_sum_right {J K : Type*} [Fintype J] [Fintype K] (d : FinDist J)
    (e : FinDist K) (k : K) : ∑ j, (FinDist.independentPair d e).prob (j, k) = e.prob k := by
  calc ∑ j, (FinDist.independentPair d e).prob (j, k) = ∑ j, d.prob j * e.prob k :=
        Finset.sum_congr rfl fun j _ => FinDist.independentPair_prob d e j k
    _ = (∑ j, d.prob j) * e.prob k := (Finset.sum_mul _ _ _).symm
    _ = 1 * e.prob k := by rw [d.sum_one]
    _ = e.prob k := one_mul _
end Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Matrix
open scoped ComplexOrder

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

theorem FinDist.variance_eq_expect_sq_sub {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) :
    p.variance f = p.expect (fun x => (f x)^2) - (p.expect f)^2 := by
  set E := p.expect f with hE
  have hsum : (∑ x, p.prob x * f x) = E := hE.symm
  show (∑ x, p.prob x * (f x - E)^2) = (∑ x, p.prob x * (f x)^2) - E^2
  have h1 : ∀ x, p.prob x * (f x - E)^2
      = p.prob x * (f x)^2 - (2 * E) * (p.prob x * f x) + p.prob x * E^2 :=
    fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsum, ← Finset.sum_mul, p.sum_one, one_mul]
  ring
end Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Matrix
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

theorem FinDist.probOf_subset_product {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (B : X → Prop) [DecidablePred B] (J : Finset (Fin L)) :
    ∑ ω ∈ Finset.univ.filter (fun ω => ∀ n ∈ J, B (ω n)), p.probOf ω
      = ∏ n ∈ J, (∑ x ∈ Finset.univ.filter B, p.prob x) := by
  classical
  have hstep1 : (∑ ω ∈ Finset.univ.filter (fun ω => ∀ n ∈ J, B (ω n)), p.probOf ω)
      = ∑ ω : Fin L → X, p.probOf ω *
          ∏ n : Fin L, (if n ∈ J then (if B (ω n) then (1:ℝ) else 0) else 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hall : ∀ n ∈ J, B (ω n)
    · rw [if_pos hall]
      have hprod : ∏ n : Fin L, (if n ∈ J then (if B (ω n) then (1:ℝ) else 0) else 1) = 1 := by
        refine Finset.prod_eq_one fun n _ => ?_
        by_cases hn : n ∈ J
        · rw [if_pos hn, if_pos (hall n hn)]
        · rw [if_neg hn]
      rw [hprod, mul_one]
    · have hnall : ¬ ∀ n ∈ J, B (ω n) := hall
      push Not at hnall
      obtain ⟨n, hnJ, hnB⟩ := hnall
      rw [if_neg hall, Finset.prod_eq_zero (Finset.mem_univ n) (by
        rw [if_pos hnJ, if_neg hnB]), mul_zero]
  rw [hstep1, FinDist.expect_prod p
    (fun n x => if n ∈ J then (if B x then (1:ℝ) else 0) else 1)]
  have hoffJ : ∀ n : Fin L, n ∉ J →
      (∑ x ∈ Finset.univ, p.prob x * (if n ∈ J then (if B x then (1:ℝ) else 0) else 1)) = 1 := by
    intro n hn
    simp only [if_neg hn, mul_one]
    exact p.sum_one
  exact (Finset.prod_subset (Finset.subset_univ J)
    (fun n _ hn => hoffJ n hn)).symm.trans
      (Finset.prod_congr rfl fun n hn => by
        simp only [if_pos hn]
        have hite : ∀ x : X, p.prob x * (if B x then (1:ℝ) else 0)
            = if B x then p.prob x else 0 := by
          intro x
          by_cases hB : B x
          · rw [if_pos hB, if_pos hB, mul_one]
          · rw [if_neg hB, if_neg hB, mul_zero]
        calc (∑ x ∈ Finset.univ, p.prob x * (if B x then (1:ℝ) else 0))
            = ∑ x ∈ Finset.univ, (if B x then p.prob x else 0) :=
              Finset.sum_congr rfl fun x _ => hite x
          _ = ∑ x ∈ Finset.univ.filter B, p.prob x := by rw [Finset.sum_filter])
end Qatlib.Concepts.MonteCarloMean.FinDistBounds
