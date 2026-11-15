/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ExclusionCheck.MUB6GlobalVectorBalls

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Concepts.UnbiasedBases.ExclusionCheck
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis
open scoped BigOperators
abbrev Slot := Fin 2 × Fin 6

def InBall (v : Phase6) (s : ℝ) (ψ : QState (Fin 6)) : Prop :=
  ∃ x : Phase6, ∃ c : ℂ, (∑ j, x j)=0 ∧ (∑ j, x j^2) ≤ s^2 ∧
    Complex.normSq c=1 ∧ ψ=fun i => c*cycleVector (v+x) i

/-- Shows that two states in the same phase ball of radius less than one tenth have squared
inner product greater than one sixth. -/
theorem same_ball_gap (v : Phase6) (s : ℝ) (hs : 0 ≤ s) (hsmall : s < 1/10)
    (ψ φ : QState (Fin 6)) (hψ : InBall v s ψ) (hφ : InBall v s φ) :
    (1 : ℝ)/6 < Complex.normSq (Inner ψ φ) := by
  obtain ⟨x,c,_hzero,hx,hc,rfl⟩ := hψ
  obtain ⟨y,d,_hzero,hy,hd,rfl⟩ := hφ
  exact same_ball_normSq_gap v x y s hs hsmall hx hy c d hc hd

/-- Bounds the squared inner product of states in distinct slots of a two-basis family by one
sixth. -/
theorem different_slots_bound (V : Fin 2 → Fin 6 → QState (Fin 6)) (hV : IsFamily V)
    (p q : Slot) (hpq : p ≠ q) :
    Complex.normSq (Inner (V p.1 p.2) (V q.1 q.2)) ≤ (1 : ℝ)/6 := by
  by_cases hr : p.1=q.1
  · have hi : p.2 ≠ q.2 := fun he => hpq (Prod.ext hr he)
    rw [← hr,hV.1 p.1 p.2 q.2,ite_eq_right hi]
    norm_num
  · exact (hV.2 p.1 q.1 hr p.2 q.2).le

def TwoSixPattern {ι : Type*} (O U : ι → ι → Prop) : Prop :=
  ∃ label : Slot ↪ ι,
    (∀ r : Fin 2, ∀ i j : Fin 6, i ≠ j → O (label (r,i)) (label (r,j))) ∧
    (∀ i j : Fin 6, U (label (0,i)) (label (1,j)))

/-- Shows that ball labels covering a two-basis family are injective when every radius is less
than one tenth. -/
theorem labels_injective {ι : Type*} (v : ι → Phase6) (s : ι → ℝ)
    (hs : ∀ a, 0 ≤ s a ∧ s a < 1/10)
    (V : Fin 2 → Fin 6 → QState (Fin 6)) (hV : IsFamily V)
    (label : Slot → ι) (hcover : ∀ p, InBall (v (label p)) (s (label p)) (V p.1 p.2)) :
    Function.Injective label := by
  intro p q he
  by_contra hpq
  have hq := hcover q
  rw [← he] at hq
  have hgap := same_ball_gap (v (label p)) (s (label p)) (hs _).1 (hs _).2
    (V p.1 p.2) (V q.1 q.2) (hcover p) hq
  exact (not_lt_of_ge (different_slots_bound V hV p q hpq)) hgap

/-- Shows that a covered two-basis family with the prescribed within-basis and cross-basis
relations yields `TwoSixPattern`. -/
theorem two_bases_force_pattern {ι : Type*} (v : ι → Phase6) (s : ι → ℝ)
    (hs : ∀ a, 0 ≤ s a ∧ s a < 1/10) (O U : ι → ι → Prop)
    (V : Fin 2 → Fin 6 → QState (Fin 6)) (hV : IsFamily V)
    (label : Slot → ι) (hcover : ∀ p, InBall (v (label p)) (s (label p)) (V p.1 p.2))
    (hO : ∀ r i j, i ≠ j → O (label (r,i)) (label (r,j)))
    (hU : ∀ i j, U (label (0,i)) (label (1,j))) : TwoSixPattern O U :=
  ⟨⟨label,labels_injective v s hs V hV label hcover⟩,hO,hU⟩

def extraIndex (r : Fin 2) : Fin 4 := ⟨r.val+2,by omega⟩

/-- Shows that the extra-basis index map is injective. -/
theorem extraIndex_injective : Function.Injective extraIndex := by
  intro r s h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [extraIndex] at hh
  omega

/-- Shows that selecting the two extra bases from a four-basis family preserves `IsFamily`. -/
theorem extra_pair_family (B : Fin 4 → Fin 6 → QState (Fin 6)) (hB : IsFamily B) :
    IsFamily (fun r : Fin 2 => B (extraIndex r)) := by
  refine ⟨fun r => hB.1 _,?_⟩
  intro r s hrs i j
  exact hB.2 _ _ (fun he => hrs (extraIndex_injective he)) i j

/-- Excludes a four-basis family when its extra bases are covered by the candidate balls and the
induced relations forbid `TwoSixPattern`. -/
theorem no_four_of_ball_graphs {ι σ : Type*} (v : ι → Phase6) (s : ι → ℝ)
    (hs : ∀ a, 0 ≤ s a ∧ s a < 1/10) (O U : ι → ι → Prop)
    (candidate : σ → QState (Fin 6) → Prop) (source : σ)
    (hno : ¬ TwoSixPattern O U)
    (hO : ∀ source a b ψ φ, candidate source ψ → candidate source φ →
      InBall (v a) (s a) ψ → InBall (v b) (s b) φ → Inner ψ φ=0 → O a b)
    (hU : ∀ source a b ψ φ, candidate source ψ → candidate source φ →
      InBall (v a) (s a) ψ → InBall (v b) (s b) φ →
      Complex.normSq (Inner ψ φ)=(1 : ℝ)/6 → U a b)
    (B : Fin 4 → Fin 6 → QState (Fin 6))
    (hcan : ∀ p : Slot, candidate source (B (extraIndex p.1) p.2))
    (cover : ∀ p : Slot, ∃ a, InBall (v a) (s a) (B (extraIndex p.1) p.2)) :
    ¬ IsFamily B := by
  intro hB
  classical
  choose label hlabel using cover
  have hV := extra_pair_family B hB
  apply hno (two_bases_force_pattern v s hs O U (fun r => B (extraIndex r)) hV label hlabel ?_ ?_)
  · intro r i j hij
    apply hO source _ _ _ _ (hcan (r,i)) (hcan (r,j)) (hlabel (r,i)) (hlabel (r,j))
    simpa only [ite_eq_right hij] using hV.1 r i j
  · intro i j
    exact hU source _ _ _ _ (hcan (0,i)) (hcan (1,j))
      (hlabel (0,i)) (hlabel (1,j)) (hV.2 0 1 (by decide) i j)
end Qatlib.Concepts.UnbiasedBases.ExclusionCheck
