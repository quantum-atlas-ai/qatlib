/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.Induction

/-! # Coordinate-word product majorants, including the highest-order cancellation -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `spatialWordPartial_clm` guarantee for the `WordProduct` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_clm {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : E →L[ℝ] H) (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) :
    spatialWordPartial (fun x => A (f x)) w=fun x => A (spatialWordPartial f w x) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [spatialWordPartial,ih]
    have hd := A.hasFDerivAt.comp x
      (((contDiff_spatialWordPartial f hf w).differentiable (by simp) x).hasFDerivAt)
    change HasFDerivAt (fun y => A (spatialWordPartial f w y)) _ x at hd
    rw [hd.fderiv]
    rfl

/-- Exact binomial convolution used by the source/reference majorants. -/
def wordProductMajorant (F G : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (n+1), (n.choose j : ℝ)*F j*G (n-j)

/-- The term containing the highest derivative of the first factor is removed.
This is the forcing remainder, not a bound assuming that unknown derivative. -/
def wordProductRemainderMajorant (F G : ℕ → ℝ) (n : ℕ) : ℝ :=
  wordProductMajorant F G n-F n*G 0

/-- Original `wordProductMajorant_zero` guarantee for the `WordProduct` construction; the complete source hypotheses are retained. -/
theorem wordProductMajorant_zero (F G : ℕ → ℝ) : wordProductMajorant F G 0=F 0*G 0 := by
  simp [wordProductMajorant]

/-- Original `wordProductMajorant_succ` guarantee for the `WordProduct` construction; the complete source hypotheses are retained. -/
theorem wordProductMajorant_succ (F G : ℕ → ℝ) (n : ℕ) :
    wordProductMajorant F G (n+1)=
      wordProductMajorant F (fun j => G (j+1)) n+
      wordProductMajorant (fun j => F (j+1)) G n := by
  unfold wordProductMajorant
  simp_rw [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => F i*G j) n]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [show n+1-j=n-j+1 by omega]

/-- Original `wordProductRemainderMajorant_succ` guarantee for the `WordProduct` construction; the complete source hypotheses are retained. -/
theorem wordProductRemainderMajorant_succ (F G : ℕ → ℝ) (n : ℕ) :
    wordProductRemainderMajorant F G (n+1)=
      wordProductRemainderMajorant (fun j => F (j+1)) G n+
      wordProductMajorant F (fun j => G (j+1)) n := by
  rw [wordProductRemainderMajorant,wordProductMajorant_succ,wordProductRemainderMajorant]
  ring

/-- Original `wordProductRemainderMajorant_eq` guarantee for the `WordProduct` construction; the complete source hypotheses are retained. -/
theorem wordProductRemainderMajorant_eq (F G : ℕ → ℝ) (n : ℕ) :
    wordProductRemainderMajorant F G n=
      ∑ j ∈ range n, (n.choose j : ℝ)*F j*G (n-j) := by
  simp [wordProductRemainderMajorant,wordProductMajorant,sum_range_succ]

/-- Original `spatialWordPartial_mul_first` guarantee for the `WordProduct` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_mul_first (f g : SpatialPoint → ℍ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    spatialWordPartial (fun x => f x*g x) [i]=fun x =>
      spatialWordPartial f [i] x*g x+f x*spatialWordPartial g [i] x := by
  funext x
  have hd := ((hf.differentiable (by simp) x).hasFDerivAt).mul'
    ((hg.differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt (fun x => f x*g x) _ x at hd
  simp only [spatialWordPartial]
  rw [hd.fderiv]
  simp [add_comm]

/-- Only coordinate-word bounds are used, with no operator-norm conversion. -/
theorem spatialWordPartial_mul_norm_le (f g : SpatialPoint → ℍ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (F G : ℕ → ℝ) (w : List (Fin 3)) (x : SpatialPoint)
    (hF : ∀ j ≤ w.length, 0 ≤ F j) (hG : ∀ j ≤ w.length, 0 ≤ G j)
    (hfB : ∀ u : List (Fin 3), u.length ≤ w.length → ‖spatialWordPartial f u x‖ ≤ F u.length)
    (hgB : ∀ u : List (Fin 3), u.length ≤ w.length → ‖spatialWordPartial g u x‖ ≤ G u.length) :
    ‖spatialWordPartial (fun y => f y*g y) w x‖ ≤ wordProductMajorant F G w.length := by
  induction w using List.reverseRecOn generalizing f g F G with
  | nil =>
    simp only [List.length_nil,spatialWordPartial,wordProductMajorant_zero,norm_mul]
    exact mul_le_mul (hfB [] le_rfl) (hgB [] le_rfl) (norm_nonneg _) (hF 0 le_rfl)
  | append_singleton w i ih =>
    let df := spatialWordPartial f [i]
    let dg := spatialWordPartial g [i]
    have hdf := contDiff_spatialWordPartial f hf [i]
    have hdg := contDiff_spatialWordPartial g hg [i]
    have hlen : (w++[i]).length=w.length+1 := by simp
    have hdfB : ∀ u : List (Fin 3), u.length ≤ w.length →
        ‖spatialWordPartial df u x‖ ≤ F (u.length+1) := by
      intro u hu
      simpa only [df,← spatialWordPartial_append,List.length_append,List.length_singleton]
        using hfB (u++[i]) (by simpa using Nat.add_le_add_right hu 1)
    have hdgB : ∀ u : List (Fin 3), u.length ≤ w.length →
        ‖spatialWordPartial dg u x‖ ≤ G (u.length+1) := by
      intro u hu
      simpa only [dg,← spatialWordPartial_append,List.length_append,List.length_singleton]
        using hgB (u++[i]) (by simpa using Nat.add_le_add_right hu 1)
    have hleft := ih df g hdf hg (fun j => F (j+1)) G
      (fun j hj => hF (j+1) (by simpa using Nat.add_le_add_right hj 1))
      (fun j hj => hG j (by simpa using hj.trans (Nat.le_succ _))) hdfB
      (fun u hu => hgB u (by simpa using hu.trans (Nat.le_succ _)))
    have hright := ih f dg hf hdg F (fun j => G (j+1))
      (fun j hj => hF j (by simpa using hj.trans (Nat.le_succ _)))
      (fun j hj => hG (j+1) (by simpa using Nat.add_le_add_right hj 1))
      (fun u hu => hfB u (by simpa using hu.trans (Nat.le_succ _))) hdgB
    rw [spatialWordPartial_append,spatialWordPartial_mul_first f g hf hg i,
      spatialWordPartial_add _ _ (hdf.mul hg) (hf.mul hdg),hlen,wordProductMajorant_succ]
    exact (norm_add_le _ _).trans (by linarith)

/-- The unknown highest derivative of f is absent from every hypothesis.
This is the noncircular estimate needed when f is a differentiated lift. -/
theorem spatialWordPartial_mul_remainder_norm_le (f g : SpatialPoint → ℍ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (F G : ℕ → ℝ) (w : List (Fin 3)) (x : SpatialPoint)
    (hF : ∀ j < w.length, 0 ≤ F j) (hG : ∀ j ≤ w.length, 0 ≤ G j)
    (hfB : ∀ u : List (Fin 3), u.length < w.length → ‖spatialWordPartial f u x‖ ≤ F u.length)
    (hgB : ∀ u : List (Fin 3), u.length ≤ w.length → ‖spatialWordPartial g u x‖ ≤ G u.length) :
    ‖spatialWordPartial (fun y => f y*g y) w x-spatialWordPartial f w x*g x‖ ≤
      wordProductRemainderMajorant F G w.length := by
  induction w using List.reverseRecOn generalizing f g F G with
  | nil => simp [spatialWordPartial,wordProductRemainderMajorant,wordProductMajorant_zero]
  | append_singleton w i ih =>
    let df := spatialWordPartial f [i]
    let dg := spatialWordPartial g [i]
    have hdf := contDiff_spatialWordPartial f hf [i]
    have hdg := contDiff_spatialWordPartial g hg [i]
    have hlen : (w++[i]).length=w.length+1 := by simp
    have hdfB : ∀ u : List (Fin 3), u.length < w.length →
        ‖spatialWordPartial df u x‖ ≤ F (u.length+1) := by
      intro u hu
      simpa only [df,← spatialWordPartial_append,List.length_append,List.length_singleton]
        using hfB (u++[i]) (by simpa using Nat.add_lt_add_right hu 1)
    have hdgB : ∀ u : List (Fin 3), u.length ≤ w.length →
        ‖spatialWordPartial dg u x‖ ≤ G (u.length+1) := by
      intro u hu
      simpa only [dg,← spatialWordPartial_append,List.length_append,List.length_singleton]
        using hgB (u++[i]) (by simpa using Nat.add_le_add_right hu 1)
    have hleft := ih df g hdf hg (fun j => F (j+1)) G
      (fun j hj => hF (j+1) (by simpa using Nat.add_lt_add_right hj 1))
      (fun j hj => hG j (by simpa using hj.trans (Nat.le_succ _))) hdfB
      (fun u hu => hgB u (by simpa using hu.trans (Nat.le_succ _)))
    have hright := spatialWordPartial_mul_norm_le f dg hf hdg F (fun j => G (j+1)) w x
      (fun j hj => hF j (by simpa using Nat.lt_succ_of_le hj))
      (fun j hj => hG (j+1) (by simpa using Nat.add_le_add_right hj 1))
      (fun u hu => hfB u (by simpa using Nat.lt_succ_of_le hu)) hdgB
    rw [spatialWordPartial_append,spatialWordPartial_mul_first f g hf hg i,
      spatialWordPartial_add _ _ (hdf.mul hg) (hf.mul hdg),
      spatialWordPartial_append,hlen,wordProductRemainderMajorant_succ]
    calc
      _ = ‖(spatialWordPartial (fun y => df y*g y) w x-spatialWordPartial df w x*g x)+
        spatialWordPartial (fun y => f y*dg y) w x‖ := by dsimp only [df,dg]; congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hleft hright)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
