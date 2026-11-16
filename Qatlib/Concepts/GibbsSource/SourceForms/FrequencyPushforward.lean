/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.CkgBounds.CKGWeight

@[expose] public section


/-! # Coherent finite pushforward of weighted parent forms

Labels with the same frequency must be added before a strictly positive
frequency Gram can be used. This file supplies that finite algebra without
injectivity, positivity, or a surjectivity premise on the label map.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators

variable {D : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sum all original labels in a fiber, retaining their complex amplitudes. -/
noncomputable def frequencyBucket (f : ι → κ) (A : ι → Operator D)
    (k : κ) : Operator D := by
  classical
  exact ∑ a, if f a = k then A a else 0

/-- Every original label occurs in exactly one bucket. -/
theorem frequencyBucket_sum (f : ι → κ) (A : ι → Operator D) :
    (∑ k, frequencyBucket f A k) = ∑ a, A a := by
  classical
  unfold frequencyBucket
  rw [Finset.sum_comm]
  simp

omit [Fintype κ] in
/-- The first-order factor is linear in each coherent bucket. -/
theorem parentFactor_frequencyBucket [DecidableEq κ] (ρ : Operator D) (f : ι → κ)
    (A : ι → Operator D) (X : Operator D) (k : κ) :
    parentFactor ρ (frequencyBucket f A k) X =
      ∑ a, if f a = k then parentFactor ρ (A a) X else 0 := by
  classical
  rw [frequencyBucket, parentFactor_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : f a = k <;> simp [ha, parentFactor_zero]

/-- Sum swap four for the stated finite source data. -/
private theorem sum_swap_four {α β γ δ M : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (F : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ i, ∑ j, F a b i j) =
      ∑ i, ∑ j, ∑ a, ∑ b, F a b i j := by
  calc
    (∑ a, ∑ b, ∑ i, ∑ j, F a b i j) =
        ∑ a, ∑ i, ∑ b, ∑ j, F a b i j :=
      Finset.sum_congr rfl fun a _ =>
        Finset.sum_comm (f := fun b i => ∑ j, F a b i j)
    _ = ∑ i, ∑ a, ∑ b, ∑ j, F a b i j :=
      Finset.sum_comm (f := fun a i => ∑ b, ∑ j, F a b i j)
    _ = ∑ i, ∑ a, ∑ j, ∑ b, F a b i j :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_comm (f := fun b j => F a b i j)
    _ = ∑ i, ∑ j, ∑ a, ∑ b, F a b i j :=
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_comm (f := fun a j => ∑ b, F a b i j)

/-- A weight depending only on the images of the labels is exactly the
weighted form of their coherent buckets. The physical half is preserved. -/
theorem wplainForm_pushforward (f : ι → κ) (w : κ → κ → ℝ)
    (ρ : Operator D) (A : ι → Operator D) (X : Operator D) :
    wplainForm (fun a b => w (f a) (f b)) ρ A X =
      wplainForm w ρ (frequencyBucket f A) X := by
  classical
  have hterm (k l : κ) (a b : ι) :
      ((w k l / 2 : ℝ) : ℂ) *
          hsInner (if f a = k then parentFactor ρ (A a) X else 0)
            (if f b = l then parentFactor ρ (A b) X else 0) =
        if f a = k then
          (if f b = l then ((w k l / 2 : ℝ) : ℂ) *
            hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X) else 0)
        else 0 := by
    by_cases ha : f a = k <;> by_cases hb : f b = l <;>
      simp [ha, hb, hsInner]
  symm
  simp only [wplainForm, parentFactor_frequencyBucket]
  simp only [hsInner_sum_left]
  simp only [hsInner_sum_right, Finset.mul_sum]
  rw [sum_swap_four]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [hterm]
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro k _ hka
    simp [Ne.symm hka]
  · intro h
    exact (h (Finset.mem_univ (f a))).elim

end Qatlib.Concepts.GibbsSource.SourceForms
