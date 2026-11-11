/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord

/-!
# Auxiliary operation counts in nested amplitude estimation

This module counts payoff rotations and sample-register Hadamard operations in the expanded
nested amplitude-estimation words associated with [KanekoEtAl2020]. Neither tag occurs in an
inner-family word, and each occurs once in a preparation word.

Expansion through outer amplitude estimation multiplies the preparation count by the total
number of forward and backward preparation accesses, yielding `2 * N - 1` for each tag.

## Main statements

* `inner_no_aux`: The inner word contains neither auxiliary tag.
* `expanded_aux_counts`: Outer expansion scales auxiliary counts by preparation accesses.
* `nested_aux_counts`: Each auxiliary tag occurs `2 * N - 1` times in the nested word.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Papers.MonteCarloInt20.CostModels.AuxiliaryCounts

/-- An inner-family word has zero occurrences of either the payoff-rotation tag or the
sample-Hadamard tag. -/
theorem inner_no_aux {I J : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A : J → Matrix I I ℂ) (i₀ : I) (S : J → Finset I)
    (w : List (AEAccessStep (Inner M I))) (t : AccessTag)
    (ht : t=.payoffRotation ∨ t=.sampleHadamard) :
    accessCount t (innerFamilyWord M A i₀ S w)=0 := by
  unfold accessCount innerFamilyWord
  rw [List.map_map]
  have h : List.map ((fun p => if p.1=t then 1 else 0) ∘
      (fun a => (innerTag a,fun j => stepMatrix (aeControlledGate M
        (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark (S j)))
        (aeAccessInstruction M (A j) i₀ a)))) w = w.map (fun _ => (0:ℕ)) := by
    apply List.map_congr_left
    intro a _
    rcases ht with rfl | rfl <;> cases a <;> rfl
  rw [h]
  simp

/-- A preparation word has exactly one occurrence of each of the payoff-rotation and
sample-Hadamard tags. -/
theorem preparation_aux_counts {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ)
    (t : AccessTag) (ht : t=.payoffRotation ∨ t=.sampleHadamard) :
    accessCount t (preparationWord n M A i₀ S D g)=1 := by
  have hz := inner_no_aux M A i₀ S (aeAccessWord (I:=I) M) t ht
  simp only [preparationWord,accessCount_append,accessCount_lift,selectedInnerWord]
  rw [hz]
  rcases ht with rfl | rfl <;> simp [accessCount]

/-- For either auxiliary tag, expanding an outer access word multiplies its count in the
preparation word by the total number of forward and backward accesses. -/
theorem expanded_aux_counts {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (i₀ : I) (S : Finset I) (w : GateWord (Matrix I I ℂ))
    (a : List (AEAccessStep (Inner N I))) (t : AccessTag)
    (ht : t=.payoffRotation ∨ t=.sampleHadamard) :
    accessCount t (a.flatMap (expandOuterStep N i₀ S w))=
      (aeForwardAccesses a+aeBackwardAccesses a)*accessCount t w := by
  have hr : reverseTag t=t := by rcases ht with rfl | rfl <;> rfl
  have hf : AccessTag.fixed ≠ t := by rcases ht with rfl | rfl <;> decide
  have ho : AccessTag.outerMark ≠ t := by rcases ht with rfl | rfl <;> decide
  induction a with
  | nil => simp [accessCount,aeForwardAccesses,aeBackwardAccesses]
  | cons a as ih =>
    cases a <;> simp only [List.flatMap_cons,accessCount_append,expandOuterStep,accessCount_lift,
      accessCount_adjoint,hr,aeForwardAccesses,aeBackwardAccesses] at * <;>
      simp only [accessCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        if_neg hf,if_neg ho,zero_add,add_zero,Nat.add_mul,Nat.one_mul] at * <;> omega

/-- For positive inner and outer sizes, each of the payoff-rotation and sample-Hadamard tags
occurs exactly `2 * N - 1` times in the nested word. -/
theorem nested_aux_counts {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ)
    (t : AccessTag) (ht : t=.payoffRotation ∨ t=.sampleHadamard) :
    accessCount t (nestedWord n M N hM A i₀ S D g)=2*N-1 := by
  have h := expanded_aux_counts N ((ZeroStr n,innerSeed M hM i₀),false)
    (Finset.univ.filter (fun p => p.2=true)) (preparationWord n M A i₀ S D g) (aeAccessWord N) t ht
  have hp := preparation_aux_counts n M A i₀ S D g t ht
  have hn := prepared_ae_separate_access_counts (I:=((Reg n × Inner M I) × Bool)) N hN
  rw [hp,hn.1,hn.2.1,Nat.mul_one] at h
  change accessCount t (nestedWord n M N hM A i₀ S D g)=N+(N-1) at h
  have he : N+(N-1)=2*N-1 := by omega
  exact h.trans he

end Qatlib.Papers.MonteCarloInt20.CostModels.AuxiliaryCounts
