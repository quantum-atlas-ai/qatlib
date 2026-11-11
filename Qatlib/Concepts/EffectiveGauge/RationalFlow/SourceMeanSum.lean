/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanExecution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-! # The executed integer accumulator and the exact normalized packet sum -/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `sum_map_flatMap` guarantee for the `SourceMeanSum` construction; the complete source hypotheses are retained. -/
private theorem sum_map_flatMap {A B M : Type*} [AddMonoid M]
    (indices : List A) (nodes : A → List B) (f : B → M) :
    ((indices.flatMap nodes).map f).sum=
      (indices.map (fun a => ((nodes a).map f).sum)).sum := by
  induction indices with
  | nil => rfl
  | cons a indices ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]

/-- Original `sum_map_range` guarantee for the `SourceMeanSum` construction; the complete source hypotheses are retained. -/
private theorem sum_map_range {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ((List.range N).map f).sum=∑ k ∈ Finset.range N, f k := by
  induction N with
  | zero => simp
  | succ N ih => simp only [List.range_succ,List.map_append,List.sum_append,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Finset.sum_range_succ,ih]

/-- Original `sourceMeanGrid_sum` guarantee for the `SourceMeanSum` construction; the complete source hypotheses are retained. -/
theorem sourceMeanGrid_sum {M : Type*} [AddCommMonoid M] (N : ℕ) (f : SourceMeanIndex → M) :
    ((sourceMeanGrid N).map f).sum=
      ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N, f (k,l,m) := by
  simp only [sourceMeanGrid,sum_map_flatMap,List.map_map,Function.comp_def,sum_map_range]

/-- Definition of source Mean Packet Average in the Rational Flow construction. -/
def sourceMeanPacketAverage (N p : ℕ) (packets : SourceMeanIndex → RationalFirstJetPacket)
    (i j : Fin 3) : ℚ :=
  (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N,
    sourceMeanUnitPoint N (k,l,m) i*firstJetPacketCurvature p (packets (k,l,m)) i j)/(N : ℚ)^3

/-- The integer N-fourth denominator is exactly the N-cubed average of
coordinate-weighted half triples. In particular its sign is negative. -/
theorem sourceMeanAccumulator_div (N p : ℕ) (hN : 0<N)
    (packets : SourceMeanIndex → RationalFirstJetPacket) (j : Fin 3) :
    (((((sourceMeanGrid N).map (fun index => sourceMeanContribution index (packets index))).sum) j : ℤ) : ℚ)/
        ((N : ℚ)^4*2^(3*p+1))=
      -sourceMeanPacketAverage N p packets (sourceMeanMomentAxis j) j := by
  have hn : (N : ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [sourceMeanGrid_sum]
  simp only [Finset.sum_apply,sourceMeanContribution,sourceMeanPacketAverage,
    sourceMeanUnitPoint,firstJetPacketCurvature]
  push_cast
  simp only [neg_mul,Finset.sum_neg_distrib]
  simp_rw [div_mul_div_comm,← Finset.sum_div]
  field_simp [hn]

/-- The actual strict decoder always succeeds, and the returned rational
number is the packet average used in the numerical error proof. -/
theorem sourceMeanUnitExecution_eq (source : RationalJetSource) (m1 m2 : ℚ)
    (N b : ℕ) (hN : 0<N) :
    sourceMeanUnitExecution source m1 m2 N b=
      some (fun j => -sourceMeanPacketAverage N (b+2)
        (fun index => roundedSourceFirstJet source m1 m2 (sourceMeanUnitPoint N index) b)
        (sourceMeanMomentAxis j) j) := by
  rw [sourceMeanUnitExecution,sourceMeanIntegerExecution_correct]
  simp only [Option.map_some]
  congr 1
  funext j
  exact sourceMeanAccumulator_div N (b+2) hN _ j

end Qatlib.Concepts.EffectiveGauge.RationalFlow
