/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceJetCurvature
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Finite integer source-mean execution with a cached period

One flattened original-query list supplies the decoder's four answers per
grid point. The decoder accumulates all three negative coordinate moments.
The period is computed outside the grid and supplied only to this internal
decoder. Query counts below concern this actual list; they are not total
bit-runtime claims.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Abbreviation for Source Mean Index in the Rational Flow construction. -/
abbrev SourceMeanIndex := ℕ × ℕ × ℕ

/-- Definition of source Mean Index Coord in the Rational Flow construction. -/
def sourceMeanIndexCoord (index : SourceMeanIndex) : Fin 3 → ℕ :=
  ![index.1,index.2.1,index.2.2]

/-- Python's x/y/z loop order, with the last coordinate varying fastest. -/
def sourceMeanGrid (N : ℕ) : List SourceMeanIndex :=
  (List.range N).flatMap (fun k => (List.range N).flatMap (fun l =>
    (List.range N).map (fun m => (k,l,m))))

/-- Definition of source Mean Unit Point in the Rational Flow construction. -/
def sourceMeanUnitPoint (N : ℕ) (index : SourceMeanIndex) : Fin 3 → ℚ :=
  fun i => (sourceMeanIndexCoord index i : ℚ)/(N : ℚ)

/-- A cached-length packet schedule; no period routine occurs inside it. -/
def sourceMeanPacketSchedule (length : ℚ) (requested : ℕ) (a : Fin 3 → ℚ) : List OriginalJetQuery :=
  let q := fun i => length*a i
  ((q,0),requested) :: List.ofFn (fun i : Fin 3 => ((q,firstJetIndex i),requested))

/-- Definition of source Mean Moment Axis in the Rational Flow construction. -/
def sourceMeanMomentAxis (j : Fin 3) : Fin 3 := j+1

/-- Definition of source Mean Contribution in the Rational Flow construction. -/
def sourceMeanContribution (index : SourceMeanIndex) (packet : RationalFirstJetPacket) : Fin 3 → ℤ :=
  fun j => -(sourceMeanIndexCoord index (sourceMeanMomentAxis j) : ℤ)*
    firstJetIntegerTriple packet.1 (packet.2 (sourceMeanMomentAxis j)) (packet.2 j)

/-- Reject short/extra answer lists, and consume exactly the packet used in
the integer accumulator. No packet oracle or mean is an input. -/
def sourceMeanDecode (length : ℚ) (p : ℕ) :
    List SourceMeanIndex → List (Fin 3 → ℚ) → Option (Fin 3 → ℤ)
  | [],[] => some 0
  | index::indices,v::dx::dy::dz::answers => do
      let packet ← firstJetPacketOfAnswerTuple length p [v,dx,dy,dz]
      let tail ← sourceMeanDecode length p indices answers
      pure (sourceMeanContribution index packet+tail)
  | _,_ => none

/-- Definition of source Mean Schedule in the Rational Flow construction. -/
def sourceMeanSchedule (m1 m2 : ℚ) (N b : ℕ) : List OriginalJetQuery :=
  let requested := b+2+rescaleSourceOverhead m1 m2
  let length := periodLower requested
  (sourceMeanGrid N).flatMap (fun index =>
    sourceMeanPacketSchedule length requested (sourceMeanUnitPoint N index))

/-- The one source evaluation list is fed directly into the strict decoder.
The length used in every query and derivative scaling is the same cached one. -/
def sourceMeanIntegerExecution (source : RationalJetSource) (m1 m2 : ℚ) (N b : ℕ) :
    Option (Fin 3 → ℤ) :=
  let requested := b+2+rescaleSourceOverhead m1 m2
  let length := periodLower requested
  let indices := sourceMeanGrid N
  let labels := indices.flatMap (fun index =>
    sourceMeanPacketSchedule length requested (sourceMeanUnitPoint N index))
  sourceMeanDecode length (b+2) indices (labels.map source)

/-- The producer's exact rational common denominator includes the coordinate
weight's additional N as well as the N-cubed normalized average. -/
def sourceMeanUnitExecution (source : RationalJetSource) (m1 m2 : ℚ) (N b : ℕ) :
    Option (Fin 3 → ℚ) :=
  (sourceMeanIntegerExecution source m1 m2 N b).map
    (fun acc j => (acc j : ℚ)/((N : ℚ)^4*2^(3*(b+2)+1)))

/-- Original `sourceMeanPacketSchedule_eq` guarantee for the `SourceMeanExecution` construction; the complete source hypotheses are retained. -/
theorem sourceMeanPacketSchedule_eq (m1 m2 : ℚ) (a : Fin 3 → ℚ) (b : ℕ) :
    sourceMeanPacketSchedule (periodLower (b+2+rescaleSourceOverhead m1 m2))
      (b+2+rescaleSourceOverhead m1 m2) a=sourceFirstJetSchedule m1 m2 a b := rfl

/-- Original `sourceMeanGrid_length` guarantee for the `SourceMeanExecution` construction; the complete source hypotheses are retained. -/
theorem sourceMeanGrid_length (N : ℕ) : (sourceMeanGrid N).length=N^3 := by
  simp [sourceMeanGrid,List.length_flatMap,pow_succ,mul_assoc]

/-- Original `sourceMeanSchedule_length` guarantee for the `SourceMeanExecution` construction; the complete source hypotheses are retained. -/
theorem sourceMeanSchedule_length (m1 m2 : ℚ) (N b : ℕ) :
    (sourceMeanSchedule m1 m2 N b).length=4*N^3 := by
  simp [sourceMeanSchedule,sourceMeanPacketSchedule,List.length_flatMap,sourceMeanGrid_length,mul_comm]

/-- The request-domain precision and derivative order belong to the actual
query list too; physical-address legality is proved in `SourceMeanError`. -/
theorem sourceMeanSchedule_request_domain (m1 m2 : ℚ) (N b : ℕ) :
    ∀ q ∈ sourceMeanSchedule m1 m2 N b,
      q.2=b+2+rescaleSourceOverhead m1 m2 ∧ (∑ i : Fin 3, q.1.2 i) ≤ 1 := by
  intro q hq
  simp only [sourceMeanSchedule,List.mem_flatMap] at hq
  obtain ⟨index,_hi,hq⟩ := hq
  simp [sourceMeanPacketSchedule,List.ofFn_succ] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> simp [firstJetIndex]

/-- Every four-answer block is the existing rounded packet from the same
source. This connects the cached execution to its already proved error. -/
theorem sourceMeanDecode_correct (source : RationalJetSource) (m1 m2 : ℚ) (N b : ℕ)
    (indices : List SourceMeanIndex) :
    sourceMeanDecode (periodLower (b+2+rescaleSourceOverhead m1 m2)) (b+2) indices
      ((indices.flatMap (fun index => sourceMeanPacketSchedule
        (periodLower (b+2+rescaleSourceOverhead m1 m2)) (b+2+rescaleSourceOverhead m1 m2)
        (sourceMeanUnitPoint N index))).map source)=
      some ((indices.map (fun index => sourceMeanContribution index
        (roundedSourceFirstJet source m1 m2 (sourceMeanUnitPoint N index) b))).sum) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    have hpacket := sourceFirstJetExecution_eq source m1 m2 (sourceMeanUnitPoint N index) b
    simp only [sourceFirstJetExecution,sourceFirstJetSchedule,rescaleSourceQuery,List.ofFn_succ,List.ofFn_zero,
      List.map_cons,List.map_nil] at hpacket
    simp only [sourceMeanPacketSchedule,List.ofFn_succ,List.ofFn_zero] at ih
    simp only [List.flatMap_cons,sourceMeanPacketSchedule,
      List.ofFn_succ,List.ofFn_zero,List.map_cons,List.cons_append,List.nil_append,
      sourceMeanDecode]
    rw [hpacket,ih]
    rfl

/-- Original `sourceMeanIntegerExecution_correct` guarantee for the `SourceMeanExecution` construction; the complete source hypotheses are retained. -/
theorem sourceMeanIntegerExecution_correct (source : RationalJetSource) (m1 m2 : ℚ) (N b : ℕ) :
    sourceMeanIntegerExecution source m1 m2 N b=
      some (((sourceMeanGrid N).map (fun index => sourceMeanContribution index
        (roundedSourceFirstJet source m1 m2 (sourceMeanUnitPoint N index) b))).sum) :=
  sourceMeanDecode_correct source m1 m2 N b (sourceMeanGrid N)

end Qatlib.Concepts.EffectiveGauge.RationalFlow
