/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws

/-!
# Endpoint and idle spectral sectors

This module identifies fixed sectors of a product of two reflections about isometry ranges.
Shared range vectors, extreme ±1 cross-Gram eigenvectors, and vectors orthogonal to both ranges
yield the endpoint and idle behavior described in [Szegedy2004].

The counted phase-detection and reflection constructions act exactly on normalized fixed
vectors: detection retains the embedded state, the all-zero phase event has probability one, and
phase reflection fixes the embedding.

## Main statements

* `two_isometry_intersection_gram_and_fixed`: range intersection characterized by paired Gram
  equations.
* `two_isometry_extreme_gram_endpoint`: fixed walk states from extreme cross-Gram eigenvalues.
* `two_isometry_idle_sector_fixed`: negation by each reflection and fixation by their product.
* `boundary_actual_zero_phase_readout_and_reflection`: exact counted behavior on fixed states.

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Qatlib.Foundations.InstrumentCore.Measurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.SpectralReadout.PhaseReadout
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators ComplexOrder

/-- The complex inner product distributes over subtraction in its first argument. -/
private theorem boundary_inner_sub_left {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (u-v) w=Qatlib.Foundations.PureStateMath.Inner u w-Qatlib.Foundations.PureStateMath.Inner v w := by simp only [Qatlib.Foundations.PureStateMath.Inner,star_sub,sub_dotProduct]

/-- The complex inner product distributes over subtraction in its second argument. -/
private theorem boundary_inner_sub_right {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner u (v-w)=Qatlib.Foundations.PureStateMath.Inner u v-Qatlib.Foundations.PureStateMath.Inner u w := by simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct_sub]

/-- Scaling the first argument of the complex inner product multiplies it by the conjugate
scalar. -/
private theorem boundary_inner_smul_left {K : Type} [Fintype K] (c : ℂ) (u v : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (c • u) v=star c*Qatlib.Foundations.PureStateMath.Inner u v := by simp only [Qatlib.Foundations.PureStateMath.Inner,star_smul,smul_dotProduct,smul_eq_mul]

/-- Scaling the second argument of the complex inner product multiplies it by that scalar. -/
private theorem boundary_inner_smul_right {K : Type} [Fintype K] (c : ℂ) (u v : QState K) :
    Qatlib.Foundations.PureStateMath.Inner u (c • v)=c*Qatlib.Foundations.PureStateMath.Inner u v := by simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct_smul,smul_eq_mul]

/-- The complex conjugate of an inner product equals the inner product with reversed arguments. -/
private theorem boundary_inner_star {K : Type} [Fintype K] (u v : QState K) :
    star (Qatlib.Foundations.PureStateMath.Inner u v)=Qatlib.Foundations.PureStateMath.Inner v u := (star_dotProduct (v:=v) (w:=u)).symm

/-- A matrix with `Aᴴ*A = 1` preserves the complex inner product of amplitude vectors. -/
private theorem boundary_isometry_inner {I K : Type} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (A : Matrix K I ℂ) (hA : Aᴴ*A=1) (u v : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (A*ᵥu) (A*ᵥv)=Qatlib.Foundations.PureStateMath.Inner u v := by
  rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,hA,Matrix.one_mulVec]

/-- Reflection about the range projector of an isometry fixes every vector in its image. -/
private theorem boundary_reflection_range {I K : Type} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (A : Matrix K I ℂ) (hA : Aᴴ*A=1) (v : QState I) :
    ReflectionAbout (A*Aᴴ)*ᵥ(A*ᵥv)=A*ᵥv := by
  rw [reflectionAbout_mulVec,Matrix.mulVec_mulVec,Matrix.mul_assoc,hA,Matrix.mul_one]
  module

/-- For two isometries, equality of their image vectors is equivalent to the paired cross-Gram
equations, and a common image vector is fixed by the product of range reflections. See
[Szegedy2004]. -/
theorem two_isometry_intersection_gram_and_fixed : ∀ (I J K : Type) [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K]
    (A : Matrix K I ℂ) (B : Matrix K J ℂ) (a : QState I) (b : QState J),
    Aᴴ*A=1 → Bᴴ*B=1 →
    (A*ᵥa=B*ᵥb ↔ (Aᴴ*B)*ᵥb=a ∧ (Bᴴ*A)*ᵥa=b) ∧
    (A*ᵥa=B*ᵥb →
      (ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ))*ᵥ(A*ᵥa)=A*ᵥa) := by
  intro I J K _ _ _ _ _ _ A B a b hA hB
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro he
    constructor
    · rw [← Matrix.mulVec_mulVec,← he,Matrix.mulVec_mulVec,hA,Matrix.one_mulVec]
    · rw [← Matrix.mulVec_mulVec,he,Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]
  · rintro ⟨hab,hba⟩
    have ha : Aᴴ*ᵥ(A*ᵥa-B*ᵥb)=0 := by
      rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hA,Matrix.one_mulVec,Matrix.mulVec_mulVec,hab,sub_self]
    have hb : Bᴴ*ᵥ(A*ᵥa-B*ᵥb)=0 := by
      rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hba,Matrix.mulVec_mulVec,hB,Matrix.one_mulVec,sub_self]
    have hi : Qatlib.Foundations.PureStateMath.Inner (A*ᵥa-B*ᵥb) (A*ᵥa-B*ᵥb)=0 := by
      rw [boundary_inner_sub_left,inner_mulVec_left_rect,inner_mulVec_left_rect,ha,hb]
      simp [Qatlib.Foundations.PureStateMath.Inner]
    exact sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp hi)
  · intro he
    rw [← Matrix.mulVec_mulVec,boundary_reflection_range A hA,he,boundary_reflection_range B hB]

/-- A cross-Gram eigenvector with eigenvalue `ε = ±1` has image vectors related by `ε`, and its
image under the first isometry is fixed by the reflection product. This is an endpoint case
of [Szegedy2004]. -/
theorem two_isometry_extreme_gram_endpoint : ∀ (I K : Type) [Fintype I] [DecidableEq I] [Fintype K]
    [DecidableEq K] (A B : Matrix K I ℂ) (v : QState I) (ε : ℂ),
    Aᴴ*A=1 → Bᴴ*B=1 → (ε=1 ∨ ε=-1) → (Aᴴ*B)*ᵥv=ε•v →
    B*ᵥv=ε•(A*ᵥv) ∧
    (ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ))*ᵥ(A*ᵥv)=A*ᵥv := by
  intro I K _ _ _ _ A B v ε hA hB he hgram
  have hphase : star ε*ε=1 := by rcases he with rfl | rfl <;> norm_num
  have hsquare : ε*ε=1 := by rcases he with rfl | rfl <;> norm_num
  have hxx : Qatlib.Foundations.PureStateMath.Inner (ε • (A*ᵥv)) (ε • (A*ᵥv))=Qatlib.Foundations.PureStateMath.Inner v v := by
    rw [boundary_inner_smul_left,boundary_inner_smul_right,boundary_isometry_inner A hA,← mul_assoc,hphase,one_mul]
  have hyy :
      Qatlib.Foundations.PureStateMath.Inner (B*ᵥv)
      (B*ᵥv)=Qatlib.Foundations.PureStateMath.Inner v v := boundary_isometry_inner B hB v v
  have hxy : Qatlib.Foundations.PureStateMath.Inner (ε • (A*ᵥv)) (B*ᵥv)=Qatlib.Foundations.PureStateMath.Inner v v := by
    rw [boundary_inner_smul_left,inner_mulVec_left_rect,Matrix.mulVec_mulVec,hgram,
      boundary_inner_smul_right,← mul_assoc,hphase,one_mul]
  have hyx : Qatlib.Foundations.PureStateMath.Inner (B*ᵥv) (ε • (A*ᵥv))=Qatlib.Foundations.PureStateMath.Inner v v := by
    rw [← boundary_inner_star, hxy,boundary_inner_star]
  have hi : Qatlib.Foundations.PureStateMath.Inner (B*ᵥv-ε • (A*ᵥv)) (B*ᵥv-ε • (A*ᵥv))=0 := by
    rw [boundary_inner_sub_left,boundary_inner_sub_right,boundary_inner_sub_right,hxx,hyy,hxy,hyx]
    ring
  have hvec : B*ᵥv=ε • (A*ᵥv) := sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp hi)
  have hrange : A*ᵥv=B*ᵥ(ε • v) := by
    rw [Matrix.mulVec_smul,hvec,smul_smul,hsquare,one_smul]
  refine ⟨hvec,?_⟩
  rw [← Matrix.mulVec_mulVec,boundary_reflection_range A hA]
  calc
    _ = ReflectionAbout (B*Bᴴ)*ᵥ(B*ᵥ(ε • v)) := congrArg (fun x=>ReflectionAbout (B*Bᴴ)*ᵥx) hrange
    _ = B*ᵥ(ε • v) := boundary_reflection_range B hB _
    _ = A*ᵥv := hrange.symm

/-- A vector annihilated by both isometry adjoints is negated by each range reflection and fixed
by their product. This is the idle-sector behavior in [Szegedy2004]. -/
theorem two_isometry_idle_sector_fixed : ∀ (I J K : Type) [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K]
    (A : Matrix K I ℂ) (B : Matrix K J ℂ) (w : QState K),
    Aᴴ*A=1 → Bᴴ*B=1 → Aᴴ*ᵥw=0 → Bᴴ*ᵥw=0 →
    ReflectionAbout (A*Aᴴ)*ᵥw=-w ∧ ReflectionAbout (B*Bᴴ)*ᵥw=-w ∧
    (ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ))*ᵥw=w := by
  intro I J K _ _ _ _ _ _ A B w _hA _hB ha hb
  have hA : ReflectionAbout (A*Aᴴ)*ᵥw=-w := by
    rw [reflectionAbout_mulVec,← Matrix.mulVec_mulVec,ha,Matrix.mulVec_zero,smul_zero,zero_sub]
  have hB : ReflectionAbout (B*Bᴴ)*ᵥw=-w := by
    rw [reflectionAbout_mulVec,← Matrix.mulVec_mulVec,hb,Matrix.mulVec_zero,smul_zero,zero_sub]
  refine ⟨hA,hB,?_⟩
  rw [← Matrix.mulVec_mulVec,hA,Matrix.mulVec_neg,hB,neg_neg]

/-- At phase zero, the product kernel packet equals the zero-ancilla embedding. -/
private theorem boundary_phase_packet_zero {I : Type} (M k : ℕ) (hM : 0<M) (v : QState I) :
    phaseKernelPacket M k 0 v=phaseReflectionEmbed M k v := by
  have hz := qpeKernel_zero_distance M hM 0 (by norm_num [phaseDistance])
  funext ⟨x,b,i⟩
  cases b with
  | true => simp [phaseKernelPacket,phaseReflectionEmbed]
  | false =>
    by_cases hx : ∀ j,(x j).val=0
    · have he : x=phaseZeroIndex M k hM := by funext j; exact Fin.ext (hx j)
      subst x
      simp [phaseKernelPacket,phaseReflectionEmbed,hz,phaseZeroIndex,Qatlib.Foundations.PureStateMath.Ket]
    · obtain ⟨j,hj⟩ := not_forall.mp hx
      have hne : x j≠(⟨0,hM⟩ : Fin M) := fun he=>hj (congrArg Fin.val he)
      have hp : (∏ j : Fin k,qpeKernel M 0 (x j))=0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz]; simp [Qatlib.Foundations.PureStateMath.Ket,hne])
      simp [phaseKernelPacket,phaseReflectionEmbed,hx,hp]

/-- For a normalized fixed vector of a unitary and `M ≥ 2`, counted phase detection leaves its
embedding unchanged, the all-zero event has probability one, and the counted phase
reflection fixes the embedding. -/
theorem boundary_actual_zero_phase_readout_and_reflection : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (w : QState I) (M k : ℕ),
    W ∈ Matrix.unitaryGroup I ℂ → Normalized w → ApplyGate W w=w → 2 ≤ M →
    ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k))
      (phaseReflectionEmbed M k w)=phaseReflectionEmbed M k w ∧
    MeasureProb (ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k))
      (phaseReflectionEmbed M k w)) (phaseZeroEvent M k)=1 ∧
    phaseReflectionState W M k w=phaseReflectionEmbed M k w := by
  intro I _ _ W w M k hW hn hw hM
  have hv : ApplyGate W w=Complex.exp (2*Real.pi*Complex.I*(0 : ℝ)) • w := by simpa using hw
  have hd := (phaseDetectionWord_eigenstate M k (by omega) W w 0 hv).trans
    (boundary_phase_packet_zero M k (by omega) w)
  have hnorm : Normalized (phaseReflectionEmbed M k w) := by
    apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
    rw [phaseReflectionEmbed_norm M k (by omega)]
    exact (normalized_iff_norm_toEuclidean_fromVec _).mp hn
  have hc : Collapse (phaseReflectionEmbed M k w) (phaseZeroEvent M k)=phaseReflectionEmbed M k w := by
    funext ⟨x,b,i⟩
    cases b <;> by_cases hx : ∀ j,(x j).val=0 <;>
      simp [collapse_apply,phaseZeroEvent,phaseReflectionEmbed,hx]
  refine ⟨hd,?_,(phase_reflection_actual_eigenstate_error M k hM W w 0 hW hv).1 (by norm_num [phaseDistance])⟩
  rw [hd]
  have hm := measureProb_collapse (phaseReflectionEmbed M k w) (phaseZeroEvent M k) Finset.univ
  simp only [hc,Finset.inter_univ] at hm
  rw [← hm]
  exact measureProb_univ hnorm

end Qatlib.Concepts.SpectralReadout.PhaseReadout
