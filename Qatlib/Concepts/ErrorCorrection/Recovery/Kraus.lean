/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
public import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Mathlib.Tactic.Choose

@[expose] public section

/-!
# Recovery of a linear space of errors

An error is correctable for an encoding and a fixed recovery when every recovery Kraus
operator composed with that error acts by a scalar on the encoded subspace. These errors
form a complex subspace. Completeness of the two Kraus families normalizes the sum of the
branch weights. Recovery therefore fixes arbitrary encoded operators, including the
off-diagonal blocks of a joint state with a reference system.
-/

namespace Qatlib.Concepts.ErrorCorrection.Recovery

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {d l : ℕ}

/-- The error operators whose recovered branches are scalar multiples of the encoding. -/
def correctable {α : Type*} (V : Matrix (Fin d) (Fin l) ℂ) (R : α → Operator d) :
    Submodule ℂ (Operator d) where
  carrier := {E | ∀ i, ∃ z : ℂ, R i * E * V = z • V}
  zero_mem' := fun i => ⟨0, by simp⟩
  add_mem' := by
    intro E F hE hF i
    obtain ⟨z, hz⟩ := hE i
    obtain ⟨w, hw⟩ := hF i
    exact ⟨z + w, by rw [Matrix.mul_add, Matrix.add_mul, hz, hw, add_smul]⟩
  smul_mem' := by
    intro a E hE i
    obtain ⟨z, hz⟩ := hE i
    exact ⟨a * z, by rw [Matrix.mul_smul, Matrix.smul_mul, hz, smul_smul]⟩

/-- Membership in the correctable space is the scalar condition on every recovered branch. -/
theorem mem_correctable {α : Type*}
    (V : Matrix (Fin d) (Fin l) ℂ) (R : α → Operator d) (E : Operator d) :
    E ∈ correctable V R ↔ ∀ i, ∃ z : ℂ, R i * E * V = z • V := Iff.rfl

/-- Complete noise and recovery Kraus families recover every encoded operator when each noise
Kraus operator belongs to the correctable space. -/
theorem recovers {r k : ℕ} (V : Matrix (Fin d) (Fin l) ℂ) (hV : Vᴴ * V = 1)
    (R : Fin r → Operator d) (hR : KrausComplete R)
    (K : Fin k → Operator d) (hK : KrausComplete K)
    (hc : ∀ j, K j ∈ correctable V R) (A : Operator l) :
    krausMap R (krausMap K (conjBranch V A)) = conjBranch V A := by
  classical
  choose coeff hcoeff using fun i j => (mem_correctable V R (K j)).mp (hc j) i
  let weight : ℂ := ∑ j, ∑ i, star (coeff i j) * coeff i j
  have hbranch (i : Fin r) (j : Fin k) (B : Operator l) :
      conjBranch (R i) (conjBranch (K j) (conjBranch V B)) =
        (star (coeff i j) * coeff i j) • conjBranch V B := by
    calc
      _ = conjBranch (R i * K j * V) B := by
        simp only [conjBranch_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hcoeff i j]
        simp only [conjBranch_apply, Matrix.conjTranspose_smul, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul]
  have hweighted (B : Operator l) :
      krausMap R (krausMap K (conjBranch V B)) = weight • conjBranch V B := by
    simp only [krausMap, LinearMap.sum_apply, map_sum, hbranch, weight, Finset.sum_smul]
  by_cases hl : 0 < l
  · let i : Fin l := ⟨0, hl⟩
    let sample : Operator l := Matrix.single i i 1
    have htrace : Matrix.trace (conjBranch V sample) = 1 := by
      rw [conjBranch_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, one_mul]
      simp [sample]
    have hnoise := tracePreserving_of_krausComplete (krausForm_krausMap K) hK
    have hrec := tracePreserving_of_krausComplete (krausForm_krausMap R) hR
    have hw := congrArg Matrix.trace (hweighted sample)
    rw [hrec _, hnoise _, Matrix.trace_smul, htrace, smul_eq_mul, mul_one] at hw
    rw [hweighted, ← hw, one_smul]
  · have hA : A = 0 := by
      apply Matrix.ext
      intro i j
      exact (hl (Nat.zero_lt_of_lt i.isLt)).elim
    simp [hA]

/-- Recovery acts as the identity on every operator encoded jointly with a finite reference. -/
theorem recovers_ref {r k ref : ℕ} (V : Matrix (Fin d) (Fin l) ℂ) (hV : Vᴴ * V = 1)
    (R : Fin r → Operator d) (hR : KrausComplete R)
    (K : Fin k → Operator d) (hK : KrausComplete K) (hc : ∀ j, K j ∈ correctable V R)
    (A : Matrix (Fin l × Fin ref) (Fin l × Fin ref) ℂ) :
    tensorLeft (krausMap R) (tensorLeft (krausMap K) (tensorLeft (conjBranch V) A)) =
      tensorLeft (conjBranch V) A := by
  apply Matrix.ext
  intro ⟨i, a⟩ ⟨j, b⟩
  exact congrFun (congrFun (recovers V hV R hR K hK hc
    (fun u v => A (u, a) (v, b))) i) j

end Qatlib.Concepts.ErrorCorrection.Recovery
