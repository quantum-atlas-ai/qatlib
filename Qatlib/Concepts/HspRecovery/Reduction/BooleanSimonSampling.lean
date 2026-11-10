/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardSamplingEvent
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

def booleanSimonSubgroup {n : ℕ} (s : BooleanVec n) : AddSubgroup (BooleanVec n) :=
  AddSubgroup.zmultiples s

@[simp] theorem self_mem_booleanSimonSubgroup {n : ℕ} (s : BooleanVec n) :
    s ∈ booleanSimonSubgroup s :=
  AddSubgroup.mem_zmultiples s

theorem mem_booleanSimonSubgroup_iff {n : ℕ} (s x : BooleanVec n) :
    x ∈ booleanSimonSubgroup s ↔ x = 0 ∨ x = s := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    have hk : (k : ZMod 2) = 0 ∨ (k : ZMod 2) = 1 := by
      generalize (k : ZMod 2) = a
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hk with hk | hk
    · left
      funext i
      change k • s i = 0
      simp [zsmul_eq_mul, hk]
    · right
      funext i
      change k • s i = s i
      simp [zsmul_eq_mul, hk]
  · rintro (hx | hx)
    · subst x
      exact (booleanSimonSubgroup s).zero_mem
    · subst x
      exact self_mem_booleanSimonSubgroup s

@[simp] theorem booleanSimonSubgroup_zero (n : ℕ) :
    booleanSimonSubgroup (0 : BooleanVec n) = ⊥ := by
  ext x
  simp [mem_booleanSimonSubgroup_iff]

def BooleanSimonPromise {n : ℕ} {R : Type*} (f : BooleanVec n → R)
    (s : BooleanVec n) : Prop :=
  ∀ x y, f x = f y ↔ x = y ∨ x = y + s

theorem booleanSimonPromise_iff_hidesSubgroup {n : ℕ} {R : Type*}
    (f : BooleanVec n → R) (s : BooleanVec n) :
    BooleanSimonPromise f s ↔ HidesSubgroup f (booleanSimonSubgroup s) := by
  unfold BooleanSimonPromise HidesSubgroup
  simp only [mem_booleanSimonSubgroup_iff, sub_eq_iff_eq_add, add_comm, add_zero]

theorem booleanSimonPromise_zero_iff {n : ℕ} {R : Type*} (f : BooleanVec n → R) :
    BooleanSimonPromise f 0 ↔ Function.Injective f := by
  unfold BooleanSimonPromise
  simp only [add_zero, or_self]
  exact ⟨fun h x y hxy => (h x y).1 hxy,
    fun h x y => ⟨fun hxy => h hxy, fun hxy => congrArg f hxy⟩⟩

theorem booleanSimonPromise_fiber {n : ℕ} {R : Type*}
    {f : BooleanVec n → R} {s : BooleanVec n} (hf : BooleanSimonPromise f s)
    (x : BooleanVec n) :
    {y | f y = f x} = ({x, x + s} : Set (BooleanVec n)) := by
  ext y
  exact (hf y x).trans (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff])

theorem booleanSimonPromise_collision_of_ne_zero {n : ℕ} {R : Type*}
    {f : BooleanVec n → R} {s : BooleanVec n} (hf : BooleanSimonPromise f s)
    (hs : s ≠ 0) (x : BooleanVec n) : f (x + s) = f x ∧ x + s ≠ x := by
  refine ⟨(hf (x + s) x).2 (Or.inr rfl), ?_⟩
  intro h
  exact hs (add_left_cancel (h.trans (add_zero x).symm))

theorem mem_booleanOrthogonal_booleanSimonSubgroup_iff {n : ℕ}
    (s a : BooleanVec n) :
    a ∈ booleanOrthogonal (booleanSimonSubgroup s) ↔ booleanDot s a = 0 := by
  have hcomm : booleanDot a s = booleanDot s a := by
    unfold booleanDot
    exact Finset.sum_congr rfl (fun i _ => mul_comm (a i) (s i))
  rw [mem_booleanOrthogonal]
  constructor
  · intro ha
    simpa only [hcomm] using ha ⟨s, self_mem_booleanSimonSubgroup s⟩
  · intro ha h
    have hle : AddSubgroup.zmultiples s ≤ (booleanDotHom a).ker := by
      apply AddSubgroup.zmultiples_le.mpr
      change booleanDot a s = 0
      rw [hcomm]
      exact ha
    exact hle h.property

theorem marginalProbLeft_hiddenSubgroupSampling_simonReg_singleton
    {n : ℕ} {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : BooleanVec n) (hf : BooleanSimonPromise f s)
    (y : Qatlib.Foundations.PureStateMath.Reg n) :
    MarginalProbLeft
        (Run (AddOracle f)
          (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv)
          (TensorState (Uniform (BooleanVec n)) (Ket 0)))
        {regBooleanEquiv n y} =
      if booleanDot s (regBooleanEquiv n y) = 0 then
        1 / (Fintype.card (characterAnnihilator (booleanSimonSubgroup s)) : ℝ)
      else 0 := by
  simpa only [mem_booleanOrthogonal_booleanSimonSubgroup_iff] using
    marginalProbLeft_hiddenSubgroupSampling_booleanReg_singleton
      f (booleanSimonSubgroup s) ((booleanSimonPromise_iff_hidesSubgroup f s).1 hf) y

theorem marginalProbLeft_hiddenSubgroupSampling_simonReg
    {n : ℕ} {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : BooleanVec n) (hf : BooleanSimonPromise f s)
    (S : Finset (Qatlib.Foundations.PureStateMath.Reg n)) :
    MarginalProbLeft
        (Run (AddOracle f)
          (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv)
          (TensorState (Uniform (BooleanVec n)) (Ket 0)))
        (S.map (regBooleanEquiv n).toEmbedding) =
      ∑ y ∈ S, if booleanDot s (regBooleanEquiv n y) = 0 then
        1 / (Fintype.card (characterAnnihilator (booleanSimonSubgroup s)) : ℝ)
      else 0 := by
  simpa only [mem_booleanOrthogonal_booleanSimonSubgroup_iff] using
    marginalProbLeft_hiddenSubgroupSampling_booleanReg
      f (booleanSimonSubgroup s) ((booleanSimonPromise_iff_hidesSubgroup f s).1 hf) S

theorem marginalProbLeft_hiddenSubgroupSampling_simonReg_bad
    {n : ℕ} {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : BooleanVec n) (hf : BooleanSimonPromise f s) :
    MarginalProbLeft
        (Run (AddOracle f)
          (hiddenSubgroupSamplingCircuit (R := R) (booleanCharacterEquiv n).toEquiv)
          (TensorState (Uniform (BooleanVec n)) (Ket 0)))
        ((Finset.univ.filter (fun y : Qatlib.Foundations.PureStateMath.Reg n =>
          booleanDot s (regBooleanEquiv n y) ≠ 0)).map
          (regBooleanEquiv n).toEmbedding) = 0 := by
  rw [marginalProbLeft_hiddenSubgroupSampling_simonReg f s hf]
  apply Finset.sum_eq_zero
  intro y hy
  exact if_neg (Finset.mem_filter.mp hy).2

end Qatlib.Concepts.HspRecovery.ReductionCore
