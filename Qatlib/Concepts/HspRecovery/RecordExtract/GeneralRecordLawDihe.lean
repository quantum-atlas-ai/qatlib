/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.GeneralRecordLawStat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.SimpRw

/-!
# The general dihedral record law

This module proves `SourceGeneralRecordLaw` for every nonzero modulus. A reflection-hiding
oracle gives a Fourier-label branch that factors into `dihedralQubitState` and an output
amplitude with squared norm sum `1 / N`, supplying the record-generation step used in
[Kuperberg2005].

## Main statements

* `source_record_joint_apply`: explicit Fourier-sum amplitudes.
* `source_record_factor`: phase-qubit factorization under the hiding promise.
* `sourceGeneralRecordLaw`: the factorization together with one-query, one-gate circuit counts.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.RecordExtract
open Matrix

/-- Applying a tensor product of a matrix with the identity acts on each fixed-second-coordinate
slice by that matrix. -/
private theorem source_tensor_one_slice {I : Type*} {J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (ψ : QState (I×J)) (x : I) (y : J) :
    ApplyGate (TensorGate U 1) ψ (x,y)=ApplyGate U (fun a => ψ (a,y)) x := by
  simp [ApplyGate,TensorGate,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply]

/-- A dihedral record amplitude is the normalized Fourier sum over inputs with the specified tag
and oracle output. -/
private theorem source_record_joint_apply (N : ℕ) [NeZero N] {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg N → S) (k : ZMod N) (t : Bool) (z : S) :
    dihedralRecordJoint N f ((k,t),z) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹*∑ a : ZMod N, ZMod.stdAddChar (k*a)*
        (Uniform (DihedralReg N) (a,t)*(if f (a,t)=z then 1 else 0)) := by
  simp only [dihedralRecordJoint,dihedralRecordCircuit,Run]
  rw [source_tensor_one_slice,source_tensor_one_slice]
  simp_rw [applyGate_addOracle]
  unfold zmodFourierGate
  simp only [ApplyGate,Matrix.mulVec,dotProduct,zmodQFTGate_apply,mul_assoc,← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hz : f (a,t)=z
  · rw [← hz]
    simp [TensorState,Ket]
  · have hsub : z-f (a,t) ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    simp [TensorState,Ket,hz,hsub]

/-- For a reflection-hiding oracle, each Fourier-label branch is the phase qubit times an output
amplitude whose squared norms sum to `1 / N`. -/
private theorem source_record_factor (N : ℕ) [NeZero N] {S : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N) (hf : DihedralReflectionHides N f s)
    (k : ZMod N) : ∃ γ : S → ℂ, (∑ z, ‖γ z‖^2)=1/(N : ℝ) ∧
      ∀ t z, dihedralRecordJoint N f ((k,t),z)=γ z*dihedralQubitState N s k t := by
  let χ := fun a : ZMod N => ZMod.stdAddChar (k*a)
  let P := fun z : S => ∑ a : ZMod N, χ a*(if f (a,false)=z then (1 : ℂ) else 0)
  let β := (Real.sqrt (N : ℝ) : ℂ)⁻¹*(Real.sqrt (Fintype.card (DihedralReg N)) : ℂ)⁻¹
  let A := (Real.sqrt 2 : ℂ)*β
  have hN : 0 < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hjoint (t : Bool) (z : S) : dihedralRecordJoint N f ((k,t),z)=
      β*(∑ a : ZMod N, χ a*(if f (a,t)=z then (1 : ℂ) else 0)) := by
    rw [source_record_joint_apply]
    dsimp [χ,β]
    simp only [Uniform]
    rw [mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hshift (a : ZMod N) : f (a,true)=f (a-s,false) := by
    symm
    apply (hf _ _).2
    right
    simp [dihedralReflect]
  have hsum (z : S) : (∑ a : ZMod N, χ a*(if f (a,true)=z then (1 : ℂ) else 0)) =
      ZMod.stdAddChar (k*s)*P z := by
    have he := Equiv.sum_comp (Equiv.addRight s)
      (fun a : ZMod N => χ a*(if f (a,true)=z then (1 : ℂ) else 0))
    rw [← he]
    dsimp [P,χ]
    simp_rw [hshift,add_sub_cancel_right,mul_add,ZMod.stdAddChar.map_add_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hinj : Function.Injective (fun a : ZMod N => f (a,false)) := by
    intro a b hab
    rcases (hf (a,false) (b,false)).1 hab with he | he
    · exact (congrArg Prod.fst he).symm
    · have h := congrArg Prod.snd he
      simp [dihedralReflect] at h
  have hnorm (z : S) : ‖P z‖^2=∑ a : ZMod N, if f (a,false)=z then (1 : ℝ) else 0 := by
    by_cases hz : ∃ a : ZMod N, f (a,false)=z
    · obtain ⟨a,ha⟩ := hz
      have he (b : ZMod N) : f (b,false)=z ↔ b=a := by
        rw [← ha]
        exact hinj.eq_iff
      dsimp [P]
      simp only [he,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      rw [show ‖χ a‖=1 from ZMod.stdAddChar.norm_apply (k*a)]
      norm_num
    · have hn : ∀ a : ZMod N, f (a,false) ≠ z := by simpa only [not_exists] using hz
      simp [P,hn]
  have hnormSum : (∑ z : S, ‖P z‖^2)=(N : ℝ) := by
    simp only [hnorm]
    rw [Finset.sum_comm]
    simp [eq_comm]
  have hA : ‖A‖^2=1/(N : ℝ)^2 := by
    dsimp [A,β]
    simp only [norm_mul,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),inv_pow]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt (Nat.cast_nonneg N),
      Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (DihedralReg N)))]
    simp only [DihedralReg,Fintype.card_prod,ZMod.card,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  refine ⟨fun z => A*P z,?_,?_⟩
  · simp only [norm_mul,mul_pow,hA,← Finset.mul_sum,hnormSum]
    field_simp
  · intro t z
    rw [hjoint]
    cases t
    · change β*P z=(A*P z)*((1 : ℂ)/Real.sqrt 2*1)
      dsimp [A]
      field_simp
    · rw [hsum]
      change β*(ZMod.stdAddChar (k*s)*P z)=(A*P z)*((1 : ℂ)/Real.sqrt 2*dihedralQubitPhase N s k)
      rw [dihedralQubitPhase_eq_stdAddChar]
      dsimp [A]
      field_simp

/-- The general dihedral record law holds for every nonzero modulus, with one query, one gate,
and the stated qubit factorization [Kuperberg2005]. -/
theorem sourceGeneralRecordLaw : SourceGeneralRecordLaw := by
  intro N _ S _ _ _ f s hf
  refine ⟨by simp [dihedralRecordCircuit, QueryCount],
    by simp [dihedralRecordCircuit, GateCount], ?_⟩
  exact source_record_factor N f s hf

end Qatlib.Concepts.HspRecovery.RecordExtract
