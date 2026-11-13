/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.HiddenSubgroupSampling
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Dihedral coset records and phase qubits

This module defines the reflection-hiding promise, a query-and-Fourier record circuit, and the
resulting joint state. The phase states `dihedralQubitState` are the labelled qubits used in the
dihedral sieve of [Kuperberg2005].

The record factorization separates the qubit state from an oracle-output amplitude with squared
norm sum `1 / N`. For power-of-two moduli, the module packages the circuit counts and proves the
uniform label-bit marginal.

## Main statements

* `dihedralRecordCircuit_unitary`: unitarity of the record circuit.
* `dihedral_record_factor`: factorization of each Fourier-label branch.
* `dihedralRecordLaw`: the power-of-two record law and circuit counts.
* `dihedralRecordBitMarginal`: the uniform label-bit marginal.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.RecordExtract

open Matrix Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

variable (N : ℕ) [NeZero N] {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- The dihedral register type consisting of a rotation label in `ZMod N` and a Boolean tag. -/
abbrev DihedralReg (N : ℕ) := ZMod N × Bool

/-- Toggle the Boolean tag while adding `s` to the rotation label on the false branch and
subtracting `s` on the true branch. -/
def dihedralReflect (s : ZMod N) : DihedralReg N → DihedralReg N
  | (a, false) => (a + s, true)
  | (a, true) => (a - s, false)

/-- The reflection-hiding promise that two inputs have equal oracle values exactly when they are
equal or related by `dihedralReflect`. -/
def DihedralReflectionHides (f : DihedralReg N → S) (s : ZMod N) : Prop :=
  ∀ p q : DihedralReg N, f p = f q ↔ q = p ∨ q = dihedralReflect N s p

/-- The cyclic quantum Fourier transform matrix on `ZMod N`. -/
noncomputable def zmodFourierGate : Matrix (ZMod N) (ZMod N) ℂ :=
  Qatlib.Concepts.QuditTeleport.TeleportCore.zmodQFTGate

/-- The cyclic Fourier gate is unitary for nonzero `N`. -/
theorem zmodFourierGate_unitary :
    zmodFourierGate N ∈ Matrix.unitaryGroup (ZMod N) ℂ :=
  Qatlib.Concepts.QuditTeleport.TeleportCore.zmodQFTGate_unitary (NeZero.pos N)

/-- The record circuit consisting of one oracle query followed by the cyclic Fourier gate on the
rotation register. -/
noncomputable def dihedralRecordCircuit : Circuit (DihedralReg N × S) :=
  [Step.query, Step.gate (TensorGate (TensorGate (zmodFourierGate N)
    (1 : Matrix Bool Bool ℂ)) (1 : Matrix S S ℂ))]

omit [AddCommGroup S] in

/-- The dihedral record circuit is a unitary circuit. -/
theorem dihedralRecordCircuit_unitary :
    IsUnitaryCircuit (dihedralRecordCircuit (N := N) (S := S)) := by
  simp only [dihedralRecordCircuit, isUnitaryCircuit_query, isUnitaryCircuit_gate,
    isUnitaryCircuit_nil, and_true]
  exact tensorGate_unitary
    (tensorGate_unitary (zmodFourierGate_unitary N) (Submonoid.one_mem _))
    (Submonoid.one_mem _)

/-- The joint state obtained by running the record circuit with the additive oracle, a uniform
dihedral input, and a zero output register. -/
noncomputable def dihedralRecordJoint (f : DihedralReg N → S) :
    QState (DihedralReg N × S) :=
  Run (AddOracle f) (dihedralRecordCircuit (N := N) (S := S))
    (TensorState (Uniform (DihedralReg N)) (Ket 0))

/-- The joint state produced by the dihedral record circuit is normalized. -/
theorem normalized_dihedralRecordJoint (f : DihedralReg N → S) :
    Normalized (dihedralRecordJoint N f) :=
  (dihedralRecordCircuit_unitary (N := N) (S := S)).normalized_run (addOracle_unitary f)
    (normalized_tensorState
      (normalized_uniform (by exact_mod_cast Fintype.card_pos)) (normalized_ket 0))

/-- The complex phase given by the exponential of `2πi` times the representative of `s * k`
divided by `N`. -/
noncomputable def dihedralQubitPhase (s k : ZMod N) : ℂ :=
  Complex.exp (((2 * Real.pi * ((s * k).val / N : ℝ) : ℝ) * Complex.I))

/-- The qubit with false amplitude `1 / sqrt 2` and true amplitude `dihedralQubitPhase N s k /
sqrt 2`. -/
noncomputable def dihedralQubitState (s k : ZMod N) : QState Bool :=
  fun t => (1 : ℂ) / Real.sqrt 2 * cond t (dihedralQubitPhase N s k) 1

omit [NeZero N] in

/-- The dihedral qubit phase has complex norm one. -/
theorem norm_dihedralQubitPhase (s k : ZMod N) : ‖dihedralQubitPhase N s k‖ = 1 := by
  show ‖Complex.exp (((2 * Real.pi * ((s * k).val / N : ℝ) : ℝ) * Complex.I))‖ = 1
  exact Complex.norm_exp_ofReal_mul_I _

omit [AddCommGroup S] in

/-- Every dihedral phase qubit is normalized. -/
theorem normalized_dihedralQubitState (s k : ZMod N) :
    Normalized (dihedralQubitState N s k) := by
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have key : ∀ x : ℂ, ‖(1 : ℂ) / Real.sqrt 2 * x‖ ^ 2 = 1 / 2 * ‖x‖ ^ 2 := by
    intro x
    rw [Complex.norm_mul, Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt, norm_one, mul_pow, div_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  unfold Normalized
  rw [Fintype.univ_bool, Finset.sum_insert (by simp), Finset.sum_singleton]
  have ht : dihedralQubitState N s k true =
      (1 : ℂ) / Real.sqrt 2 * dihedralQubitPhase N s k := rfl
  have hf : dihedralQubitState N s k false = (1 : ℂ) / Real.sqrt 2 * 1 := rfl
  rw [ht, hf, key _, key 1, norm_dihedralQubitPhase, norm_one]
  norm_num

/-- The subtype of normalized pure qubit states. -/
abbrev NormQ : Type := { χ : QState Bool // Normalized χ }

/-- Normalize a qubit branch using `ConditionalState`, returning `Plus` when no conditional
state is available. -/
noncomputable def actualRecordState (branch : QState Bool) : NormQ := by
  cases h : ConditionalState branch with
  | some ξ => exact ⟨ξ, normalized_of_conditionalState_eq_some h⟩
  | none => exact ⟨Plus, normalized_plus⟩

/-- The actual record law retaining the Fourier label, oracle output, and normalized conditional
qubit branch. -/
noncomputable def dihedralActualRecord (f : DihedralReg N → S) :
    PMF (ZMod N × S × NormQ) :=
  (bornDistribution (dihedralRecordJoint N f) (normalized_dihedralRecordJoint N f)).map
    fun q =>
      let k : ZMod N := q.1.1
      let z : S := q.2
      (k, z, actualRecordState (fun t => dihedralRecordJoint N f ((k, t), z)))

/-- Applying `U` tensored with the identity to a joint state acts by `U` on each slice with
fixed second coordinate. -/
private theorem dihedral_tensor_one_slice {I : Type*} {J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (ψ : QState (I×J)) (x : I) (y : J) :
    ApplyGate (TensorGate U 1) ψ (x,y)=ApplyGate U (fun a => ψ (a,y)) x := by
  simp [ApplyGate,TensorGate,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply]

/-- Each record-state amplitude is the normalized Fourier sum of the uniform input amplitudes
restricted to the specified oracle-output fiber. -/
private theorem dihedral_record_joint_apply (N : ℕ) [NeZero N] {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg N → S) (k : ZMod N) (t : Bool) (z : S) :
    dihedralRecordJoint N f ((k,t),z) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹*∑ a : ZMod N, ZMod.stdAddChar (k*a)*
        (Uniform (DihedralReg N) (a,t)*(if f (a,t)=z then 1 else 0)) := by
  simp only [dihedralRecordJoint,dihedralRecordCircuit,Run]
  rw [dihedral_tensor_one_slice,dihedral_tensor_one_slice]
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

/-- The dihedral qubit phase equals the standard additive character evaluated at `k * s`. -/
theorem dihedralQubitPhase_eq_stdAddChar (N : ℕ) [NeZero N] (s k : ZMod N) :
    dihedralQubitPhase N s k=ZMod.stdAddChar (k*s) := by
  rw [ZMod.stdAddChar_apply]
  rw [ZMod.toCircle_apply]
  unfold dihedralQubitPhase
  congr 1
  rw [mul_comm k s]
  push_cast
  ring

/-- Under the reflection-hiding promise, each Fourier-label branch factors as the phase qubit
times an output amplitude whose squared norms sum to `1 / N`. -/
private theorem dihedral_record_factor (N : ℕ) [NeZero N] {S : Type*} [Fintype S] [DecidableEq S]
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
    rw [dihedral_record_joint_apply]
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
      simp only [he,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
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

/-- For a power-of-two modulus and a reflection-hiding oracle, the record circuit uses one query
and one gate and has the stated phase-qubit factorization [Kuperberg2005]. -/
theorem dihedralRecordLaw (n : ℕ) {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (s : ZMod (2^n)) (hf : DihedralReflectionHides (2^n) f s) :
    QueryCount (dihedralRecordCircuit (N := 2^n) (S := S))=1 ∧
    GateCount (dihedralRecordCircuit (N := 2^n) (S := S))=1 ∧
    ∀ k : ZMod (2^n), ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖^2)=1/(2^n : ℝ) ∧
      ∀ t z, dihedralRecordJoint (2^n) f ((k,t),z)=γ z*dihedralQubitState (2^n) s k t := by
  refine ⟨by simp [dihedralRecordCircuit,QueryCount],by simp [dihedralRecordCircuit,GateCount],?_⟩
  intro k
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using dihedral_record_factor (2^n) f s hf k

/-- Each computational-basis outcome of a dihedral phase qubit has Born probability one half. -/
theorem dihedralQubitState_born (N : ℕ) [NeZero N] (s k : ZMod N) (t : Bool) :
    BornProb (dihedralQubitState N s k) t=1/2 := by
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  cases t <;>
    simp only [BornProb,dihedralQubitState,Bool.cond_false,Bool.cond_true,norm_mul,norm_div,
      norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hroot,mul_pow,div_pow,
      norm_dihedralQubitPhase,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> norm_num

/-- For a reflection-hiding oracle at modulus `2 ^ n`, each label-bit pair has Born marginal `1
/ (2 * 2 ^ n)`. -/
theorem dihedralRecordBitMarginal (n : ℕ) {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (s : ZMod (2^n)) (hf : DihedralReflectionHides (2^n) f s)
    (k : ZMod (2^n)) (t : Bool) :
    (∑ z : S, BornProb (dihedralRecordJoint (2^n) f) ((k,t),z))=1/(2*(2^n : ℝ)) := by
  obtain ⟨γ,hγ,hfactor⟩ := (dihedralRecordLaw n f s hf).2.2 k
  have he (z : S) : BornProb (dihedralRecordJoint (2^n) f) ((k,t),z)=‖γ z‖^2*(1/2) := by
    unfold BornProb
    rw [hfactor,norm_mul,mul_pow]
    rw [show ‖dihedralQubitState (2^n) s k t‖^2=1/2 from dihedralQubitState_born _ _ _ _]
  simp only [he,← Finset.sum_mul,hγ]
  ring

end Qatlib.Concepts.HspRecovery.RecordExtract
