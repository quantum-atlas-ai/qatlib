/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl
import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution

/-!
# Local Fresh-Copy Register Layout

The `3*n+2` physical wires contain a control bit, two `n`-qubit data registers, `n` AND scratch
bits, and one parity scratch bit. The equivalence `localCopySplit` exposes this decomposition,
while the isometry `localCopyFrame` initializes the scratch to zero in the circuit setting of
[NielsenChuang2010].

The words `localCopyBellSteps`, `localCopyComputeAndParity`, and `localCopyControlledPhaseSteps`
form `localControlledSwapSteps`. They provide the explicit local gates whose clean frame action
is established by the companion semantics modules.

## Main statements

- `localCopyFrame_isometry` proves that clean embedding preserves inner products.
- `local_copy_explicit_layout_and_clean_frame` records the wire indices and clean frame entries.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators
set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers

/-- The control wire at physical index zero in the `3*n+2`-wire layout. -/
def localCopyControlWire (n : ℕ) : Fin (3*n+2) := ⟨0, by omega⟩

/-- The parity scratch wire at physical index `1+3*n`. -/
def localCopyParityWire (n : ℕ) : Fin (3*n+2) := ⟨1+3*n, by omega⟩

/-- The `i`th data wire at physical index `1+i.val`. -/
def localCopyDataWire (n : ℕ) (i : Fin n) : Fin (3*n+2) := ⟨1+i.val, by omega⟩

/-- The `i`th fresh copy wire at physical index `1+n+i.val`. -/
def localCopyFreshWire (n : ℕ) (i : Fin n) : Fin (3*n+2) := ⟨1+n+i.val, by omega⟩

/-- The `i`th AND scratch wire at physical index `1+2*n+i.val`. -/
def localCopyAndWire (n : ℕ) (i : Fin n) : Fin (3*n+2) := ⟨1+2*n+i.val, by omega⟩

/-- The physical bit register assembled from a logical control and pair of data labels together
with AND and parity scratch values. -/
private def localCopyAssemble (n : ℕ)
    (p : (Bool × (Fin (2^n) × Fin (2^n))) × (Reg n × Bool)) : Reg (3*n+2) :=
  fun k => if h0 : k.val = 0 then p.1.1
    else if hd : k.val < 1+n then (bitVecEquiv n).symm p.1.2.1 ⟨k.val-1, by omega⟩
    else if hf : k.val < 1+2*n then (bitVecEquiv n).symm p.1.2.2 ⟨k.val-(1+n), by omega⟩
    else if ha : k.val < 1+3*n then p.2.1 ⟨k.val-(1+2*n), by omega⟩
    else p.2.2

/-- The equivalence splitting the physical register into a logical control and pair of `n`-qubit
labels, plus AND and parity scratch. -/
def localCopySplit (n : ℕ) :
    Reg (3*n+2) ≃ (Bool × (Fin (2^n) × Fin (2^n))) × (Reg n × Bool) where
  toFun x := ((x (localCopyControlWire n),
    (bitVecEquiv n (fun i => x (localCopyDataWire n i)),
     bitVecEquiv n (fun i => x (localCopyFreshWire n i)))),
    (fun i => x (localCopyAndWire n i), x (localCopyParityWire n)))
  invFun := localCopyAssemble n
  left_inv x := by
    funext k
    dsimp [localCopyAssemble]
    split_ifs with h0 hd hf ha
    · congr 1
      apply Fin.ext
      exact h0.symm
    · simp only [Equiv.symm_apply_apply]
      congr 1
      apply Fin.ext
      dsimp [localCopyDataWire]
      omega
    · simp only [Equiv.symm_apply_apply]
      congr 1
      apply Fin.ext
      dsimp [localCopyFreshWire]
      omega
    · congr 1
      apply Fin.ext
      dsimp [localCopyAndWire]
      omega
    · congr 1
      apply Fin.ext
      dsimp [localCopyParityWire]
      omega
  right_inv p := by
    rcases p with ⟨⟨b, d, f⟩, a, q⟩
    have hd : (fun i : Fin n => localCopyAssemble n ((b, (d,f)), (a,q))
        (localCopyDataWire n i)) = (bitVecEquiv n).symm d := by
      funext i
      simp [localCopyAssemble, localCopyDataWire, show 1+i.val < 1+n by omega]
    have hf : (fun i : Fin n => localCopyAssemble n ((b, (d,f)), (a,q))
        (localCopyFreshWire n i)) = (bitVecEquiv n).symm f := by
      funext i
      simp [localCopyAssemble, localCopyFreshWire,
          show ¬ 1+n+i.val < 1+n by omega, show 1+n+i.val < 1+2*n by omega]
    have ha : (fun i : Fin n => localCopyAssemble n ((b, (d,f)), (a,q))
        (localCopyAndWire n i)) = a := by
      funext i
      simp [localCopyAssemble, localCopyAndWire, show ¬ 1+2*n+i.val < 1+n by omega, show ¬ 1+2*n+i.val < 1+2*n by omega,
        show 1+2*n+i.val < 1+3*n by omega]
    simp only [hd, hf, ha, Equiv.apply_symm_apply]
    simp [localCopyAssemble, localCopyControlWire, localCopyParityWire,
      show ¬ 1+3*n < 1+n by omega,
      show ¬ 1+3*n < 1+2*n by omega]

/-- The clean embedding matrix assigning each logical basis state its physical representative
with all AND and parity scratch bits zero. -/
noncomputable def localCopyFrame (n : ℕ) :
    Matrix (Reg (3*n+2)) (Bool × (Fin (2^n) × Fin (2^n))) ℂ :=
  fun x p => if localCopySplit n x = (p, ((fun _ => false), false)) then 1 else 0

/-- The clean embedding matrix is an isometry. -/
theorem localCopyFrame_isometry (n : ℕ) : IsIsometry (localCopyFrame n) := by
  let f := fun p : Bool × (Fin (2^n) × Fin (2^n)) =>
    (localCopySplit n).symm (p, ((fun _ => false), false))
  have hf : Function.Injective f := by
    intro p q h
    exact congrArg Prod.fst ((localCopySplit n).symm.injective h)
  have he : ∀ x p, localCopyFrame n x p = if x = f p then (1 : ℂ) else 0 := by
    intro x p
    simp only [localCopyFrame, f, Equiv.eq_symm_apply]
  unfold IsIsometry
  ext p q
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, he, Matrix.one_apply]
  by_cases hpq : p = q
  · subst q
    rw [Finset.sum_eq_single (f p)]
    · simp
    · intro x _ hx; simp [hx]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hpq]
    · intro x _
      have hne : f p ≠ f q := fun h => hpq (hf h)
      by_cases hx : x = f p
      · rw [hx]; simp [hne]
      · by_cases hx' : x = f q
        · rw [hx']; simp [Ne.symm hne]
        · simp [hx]

/-- The layout has the stated control, parity, data, fresh copy, and AND wire indices, and its
clean frame is an isometry. The frame entries select exactly the physical states with the
prescribed logical label and zero scratch. -/
theorem local_copy_explicit_layout_and_clean_frame :
    ∀ n : ℕ, (localCopyControlWire n).val = 0 ∧
      (localCopyParityWire n).val = 1+3*n ∧
      (∀ i : Fin n, (localCopyDataWire n i).val = 1+i.val ∧
        (localCopyFreshWire n i).val = 1+n+i.val ∧
        (localCopyAndWire n i).val = 1+2*n+i.val) ∧
      IsIsometry (localCopyFrame n) ∧
      (∀ (x : Reg (3*n+2)) (p : Bool × (Fin (2^n) × Fin (2^n))),
        localCopyFrame n x p =
          if localCopySplit n x = (p, ((fun _ => false), false)) then 1 else 0) := by
  intro n
  exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩, localCopyFrame_isometry n, fun _ _ => rfl⟩

/-- The Bell basis word applying a Hadamard on each data wire followed by a CNOT from that wire
to its corresponding fresh copy wire. -/
noncomputable def localCopyBellSteps (n : ℕ) : List (ReflectionGate (3*n+2)) :=
  (List.finRange n).flatMap fun i =>
    [.inl (localCopyDataWire n i, Hadamard),
     .inr (localCopyDataWire n i, localCopyFreshWire n i)]

/-- The physical basis permutation exchanging the data and fresh copy register labels while
preserving control and scratch. -/
def localCopySwapBasis (n : ℕ) (x : Reg (3*n+2)) : Reg (3*n+2) :=
  let p := localCopySplit n x
  (localCopySplit n).symm ((p.1.1, (p.1.2.2, p.1.2.1)), p.2)

/-- The permutation matrix exchanging the physical data and fresh copy registers. -/
noncomputable def localCopyRegisterSwap (n : ℕ) : Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ :=
  permMatrix (localCopySwapBasis n)

/-- The word computing each data and fresh bitwise AND into its scratch wire and accumulating
those ANDs into the parity wire. -/
noncomputable def localCopyComputeAndParity (n : ℕ) : List (ReflectionGate (3*n+2)) :=
  (List.finRange n).flatMap fun i =>
    toffoliLocalSteps (localCopyDataWire n i) (localCopyFreshWire n i)
      (localCopyAndWire n i) ++ [.inr (localCopyAndWire n i, localCopyParityWire n)]

/-- The embedding of a known two qubit control-synthesis step into the physical control and
parity wires. -/
noncomputable def localCopyControlStep (n : ℕ) : KnownQubitControlStep → ReflectionGate (3*n+2)
  | .single b p => .inl (if b then localCopyControlWire n else localCopyParityWire n,
      knownQubitUnitary p)
  | .cnot => .inr (localCopyControlWire n, localCopyParityWire n)

/-- The known qubit synthesis word for a parity wire rotation by `2*θ` controlled by the
physical control wire. -/
noncomputable def localCopyControlledPhaseSteps (n : ℕ) (θ : ℝ) :
    List (ReflectionGate (3*n+2)) :=
  (knownQubitControlSteps (knownQubitAnglesOfUnitary (Rz (2*θ)))).map (localCopyControlStep n)

/-- The local controlled partial swap word combining inverse Bell preparation, parity
computation, a controlled phase, uncomputation, Bell preparation, and a final negative angle
control rotation. -/
noncomputable def localControlledSwapSteps (n : ℕ) (θ : ℝ) : List (ReflectionGate (3*n+2)) :=
  reflectionAdjoint (localCopyBellSteps n) ++ localCopyComputeAndParity n ++
    localCopyControlledPhaseSteps n θ ++ reflectionAdjoint (localCopyComputeAndParity n) ++
    localCopyBellSteps n ++ [.inl (localCopyControlWire n, Rz (-θ))]
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
