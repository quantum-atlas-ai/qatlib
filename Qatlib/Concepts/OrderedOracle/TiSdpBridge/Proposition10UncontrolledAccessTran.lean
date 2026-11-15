/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Proposition10UncontrolledAccessStat
public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ControlledAccessSimulationKernelTran
public import Qatlib.Foundations.BornMetrics.EventProbability
public import Qatlib.Foundations.QueryWordCore.Circuit

@[expose] public section
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators

def ospComplementInput (n : ℕ) [NeZero n] (j : Fin (2*n)) : Fin (2*n) :=
  ⟨((j:ℕ)+n)%(2*n),Nat.mod_lt _ (by have hn := NeZero.pos n; omega)⟩

/-- Complementing an ordered-search input negates every oracle bit. -/
theorem osp_complement_bit (n : ℕ) [NeZero n] (j i : Fin (2*n)) :
    ospBit n (ospComplementInput n j) i= !(ospBit n j i) := by
  have hn : (0:ℤ)<n := by exact_mod_cast NeZero.pos n
  let r : ℤ := ((i:ℤ)-(j:ℤ))%(2*(n:ℤ))
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrN : r<2*(n:ℤ) := Int.emod_lt_of_pos _ (by omega)
  have he : ((i:ℤ)-(ospComplementInput n j:ℤ))%(2*(n:ℤ))=
      (r-(n:ℤ))%(2*(n:ℤ)) := by
    change ((i:ℤ)-((((j:ℕ)+n)%(2*n):ℕ):ℤ))%(2*(n:ℤ))=_
    rw [Int.natCast_mod]
    push_cast
    rw [Int.sub_emod_emod]
    rw [show (i:ℤ)-((j:ℤ)+(n:ℤ))=((i:ℤ)-(j:ℤ))-(n:ℤ) by ring]
    exact (Int.emod_sub_emod _ _ _).symm
  unfold ospBit
  rw [he]
  change decide ((r-(n:ℤ))%(2*(n:ℤ))<(n:ℤ))= !(decide (r<(n:ℤ)))
  by_cases hr : r<(n:ℤ)
  · have hm : (r-(n:ℤ))%(2*(n:ℤ))=r+(n:ℤ) := by
      rw [show r-(n:ℤ)=(r+(n:ℤ))-2*(n:ℤ) by ring,Int.sub_emod_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm]
    simp [hr,show ¬r+(n:ℤ)<(n:ℤ) by omega]
  · have hm : (r-(n:ℤ))%(2*(n:ℤ))=r-(n:ℤ) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm]
    simp [hr,show r-(n:ℤ)<(n:ℤ) by omega]

/-- Complementing an ordered-search input leaves its required output unchanged. -/
theorem osp_complement_output (n : ℕ) [NeZero n] (j : Fin (2*n)) :
    ospFun n (ospComplementInput n j)=ospFun n j := by
  apply Fin.val_injective
  change (((j:ℕ)+n)%(2*n))%n=(j:ℕ)%n
  rw [Nat.mod_mod_of_dvd _ (by norm_num : n ∣ 2*n),Nat.add_mod_right]

/-- Normalizing oracle bits against the reference bit yields either the original ordered-search
input or its complement. -/
theorem osp_reference_normalized_input (n : ℕ) [NeZero n] (j : Fin (2*n)) :
    (fun i => ospBit n j i ^^ ospBit n j (0 : Fin (2*n)))=
      ospBit n (if ospBit n j (0 : Fin (2*n)) then ospComplementInput n j else j) := by
  funext i
  cases ospBit n j (0 : Fin (2*n)) <;> simp [osp_complement_bit]

/-- An ordered-search controlled-oracle algorithm admits an uncontrolled simulation preserving
success probability, query count, unitarity, and input normalization. -/
theorem proposition10UncontrolledAccess : Proposition10UncontrolledAccess := by
  intro n _ W _ _ ε C ψ E _ _ hC hψ hs
  obtain ⟨hq,hu,hinit,_⟩ := controlledAccessSimulationKernel (Fin (2*n)) W 0 (ospBit n 0) C ψ
  refine ⟨hu hC,hinit hψ,hq,?_⟩
  intro j
  have hr := (controlledAccessSimulationKernel (Fin (2*n)) W 0 (ospBit n j) C ψ).2.2.2
  have hp : ‖((if ospBit n j (0 : Fin (2*n)) then (-1:ℂ) else 1)^QueryCount C)‖=1 := by
    split_ifs <;> simp
  rw [hr,measureProb_smul,hp,one_pow,one_mul,
    measureProb_tensorState_right (normalized_ket (0 : Fin (2*n))),osp_reference_normalized_input]
  cases hf : ospBit n j (0 : Fin (2*n)) with
  | false => simpa only [hf,Bool.false_eq_true,ite_false] using hs j
  | true =>
    simpa only [hf,ite_true,osp_complement_output] using hs (ospComplementInput n j)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
