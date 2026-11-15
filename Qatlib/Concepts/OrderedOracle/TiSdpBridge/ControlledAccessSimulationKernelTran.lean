/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ControlledAccessSimulationKernelStat
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

@[expose] public section
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

omit [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W] in

/-- The ordered-search access swap is an involution. -/
theorem osp_access_swap_involutive : Function.Involutive (@ospAccessSwap I W) := by
  rintro ⟨a,⟨⟨b,i⟩,w⟩⟩
  cases b <;> rfl

/-- The permutation matrix of the ordered-search access swap is unitary. -/
theorem osp_access_swap_unitary :
    permMatrix (@ospAccessSwap I W) ∈ Matrix.unitaryGroup (I×((Bool×I)×W)) ℂ :=
  permMatrix_unitary osp_access_swap_involutive

/-- The plain bus oracle multiplies each amplitude by the phase determined by its bus index. -/
theorem osp_plain_bus_apply (f : I → Bool) (ψ : QState (I×((Bool×I)×W)))
    (a : I) (p : (Bool×I)×W) :
    ApplyGate (ospPlainBusOracle f) ψ (a,p)=(if f a then (-1:ℂ) else 1)*ψ (a,p) := by
  simp [ApplyGate,ospPlainBusOracle,TensorGate,PhaseOracle,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Matrix.diagonal_apply,Matrix.one_apply]

/-- The controlled phase oracle multiplies an amplitude by negative one exactly when its control
and queried bit are both true. -/
theorem osp_controlled_apply (f : I → Bool) (ψ : QState ((Bool×I)×W)) (p : (Bool×I)×W) :
    ApplyGate (ospControlledPhaseOracle f) ψ p=(if p.1.1 && f p.1.2 then (-1:ℂ) else 1)*ψ p := by
  exact Matrix.mulVec_diagonal _ ψ p

/-- The one-query simulation implements the reference-normalized controlled phase oracle up to
the reference bit's global phase. -/
theorem osp_one_query_run (i₀ : I) (f : I → Bool) (ψ : QState ((Bool×I)×W)) :
    Run (ospPlainBusOracle f) (ospRemoveControlledStep (.query : Step ((Bool×I)×W)))
      (TensorState (Ket i₀) ψ)=
      (if f i₀ then (-1:ℂ) else 1) • TensorState (Ket i₀)
        (ApplyGate (ospControlledPhaseOracle (fun i => f i ^^ f i₀)) ψ) := by
  simp only [ospRemoveControlledStep,Run]
  funext p
  rcases p with ⟨a,⟨⟨b,i⟩,w⟩⟩
  rw [applyGate_permMatrix osp_access_swap_involutive,osp_plain_bus_apply,
    applyGate_permMatrix osp_access_swap_involutive,osp_access_swap_involutive]
  cases b <;> cases hf : f i₀ <;> cases hi : f i <;> by_cases ha : a=i₀ <;>
    simp [ospAccessSwap,TensorState,Ket,osp_controlled_apply,Pi.smul_apply,smul_eq_mul,ha,hf,hi]

/-- Circuit execution commutes with scalar multiplication of the input state. -/
theorem osp_run_smul {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (C : Circuit H) (a : ℂ) (ψ : QState H) :
    Run O C (a•ψ)=a•Run O C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [Run,ApplyGate,Matrix.mulVec_smul,ih]

omit [Fintype I] [Fintype W] in

/-- Removing controlled access preserves the circuit query count. -/
theorem osp_remove_query_count (C : Circuit ((Bool×I)×W)) :
    QueryCount (ospRemoveControlledCircuit C)=QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    change QueryCount (C.flatMap ospRemoveControlledStep)=QueryCount C at ih
    cases s <;> simp [ospRemoveControlledCircuit,ospRemoveControlledStep,QueryCount,ih]

/-- Removing controlled access preserves circuit unitarity. -/
theorem osp_remove_unitary (C : Circuit ((Bool×I)×W)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (ospRemoveControlledCircuit C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU,hC⟩ := (isUnitaryCircuit_gate U C).mp hC
      simpa only [ospRemoveControlledCircuit,List.flatMap_cons,ospRemoveControlledStep,
        List.singleton_append,isUnitaryCircuit_gate] using
        And.intro (tensorGate_unitary (Submonoid.one_mem _) hU) (ih hC)
    | query =>
      have hc := ih ((isUnitaryCircuit_query C).mp hC)
      simpa only [ospRemoveControlledCircuit,List.flatMap_cons,ospRemoveControlledStep,
        List.cons_append,List.nil_append,isUnitaryCircuit_gate,isUnitaryCircuit_query] using
        And.intro osp_access_swap_unitary (And.intro osp_access_swap_unitary hc)

/-- The circuit simulation reproduces the reference-normalized controlled-oracle run, with the
reference phase raised to the original query count. -/
theorem osp_remove_run (i₀ : I) (f : I → Bool) (C : Circuit ((Bool×I)×W))
    (ψ : QState ((Bool×I)×W)) :
    Run (ospPlainBusOracle f) (ospRemoveControlledCircuit C) (TensorState (Ket i₀) ψ)=
      ((if f i₀ then (-1:ℂ) else 1)^QueryCount C) • TensorState (Ket i₀)
        (Run (ospControlledPhaseOracle (fun i => f i ^^ f i₀)) C ψ) := by
  induction C generalizing ψ with
  | nil => simp [ospRemoveControlledCircuit,Run,QueryCount]
  | cons s C ih =>
    rw [ospRemoveControlledCircuit,List.flatMap_cons,run_append]
    change Run (ospPlainBusOracle f) (ospRemoveControlledCircuit C)
      (Run (ospPlainBusOracle f) (ospRemoveControlledStep s) (TensorState (Ket i₀) ψ))=_
    cases s with
    | gate U =>
      simp only [ospRemoveControlledStep,Run,applyGate_tensorGate,applyGate_one]
      exact ih (ApplyGate U ψ)
    | query =>
      rw [osp_one_query_run,osp_run_smul,ih]
      simp only [QueryCount,Run,pow_succ',mul_smul]

/-- Controlled access removal preserves query count and unitarity, embeds normalized inputs, and
satisfies the stated execution formula up to global phase. -/
theorem controlledAccessSimulationKernel : ControlledAccessSimulationKernel := by
  intro I W _ _ _ _ i₀ f C ψ
  exact ⟨osp_remove_query_count C,osp_remove_unitary C,
    fun hψ => normalized_tensorState (normalized_ket i₀) hψ,osp_remove_run i₀ f C ψ⟩

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
