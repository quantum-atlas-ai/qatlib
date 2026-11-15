/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.Section6Gadget

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.GraphQuery.GcBaselines
open Matrix
open scoped Classical

abbrev GadgetHostRegister (n : ℕ) (W : Type) := (Fin (gadgetAddrCount n) × Bool) × W
abbrev GadgetSourceRegister (n : ℕ) (W : Type) := (Fin (n*n) × Bool) × GadgetHostRegister n W

def gadgetVariableRole {n : ℕ} : GadgetVertex n → GadgetVertex n → Option (Fin n × Fin n)
  | .layer 0 a, .layer 1 b => some (b,a)
  | .layer 1 b, .layer 0 a => some (b,a)
  | .layer 2 b, .layer 3 a => some (b,a)
  | .layer 3 a, .layer 2 b => some (b,a)
  | _, _ => none

def gadgetAddressRole (n : ℕ) (a : Fin (gadgetAddrCount n)) : Option (Fin n × Fin n) :=
  gadgetVariableRole (gadgetAddrEquiv n a).1 (gadgetAddrEquiv n a).2

def gadgetSourceLabels (n : ℕ) (x : Fin n → Fin n → Bool) : Fin (n*n) → Bool :=
  fun i => let j := (finProdFinEquiv (m := n) (n := n)).symm i
           x j.1 j.2

def gadgetSourceZero (n : ℕ) (hn : 0 < n) : Fin (n*n) × Bool :=
  (finProdFinEquiv (⟨0,hn⟩,⟨0,hn⟩),false)

def gadgetSourceAddress (n : ℕ) (hn : 0 < n) (a : Fin (gadgetAddrCount n)) : Fin (n*n) :=
  finProdFinEquiv ((gadgetAddressRole n a).getD (⟨0,hn⟩,⟨0,hn⟩))

def gadgetAddressRoute {W : Type} [Fintype W] [DecidableEq W] (n : ℕ) (hn : 0 < n) :
    Matrix (GadgetSourceRegister n W) (GadgetSourceRegister n W) ℂ :=
  permMatrix fun p =>
    (((Equiv.swap (gadgetSourceZero n hn).1 (gadgetSourceAddress n hn p.2.1.1)) p.1.1,p.1.2),p.2)

def gadgetMaskTarget {W : Type} [Fintype W] [DecidableEq W] (n : ℕ)
    (adj : Fin n → Fin n → Bool) :
    Matrix (GadgetSourceRegister n W) (GadgetSourceRegister n W) ℂ :=
  permMatrix fun p =>
    (p.1,((p.2.1.1,p.2.1.2 ^^
      (if (gadgetAddressRole n p.2.1.1).isSome then p.1.2
        else gadgetOracleBit adj (fun _ _ => false) p.2.1.1)),p.2.2))

def gadgetCompileStep {W : Type} [Fintype W] [DecidableEq W] (n : ℕ) (hn : 0 < n)
    (adj : Fin n → Fin n → Bool) : Step (GadgetHostRegister n W) → Circuit (GadgetSourceRegister n W)
  | .gate U => [.gate (TensorGate (1 : Matrix (Fin (n*n) × Bool) (Fin (n*n) × Bool) ℂ) U)]
  | .query => [.gate (gadgetAddressRoute n hn), .query, .gate (gadgetMaskTarget n adj),
    .query, .gate (gadgetAddressRoute n hn)]

def gadgetCompileCircuit {W : Type} [Fintype W] [DecidableEq W] (n : ℕ) (hn : 0 < n)
    (adj : Fin n → Fin n → Bool) (C : Circuit (GadgetHostRegister n W)) :
    Circuit (GadgetSourceRegister n W) := C.flatMap (gadgetCompileStep n hn adj)

end Qatlib.Concepts.GraphQuery.GcBaselines
