/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.FiniteBasisPhi3PaddingStat
import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3UniversalityTheorem1Quan

/-!
# Exact Phi3 synthesis after finite-basis padding

`finiteBasisPhi3Padding` combines an injective finite-basis encoding with exact unitary
synthesis on three extra wires. The separate zero-data case preserves the scalar phase of a
zero-qubit unitary and completes the same cost and execution guarantees at width zero. The
background is described in [Yao1993].

## Main statements

* `phi3_zero_data_synthesis`: exact synthesis for zero data qubits.
* `finiteBasisPhi3Padding`: the full encoding, padding, and synthesis guarantee.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.Phi3Universal

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
open Matrix
open scoped Classical BigOperators

/-- Every unitary on the zero-qubit register has an exact Phi3 implementation on three auxiliary
wires, with no queries, gate count equal to word length, and length bounded by
`phi3PaddingBudget 0`. -/
theorem phi3_zero_data_synthesis (U : Matrix (Reg 0) (Reg 0) ℂ)
    (hU : U ∈ unitaryGroup (Reg 0) ℂ) :
    ∃ gs : List (Phi3Gate (0+3)),
      IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
      GateCount (phi3Compile gs) = gs.length ∧ gs.length ≤ phi3PaddingBudget 0 ∧
      ∀ ψ : QState (Reg 0), Run 1 (phi3Compile gs)
        (knownWireEmbed (knownPrefixWires 0 3) ψ) =
        knownWireEmbed (knownPrefixWires 0 3) (U *ᵥ ψ) := by
  let x : Reg 0 := fun _ => false
  let z : ℂ := U x x
  have hz : star z * z = 1 := by
    have hu : Uᴴ*U=1 := by
      simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hU
    have hh := congrArg (fun V : Matrix (Reg 0) (Reg 0) ℂ => V x x) hu
    change (∑ y : Reg 0, star (U y x) * U y x) = 1 at hh
    rw [Finset.sum_eq_single x] at hh
    · exact hh
    · intro y _ hy
      exact (hy (Subsingleton.elim _ _)).elim
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  have hz' : z * star z = 1 := (mul_comm z (star z)).trans hz
  have hlocal : z • (1 : Matrix (Reg 3) (Reg 3) ℂ) ∈ unitaryGroup (Reg 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    simp [Matrix.conjTranspose_smul, smul_smul]
    change (z * star z) • (1 : Matrix (Reg 3) (Reg 3) ℂ) = 1
    rw [hz', one_smul]
  let g : Phi3Gate 3 := ⟨id, Function.injective_id, z • 1, hlocal⟩
  have hg : phi3GateMatrix g = z • 1 := by
    ext r s
    simp [phi3GateMatrix, g]
  have hscalar (ψ : QState (Reg 0)) : U *ᵥ ψ = z • ψ := by
    funext y
    have hy : y=x := Subsingleton.elim _ _
    change (∑ u : Reg 0, U y u * ψ u) = z * ψ y
    rw [Finset.sum_eq_single x]
    · rw [hy]
    · intro u _ hu
      exact (hu (Subsingleton.elim _ _)).elim
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  obtain ⟨hq,hc⟩ := phi3Compile_count [g]
  refine ⟨[g], isUnitaryCircuit_phi3Compile [g], hq, hc, by norm_num [phi3PaddingBudget], ?_⟩
  intro ψ
  simp only [phi3Compile, List.map_cons, List.map_nil, Run, ApplyGate, hg,
    Matrix.smul_mulVec, Matrix.one_mulVec, hscalar, knownWireEmbed_smul]

/-- Finite basis encoding, unitary padding, and exact Phi3 synthesis satisfy
`FiniteBasisPhi3Padding`, including preservation of normalized embedded states and the
stated word-length budget [Yao1993]. -/
theorem finiteBasisPhi3Padding : FiniteBasisPhi3Padding := by
  constructor
  · intro I _ b hb
    exact finiteBasisCode_injective hb
  · intro I _ _ b e U he hU
    refine ⟨finiteBasisPadUnitary_unitary e he U hU,
      (fun _ hψ => finiteBasisPadState_normalized e he hψ),
      finiteBasisPadUnitary_apply e he U, ?_⟩
    have hV := finiteBasisPadUnitary_unitary e he U hU
    cases b with
    | zero =>
      obtain ⟨gs,hgs,hq,hc,hlen,hr⟩ := phi3_zero_data_synthesis (finiteBasisPadUnitary e U) hV
      refine ⟨gs,hgs,hq,hc,hlen,?_⟩
      intro ψ
      rw [hr]
      exact congrArg (knownWireEmbed (knownPrefixWires 0 3))
        (finiteBasisPadUnitary_apply e he U ψ)
    | succ b =>
      obtain ⟨gs,hgs,hq,hc,hlen,hr⟩ :=
        phi3UniversalityTheorem1 (b+1) (by omega) (finiteBasisPadUnitary e U) hV
      refine ⟨gs,hgs,hq,hc,hlen,?_⟩
      intro ψ
      rw [hr]
      exact congrArg (knownWireEmbed (knownPrefixWires (b+1) 3))
        (finiteBasisPadUnitary_apply e he U ψ)

end Qatlib.Concepts.UniformBqp.Phi3Compile
