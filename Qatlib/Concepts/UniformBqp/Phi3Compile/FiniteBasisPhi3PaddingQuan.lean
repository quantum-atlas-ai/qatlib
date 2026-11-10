/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.FiniteBasisPhi3PaddingStat
import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3UniversalityTheorem1Quan
set_option warningAsError false
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
