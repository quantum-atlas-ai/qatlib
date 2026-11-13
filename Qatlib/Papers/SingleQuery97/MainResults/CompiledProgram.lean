/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.EncoderCircuit

/-!
# Compiling a one-query linear-code program

`lifted` realizes a list of known additive maps as gates on the encoding registers while
preserving a separate answer register. The circuit `word` uses these gates to compute and
uncompute the linear encoding around one hidden-oracle query, with Fourier preparation and
readout giving the response label. See [TerhalSmolin1998] for the source development.

## Main statements

* `run_lifted`: evaluates the known-gate list as addition of the sum of its maps.
* `word_resources`: counts one query and `2 + 2 * fs.length` explicit gates.
* `run_word`: returns the response basis state with the encoding workspace reset to zero.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.CompiledProgram

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.QuditTeleport.TeleportCore
open EncoderCircuit LinearCodeProgram

section Lift
variable {I X R : Type} [Fintype I] [DecidableEq I]
  [Fintype X] [DecidableEq X] [AddCommGroup X]
  [Fintype R] [DecidableEq R]

/-- The list of known additive gates associated with `fs`, lifted to preserve the separate
answer register. -/
noncomputable def lifted (fs : List (I → X)) : Circuit ((I × X) × R) :=
  fs.map (fun f => Step.gate (TensorGate (AddOracle f) 1))

omit [Fintype I] [Fintype X] [Fintype R] in

/-- The lifted known-map circuit uses no queries and has one explicit gate per list entry. -/
theorem lifted_resources (fs : List (I → X)) :
    QueryCount (lifted (R:=R) fs) = 0 ∧ GateCount (lifted (R:=R) fs) = fs.length := by
  induction fs with
  | nil => exact ⟨rfl,rfl⟩
  | cons f fs ih => simpa [lifted] using ih

/-- Every explicit gate of the lifted known-map circuit is unitary. -/
theorem lifted_unitary (fs : List (I → X)) : IsUnitaryCircuit (lifted (R:=R) fs) := by
  induction fs with
  | nil => exact isUnitaryCircuit_nil
  | cons f fs ih =>
    exact (isUnitaryCircuit_gate _ _).2
      ⟨tensorGate_unitary (addOracle_unitary f) (Matrix.unitaryGroup R ℂ).one_mem, ih⟩

/-- Running the lifted list applies addition of `fs.sum` to the encoding registers and leaves
the answer state unchanged. -/
theorem run_lifted (oracle : Matrix ((I × X) × R) ((I × X) × R) ℂ)
    (fs : List (I → X)) (ψ : QState (I × X)) (η : QState R) :
    Run oracle (lifted fs) (TensorState ψ η) = TensorState (ApplyGate (AddOracle fs.sum) ψ) η := by
  induction fs generalizing ψ with
  | nil => simp [lifted]
  | cons f fs ih =>
    simp only [lifted, List.map_cons, Run, applyGate_tensorGate, applyGate_one]
    rw [show Run oracle (fs.map (fun f => Step.gate (TensorGate (AddOracle f) 1)))
        (TensorState (ApplyGate (AddOracle f) ψ) η) = _ from ih _]
    rw [← applyGate_mul, ← addOracle_add, List.sum_cons, add_comm f]

end Lift

variable {A m n : ℕ} [NeZero A]

/-- The compiled linear-code query word with Fourier preparation, known encoding gates, one
query, inverse encoding gates, and Fourier readout. -/
noncomputable def word (fs : List ((Fin m → ZMod A) → (Fin n → ZMod A))) :
    Circuit (((Fin m → ZMod A) × (Fin n → ZMod A)) × ZMod A) :=
  [Step.gate (TensorGate (TensorGate (positiveFourier A m) 1) (zmodQFTGate (N:=A))ᴴ)] ++
    lifted fs ++ [Step.query] ++ lifted (fs.map Neg.neg) ++
    [Step.gate (TensorGate (TensorGate (positiveFourier A m) 1) 1)]

/-- The compiled query word has exactly one query and `2 + 2 * fs.length` explicit gates. -/
theorem word_resources (fs : List ((Fin m → ZMod A) → (Fin n → ZMod A))) :
    QueryCount (word fs) = 1 ∧ GateCount (word fs) = 2+2*fs.length := by
  simp only [word, queryCount_append, gateCount_append,
    (lifted_resources (R:=ZMod A) fs).1, (lifted_resources (R:=ZMod A) fs).2,
    (lifted_resources (R:=ZMod A) (fs.map Neg.neg)).1,
    (lifted_resources (R:=ZMod A) (fs.map Neg.neg)).2,
    List.length_map, queryCount_gate, queryCount_nil, gateCount_gate, gateCount_nil,
    queryCount_query, gateCount_query]
  constructor
  · trivial
  · omega

/-- Every explicit gate in the compiled linear-code query word is unitary. -/
theorem word_unitary (fs : List ((Fin m → ZMod A) → (Fin n → ZMod A))) :
    IsUnitaryCircuit (word fs) := by
  have hF := tensorGate_unitary (positiveFourier_unitary A m)
    (Matrix.unitaryGroup (Fin n → ZMod A) ℂ).one_mem
  have hprep := tensorGate_unitary hF
    (conjTranspose_mem_unitaryGroup (zmodQFTGate_unitary (N:=A) (NeZero.pos A)))
  have hpost := tensorGate_unitary hF (Matrix.unitaryGroup (ZMod A) ℂ).one_mem
  simp only [word, isUnitaryCircuit_append, isUnitaryCircuit_gate,
    isUnitaryCircuit_query, isUnitaryCircuit_nil, and_true]
  exact ⟨⟨⟨hprep, lifted_unitary fs⟩, lifted_unitary _⟩, hpost⟩

/-- If the known maps sum to `encode g`, the compiled word returns `Ket (response g y)`,
restores the encoding workspace to zero, and leaves the answer in `charState 1`. -/
theorem run_word (g : Fin m → Fin n → ZMod A)
    (fs : List ((Fin m → ZMod A) → (Fin n → ZMod A)))
    (hfs : fs.sum = encode g) (y : Fin n → ZMod A) :
    Run (oracle y) (word fs)
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1:ZMod A))) =
    TensorState (TensorState (Ket (response g y)) (Ket 0)) (charState (1:ZMod A)) := by
  have hn : (fs.map Neg.neg).sum = -encode g := by
    have hs : ∀ l : List ((Fin m → ZMod A) → (Fin n → ZMod A)),
        (l.map Neg.neg).sum = -l.sum := by
      intro l
      induction l with
      | nil => simp
      | cons f l ih => simp [ih, add_comm]
    rw [hs, hfs]
  have hη : charState (1:ZMod A) = (fun b : ZMod A =>
      (Real.sqrt (A:ℝ):ℂ)⁻¹ * ZMod.stdAddChar b) := by
    funext b
    rw [charState_apply, one_mul]
  have hk := ActualQuery.one_query_character_kickback
    (fun p : (Fin m → ZMod A) × (Fin n → ZMod A) => answer y p.2)
    (ZMod.stdAddChar (N:=A)) (Real.sqrt (A:ℝ):ℂ)⁻¹
    (ApplyGate (AddOracle (encode g)) (TensorState (Uniform (Fin m → ZMod A)) (Ket 0)))
  rw [← hη] at hk
  have hclean := ActualQuery.encodedQueryWord_clean (encode g) (answer y)
    (ZMod.stdAddChar (N:=A)) (Real.sqrt (A:ℝ):ℂ)⁻¹ (Uniform (Fin m → ZMod A))
  rw [← hη] at hclean
  simp only [ActualQuery.encodedQueryWord, Run, applyGate_tensorGate, applyGate_one] at hclean
  rw [show ApplyGate (AddOracle (fun p => answer y p.2))
      (TensorState (ApplyGate (AddOracle (encode g))
        (TensorState (Uniform (Fin m → ZMod A)) (Ket 0))) (charState 1)) = _ from hk] at hclean
  simp only [applyGate_tensorGate, applyGate_one] at hclean
  simp only [word, run_append, Run, applyGate_tensorGate,
    applyGate_one, positiveFourier_zero, prepare_answer]
  rw [run_lifted, hfs]
  change ApplyGate (TensorGate (TensorGate (positiveFourier A m) 1) 1)
    (Run (oracle y) (lifted (fs.map Neg.neg))
      (ApplyGate (oracle y) (TensorState (ApplyGate (AddOracle (encode g))
        (TensorState (Uniform (Fin m → ZMod A)) (Ket 0))) (charState 1)))) = _
  rw [show ApplyGate (oracle y)
      (TensorState (ApplyGate (AddOracle (encode g))
        (TensorState (Uniform (Fin m → ZMod A)) (Ket 0))) (charState 1)) = _ from hk]
  rw [run_lifted, hn, hclean]
  have hp : (fun s : Fin m → ZMod A => ZMod.stdAddChar (-answer y (encode g s)) *
      Uniform (Fin m → ZMod A) s) =
      Qatlib.Concepts.WalkFind.UniformThree.characterState
        (-FourierReadout.dotCharacter (response g y)) := by
    funext s
    simp only [answer_encode, Qatlib.Concepts.WalkFind.UniformThree.characterState,
      AddChar.neg_apply, FourierReadout.dotCharacter, AddChar.compAddMonoidHom_apply,
      AddChar.map_neg_eq_conj, Uniform,
      Qatlib.Concepts.WalshMoment.Forrelation.fourierScale]
    ring
  rw [hp]
  simp only [applyGate_tensorGate, applyGate_one, positiveFourier_response]

end Qatlib.Papers.SingleQuery97.MainResults.CompiledProgram
