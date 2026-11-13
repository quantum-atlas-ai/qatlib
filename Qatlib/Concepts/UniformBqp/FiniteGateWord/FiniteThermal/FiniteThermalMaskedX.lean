/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalMultiX

/-!
# Masked controls for finite controlled-X words

This module forms `thermalMaskedX` by conjugating a positive-control word with X gates on
controls required to be false. It establishes basis and coherent semantics for the mask
predicate `thermalMatch`, together with legality and exact cost, using the elementary
controlled-gate framework of [BarencoEtAl1995].

## Main statements

* `thermalMaskedX_basis`: the target is toggled exactly when the prescribed positive and
  negative controls match.
* `thermalMaskedX_coherent`: extends the basis action to states supported on clean workspace.
* `thermalMaskedX_cost`: accounts for the controlled word and both X masks.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

/-- The list of X gate codes on the wires in `ms`, in list order. -/
def thermalXMask {n : ℕ} (ms : List (Fin n)) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  ms.map (fun w => .x w.val)

/-- The basis label obtained by successively negating the bits on the listed wires, including
repeated flips when a wire occurs more than once. -/
def thermalFlipBasis {n : ℕ} : List (Fin n) → Qatlib.Foundations.PureStateMath.Reg n → Qatlib.Foundations.PureStateMath.Reg n
  | [],x => x
  | a::ms,x => thermalFlipBasis ms (Function.update x a (!x a))

/-- Running the one-gate X word on `Ket x` negates bit `t` and leaves all other bits unchanged. -/
private theorem flip_run {n : ℕ} (t : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.x t.val])
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (!x t)) := by
  have h := thermalMultiX_basis ([] : List (Fin n)) t [] (by simp) (by simp) x (by simp)
  simpa [thermalMultiX,thermalControl] using h

/-- Running an X mask on a basis state produces the basis state labeled by `thermalFlipBasis ms
x`. -/
theorem thermalXMask_basis {n : ℕ} (ms : List (Fin n)) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalXMask ms))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (thermalFlipBasis ms x) := by
  induction ms generalizing x with
  | nil => rfl
  | cons a ms ih =>
    have he : thermalXMask (a::ms) = [.x a.val] ++ thermalXMask ms := rfl
    rw [he,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
    change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalXMask ms))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.x a.val]) (Qatlib.Foundations.PureStateMath.Ket x)) = _
    rw [flip_run a x,ih]
    rfl

/-- For a list of distinct wires, `thermalFlipBasis` negates exactly the coordinates belonging
to the list. -/
theorem thermalFlipBasis_apply {n : ℕ} (ms : List (Fin n)) (hn : ms.Nodup)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (u : Fin n) :
    thermalFlipBasis ms x u = if u∈ms then !x u else x u := by
  induction ms generalizing x with
  | nil => simp [thermalFlipBasis]
  | cons a ms ih =>
    have ha : a∉ms := (List.nodup_cons.mp hn).1
    rw [thermalFlipBasis,ih hn.tail]
    by_cases hua : u=a
    · subst u
      simp [ha]
    · simp [hua]

/-- The adjoint finite word of an X mask is the X mask with the wire list reversed. -/
theorem thermalXMask_adjoint {n : ℕ} (ms : List (Fin n)) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalXMask ms) = thermalXMask ms.reverse := by
  simp [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint,thermalXMask,List.map_reverse,List.map_map,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeAdjoint]

/-- The word consisting of an X mask on `zeros`, the positive-control word `thermalMultiX`, and
the adjoint X mask. -/
def thermalMaskedX {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n) (ws : List (Fin n)) :=
  thermalXMask zeros ++ thermalMultiX cs t ws ++ Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalXMask zeros)

/-- The conjunction requiring each control bit to be false when its wire belongs to `zeros` and
true otherwise. -/
def thermalMatch {n : ℕ} (cs zeros : List (Fin n)) (x : Qatlib.Foundations.PureStateMath.Reg n) : Bool :=
  cs.all (fun c => if c∈zeros then !x c else x c)

/-- For distinct control, target, and workspace wires, a distinct zero-mask contained in the
controls, and sufficient workspace initialized to false, the masked word toggles only `t` by
`thermalMatch cs zeros x`. -/
theorem thermalMaskedX_basis {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hn : (cs ++ t::ws).Nodup) (hz : zeros.Nodup)
    (hsub : ∀ w∈zeros,w∈cs) (hlen : cs.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs zeros t ws))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ thermalMatch cs zeros x)) := by
  have hzt : t∉zeros := by
    intro ht
    exact (List.disjoint_left.mp hn.disjoint) (hsub t ht) (by simp)
  have hwz (w : Fin n) (hw : w∈ws) : w∉zeros := by
    intro hzw
    exact (List.disjoint_left.mp hn.disjoint) (hsub w hzw) (by simp [hw])
  let y := thermalFlipBasis zeros x
  have hyc : ∀ w∈ws,y w=false := by
    intro w hw
    simp only [y,thermalFlipBasis_apply zeros hz,if_neg (hwz w hw),hc w hw]
  have hyt : y t=x t := by simp only [y,thermalFlipBasis_apply zeros hz,if_neg hzt]
  have hcy : thermalControl cs y=thermalMatch cs zeros x := by
    unfold thermalControl thermalMatch
    exact List.all_congr rfl (fun c => thermalFlipBasis_apply zeros hz x c)
  have hb := thermalMultiX_basis cs t ws hn hlen y hyc
  rw [hcy,hyt] at hb
  let z := Function.update y t (x t ^^ thermalMatch cs zeros x)
  have hrestore : thermalFlipBasis zeros.reverse z =
      Function.update x t (x t ^^ thermalMatch cs zeros x) := by
    funext u
    rw [thermalFlipBasis_apply zeros.reverse (List.nodup_reverse.mpr hz)]
    simp only [List.mem_reverse]
    by_cases hut : u=t
    · subst u
      simp [z,hzt]
    · simp only [z,Function.update_of_ne hut,y,thermalFlipBasis_apply zeros hz]
      by_cases huz : u∈zeros <;> simp [huz]
  simp only [thermalMaskedX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalXMask zeros)))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMultiX cs t ws))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalXMask zeros)) (Qatlib.Foundations.PureStateMath.Ket x))) = _
  rw [thermalXMask_basis,hb,thermalXMask_adjoint,thermalXMask_basis,hrestore]

/-- Every X mask on wires of type `Fin n` is a legal finite word on `n` wires. -/
theorem thermalXMask_legal {n : ℕ} (ms : List (Fin n)) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalXMask ms)=true := by
  simp only [thermalXMask,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_map]
  apply List.all_eq_true.mpr
  intro w _
  simp [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,w.isLt]

/-- The masked word is legal when the control, target, and workspace wires are distinct and
`cs.length ≤ ws.length + 2`. -/
theorem thermalMaskedX_legal {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hn : (cs ++ t::ws).Nodup) (hlen : cs.length ≤ ws.length+2) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalMaskedX cs zeros t ws)=true := by
  have hm := thermalMultiX_legal cs t ws hn hlen
  have hl := thermalXMask_legal zeros
  have hr : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalXMask zeros))=true := by
    rw [thermalXMask_adjoint]
    exact thermalXMask_legal zeros.reverse
  simpa only [thermalMaskedX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append,Bool.and_eq_true]
    using And.intro (And.intro hl hm) hr

/-- With sufficient workspace, the masked word has zero queries and gate count `2 * zeros.length
+ (if cs.length ≤ 1 then 1 else 15 * (2 * cs.length - 3))`. -/
theorem thermalMaskedX_cost {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hlen : cs.length ≤ ws.length+2) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs zeros t ws)) =
      2*zeros.length+(if cs.length ≤ 1 then 1 else 15*(2*cs.length-3)) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs zeros t ws))=0 := by
  refine ⟨?_,(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1⟩
  have hm := (thermalMultiX_cost cs t ws hlen).1
  rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2] at hm ⊢
  simp only [thermalMaskedX,List.length_append,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint,List.length_map,
    List.length_reverse,thermalXMask] at ⊢
  rw [hm]
  omega

/-- For distinct control, target, and workspace wires, a distinct zero-mask contained in the
controls, and sufficient workspace, the masked word toggles `t` by `thermalMatch` in each
basis component of a state supported on false workspace. -/
theorem thermalMaskedX_coherent {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hn : (cs ++ t::ws).Nodup) (hz : zeros.Nodup)
    (hsub : ∀ w∈zeros,w∈cs) (hlen : cs.length ≤ ws.length+2) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n))
    (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬∀ w∈ws,x w=false) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs zeros t ws)) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket
        (Function.update x t (x t ^^ thermalMatch cs zeros x)) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hcx : ∀ w∈ws,x w=false
  · have hb := thermalMaskedX_basis cs zeros t ws hn hz hsub hlen x hcx
    rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
    exact congrArg (fun v => psi x • v) hb
  · simp only [hc x hcx,zero_smul]

/-- Under the distinct-wire, zero-mask, workspace-size, and false-workspace hypotheses,
`finiteWordRun` returns the basis state with only `t` XORed by `thermalMatch cs zeros x`. -/
theorem thermalMaskedX_public {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hn : (cs ++ t::ws).Nodup) (hz : zeros.Nodup)
    (hsub : ∀ w∈zeros,w∈cs) (hlen : cs.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun n (thermalMaskedX cs zeros t ws) (Qatlib.Foundations.PureStateMath.Ket x) =
      some (Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ thermalMatch cs zeros x))) := by
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun,thermalMaskedX_legal cs zeros t ws hn hlen,if_true]
  rw [thermalMaskedX_basis cs zeros t ws hn hz hsub hlen x hc]

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
