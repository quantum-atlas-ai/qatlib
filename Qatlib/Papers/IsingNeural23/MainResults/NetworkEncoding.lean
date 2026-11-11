/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BinaryOptEncode.ExactGadgets.LocalGadgets

/-!
# Integer sign-network constraint encoding

This module defines integer affine layers `affineLayer`, sign-activated layers `evaluateLayer`,
and the recursive evaluation `networkValue`. The nonnegative slack constraints from
[SongEtAl2023] characterize each sign layer and uniquely determine every encoded activation up
to a prescribed depth.

## Main statements

* `layer_constraints_iff`: characterizes layer evaluation by the slack constraints.
* `network_constraints_witness`: provides slack witnesses for evaluated networks.
* `encoded_network_unique`: proves uniqueness of activations satisfying the encoding.

## References

* [Song et al., 2023][SongEtAl2023]
-/

set_option autoImplicit false
namespace Qatlib.Papers.IsingNeural23.MainResults
open Qatlib.Concepts.BinaryOptEncode.ExactGadgets
open scoped BigOperators

/-- The integer affine layer obtained by multiplying the input by `W` and adding `bias`. -/
def affineLayer {I O : Type*} [Fintype I] (W : Matrix O I ℤ) (bias : O → ℤ)
    (input : I → ℤ) : O → ℤ := fun j => (∑ i, W j i * input i) + bias j

/-- The layer obtained by applying `signPlus` to each integer affine preactivation. -/
def evaluateLayer {I O : Type*} [Fintype I] (W : Matrix O I ℤ) (bias : O → ℤ)
    (input : I → ℤ) : O → ℤ := fun j => signPlus (affineLayer W bias input j)

/-- Every output of `evaluateLayer` equals either `1` or `-1`. -/
theorem evaluateLayer_binary {I O : Type*} [Fintype I] (W : Matrix O I ℤ)
    (bias : O → ℤ) (input : I → ℤ) (j : O) :
    evaluateLayer W bias input j = 1 ∨ evaluateLayer W bias input j = -1 := by
  simp only [evaluateLayer, signPlus]
  split_ifs <;> simp

/-- For outputs restricted to `1` and `-1`, the nonnegative integer slack constraints hold
exactly when the output equals `evaluateLayer W bias input`. -/
theorem layer_constraints_iff {I O : Type*} [Fintype I]
    (W : Matrix O I ℤ) (bias : O → ℤ) (input : I → ℤ) (output : O → ℤ)
    (hout : ∀ j, output j = 1 ∨ output j = -1) :
    (∀ j, ∃ r t : ℤ, 0 ≤ r ∧ 0 ≤ t ∧
      output j * affineLayer W bias input j = r ∧ output j + 2 * r = 1 + t) ↔
      output = evaluateLayer W bias input := by
  constructor
  · intro h
    funext j
    exact (sign_constraints_iff _ _ (hout j)).mp (h j)
  · intro h j
    apply (sign_constraints_iff _ _ (hout j)).mpr
    exact congrFun h j

/-- The recursive evaluation of the network, starting at `input` and applying one sign-activated
affine layer at each step. -/
def networkValue (width : ℕ → ℕ)
    (weights : ∀ l, Matrix (Fin (width (l + 1))) (Fin (width l)) ℤ)
    (bias : ∀ l, Fin (width (l + 1)) → ℤ) (input : Fin (width 0) → ℤ) :
    (l : ℕ) → Fin (width l) → ℤ
  | 0 => input
  | l + 1 => evaluateLayer (weights l) (bias l) (networkValue width weights bias input l)

/-- Every evaluated layer possesses nonnegative integer witnesses for the sign-network slack
constraints of [SongEtAl2023]. -/
theorem network_constraints_witness (width : ℕ → ℕ)
    (weights : ∀ l, Matrix (Fin (width (l + 1))) (Fin (width l)) ℤ)
    (bias : ∀ l, Fin (width (l + 1)) → ℤ) (input : Fin (width 0) → ℤ) (l : ℕ) :
    ∀ j, ∃ r t : ℤ, 0 ≤ r ∧ 0 ≤ t ∧
      networkValue width weights bias input (l + 1) j *
        affineLayer (weights l) (bias l) (networkValue width weights bias input l) j = r ∧
      networkValue width weights bias input (l + 1) j + 2 * r = 1 + t := by
  have h := (layer_constraints_iff (weights l) (bias l)
    (networkValue width weights bias input l)
    (evaluateLayer (weights l) (bias l) (networkValue width weights bias input l))
    (evaluateLayer_binary (weights l) (bias l) (networkValue width weights bias input l))).mpr rfl
  simpa only [networkValue] using h

/-- Activations with the prescribed input, binary signs, and slack constraints agree with
`networkValue` at every layer up to `depth`. See [SongEtAl2023]. -/
theorem encoded_network_unique (width : ℕ → ℕ)
    (weights : ∀ l, Matrix (Fin (width (l + 1))) (Fin (width l)) ℤ)
    (bias : ∀ l, Fin (width (l + 1)) → ℤ) (input : Fin (width 0) → ℤ)
    (activation : ∀ l, Fin (width l) → ℤ) (depth : ℕ) (h0 : activation 0 = input)
    (hsign : ∀ l, l < depth → ∀ j, activation (l + 1) j = 1 ∨ activation (l + 1) j = -1)
    (hc : ∀ l, l < depth → ∀ j, ∃ r t : ℤ, 0 ≤ r ∧ 0 ≤ t ∧
      activation (l + 1) j * affineLayer (weights l) (bias l) (activation l) j = r ∧
        activation (l + 1) j + 2 * r = 1 + t) :
    ∀ l, l ≤ depth → activation l = networkValue width weights bias input l := by
  intro l
  induction l with
  | zero => intro _; exact h0
  | succ l ih =>
    intro hl
    have hlt : l < depth := by omega
    have hp := ih (by omega)
    have hn := (layer_constraints_iff (weights l) (bias l) (activation l)
      (activation (l + 1)) (hsign l hlt)).mp (hc l hlt)
    simpa only [hp, networkValue] using hn

/-- An activation equal to the evaluated depth-`depth` network yields the same final affine
prediction. -/
theorem encoded_prediction {O : Type*} (width : ℕ → ℕ)
    (weights : ∀ l, Matrix (Fin (width (l + 1))) (Fin (width l)) ℤ)
    (bias : ∀ l, Fin (width (l + 1)) → ℤ) (input : Fin (width 0) → ℤ)
    (depth : ℕ) (lastW : Matrix O (Fin (width depth)) ℤ) (lastB : O → ℤ)
    (activation : Fin (width depth) → ℤ) (h : activation = networkValue width weights bias input depth) :
    affineLayer lastW lastB activation =
      affineLayer lastW lastB (networkValue width weights bias input depth) := by rw [h]

end Qatlib.Papers.IsingNeural23.MainResults
