/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound.Lemma5Budget

@[expose] public section

/-!
# Clean-input instantiation of the source error bound

Fixed source: [Kitaev 1995, Abelian Stabilizer Problem](https://arxiv.org/abs/quant-ph/9511026),
Lemma 5 (printed p. 12).  A mixed word consisting of a single wire-swap instruction computes
the wire-swap function on two qubits exactly.  The source form of Lemma 5 — target error plus
twice the word length times the per-step precision — is instantiated on the concrete
correctness event with a legal clean basis input.  A uniform constant `2` is placed outside
all quantifiers. The numerical gate model implements this permutation exactly at every
precision, so the example instantiates the correctness event and input of the bound.

## Main statements

* `lemma5_swap_source_form`: if the ideal word answers the correctness event with probability
  within `ε` of certainty, the implemented word does so with probability within
  `ε + 2 * L * δ` for word length `L = 1`.
* `swapTwoWord_ideal_correct`: the ideal single-swap word is correct with certainty.

## References

* [Kitaev1995], Lemma 5
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma5CleanInput

open scoped Matrix.Norms.L2Operator

open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound

/-- The wire-swap instruction on the two qubits of a two-bit register. -/
def swapTwo : LocalQFTGate 2 := .swap 0 1

/-- The register map swapping the two wires of a two-bit register. -/
def swapTwoFun (x : Reg 2) : Reg 2 := fun i => x (Equiv.swap (0 : Fin 2) 1 i)

/-- The single-gate mixed word implementing `swapTwo` at precision `m`. -/
def swapTwoWord (m : ℕ) : List (MixedStep 2 2 Unit) := [.known swapTwo m]

/-- The single-swap word has vacuously valid controls. -/
theorem validControls_swapTwoWord (m : ℕ) : ValidControls (swapTwoWord m) := by
  intro s hs
  rcases List.mem_singleton.mp hs with rfl
  exact True.intro

/-- The single-swap word is legal for any paid list: it makes no oracle calls. -/
theorem swapTwoWord_legal (m : ℕ) (paid : List (AccessForm Unit)) :
    mixedWordLegal (swapTwoWord m) paid := by
  intro s hs
  rcases List.mem_singleton.mp hs with rfl
  exact True.intro

/-- The precision labels of the single-swap word are the singleton `[m]`. -/
theorem knownPrecs_swapTwoWord (m : ℕ) : knownPrecs (swapTwoWord m) = [m] := by
  simp [swapTwoWord, knownPrecs]

/-- The trivial oracle model answering every slot with the identity matrix. -/
noncomputable def unitOracle : Unit → Matrix (Reg 2) (Reg 2) ℂ := fun _ => 1

/-- Every value of the trivial oracle model is unitary. -/
theorem unitOracle_unitary (s : Unit) : unitOracle s ∈ Matrix.unitaryGroup (Reg 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp [unitOracle]

/-- The exact gate matrix of `swapTwo` is the permutation matrix of `swapTwoFun`. -/
theorem localGateMatrix_swapTwo :
    localGateMatrix swapTwo = permMatrix swapTwoFun := rfl

/-- `swapTwoFun` is an involution. -/
theorem swapTwoFun_involutive : Function.Involutive swapTwoFun := by
  intro x
  funext i
  show x (Equiv.swap (0 : Fin 2) 1 (Equiv.swap (0 : Fin 2) 1 i)) = x i
  rw [Equiv.swap_apply_self]

/-- The ideal (exact-gate) single-swap word applies the wire swap to every basis state. -/
theorem swapTwoWord_ideal_apply (m : ℕ) (x : Reg 2) :
    ApplyGate (mixedWordMatrix (le_refl 2) unitOracle (swapTwoWord m)) (Ket x)
      = Ket (swapTwoFun x) := by
  simp only [mixedWordMatrix, swapTwoWord, List.map_cons, List.map_nil, List.reverse_singleton,
    List.prod_singleton]
  rw [show mixedStepMatrix (le_refl 2) unitOracle (.known swapTwo m) = localGateMatrix swapTwo
    from rfl, localGateMatrix_swapTwo]
  exact applyGate_permMatrix_ket swapTwoFun_involutive x

/-- The ideal single-swap word outputs the swapped register with certainty: the correctness
event `{swapTwoFun x}` has Born probability one on the clean basis input `Ket x`. -/
theorem swapTwoWord_ideal_correct (m : ℕ) (x : Reg 2) :
    MeasureProb (ApplyGate (mixedWordMatrix (le_refl 2) unitOracle (swapTwoWord m)) (Ket x))
      {swapTwoFun x} = 1 := by
  rw [swapTwoWord_ideal_apply m x]
  simp [MeasureProb, bornProb_ket]

/-- The source form of [Kitaev1995], Lemma 5, on a concrete legal instance: the
single-swap mixed word computes the wire-swap function on two qubits.  If the ideal
exact-gate word answers the correctness event with probability within `ε` of certainty, then
the implemented numerical word does so with probability within `ε + 2 * L * δ` for the uniform
constant `2` and the word length `L`.  The input is the clean normalized basis state `Ket x`
on the two-qubit register, so the domain is non-degenerate. -/
theorem lemma5_swap_source_form :
    ∃ uniformConstant : ℝ, 0 < uniformConstant ∧
      ∀ (m : ℕ) (δ ε : ℝ), 0 ≤ δ → ((2 : ℝ)⁻¹) ^ m ≤ δ → 0 ≤ ε →
        ∀ (x : Reg 2),
          |MeasureProb (ApplyGate (mixedWordMatrix (le_refl 2) unitOracle (swapTwoWord m))
              (Ket x)) {swapTwoFun x} - 1| ≤ ε →
          |MeasureProb (ApplyGate (word (le_refl 2) unitOracle (swapTwoWord m)) (Ket x))
              {swapTwoFun x} - 1| ≤
            ε + uniformConstant * ((swapTwoWord m).length : ℝ) * δ := by
  refine ⟨2, by norm_num, fun m δ ε hδ0 hδ _ x hideal => ?_⟩
  have hδ' : ∀ m' ∈ knownPrecs (swapTwoWord m), ((2 : ℝ)⁻¹) ^ m' ≤ δ := by
    intro m' hm'
    rw [knownPrecs_swapTwoWord m] at hm'
    rcases List.mem_singleton.mp hm' with rfl
    exact hδ
  have hbridge := lemma5_mixedWord_uniform (le_refl 2) Unit unitOracle (swapTwoWord m) []
    (validControls_swapTwoWord m) (swapTwoWord_legal m []) unitOracle_unitary δ hδ0 hδ'
    (Ket x) {swapTwoFun x} (normalized_ket x)
  let A := MeasureProb (ApplyGate (word (le_refl 2) unitOracle (swapTwoWord m)) (Ket x))
    {swapTwoFun x}
  let B := MeasureProb
    (ApplyGate (mixedWordMatrix (le_refl 2) unitOracle (swapTwoWord m)) (Ket x)) {swapTwoFun x}
  calc |A - 1| = |(A - B) + (B - 1)| := by rw [sub_add_sub_cancel]
    _ ≤ |A - B| + |B - 1| := abs_add_le _ _
    _ ≤ 2 * ((swapTwoWord m).length : ℝ) * δ + ε := add_le_add hbridge hideal
    _ = ε + 2 * ((swapTwoWord m).length : ℝ) * δ := by ring

end Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma5CleanInput
