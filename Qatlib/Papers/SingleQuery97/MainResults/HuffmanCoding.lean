/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.CharacterSum
import Qatlib.Papers.SingleQuery97.MainResults.WalshSearch

/-!
# Binary code states and Huffman collision criteria

This module associates binary codewords with phase states and characterizes their inner
products, projections, and ambiguity through codeword equality. It also defines the proposed
Huffman quantum and classical time expressions from [TerhalSmolin1998] and compares the quantum
expression with its Walsh counterpart.

## Main statements

* `huffman_ambiguity_iff_collision`: An input has a distinct input with nonorthogonal code state
  exactly when its codeword collides.
* `proposedHuffmanTime_le_walsh`: If the Huffman code length is at most the Walsh length, its
  proposed quantum time is at most the proposed Walsh quantum time.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

namespace Qatlib.Papers.SingleQuery97.MainResults.HuffmanCoding

open Qatlib.Papers.SingleQuery97.MainResults.CharacterSum
open Qatlib.Papers.SingleQuery97.MainResults.WalshSearch

variable {ι : Type*}

/-- The normalized binary phase-state amplitude associated with the codeword of `y`. -/
noncomputable def codeState {m : ℕ} (code : ι → Fin m → ZMod 2) (y : ι) :
    (Fin m → ZMod 2) → ℂ :=
  stateAmp (A := 2) (m := m) (code y)

/-- The inner product of two binary code states is `1` when their codewords coincide and `0`
otherwise. -/
theorem huffmanStates_orthonormal {m : ℕ} (code : ι → Fin m → ZMod 2)
    (y y' : ι) :
    inner (codeState code y) (codeState code y') =
      if code y = code y' then 1 else 0 :=
  inner_stateAmp (A := 2) (m := m) (by norm_num) (code y) (code y')

/-- Two binary code states have nonzero inner product exactly when their codewords coincide. -/
theorem huffman_nonorthogonal_iff_code_equal {m : ℕ} (code : ι → Fin m → ZMod 2) (y y' : ι) :
    inner (codeState code y) (codeState code y') ≠ 0 ↔ code y = code y' := by
  rw [huffmanStates_orthonormal]
  by_cases h : code y = code y' <;> simp [h]

/-- Projecting one binary code state onto another retains the state for equal codewords and
yields zero otherwise. -/
theorem huffmanMeasurement {m : ℕ} (code : ι → Fin m → ZMod 2) (y y' : ι) :
    proj (codeState code y) (codeState code y') =
      if code y = code y' then codeState code y' else 0 := by
  unfold proj
  rw [show inner (codeState code y) (codeState code y') =
      if code y = code y' then (1 : ℂ) else 0 from huffmanStates_orthonormal code y y']
  by_cases h : code y = code y'
  · rw [if_pos h, if_pos h]
    funext x
    simp [codeState, h]
  · rw [if_neg h, if_neg h]
    funext x
    simp

/-- The property that another input has the same binary codeword as `y`. -/
def Collision {m : ℕ} (code : ι → Fin m → ZMod 2) (y : ι) : Prop :=
  ∃ y' : ι, y' ≠ y ∧ code y' = code y

/-- An input has a distinct input with nonorthogonal code state exactly when its codeword
collides. -/
theorem huffman_ambiguity_iff_collision {m : ℕ} (code : ι → Fin m → ZMod 2) (y : ι) :
    (∃ y' : ι, y' ≠ y ∧ inner (codeState code y) (codeState code y') ≠ 0) ↔
      Collision code y := by
  unfold Collision
  constructor
  · rintro ⟨y', hyne, hinner⟩
    exact ⟨y', hyne, ((huffman_nonorthogonal_iff_code_equal code y y').mp hinner).symm⟩
  · rintro ⟨y', hyne, hcode⟩
    exact ⟨y', hyne, (huffman_nonorthogonal_iff_code_equal code y y').mpr hcode.symm⟩

/-- The proposed Huffman quantum time expression `2 + m * n + T`. -/
def proposedHuffmanQuantumTime (n m T : ℕ) : ℕ := 2 + m * n + T

/-- The proposed Huffman classical time expression `m / 2 + m * T`, with natural-number
division. -/
def proposedHuffmanClassicalTime (m T : ℕ) : ℕ := m / 2 + m * T

/-- If the Huffman code length is at most the Walsh length, its proposed quantum time is at most
the proposed Walsh quantum time. -/
theorem proposedHuffmanTime_le_walsh {n m k T : ℕ} (hm : m ≤ k) :
    proposedHuffmanQuantumTime n m T ≤ proposedWalshQuantumTime n k T := by
  unfold proposedHuffmanQuantumTime proposedWalshQuantumTime
  have h : m * n ≤ n * k := by
    simpa [mul_comm] using Nat.mul_le_mul_right n hm
  omega

end Qatlib.Papers.SingleQuery97.MainResults.HuffmanCoding
