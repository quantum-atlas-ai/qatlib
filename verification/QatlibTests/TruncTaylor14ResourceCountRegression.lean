/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TruncTaylor14.ResourceCount.ResourceCount

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.TruncTaylor14ResourceCountRegression

open Qatlib.Papers.TruncTaylor14.ResourceCount
open Qatlib.Concepts.CoherentSim.FactorialTaylor

-- Eq. (22) exact width at concrete parameters: ancillaBits 4 5 = 4 + 4·⌈log₂5⌉ = 16 ≤ 24.
example : ancillaBits 4 5 ≤ 2 * 4 * Nat.clog 2 5 :=
  ancBits_le 4 5 (by norm_num)

-- The bound genuinely needs `L ≥ 2`: at `L = 1` the right side collapses to 0.
example : ¬(ancillaBits 1 1 ≤ 2 * 1 * Nat.clog 2 1) := by
  rw [Nat.clog_one_right]
  simp only [ancillaBits]
  omega

-- Injectivity of the unary encoding applies at a fixed register size.
example (a b : Fin (5 + 1)) (h : unaryReg 5 a = unaryReg 5 b) : a = b :=
  unaryReg_inj 5 h

-- Distinct indices at `K = 3` really get distinct unary code words.
example :
    unaryReg 3 (⟨2, by omega⟩ : Fin (3 + 1)) ≠ unaryReg 3 (⟨3, by omega⟩ : Fin (3 + 1)) := by
  intro h
  have h1 := congrFun h (⟨2, by omega⟩ : Fin 3)
  simp only [unaryReg] at h1
  norm_num at h1

-- Each cascade step lands in the unitary group at a concrete angle.
example : cascM 1 (Real.pi / 4) ⟨0, by omega⟩ ∈
    Matrix.unitaryGroup (Fin (1 + 1)) ℂ :=
  cascM_uni 1 (Real.pi / 4) ⟨0, by omega⟩

-- Eq. (22) rate: witnesses instantiated with `s = 1` and `k = m₀`
-- (then `m₀ ≤ 2·(m₀ + 8) = factorialTaylorPrecision 1 m₀`).
example (L : ℕ) (hL : 2 ≤ L) : ∃ (c : ℝ) (k : ℕ),
    (ancillaBits (factorialTaylorCutoff (factorialTaylorPrecision 1 k)) L : ℝ) ≤
      c * (Nat.clog 2 L : ℝ) *
        ((factorialTaylorPrecision 1 k : ℝ) /
          (Nat.log 2 (factorialTaylorPrecision 1 k) : ℝ)) := by
  obtain ⟨C, m₀, -, -, h⟩ := eq22_ancilla_rate
  refine ⟨(C : ℝ), m₀, h L 1 m₀ hL ?_⟩
  simp only [factorialTaylorPrecision, Nat.clog_one_right, Nat.max_self]
  omega

-- Eq. (23) rate instantiated the same way, at `L = 3`.
example : ∃ (c : ℝ) (k : ℕ),
    (prepGates (factorialTaylorCutoff (factorialTaylorPrecision 1 k)) 3 : ℝ) ≤
      c * (3 : ℝ) *
        ((factorialTaylorPrecision 1 k : ℝ) /
          (Nat.log 2 (factorialTaylorPrecision 1 k) : ℝ)) := by
  obtain ⟨C, m₀, -, -, h⟩ := eq23_prep_rate
  refine ⟨(C : ℝ), m₀, h 3 1 m₀ (by norm_num) ?_⟩
  simp only [factorialTaylorPrecision, Nat.clog_one_right, Nat.max_self]
  omega

-- Eq. (24) rate instantiated the same way, at `L = 5`, `n = 4`.
example : ∃ (c : ℝ) (k : ℕ),
    (selectVGates (factorialTaylorCutoff (factorialTaylorPrecision 1 k)) 5 4 : ℝ) ≤
      c * ((5 : ℝ) * ((4 : ℝ) + (Nat.clog 2 (max 1 5) : ℝ))) *
        ((factorialTaylorPrecision 1 k : ℝ) /
          (Nat.log 2 (factorialTaylorPrecision 1 k) : ℝ)) := by
  obtain ⟨C, m₀, -, -, h⟩ := eq24_select_rate
  refine ⟨(C : ℝ), m₀, h 5 4 1 m₀ ?_⟩
  · simp only [factorialTaylorPrecision, Nat.clog_one_right, Nat.max_self]
    omega

-- Eq. (25) rate instantiated the same way, at `n = 2`.
example : ∃ (c : ℝ) (k : ℕ),
    (sparseSegGates (factorialTaylorCutoff (factorialTaylorPrecision 1 k)) 2
        (factorialTaylorPrecision 1 k) : ℝ) ≤
      c * (2 : ℝ) *
        ((factorialTaylorPrecision 1 k : ℝ) ^ (2 : ℕ) /
          (Nat.log 2 (factorialTaylorPrecision 1 k) : ℝ)) := by
  obtain ⟨C, m₀, -, -, h⟩ := eq25_sparse_rate
  refine ⟨(C : ℝ), m₀, h 2 1 m₀ (by norm_num) ?_⟩
  simp only [factorialTaylorPrecision, Nat.clog_one_right, Nat.max_self]
  omega

-- Pauli tensor words are unitary at a concrete word `X ⊗ Z` on two qubits.
example : pauliWord 2 (fun i => if i = 0 then 1 else 3) *
    Matrix.conjTranspose (pauliWord 2 (fun i => if i = 0 then 1 else 3)) = 1 :=
  pauliWord_unitary 2 _

-- The block-diagonal Pauli select is unitary at `L = 2`, `n = 1`.
example : pauliSelect 2 1 (fun q _ => if q = 0 then 1 else 3) *
    Matrix.conjTranspose (pauliSelect 2 1 (fun q _ => if q = 0 then 1 else 3)) = 1 :=
  pauliSelect_unitary 2 1 _

end QatlibTests.TruncTaylor14ResourceCountRegression
