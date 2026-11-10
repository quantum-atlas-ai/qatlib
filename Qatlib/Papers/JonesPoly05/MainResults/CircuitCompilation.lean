/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly05.MainResults.KauffmanStateSum
import Mathlib.Data.Matrix.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.JonesPoly05.MainResults.CircuitCompilation

open Qatlib.Papers.JonesPoly05.MainResults.Kauffman

abbrev GateWord (N : ℕ) := List (Matrix (Fin N) (Fin N) ℂ)

def wordMatrix {N : ℕ} (w : GateWord N) : Matrix (Fin N) (Fin N) ℂ :=
  w.prod

theorem wordMatrix_append {N : ℕ} (u v : GateWord N) :
    wordMatrix (u ++ v) = wordMatrix u * wordMatrix v := by
  simp [wordMatrix, List.prod_append]

def braidOperator
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {n : ℕ} (B : BraidWord n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (B.map fun g => φ n g.idx).prod

def LocalCompiles
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (c n k : ℕ) : Prop :=
  ∀ i : Fin (n - 1), ∃ w : GateWord (2 ^ n),
    wordMatrix w = φ n i ∧ w.length ≤ c * (n + k + 1) ^ c

theorem corollary31_braid_circuit
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {n : ℕ} (c k : ℕ) (B : BraidWord n) (h32 : LocalCompiles φ c n k) :
    ∃ Q : GateWord (2 ^ n),
      wordMatrix Q = braidOperator φ B ∧ Q.length ≤ B.length * c * (n + k + 1) ^ c := by
  induction B with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [wordMatrix, braidOperator]
      · simp
  | cons g t ih =>
      obtain ⟨w, hw, hlen⟩ := h32 g.idx
      obtain ⟨Q, hQ, hQlen⟩ := ih
      refine ⟨w ++ Q, ?_, ?_⟩
      · rw [wordMatrix_append, hw, hQ]
        simp [braidOperator]
      · rw [List.length_append]
        simp only [List.length_cons]
        nlinarith

theorem polyBounded_mul_pow (c : ℕ) :
    ∃ C : ℕ, ∀ m n k : ℕ, m * c * (n + k + 1) ^ c ≤
      C * (m + n + k + 1) ^ C := by
  refine ⟨c + 2, fun m n k => ?_⟩
  set X : ℕ := m + n + k + 1 with hX
  have hm : m ≤ X := by
    rw [hX]
    calc m ≤ m + n := Nat.le_add_right m n
      _ ≤ (m + n) + k := Nat.le_add_right (m + n) k
      _ ≤ ((m + n) + k) + 1 := Nat.le_add_right ((m + n) + k) 1
  have hy : n + k + 1 ≤ X := by simp [hX]
  have hc : c ≤ c + 2 := Nat.le_add_right c 2
  have hp : (n + k + 1) ^ c ≤ X ^ c := Nat.pow_le_pow_left hy c
  have hX1 : 1 ≤ X := by simp [hX]
  calc m * c * (n + k + 1) ^ c
      ≤ X * (c + 2) * X ^ c := by
        gcongr
    _ = (c + 2) * (X * X ^ c) := by ring
    _ = (c + 2) * X ^ (c + 1) := by rw [pow_succ']
    _ ≤ (c + 2) * X ^ (c + 2) := by
        have hexp : X ^ (c + 1) ≤ X ^ (c + 2) :=
          Nat.pow_le_pow_right hX1 (Nat.le_succ (c + 1))
        exact Nat.mul_le_mul_left (c + 2) hexp

theorem corollary31_polynomial_circuit
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {n : ℕ} (c k : ℕ) (B : BraidWord n) (h32 : LocalCompiles φ c n k) :
    ∃ C : ℕ, ∃ Q : GateWord (2 ^ n),
      wordMatrix Q = braidOperator φ B ∧
        Q.length ≤ C * (B.length + n + k + 1) ^ C := by
  obtain ⟨Q, hQ, hlen⟩ := corollary31_braid_circuit φ c k B h32
  obtain ⟨C, hC⟩ := polyBounded_mul_pow c
  exact ⟨C, Q, hQ, le_trans hlen (hC B.length n k)⟩

end Qatlib.Papers.JonesPoly05.MainResults.CircuitCompilation
