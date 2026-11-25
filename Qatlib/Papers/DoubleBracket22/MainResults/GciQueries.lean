/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DoubleBracket22.MainResults.Model.DoubleBracketModel
public import Qatlib.Foundations.QueryWordCore.HamiltonianQuery

@[expose] public section

/-!
# Executable query list for the reduced GCI transpiler

Section 1.6 of arXiv:2206.11772v4 counts evolutions under the input
Hamiltonian. Diagonal evolutions are explicit gates in this program.
The list is stored in state application order, which is the reversal
of the matrix product order in Eq. (49).
-/

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.HamiltonianQuery
open Qatlib.Papers.DoubleBracket22.MainResults.Model

namespace Qatlib.Papers.DoubleBracket22.MainResults

variable {D : ℕ}

/-- A source GCI program uses the library's Hamiltonian-query instructions. -/
abbrev GciProgram (D : ℕ) := List (HamiltonianQueryStep (Fin D))

/-- The reversed instruction for a gate or a signed Hamiltonian query. -/
def adjointGciStep : HamiltonianQueryStep (Fin D) → HamiltonianQueryStep (Fin D)
  | .gate U => .gate Uᴴ
  | .evolve t => .evolve (-t)

/-- The adjoint program reverses the order of adjointed instructions. -/
def adjointGciProgram (program : GciProgram D) : GciProgram D :=
  program.reverse.map adjointGciStep

/-- Reversing the signs and direction of a program preserves its query count. -/
theorem adjointGciProgram_queryCount (program : GciProgram D) :
    HamiltonianQueryCount (adjointGciProgram program) = HamiltonianQueryCount program := by
  induction program with
  | nil => rfl
  | cons step rest ih =>
    rw [adjointGciProgram, List.reverse_cons, List.map_append, hamiltonianQueryCount_append]
    change HamiltonianQueryCount (adjointGciProgram rest) +
      HamiltonianQueryCount [adjointGciStep step] = _
    rw [ih]
    cases step <;> simp [adjointGciStep, HamiltonianQueryCount, Nat.add_comm]

/-- Abstract Algorithm 3 with the reversal from Quantum Algorithm 4
already applied. Only the central evolution queries the input Hamiltonian. -/
def reducedGciProgram (diagonals : ℕ → Mat D) (s : ℕ → ℝ) : ℕ → GciProgram D
  | 0 => []
  | k + 1 =>
    let V := reducedGciProgram diagonals s k
    let t := Real.sqrt (s k)
    [.gate (HamiltonianEvolution (diagonals k) t)] ++ V ++ [.evolve (-t)] ++
      adjointGciProgram V ++ [.gate (HamiltonianEvolution (diagonals k) (-t))] ++ V

/-- Validity of a concatenated word is exactly validity of its two subwords. -/
private theorem queryValid_append (left right : GciProgram D) :
    HamiltonianQueryValid (left ++ right) ↔
      HamiltonianQueryValid left ∧ HamiltonianQueryValid right := by
  constructor
  · intro h
    exact ⟨fun U hU => h U (List.mem_append_left right hU),
      fun U hU => h U (List.mem_append_right left hU)⟩
  · rintro ⟨hL, hR⟩ U hU
    exact (List.mem_append.mp hU).elim (hL U) (hR U)

/-- The adjoint of a valid query program is valid. -/
private theorem adjointGciProgram_valid (program : GciProgram D)
    (h : HamiltonianQueryValid program) : HamiltonianQueryValid (adjointGciProgram program) := by
  intro U hU
  obtain ⟨step, hmem, hstep⟩ := List.mem_map.mp hU
  have hmem' : step ∈ program := List.mem_reverse.mp hmem
  cases step with
  | gate V =>
    have hEq : Vᴴ = U := HamiltonianQueryStep.gate.inj hstep
    rw [← hEq, ← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (h V hmem')
  | evolve t => cases hstep

/-- The source word's explicit gates are unitary when the diagonal
generators are Hermitian. -/
theorem reducedGciProgram_valid (diagonals : ℕ → Mat D) (s : ℕ → ℝ)
    (hdiag : ∀ k, (diagonals k).IsHermitian) (K : ℕ) :
    HamiltonianQueryValid (reducedGciProgram diagonals s K) := by
  have hgate (k : ℕ) (t : ℝ) :
      HamiltonianQueryValid [.gate (HamiltonianEvolution (diagonals k) t)] := by
    intro U hU
    have hEq : U = HamiltonianEvolution (diagonals k) t := by simpa using hU
    rw [hEq]
    exact hamiltonianEvolution_unitary (hdiag k) t
  have hevolve (t : ℝ) : HamiltonianQueryValid ([.evolve t] : GciProgram D) := by
    intro _ h
    simp at h
  induction K with
  | zero => intro _ h; simp [reducedGciProgram] at h
  | succ k ih =>
    simp only [reducedGciProgram, queryValid_append, hgate, ih, hevolve,
      adjointGciProgram_valid _ ih, and_self]

/-- Matrix of a program, composing its instructions in state application order. -/
def gciQueryMatrix (H : Mat D) : GciProgram D → Mat D
  | [] => 1
  | .gate U :: rest => gciQueryMatrix H rest * U
  | .evolve t :: rest => gciQueryMatrix H rest * HamiltonianEvolution H t

/-- The Hamiltonian-query evaluator acts by the associated matrix on every state. -/
theorem reducedGciProgram_run (H : Mat D) (program : GciProgram D) (ψ : QState (Fin D)) :
    HamiltonianQueryRun H program ψ = ApplyGate (gciQueryMatrix H program) ψ := by
  induction program generalizing ψ with
  | nil => simp [HamiltonianQueryRun, gciQueryMatrix]
  | cons step rest ih =>
    cases step <;> simp only [HamiltonianQueryRun, gciQueryMatrix, ih, applyGate_mul]

/-- Concatenation composes the right program after the left program. -/
private theorem gciQueryMatrix_append (H : Mat D) (left right : GciProgram D) :
    gciQueryMatrix H (left ++ right) = gciQueryMatrix H right * gciQueryMatrix H left := by
  induction left with
  | nil => simp [gciQueryMatrix]
  | cons step rest ih =>
    cases step <;> simp only [List.cons_append, gciQueryMatrix, ih, Matrix.mul_assoc]

/-- For a Hermitian input generator, the adjoint program denotes the adjoint matrix. -/
private theorem adjointGciProgram_matrix (H : Mat D) (hH : H.IsHermitian) (program : GciProgram D) :
    gciQueryMatrix H (adjointGciProgram program) = (gciQueryMatrix H program)ᴴ := by
  have hneg (t : ℝ) : HamiltonianEvolution H (-t) = (HamiltonianEvolution H t)ᴴ := by
    simp only [HamiltonianEvolution, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq,
      RCLike.star_def, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg,
      neg_neg, mul_neg, neg_mul]
  induction program with
  | nil => simp [adjointGciProgram, gciQueryMatrix]
  | cons step rest ih =>
    rw [adjointGciProgram, List.reverse_cons, List.map_append, gciQueryMatrix_append]
    change gciQueryMatrix H [adjointGciStep step] * gciQueryMatrix H (adjointGciProgram rest) = _
    rw [ih]
    cases step <;> simp only [adjointGciStep, gciQueryMatrix, one_mul, Matrix.conjTranspose_mul, hneg]

/-- Eq. (49): one additional program step implements the source's
frame-shifted input evolution with the diagonal gates on either side. -/
theorem eq49_reducedGci_matrix_step (H : Mat D) (hH : H.IsHermitian)
    (diagonals : ℕ → Mat D) (s : ℕ → ℝ) (k : ℕ) :
    let V := gciQueryMatrix H (reducedGciProgram diagonals s k)
    let t := Real.sqrt (s k)
    gciQueryMatrix H (reducedGciProgram diagonals s (k + 1)) =
      V * HamiltonianEvolution (diagonals k) (-t) * Vᴴ *
        HamiltonianEvolution H (-t) * V * HamiltonianEvolution (diagonals k) t := by
  simp only [reducedGciProgram, gciQueryMatrix_append, adjointGciProgram_matrix H hH,
    gciQueryMatrix, one_mul, Matrix.mul_assoc]

/-- Eq. (51): there are three instances of the old program, including its
adjoint, and one additional query under the input Hamiltonian. -/
theorem eq51_reducedGci_query_recursion (diagonals : ℕ → Mat D) (s : ℕ → ℝ) (k : ℕ) :
    HamiltonianQueryCount (reducedGciProgram diagonals s (k + 1)) =
      3 * HamiltonianQueryCount (reducedGciProgram diagonals s k) + 1 := by
  simp only [reducedGciProgram, hamiltonianQueryCount_append, adjointGciProgram_queryCount,
    HamiltonianQueryCount]
  omega

/-- The exact evolution-query count of the reduced GCI program after `K` steps. -/
theorem eq52_reducedGci_query_count (diagonals : ℕ → Mat D) (s : ℕ → ℝ) (K : ℕ) :
    HamiltonianQueryCount (reducedGciProgram diagonals s K) = (3 ^ K - 1) / 2 := by
  have h (k : ℕ) : 2 * HamiltonianQueryCount (reducedGciProgram diagonals s k) + 1 = 3 ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, ← ih, eq51_reducedGci_query_recursion]
      omega
  have hK := h K
  omega

/-- The exact count gives the bound `N(K) ≤ 3^K` in the cost model of Eq. (52). -/
theorem eq52_reducedGci_query_upper_bound (diagonals : ℕ → Mat D) (s : ℕ → ℝ) (K : ℕ) :
    HamiltonianQueryCount (reducedGciProgram diagonals s K) ≤ 3 ^ K := by
  rw [eq52_reducedGci_query_count]
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

end Qatlib.Papers.DoubleBracket22.MainResults
