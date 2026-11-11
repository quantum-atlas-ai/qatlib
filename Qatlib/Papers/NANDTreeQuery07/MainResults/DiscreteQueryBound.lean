/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Qatlib.Papers.NANDTreeQuery07.MainResults.AssemblyBound

/-!
# NAND Tree Programs and Conditional Query Bounds

This module defines the balanced Boolean function `nandTree` and the circuit data
`NandTreeProgram` for the discrete query setting of [ChildsEtAl2009Formula]. The program
definitions specify its success probability, query count, and the predicate requiring unitary
gates and success probability at least two thirds on every input.

## Main statements

* `nandTree_nand` gives the recursive NAND rule, while `nandTree_const_add_two` records period
  two on constant inputs.
* `two_query_block_query_cost` and `queryCount_repeat_two_query_block` count the queries in one
  block and in repeated blocks.
* `zero_depth_one_query_program` constructs a computing program with one query at depth zero.
* `nand_tree_query_bound_of_step_bound` bounds the queries of any computing program satisfying
  the stated step bound and the equality `queryCount = 2 * K`.

## References

* [Childs et al., 2009][ChildsEtAl2009Formula]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open scoped Matrix

namespace Qatlib.Papers.NANDTreeQuery07.MainResults

/-- The balanced NAND tree function on `2^n` Boolean inputs associated with the evaluation
problem in [ChildsEtAl2009Formula], defined as the single input at depth zero and the NAND
of the two half sized subtrees at each successor depth. -/
noncomputable def nandTree : (n : ℕ) → (Fin (2 ^ n) → Bool) → Bool
  | 0 => fun x => x ⟨0, by norm_num⟩
  | n + 1 => fun x =>
      let hle : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
      let left : Fin (2 ^ n) → Bool := fun i => x (Fin.castLE hle i)
      let right : Fin (2 ^ n) → Bool := fun i =>
        x ⟨2 ^ n + i.val, by
          have hi := i.isLt
          calc 2 ^ n + i.val < 2 ^ n + 2 ^ n := Nat.add_lt_add_left hi _
            _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; ring⟩
      !(nandTree n left && nandTree n right)

/-- At depth zero, the NAND tree with constant input `c` evaluates to `c`. -/
@[simp] theorem nandTree_zero (c : Bool) : nandTree 0 (fun _ => c) = c := by
  simp [nandTree]

/-- At successor depth, the balanced NAND tree is the negation of the conjunction of the NAND
tree values on its left and right halves. This is the recursive function identity associated
with the evaluation problem in [ChildsEtAl2009Formula]. -/
theorem nandTree_nand (n : ℕ) (x : Fin (2 ^ (n + 1)) → Bool) :
    nandTree (n + 1) x =
      !(nandTree n (fun i => x (Fin.castLE (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ n)) i)) &&
        nandTree n (fun i => x ⟨2 ^ n + i.val, by
          have hi := i.isLt
          calc 2 ^ n + i.val < 2 ^ n + 2 ^ n := Nat.add_lt_add_left hi _
            _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; ring⟩)) := rfl

/-- Increasing the depth of a constant input NAND tree by one negates its value. -/
theorem nandTree_const_succ (c : Bool) (n : ℕ) :
    nandTree (n + 1) (fun _ => c) = !(nandTree n (fun _ => c)) := by
  simp [nandTree, Bool.and_self]

/-- Increasing the depth of a constant input NAND tree by two preserves its value. -/
theorem nandTree_const_add_two (c : Bool) (n : ℕ) :
    nandTree (n + 2) (fun _ => c) = nandTree n (fun _ => c) := by
  rw [nandTree_const_succ, nandTree_const_succ]
  simp

/-- A circuit, initial state, and Boolean decoding function on the query workspace for a depth
`n` balanced NAND tree with auxiliary workspace `W`. This is program data for the discrete
query setting associated with [ChildsEtAl2009Formula]. -/
structure NandTreeProgram (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where
  circuit : Circuit (PolynomialWorkspace (Fin (2 ^ n)) W)
  initial : QState (PolynomialWorkspace (Fin (2 ^ n)) W)
  decode : PolynomialWorkspace (Fin (2 ^ n)) W → Bool

/-- The measurement weight of outcomes whose decoded Boolean value equals `nandTree n x`, after
running the program with the bit oracle for input `x` tensored with the identity on `W`. -/
noncomputable def NandTreeProgram.successProb {n : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] (P : NandTreeProgram n W) (x : Fin (2 ^ n) → Bool) : ℝ :=
  MeasureProb
    (Run (TensorGate (BitOracleOn x) (1 : Matrix W W ℂ)) P.circuit P.initial)
    (Finset.univ.filter (fun z => P.decode z = nandTree n x))

/-- The number of query steps in the program's circuit. -/
def NandTreeProgram.queryCount {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (P : NandTreeProgram n W) : ℕ :=
  QueryCount P.circuit

/-- The predicate that every explicit gate in the program's circuit is unitary and its success
probability is at least two thirds on every input. This specifies a computation condition
associated with the query model in [ChildsEtAl2009Formula]. -/
def NandTreeProgram.Computes {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (P : NandTreeProgram n W) : Prop :=
  IsUnitaryCircuit P.circuit ∧ ∀ x, (2 : ℝ) / 3 ≤ P.successProb x

/-- A basis state has measurement probability one for a set containing its basis label and zero
otherwise. -/
theorem measureProb_ket {I : Type*} [Fintype I] [DecidableEq I] (p : I) (S : Finset I) :
    MeasureProb (Ket p) S = if p ∈ S then 1 else 0 := by
  by_cases hp : p ∈ S
  · rw [if_pos hp]
    unfold MeasureProb
    rw [Finset.sum_eq_single p (fun b _ hbp => by rw [bornProb_ket]; simp [hbp])
      (fun h => absurd hp h)]
    simp [bornProb_ket]
  · rw [if_neg hp]
    unfold MeasureProb
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [bornProb_ket]
    rw [if_neg (show ¬ (b = p) from fun h => hp (h ▸ hb))]

/-- A circuit block consisting of a query, a gate `U`, and another query has query count two.
This is the query counting component associated with the simulation construction in
[ChildsEtAl2009Formula]. -/
@[simp] theorem two_query_block_query_cost {I : Type*} (U : Matrix I I ℂ) :
    QueryCount ([Step.query, Step.gate U, Step.query] : Circuit I) = 2 := rfl

/-- Repeating a query, gate, query block `K` times gives query count `2 * K`. This is the
repeated block counting component associated with the query bound in
[ChildsEtAl2009Formula]. -/
theorem queryCount_repeat_two_query_block {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (K : ℕ) :
    QueryCount (RepeatCircuit ([Step.query, Step.gate U, Step.query] : Circuit I) K) =
      2 * K := by
  rw [queryCount_repeatCircuit, two_query_block_query_cost, Nat.mul_comm]

/-- There exists a depth zero NAND tree program with auxiliary workspace `Unit` that satisfies
`Computes` and uses exactly one query. This is the single input component associated with
the NAND tree evaluation setting in [ChildsEtAl2009Formula]. -/
theorem zero_depth_one_query_program :
    ∃ P : NandTreeProgram 0 Unit, P.Computes ∧ P.queryCount = 1 := by
  let k0 : Fin (2 ^ 0) := ⟨0, by norm_num⟩
  refine ⟨⟨[Step.query], Ket ((k0, false), ()), fun z => z.1.2⟩, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simp [IsUnitaryCircuit]
    · intro x
      have hrun :
          Run (TensorGate (BitOracleOn x) (1 : Matrix Unit Unit ℂ)) [Step.query]
              (Ket ((k0, false), ())) = Ket ((k0, false ^^ x k0), ()) := by
        simp only [run_query, run_nil]
        rw [show Ket ((k0, false), ()) =
            TensorState (Ket (k0, false)) (Ket ()) from
          (tensorState_ket_ket (I := Fin (2 ^ 0) × Bool) (J := Unit) _ _).symm]
        rw [applyGate_tensorGate, applyGate_bitOracleOn_ket, applyGate_one]
        exact tensorState_ket_ket (I := Fin (2 ^ 0) × Bool) (J := Unit) _ _
      have hmem : ((k0, false ^^ x k0), ()) ∈
          Finset.univ.filter (fun z : PolynomialWorkspace (Fin (2 ^ 0)) Unit =>
            z.1.2 = nandTree 0 x) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp [nandTree, k0]
      simp only [NandTreeProgram.successProb, hrun, measureProb_ket]
      rw [if_pos hmem]
      norm_num
  · rfl

/-- For `δ >= 0`, `δ / 2 < ε`, and positive `C₀` and `c`, gives a uniform positive constant
bounding the query count by `C * (2^n)^(1 / 2 + ε)`. This conditional assembly associated
with [ChildsEtAl2009Formula] applies to any computing NAND tree program with query count `2
* K` whose step count satisfies the stated simulation bound. -/
theorem nand_tree_query_bound_of_step_bound
    (ε δ : ℝ) (hδ : 0 ≤ δ) (hε : δ / 2 < ε)
    (C₀ c : ℝ) (hC₀ : 0 < C₀) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
        (P : NandTreeProgram n W) (K : ℕ),
      P.Computes →
      P.queryCount = 2 * K →
      (K : ℝ) ≤ C₀ * (3 * (c * Real.sqrt ((2 : ℝ) ^ n * Real.log ((2 : ℝ) ^ n)))) ^ (1 + δ) →
      (P.queryCount : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hbound⟩ := discrete_query_bound_of_step_bound ε δ hδ hε C₀ c hC₀ hc
  refine ⟨C, hC, ?_⟩
  intro n W _ _ P K _hcomp hq hK
  have hq' : (P.queryCount : ℝ) = 2 * (K : ℝ) := by
    rw [hq]; push_cast; ring
  rw [hq']
  exact hbound n K hK

end Qatlib.Papers.NANDTreeQuery07.MainResults
