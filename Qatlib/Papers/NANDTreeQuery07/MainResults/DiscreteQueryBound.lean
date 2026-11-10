/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Qatlib.Papers.NANDTreeQuery07.MainResults.AssemblyBound
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open scoped Matrix

namespace Qatlib.Papers.NANDTreeQuery07.MainResults

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

@[simp] theorem nandTree_zero (c : Bool) : nandTree 0 (fun _ => c) = c := by
  simp [nandTree]

theorem nandTree_nand (n : ℕ) (x : Fin (2 ^ (n + 1)) → Bool) :
    nandTree (n + 1) x =
      !(nandTree n (fun i => x (Fin.castLE (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ n)) i)) &&
        nandTree n (fun i => x ⟨2 ^ n + i.val, by
          have hi := i.isLt
          calc 2 ^ n + i.val < 2 ^ n + 2 ^ n := Nat.add_lt_add_left hi _
            _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; ring⟩)) := rfl

theorem nandTree_const_succ (c : Bool) (n : ℕ) :
    nandTree (n + 1) (fun _ => c) = !(nandTree n (fun _ => c)) := by
  simp [nandTree, Bool.and_self]

theorem nandTree_const_add_two (c : Bool) (n : ℕ) :
    nandTree (n + 2) (fun _ => c) = nandTree n (fun _ => c) := by
  rw [nandTree_const_succ, nandTree_const_succ]
  simp

structure NandTreeProgram (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where
  circuit : Circuit (PolynomialWorkspace (Fin (2 ^ n)) W)
  initial : QState (PolynomialWorkspace (Fin (2 ^ n)) W)
  decode : PolynomialWorkspace (Fin (2 ^ n)) W → Bool

noncomputable def NandTreeProgram.successProb {n : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] (P : NandTreeProgram n W) (x : Fin (2 ^ n) → Bool) : ℝ :=
  MeasureProb
    (Run (TensorGate (BitOracleOn x) (1 : Matrix W W ℂ)) P.circuit P.initial)
    (Finset.univ.filter (fun z => P.decode z = nandTree n x))

def NandTreeProgram.queryCount {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (P : NandTreeProgram n W) : ℕ :=
  QueryCount P.circuit

def NandTreeProgram.Computes {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (P : NandTreeProgram n W) : Prop :=
  IsUnitaryCircuit P.circuit ∧ ∀ x, (2 : ℝ) / 3 ≤ P.successProb x

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

@[simp] theorem two_query_block_query_cost {I : Type*} (U : Matrix I I ℂ) :
    QueryCount ([Step.query, Step.gate U, Step.query] : Circuit I) = 2 := rfl

theorem queryCount_repeat_two_query_block {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (K : ℕ) :
    QueryCount (RepeatCircuit ([Step.query, Step.gate U, Step.query] : Circuit I) K) =
      2 * K := by
  rw [queryCount_repeatCircuit, two_query_block_query_cost, Nat.mul_comm]

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
