/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQueryLaws
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeQueryLowerBoundBeal
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

structure DecisionProgram (I W : Type) where
  circuit : Circuit (PolynomialWorkspace I W)
  initial : QState (PolynomialWorkspace I W)
  accept : Finset (PolynomialWorkspace I W)

noncomputable def DecisionProgram.successProb (P : DecisionProgram I W) (g : I → Bool) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) P.circuit P.initial) P.accept

def DecisionProgram.ExactFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool, P.successProb g = if f g then (1 : ℝ) else 0

def DecisionProgram.BoundedFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool,
    |P.successProb g - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3

def DecisionProgram.SuccessFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool,
    if f g then (2 / 3 : ℝ) ≤ P.successProb g else P.successProb g ≤ 1 / 3

def DecisionProgram.ZeroErrorFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool, P.successProb g = if f g then (1 : ℝ) else 0

def DecisionProgram.ZeroErrorInconclusiveFor (P : DecisionProgram I W) (f : (I → Bool) → Bool)
    (threshold : ℝ) : Prop :=
  ∀ g : I → Bool,
    if f g then 1 - threshold ≤ P.successProb g else P.successProb g ≤ threshold

structure MachineClass (I W : Type) where
  programs : List (DecisionProgram I W)
  nonempty : programs ≠ []

def listMin? : List ℕ → Option ℕ
  | [] => none
  | x :: xs =>
    match listMin? xs with
    | none => some x
    | some y => some (min x y)

noncomputable def finsetMinNat (s : Finset ℕ) (h : ∃ n, n ∈ s) : ℕ := Nat.find h

theorem finsetMinNat_mem {s : Finset ℕ} {h : ∃ n, n ∈ s} : finsetMinNat s h ∈ s :=
  Nat.find_spec h

theorem finsetMinNat_le {s : Finset ℕ} {h : ∃ n, n ∈ s} {x : ℕ} (hx : x ∈ s) :
    finsetMinNat s h ≤ x :=
  Nat.find_min' h hx

def MachineClass.exactCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.ExactFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

def MachineClass.zeroErrorCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.ZeroErrorFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

def MachineClass.boundedCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.BoundedFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

def MachineClass.successCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.SuccessFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

theorem MachineClass.queryCount_mem_exactCountSet {M : MachineClass I W} {f : (I → Bool) → Bool}
    {Q : DecisionProgram I W} (hQ : Q ∈ M.programs) (hQf : Q.ExactFor f) :
    QueryCount Q.circuit ∈ M.exactCountSet f := by
  unfold MachineClass.exactCountSet
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨Q, List.mem_filter.mpr ⟨hQ, by simp [hQf]⟩, rfl⟩

theorem MachineClass.exactCountSet_of_mem {M : MachineClass I W} {f : (I → Bool) → Bool}
    {y : ℕ} (hy : y ∈ M.exactCountSet f) :
    ∃ Q ∈ M.programs, Q.ExactFor f ∧ QueryCount Q.circuit = y := by
  unfold MachineClass.exactCountSet at hy
  rw [List.mem_toFinset, List.mem_map] at hy
  obtain ⟨Q, hQ, hcnt⟩ := hy
  obtain ⟨hQm, hQf'⟩ := List.mem_filter.mp hQ
  exact ⟨Q, hQm, of_decide_eq_true hQf', hcnt⟩

noncomputable def MachineClass.minExactQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.exactCountSet f) : ℕ :=
  finsetMinNat (M.exactCountSet f) h

noncomputable def MachineClass.minZeroErrorQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.zeroErrorCountSet f) : ℕ :=
  finsetMinNat (M.zeroErrorCountSet f) h

noncomputable def MachineClass.minBoundedQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.boundedCountSet f) : ℕ :=
  finsetMinNat (M.boundedCountSet f) h

noncomputable def MachineClass.minSuccessQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.successCountSet f) : ℕ :=
  finsetMinNat (M.successCountSet f) h

theorem MachineClass.minExactQueries_le {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.exactCountSet f} {Q : DecisionProgram I W} (hQ : Q ∈ M.programs)
    (hQf : Q.ExactFor f) :
    M.minExactQueries f h ≤ QueryCount Q.circuit :=
  finsetMinNat_le (M.queryCount_mem_exactCountSet hQ hQf)

theorem MachineClass.minExactQueries_attained {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.exactCountSet f} :
    ∃ Q ∈ M.programs, Q.ExactFor f ∧ QueryCount Q.circuit = M.minExactQueries f h := by
  obtain ⟨Q, hQ, hQf, hcnt⟩ :=
    M.exactCountSet_of_mem (finsetMinNat_mem (s := M.exactCountSet f) (h := h))
  exact ⟨Q, hQ, hQf, hcnt⟩

theorem MachineClass.minZeroErrorQueries_le {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.zeroErrorCountSet f} {Q : DecisionProgram I W} (hQ : Q ∈ M.programs)
    (hQf : Q.ZeroErrorFor f) :
    M.minZeroErrorQueries f h ≤ QueryCount Q.circuit := by
  have hmem : QueryCount Q.circuit ∈ M.zeroErrorCountSet f := by
    unfold MachineClass.zeroErrorCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨Q, List.mem_filter.mpr ⟨hQ, by simp [hQf]⟩, rfl⟩
  exact finsetMinNat_le hmem

theorem MachineClass.minZeroErrorQueries_attained {M : MachineClass I W}
    {f : (I → Bool) → Bool} {h : ∃ n, n ∈ M.zeroErrorCountSet f} :
    ∃ Q ∈ M.programs, Q.ZeroErrorFor f ∧ QueryCount Q.circuit = M.minZeroErrorQueries f h := by
  have hmem : M.minZeroErrorQueries f h ∈ M.zeroErrorCountSet f :=
    finsetMinNat_mem (s := M.zeroErrorCountSet f) (h := h)
  unfold MachineClass.zeroErrorCountSet at hmem
  rw [List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨Q, hQ, hcnt⟩ := hmem
  obtain ⟨hQm, hQf'⟩ := List.mem_filter.mp hQ
  exact ⟨Q, hQm, of_decide_eq_true hQf', hcnt⟩

variable {Q O : Type}

inductive ClassicalAnswer (B : Type) where
  | bit : B → ClassicalAnswer B
  | inconclusive : ClassicalAnswer B

structure ClassicalProgram (Q O : Type) where
  support : Finset (BoolQueryTree Q O)
  support_nonempty : ∃ t, t ∈ support
  law : PMF (BoolQueryTree Q O)
  support_eq : ∀ t, t ∈ support ↔ law t ≠ 0
  worstQueries : ℕ
  worstQueries_spec : ∀ t, t ∈ support → Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t ≤ worstQueries

theorem ClassicalProgram.worstQueries_ge (prog : ClassicalProgram Q O)
    {t : BoolQueryTree Q O} (ht : t ∈ prog.support) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t ≤ prog.worstQueries :=
  prog.worstQueries_spec t ht

theorem ClassicalProgram.support_pos (prog : ClassicalProgram Q O) {t : BoolQueryTree Q O}
    (ht : t ∈ prog.support) : prog.law t ≠ 0 :=
  (prog.support_eq t).mp ht

noncomputable def ClassicalProgram.expectedQueries (prog : ClassicalProgram Q O) (o : Q → Bool) :
    ℝ≥0∞ :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries prog.law o

noncomputable def ClassicalProgram.worstExpectedQueries (prog : ClassicalProgram Q O)
    (oracles : Finset (Q → Bool)) : ℝ≥0∞ :=
  oracles.toList.foldl
    (fun acc o => max acc (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries prog.law o)) 0

noncomputable def oraclePoint (g : I → Bool) : I → ℝ := fun i => if g i then 1 else 0

noncomputable def treeAcceptPolynomial {I : Type} [DecidableEq I] :
    BoolQueryTree I Bool → MvPolynomial I ℝ
  | .halt b => if b then 1 else 0
  | .ask i onFalse onTrue =>
      (1 - MvPolynomial.X i) * treeAcceptPolynomial onFalse
        + MvPolynomial.X i * treeAcceptPolynomial onTrue

theorem one_sub_X_totalDegree_le {I : Type} [DecidableEq I] (i : I) :
    (1 - MvPolynomial.X (σ := I) (R := ℝ) i : MvPolynomial I ℝ).totalDegree ≤ 1 := by
  have h1 : (1 : MvPolynomial I ℝ).totalDegree = 0 := MvPolynomial.totalDegree_one
  have h2 : ((-1 : ℝ) • (MvPolynomial.X (σ := I) (R := ℝ) i)).totalDegree ≤ 1 := by
    have hh := MvPolynomial.totalDegree_smul_le (-1 : ℝ) (MvPolynomial.X (σ := I) (R := ℝ) i)
    rwa [MvPolynomial.totalDegree_X] at hh
  have hneg : (-MvPolynomial.X (σ := I) (R := ℝ) i)
      = (-1 : ℝ) • (MvPolynomial.X (σ := I) (R := ℝ) i) := by
    simp
  have hsum : (1 - MvPolynomial.X (σ := I) (R := ℝ) i : MvPolynomial I ℝ).totalDegree
      ≤ max (1 : MvPolynomial I ℝ).totalDegree
          ((-1 : ℝ) • (MvPolynomial.X (σ := I) (R := ℝ) i)).totalDegree := by
    rw [sub_eq_add_neg, hneg]
    exact MvPolynomial.totalDegree_add _ _
  refine le_trans hsum ?_
  rw [h1]
  omega

theorem treeAcceptPolynomial_eval {I : Type} [DecidableEq I] (t : BoolQueryTree I Bool)
    (g : I → Bool) :
    MvPolynomial.eval (oraclePoint g) (treeAcceptPolynomial t) =
      if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g t).1 then (1 : ℝ) else 0 := by
  induction t with
  | halt b => cases b <;> simp [treeAcceptPolynomial, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
  | ask i onFalse onTrue ihFalse ihTrue =>
    rw [treeAcceptPolynomial]
    by_cases hgi : g i = true
    · have hrun : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (.ask i onFalse onTrue)).1
          = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g onTrue).1 := by
        simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hgi]
      rw [hrun]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub,
        MvPolynomial.eval_X, oraclePoint, if_pos hgi]
      rw [ihTrue]
      simp
    · have hrun : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (.ask i onFalse onTrue)).1
          = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g onFalse).1 := by
        simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hgi]
      rw [hrun]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub,
        MvPolynomial.eval_X, oraclePoint, if_neg hgi]
      rw [ihFalse]
      simp

theorem treeAcceptPolynomial_totalDegree_le {I : Type} [DecidableEq I] (t : BoolQueryTree I Bool) :
    (treeAcceptPolynomial t).totalDegree ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t := by
  induction t with
  | halt b => cases b <;> simp [treeAcceptPolynomial, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | ask i onFalse onTrue ihFalse ihTrue =>
    have hMF : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onFalse
        ≤ max (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onFalse) (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onTrue) :=
      le_max_left _ _
    have hMT : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onTrue
        ≤ max (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onFalse) (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onTrue) :=
      le_max_right _ _
    have hmaxF : (treeAcceptPolynomial onFalse).totalDegree
        ≤ max (treeAcceptPolynomial onFalse).totalDegree
            (treeAcceptPolynomial onTrue).totalDegree :=
      le_max_left _ _
    have hmaxT : (treeAcceptPolynomial onTrue).totalDegree
        ≤ max (treeAcceptPolynomial onFalse).totalDegree
            (treeAcceptPolynomial onTrue).totalDegree :=
      le_max_right _ _
    have hmul1 : ((1 - MvPolynomial.X (σ := I) (R := ℝ) i) * treeAcceptPolynomial onFalse).totalDegree
        ≤ (treeAcceptPolynomial onFalse).totalDegree + 1 := by
      have hh := MvPolynomial.totalDegree_mul
        (1 - MvPolynomial.X (σ := I) (R := ℝ) i) (treeAcceptPolynomial onFalse)
      have h1 := one_sub_X_totalDegree_le i
      omega
    have hmul2 :
        (MvPolynomial.X (σ := I) (R := ℝ) i * treeAcceptPolynomial onTrue).totalDegree
        ≤ (treeAcceptPolynomial onTrue).totalDegree + 1 := by
      have hh := MvPolynomial.totalDegree_mul
        (MvPolynomial.X (σ := I) (R := ℝ) i) (treeAcceptPolynomial onTrue)
      have hX : (MvPolynomial.X (σ := I) (R := ℝ) i).totalDegree = 1 :=
        MvPolynomial.totalDegree_X i
      omega
    have hsum : (treeAcceptPolynomial (.ask i onFalse onTrue)).totalDegree
        ≤ 1 + max (treeAcceptPolynomial onFalse).totalDegree
            (treeAcceptPolynomial onTrue).totalDegree := by
      rw [treeAcceptPolynomial]
      refine le_trans (MvPolynomial.totalDegree_add
        ((1 - MvPolynomial.X (σ := I) (R := ℝ) i) * treeAcceptPolynomial onFalse)
        (MvPolynomial.X (σ := I) (R := ℝ) i * treeAcceptPolynomial onTrue)) ?_
      rw [max_le_iff]
      exact ⟨le_trans hmul1 (by
                calc (treeAcceptPolynomial onFalse).totalDegree + 1
                    ≤ max (treeAcceptPolynomial onFalse).totalDegree
                        (treeAcceptPolynomial onTrue).totalDegree + 1 :=
                  Nat.add_le_add_right hmaxF 1
                  _ = 1 + max (treeAcceptPolynomial onFalse).totalDegree
                        (treeAcceptPolynomial onTrue).totalDegree := by omega),
            le_trans hmul2 (by
                calc (treeAcceptPolynomial onTrue).totalDegree + 1
                    ≤ max (treeAcceptPolynomial onFalse).totalDegree
                        (treeAcceptPolynomial onTrue).totalDegree + 1 :=
                  Nat.add_le_add_right hmaxT 1
                  _ = 1 + max (treeAcceptPolynomial onFalse).totalDegree
                        (treeAcceptPolynomial onTrue).totalDegree := by omega)⟩
    refine le_trans hsum ?_
    show 1 + max (treeAcceptPolynomial onFalse).totalDegree
        (treeAcceptPolynomial onTrue).totalDegree
        ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries (.ask i onFalse onTrue)
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
    have hmax1 : max (treeAcceptPolynomial onFalse).totalDegree
        (treeAcceptPolynomial onTrue).totalDegree
        ≤ max (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onFalse) (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries onTrue) := by
      rw [max_le_iff]
      exact ⟨le_trans ihFalse hMF, le_trans ihTrue hMT⟩
    exact Nat.add_le_add_left hmax1 1

noncomputable def groverAngle (N M : ℕ) (_hM : 0 < M) (_hN : M ≤ N) : ℝ :=
  Real.arcsin (Real.sqrt ((M : ℝ) / (N : ℝ)))

def groverRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | 0, 0 => Real.cos θ
    | 0, 1 => -Real.sin θ
    | 1, 0 => Real.sin θ
    | 1, 1 => Real.cos θ

noncomputable def groverSuccessProb (N M k : ℕ) (hM : 0 < M) (hN : M ≤ N) : ℝ :=
  Real.sin ((2 * k + 1) * groverAngle N M hM hN) ^ 2

noncomputable def groverIterations (N M : ℕ) (hM : 0 < M) (hN : M ≤ N) : ℕ :=
  Nat.ceil (Real.pi / (4 * groverAngle N M hM hN) - 1 / 2)

theorem MachineClass.minBoundedQueries_le {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.boundedCountSet f} {Q : DecisionProgram I W} (hQ : Q ∈ M.programs)
    (hQf : Q.BoundedFor f) :
    M.minBoundedQueries f h ≤ QueryCount Q.circuit := by
  have hmem : QueryCount Q.circuit ∈ M.boundedCountSet f := by
    unfold MachineClass.boundedCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨Q, List.mem_filter.mpr ⟨hQ, by simp [hQf]⟩, rfl⟩
  exact finsetMinNat_le hmem

theorem MachineClass.minSuccessQueries_le {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.successCountSet f} {Q : DecisionProgram I W} (hQ : Q ∈ M.programs)
    (hQf : Q.SuccessFor f) :
    M.minSuccessQueries f h ≤ QueryCount Q.circuit := by
  have hmem : QueryCount Q.circuit ∈ M.successCountSet f := by
    unfold MachineClass.successCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨Q, List.mem_filter.mpr ⟨hQ, by simp [hQf]⟩, rfl⟩
  exact finsetMinNat_le hmem

end Qatlib.Concepts.QueryComplexity.DegreeMethod
