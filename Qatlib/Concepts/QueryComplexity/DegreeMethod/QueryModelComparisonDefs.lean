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

/-!
# Decision programs and query minima

This module defines finite quantum machine classes and their exact and bounded-error decision
predicates, and records minimum query counts when qualifying programs exist.
`treeAcceptPolynomial` encodes a deterministic Boolean query tree by a real multivariate
polynomial, as in the polynomial method of [BealsEtAl2001].

Classical programs carry a finitely supported probability law and a worst-case query bound.
The module also defines the angle, planar rotation, success formula, and iteration count used
in Grover search.

## Main statements

* `MachineClass.minExactQueries_attained`: exact query minima are realized.
* `treeAcceptPolynomial_eval`: the polynomial agrees with the tree on Boolean inputs.
* `treeAcceptPolynomial_totalDegree_le`: degree is bounded by maximum tree queries.
* `groverSuccessProb`: the squared-sine search success formula.

## References

* [Beals et al., 2001][BealsEtAl2001]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

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

/-- A quantum decision program specified by a circuit, initial state, and accepting basis
outcomes. -/
structure DecisionProgram (I W : Type) where
  circuit : Circuit (PolynomialWorkspace I W)
  initial : QState (PolynomialWorkspace I W)
  accept : Finset (PolynomialWorkspace I W)

/-- The measurement weight of the accepting outcomes after running the program with Boolean
oracle `g`. -/
noncomputable def DecisionProgram.successProb (P : DecisionProgram I W) (g : I → Bool) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) P.circuit P.initial) P.accept

/-- The acceptance weight equals the Boolean indicator of `f` on every oracle input. -/
def DecisionProgram.ExactFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool, P.successProb g = if f g then (1 : ℝ) else 0

/-- The acceptance weight differs from the Boolean indicator of `f` by at most `1 / 3` on every
input. -/
def DecisionProgram.BoundedFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool,
    |P.successProb g - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3

/-- Acceptance is at least `2 / 3` on true inputs and at most `1 / 3` on false inputs. -/
def DecisionProgram.SuccessFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool,
    if f g then (2 / 3 : ℝ) ≤ P.successProb g else P.successProb g ≤ 1 / 3

/-- The zero-error predicate requiring acceptance weight to equal the Boolean indicator of `f`
on every input. -/
def DecisionProgram.ZeroErrorFor (P : DecisionProgram I W) (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool, P.successProb g = if f g then (1 : ℝ) else 0

/-- The threshold predicate requiring acceptance at least `1 - threshold` on true inputs and at
most `threshold` on false inputs. -/
def DecisionProgram.ZeroErrorInconclusiveFor (P : DecisionProgram I W) (f : (I → Bool) → Bool)
    (threshold : ℝ) : Prop :=
  ∀ g : I → Bool,
    if f g then 1 - threshold ≤ P.successProb g else P.successProb g ≤ threshold

/-- A nonempty finite list of quantum decision programs. -/
structure MachineClass (I W : Type) where
  programs : List (DecisionProgram I W)
  nonempty : programs ≠ []

/-- Return the least element of a natural-number list, or `none` for the empty list. -/
def listMin? : List ℕ → Option ℕ
  | [] => none
  | x :: xs =>
    match listMin? xs with
    | none => some x
    | some y => some (min x y)

/-- The least natural number in a finite set, given a witness that the set is nonempty. -/
noncomputable def finsetMinNat (s : Finset ℕ) (h : ∃ n, n ∈ s) : ℕ := Nat.find h

/-- The minimum selected by `finsetMinNat` belongs to the given finite set. -/
theorem finsetMinNat_mem {s : Finset ℕ} {h : ∃ n, n ∈ s} : finsetMinNat s h ∈ s :=
  Nat.find_spec h

/-- The minimum selected by `finsetMinNat` is at most every member of the finite set. -/
theorem finsetMinNat_le {s : Finset ℕ} {h : ∃ n, n ∈ s} {x : ℕ} (hx : x ∈ s) :
    finsetMinNat s h ≤ x :=
  Nat.find_min' h hx

/-- The finite set of query counts of programs in the machine class computing `f` exactly. -/
def MachineClass.exactCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.ExactFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

/-- The finite set of query counts of programs in the machine class satisfying the zero-error
predicate for `f`. -/
def MachineClass.zeroErrorCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.ZeroErrorFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

/-- The finite set of query counts of programs in the machine class computing `f` with error at
most `1 / 3`. -/
def MachineClass.boundedCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.BoundedFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

/-- The finite set of query counts of programs in the machine class satisfying the success
predicate for `f`. -/
def MachineClass.successCountSet (M : MachineClass I W) (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun Q => decide (Q.SuccessFor f))).map (fun Q => QueryCount Q.circuit) |>.toFinset

/-- The query count of any exact program in the machine class belongs to its exact count set. -/
theorem MachineClass.queryCount_mem_exactCountSet {M : MachineClass I W} {f : (I → Bool) → Bool}
    {Q : DecisionProgram I W} (hQ : Q ∈ M.programs) (hQf : Q.ExactFor f) :
    QueryCount Q.circuit ∈ M.exactCountSet f := by
  unfold MachineClass.exactCountSet
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨Q, List.mem_filter.mpr ⟨hQ, by simp [hQf]⟩, rfl⟩

/-- Every member of the exact count set is realized by an exact program in the machine class. -/
theorem MachineClass.exactCountSet_of_mem {M : MachineClass I W} {f : (I → Bool) → Bool}
    {y : ℕ} (hy : y ∈ M.exactCountSet f) :
    ∃ Q ∈ M.programs, Q.ExactFor f ∧ QueryCount Q.circuit = y := by
  unfold MachineClass.exactCountSet at hy
  rw [List.mem_toFinset, List.mem_map] at hy
  obtain ⟨Q, hQ, hcnt⟩ := hy
  obtain ⟨hQm, hQf'⟩ := List.mem_filter.mp hQ
  exact ⟨Q, hQm, of_decide_eq_true hQf', hcnt⟩

/-- The minimum query count among exact programs in the machine class, given existence of a
realized count. -/
noncomputable def MachineClass.minExactQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.exactCountSet f) : ℕ :=
  finsetMinNat (M.exactCountSet f) h

/-- The minimum query count among zero-error programs in the machine class, given existence of a
realized count. -/
noncomputable def MachineClass.minZeroErrorQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.zeroErrorCountSet f) : ℕ :=
  finsetMinNat (M.zeroErrorCountSet f) h

/-- The minimum query count among bounded-error programs in the machine class, given existence
of a realized count. -/
noncomputable def MachineClass.minBoundedQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.boundedCountSet f) : ℕ :=
  finsetMinNat (M.boundedCountSet f) h

/-- The minimum query count among programs satisfying the success predicate, given existence of
a realized count. -/
noncomputable def MachineClass.minSuccessQueries (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.successCountSet f) : ℕ :=
  finsetMinNat (M.successCountSet f) h

/-- The minimum exact query count is at most the query count of any exact program in the machine
class. -/
theorem MachineClass.minExactQueries_le {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.exactCountSet f} {Q : DecisionProgram I W} (hQ : Q ∈ M.programs)
    (hQf : Q.ExactFor f) :
    M.minExactQueries f h ≤ QueryCount Q.circuit :=
  finsetMinNat_le (M.queryCount_mem_exactCountSet hQ hQf)

/-- An exact program in the machine class realizes the minimum exact query count. -/
theorem MachineClass.minExactQueries_attained {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.exactCountSet f} :
    ∃ Q ∈ M.programs, Q.ExactFor f ∧ QueryCount Q.circuit = M.minExactQueries f h := by
  obtain ⟨Q, hQ, hQf, hcnt⟩ :=
    M.exactCountSet_of_mem (finsetMinNat_mem (s := M.exactCountSet f) (h := h))
  exact ⟨Q, hQ, hQf, hcnt⟩

/-- The minimum zero-error query count is at most the query count of any qualifying program in
the machine class. -/
theorem MachineClass.minZeroErrorQueries_le {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.zeroErrorCountSet f} {Q : DecisionProgram I W} (hQ : Q ∈ M.programs)
    (hQf : Q.ZeroErrorFor f) :
    M.minZeroErrorQueries f h ≤ QueryCount Q.circuit := by
  have hmem : QueryCount Q.circuit ∈ M.zeroErrorCountSet f := by
    unfold MachineClass.zeroErrorCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨Q, List.mem_filter.mpr ⟨hQ, by simp [hQf]⟩, rfl⟩
  exact finsetMinNat_le hmem

/-- A zero-error program in the machine class realizes the minimum zero-error query count. -/
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

/-- A classical answer is either a value of type `B` or an inconclusive outcome. -/
inductive ClassicalAnswer (B : Type) where
  | bit : B → ClassicalAnswer B
  | inconclusive : ClassicalAnswer B

/-- A classical randomized program with a finite nonempty support of Boolean query trees, a
probability law supported exactly there, and a common worst-case query bound. -/
structure ClassicalProgram (Q O : Type) where
  support : Finset (BoolQueryTree Q O)
  support_nonempty : ∃ t, t ∈ support
  law : PMF (BoolQueryTree Q O)
  support_eq : ∀ t, t ∈ support ↔ law t ≠ 0
  worstQueries : ℕ
  worstQueries_spec : ∀ t, t ∈ support → Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t ≤ worstQueries

/-- Every tree in the program's support has maximum query count bounded by `worstQueries`. -/
theorem ClassicalProgram.worstQueries_ge (prog : ClassicalProgram Q O)
    {t : BoolQueryTree Q O} (ht : t ∈ prog.support) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t ≤ prog.worstQueries :=
  prog.worstQueries_spec t ht

/-- Every tree in the program's support has nonzero probability under its law. -/
theorem ClassicalProgram.support_pos (prog : ClassicalProgram Q O) {t : BoolQueryTree Q O}
    (ht : t ∈ prog.support) : prog.law t ≠ 0 :=
  (prog.support_eq t).mp ht

/-- The expected number of queries under the program's tree distribution for a fixed Boolean
oracle. -/
noncomputable def ClassicalProgram.expectedQueries (prog : ClassicalProgram Q O) (o : Q → Bool) :
    ℝ≥0∞ :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries prog.law o

/-- The maximum expected query count over a specified finite set of Boolean oracles, with value
zero for an empty set. -/
noncomputable def ClassicalProgram.worstExpectedQueries (prog : ClassicalProgram Q O)
    (oracles : Finset (Q → Bool)) : ℝ≥0∞ :=
  oracles.toList.foldl
    (fun acc o => max acc (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries prog.law o)) 0

/-- Embed a Boolean oracle into real coordinates by sending false to zero and true to one. -/
noncomputable def oraclePoint (g : I → Bool) : I → ℝ := fun i => if g i then 1 else 0

/-- The real multivariate acceptance polynomial obtained recursively from a Boolean decision
tree. -/
noncomputable def treeAcceptPolynomial {I : Type} [DecidableEq I] :
    BoolQueryTree I Bool → MvPolynomial I ℝ
  | .halt b => if b then 1 else 0
  | .ask i onFalse onTrue =>
      (1 - MvPolynomial.X i) * treeAcceptPolynomial onFalse
        + MvPolynomial.X i * treeAcceptPolynomial onTrue

/-- The total degree of `1 - MvPolynomial.X i` over the reals is at most one. -/
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

/-- Evaluating the acceptance polynomial at a Boolean oracle point gives the indicator of the
tree's output. -/
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

/-- The total degree of a tree's acceptance polynomial is at most its maximum number of queries. -/
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

/-- The Grover angle `arcsin (sqrt (M / N))` for a positive number `M` of marked items among `N`
items. -/
noncomputable def groverAngle (N M : ℕ) (_hM : 0 < M) (_hN : M ≤ N) : ℝ :=
  Real.arcsin (Real.sqrt ((M : ℝ) / (N : ℝ)))

/-- The real two-dimensional rotation matrix through angle `θ`. -/
def groverRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | 0, 0 => Real.cos θ
    | 0, 1 => -Real.sin θ
    | 1, 0 => Real.sin θ
    | 1, 1 => Real.cos θ

/-- The squared-sine expression `sin ((2 * k + 1) * groverAngle N M hM hN) ^ 2` for Grover
search after `k` iterations. -/
noncomputable def groverSuccessProb (N M k : ℕ) (hM : 0 < M) (hN : M ≤ N) : ℝ :=
  Real.sin ((2 * k + 1) * groverAngle N M hM hN) ^ 2

/-- The natural ceiling of `π / (4 * groverAngle N M hM hN) - 1 / 2`. -/
noncomputable def groverIterations (N M : ℕ) (hM : 0 < M) (hN : M ≤ N) : ℕ :=
  Nat.ceil (Real.pi / (4 * groverAngle N M hM hN) - 1 / 2)

/-- The minimum bounded-error query count is at most the query count of any bounded-error
program in the machine class. -/
theorem MachineClass.minBoundedQueries_le {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.boundedCountSet f} {Q : DecisionProgram I W} (hQ : Q ∈ M.programs)
    (hQf : Q.BoundedFor f) :
    M.minBoundedQueries f h ≤ QueryCount Q.circuit := by
  have hmem : QueryCount Q.circuit ∈ M.boundedCountSet f := by
    unfold MachineClass.boundedCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨Q, List.mem_filter.mpr ⟨hQ, by simp [hQf]⟩, rfl⟩
  exact finsetMinNat_le hmem

/-- The minimum success-convention query count is at most the query count of any qualifying
program in the machine class. -/
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
