/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

set_option backward.isDefEq.respectTransparency false

/-!
# CSP model for arXiv:1601.01744 (QAOACSP16)

Lin--Zhu, *Performance of QAOA on Typical Instances of Constraint Satisfaction
Problems with Bounded Degree*, fixed arXiv:1601.01744v1 (8 Jan 2016).

Definitions 1--3 (p.2) and the bounded-degree / no-overlapping-constraints
notions of Sections 2 and 5.  A `Predicate` is a local real-valued function on
the Boolean cube (Definition 1/2), `CSPInstance` is the list of `m` constraints,
`mu` is the mean satisfaction of a uniformly random assignment (`ψ̂(∅)`,
Theorem 1 and Definition 3), and `IsTypical` is equation (2.2): every random
predicate family has zero mean after subtracting its uniform mean.

Boundary: this file contains only the combinatorial objects and elementary
inequalities.  It does not assert any QAOA performance statement.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A single constraint: a real-valued predicate together with its scope.

Definition 2 of the paper (p.2): a constraint is `(ψ, S)` where `S` is the
scope.  Locality (`local`) records that the value depends only on the variables
in the scope.  The paper works with Boolean predicates `ψ : {0,1} → {0,1}` for
CSPs and relaxes the image to `ℝ` for generalized Max-XOR (Section 4.1). -/
structure Predicate (V : Type) [Fintype V] where
  /-- Scope of the constraint. -/
  scope : Finset V
  /-- Value of the predicate on a full assignment. -/
  val : (V → Bool) → ℝ
  /-- The value only depends on the variables inside the scope. -/
  locality : ∀ z z' : V → Bool, (∀ v ∈ scope, z v = z' v) → val z = val z'

/-- A Max-CSP instance with `m > 0` constraints. -/
structure CSPInstance (V : Type) [Fintype V] where
  /-- Number of constraints. -/
  m : ℕ
  /-- The instance is nonempty. -/
  hm : 0 < m
  /-- The constraints. -/
  con : Fin m → Predicate V

/-- Total number of satisfied constraints at an assignment. -/
def satValue (X : CSPInstance V) (z : V → Bool) : ℝ :=
  ∑ l, (X.con l).val z

/-- Fraction of satisfied constraints at an assignment. -/
def satFraction (X : CSPInstance V) (z : V → Bool) : ℝ :=
  satValue X z / (X.m : ℝ)

/-- Uniform expectation over the Boolean cube.  By Theorem 1 (p.2) this is the
constant Fourier coefficient `f̂(∅)`. -/
def uniformExpect (f : (V → Bool) → ℝ) : ℝ :=
  (∑ z, f z) / (Fintype.card (V → Bool) : ℝ)

/-- Mean value of one predicate under a uniformly random assignment, i.e.
`ψ̂(∅)`: the probability that the constraint is satisfied. -/
def constraintMean (p : Predicate V) : ℝ := uniformExpect p.val

/-- `μ`: the fraction of constraints satisfied in expectation by a uniformly
random assignment (Section 1, p.1). -/
def mu (X : CSPInstance V) : ℝ :=
  (∑ l, constraintMean (X.con l)) / (X.m : ℝ)

/-- Bounded degree `D`: every variable occurs in at most `D` constraints
(Section 1, p.1). -/
def BoundedDegree (X : CSPInstance V) (D : ℕ) : Prop :=
  ∀ v : V, (Finset.univ.filter fun l : Fin X.m => v ∈ (X.con l).scope).card ≤ D

/-- Every scope has arity at most `k` (Boolean CSPs of arity bounded by `k`,
Section 2, p.2). -/
def BoundedArity (X : CSPInstance V) (k : ℕ) : Prop :=
  ∀ l : Fin X.m, (X.con l).scope.card ≤ k

/-- Definition 4 of the paper (p.13, quoted from arXiv:1505.03424): the scopes
of any two distinct constraints intersect in at most one variable. -/
def NoOverlapping (X : CSPInstance V) : Prop :=
  ∀ l l' : Fin X.m, l ≠ l' → ((X.con l).scope ∩ (X.con l').scope).card ≤ 1

/-- Typicality, equation (2.2) of Definition 3 (p.2): a random predicate family
has zero mean after subtracting the uniform mean, at every point of the cube.
This is the coordinate form of the Fourier condition (2.3). -/
def IsTypical {P : Type} [Fintype P] (sel : P → Predicate V) (law : FinDist P) : Prop :=
  ∀ z : V → Bool, law.expect (fun p => (sel p).val z - constraintMean (sel p)) = 0

/-- The instance built by choosing, independently for every constraint, a
predicate from the family `sel` according to the law `law` (Section 2, p.2). -/
def sampledInstance (m : ℕ) (hm : 0 < m) {P : Type}
    (sel : Fin m → P → Predicate V) (ω : Fin m → P) : CSPInstance V where
  m := m
  hm := hm
  con := fun l => sel l (ω l)

/-- The `l`-th constraint of `sampledInstance` is the selected predicate. -/
@[simp] theorem sampledInstance_con (m : ℕ) (hm : 0 < m) {P : Type}
    (sel : Fin m → P → Predicate V) (ω : Fin m → P) (l : Fin m) :
    (sampledInstance m hm sel ω).con l = sel l (ω l) := rfl

/-- A constant has its constant as uniform mean. -/
theorem uniformExpect_const (c : ℝ) : uniformExpect (fun _ : V → Bool => c) = c := by
  unfold uniformExpect
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hpos : (0 : ℝ) < (Fintype.card (V → Bool) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := V → Bool)
  field_simp [hpos.ne']

/-- The uniform mean is additive. -/
theorem uniformExpect_add (f g : (V → Bool) → ℝ) :
    uniformExpect (fun z => f z + g z) = uniformExpect f + uniformExpect g := by
  unfold uniformExpect
  rw [Finset.sum_add_distrib, add_div]

/-- The uniform mean commutes with real scalar multiplication. -/
theorem uniformExpect_smul (c : ℝ) (f : (V → Bool) → ℝ) :
    uniformExpect (fun z => c * f z) = c * uniformExpect f := by
  unfold uniformExpect
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Total satisfaction is nonnegative when all predicates are nonnegative. -/
theorem satValue_nonneg (X : CSPInstance V) (z : V → Bool)
    (h : ∀ l : Fin X.m, ∀ z, 0 ≤ (X.con l).val z) : 0 ≤ satValue X z :=
  Finset.sum_nonneg fun l _ => h l z

/-- Total satisfaction is at most `m` when every predicate is bounded by one. -/
theorem satValue_le_m (X : CSPInstance V) (z : V → Bool)
    (h : ∀ l : Fin X.m, ∀ z, (X.con l).val z ≤ 1) : satValue X z ≤ (X.m : ℝ) := by
  calc
    satValue X z ≤ ∑ _l : Fin X.m, (1 : ℝ) :=
      Finset.sum_le_sum fun l _ => h l z
    _ = (X.m : ℝ) := by simp

/-- The satisfied fraction lies in `[0,1]` for Boolean predicates. -/
theorem satFraction_mem_unit (X : CSPInstance V) (z : V → Bool)
    (h0 : ∀ l : Fin X.m, ∀ z, 0 ≤ (X.con l).val z)
    (h1 : ∀ l : Fin X.m, ∀ z, (X.con l).val z ≤ 1) :
    satFraction X z ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · exact div_nonneg (satValue_nonneg X z h0) (by positivity)
  · rw [satFraction, div_le_one (by exact_mod_cast X.hm)]
    exact satValue_le_m X z h1

/-- `μ` is nonnegative for nonnegative predicates. -/
theorem mu_nonneg (X : CSPInstance V)
    (h0 : ∀ l : Fin X.m, ∀ z, 0 ≤ (X.con l).val z) : 0 ≤ mu X := by
  unfold mu constraintMean uniformExpect
  apply div_nonneg
  · exact Finset.sum_nonneg fun l _ => div_nonneg
      (Finset.sum_nonneg fun z _ => h0 l z) (by positivity)
  · positivity

/-- `μ` is at most one for Boolean predicates. -/
theorem mu_le_one (X : CSPInstance V)
    (h1 : ∀ l : Fin X.m, ∀ z, (X.con l).val z ≤ 1) : mu X ≤ 1 := by
  unfold mu constraintMean uniformExpect
  rw [div_le_one (by exact_mod_cast X.hm)]
  calc
    (∑ l : Fin X.m, (∑ z, (X.con l).val z) / (Fintype.card (V → Bool) : ℝ))
        ≤ ∑ _l : Fin X.m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      rw [div_le_one (by exact_mod_cast Fintype.card_pos (α := V → Bool))]
      calc
        (∑ z, (X.con l).val z) ≤ ∑ _z : V → Bool, (1 : ℝ) :=
          Finset.sum_le_sum fun z _ => h1 l z
        _ = (Fintype.card (V → Bool) : ℝ) := by simp
    _ = (X.m : ℝ) := by simp

end Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel
