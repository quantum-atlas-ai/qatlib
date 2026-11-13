/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Black-box group vocabulary and algebraic task feasibility

Encodings and hiding predicates specify mathematical data. The legacy
`TaskSolution` and `HiddenSubgroupSolution` records attach independent ledgers;
there is no oracle program or execution semantics linking their fields.
`PolySolvable` and `PolySolvableIn` therefore describe ledger packaging only,
not operational polynomial-time solvability. Their polynomial constants are
chosen for a single instance, not uniformly over inputs.

The claim modules prove finite-group feasibility and algebraic reconstruction
without promoting these results to complexity claims. All structure and field
names are retained for compatibility.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults

/-- A finite type of codes equipped with a partial decoding map into `G`. -/
structure Encoding (G : Type*) where

  Code : Type*
  [fintypeCode : Fintype Code]

  decode : Code → Option G

attribute [instance] Encoding.fintypeCode

namespace Encoding

variable {G : Type*}

/-- The predicate that every group element has exactly one code decoding to it. -/
def Unique (E : Encoding G) : Prop :=
  ∀ g : G, ∃! c : E.Code, E.decode c = some g

/-- The negation of the unique-encoding predicate `Encoding.Unique`. -/
def NonUnique (E : Encoding G) : Prop :=
  ¬ E.Unique

end Encoding

/-- Black-box group metadata consisting of an encoding length, a finite generating set with a
generation proof, and the parameter `nu`. -/
structure BlackBoxGroupData (G : Type*) [Group G] where

  encodingLength : ℕ

  generators : Finset G

  generates : Subgroup.closure (generators : Set G) = ⊤

  nu : ℕ

namespace BlackBoxGroupData

variable {G : Type*} [Group G]

/-- The input-size expression given by encoding length times the cardinality of the stored
generating set. -/
def inputSize (B : BlackBoxGroupData G) : ℕ :=
  B.encodingLength * B.generators.card

/-- The natural cardinality `Nat.card G` of the underlying group. -/
noncomputable def groupOrder (_B : BlackBoxGroupData G) : ℕ := Nat.card G

end BlackBoxGroupData

/-- The predicate that `ν ≥ 1` and `ν = 1` whenever `G` is solvable. -/
structure NuSpec (G : Type*) [Group G] (ν : ℕ) : Prop where

  pos : 1 ≤ ν

  solvable_eq_one : Group.IsSolvable G → ν = 1

/-- A subgroup `H` and a function `f` whose equal values are characterized by `a⁻¹ * b ∈ H`. -/
structure HiddenSubgroupInstance (G : Type*) [Group G] (X : Type*) where

  H : Subgroup G

  f : G → X

  hides : ∀ a b : G, f a = f b ↔ a⁻¹ * b ∈ H

namespace HiddenSubgroupInstance

variable {G : Type*} [Group G] {X : Type*}

/-- The hiding value at `a` equals the hiding value at the identity exactly when `a` belongs to
the hidden subgroup. -/
theorem hides_one (I : HiddenSubgroupInstance G X) (a : G) :
    I.f a = I.f 1 ↔ a ∈ I.H := by
  simpa [mul_one, Subgroup.inv_mem_iff] using I.hides a 1

/-- Membership in the hidden subgroup is equivalent to equality with the hiding value at the
identity. -/
theorem mem_iff_f_eq_one (I : HiddenSubgroupInstance G X) (a : G) :
    a ∈ I.H ↔ I.f a = I.f 1 :=
  (I.hides_one a).symm

end HiddenSubgroupInstance

/-- An element-order oracle and a Boolean membership oracle with a correctness specification for
commuting families of prime exponent. -/
structure Oracles {G : Type*} [Group G] (B : BlackBoxGroupData G) where

  orderOracle : G → ℕ

  order_spec : ∀ g : G, orderOracle g = orderOf g

  elementaryMembership : ∀ (_S : Finset G) (_g : G), Bool

  elementaryMembership_spec :
    ∀ (S : Finset G) (g : G),
      (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) →
      (∃ p : ℕ, p.Prime ∧ ∀ a ∈ S, a ^ p = 1) →
      (elementaryMembership S g = true ↔ g ∈ Subgroup.closure (S : Set G))

namespace Oracles

variable {G : Type*} [Group G] {B : BlackBoxGroupData G}

/-- The order oracle returns `orderOf g`. -/
theorem orderOracle_eq_orderOf (Ω : Oracles B) (g : G) :
    Ω.orderOracle g = orderOf g :=
  Ω.order_spec g

end Oracles

/-- Numerical resource metadata, with no certified link to an execution. -/
structure CostLedger where

  queries : ℕ

  groupOps : ℕ

  gates : ℕ

namespace CostLedger

/-- The maximum of the query, group-operation, and gate counts. -/
def total (l : CostLedger) : ℕ :=
  max l.queries (max l.groupOps l.gates)

/-- The ledger with all three counts equal to zero. -/
def zero : CostLedger := ⟨0, 0, 0⟩

/-- The total of the zero ledger is zero. -/
@[simp] theorem total_zero : zero.total = 0 := by
  simp [zero, total]

end CostLedger

/-- The predicate that a ledger's total is bounded by `c * (B.inputSize + B.nu + 1)^k` for some
natural `c` and `k`. -/
def PolyBounded {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (l : CostLedger) : Prop :=
  ∃ c k : ℕ, l.total ≤ c * (B.inputSize + B.nu + 1) ^ k

/-- The predicate that a ledger's total is bounded by `c * (B.inputSize + p + 1)^k` for some
natural `c` and `k`. -/
def PolyBoundedIn {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (p : ℕ) (l : CostLedger) : Prop :=
  ∃ c k : ℕ, l.total ≤ c * (B.inputSize + p + 1) ^ k

/-- The five task labels for membership, order and presentation, center, composition series, and
Sylow subgroups. -/
inductive Task where

  | membershipTest

  | orderAndPresentation

  | center

  | compositionSeries

  | sylow
  deriving DecidableEq, Repr

/-- The predicate that `K.subgroupOf H` is normal in `H`. -/
def NormalIn {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  (K.subgroupOf H).Normal

/-- The predicate that `K` is a proper normal subgroup of `H` with no normal subgroup strictly
between its image in `H` and the top subgroup. -/
def IsSimpleFactor {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  K ≤ H ∧ NormalIn K H ∧ K ≠ H ∧
    ∀ M : Subgroup H, K.subgroupOf H ≤ M → M.Normal → M = ⊤ ∨ M = K.subgroupOf H

/-- The existence of a finite strictly descending chain from the whole group to the trivial
subgroup with each successive factor satisfying `IsSimpleFactor`. -/
def HasCompositionSeries (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (C : ℕ → Subgroup G),
    C 0 = ⊤ ∧ C n = ⊥ ∧
    (∀ i < n, C (i + 1) < C i) ∧
    (∀ i < n, IsSimpleFactor (C (i + 1)) (C i))

/-- The predicate that every group element is a finite product of integer powers of group
elements. -/
def HasGeneratorWords {G : Type*} [Group G] (_B : BlackBoxGroupData G) : Prop :=
  ∀ g : G, ∃ w : List (G × ℤ), (w.map (fun q => q.1 ^ q.2)).prod = g

/-- The task-dependent feasibility predicate expressing word representations, a presentation on
finitely many generators, generators of the center, a composition series, or Sylow subgroup
existence. -/
def TaskFeasible {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (_Ω : Oracles B) : Task → Prop
  | .membershipTest => HasGeneratorWords B
  | .orderAndPresentation =>
      ∃ (α : Type) (_ : Fintype α) (rel : Set (FreeGroup α)),
        Nonempty (PresentedGroup rel ≃* G)
  | .center => ∃ S : Finset G, Subgroup.closure (S : Set G) = Subgroup.center G
  | .compositionSeries => HasCompositionSeries G
  | .sylow => ∀ p : ℕ, p.Prime → Nonempty (Sylow p G)

/-- A task together with a cost ledger satisfying `PolyBounded` and a proof of its
`TaskFeasible` predicate. -/
structure TaskSolution {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) where

  task : Task

  cost : CostLedger

  poly : PolyBounded B cost

  feasible : TaskFeasible B Ω task

/-- Legacy feasibility/ledger packaging for a single instance. Despite its
name this predicate does not assert an implemented polynomial-time algorithm. -/
def PolySolvable {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) (t : Task) : Prop :=
  ∃ s : TaskSolution B Ω, s.task = t

/-- Legacy single-instance ledger packaging and mathematical feasibility;
this does not assert an implemented polynomial-time algorithm. -/
def PolySolvableIn {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) (p : ℕ) (t : Task) : Prop :=
  ∃ cost : CostLedger, PolyBoundedIn B p cost ∧ TaskFeasible B Ω t

/-- A finite generating set for the hidden subgroup together with a cost ledger. -/
structure HiddenSubgroupSolution {G : Type*} [Group G] {X : Type*}
    (B : BlackBoxGroupData G) (I : HiddenSubgroupInstance G X) where

  generators : Finset G

  generates : Subgroup.closure (generators : Set G) = I.H

  cost : CostLedger

/-- The list containing all five task labels. -/
def allTasks : List Task :=
  [.membershipTest, .orderAndPresentation, .center, .compositionSeries, .sylow]

/-- Black-box data for a normal quotient using the original encoding length, the supplied
quotient generators, and parameter `νq`. -/
noncomputable def quotientData {G : Type*} [Group G]
    (B : BlackBoxGroupData G) (N : Subgroup G) [N.Normal] (νq : ℕ)
    (gens : Finset (G ⧸ N))
    (hgens : Subgroup.closure (gens : Set (G ⧸ N)) = ⊤) :
    BlackBoxGroupData (G ⧸ N) where
  encodingLength := B.encodingLength
  generators := gens
  generates := hgens
  nu := νq

end Qatlib.Papers.NonAbelianHSP01.MainResults
